"""
DMN Parser - Converts DMN XML to Intermediate Representation.

Parses DMN 1.3 compliant XML decision tables.
"""

from lxml import etree
from typing import Optional, List
import re

from ..ir.intermediate import (
    DecisionModel, Decision, Rule, Condition, Conclusion,
    Variable, Literal, Expression, DataType, OperatorType
)


class DMNParser:
    """Parse DMN XML into IR."""

    DMN_NAMESPACE = "https://www.omg.org/spec/DMN/20191111/MODEL/"

    def __init__(self):
        self.nsmap = {
            'dmn': self.DMN_NAMESPACE
        }

    def parse(self, dmn_xml: str) -> DecisionModel:
        """Parse DMN XML string into IR."""
        root = etree.fromstring(dmn_xml.encode('utf-8'))
        return self._parse_definitions(root)

    def parse_file(self, filepath: str) -> DecisionModel:
        """Parse DMN XML file into IR."""
        tree = etree.parse(filepath)
        root = tree.getroot()
        return self._parse_definitions(root)

    def _parse_definitions(self, root: etree.Element) -> DecisionModel:
        """Parse definitions element."""
        # Handle namespace
        ns = root.nsmap.get(None, self.DMN_NAMESPACE)
        nsmap = {'dmn': ns}

        name = root.get('name', 'DMNModel')
        namespace = root.get('namespace', 'http://example.org/dmn')

        # Parse all decisions
        decisions = []
        for decision_elem in root.xpath('.//dmn:decision', namespaces=nsmap):
            decision = self._parse_decision(decision_elem, nsmap)
            if decision:
                decisions.append(decision)

        model = DecisionModel(
            name=name,
            namespace=namespace,
            decisions=decisions
        )

        return model

    def _parse_decision(self, elem: etree.Element, nsmap: dict) -> Optional[Decision]:
        """Parse decision element."""
        decision_id = elem.get('id', '')
        decision_name = elem.get('name', decision_id)

        # Get description
        desc_elem = elem.find('.//dmn:description', namespaces=nsmap)
        description = desc_elem.text if desc_elem is not None else None

        # Find decision table
        table_elem = elem.find('.//dmn:decisionTable', namespaces=nsmap)
        if table_elem is None:
            return None

        hit_policy = table_elem.get('hitPolicy', 'UNIQUE')

        # Parse inputs
        inputs = []
        for input_elem in table_elem.findall('.//dmn:input', namespaces=nsmap):
            var = self._parse_input(input_elem, nsmap)
            if var:
                inputs.append(var)

        # Parse outputs
        outputs = []
        for output_elem in table_elem.findall('.//dmn:output', namespaces=nsmap):
            var = self._parse_output(output_elem, nsmap)
            if var:
                outputs.append(var)

        # Parse rules
        rules = []
        for rule_elem in table_elem.findall('.//dmn:rule', namespaces=nsmap):
            rule = self._parse_rule(rule_elem, inputs, outputs, nsmap)
            if rule:
                rules.append(rule)

        decision = Decision(
            name=decision_id,
            inputs=inputs,
            outputs=outputs,
            rules=rules,
            description=description,
            hit_policy=hit_policy
        )

        return decision

    def _parse_input(self, elem: etree.Element, nsmap: dict) -> Optional[Variable]:
        """Parse input element."""
        label = elem.get('label', '')

        # Get input expression
        expr_elem = elem.find('.//dmn:inputExpression', namespaces=nsmap)
        if expr_elem is None:
            return None

        type_ref = expr_elem.get('typeRef', 'string')
        text_elem = expr_elem.find('.//dmn:text', namespaces=nsmap)
        var_name = text_elem.text if text_elem is not None else label

        data_type = self._feel_to_datatype(type_ref)

        return Variable(
            name=var_name.strip(),
            data_type=data_type,
            description=label
        )

    def _parse_output(self, elem: etree.Element, nsmap: dict) -> Optional[Variable]:
        """Parse output element."""
        var_name = elem.get('name', '')
        label = elem.get('label', var_name)
        type_ref = elem.get('typeRef', 'string')

        data_type = self._feel_to_datatype(type_ref)

        return Variable(
            name=var_name.strip() if var_name else label.strip(),
            data_type=data_type,
            description=label
        )

    def _parse_rule(self, elem: etree.Element, inputs: List[Variable],
                   outputs: List[Variable], nsmap: dict) -> Optional[Rule]:
        """Parse rule element."""
        rule_id = elem.get('id', '')

        # Get description
        desc_elem = elem.find('.//dmn:description', namespaces=nsmap)
        description = desc_elem.text if desc_elem is not None else None

        # Get annotation
        annot_elem = elem.find('.//dmn:annotationEntry/dmn:text', namespaces=nsmap)
        annotation = annot_elem.text if annot_elem is not None else None

        # Parse input entries
        conditions = []
        input_entries = elem.findall('.//dmn:inputEntry', namespaces=nsmap)
        for i, entry_elem in enumerate(input_entries):
            if i < len(inputs):
                text_elem = entry_elem.find('.//dmn:text', namespaces=nsmap)
                if text_elem is not None and text_elem.text and text_elem.text.strip() != '-':
                    condition = self._parse_input_entry(text_elem.text, inputs[i])
                    if condition:
                        conditions.append(condition)

        # Parse output entries
        conclusions = []
        output_entries = elem.findall('.//dmn:outputEntry', namespaces=nsmap)
        for i, entry_elem in enumerate(output_entries):
            if i < len(outputs):
                text_elem = entry_elem.find('.//dmn:text', namespaces=nsmap)
                if text_elem is not None and text_elem.text:
                    conclusion = self._parse_output_entry(text_elem.text, outputs[i])
                    if conclusion:
                        conclusions.append(conclusion)

        rule = Rule(
            id=rule_id,
            conditions=conditions,
            conclusions=conclusions,
            description=description,
            annotation=annotation
        )

        return rule

    def _parse_input_entry(self, feel_text: str, variable: Variable) -> Optional[Condition]:
        """Parse FEEL expression from input entry into condition."""
        feel_text = feel_text.strip()

        # Parse comparison operators
        # Match patterns like: ">= 650", "< 100", "== true", etc.
        comp_pattern = r'^(>=|<=|>|<|==|!=)\s*(.+)$'
        match = re.match(comp_pattern, feel_text)

        if match:
            op_str, value_str = match.groups()
            op = self._feel_op_to_operator(op_str)
            value = self._parse_feel_value(value_str.strip(), variable.data_type)

            expr = Expression(
                operator=op,
                operands=[variable, value]
            )

            return Condition(expression=expr)

        # Handle range: [10..20], (10..20), etc.
        # For now, convert to >= AND <=
        range_pattern = r'^[\[\(](\d+)\.\.(\d+)[\]\)]$'
        match = re.match(range_pattern, feel_text)
        if match:
            low, high = match.groups()
            low_val = Literal(value=int(low), data_type=DataType.NUMBER)
            high_val = Literal(value=int(high), data_type=DataType.NUMBER)

            expr = Expression(
                operator=OperatorType.AND,
                operands=[
                    Expression(operator=OperatorType.GTE, operands=[variable, low_val]),
                    Expression(operator=OperatorType.LTE, operands=[variable, high_val])
                ]
            )
            return Condition(expression=expr)

        # Handle exact match (just a value)
        value = self._parse_feel_value(feel_text, variable.data_type)
        expr = Expression(
            operator=OperatorType.EQ,
            operands=[variable, value]
        )
        return Condition(expression=expr)

    def _parse_output_entry(self, feel_text: str, variable: Variable) -> Optional[Conclusion]:
        """Parse FEEL expression from output entry into conclusion."""
        feel_text = feel_text.strip()

        value = self._parse_feel_value(feel_text, variable.data_type)

        return Conclusion(
            variable=variable,
            value=value
        )

    def _parse_feel_value(self, value_str: str, data_type: DataType) -> Literal:
        """Parse FEEL value string into Literal."""
        value_str = value_str.strip()

        # String literal
        if value_str.startswith('"') and value_str.endswith('"'):
            return Literal(value=value_str[1:-1], data_type=DataType.STRING)

        # Boolean
        if value_str.lower() == 'true':
            return Literal(value=True, data_type=DataType.BOOLEAN)
        elif value_str.lower() == 'false':
            return Literal(value=False, data_type=DataType.BOOLEAN)

        # Number
        try:
            if '.' in value_str:
                return Literal(value=float(value_str), data_type=DataType.NUMBER)
            else:
                return Literal(value=int(value_str), data_type=DataType.NUMBER)
        except ValueError:
            pass

        # Default to string/atom
        return Literal(value=value_str, data_type=data_type)

    def _feel_op_to_operator(self, op_str: str) -> OperatorType:
        """Convert FEEL operator to OperatorType."""
        op_map = {
            '>=': OperatorType.GTE,
            '<=': OperatorType.LTE,
            '>': OperatorType.GT,
            '<': OperatorType.LT,
            '==': OperatorType.EQ,
            '=': OperatorType.EQ,
            '!=': OperatorType.NE,
        }
        return op_map.get(op_str, OperatorType.EQ)

    def _feel_to_datatype(self, feel_type: str) -> DataType:
        """Convert FEEL type to DataType."""
        type_map = {
            'string': DataType.STRING,
            'number': DataType.NUMBER,
            'boolean': DataType.BOOLEAN,
            'date': DataType.DATE,
        }
        return type_map.get(feel_type.lower(), DataType.STRING)
