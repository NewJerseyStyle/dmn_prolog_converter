"""
DMN Generator - Converts Intermediate Representation to DMN XML.

Generates DMN 1.3 compliant XML with decision tables.
"""

from lxml import etree
from typing import Optional
from ..ir.intermediate import (
    DecisionModel, Decision, Rule, Condition, Conclusion,
    Variable, Literal, Expression, DataType, OperatorType
)


class DMNGenerator:
    """Generate DMN XML from IR."""

    DMN_NAMESPACE = "https://www.omg.org/spec/DMN/20191111/MODEL/"
    FEEL_NAMESPACE = "https://www.omg.org/spec/DMN/20191111/FEEL/"

    def __init__(self):
        self.nsmap = {
            None: self.DMN_NAMESPACE,
            'feel': self.FEEL_NAMESPACE
        }

    def generate(self, model: DecisionModel) -> str:
        """Generate DMN XML from DecisionModel."""
        # Create root definitions element
        definitions = etree.Element(
            'definitions',
            nsmap=self.nsmap,
            id=f"{model.name}_definitions",
            name=model.name,
            namespace=model.namespace
        )

        # Add metadata
        definitions.set('exporter', 'Prolog-DMN Converter')
        definitions.set('exporterVersion', '1.0')

        # Add each decision
        for decision in model.decisions:
            decision_elem = self._create_decision_element(decision)
            definitions.append(decision_elem)

        # Pretty print XML
        xml_str = etree.tostring(
            definitions,
            pretty_print=True,
            xml_declaration=True,
            encoding='UTF-8'
        ).decode('utf-8')

        return xml_str

    def generate_file(self, model: DecisionModel, filepath: str):
        """Generate DMN XML file."""
        xml_str = self.generate(model)
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(xml_str)

    def _create_decision_element(self, decision: Decision) -> etree.Element:
        """Create decision element with decision table."""
        decision_elem = etree.Element(
            'decision',
            id=decision.name,
            name=self._format_name(decision.name)
        )

        # Add description if available
        if decision.description:
            desc = etree.SubElement(decision_elem, 'description')
            desc.text = decision.description

        # Create decision table
        decision_table = self._create_decision_table(decision)
        decision_elem.append(decision_table)

        return decision_elem

    def _create_decision_table(self, decision: Decision) -> etree.Element:
        """Create decision table element."""
        table = etree.Element(
            'decisionTable',
            id=f"{decision.name}_table",
            hitPolicy=decision.hit_policy,
            outputLabel=decision.name
        )

        # Add inputs
        for var in decision.inputs:
            input_elem = self._create_input(var)
            table.append(input_elem)

        # Add outputs
        for var in decision.outputs:
            output_elem = self._create_output(var)
            table.append(output_elem)

        # Add rules
        for i, rule in enumerate(decision.rules):
            rule_elem = self._create_rule(rule, i + 1, decision)
            table.append(rule_elem)

        return table

    def _create_input(self, variable: Variable) -> etree.Element:
        """Create input element."""
        input_elem = etree.Element(
            'input',
            id=f"input_{variable.name}",
            label=self._format_name(variable.name)
        )

        input_expr = etree.SubElement(input_elem, 'inputExpression')
        input_expr.set('typeRef', self._datatype_to_feel(variable.data_type))

        text = etree.SubElement(input_expr, 'text')
        text.text = variable.name

        return input_elem

    def _create_output(self, variable: Variable) -> etree.Element:
        """Create output element."""
        output_elem = etree.Element(
            'output',
            id=f"output_{variable.name}",
            label=self._format_name(variable.name),
            name=variable.name,
            typeRef=self._datatype_to_feel(variable.data_type)
        )

        return output_elem

    def _create_rule(self, rule: Rule, rule_num: int, decision: Decision) -> etree.Element:
        """Create rule element."""
        rule_elem = etree.Element(
            'rule',
            id=rule.id or f"rule_{rule_num}"
        )

        # Add description if available
        if rule.description:
            desc = etree.SubElement(rule_elem, 'description')
            desc.text = rule.description

        # Create input entries for each input variable
        # Match conditions to inputs
        input_entries = self._create_input_entries(rule, decision.inputs)
        for entry in input_entries:
            rule_elem.append(entry)

        # Create output entries
        output_entries = self._create_output_entries(rule, decision.outputs)
        for entry in output_entries:
            rule_elem.append(entry)

        # Add annotation if available
        if rule.annotation:
            annotation = etree.SubElement(rule_elem, 'annotationEntry')
            text = etree.SubElement(annotation, 'text')
            text.text = rule.annotation

        return rule_elem

    def _create_input_entries(self, rule: Rule, inputs: list) -> list:
        """Create input entry elements for rule."""
        entries = []

        # Map conditions to inputs
        condition_map = {}
        for condition in rule.conditions:
            # Extract variable from condition
            var_name = self._extract_variable_from_condition(condition)
            if var_name:
                condition_map[var_name] = condition

        # Create entry for each input
        for input_var in inputs:
            entry = etree.Element('inputEntry')
            text_elem = etree.SubElement(entry, 'text')

            if input_var.name in condition_map:
                # Convert condition to FEEL
                feel_expr = self._condition_to_feel(condition_map[input_var.name], input_var.name)
                text_elem.text = feel_expr
            else:
                # No condition for this input, use wildcard
                text_elem.text = '-'

            entries.append(entry)

        return entries

    def _create_output_entries(self, rule: Rule, outputs: list) -> list:
        """Create output entry elements for rule."""
        entries = []

        # Map conclusions to outputs
        conclusion_map = {}
        for conclusion in rule.conclusions:
            conclusion_map[conclusion.variable.name] = conclusion

        # Create entry for each output
        for output_var in outputs:
            entry = etree.Element('outputEntry')
            text_elem = etree.SubElement(entry, 'text')

            if output_var.name in conclusion_map:
                # Convert conclusion value to FEEL
                conclusion = conclusion_map[output_var.name]
                text_elem.text = self._value_to_feel(conclusion.value)
            else:
                # Default: true (predicate succeeds)
                text_elem.text = 'true'

            entries.append(entry)

        return entries

    def _extract_variable_from_condition(self, condition: Condition) -> Optional[str]:
        """Extract the primary variable name from a condition."""
        expr = condition.expression
        if len(expr.operands) > 0:
            first_op = expr.operands[0]
            if isinstance(first_op, Variable):
                return first_op.name
        return None

    def _condition_to_feel(self, condition: Condition, var_name: str) -> str:
        """Convert condition to FEEL expression for input entry.

        For input entries, we want the test expression (e.g., '>= 650')
        rather than the full comparison (e.g., 'Score >= 650').
        """
        expr = condition.expression

        # Handle comparison operators
        if expr.operator in [OperatorType.GTE, OperatorType.LTE, OperatorType.GT,
                             OperatorType.LT, OperatorType.EQ, OperatorType.NE]:
            if len(expr.operands) == 2:
                left, right = expr.operands[0], expr.operands[1]

                # If left is the variable, return "op right"
                if isinstance(left, Variable) and left.name == var_name:
                    return f"{expr.operator.value} {self._operand_to_feel(right)}"
                # If right is the variable, reverse the operator
                elif isinstance(right, Variable) and right.name == var_name:
                    reversed_op = self._reverse_operator(expr.operator)
                    return f"{reversed_op.value} {self._operand_to_feel(left)}"

        # Fallback to full FEEL expression
        return condition.to_feel()

    def _reverse_operator(self, op: OperatorType) -> OperatorType:
        """Reverse comparison operator (for when variable is on right)."""
        reverse_map = {
            OperatorType.GT: OperatorType.LT,
            OperatorType.GTE: OperatorType.LTE,
            OperatorType.LT: OperatorType.GT,
            OperatorType.LTE: OperatorType.GTE,
            OperatorType.EQ: OperatorType.EQ,
            OperatorType.NE: OperatorType.NE,
        }
        return reverse_map.get(op, op)

    def _operand_to_feel(self, operand) -> str:
        """Convert operand to FEEL string."""
        if isinstance(operand, Variable):
            return operand.name
        elif isinstance(operand, Literal):
            return self._value_to_feel(operand)
        elif isinstance(operand, Expression):
            # Recursively handle nested expressions
            return f"({self._expr_to_feel(operand)})"
        return str(operand)

    def _expr_to_feel(self, expr: Expression) -> str:
        """Convert expression to FEEL."""
        if expr.operator in [OperatorType.AND, OperatorType.OR]:
            parts = [self._operand_to_feel(op) for op in expr.operands]
            op_str = " and " if expr.operator == OperatorType.AND else " or "
            return op_str.join(parts)
        elif len(expr.operands) == 2:
            left = self._operand_to_feel(expr.operands[0])
            right = self._operand_to_feel(expr.operands[1])
            return f"{left} {expr.operator.value} {right}"
        return ""

    def _value_to_feel(self, value) -> str:
        """Convert value to FEEL string."""
        if isinstance(value, Literal):
            if value.data_type == DataType.STRING:
                return f'"{value.value}"'
            elif value.data_type == DataType.BOOLEAN:
                return str(value.value).lower()
            else:
                return str(value.value)
        elif isinstance(value, Expression):
            return self._expr_to_feel(value)
        return str(value)

    def _datatype_to_feel(self, data_type: DataType) -> str:
        """Convert IR data type to FEEL type."""
        type_map = {
            DataType.STRING: 'string',
            DataType.NUMBER: 'number',
            DataType.BOOLEAN: 'boolean',
            DataType.DATE: 'date',
            DataType.ATOM: 'string',
        }
        return type_map.get(data_type, 'string')

    def _format_name(self, name: str) -> str:
        """Format name for display (convert snake_case to Title Case)."""
        return ' '.join(word.capitalize() for word in name.split('_'))
