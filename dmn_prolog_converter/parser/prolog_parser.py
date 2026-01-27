r"""
Prolog Parser - Converts restricted Prolog to Intermediate Representation.

Supports:
- Horn clauses: head :- body.
- Simple predicates
- Comparison operators: =, >, <, >=, =<, ==, \=
- Arithmetic operators: +, -, *, /
- Logical conjunction (,)
- Facts and rules
"""

from lark import Lark, Transformer, v_args
from typing import List, Union
import re

from ..ir.intermediate import (
    DecisionModel, Decision, Rule, Condition, Conclusion,
    Variable, Literal, Expression, DataType, OperatorType
)


# Prolog grammar for restricted subset
PROLOG_GRAMMAR = r"""
    start: statement+

    statement: fact | rule

    fact: atom_head "."
    rule: atom_head ":-" body "."

    atom_head: ATOM "(" args? ")"

    body: goal ("," goal)*

    goal: comparison | pred_call

    pred_call: ATOM "(" args? ")"

    args: expr ("," expr)*

    expr: arithmetic
        | simple_term

    simple_term: variable | number | string | atom | pred_call | "(" expr ")"

    comparison: expr OP expr

    arithmetic: simple_term ARITH simple_term

    OP: ">=" | "=<" | ">" | "<" | "==" | "\\=" | "="
    ARITH: "+" | "-" | "*" | "/"

    number: NUMBER
    string: STRING
    atom: ATOM
    variable: VARIABLE

    ATOM: /[a-z][a-z0-9_]*/
    VARIABLE: /[A-Z][a-zA-Z0-9_]*/
    NUMBER: /-?\d+\.\d+/ | /-?\d+/
    STRING: /"[^"]*"/ | /'[^']*'/

    COMMENT: /%[^\n]*/

    %import common.WS
    %ignore WS
    %ignore COMMENT
"""


class PrologTransformer(Transformer):
    """Transform Lark parse tree into IR."""

    def __init__(self):
        super().__init__()
        self.decisions = {}
        self.current_variables = {}

    def start(self, items):
        """Top-level: collect all decisions."""
        model = DecisionModel(
            name="PrologModel",
            decisions=list(self.decisions.values())
        )
        return model

    def atom_head(self, items):
        """Head of fact or rule."""
        name = str(items[0])
        args = items[1] if len(items) > 1 else []
        return {'name': name, 'args': args}

    def fact(self, items):
        """Fact: predicate without body."""
        head = items[0]
        pred_name = head['name']

        # Create decision if not exists
        if pred_name not in self.decisions:
            decision = Decision(
                name=pred_name,
                inputs=[],
                outputs=[],
                rules=[]
            )
            self.decisions[pred_name] = decision

        # Add as a rule with no conditions
        rule = Rule(
            conditions=[],
            conclusions=[]
        )

        # Infer variables from arguments
        for i, arg in enumerate(head.get('args', [])):
            var = self._create_variable(f"arg{i}", arg)
            if var:
                conclusion = Conclusion(
                    variable=var,
                    value=self._term_to_literal(arg)
                )
                rule.conclusions.append(conclusion)

        self.decisions[pred_name].rules.append(rule)
        return rule

    def rule(self, items):
        """Rule: predicate :- body."""
        head = items[0]
        body = items[1]

        pred_name = head['name']

        # Extract all variables from head
        head_var_names = []
        for arg in head.get('args', []):
            if isinstance(arg, str) and arg[0].isupper():
                head_var_names.append(arg)

        # Analyze body to determine inputs vs outputs
        input_vars = set()
        output_assignments = {}  # var_name -> value

        for goal in body:
            if isinstance(goal, dict) and goal.get('type') == 'comparison':
                left = goal['left']
                right = goal['right']
                op = goal['operator']

                # If it's an assignment (=), mark as output
                if op == OperatorType.EQ:
                    if isinstance(left, str) and left in head_var_names:
                        output_assignments[left] = right
                    elif isinstance(right, str) and right in head_var_names:
                        output_assignments[right] = left
                else:
                    # Regular comparison - variables are inputs
                    if isinstance(left, str) and left in head_var_names:
                        input_vars.add(left)
                    if isinstance(right, str) and right in head_var_names:
                        input_vars.add(right)

        # Create decision if not exists
        if pred_name not in self.decisions:
            inputs = [self._create_variable(name) for name in head_var_names if name in input_vars]
            outputs = [self._create_variable(name) for name in head_var_names if name in output_assignments]

            decision = Decision(
                name=pred_name,
                inputs=inputs,
                outputs=outputs,
                rules=[]
            )
            self.decisions[pred_name] = decision
        else:
            # Update decision inputs/outputs if needed
            decision = self.decisions[pred_name]
            for name in input_vars:
                var = self._create_variable(name)
                if var and var not in decision.inputs:
                    decision.inputs.append(var)
            for name in output_assignments.keys():
                var = self._create_variable(name)
                if var and var not in decision.outputs:
                    decision.outputs.append(var)

        # Extract conditions (non-assignment comparisons)
        conditions = []
        conclusions = []

        for goal in body:
            if isinstance(goal, dict) and goal.get('type') == 'comparison':
                op = goal['operator']
                if op == OperatorType.EQ:
                    # This is an assignment/conclusion
                    left = goal['left']
                    right = goal['right']

                    # Determine which side is the variable
                    if isinstance(left, str) and left in output_assignments:
                        var = self._create_variable(left)
                        value = self._term_to_literal(right)
                        conclusions.append(Conclusion(variable=var, value=value))
                    elif isinstance(right, str) and right in output_assignments:
                        var = self._create_variable(right)
                        value = self._term_to_literal(left)
                        conclusions.append(Conclusion(variable=var, value=value))
                else:
                    # This is a condition
                    cond = self._create_condition(goal)
                    if cond:
                        conditions.append(cond)

        # Create rule
        rule = Rule(
            conditions=conditions,
            conclusions=conclusions
        )

        self.decisions[pred_name].rules.append(rule)
        return rule

    def body(self, items):
        """Body: list of goals."""
        return items

    def goal(self, items):
        """Goal: comparison, predicate, or arithmetic."""
        return items[0]

    def pred_call(self, items):
        """Predicate call: name(args)."""
        name = str(items[0])
        args = items[1] if len(items) > 1 else []
        return {'type': 'pred_call', 'name': name, 'args': args}

    def args(self, items):
        """Arguments list."""
        return items

    def expr(self, items):
        """Expression: arithmetic or simple term."""
        return items[0]

    def simple_term(self, items):
        """Simple term: variable, literal, or predicate."""
        return items[0]

    def comparison(self, items):
        """Comparison: term op term."""
        left, op_token, right = items[0], items[1], items[2]

        op_map = {
            '>=': OperatorType.GTE,
            '=<': OperatorType.LTE,
            '>': OperatorType.GT,
            '<': OperatorType.LT,
            '==': OperatorType.EQ,
            '=': OperatorType.EQ,
            '\\=': OperatorType.NE,
        }
        op = op_map.get(str(op_token), OperatorType.EQ)

        return {
            'type': 'comparison',
            'operator': op,
            'left': left,
            'right': right
        }

    def arithmetic(self, items):
        """Arithmetic: term op term."""
        left, op_token, right = items[0], items[1], items[2]

        op_map = {
            '+': OperatorType.ADD,
            '-': OperatorType.SUB,
            '*': OperatorType.MUL,
            '/': OperatorType.DIV,
        }
        op = op_map.get(str(op_token), OperatorType.ADD)

        return {
            'type': 'arithmetic',
            'operator': op,
            'left': left,
            'right': right
        }

    def number(self, items):
        """Number literal."""
        num_str = str(items[0])
        if '.' in num_str:
            return float(num_str)
        return int(num_str)

    def string(self, items):
        """String literal."""
        return str(items[0])[1:-1]  # Remove quotes

    def atom(self, items):
        """Atom literal."""
        return str(items[0])

    def variable(self, items):
        """Variable."""
        return str(items[0])

    def _create_variable(self, name: str, value=None) -> Variable:
        """Create or retrieve variable."""
        if isinstance(name, dict):
            # Handle complex terms
            return None

        if name not in self.current_variables:
            data_type = self._infer_type(value)
            var = Variable(name=name, data_type=data_type)
            self.current_variables[name] = var
        return self.current_variables[name]

    def _infer_type(self, value) -> DataType:
        """Infer data type from value."""
        if isinstance(value, bool):
            return DataType.BOOLEAN
        elif isinstance(value, int) or isinstance(value, float):
            return DataType.NUMBER
        elif isinstance(value, str):
            if value.isupper() and value[0].isupper():
                return DataType.ATOM  # Variable
            return DataType.STRING
        return DataType.ATOM

    def _term_to_literal(self, term) -> Literal:
        """Convert term to literal."""
        if isinstance(term, (int, float)):
            return Literal(value=term, data_type=DataType.NUMBER)
        elif isinstance(term, bool):
            return Literal(value=term, data_type=DataType.BOOLEAN)
        elif isinstance(term, str):
            return Literal(value=term, data_type=DataType.ATOM)
        else:
            return Literal(value=str(term), data_type=DataType.STRING)

    def _create_condition(self, comp_dict) -> Condition:
        """Create condition from comparison dictionary."""
        left = comp_dict['left']
        right = comp_dict['right']
        op = comp_dict['operator']

        left_operand = self._term_to_operand(left)
        right_operand = self._term_to_operand(right)

        expr = Expression(
            operator=op,
            operands=[left_operand, right_operand]
        )

        return Condition(expression=expr)

    def _term_to_operand(self, term):
        """Convert term to expression operand."""
        if isinstance(term, str):
            if term[0].isupper():
                # Variable
                return self._create_variable(term)
            else:
                # Atom
                return Literal(value=term, data_type=DataType.ATOM)
        elif isinstance(term, (int, float)):
            return Literal(value=term, data_type=DataType.NUMBER)
        elif isinstance(term, dict):
            if term.get('type') == 'arithmetic':
                left = self._term_to_operand(term['left'])
                right = self._term_to_operand(term['right'])
                return Expression(
                    operator=term['operator'],
                    operands=[left, right]
                )
        return Literal(value=str(term), data_type=DataType.STRING)


class PrologParser:
    """Main Prolog parser class."""

    def __init__(self):
        self.parser = Lark(PROLOG_GRAMMAR, parser='lalr')
        self.transformer = PrologTransformer()

    def parse(self, prolog_code: str) -> DecisionModel:
        """Parse Prolog code into IR."""
        tree = self.parser.parse(prolog_code)
        model = self.transformer.transform(tree)
        return model

    def parse_file(self, filepath: str) -> DecisionModel:
        """Parse Prolog file into IR."""
        with open(filepath, 'r', encoding='utf-8') as f:
            prolog_code = f.read()
        return self.parse(prolog_code)
