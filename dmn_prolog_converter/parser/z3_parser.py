"""
Z3 Parser - Converts Z3 SMT-LIB format to Intermediate Representation.

Supports:
- Variable declarations (declare-const, declare-fun)
- Assertions (assert)
- Comparison operators (=, >, <, >=, <=, distinct)
- Arithmetic operators (+, -, *, /)
- Logical operators (and, or, not)
- Types: Int, Bool, Real, String
"""

import re
from typing import List, Dict, Any, Optional, Union

from ..ir.intermediate import (
    DecisionModel, Decision, Rule, Condition, Conclusion,
    Variable, Literal, Expression, DataType, OperatorType
)


class Z3Parser:
    """Parse Z3 SMT-LIB format into IR."""

    def __init__(self):
        self.variables: Dict[str, Variable] = {}
        self.assertions: List[Any] = []

    def parse(self, z3_code: str) -> DecisionModel:
        """Parse Z3 code into IR."""
        # Remove comments
        z3_code = self._remove_comments(z3_code)

        # Tokenize
        tokens = self._tokenize(z3_code)

        # Parse tokens
        expressions = self._parse_tokens(tokens)

        # Extract declarations and assertions
        for expr in expressions:
            if isinstance(expr, list) and len(expr) > 0:
                cmd = expr[0]
                if cmd == 'declare-const':
                    self._process_declaration(expr)
                elif cmd == 'declare-fun':
                    self._process_function_declaration(expr)
                elif cmd == 'assert':
                    self._process_assertion(expr[1])

        # Build decision from assertions
        decision = self._build_decision()

        model = DecisionModel(
            name="Z3Model",
            decisions=[decision] if decision else []
        )

        return model

    def parse_file(self, filepath: str) -> DecisionModel:
        """Parse Z3 file into IR."""
        with open(filepath, 'r', encoding='utf-8') as f:
            z3_code = f.read()
        return self.parse(z3_code)

    def _remove_comments(self, code: str) -> str:
        """Remove SMT-LIB comments."""
        # Remove single-line comments (;)
        lines = []
        for line in code.split('\n'):
            comment_pos = line.find(';')
            if comment_pos >= 0:
                line = line[:comment_pos]
            lines.append(line)
        return '\n'.join(lines)

    def _tokenize(self, code: str) -> List[str]:
        """Tokenize SMT-LIB code."""
        # Replace parens with spaces for tokenization
        code = code.replace('(', ' ( ').replace(')', ' ) ')

        # Split on whitespace
        tokens = code.split()

        return tokens

    def _parse_tokens(self, tokens: List[str]) -> List[Any]:
        """Parse tokens into S-expressions."""
        expressions = []
        stack = []
        current = []

        for token in tokens:
            if token == '(':
                stack.append(current)
                current = []
            elif token == ')':
                if stack:
                    completed = current
                    current = stack.pop()
                    current.append(completed)
                else:
                    expressions.append(current)
                    current = []
            else:
                current.append(token)

        if current:
            expressions.append(current)

        return expressions

    def _process_declaration(self, expr: List) -> None:
        """Process variable declaration: (declare-const x Int)."""
        if len(expr) < 3:
            return

        var_name = expr[1]
        var_type = expr[2]

        data_type = self._z3_type_to_datatype(var_type)
        var = Variable(name=var_name, data_type=data_type)
        self.variables[var_name] = var

    def _process_function_declaration(self, expr: List) -> None:
        """Process function declaration: (declare-fun f (Int) Bool)."""
        if len(expr) < 4:
            return

        func_name = expr[1]
        # For now, treat as variable
        return_type = expr[-1]

        data_type = self._z3_type_to_datatype(return_type)
        var = Variable(name=func_name, data_type=data_type)
        self.variables[func_name] = var

    def _process_assertion(self, expr: Any) -> None:
        """Process assertion: (assert (>= x 100))."""
        self.assertions.append(expr)

    def _build_decision(self) -> Optional[Decision]:
        """Build decision from assertions."""
        if not self.assertions:
            return None

        # Group assertions into rules
        # For now, create one rule per assertion combination
        rules = []

        # Separate conditions from conclusions
        conditions = []
        conclusions = []

        for assertion in self.assertions:
            if isinstance(assertion, list):
                cond = self._parse_condition(assertion)
                if cond:
                    conditions.append(cond)

        # Create a rule
        if conditions:
            rule = Rule(conditions=conditions, conclusions=conclusions)
            rules.append(rule)

        # Determine inputs and outputs
        inputs = list(self.variables.values())
        outputs = []

        decision = Decision(
            name="z3_decision",
            inputs=inputs,
            outputs=outputs,
            rules=rules
        )

        return decision

    def _parse_condition(self, expr: List) -> Optional[Condition]:
        """Parse condition from S-expression."""
        if not isinstance(expr, list) or len(expr) == 0:
            return None

        op = expr[0]

        # Binary comparison operators
        if op in ['=', '>', '<', '>=', '<=', 'distinct']:
            if len(expr) >= 3:
                left = self._parse_term(expr[1])
                right = self._parse_term(expr[2])

                op_type = self._z3_op_to_operator(op)

                expression = Expression(
                    operator=op_type,
                    operands=[left, right]
                )

                return Condition(expression=expression)

        # Logical operators
        elif op in ['and', 'or', 'not']:
            if op == 'not':
                if len(expr) >= 2:
                    inner = self._parse_condition(expr[1])
                    if inner:
                        expression = Expression(
                            operator=OperatorType.NOT,
                            operands=[inner.expression]
                        )
                        return Condition(expression=expression)
            else:
                # and/or: combine multiple conditions
                sub_conditions = []
                for sub_expr in expr[1:]:
                    sub_cond = self._parse_condition(sub_expr)
                    if sub_cond:
                        sub_conditions.append(sub_cond.expression)

                if len(sub_conditions) >= 2:
                    op_type = OperatorType.AND if op == 'and' else OperatorType.OR
                    expression = Expression(
                        operator=op_type,
                        operands=sub_conditions
                    )
                    return Condition(expression=expression)

        # Arithmetic wrapped in comparison
        elif op in ['+', '-', '*', '/']:
            # This is likely part of a larger expression
            return None

        return None

    def _parse_term(self, term: Any) -> Union[Variable, Literal, Expression]:
        """Parse a term (variable, literal, or expression)."""
        if isinstance(term, str):
            # Check if it's a variable
            if term in self.variables:
                return self.variables[term]

            # Check if it's a number
            try:
                if '.' in term:
                    return Literal(value=float(term), data_type=DataType.NUMBER)
                else:
                    return Literal(value=int(term), data_type=DataType.NUMBER)
            except ValueError:
                pass

            # Check if it's a boolean
            if term.lower() == 'true':
                return Literal(value=True, data_type=DataType.BOOLEAN)
            elif term.lower() == 'false':
                return Literal(value=False, data_type=DataType.BOOLEAN)

            # Treat as string literal
            return Literal(value=term, data_type=DataType.STRING)

        elif isinstance(term, list) and len(term) > 0:
            # Arithmetic expression
            op = term[0]
            if op in ['+', '-', '*', '/']:
                if len(term) >= 3:
                    left = self._parse_term(term[1])
                    right = self._parse_term(term[2])

                    op_type = self._z3_arith_to_operator(op)

                    return Expression(
                        operator=op_type,
                        operands=[left, right]
                    )

        return Literal(value=str(term), data_type=DataType.STRING)

    def _z3_type_to_datatype(self, z3_type: str) -> DataType:
        """Convert Z3 type to IR DataType."""
        type_map = {
            'Int': DataType.NUMBER,
            'Real': DataType.NUMBER,
            'Bool': DataType.BOOLEAN,
            'String': DataType.STRING,
        }
        return type_map.get(z3_type, DataType.STRING)

    def _z3_op_to_operator(self, z3_op: str) -> OperatorType:
        """Convert Z3 operator to IR OperatorType."""
        op_map = {
            '=': OperatorType.EQ,
            '>': OperatorType.GT,
            '<': OperatorType.LT,
            '>=': OperatorType.GTE,
            '<=': OperatorType.LTE,
            'distinct': OperatorType.NE,
        }
        return op_map.get(z3_op, OperatorType.EQ)

    def _z3_arith_to_operator(self, z3_op: str) -> OperatorType:
        """Convert Z3 arithmetic operator to IR OperatorType."""
        op_map = {
            '+': OperatorType.ADD,
            '-': OperatorType.SUB,
            '*': OperatorType.MUL,
            '/': OperatorType.DIV,
        }
        return op_map.get(z3_op, OperatorType.ADD)
