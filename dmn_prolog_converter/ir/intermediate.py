"""
Intermediate Representation (IR) for Prolog-DMN conversion.

This IR serves as the pivot format between Prolog and DMN, capturing:
- Decision structures
- Rules and conditions
- Input/output variables
- Data types and constraints
"""

from dataclasses import dataclass, field
from typing import List, Dict, Any, Optional, Union
from enum import Enum


class DataType(Enum):
    """Supported data types."""
    STRING = "string"
    NUMBER = "number"
    BOOLEAN = "boolean"
    DATE = "date"
    ATOM = "atom"  # Prolog atom


class OperatorType(Enum):
    """Comparison and logical operators."""
    # Comparison
    EQ = "=="
    NE = "!="
    GT = ">"
    GTE = ">="
    LT = "<"
    LTE = "<="
    # Logical
    AND = "and"
    OR = "or"
    NOT = "not"
    # Arithmetic
    ADD = "+"
    SUB = "-"
    MUL = "*"
    DIV = "/"


@dataclass
class Variable:
    """Represents a variable in the decision."""
    name: str
    data_type: DataType
    description: Optional[str] = None


@dataclass
class Literal:
    """Represents a literal value."""
    value: Union[str, int, float, bool]
    data_type: DataType


@dataclass
class Expression:
    """Represents an expression (comparison, logical, arithmetic)."""
    operator: OperatorType
    operands: List[Union['Expression', Variable, Literal]]


@dataclass
class Condition:
    """Represents a condition in a rule (antecedent)."""
    expression: Expression

    def to_feel(self) -> str:
        """Convert to FEEL expression."""
        return self._expr_to_feel(self.expression)

    def _expr_to_feel(self, expr: Union[Expression, Variable, Literal]) -> str:
        """Recursively convert expression to FEEL."""
        if isinstance(expr, Variable):
            return expr.name
        elif isinstance(expr, Literal):
            if expr.data_type == DataType.STRING:
                return f'"{expr.value}"'
            elif expr.data_type == DataType.BOOLEAN:
                return str(expr.value).lower()
            else:
                return str(expr.value)
        elif isinstance(expr, Expression):
            if expr.operator in [OperatorType.AND, OperatorType.OR]:
                parts = [self._expr_to_feel(op) for op in expr.operands]
                op_str = " and " if expr.operator == OperatorType.AND else " or "
                return f"({op_str.join(parts)})"
            elif expr.operator == OperatorType.NOT:
                return f"not({self._expr_to_feel(expr.operands[0])})"
            elif len(expr.operands) == 2:
                left = self._expr_to_feel(expr.operands[0])
                right = self._expr_to_feel(expr.operands[1])
                return f"{left} {expr.operator.value} {right}"
        return ""


@dataclass
class Conclusion:
    """Represents a conclusion in a rule (consequent)."""
    variable: Variable
    value: Union[Literal, Expression]


@dataclass
class Rule:
    """Represents a single rule (Prolog clause or DMN table row)."""
    id: Optional[str] = None
    conditions: List[Condition] = field(default_factory=list)
    conclusions: List[Conclusion] = field(default_factory=list)
    description: Optional[str] = None
    annotation: Optional[str] = None  # For DMN annotations


@dataclass
class Decision:
    """Represents a decision (Prolog predicate or DMN decision table)."""
    name: str
    inputs: List[Variable]
    outputs: List[Variable]
    rules: List[Rule]
    description: Optional[str] = None
    hit_policy: str = "UNIQUE"  # DMN hit policy (UNIQUE, FIRST, etc.)

    def to_prolog_predicate(self) -> str:
        """Get the Prolog predicate signature."""
        args = [v.name for v in self.inputs + self.outputs]
        return f"{self.name}({', '.join(args)})"


@dataclass
class DecisionModel:
    """Top-level model containing multiple decisions."""
    name: str
    namespace: str = "http://example.org/dmn"
    decisions: List[Decision] = field(default_factory=list)
    metadata: Dict[str, Any] = field(default_factory=dict)

    def get_decision(self, name: str) -> Optional[Decision]:
        """Get decision by name."""
        for decision in self.decisions:
            if decision.name == name:
                return decision
        return None
