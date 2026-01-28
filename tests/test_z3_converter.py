"""
Tests for Z3 SMT-LIB conversion.

Tests Z3 <-> DMN bidirectional conversion.
"""

import pytest
import os
from pathlib import Path

from dmn_prolog_converter.converter import PrologDMNConverter
from dmn_prolog_converter.parser.z3_parser import Z3Parser
from dmn_prolog_converter.generator.z3_generator import Z3Generator


class TestZ3Parser:
    """Test Z3 SMT-LIB parser."""

    def test_parse_simple_z3(self):
        """Test parsing simple Z3 code."""
        z3_code = """
        ; Simple Z3 example
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 100))
        (assert (= y 35))
        """

        parser = Z3Parser()
        model = parser.parse(z3_code)

        assert model is not None
        assert len(model.decisions) == 1
        assert len(model.decisions[0].inputs) == 2

    def test_parse_tax_bracket(self):
        """Test parsing tax bracket Z3 file."""
        test_dir = Path(__file__).parent
        z3_file = test_dir / "examples" / "tax_bracket.smt2"

        if not z3_file.exists():
            pytest.skip("tax_bracket.smt2 not found")

        parser = Z3Parser()
        model = parser.parse_file(str(z3_file))

        assert model is not None
        assert len(model.decisions) >= 1
        decision = model.decisions[0]
        # Income is input, TaxRate is output (in conclusions)
        assert len(decision.inputs) >= 1  # At least Income
        assert len(decision.outputs) >= 1  # At least TaxRate

    def test_parse_comparisons(self):
        """Test parsing comparison operators."""
        z3_code = """
        (declare-const a Int)
        (declare-const b Int)
        (assert (> a 10))
        (assert (<= b 20))
        (assert (= a b))
        """

        parser = Z3Parser()
        model = parser.parse(z3_code)

        assert model is not None
        decision = model.decisions[0]
        assert len(decision.rules) >= 1

    def test_parse_logical_operators(self):
        """Test parsing logical operators (and, or, not)."""
        z3_code = """
        (declare-const x Int)
        (declare-const y Int)
        (assert (and (>= x 50) (< x 100)))
        (assert (or (= y 1) (= y 2)))
        """

        parser = Z3Parser()
        model = parser.parse(z3_code)

        assert model is not None

    def test_parse_types(self):
        """Test parsing different types."""
        z3_code = """
        (declare-const num Int)
        (declare-const flag Bool)
        (declare-const name String)
        (assert (= num 42))
        (assert (= flag true))
        """

        parser = Z3Parser()
        model = parser.parse(z3_code)

        assert model is not None
        decision = model.decisions[0]
        # Check that variables with different types are parsed
        var_names = [v.name for v in decision.inputs]
        assert 'num' in var_names
        assert 'flag' in var_names


class TestZ3Generator:
    """Test Z3 SMT-LIB generator."""

    def test_generate_simple_z3(self):
        """Test generating simple Z3 code."""
        from dmn_prolog_converter.ir.intermediate import (
            DecisionModel, Decision, Rule, Condition, Conclusion,
            Variable, Literal, Expression, DataType, OperatorType
        )

        # Create simple decision model
        income = Variable(name="Income", data_type=DataType.NUMBER)
        tax_rate = Variable(name="TaxRate", data_type=DataType.NUMBER)

        condition = Condition(
            expression=Expression(
                operator=OperatorType.GTE,
                operands=[income, Literal(value=100000, data_type=DataType.NUMBER)]
            )
        )

        conclusion = Conclusion(
            variable=tax_rate,
            value=Literal(value=35, data_type=DataType.NUMBER)
        )

        rule = Rule(conditions=[condition], conclusions=[conclusion])
        decision = Decision(
            name="tax_bracket",
            inputs=[income],
            outputs=[tax_rate],
            rules=[rule]
        )

        model = DecisionModel(name="TaxModel", decisions=[decision])

        # Generate Z3
        generator = Z3Generator()
        z3_code = generator.generate(model)

        assert z3_code is not None
        assert "(declare-const Income Int)" in z3_code
        assert "(declare-const TaxRate Int)" in z3_code
        assert "(assert" in z3_code
        assert ">=" in z3_code

    def test_generate_all_operators(self):
        """Test generating all supported operators."""
        from dmn_prolog_converter.ir.intermediate import (
            DecisionModel, Decision, Rule, Condition,
            Variable, Literal, Expression, DataType, OperatorType
        )

        x = Variable(name="x", data_type=DataType.NUMBER)
        y = Variable(name="y", data_type=DataType.NUMBER)

        operators = [
            OperatorType.EQ,
            OperatorType.NE,
            OperatorType.GT,
            OperatorType.GTE,
            OperatorType.LT,
            OperatorType.LTE,
        ]

        rules = []
        for op in operators:
            condition = Condition(
                expression=Expression(
                    operator=op,
                    operands=[x, Literal(value=10, data_type=DataType.NUMBER)]
                )
            )
            rule = Rule(conditions=[condition], conclusions=[])
            rules.append(rule)

        decision = Decision(
            name="test",
            inputs=[x, y],
            outputs=[],
            rules=rules
        )

        model = DecisionModel(name="TestModel", decisions=[decision])

        generator = Z3Generator()
        z3_code = generator.generate(model)

        assert z3_code is not None
        # Check that operators are present
        assert "=" in z3_code
        assert ">" in z3_code
        assert ">=" in z3_code
        assert "<" in z3_code
        assert "<=" in z3_code

    def test_generate_boolean_types(self):
        """Test generating boolean variables."""
        from dmn_prolog_converter.ir.intermediate import (
            DecisionModel, Decision, Rule, Condition,
            Variable, Literal, Expression, DataType, OperatorType
        )

        flag = Variable(name="isApproved", data_type=DataType.BOOLEAN)

        condition = Condition(
            expression=Expression(
                operator=OperatorType.EQ,
                operands=[flag, Literal(value=True, data_type=DataType.BOOLEAN)]
            )
        )

        rule = Rule(conditions=[condition], conclusions=[])
        decision = Decision(
            name="test",
            inputs=[flag],
            outputs=[],
            rules=[rule]
        )

        model = DecisionModel(name="TestModel", decisions=[decision])

        generator = Z3Generator()
        z3_code = generator.generate(model)

        assert "(declare-const isApproved Bool)" in z3_code
        assert "true" in z3_code


class TestZ3Converter:
    """Test full Z3 <-> DMN conversion."""

    def test_z3_to_dmn_conversion(self, tmp_path):
        """Test Z3 -> DMN conversion."""
        converter = PrologDMNConverter()

        # Create test Z3 file
        z3_file = tmp_path / "test.smt2"
        z3_content = """
        ; Tax bracket
        (declare-const Income Int)
        (declare-const TaxRate Int)
        (assert (>= Income 100000))
        (assert (= TaxRate 35))
        """
        z3_file.write_text(z3_content)

        dmn_file = tmp_path / "test.dmn"

        # Convert
        result = converter.z3_to_dmn(str(z3_file), str(dmn_file), validate=False)

        assert dmn_file.exists()
        dmn_content = dmn_file.read_text()
        assert "<?xml" in dmn_content
        assert "definitions" in dmn_content

    def test_dmn_to_z3_conversion(self, tmp_path):
        """Test DMN -> Z3 conversion."""
        converter = PrologDMNConverter()

        # First create a Prolog file and convert to DMN
        prolog_file = tmp_path / "test.pl"
        prolog_content = """
        tax_bracket(Income, TaxRate) :-
            Income >= 100000,
            TaxRate = 35.
        """
        prolog_file.write_text(prolog_content)

        dmn_file = tmp_path / "test.dmn"
        converter.prolog_to_dmn(str(prolog_file), str(dmn_file), validate=False)

        # Now convert DMN to Z3
        z3_file = tmp_path / "test.smt2"
        result = converter.dmn_to_z3(str(dmn_file), str(z3_file))

        assert z3_file.exists()
        z3_content = z3_file.read_text()
        assert "(declare-const" in z3_content
        assert "(assert" in z3_content

    def test_prolog_to_z3_conversion(self, tmp_path):
        """Test Prolog -> Z3 conversion."""
        converter = PrologDMNConverter()

        prolog_file = tmp_path / "test.pl"
        prolog_content = """
        eligible(Credit, Result) :-
            Credit >= 650,
            Result = approved.
        """
        prolog_file.write_text(prolog_content)

        z3_file = tmp_path / "test.smt2"
        result = converter.prolog_to_z3(str(prolog_file), str(z3_file))

        assert z3_file.exists()
        z3_content = z3_file.read_text()
        assert "(declare-const Credit" in z3_content
        assert "(declare-const Result" in z3_content
        assert ">=" in z3_content

    def test_z3_to_prolog_conversion(self, tmp_path):
        """Test Z3 -> Prolog conversion."""
        converter = PrologDMNConverter()

        z3_file = tmp_path / "test.smt2"
        z3_content = """
        (declare-const Credit Int)
        (declare-const Result String)
        (assert (>= Credit 650))
        (assert (= Result "approved"))
        """
        z3_file.write_text(z3_content)

        prolog_file = tmp_path / "test.pl"
        result = converter.z3_to_prolog(str(z3_file), str(prolog_file))

        assert prolog_file.exists()
        prolog_content = prolog_file.read_text()
        # Check basic Prolog structure
        assert ":-" in prolog_content

    def test_z3_roundtrip(self, tmp_path):
        """Test Z3 -> DMN -> Z3 roundtrip."""
        converter = PrologDMNConverter()

        # Original Z3
        z3_file = tmp_path / "original.smt2"
        z3_content = """
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 100))
        (assert (= y 35))
        """
        z3_file.write_text(z3_content)

        # Convert to DMN
        dmn_file = tmp_path / "intermediate.dmn"
        converter.z3_to_dmn(str(z3_file), str(dmn_file), validate=False)

        # Convert back to Z3
        z3_file2 = tmp_path / "roundtrip.smt2"
        converter.dmn_to_z3(str(dmn_file), str(z3_file2))

        assert z3_file2.exists()
        z3_content2 = z3_file2.read_text()
        # Check that basic structure is preserved
        assert "(declare-const" in z3_content2
        assert "(assert" in z3_content2

    def test_example_files(self):
        """Test conversion of example files."""
        test_dir = Path(__file__).parent
        examples_dir = test_dir / "examples"

        z3_files = list(examples_dir.glob("*.smt2"))

        if not z3_files:
            pytest.skip("No Z3 example files found")

        converter = PrologDMNConverter()

        for z3_file in z3_files:
            # Parse Z3 file
            parser = Z3Parser()
            model = parser.parse_file(str(z3_file))

            assert model is not None
            assert len(model.decisions) >= 1


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
