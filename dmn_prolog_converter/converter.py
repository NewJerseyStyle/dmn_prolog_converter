"""
Main Converter API - Bidirectional Prolog <-> DMN <-> Z3 conversion.

Usage:
    converter = PrologDMNConverter()

    # Prolog -> DMN
    dmn_xml = converter.prolog_to_dmn("input.pl")

    # DMN -> Prolog
    prolog_code = converter.dmn_to_prolog("input.dmn")

    # Z3 -> DMN
    dmn_xml = converter.z3_to_dmn("input.smt2")

    # DMN -> Z3
    z3_code = converter.dmn_to_z3("input.dmn")
"""

from pathlib import Path
from .parser.prolog_parser import PrologParser
from .parser.dmn_parser import DMNParser
from .parser.z3_parser import Z3Parser
from .generator.dmn_generator import DMNGenerator
from .generator.prolog_generator import PrologGenerator
from .generator.z3_generator import Z3Generator
from .ir.intermediate import DecisionModel
from .validation.dmn_validator import DMNValidator
from .execution.dmn_executor import DMNExecutor, ExecutionTester


class PrologDMNConverter:
    """Bidirectional converter between Prolog, DMN, and Z3."""

    def __init__(self):
        self.prolog_parser = PrologParser()
        self.dmn_parser = DMNParser()
        self.z3_parser = Z3Parser()
        self.dmn_generator = DMNGenerator()
        self.prolog_generator = PrologGenerator()
        self.z3_generator = Z3Generator()
        self.validator = DMNValidator()
        self.executor = DMNExecutor()
        self.tester = ExecutionTester()

    def prolog_to_dmn(self, input_path: str, output_path: str = None, validate: bool = True) -> str:
        """
        Convert Prolog file to DMN XML.

        Args:
            input_path: Path to Prolog file
            output_path: Optional output path for DMN file
            validate: Whether to validate generated DMN (default: True)

        Returns:
            DMN XML string
        """
        # Parse Prolog to IR
        model = self.prolog_parser.parse_file(input_path)

        # Generate DMN from IR
        dmn_xml = self.dmn_generator.generate(model)

        # Validate if requested
        if validate:
            is_valid, message = self.validator.validate_dmn_string(dmn_xml)
            if not is_valid:
                print(f"Warning: Generated DMN validation failed: {message}")
            else:
                print(f"[OK] DMN validation passed: {message}")

        # Save to file if output path provided
        if output_path:
            with open(output_path, 'w', encoding='utf-8') as f:
                f.write(dmn_xml)

        return dmn_xml

    def dmn_to_prolog(self, input_path: str, output_path: str = None) -> str:
        """
        Convert DMN XML file to Prolog code.

        Args:
            input_path: Path to DMN file
            output_path: Optional output path for Prolog file

        Returns:
            Prolog code string
        """
        # Parse DMN to IR
        model = self.dmn_parser.parse_file(input_path)

        # Generate Prolog from IR
        prolog_code = self.prolog_generator.generate(model)

        # Save to file if output path provided
        if output_path:
            with open(output_path, 'w', encoding='utf-8') as f:
                f.write(prolog_code)

        return prolog_code

    def prolog_string_to_dmn(self, prolog_code: str) -> str:
        """Convert Prolog code string to DMN XML string."""
        model = self.prolog_parser.parse(prolog_code)
        return self.dmn_generator.generate(model)

    def dmn_string_to_prolog(self, dmn_xml: str) -> str:
        """Convert DMN XML string to Prolog code string."""
        model = self.dmn_parser.parse(dmn_xml)
        return self.prolog_generator.generate(model)

    def z3_to_dmn(self, input_path: str, output_path: str = None, validate: bool = True) -> str:
        """
        Convert Z3 SMT-LIB file to DMN XML.

        Args:
            input_path: Path to Z3 file
            output_path: Optional output path for DMN file
            validate: Whether to validate generated DMN (default: True)

        Returns:
            DMN XML string
        """
        # Parse Z3 to IR
        model = self.z3_parser.parse_file(input_path)

        # Generate DMN from IR
        dmn_xml = self.dmn_generator.generate(model)

        # Validate if requested
        if validate:
            is_valid, message = self.validator.validate_dmn_string(dmn_xml)
            if not is_valid:
                print(f"Warning: Generated DMN validation failed: {message}")
            else:
                print(f"[OK] DMN validation passed: {message}")

        # Save to file if output path provided
        if output_path:
            with open(output_path, 'w', encoding='utf-8') as f:
                f.write(dmn_xml)

        return dmn_xml

    def dmn_to_z3(self, input_path: str, output_path: str = None) -> str:
        """
        Convert DMN XML file to Z3 SMT-LIB code.

        Args:
            input_path: Path to DMN file
            output_path: Optional output path for Z3 file

        Returns:
            Z3 code string
        """
        # Parse DMN to IR
        model = self.dmn_parser.parse_file(input_path)

        # Generate Z3 from IR
        z3_code = self.z3_generator.generate(model)

        # Save to file if output path provided
        if output_path:
            with open(output_path, 'w', encoding='utf-8') as f:
                f.write(z3_code)

        return z3_code

    def z3_string_to_dmn(self, z3_code: str) -> str:
        """Convert Z3 code string to DMN XML string."""
        model = self.z3_parser.parse(z3_code)
        return self.dmn_generator.generate(model)

    def dmn_string_to_z3(self, dmn_xml: str) -> str:
        """Convert DMN XML string to Z3 code string."""
        model = self.dmn_parser.parse(dmn_xml)
        return self.z3_generator.generate(model)

    def prolog_to_z3(self, input_path: str, output_path: str = None) -> str:
        """
        Convert Prolog file to Z3 SMT-LIB code.

        Args:
            input_path: Path to Prolog file
            output_path: Optional output path for Z3 file

        Returns:
            Z3 code string
        """
        # Parse Prolog to IR
        model = self.prolog_parser.parse_file(input_path)

        # Generate Z3 from IR
        z3_code = self.z3_generator.generate(model)

        # Save to file if output path provided
        if output_path:
            with open(output_path, 'w', encoding='utf-8') as f:
                f.write(z3_code)

        return z3_code

    def z3_to_prolog(self, input_path: str, output_path: str = None) -> str:
        """
        Convert Z3 SMT-LIB file to Prolog code.

        Args:
            input_path: Path to Z3 file
            output_path: Optional output path for Prolog file

        Returns:
            Prolog code string
        """
        # Parse Z3 to IR
        model = self.z3_parser.parse_file(input_path)

        # Generate Prolog from IR
        prolog_code = self.prolog_generator.generate(model)

        # Save to file if output path provided
        if output_path:
            with open(output_path, 'w', encoding='utf-8') as f:
                f.write(prolog_code)

        return prolog_code

    def validate_roundtrip(self, prolog_path: str, test_cases: list = None) -> tuple[bool, str]:
        """
        Validate that Prolog -> DMN -> Prolog conversion is consistent.

        Args:
            prolog_path: Path to original Prolog file
            test_cases: Optional list of test cases for execution testing

        Returns:
            Tuple of (is_valid, message)
        """
        try:
            # Original Prolog -> IR
            model1 = self.prolog_parser.parse_file(prolog_path)

            # IR -> DMN
            dmn_xml = self.dmn_generator.generate(model1)

            # Validate DMN
            is_valid, val_msg = self.validator.validate_dmn_string(dmn_xml)
            if not is_valid:
                return False, f"DMN validation failed: {val_msg}"

            # DMN -> IR
            model2 = self.dmn_parser.parse(dmn_xml)

            # Compare models
            if len(model1.decisions) != len(model2.decisions):
                return False, f"Decision count mismatch: {len(model1.decisions)} vs {len(model2.decisions)}"

            for d1, d2 in zip(model1.decisions, model2.decisions):
                if d1.name != d2.name:
                    return False, f"Decision name mismatch: {d1.name} vs {d2.name}"
                if len(d1.rules) != len(d2.rules):
                    return False, f"Rule count mismatch in {d1.name}: {len(d1.rules)} vs {len(d2.rules)}"

            # If test cases provided, do execution testing
            if test_cases and model1.decisions:
                import tempfile
                with tempfile.NamedTemporaryFile(mode='w', suffix='.dmn', delete=False, encoding='utf-8') as f:
                    f.write(dmn_xml)
                    dmn_temp = f.name

                try:
                    decision_id = model1.decisions[0].name
                    exec_results = self.tester.compare_execution(
                        prolog_path, dmn_temp, decision_id, test_cases
                    )

                    if exec_results['failed'] > 0:
                        return False, f"Execution testing failed: {exec_results['failed']}/{exec_results['total_tests']} tests failed"

                finally:
                    import os
                    if os.path.exists(dmn_temp):
                        os.unlink(dmn_temp)

            return True, "Roundtrip validation successful"

        except Exception as e:
            return False, f"Validation error: {str(e)}"


def main():
    """CLI entry point."""
    import argparse

    parser = argparse.ArgumentParser(
        description='Convert between Prolog and DMN formats'
    )
    parser.add_argument('input', help='Input file (Prolog or DMN)')
    parser.add_argument('output', help='Output file')
    parser.add_argument(
        '--to-dmn',
        action='store_true',
        help='Convert Prolog to DMN (default: auto-detect)'
    )
    parser.add_argument(
        '--to-prolog',
        action='store_true',
        help='Convert DMN to Prolog (default: auto-detect)'
    )
    parser.add_argument(
        '--validate',
        action='store_true',
        help='Validate roundtrip conversion'
    )

    args = parser.parse_args()

    converter = PrologDMNConverter()

    # Auto-detect conversion direction
    input_ext = Path(args.input).suffix.lower()

    if args.validate:
        is_valid, message = converter.validate_roundtrip(args.input)
        print(message)
        exit(0 if is_valid else 1)

    if args.to_dmn or input_ext in ['.pl', '.prolog']:
        print(f"Converting Prolog to DMN: {args.input} -> {args.output}")
        converter.prolog_to_dmn(args.input, args.output)
        print("Conversion complete!")

    elif args.to_prolog or input_ext in ['.dmn', '.xml']:
        print(f"Converting DMN to Prolog: {args.input} -> {args.output}")
        converter.dmn_to_prolog(args.input, args.output)
        print("Conversion complete!")

    else:
        print(f"Error: Cannot determine conversion direction from extension '{input_ext}'")
        print("Use --to-dmn or --to-prolog flag")
        exit(1)


if __name__ == '__main__':
    main()
