#!/usr/bin/env python3
"""
Command-line interface for DMN-Prolog Converter.

Provides easy-to-use CLI commands for converting between Prolog and DMN.
"""

import argparse
import sys
from pathlib import Path
from typing import Optional

from .converter import PrologDMNConverter
from .validation.dmn_validator import DMNValidator


def main():
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description='Convert between Prolog and DMN formats',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Convert Prolog to DMN
  dmn-prolog convert rules.pl rules.dmn

  # Convert DMN to Prolog
  dmn-prolog convert rules.dmn rules.pl

  # Validate DMN file
  dmn-prolog validate rules.dmn

  # Validate roundtrip conversion
  dmn-prolog roundtrip rules.pl

  # Quick conversion shortcuts
  prolog2dmn input.pl output.dmn
  dmn2prolog input.dmn output.pl
        """
    )

    subparsers = parser.add_subparsers(dest='command', help='Command to execute')

    # Convert command
    convert_parser = subparsers.add_parser(
        'convert',
        help='Convert between Prolog and DMN'
    )
    convert_parser.add_argument('input', help='Input file (Prolog or DMN)')
    convert_parser.add_argument('output', help='Output file')
    convert_parser.add_argument(
        '--no-validate',
        action='store_true',
        help='Skip validation when converting to DMN'
    )

    # Validate command
    validate_parser = subparsers.add_parser(
        'validate',
        help='Validate DMN file'
    )
    validate_parser.add_argument('file', help='DMN file to validate')

    # Roundtrip command
    roundtrip_parser = subparsers.add_parser(
        'roundtrip',
        help='Validate roundtrip conversion (Prolog -> DMN -> Prolog)'
    )
    roundtrip_parser.add_argument('file', help='Prolog file to test')

    # Info command
    info_parser = subparsers.add_parser(
        'info',
        help='Show information about a file'
    )
    info_parser.add_argument('file', help='File to inspect')

    # Version command
    version_parser = subparsers.add_parser(
        'version',
        help='Show version information'
    )

    args = parser.parse_args()

    if not args.command:
        parser.print_help()
        return 0

    # Execute command
    if args.command == 'convert':
        return convert_command(args.input, args.output, not args.no_validate)
    elif args.command == 'validate':
        return validate_command(args.file)
    elif args.command == 'roundtrip':
        return roundtrip_command(args.file)
    elif args.command == 'info':
        return info_command(args.file)
    elif args.command == 'version':
        return version_command()

    return 0


def convert_command(input_path: str, output_path: str, validate: bool = True) -> int:
    """Convert between Prolog, DMN, and Z3."""
    converter = PrologDMNConverter()

    input_file = Path(input_path)
    output_file = Path(output_path)

    if not input_file.exists():
        print(f"[ERROR] Input file not found: {input_path}", file=sys.stderr)
        return 1

    # Determine conversion direction
    input_ext = input_file.suffix.lower()
    output_ext = output_file.suffix.lower()

    try:
        if input_ext in ['.pl', '.prolog'] and output_ext in ['.dmn', '.xml']:
            # Prolog -> DMN
            print(f"Converting Prolog to DMN: {input_path} -> {output_path}")
            converter.prolog_to_dmn(str(input_file), str(output_file), validate=validate)
            print("[OK] Conversion complete!")

        elif input_ext in ['.dmn', '.xml'] and output_ext in ['.pl', '.prolog']:
            # DMN -> Prolog
            print(f"Converting DMN to Prolog: {input_path} -> {output_path}")
            converter.dmn_to_prolog(str(input_file), str(output_file))
            print("[OK] Conversion complete!")

        elif input_ext in ['.smt2', '.smt'] and output_ext in ['.dmn', '.xml']:
            # Z3 -> DMN
            print(f"Converting Z3 to DMN: {input_path} -> {output_path}")
            converter.z3_to_dmn(str(input_file), str(output_file), validate=validate)
            print("[OK] Conversion complete!")

        elif input_ext in ['.dmn', '.xml'] and output_ext in ['.smt2', '.smt']:
            # DMN -> Z3
            print(f"Converting DMN to Z3: {input_path} -> {output_path}")
            converter.dmn_to_z3(str(input_file), str(output_file))
            print("[OK] Conversion complete!")

        elif input_ext in ['.pl', '.prolog'] and output_ext in ['.smt2', '.smt']:
            # Prolog -> Z3
            print(f"Converting Prolog to Z3: {input_path} -> {output_path}")
            converter.prolog_to_z3(str(input_file), str(output_file))
            print("[OK] Conversion complete!")

        elif input_ext in ['.smt2', '.smt'] and output_ext in ['.pl', '.prolog']:
            # Z3 -> Prolog
            print(f"Converting Z3 to Prolog: {input_path} -> {output_path}")
            converter.z3_to_prolog(str(input_file), str(output_file))
            print("[OK] Conversion complete!")

        else:
            print(f"[ERROR] Cannot determine conversion direction", file=sys.stderr)
            print(f"Input: {input_ext}, Output: {output_ext}", file=sys.stderr)
            print(f"Supported conversions:", file=sys.stderr)
            print(f"  .pl/.prolog <-> .dmn/.xml", file=sys.stderr)
            print(f"  .smt2/.smt <-> .dmn/.xml", file=sys.stderr)
            print(f"  .pl/.prolog <-> .smt2/.smt", file=sys.stderr)
            return 1

        return 0

    except Exception as e:
        print(f"[ERROR] Conversion failed: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        return 1


def validate_command(file_path: str) -> int:
    """Validate DMN file."""
    validator = DMNValidator()

    file = Path(file_path)
    if not file.exists():
        print(f"[ERROR] File not found: {file_path}", file=sys.stderr)
        return 1

    print(f"Validating DMN: {file_path}")

    try:
        is_valid, message = validator.validate_dmn_file(str(file))

        if is_valid:
            print(f"[OK] {message}")
            return 0
        else:
            print(f"[FAIL] {message}", file=sys.stderr)
            return 1

    except Exception as e:
        print(f"[ERROR] Validation failed: {e}", file=sys.stderr)
        return 1


def roundtrip_command(file_path: str) -> int:
    """Validate roundtrip conversion."""
    converter = PrologDMNConverter()

    file = Path(file_path)
    if not file.exists():
        print(f"[ERROR] File not found: {file_path}", file=sys.stderr)
        return 1

    print(f"Testing roundtrip conversion: {file_path}")
    print("  Prolog -> DMN -> Prolog")

    try:
        is_valid, message = converter.validate_roundtrip(str(file))

        if is_valid:
            print(f"[OK] {message}")
            return 0
        else:
            print(f"[FAIL] {message}", file=sys.stderr)
            return 1

    except Exception as e:
        print(f"[ERROR] Roundtrip test failed: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        return 1


def info_command(file_path: str) -> int:
    """Show information about a file."""
    file = Path(file_path)
    if not file.exists():
        print(f"[ERROR] File not found: {file_path}", file=sys.stderr)
        return 1

    ext = file.suffix.lower()

    print(f"File Information: {file_path}")
    print(f"  Type: {ext}")
    print(f"  Size: {file.stat().st_size} bytes")

    if ext in ['.pl', '.prolog']:
        # Parse Prolog
        from .parser.prolog_parser import PrologParser

        try:
            parser = PrologParser()
            model = parser.parse_file(str(file))

            print(f"  Format: Prolog")
            print(f"  Decisions: {len(model.decisions)}")

            for decision in model.decisions:
                print(f"\n  Decision: {decision.name}")
                print(f"    Inputs: {', '.join(v.name for v in decision.inputs)}")
                print(f"    Outputs: {', '.join(v.name for v in decision.outputs)}")
                print(f"    Rules: {len(decision.rules)}")

        except Exception as e:
            print(f"  [ERROR] Failed to parse: {e}", file=sys.stderr)
            return 1

    elif ext in ['.dmn', '.xml']:
        # Parse DMN
        from .parser.dmn_parser import DMNParser

        try:
            parser = DMNParser()
            model = parser.parse_file(str(file))

            print(f"  Format: DMN")
            print(f"  Model: {model.name}")
            print(f"  Decisions: {len(model.decisions)}")

            for decision in model.decisions:
                print(f"\n  Decision: {decision.name}")
                print(f"    Inputs: {', '.join(v.name for v in decision.inputs)}")
                print(f"    Outputs: {', '.join(v.name for v in decision.outputs)}")
                print(f"    Rules: {len(decision.rules)}")
                print(f"    Hit Policy: {decision.hit_policy}")

        except Exception as e:
            print(f"  [ERROR] Failed to parse: {e}", file=sys.stderr)
            return 1

    elif ext in ['.smt2', '.smt']:
        # Parse Z3
        from .parser.z3_parser import Z3Parser

        try:
            parser = Z3Parser()
            model = parser.parse_file(str(file))

            print(f"  Format: Z3 SMT-LIB")
            print(f"  Decisions: {len(model.decisions)}")

            for decision in model.decisions:
                print(f"\n  Decision: {decision.name}")
                print(f"    Variables: {', '.join(v.name for v in decision.inputs)}")
                print(f"    Rules: {len(decision.rules)}")

        except Exception as e:
            print(f"  [ERROR] Failed to parse: {e}", file=sys.stderr)
            return 1

    else:
        print(f"  [WARN] Unknown file type: {ext}")

    return 0


def version_command() -> int:
    """Show version information."""
    print("DMN-Prolog Converter v1.0.0")
    print()
    print("Installed packages:")

    try:
        import lark
        print(f"  lark: {lark.__version__}")
    except:
        print(f"  lark: not installed")

    try:
        import lxml
        print(f"  lxml: {lxml.__version__}")
    except:
        print(f"  lxml: not installed")

    try:
        import cdmn
        print(f"  cdmn: installed (validation enabled)")
    except:
        print(f"  cdmn: not installed (validation disabled)")

    try:
        import pyswip
        print(f"  pyswip: installed (Prolog execution enabled)")
    except:
        print(f"  pyswip: not installed (Prolog execution disabled)")

    print()
    print("Documentation: https://github.com/NewJerseyStyle/dmn-prolog-converter")

    return 0


def prolog_to_dmn_cli():
    """Shortcut command for Prolog to DMN conversion."""
    if len(sys.argv) < 3:
        print("Usage: prolog2dmn <input.pl> <output.dmn>")
        return 1

    input_path = sys.argv[1]
    output_path = sys.argv[2]

    return convert_command(input_path, output_path, validate=True)


def dmn_to_prolog_cli():
    """Shortcut command for DMN to Prolog conversion."""
    if len(sys.argv) < 3:
        print("Usage: dmn2prolog <input.dmn> <output.pl>")
        return 1

    input_path = sys.argv[1]
    output_path = sys.argv[2]

    return convert_command(input_path, output_path, validate=False)


def z3_to_dmn_cli():
    """Shortcut command for Z3 to DMN conversion."""
    if len(sys.argv) < 3:
        print("Usage: z32dmn <input.smt2> <output.dmn>")
        return 1

    input_path = sys.argv[1]
    output_path = sys.argv[2]

    return convert_command(input_path, output_path, validate=True)


def dmn_to_z3_cli():
    """Shortcut command for DMN to Z3 conversion."""
    if len(sys.argv) < 3:
        print("Usage: dmn2z3 <input.dmn> <output.smt2>")
        return 1

    input_path = sys.argv[1]
    output_path = sys.argv[2]

    return convert_command(input_path, output_path, validate=False)


if __name__ == '__main__':
    sys.exit(main())
