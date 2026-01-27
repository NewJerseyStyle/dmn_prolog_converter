"""
Test the bidirectional converter with examples.
"""

import sys
import os
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from dmn_prolog_converter.converter import PrologDMNConverter


def test_prolog_to_dmn():
    """Test Prolog to DMN conversion."""
    print("=" * 60)
    print("TEST: Prolog to DMN Conversion")
    print("=" * 60)

    converter = PrologDMNConverter()

    examples = [
        'loan_eligibility.pl',
        'discount_calculation.pl',
        'tax_bracket.pl'
    ]

    for example in examples:
        input_path = Path(__file__).parent / 'examples' / example
        output_path = Path(__file__).parent / 'examples' / example.replace('.pl', '.dmn')

        print(f"\nConverting: {example}")

        try:
            dmn_xml = converter.prolog_to_dmn(str(input_path), str(output_path))
            print(f"[OK] Successfully generated: {output_path.name}")
            print(f"  Size: {len(dmn_xml)} bytes")
        except Exception as e:
            print(f"[FAIL] Error: {e}")

    print()


def test_dmn_to_prolog():
    """Test DMN to Prolog conversion (roundtrip)."""
    print("=" * 60)
    print("TEST: DMN to Prolog Conversion (Roundtrip)")
    print("=" * 60)

    converter = PrologDMNConverter()

    examples = [
        'loan_eligibility.dmn',
        'discount_calculation.dmn',
        'tax_bracket.dmn'
    ]

    for example in examples:
        input_path = Path(__file__).parent / 'examples' / example
        output_path = Path(__file__).parent / 'examples' / example.replace('.dmn', '_roundtrip.pl')

        if not input_path.exists():
            print(f"\nSkipping: {example} (not found)")
            continue

        print(f"\nConverting: {example}")

        try:
            prolog_code = converter.dmn_to_prolog(str(input_path), str(output_path))
            print(f"[OK] Successfully generated: {output_path.name}")
            print(f"  Size: {len(prolog_code)} bytes")

            # Show preview
            lines = prolog_code.split('\n')[:10]
            print("\n  Preview:")
            for line in lines:
                print(f"    {line}")
            if len(prolog_code.split('\n')) > 10:
                print("    ...")

        except Exception as e:
            print(f"[FAIL] Error: {e}")
            import traceback
            traceback.print_exc()

    print()


def test_validation():
    """Test roundtrip validation."""
    print("=" * 60)
    print("TEST: Roundtrip Validation")
    print("=" * 60)

    converter = PrologDMNConverter()

    examples = [
        'loan_eligibility.pl',
        'discount_calculation.pl',
        'tax_bracket.pl'
    ]

    for example in examples:
        input_path = Path(__file__).parent / 'examples' / example

        print(f"\nValidating: {example}")

        is_valid, message = converter.validate_roundtrip(str(input_path))

        if is_valid:
            print(f"[OK] {message}")
        else:
            print(f"[FAIL] {message}")

    print()


def show_example_output():
    """Show detailed output for one example."""
    print("=" * 60)
    print("EXAMPLE: Tax Bracket Decision")
    print("=" * 60)

    converter = PrologDMNConverter()
    input_path = Path(__file__).parent / 'examples' / 'tax_bracket.pl'

    # Show original Prolog
    print("\n--- Original Prolog ---")
    with open(input_path, 'r') as f:
        prolog_code = f.read()
        print(prolog_code)

    # Convert to DMN
    print("\n--- Generated DMN (excerpt) ---")
    dmn_xml = converter.prolog_to_dmn(str(input_path))
    lines = dmn_xml.split('\n')
    for i, line in enumerate(lines):
        if i < 30 or i > len(lines) - 5:
            print(line)
        elif i == 30:
            print("...")

    print()


if __name__ == '__main__':
    test_prolog_to_dmn()
    test_dmn_to_prolog()
    test_validation()
    show_example_output()

    print("=" * 60)
    print("All tests completed!")
    print("=" * 60)
