"""
Test DMN execution and validation.
"""

import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from dmn_prolog_converter.converter import PrologDMNConverter
from dmn_prolog_converter.execution.dmn_executor import DMNExecutor, ExecutionTester


def test_tax_bracket_execution():
    """Test tax bracket decision execution."""
    print("=" * 60)
    print("TEST: Tax Bracket Decision Execution")
    print("=" * 60)

    converter = PrologDMNConverter()
    executor = DMNExecutor()

    if not executor.cdmn_available:
        print("\n[WARN] cDMN not installed - skipping execution tests")
        print("Install with: pip install cdmn")
        return

    # Convert example to DMN
    input_path = Path(__file__).parent / 'examples' / 'tax_bracket.pl'

    if not input_path.exists():
        print(f"\n[WARN] Example file not found: {input_path}")
        return

    output_path = Path(__file__).parent / 'examples' / 'tax_bracket_test.dmn'

    print(f"\nConverting: {input_path.name}")
    dmn_xml = converter.prolog_to_dmn(str(input_path), str(output_path), validate=True)

    # Test execution
    test_cases = [
        {'Income': 150000},  # High bracket
        {'Income': 75000},   # Upper-middle
        {'Income': 40000},   # Middle
        {'Income': 20000},   # Lower-middle
        {'Income': 10000},   # Low
    ]

    print(f"\n--- Executing {len(test_cases)} Test Cases ---")

    for i, inputs in enumerate(test_cases, 1):
        print(f"\nTest {i}: Income = ${inputs['Income']:,}")

        result = executor.execute_decision(
            str(output_path),
            'determine_tax_rate',
            inputs
        )

        if result:
            print(f"  → Tax Rate: {result.get('TaxRate', 'N/A')}%")
        else:
            print("  → Execution failed")

    # Cleanup
    if output_path.exists():
        output_path.unlink()

    print()


def test_discount_execution():
    """Test discount calculation execution."""
    print("=" * 60)
    print("TEST: Discount Calculation Execution")
    print("=" * 60)

    converter = PrologDMNConverter()
    executor = DMNExecutor()

    if not executor.cdmn_available:
        print("\n[WARN] cDMN not installed - skipping")
        return

    input_path = Path(__file__).parent / 'examples' / 'discount_calculation.pl'

    if not input_path.exists():
        print(f"\n[WARN] Example file not found: {input_path}")
        return

    output_path = Path(__file__).parent / 'examples' / 'discount_test.dmn'

    print(f"\nConverting: {input_path.name}")
    dmn_xml = converter.prolog_to_dmn(str(input_path), str(output_path), validate=True)

    # Test cases
    test_cases = [
        {'LoyaltyStatus': 'vip', 'OrderAmount': 500},
        {'LoyaltyStatus': 'premium', 'OrderAmount': 1500},
        {'LoyaltyStatus': 'premium', 'OrderAmount': 800},
        {'LoyaltyStatus': 'standard', 'OrderAmount': 600},
        {'LoyaltyStatus': 'standard', 'OrderAmount': 300},
    ]

    print(f"\n--- Executing {len(test_cases)} Test Cases ---")

    for i, inputs in enumerate(test_cases, 1):
        print(f"\nTest {i}: Status={inputs['LoyaltyStatus']}, Amount=${inputs['OrderAmount']}")

        result = executor.execute_decision(
            str(output_path),
            'calculate_discount',
            inputs
        )

        if result:
            print(f"  → Discount: {result.get('Discount', 'N/A')}%")
        else:
            print("  → Execution failed")

    # Cleanup
    if output_path.exists():
        output_path.unlink()

    print()


def test_roundtrip_with_execution():
    """Test roundtrip validation with execution testing."""
    print("=" * 60)
    print("TEST: Roundtrip Validation with Execution")
    print("=" * 60)

    converter = PrologDMNConverter()

    input_path = Path(__file__).parent / 'examples' / 'tax_bracket.pl'

    if not input_path.exists():
        print(f"\n[WARN] Example file not found: {input_path}")
        return

    # Define test cases
    test_cases = [
        {
            'inputs': {'Income': 150000},
            'expected': {'TaxRate': 35}
        },
        {
            'inputs': {'Income': 75000},
            'expected': {'TaxRate': 28}
        },
        {
            'inputs': {'Income': 10000},
            'expected': {'TaxRate': 10}
        },
    ]

    print(f"\nValidating: {input_path.name}")
    is_valid, message = converter.validate_roundtrip(str(input_path), test_cases)

    if is_valid:
        print(f"[OK] {message}")
    else:
        print(f"[FAIL] {message}")

    print()


if __name__ == '__main__':
    print("\n" + "=" * 60)
    print("  DMN Execution Tests")
    print("=" * 60)

    test_tax_bracket_execution()
    test_discount_execution()
    test_roundtrip_with_execution()

    print("=" * 60)
    print("  Tests Complete!")
    print("=" * 60)
    print()
