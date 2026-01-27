# cDMN Integration Guide

This guide explains how to use cDMN for validation, execution, and testing of the converted DMN files.

## What is cDMN?

[cDMN](https://cdmn.readthedocs.io/en/stable/) is a Python library for:
- **Parsing** DMN XML files
- **Validating** DMN decision models
- **Executing** DMN decision tables
- **Testing** decision logic

## Installation

```bash
# Install only cDMN with the convertor
pip install dmn-prolog-convertor[validation]

# Optional: Install both cDMN and Prolog execution Python package
pip install dmn-prolog-convertor[execution]
```

> :warning: Installing `dmn-prolog-convertor[execution]` does not automatically install SWI-Prolog to the system, it only enable Python to connect SWI-Prolog if you have installed. Follow instructions of [Installing SWI-Prolog](https://pyswip.readthedocs.io/en/latest/get_started.html#install-swi-prolog) before install us.

## Features

### 1. Automatic DMN Validation

When converting Prolog to DMN, validation is automatic:

```python
from src.converter import PrologDMNConverter

converter = PrologDMNConverter()

# Automatic validation
dmn_xml = converter.prolog_to_dmn("rules.pl", "rules.dmn", validate=True)
# Output: ✓ DMN validation passed: DMN is valid and can be executed
```

### 2. Manual DMN Validation

Validate DMN files independently:

```python
from src.validation.dmn_validator import DMNValidator

validator = DMNValidator()

# Validate DMN file
is_valid, message = validator.validate_dmn_file("rules.dmn")
print(f"Valid: {is_valid}, Message: {message}")

# Validate DMN string
dmn_xml = open("rules.dmn").read()
is_valid, message = validator.validate_dmn_string(dmn_xml)
```

### 3. DMN Execution

Execute DMN decisions with test data:

```python
from src.execution.dmn_executor import DMNExecutor

executor = DMNExecutor()

# Execute a decision
inputs = {"Income": 75000}
result = executor.execute_decision(
    "tax_rules.dmn",
    "determine_tax_rate",  # decision ID
    inputs
)

print(f"Tax Rate: {result['TaxRate']}")
# Output: Tax Rate: 28
```

### 4. Batch Execution

Test multiple cases at once:

```python
test_cases = [
    {"Income": 150000},
    {"Income": 75000},
    {"Income": 30000},
]

results = executor.batch_execute(
    "tax_rules.dmn",
    "determine_tax_rate",
    test_cases
)

for inputs, result in zip(test_cases, results):
    print(f"Income: ${inputs['Income']:,} → Tax Rate: {result['TaxRate']}%")
```

### 5. Prolog vs DMN Comparison

Verify that Prolog and DMN produce identical results:

```python
from src.execution.dmn_executor import ExecutionTester

tester = ExecutionTester()

# Define test cases with expected outputs
test_cases = [
    {
        'inputs': {'Income': 150000},
        'expected': {'TaxRate': 35}
    },
    {
        'inputs': {'Income': 75000},
        'expected': {'TaxRate': 28}
    },
]

# Compare Prolog and DMN execution
results = tester.compare_execution(
    "tax_rules.pl",
    "tax_rules.dmn",
    "determine_tax_rate",
    test_cases
)

# Generate report
report = tester.generate_test_report(results)
print(report)
```

### 6. Roundtrip Validation with Execution

Validate that conversion is correct by testing execution:

```python
from src.converter import PrologDMNConverter

converter = PrologDMNConverter()

test_cases = [
    {
        'inputs': {'Income': 150000},
        'expected': {'TaxRate': 35}
    },
]

is_valid, message = converter.validate_roundtrip(
    "tax_rules.pl",
    test_cases=test_cases
)

print(message)
# Output: Roundtrip validation successful
```

## Running Demos

### Execution Tests

```bash
python tests/test_execution.py
```

## Common Use Cases

### Use Case 1: Legal Rule Validation

```python
# Legal team provides rules in Prolog
prolog_rules = """
eligible_for_benefit(Age, Income, Eligible) :-
    Age >= 65,
    Income < 50000,
    Eligible = yes.
"""

# Convert to DMN
dmn_xml = converter.prolog_string_to_dmn(prolog_rules)

# Validate DMN
is_valid, msg = validator.validate_dmn_string(dmn_xml)
if is_valid:
    print("✓ Rules are valid and ready for deployment")
else:
    print(f"✗ Rules have errors: {msg}")
```

### Use Case 2: Regression Testing

```python
# After modifying rules, ensure behavior is unchanged
test_cases = [
    {'inputs': {'Age': 70, 'Income': 40000}, 'expected': {'Eligible': 'yes'}},
    {'inputs': {'Age': 60, 'Income': 40000}, 'expected': {'Eligible': 'no'}},
    {'inputs': {'Age': 70, 'Income': 60000}, 'expected': {'Eligible': 'no'}},
]

results = tester.compare_execution(
    "benefit_rules.pl",
    "benefit_rules.dmn",
    "eligible_for_benefit",
    test_cases
)

if results['failed'] == 0:
    print("✓ All regression tests passed")
else:
    print(f"✗ {results['failed']} tests failed")
    print(tester.generate_test_report(results))
```

### Use Case 3: Production Validation

```python
# Before deploying to production, validate with real-world data
production_tests = load_test_data("production_test_cases.json")

results = executor.batch_execute(
    "production_rules.dmn",
    "credit_decision",
    production_tests
)

# Check for any failures
failures = [r for r in results if r is None or 'error' in r]
if failures:
    print(f"⚠ {len(failures)} execution failures detected")
else:
    print("✓ All production tests passed - ready for deployment")
```

## Troubleshooting

### Execution Fails

If DMN execution returns `None`:

1. Check DMN is valid: `validator.validate_dmn_file("file.dmn")`
2. Verify decision ID matches: use exact ID from DMN file
3. Check input variable names match DMN inputs exactly
4. Ensure data types are correct (numbers as numbers, not strings)

### Type Mismatches

DMN expects typed inputs. If you get type errors:

```python
# ✗ Wrong - strings when numbers expected
inputs = {"Income": "75000"}

# ✓ Correct - use proper types
inputs = {"Income": 75000}
```

## API Reference

### DMNValidator

```python
validator = DMNValidator()

# Validate DMN string
is_valid, message = validator.validate_dmn_string(dmn_xml)

# Validate DMN file
is_valid, message = validator.validate_dmn_file("rules.dmn")

# Get decision info
info = validator.get_decision_info("rules.dmn")
```

### DMNExecutor

```python
executor = DMNExecutor()

# Execute single decision
result = executor.execute_decision(dmn_path, decision_id, inputs)

# Execute from string
result = executor.execute_decision_string(dmn_xml, decision_id, inputs)

# Batch execution
results = executor.batch_execute(dmn_path, decision_id, test_cases)
```

### ExecutionTester

```python
tester = ExecutionTester()

# Compare Prolog and DMN
results = tester.compare_execution(prolog_path, dmn_path, decision_id, test_cases)

# Generate report
report = tester.generate_test_report(results)
print(report)
```

## Resources

- [cDMN Documentation](https://cdmn.readthedocs.io/en/stable/)
- [DMN Specification](https://www.omg.org/spec/DMN/)
- [FEEL Language Reference](https://docs.camunda.org/manual/latest/reference/dmn/feel/)
