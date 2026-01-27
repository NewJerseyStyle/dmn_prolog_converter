# Quick Start Guide

## Install

```bash
cd dmn-prolog-convertor
pip install lark lxml cdmn
```

## Convert Prolog to DMN

```python
from src.converter import PrologDMNConverter

converter = PrologDMNConverter()
dmn_xml = converter.prolog_to_dmn("input.pl", "output.dmn", validate=True)
```

## Convert DMN to Prolog

```python
prolog_code = converter.dmn_to_prolog("input.dmn", "output.pl")
```

## Validate DMN

```python
from src.validation.dmn_validator import DMNValidator

validator = DMNValidator()
is_valid, message = validator.validate_dmn_file("rules.dmn")
print(f"Valid: {is_valid}")
```

## Command Line

```bash
# Prolog → DMN
python -m src.converter input.pl output.dmn

# DMN → Prolog
python -m src.converter input.dmn output.pl
```

## Run Demos

```bash
# Basic conversion
python demo.py

# With cDMN validation
python demo_validation.py

# Run tests
python tests/test_converter.py
```

## Example

**Input (input.pl):**
```prolog
tax_rate(Income, Rate) :-
    Income >= 100000,
    Rate = 35.

tax_rate(Income, Rate) :-
    Income < 100000,
    Rate = 28.
```

**Convert:**
```python
converter.prolog_to_dmn("input.pl", "output.dmn", validate=True)
# Output: [OK] SUCCESS: DMN syntax is valid
```

**Result:** Valid DMN 1.3 XML with decision table

## Documentation

- **README.md**: Full documentation
- **USAGE_GUIDE.md**: Detailed usage
- **CDMN_INTEGRATION.md**: Validation & execution
- **SUMMARY.md**: Complete summary

## Support

File issues at: `https://github.com/yourusername/dmn-prolog-convertor/issues`
