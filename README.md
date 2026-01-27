# DMN-Prolog Bidirectional Converter

A Python tool for bidirectional conversion between Prolog code and DMN (Decision Model and Notation) for legal/business rule management.

## Overview

This tool enables a powerful workflow for converting legal documents into executable decision logic:

```
Legal Document → LLM → Prolog → DMN → Review → Deploy (Prolog or DMN)
                         ↑                ↓
                         └────────────────┘
                         (Bidirectional)
```

**Why this approach?**
- **LLM-Friendly Input**: Prolog syntax is simpler and more reliable for LLMs to generate than verbose DMN XML
- **Human-Friendly Review**: DMN provides visual decision tables that legal/business specialists can review
- **Flexible Deployment**: Deploy as either Prolog (for Prolog engines) or DMN (for DMN engines)
- **Quality Control**: Bidirectional conversion ensures consistency and reduces hallucination

## Supported Prolog Subset

To ensure DMN compatibility, the converter supports a restricted Prolog subset:

- ✓ **Horn clauses only** (no negation-as-failure, no cuts)
- ✓ **Deterministic rules** (single output per input combination)
- ✓ **Simple data types** (atoms, numbers, strings, booleans)
- ✓ **Decision table structure** (pattern-matching rules)
- ✓ **Limited recursion** (≤ 3 levels)
- ✓ **FEEL expression compatibility** (comparison operators: `>=`, `=<`, `>`, `<`, `==`, `\=`)

## Installation

```bash
# Basic installation (conversion only)
pip install dmn-prolog-converter

# With validation support
pip install dmn-prolog-converter[validation]

# With all optional features
pip install dmn-prolog-converter[execution]
```

See [CDMN_INTEGRATION.md](CDMN_INTEGRATION.md) for details.

## Quick Start

### Command Line

After installation, you'll have these commands available:

```bash
dmn-prolog          # Main CLI tool
prolog2dmn          # Shortcut: Prolog to DMN
dmn2prolog          # Shortcut: DMN to Prolog
```

Example usage
```bash
# Convert Prolog to DMN
dmn-prolog convert rules.pl rules.dmn

# Convert DMN to Prolog
dmn-prolog convert rules.dmn rules.pl

# Validate DMN
dmn-prolog validate rules.dmn

# Show file info
dmn-prolog info rules.pl

# Quick shortcuts
prolog2dmn input.pl output.dmn
dmn2prolog input.dmn output.pl
```

See [CLI_GUIDE.md](CLI_GUIDE.md) for complete CLI documentation.

### Python API

```python
from src.converter import PrologDMNConverter

converter = PrologDMNConverter()

# Prolog → DMN (with automatic validation)
dmn_xml = converter.prolog_to_dmn("input.pl", "output.dmn", validate=True)

# DMN → Prolog
prolog_code = converter.dmn_to_prolog("input.dmn", "output.pl")

# String-based conversion
dmn_xml = converter.prolog_string_to_dmn(prolog_code)
prolog_code = converter.dmn_string_to_prolog(dmn_xml)

# Validate roundtrip conversion
is_valid, message = converter.validate_roundtrip("input.pl")
print(message)
```

### DMN Execution (with cDMN)

```python
from src.execution.dmn_executor import DMNExecutor

executor = DMNExecutor()

# Execute DMN decision
inputs = {"Income": 75000}
result = executor.execute_decision("tax_rules.dmn", "determine_tax_rate", inputs)
print(f"Tax Rate: {result['TaxRate']}%")

# Test multiple scenarios
test_cases = [
    {"Income": 150000},
    {"Income": 75000},
    {"Income": 30000}
]
results = executor.batch_execute("tax_rules.dmn", "determine_tax_rate", test_cases)
```

See [CDMN_INTEGRATION.md](CDMN_INTEGRATION.md) for complete guide.

### Command Line

```bash
# Prolog → DMN
python -m src.converter input.pl output.dmn

# DMN → Prolog
python -m src.converter input.dmn output.pl

# Auto-detect based on file extension
python -m src.converter tax_rules.pl tax_rules.dmn

# Validate roundtrip
python -m src.converter --validate input.pl
```

### Quick Demo

```bash
python demo.py
```

## Examples

### Example 1: Tax Bracket Decision

**Prolog Input** (`tax_bracket.pl`):
```prolog
% Tax Bracket Determination
determine_tax_rate(Income, TaxRate) :-
    Income >= 100000,
    TaxRate = 35.

determine_tax_rate(Income, TaxRate) :-
    Income >= 50000,
    Income < 100000,
    TaxRate = 28.

determine_tax_rate(Income, TaxRate) :-
    Income < 50000,
    TaxRate = 15.
```

**Generated DMN Output**:
```xml
<?xml version='1.0' encoding='UTF-8'?>
<definitions xmlns="https://www.omg.org/spec/DMN/20191111/MODEL/"
             id="PrologModel_definitions"
             name="PrologModel"
             namespace="http://example.org/dmn">
  <decision id="determine_tax_rate" name="Determine Tax Rate">
    <decisionTable id="determine_tax_rate_table" hitPolicy="UNIQUE">
      <input id="input_Income" label="Income">
        <inputExpression typeRef="number">
          <text>Income</text>
        </inputExpression>
      </input>
      <output id="output_TaxRate" label="Tax Rate" name="TaxRate" typeRef="number"/>
      <rule id="rule_1">
        <inputEntry><text>&gt;= 100000</text></inputEntry>
        <outputEntry><text>35</text></outputEntry>
      </rule>
      <rule id="rule_2">
        <inputEntry><text>&gt;= 50000 and &lt; 100000</text></inputEntry>
        <outputEntry><text>28</text></outputEntry>
      </rule>
      <rule id="rule_3">
        <inputEntry><text>&lt; 50000</text></inputEntry>
        <outputEntry><text>15</text></outputEntry>
      </rule>
    </decisionTable>
  </decision>
</definitions>
```

### Example 2: Loan Eligibility

See `tests/examples/loan_eligibility.pl` for a more complex example with multiple conditions.

### Example 3: Discount Calculation

See `tests/examples/discount_calculation.pl` for categorical rules.

## Project Structure

```
dmn-prolog-convertor/
├── src/
│   ├── parser/
│   │   ├── prolog_parser.py    # Parse Prolog → IR (using Lark)
│   │   └── dmn_parser.py       # Parse DMN → IR (using lxml)
│   ├── generator/
│   │   ├── prolog_generator.py # Generate Prolog from IR
│   │   └── dmn_generator.py    # Generate DMN XML from IR
│   ├── ir/
│   │   └── intermediate.py     # Intermediate Representation
│   └── converter.py            # Main converter API
├── tests/
│   ├── test_converter.py       # Integration tests
│   └── examples/               # Example files
│       ├── tax_bracket.pl
│       ├── loan_eligibility.pl
│       └── discount_calculation.pl
├── demo.py                     # Quick demo script
├── requirements.txt            # Dependencies
├── setup.py                    # Package setup
└── README.md
```

## Architecture

### Intermediate Representation (IR)

The converter uses a pivot IR that captures the essential structure of both Prolog and DMN:

- **DecisionModel**: Top-level container
- **Decision**: A decision (Prolog predicate / DMN decision table)
- **Rule**: A single rule (Prolog clause / DMN table row)
- **Condition**: Antecedent (body of Prolog clause / input entry)
- **Conclusion**: Consequent (head of Prolog clause / output entry)
- **Expression**: Logical/comparison/arithmetic expression
- **Variable**: Input/output variable with type information
- **Literal**: Constant value

### Conversion Pipeline

```
Prolog Code
    ↓
[Prolog Parser] → Uses Lark grammar
    ↓
Intermediate Representation (IR)
    ↓
[DMN Generator] → Generates XML with lxml
    ↓
DMN XML
```

And vice versa:

```
DMN XML
    ↓
[DMN Parser] → Parses XML with lxml
    ↓
Intermediate Representation (IR)
    ↓
[Prolog Generator] → Generates Prolog code
    ↓
Prolog Code
```

## Testing

Run the test suite:

```bash
# Run all tests
python tests/test_converter.py

# Run specific test
python -c "from tests.test_converter import test_prolog_to_dmn; test_prolog_to_dmn()"
```

## Limitations & Future Work

**Current Limitations:**
- No support for complex Prolog features (cuts, negation-as-failure, DCGs)
- Limited to decision tables (no decision requirement diagrams)
- No support for DMN business knowledge models or contexts
- Arithmetic expressions are basic

**Future Enhancements:**
- Support for DMN FEEL functions
- Decision requirement diagram generation
- Semantic validation of business logic
- Integration with LLM for natural language descriptions
- Support for more complex Prolog constructs (via approximation)
- Visual DMN table editor integration

## Use Cases

1. **Legal Document Automation**: Convert legal rules to executable format
2. **Business Rule Management**: Maintain rules in both technical and business-friendly formats
3. **Legacy Migration**: Migrate Prolog expert systems to DMN standard
4. **LLM-Powered Rule Generation**: Let LLMs generate Prolog, convert to DMN for review
5. **Dual Deployment**: Maintain single source, deploy to both Prolog and DMN engines

## Contributing

Contributions welcome! Areas for improvement:
- Additional test cases
- Support for more Prolog patterns
- Enhanced FEEL expression generation
- Documentation improvements

## License

MIT License - see LICENSE file for details

## References

- [DMN 1.3 Specification](https://www.omg.org/spec/DMN/1.3/)
- [FEEL Language Guide](https://docs.camunda.org/manual/latest/reference/dmn/feel/)
- [Prolog Tutorial](https://www.swi-prolog.org/pldoc/man?section=quickstart)
- [Lark Parser Documentation](https://lark-parser.readthedocs.io/)
