# Z3 SMT-LIB Conversion Guide

Complete guide to using Z3 SMT-LIB format with the DMN-Prolog Converter.

## Overview

The converter supports bidirectional conversion between Z3 SMT-LIB format and DMN/Prolog:

```
Z3 SMT-LIB ←→ DMN ←→ Prolog
```

This enables you to:
- Convert business rules to Z3 for formal verification
- Convert Z3 constraints to DMN decision tables
- Verify decision logic using Z3 theorem prover
- Translate between all three formats

## Quick Start

### Installation

```bash
pip install dmn-prolog-converter
```

### Basic Usage

```bash
# Z3 to DMN
dmn-prolog convert rules.smt2 rules.dmn

# DMN to Z3
dmn-prolog convert rules.dmn rules.smt2

# Prolog to Z3
dmn-prolog convert rules.pl rules.smt2

# Z3 to Prolog
dmn-prolog convert rules.smt2 rules.pl
```

### CLI Shortcuts

```bash
z32dmn input.smt2 output.dmn    # Z3 → DMN
dmn2z3 input.dmn output.smt2    # DMN → Z3
```

## Z3 SMT-LIB Format

### What is Z3?

Z3 is a high-performance theorem prover from Microsoft Research. SMT-LIB is the standard input format for SMT (Satisfiability Modulo Theories) solvers like Z3.

### Basic Syntax

Z3 SMT-LIB uses S-expressions (LISP-like syntax):

```smt2
; Comments start with semicolon
(declare-const x Int)              ; Declare variable x of type Int
(assert (>= x 100))                ; Assert that x >= 100
(assert (= y 35))                  ; Assert that y equals 35
(check-sat)                        ; Check if constraints are satisfiable
(get-model)                        ; Get a satisfying model
```

## Supported Features

### Data Types

| Z3 Type | DMN Type | Prolog Type | Notes |
|---------|----------|-------------|-------|
| `Int` | number | Number | Integers |
| `Real` | number | Number | Real numbers |
| `Bool` | boolean | Boolean | true/false |
| `String` | string | Atom/String | Text |

**Example:**

```smt2
(declare-const age Int)
(declare-const approved Bool)
(declare-const name String)
```

### Comparison Operators

| Z3 Operator | Meaning | DMN | Prolog |
|-------------|---------|-----|--------|
| `=` | Equal | `=` | `=` |
| `distinct` | Not equal | `!=` | `\=` |
| `>` | Greater than | `>` | `>` |
| `>=` | Greater or equal | `>=` | `>=` |
| `<` | Less than | `<` | `<` |
| `<=` | Less or equal | `<=` | `=<` |

**Example:**

```smt2
(declare-const Income Int)
(declare-const TaxRate Int)

; High income bracket
(assert (>= Income 100000))
(assert (= TaxRate 35))
```

### Logical Operators

| Z3 Operator | Meaning | Example |
|-------------|---------|---------|
| `and` | Conjunction | `(and (>= x 50) (< x 100))` |
| `or` | Disjunction | `(or (= y 1) (= y 2))` |
| `not` | Negation | `(not (< x 0))` |
| `=>` | Implication | `(=> (>= x 100) (= y 35))` |

**Example:**

```smt2
(declare-const Credit Int)
(declare-const Income Int)
(declare-const Result String)

; Loan eligibility: credit >= 650 AND income >= 50000
(assert (and (>= Credit 650) (>= Income 50000)))
(assert (= Result "approved"))
```

### Arithmetic Operators

| Z3 Operator | Meaning | Example |
|-------------|---------|---------|
| `+` | Addition | `(+ x y)` |
| `-` | Subtraction | `(- x y)` |
| `*` | Multiplication | `(* x 3)` |
| `/` | Division | `(/ x y)` |

**Example:**

```smt2
(declare-const Income Int)
(declare-const Expense Int)
(declare-const Affordable Bool)

; Check if income is at least 3 times the expense
(assert (>= Income (* Expense 3)))
(assert (= Affordable true))
```

## Limitations

### What is Supported

✅ Variable declarations (`declare-const`)
✅ Basic assertions (`assert`)
✅ Comparison operators (`=`, `>`, `<`, `>=`, `<=`, `distinct`)
✅ Arithmetic operators (`+`, `-`, `*`, `/`)
✅ Logical operators (`and`, `or`, `not`, `=>`)
✅ Basic types (Int, Bool, Real, String)

### What is NOT Supported

❌ **Quantifiers**: `forall`, `exists`
```smt2
; NOT SUPPORTED
(assert (forall ((x Int)) (>= x 0)))
```

❌ **Functions**: User-defined functions
```smt2
; NOT SUPPORTED
(define-fun max ((x Int) (y Int)) Int
  (ite (> x y) x y))
```

❌ **Arrays**: Array theory
```smt2
; NOT SUPPORTED
(declare-const arr (Array Int Int))
```

❌ **Bit-vectors**: Bit-vector theory
```smt2
; NOT SUPPORTED
(declare-const bv (_ BitVec 32))
```

❌ **Uninterpreted functions**: Functions without definitions
```smt2
; PARTIALLY SUPPORTED (treated as variables)
(declare-fun f (Int) Bool)
```

❌ **Complex expressions in assertions**: Nested implications, complex if-then-else
```smt2
; LIMITED SUPPORT
(assert (ite (> x 0) (= y 1) (= y 2)))
```

### Workarounds

**Problem**: Complex conditions

```smt2
; Instead of:
(assert (=> (and (>= x 50) (< x 100)) (= y 28)))

; Use separate assertions:
(assert (>= x 50))
(assert (< x 100))
(assert (= y 28))
```

**Problem**: Implications (=>)

The parser treats implications as separate conditions and conclusions. The structure `(=> condition conclusion)` is converted to a rule with condition and conclusion.

## Examples

### Example 1: Tax Bracket Determination

**Z3 SMT-LIB** (`tax_bracket.smt2`):

```smt2
; Tax Bracket Determination
(declare-const Income Int)
(declare-const TaxRate Int)

; Rule 1: High income (>= 100000) → 35% tax
(assert (=> (>= Income 100000) (= TaxRate 35)))

; Rule 2: Upper-middle income (50000-99999) → 28% tax
(assert (=> (and (>= Income 50000) (< Income 100000)) (= TaxRate 28)))

; Rule 3: Middle income (30000-49999) → 22% tax
(assert (=> (and (>= Income 30000) (< Income 50000)) (= TaxRate 22)))

; Rule 4: Lower-middle income (15000-29999) → 15% tax
(assert (=> (and (>= Income 15000) (< Income 30000)) (= TaxRate 15)))

; Rule 5: Low income (< 15000) → 10% tax
(assert (=> (< Income 15000) (= TaxRate 10)))

(check-sat)
(get-model)
```

**Convert to DMN:**

```bash
dmn-prolog convert tax_bracket.smt2 tax_bracket.dmn
```

**Convert to Prolog:**

```bash
dmn-prolog convert tax_bracket.smt2 tax_bracket.pl
```

### Example 2: Loan Eligibility

**Z3 SMT-LIB** (`loan_eligibility.smt2`):

```smt2
; Loan Eligibility Decision
(declare-const CreditScore Int)
(declare-const AnnualIncome Int)
(declare-const LoanAmount Int)
(declare-const Decision String)

; Premium tier: credit >= 700, income >= 3x loan amount
(assert (=>
    (and (>= CreditScore 700) (>= AnnualIncome (* LoanAmount 3)))
    (= Decision "premium")))

; Standard tier: credit >= 650, income >= 4x loan amount
(assert (=>
    (and (>= CreditScore 650) (< CreditScore 700)
         (>= AnnualIncome (* LoanAmount 4)))
    (= Decision "standard")))

; Denied: credit < 650
(assert (=> (< CreditScore 650) (= Decision "denied")))

(check-sat)
(get-model)
```

**Convert to DMN:**

```bash
z32dmn loan_eligibility.smt2 loan_eligibility.dmn
```

### Example 3: Risk Assessment

**Z3 SMT-LIB** (`risk_assessment.smt2`):

```smt2
; Risk Level Assessment
(declare-const RiskScore Int)
(declare-const RiskLevel String)

; Low risk: score >= 80
(assert (=> (>= RiskScore 80) (= RiskLevel "low")))

; Medium risk: 50 <= score < 80
(assert (=> (and (>= RiskScore 50) (< RiskScore 80)) (= RiskLevel "medium")))

; High risk: score < 50
(assert (=> (< RiskScore 50) (= RiskLevel "high")))

(check-sat)
(get-model)
```

## Using Z3 with the Converter

### Workflow 1: Verify Business Rules

```bash
# 1. Start with Prolog rules
cat > rules.pl << 'EOF'
eligible(Credit, Income, Result) :-
    Credit >= 650,
    Income >= 50000,
    Result = approved.
EOF

# 2. Convert to Z3
prolog2z3 rules.pl rules.smt2

# 3. Verify with Z3 theorem prover
z3 rules.smt2
```

### Workflow 2: Convert Decision Tables to Z3

```bash
# 1. Create DMN decision table (using Camunda Modeler, etc.)
# rules.dmn

# 2. Convert to Z3 for verification
dmn2z3 rules.dmn rules.smt2

# 3. Check satisfiability
z3 rules.smt2
```

### Workflow 3: Full Cycle

```bash
# Prolog → DMN → Z3 → verify → back to Prolog
prolog2dmn rules.pl rules.dmn
dmn2z3 rules.dmn rules.smt2
z3 rules.smt2  # Verify
z32prolog rules.smt2 verified_rules.pl
```

## Python API

### Convert Z3 to DMN

```python
from dmn_prolog_converter.converter import PrologDMNConverter

converter = PrologDMNConverter()

# File-based conversion
dmn_xml = converter.z3_to_dmn("rules.smt2", "rules.dmn")

# String-based conversion
z3_code = """
(declare-const x Int)
(assert (>= x 100))
"""
dmn_xml = converter.z3_string_to_dmn(z3_code)
```

### Convert DMN to Z3

```python
from dmn_prolog_converter.converter import PrologDMNConverter

converter = PrologDMNConverter()

# File-based conversion
z3_code = converter.dmn_to_z3("rules.dmn", "rules.smt2")

# String-based conversion
dmn_xml = """<definitions>...</definitions>"""
z3_code = converter.dmn_string_to_z3(dmn_xml)
```

### Parse Z3 Directly

```python
from dmn_prolog_converter.parser.z3_parser import Z3Parser

parser = Z3Parser()

# Parse Z3 file
model = parser.parse_file("rules.smt2")

# Parse Z3 string
z3_code = "(declare-const x Int)(assert (>= x 100))"
model = parser.parse(z3_code)

# Access parsed data
for decision in model.decisions:
    print(f"Decision: {decision.name}")
    print(f"Inputs: {[v.name for v in decision.inputs]}")
    print(f"Rules: {len(decision.rules)}")
```

### Generate Z3 from IR

```python
from dmn_prolog_converter.generator.z3_generator import Z3Generator
from dmn_prolog_converter.ir.intermediate import (
    DecisionModel, Decision, Rule, Condition,
    Variable, Literal, Expression, DataType, OperatorType
)

# Create decision model
income = Variable(name="Income", data_type=DataType.NUMBER)
tax_rate = Variable(name="TaxRate", data_type=DataType.NUMBER)

condition = Condition(
    expression=Expression(
        operator=OperatorType.GTE,
        operands=[income, Literal(value=100000, data_type=DataType.NUMBER)]
    )
)

rule = Rule(conditions=[condition], conclusions=[])
decision = Decision(name="tax", inputs=[income], outputs=[tax_rate], rules=[rule])
model = DecisionModel(name="TaxModel", decisions=[decision])

# Generate Z3
generator = Z3Generator()
z3_code = generator.generate(model)
print(z3_code)
```

## Advanced Topics

### Verification with Z3

Use Z3 to verify decision logic:

```bash
# Generate Z3 from business rules
prolog2z3 rules.pl rules.smt2

# Check satisfiability
z3 rules.smt2

# Check with additional constraints
cat >> rules.smt2 << 'EOF'
(assert (< Income 0))  ; Test negative income
(check-sat)
EOF
z3 rules.smt2  # Should return "unsat"
```

### Custom Verification Queries

Add verification queries to your Z3 files:

```smt2
; Original rules
(declare-const Income Int)
(declare-const TaxRate Int)
(assert (=> (>= Income 100000) (= TaxRate 35)))

; Verification: Can TaxRate be 35 with income < 100000?
(push)
(assert (= TaxRate 35))
(assert (< Income 100000))
(check-sat)  ; Should be "unsat"
(pop)
```

### Integration with Formal Methods

```python
# Generate Z3 for formal verification
from dmn_prolog_converter.converter import PrologDMNConverter

converter = PrologDMNConverter()
converter.prolog_to_z3("rules.pl", "rules.smt2")

# Run Z3 verification
import subprocess
result = subprocess.run(["z3", "rules.smt2"], capture_output=True, text=True)
if "sat" in result.stdout:
    print("Rules are satisfiable")
else:
    print("Rules have contradictions")
```

## See Also

- [CLI_GUIDE.md](CLI_GUIDE.md) - Complete CLI reference
- [README.md](README.md) - Project overview
- [Z3 Documentation](https://microsoft.github.io/z3guide/) - Official Z3 guide
- [SMT-LIB Standard](http://smtlib.cs.uiowa.edu/) - SMT-LIB format specification

## License

MIT License - see LICENSE file
