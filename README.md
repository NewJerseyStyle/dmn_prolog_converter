# DMN-Prolog Bidirectional Converter

[![Test DMN-Prolog-Z3 Converter](https://github.com/NewJerseyStyle/dmn_prolog_converter/actions/workflows/test.yml/badge.svg)](https://github.com/NewJerseyStyle/dmn_prolog_converter/actions/workflows/test.yml)
[![PyPI - Version](https://img.shields.io/pypi/v/dmn-prolog-converter)](https://pypi.org/project/dmn-prolog-converter/)

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
dmn-prolog          # Main CLI tool with subcommands
prolog2dmn          # Quick shortcut: Prolog → DMN
dmn2prolog          # Quick shortcut: DMN → Prolog
z32dmn              # Quick shortcut: Z3 → DMN
dmn2z3              # Quick shortcut: DMN → Z3
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
dmn-prolog info rules.smt2

# Quick shortcuts
prolog2dmn input.pl output.dmn
dmn2prolog input.dmn output.pl
z32dmn input.smt2 output.dmn
dmn2z3 input.dmn output.smt2
```

See [CLI_GUIDE.md](CLI_GUIDE.md) for complete CLI documentation.

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
