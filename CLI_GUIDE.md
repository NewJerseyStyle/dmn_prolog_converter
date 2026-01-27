# Command-Line Interface Guide

Complete guide to using the DMN-Prolog Converter CLI tools.

## Available Commands

After installation, you have access to these commands:

```bash
dmn-prolog          # Main CLI tool with subcommands
prolog2dmn          # Quick shortcut: Prolog → DMN
dmn2prolog          # Quick shortcut: DMN → Prolog
```

## Main CLI: dmn-prolog

### Show Help

```bash
dmn-prolog --help
dmn-prolog convert --help
```

### Convert Command

Convert between Prolog and DMN formats.

**Syntax:**
```bash
dmn-prolog convert <input> <output> [options]
```

**Examples:**

```bash
# Prolog to DMN (with validation)
dmn-prolog convert rules.pl rules.dmn

# DMN to Prolog
dmn-prolog convert rules.dmn rules.pl

# Skip validation
dmn-prolog convert rules.pl rules.dmn --no-validate
```

**Options:**
- `--no-validate` - Skip DMN validation (faster, but not recommended)

### Validate Command

Validate DMN files using cDMN.

**Syntax:**
```bash
dmn-prolog validate <file.dmn>
```

**Examples:**

```bash
# Validate DMN file
dmn-prolog validate rules.dmn

# Output
[OK] DMN syntax is valid
```

### Roundtrip Command

Test that Prolog → DMN → Prolog conversion preserves logic.

**Syntax:**
```bash
dmn-prolog roundtrip <file.pl>
```

**Examples:**

```bash
# Test roundtrip conversion
dmn-prolog roundtrip tax_rules.pl

# Output
Testing roundtrip conversion: tax_rules.pl
  Prolog -> DMN -> Prolog
[OK] Roundtrip validation successful
```

### Info Command

Show detailed information about a file.

**Syntax:**
```bash
dmn-prolog info <file>
```

**Examples:**

```bash
# Inspect Prolog file
dmn-prolog info rules.pl

# Output
File Information: rules.pl
  Type: .pl
  Size: 1234 bytes
  Format: Prolog
  Decisions: 3

  Decision: tax_bracket
    Inputs: Income
    Outputs: TaxRate
    Rules: 5
```

```bash
# Inspect DMN file
dmn-prolog info rules.dmn

# Output
File Information: rules.dmn
  Type: .dmn
  Size: 5678 bytes
  Format: DMN
  Model: TaxModel
  Decisions: 3

  Decision: tax_bracket
    Inputs: Income
    Outputs: TaxRate
    Rules: 5
    Hit Policy: UNIQUE
```

## Quick Shortcuts

### prolog2dmn

Quickly convert Prolog to DMN.

**Syntax:**
```bash
prolog2dmn <input.pl> <output.dmn>
```

**Examples:**

```bash
prolog2dmn tax_rules.pl tax_rules.dmn
```

Equivalent to:
```bash
dmn-prolog convert tax_rules.pl tax_rules.dmn
```

### dmn2prolog

Quickly convert DMN to Prolog.

**Syntax:**
```bash
dmn2prolog <input.dmn> <output.pl>
```

**Examples:**

```bash
dmn2prolog tax_rules.dmn tax_rules.pl
```

Equivalent to:
```bash
dmn-prolog convert tax_rules.dmn tax_rules.pl
```

## Use with Python Module

If the CLI isn't in your PATH, use Python module syntax:

```bash
python -m dmn_prolog_converter.cli --help
python -m dmn_prolog_converter.cli convert input.pl output.dmn
python -m dmn_prolog_converter.cli version
```

## Exit Codes

All commands return standard exit codes:

- `0` - Success
- `1` - Error (file not found, validation failed, etc.)

## Integration with GitHub Actions

```yaml
name: Validate DMN

on: [push, pull_request]

jobs:
  validate:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2

      - name: Setup Python
        uses: actions/setup-python@v2
        with:
          python-version: '3.9'

      - name: Install converter
        run: pip install dmn-prolog-converter[validation]

      - name: Convert Prolog to DMN
        run: dmn-prolog convert rules.pl rules.dmn

      - name: Validate DMN
        run: dmn-prolog validate rules.dmn

      - name: Test roundtrip
        run: dmn-prolog roundtrip rules.pl
```

## Troubleshooting: `Command not found: dmn-prolog`

**Solution 1:** Add pip scripts directory to PATH

```bash
# Find scripts directory
pip show dmn-prolog-converter | grep Location

# Add to PATH (Linux/macOS)
export PATH="$HOME/.local/bin:$PATH"

# Add to PATH (Windows)
set PATH=%APPDATA%\Python\Scripts;%PATH%
```

**Solution 2:** Use python -m

```bash
python -m dmn_prolog_converter.cli convert input.pl output.dmn
```

## Environment Variables

Set these environment variables to customize behavior:

```bash
# Disable validation warnings
export DMN_NO_VALIDATION_WARNINGS=1

# Set default hit policy
export DMN_DEFAULT_HIT_POLICY=FIRST
```

## See Also

- [README.md](README.md) - Full documentation
