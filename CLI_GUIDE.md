# Command-Line Interface Guide

Complete guide to using the DMN-Prolog Converter CLI tools.

## Installation

```bash
pip install dmn-prolog-converter[validation]
```

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

### Version Command

Show version and installed dependencies.

**Syntax:**
```bash
dmn-prolog version
```

**Output:**
```
DMN-Prolog Converter v1.0.0

Installed packages:
  lark: 1.3.1
  lxml: 6.0.2
  cdmn: installed (validation enabled)
  pyswip: not installed (Prolog execution disabled)

Documentation: https://github.com/yourusername/dmn-prolog-converter
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

## Batch Processing

### Convert Multiple Files

**Bash/Linux:**
```bash
# Convert all .pl files to .dmn
for file in *.pl; do
    dmn-prolog convert "$file" "${file%.pl}.dmn"
done
```

**PowerShell:**
```powershell
# Convert all .pl files to .dmn
Get-ChildItem *.pl | ForEach-Object {
    $output = $_.BaseName + ".dmn"
    dmn-prolog convert $_.Name $output
}
```

**Python:**
```python
import os
import subprocess

for file in os.listdir('.'):
    if file.endswith('.pl'):
        output = file.replace('.pl', '.dmn')
        subprocess.run(['dmn-prolog', 'convert', file, output])
```

### Validate Multiple Files

**Bash:**
```bash
for file in *.dmn; do
    echo "Validating $file"
    dmn-prolog validate "$file"
done
```

**Python:**
```python
import os
import subprocess

dmn_files = [f for f in os.listdir('.') if f.endswith('.dmn')]
for file in dmn_files:
    print(f"Validating {file}")
    subprocess.run(['dmn-prolog', 'validate', file])
```

## Exit Codes

All commands return standard exit codes:

- `0` - Success
- `1` - Error (file not found, validation failed, etc.)

**Example usage in scripts:**

```bash
#!/bin/bash

if dmn-prolog convert rules.pl rules.dmn; then
    echo "Conversion successful!"
    dmn-prolog validate rules.dmn
else
    echo "Conversion failed!"
    exit 1
fi
```

## Integration with CI/CD

### GitHub Actions

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

### GitLab CI

```yaml
validate_dmn:
  image: python:3.9
  script:
    - pip install dmn-prolog-converter[validation]
    - dmn-prolog convert rules.pl rules.dmn
    - dmn-prolog validate rules.dmn
    - dmn-prolog roundtrip rules.pl
```

### Pre-commit Hook

Create `.git/hooks/pre-commit`:

```bash
#!/bin/bash

# Validate all changed Prolog files
for file in $(git diff --cached --name-only --diff-filter=ACM | grep '\.pl$'); do
    echo "Validating $file"

    # Convert to DMN
    dmn_file="${file%.pl}.dmn"
    dmn-prolog convert "$file" "$dmn_file"

    # Validate roundtrip
    if ! dmn-prolog roundtrip "$file"; then
        echo "Roundtrip validation failed for $file"
        exit 1
    fi
done

exit 0
```

## Advanced Usage

### Custom Python Scripts

```python
#!/usr/bin/env python3
from dmn_prolog_converter.cli import convert_command

# Programmatic conversion
result = convert_command('input.pl', 'output.dmn', validate=True)
if result == 0:
    print("Success!")
```

### Piping and Redirection

```bash
# Capture output
dmn-prolog info rules.pl > info.txt

# Error handling
dmn-prolog convert rules.pl rules.dmn 2> errors.log

# Silent mode
dmn-prolog validate rules.dmn > /dev/null 2>&1 && echo "Valid"
```

## Troubleshooting

### Command not found: dmn-prolog

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

### Permission denied

```bash
# Linux/macOS: Make sure pip installed correctly
pip install --user dmn-prolog-converter[validation]

# Or install in virtual environment
python -m venv venv
source venv/bin/activate
pip install dmn-prolog-converter[validation]
```

### Validation not working

```bash
# Install validation dependencies
pip install dmn-prolog-converter[validation]

# Or install cdmn separately
pip install cdmn
```

## Environment Variables

Set these environment variables to customize behavior:

```bash
# Disable validation warnings
export DMN_NO_VALIDATION_WARNINGS=1

# Set default hit policy
export DMN_DEFAULT_HIT_POLICY=FIRST
```

## Examples

### Complete Workflow

```bash
# 1. Create Prolog rules
cat > loan_rules.pl << 'EOF'
eligible_for_loan(Credit, Income, Decision) :-
    Credit >= 700,
    Income >= 50000,
    Decision = approved.
EOF

# 2. Convert to DMN
dmn-prolog convert loan_rules.pl loan_rules.dmn

# 3. Validate DMN
dmn-prolog validate loan_rules.dmn

# 4. Show info
dmn-prolog info loan_rules.dmn

# 5. Test roundtrip
dmn-prolog roundtrip loan_rules.pl
```

### Batch Conversion with Validation

```bash
#!/bin/bash

for prolog_file in src/rules/*.pl; do
    base=$(basename "$prolog_file" .pl)
    dmn_file="dmn/$base.dmn"

    echo "Processing $base..."

    # Convert
    if dmn-prolog convert "$prolog_file" "$dmn_file"; then
        echo "  [OK] Converted"

        # Validate
        if dmn-prolog validate "$dmn_file"; then
            echo "  [OK] Validated"
        else
            echo "  [FAIL] Validation failed"
            exit 1
        fi
    else
        echo "  [FAIL] Conversion failed"
        exit 1
    fi
done

echo "All files processed successfully!"
```

## See Also

- [INSTALL.md](INSTALL.md) - Installation guide
- [QUICK_START.md](QUICK_START.md) - Quick start
- [USAGE_GUIDE.md](USAGE_GUIDE.md) - Detailed usage
- [README.md](README.md) - Full documentation
