# Installation Guide

## Install from pip (Recommended)

Once published to PyPI:

```bash
# Basic installation (conversion only)
pip install dmn-prolog-converter

# With validation support
pip install dmn-prolog-converter[validation]

# With all optional features
pip install dmn-prolog-converter[execution]
```

## Install from Source

### Clone and Install

```bash
# Clone repository
git clone https://github.com/yourusername/dmn-prolog-converter.git
cd dmn-prolog-converter

# Install in development mode
pip install -e .

# Or install with optional dependencies
pip install -e .[validation,execution]
```

### Install from Local Directory

```bash
# If you have the source code locally
cd dmn-prolog-converter
pip install .

# With optional dependencies
pip install .[validation]
```

## Verify Installation

```bash
# Check version
dmn-prolog version

# Show help
dmn-prolog --help

# Test conversion
dmn-prolog convert tests/examples/tax_bracket.pl output.dmn
```

## Command-Line Tools

After installation, you'll have these commands available:

```bash
dmn-prolog          # Main CLI tool
prolog2dmn          # Shortcut: Prolog to DMN
dmn2prolog          # Shortcut: DMN to Prolog
```

## Dependencies

### Required

- Python >= 3.8
- lark >= 1.1.9 (Prolog parsing)
- lxml >= 5.1.0 (DMN XML generation)

### Optional

- cdmn >= 0.1.0 (DMN validation) - Install with `[validation]`
- pyswip >= 0.2.10 (Prolog execution) - Install with `[execution]`

## Platform-Specific Notes

### Windows

```bash
pip install dmn-prolog-converter
```

No additional setup required.

### macOS

```bash
pip install dmn-prolog-converter
```

For Prolog execution support (optional):
```bash
brew install swi-prolog
pip install pyswip
```

### Linux (Ubuntu/Debian)

```bash
pip install dmn-prolog-converter
```

For Prolog execution support (optional):
```bash
sudo apt-get install swi-prolog
pip install pyswip
```

## Virtual Environment (Recommended)

```bash
# Create virtual environment
python -m venv venv

# Activate (Windows)
venv\Scripts\activate

# Activate (macOS/Linux)
source venv/bin/activate

# Install
pip install dmn-prolog-converter[validation]
```

## Development Installation

For contributing or development:

```bash
# Clone repository
git clone https://github.com/yourusername/dmn-prolog-converter.git
cd dmn-prolog-converter

# Install in development mode with dev dependencies
pip install -e .[validation,execution,dev]

# Run tests
pytest tests/

# Format code
black dmn_prolog_converter/
```

## Troubleshooting

### Import Error: No module named 'dmn_prolog_converter'

**Solution:** Make sure installation completed successfully:
```bash
pip install --force-reinstall dmn-prolog-converter
```

### Command not found: dmn-prolog

**Solution:** Ensure pip's bin directory is in your PATH:
```bash
# Check where pip installs scripts
python -m pip show dmn-prolog-converter

# Add to PATH (Linux/macOS)
export PATH="$HOME/.local/bin:$PATH"

# Or use python -m
python -m dmn_prolog_converter.cli --help
```

### cDMN validation not working

**Solution:** Install validation dependencies:
```bash
pip install dmn-prolog-converter[validation]
```

### Prolog execution not working

**Solution:** Install SWI-Prolog and pyswip:
```bash
# Install SWI-Prolog (platform-specific)
# Windows: Download from https://www.swi-prolog.org/
# macOS: brew install swi-prolog
# Linux: sudo apt-get install swi-prolog

# Install pyswip
pip install pyswip
```

## Uninstall

```bash
pip uninstall dmn-prolog-converter
```

## Upgrade

```bash
# Upgrade to latest version
pip install --upgrade dmn-prolog-converter

# Upgrade with optional dependencies
pip install --upgrade dmn-prolog-converter[validation]
```

## Next Steps

After installation, see:
- [QUICK_START.md](QUICK_START.md) - Get started quickly
- [USAGE_GUIDE.md](USAGE_GUIDE.md) - Detailed usage
- [README.md](README.md) - Full documentation

## Support

- Issues: https://github.com/yourusername/dmn-prolog-converter/issues
- Documentation: https://github.com/yourusername/dmn-prolog-converter
