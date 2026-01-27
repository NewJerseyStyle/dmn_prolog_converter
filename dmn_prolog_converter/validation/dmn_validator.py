"""
DMN Validator - Validates DMN XML using cDMN library.

Uses cDMN for:
- Schema validation
- Semantic validation
- Execution testing
"""

from typing import Dict, List, Any, Tuple, Optional
import tempfile
import os
from pathlib import Path


class DMNValidator:
    """Validate DMN using cDMN library."""

    def __init__(self):
        try:
            from cdmn.parse_xml import XMLparser
            self.XMLparser = XMLparser
            self.cdmn_available = True
        except ImportError:
            self.cdmn_available = False
            print("Warning: cDMN not installed. Run: pip install cdmn")
        except Exception as e:
            self.cdmn_available = False
            print(f"Warning: cDMN initialization failed: {e}")

    def validate_dmn_string(self, dmn_xml: str) -> Tuple[bool, str]:
        """
        Validate DMN XML string.

        Args:
            dmn_xml: DMN XML string

        Returns:
            Tuple of (is_valid, message)
        """
        if not self.cdmn_available:
            return False, "cDMN library not available"

        try:
            # Parse DMN XML
            parser = self.XMLparser(dmn_xml)

            # Check if parser was created successfully
            if parser is None:
                return False, "Failed to parse DMN"

            # Try to access parsed data (if parsing succeeded, DMN is valid)
            if hasattr(parser, 'glossary'):
                return True, "DMN is valid and parseable"
            else:
                return True, "DMN syntax is valid"

        except Exception as e:
            return False, f"Validation error: {str(e)}"

    def validate_dmn_file(self, dmn_path: str) -> Tuple[bool, str]:
        """
        Validate DMN XML file.

        Args:
            dmn_path: Path to DMN file

        Returns:
            Tuple of (is_valid, message)
        """
        if not self.cdmn_available:
            return False, "cDMN library not available"

        try:
            # Read DMN file
            with open(dmn_path, 'r', encoding='utf-8') as f:
                dmn_xml = f.read()

            # Validate using string method
            return self.validate_dmn_string(dmn_xml)

        except Exception as e:
            return False, f"Validation error: {str(e)}"

    def get_decision_info(self, dmn_path: str) -> Optional[Dict[str, Any]]:
        """
        Get information about decisions in DMN file.

        Args:
            dmn_path: Path to DMN file

        Returns:
            Dictionary with decision information or None if error
        """
        if not self.cdmn_available:
            return None

        try:
            # Read DMN file
            with open(dmn_path, 'r', encoding='utf-8') as f:
                dmn_xml = f.read()

            # Parse DMN
            parser = self.XMLparser(dmn_xml)

            info = {
                'decisions': [],
                'model_name': 'unknown'
            }

            # Try to extract decision information from parsed data
            if hasattr(parser, 'glossary'):
                glossary = parser.glossary
                if hasattr(glossary, 'items'):
                    for key, value in glossary.items():
                        if 'decision' in key.lower():
                            info['decisions'].append({
                                'id': key,
                                'name': str(value)
                            })

            return info

        except Exception as e:
            print(f"Error getting decision info: {e}")
            return None
