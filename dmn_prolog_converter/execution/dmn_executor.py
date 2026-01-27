"""
DMN Executor - Execute DMN decision tables using cDMN.

Provides execution and testing capabilities for DMN files.
"""

from typing import Dict, List, Any, Optional, Tuple
import tempfile
import os


class DMNExecutor:
    """Execute DMN decision tables using cDMN."""

    def __init__(self):
        self.cdmn_available = False
        self.api = None
        # Note: cDMN execution requires idp-engine
        # For now, execution is not supported - validation only works

    def execute_decision(self, dmn_path: str, decision_id: str,
                        input_data: Dict[str, Any]) -> Optional[Dict[str, Any]]:
        """
        Execute a specific decision with given inputs.

        Args:
            dmn_path: Path to DMN file
            decision_id: ID of decision to execute
            input_data: Dictionary of input values

        Returns:
            Dictionary with output values or None if error
        """
        print("Note: DMN execution via cDMN requires additional setup.")
        print("Options:")
        print("  1. Install idp-engine: pip install idp-engine")
        print("  2. Use external DMN engines (Camunda, Drools, etc.)")
        print("  3. Use the generated DMN in your existing DMN platform")
        return None

    def execute_decision_string(self, dmn_xml: str, decision_id: str,
                               input_data: Dict[str, Any]) -> Optional[Dict[str, Any]]:
        """
        Execute a decision from DMN XML string.

        Args:
            dmn_xml: DMN XML string
            decision_id: ID of decision to execute
            input_data: Dictionary of input values

        Returns:
            Dictionary with output values or None if error
        """
        if not self.cdmn_available:
            return None

        try:
            # Write to temporary file
            with tempfile.NamedTemporaryFile(mode='w', suffix='.dmn', delete=False, encoding='utf-8') as f:
                f.write(dmn_xml)
                temp_path = f.name

            try:
                result = self.execute_decision(temp_path, decision_id, input_data)
                return result

            finally:
                # Clean up
                if os.path.exists(temp_path):
                    os.unlink(temp_path)

        except Exception as e:
            print(f"Execution error: {e}")
            return None

    def batch_execute(self, dmn_path: str, decision_id: str,
                     test_cases: List[Dict[str, Any]]) -> List[Optional[Dict[str, Any]]]:
        """
        Execute multiple test cases.

        Args:
            dmn_path: Path to DMN file
            decision_id: ID of decision to execute
            test_cases: List of input dictionaries

        Returns:
            List of output dictionaries
        """
        results = []
        for test_case in test_cases:
            result = self.execute_decision(dmn_path, decision_id, test_case)
            results.append(result)
        return results


class PrologExecutor:
    """Execute Prolog code for comparison with DMN."""

    def __init__(self):
        self.prolog_available = False
        try:
            from pyswip import Prolog
            self.Prolog = Prolog
            self.prolog_available = True
        except ImportError:
            print("Warning: PySwip not installed. Prolog execution disabled.")
            print("Install with: pip install pyswip")
        except Exception as e:
            print(f"Warning: PySwip initialization failed: {e}")
            print("Prolog execution disabled.")

    def execute_query(self, prolog_path: str, predicate: str,
                     args: Dict[str, Any]) -> Optional[List[Dict[str, Any]]]:
        """
        Execute Prolog query.

        Args:
            prolog_path: Path to Prolog file
            predicate: Predicate name
            args: Dictionary of argument values

        Returns:
            List of result bindings or None if error
        """
        if not self.prolog_available:
            return None

        try:
            prolog = self.Prolog()

            # Consult the file
            prolog.consult(prolog_path)

            # Build query string
            # Convert args dict to Prolog terms
            arg_strs = []
            for key, value in args.items():
                if isinstance(value, str):
                    arg_strs.append(f"'{value}'")
                else:
                    arg_strs.append(str(value))

            # Add output variables
            output_vars = [k for k in args.keys() if k.startswith('_')]
            for var in output_vars:
                arg_strs.append(var)

            query = f"{predicate}({','.join(arg_strs)})"

            # Execute query
            results = list(prolog.query(query))
            return results

        except Exception as e:
            print(f"Prolog execution error: {e}")
            return None


class ExecutionTester:
    """Test that Prolog and DMN produce same results."""

    def __init__(self):
        self.dmn_executor = DMNExecutor()
        self.prolog_executor = PrologExecutor()

    def compare_execution(self, prolog_path: str, dmn_path: str,
                         decision_id: str, test_cases: List[Dict[str, Any]]) -> Dict[str, Any]:
        """
        Compare Prolog and DMN execution results.

        Args:
            prolog_path: Path to Prolog file
            dmn_path: Path to DMN file
            decision_id: Decision/predicate name
            test_cases: List of test cases with inputs and expected outputs

        Returns:
            Dictionary with comparison results
        """
        results = {
            'total_tests': len(test_cases),
            'passed': 0,
            'failed': 0,
            'errors': [],
            'details': []
        }

        for i, test_case in enumerate(test_cases):
            test_result = {
                'test_num': i + 1,
                'inputs': test_case.get('inputs', {}),
                'expected': test_case.get('expected', {}),
                'dmn_result': None,
                'prolog_result': None,
                'match': False,
                'error': None
            }

            try:
                # Execute DMN
                dmn_inputs = test_case.get('inputs', {})
                dmn_result = self.dmn_executor.execute_decision(dmn_path, decision_id, dmn_inputs)
                test_result['dmn_result'] = dmn_result

                # Execute Prolog (if available)
                if self.prolog_executor.prolog_available:
                    prolog_result = self.prolog_executor.execute_query(
                        prolog_path, decision_id, dmn_inputs
                    )
                    test_result['prolog_result'] = prolog_result

                    # Compare results
                    if dmn_result and prolog_result:
                        # Simple comparison (can be enhanced)
                        test_result['match'] = self._compare_results(dmn_result, prolog_result)

                # Check against expected
                expected = test_case.get('expected', {})
                if expected and dmn_result:
                    match_expected = all(
                        dmn_result.get(k) == v for k, v in expected.items()
                    )
                    if match_expected:
                        results['passed'] += 1
                    else:
                        results['failed'] += 1
                        test_result['error'] = f"Expected {expected}, got {dmn_result}"
                else:
                    # No expected result, just check DMN ran
                    if dmn_result:
                        results['passed'] += 1

            except Exception as e:
                results['failed'] += 1
                test_result['error'] = str(e)
                results['errors'].append(f"Test {i+1}: {str(e)}")

            results['details'].append(test_result)

        return results

    def _compare_results(self, dmn_result: Dict[str, Any],
                        prolog_result: List[Dict[str, Any]]) -> bool:
        """Compare DMN and Prolog results."""
        if not prolog_result:
            return False

        # Take first Prolog result (deterministic rules should have only one)
        if len(prolog_result) > 0:
            prolog_first = prolog_result[0]
            # Simple key-value comparison
            for key, value in dmn_result.items():
                if key in prolog_first and prolog_first[key] != value:
                    return False
            return True

        return False

    def generate_test_report(self, results: Dict[str, Any]) -> str:
        """Generate human-readable test report."""
        lines = []
        lines.append("=" * 60)
        lines.append("EXECUTION TEST REPORT")
        lines.append("=" * 60)
        lines.append(f"Total Tests: {results['total_tests']}")
        lines.append(f"Passed: {results['passed']}")
        lines.append(f"Failed: {results['failed']}")
        lines.append(f"Success Rate: {results['passed']/results['total_tests']*100:.1f}%")
        lines.append("")

        if results['errors']:
            lines.append("ERRORS:")
            for error in results['errors']:
                lines.append(f"  - {error}")
            lines.append("")

        lines.append("DETAILS:")
        for detail in results['details']:
            lines.append(f"\nTest {detail['test_num']}:")
            lines.append(f"  Inputs: {detail['inputs']}")
            lines.append(f"  Expected: {detail.get('expected', 'N/A')}")
            lines.append(f"  DMN Result: {detail.get('dmn_result', 'N/A')}")
            if detail.get('prolog_result'):
                lines.append(f"  Prolog Result: {detail.get('prolog_result', 'N/A')}")
            if detail.get('error'):
                lines.append(f"  Error: {detail['error']}")

        lines.append("=" * 60)
        return "\n".join(lines)
