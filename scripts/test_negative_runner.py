"""Unit tests for the negative-test runner's process boundary."""

import importlib.util
from pathlib import Path
import unittest

SPEC = importlib.util.spec_from_file_location(
    "run_negative_tests", Path(__file__).with_name("run_negative_tests.py")
)
RUNNER = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(RUNNER)


class NegativeRunnerTests(unittest.TestCase):
    def test_expected_type_error_passes(self):
        self.assertIsNone(
            RUNNER.classify(1, "fixture.lean:2:1: error: Type mismatch")
        )
        self.assertIsNone(
            RUNNER.classify(
                1,
                "fixture.lean:2:1: error(lean.synthInstanceFailed): failed to synthesize",
            )
        )

    def test_infrastructure_and_fixture_failures_do_not_pass(self):
        cases = [
            (0, ""),
            (127, "lean: command not found"),
            (137, "fixture.lean:2:1: error: Type mismatch"),
            (1, "internal compiler failure"),
            (1, "fixture.lean:1:0: error: unknown module prefix 'Missing'"),
            (1, "fixture.lean:2:1: error: Unknown identifier `renamedAPI`"),
            (1, "fixture.lean:2:1: error: unexpected token '}'"),
        ]
        for status, output in cases:
            with self.subTest(status=status, output=output):
                self.assertIsNotNone(RUNNER.classify(status, output))

    def test_timeout_is_an_error_message(self):
        self.assertIn("timed out", "compiler timed out after 0.05s")


if __name__ == "__main__":
    unittest.main()
