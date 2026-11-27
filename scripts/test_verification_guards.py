#!/usr/bin/env python3
"""Regression tests for the lightweight proof-admission and axiom guards."""
import re
import unittest

from check_axioms import check_output
from check_no_admissions import code_only


class GuardTests(unittest.TestCase):
    def test_nested_comments_and_strings_are_skipped(self):
        text = '/- sorry /- axiom -/ admit -/ "sorry" -- axiom\ntheorem good := True.intro'
        self.assertIsNone(re.search(r"\b(?:sorry|admit|axiom)\b", code_only(text)))

    def test_real_admission_survives(self):
        self.assertIn("sorry", code_only("theorem bad : True := by sorry"))

    def test_axiom_command_survives(self):
        self.assertIn("axiom", code_only("axiom bad : False"))

    def test_standard_axioms(self):
        check_output("theorem depends on axioms: [propext, Classical.choice, Quot.sound]")

    def test_unfinished_proof_axiom_rejected(self):
        with self.assertRaises(ValueError):
            check_output("theorem depends on axioms: [propext, sorryAx]")

    def test_other_nonstandard_axiom_rejected(self):
        with self.assertRaises(ValueError):
            check_output("theorem depends on axioms: [unproved_main_theorem]")

    def test_empty_audit_rejected(self):
        with self.assertRaises(ValueError):
            check_output("no declarations were checked")


if __name__ == "__main__":
    unittest.main()
