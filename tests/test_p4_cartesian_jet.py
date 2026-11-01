"""Regression suite for the unrestricted P4 Cartesian-product identity."""
import io
import unittest
from contextlib import redirect_stdout
from oracles import p4_cartesian_jet_audit as p4


class CartesianP4JetTests(unittest.TestCase):
    def test_complete_unlabeled_oracle_and_jet(self):
        output = io.StringIO()
        with redirect_stdout(output):
            p4.main()
        self.assertIn('Unordered graph pairs checked:    1431', output.getvalue())
        self.assertIn('Third difference at (K2,K2,K2) = 24', output.getvalue())
        self.assertIn('All assertions passed.', output.getvalue())

    def test_non_induced_chords_are_counted(self):
        self.assertEqual(p4.p4_direct(p4.graph_from_mask(4, 63)), 12)
        self.assertEqual(p4.p4_direct(p4.cartesian(p4.graph_from_mask(2, 1),
                                                   p4.graph_from_mask(2, 1))), 4)

    def test_empty_factor_and_unit(self):
        edge = p4.graph_from_mask(2, 1)
        self.assertEqual(p4.p4_direct(p4.cartesian((), edge)), 0)
        self.assertEqual(p4.p4_direct(p4.cartesian(((),), edge)), p4.p4_direct(edge))


if __name__ == '__main__':
    unittest.main()
