"""Regression suite for the unrestricted P4 Cartesian-product identity."""
import hashlib
import io
import json
import re
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

from oracles import p4_cartesian_jet_audit as p4


ROOT = Path(__file__).resolve().parents[1]
RECEIPT = Path("conformance/receipts/p4-cartesian-jet-2026-11-01.json")
ORACLE = Path("oracles/p4_cartesian_jet_audit.py")


def unique_fields(pairs):
    fields = {}
    for key, value in pairs:
        if key in fields:
            raise ValueError(f"duplicate receipt field: {key}")
        fields[key] = value
    return fields


def verify_source_receipt(root):
    receipt = json.loads((root / RECEIPT).read_bytes(), object_pairs_hook=unique_fields)
    if not isinstance(receipt, dict):
        raise ValueError("receipt must be a JSON object")
    if receipt.get("schema") != "gpr-p4-cartesian-jet-audit-v1":
        raise ValueError("invalid receipt schema")
    if receipt.get("claim") != "GPR-P4-CARTESIAN-JET":
        raise ValueError("invalid receipt claim")
    if receipt.get("source") != ORACLE.as_posix():
        raise ValueError("invalid receipt source")
    expected = receipt.get("source_sha256")
    if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{64}", expected):
        raise ValueError("source_sha256 must be 64 lowercase hexadecimal characters")
    actual = hashlib.sha256((root / ORACLE).read_bytes()).hexdigest()
    if actual != expected:
        raise ValueError(f"oracle SHA-256 mismatch: receipt={expected}, actual={actual}")


class SourceReceiptTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.oracle = self.root / ORACLE
        self.receipt = self.root / RECEIPT
        for path in (ORACLE, RECEIPT):
            (self.root / path).parent.mkdir(parents=True, exist_ok=True)
            (self.root / path).write_bytes((ROOT / path).read_bytes())

    def test_committed_source_matches_receipt(self):
        verify_source_receipt(ROOT)

    def test_source_edit_without_receipt_regeneration(self):
        with self.oracle.open("ab") as source:
            source.write(b"\n# provenance negative control\n")
        with self.assertRaisesRegex(ValueError, "oracle SHA-256 mismatch"):
            verify_source_receipt(self.root)

    def test_incorrect_well_formed_hash(self):
        receipt = json.loads(self.receipt.read_bytes())
        receipt["source_sha256"] = "0" * 64
        self.receipt.write_text(json.dumps(receipt), encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "oracle SHA-256 mismatch"):
            verify_source_receipt(self.root)

    def test_malformed_receipts(self):
        valid = json.loads(self.receipt.read_bytes())
        missing = valid.copy()
        del missing["source_sha256"]
        cases = (
            ("invalid JSON", "{", "Expecting"),
            ("non-object", "[]", "JSON object"),
            ("missing hash", json.dumps(missing), "source_sha256"),
            ("non-string hash", json.dumps(dict(valid, source_sha256=123)), "source_sha256"),
            ("short hash", json.dumps(dict(valid, source_sha256="abcd")), "source_sha256"),
            ("non-hex hash", json.dumps(dict(valid, source_sha256="g" * 64)), "source_sha256"),
            ("wrong source", json.dumps(dict(valid, source="../other.py")), "invalid receipt source"),
            ("duplicate hash", json.dumps(valid)[:-1] + ', "source_sha256": null}', "duplicate"),
        )
        for label, content, error in cases:
            with self.subTest(label=label):
                self.receipt.write_text(content, encoding="utf-8")
                with self.assertRaisesRegex(ValueError, error):
                    verify_source_receipt(self.root)


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
