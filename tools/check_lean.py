"""Replay the pinned Lean build and inspect transitive axioms of the API."""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT / 'formal'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def check(output, expected):
    records = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.S)
    if {name for name, _ in records} != set(expected) or len(records) != len(expected):
        raise RuntimeError('missing, duplicate, or unexpected axiom audit records:\n'+output)
    for name, axioms in records:
        actual = {a.strip() for a in axioms.split(',') if a.strip()}
        if actual - ALLOWED:
            raise RuntimeError(f'{name}: unapproved axioms {actual - ALLOWED}')
    return len(records)


def run():
    subprocess.run(['lake', 'build'], cwd=FORMAL, check=True)
    result = subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', 'Axioms.lean'],
                            cwd=FORMAL, check=True, text=True, capture_output=True)
    expected = re.findall(r'^#print axioms (\S+)$', (FORMAL/'Axioms.lean').read_text(), re.M)
    count = check(result.stdout, expected)
    print(result.stdout, end='')
    print(f'Lean kernel build and {count} transitive axiom audits: PASS')


if __name__ == '__main__':
    run()
