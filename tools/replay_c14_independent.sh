#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root/oracles/c14"
g++ -std=c++20 -O3 -Wall -Wextra c14_words.cpp -o /tmp/gpr-c14-words
g++ -std=c++20 -O3 -Wall -Wextra c14_even_blocks.cpp -o /tmp/gpr-c14-even-blocks
/tmp/gpr-c14-words > /tmp/gpr-c14-words.txt
/tmp/gpr-c14-even-blocks > /tmp/gpr-c14-even-blocks.txt
python3 chord_recurrence.py > /tmp/gpr-c14-recurrence.txt
python3 chord_matching.py > /tmp/gpr-c14-chords.txt
python3 chord_bijection_check.py > /tmp/gpr-c14-bijection.txt
python3 - <<'PY'
from pathlib import Path
import re
a=Path('/tmp/gpr-c14-words.txt').read_text()
b=Path('/tmp/gpr-c14-even-blocks.txt').read_text()
for k,v in {4:392,5:33530,6:89782,7:38232}.items():
    assert f"P[{k}]={v}" in a
    assert re.search(rf"even_partitions\[{k}\]=\d+ simple\[{k}\]={v}",b)
for n,v in {4:5376,5:4652160,6:203258880,7:3337213440}.items():
    assert re.search(rf"Q{n} root_oriented=\d+ cycles={v}",a)
assert 'agreements 135135 mismatches []' in Path('/tmp/gpr-c14-bijection.txt').read_text()
assert 'corrected_sigma7: 880865280' in Path('/tmp/gpr-c14-recurrence.txt').read_text()
print("PASS ALL independent c14 cycle-count / chord / symbol checks")
PY
echo "Mojo source is in experiments/c14; no Mojo SDK was available during initial local verification."
