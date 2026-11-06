#!/usr/bin/env python3
"""Bind the bundled manuscript and correspondence labels to the Overleaf export."""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent


def check(aux_path=None):
    """Verify the immutable source and optionally fresh correspondence numbers."""
    record = json.loads((ROOT / 'manuscript/source.json').read_text())
    source = (ROOT / record['bundled_source']).read_bytes()
    actual = hashlib.sha256(source).hexdigest()
    if actual != record['source_sha256']:
        raise ValueError('Bundled TeX differs from the recorded Overleaf snapshot')
    text = source.decode('utf-8')
    for label in record['labels']:
        if text.count('\\label{' + label + '}') != 1:
            raise ValueError('Missing or repeated correspondence label: ' + label)
    for marker in ['% BEGIN SHORT PAPER', '% END SHORT PAPER', '% BEGIN FULL PAPER']:
        if text.count(marker) != 1:
            raise ValueError('Missing or repeated source boundary: ' + marker)
    if aux_path:
        aux = Path(aux_path).read_text()
        for label, number in record['labels'].items():
            match = re.search(r'\\newlabel\{' + re.escape(label) + r'\}\{\{([^}]+)\}', aux)
            if match is None or match.group(1) != number:
                raise ValueError('Correspondence number differs from fresh TeX build: ' + label)
    return {'status': 'passed', 'source_sha256': actual,
            'correspondence_labels': len(record['labels']),
            'fresh_numbers_checked': aux_path is not None}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--aux', type=Path, help='Also verify numbers from a fresh TeX build')
    args = parser.parse_args()
    print(json.dumps(check(args.aux), indent=2))


if __name__ == '__main__':
    main()
