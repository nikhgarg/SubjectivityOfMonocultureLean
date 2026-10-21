"""Check public audit metadata; optionally replay its privately retained inputs.

The default checks schemas and exact code identity without private credentials.
Replay delegates to the pinned AML owners and never issues mathematical acceptance.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

import jsonschema


def relative_path(name: str) -> PurePosixPath:
    relative = PurePosixPath(name)
    if (not name or not relative.parts or relative.is_absolute() or str(relative) != name
            or any(part in {'.', '..', '.git', '.lake'} for part in relative.parts)
            or '\\' in name):
        raise ValueError('Unbounded artifact path: ' + name)
    return relative


def regular_file(root: Path, name: str) -> Path:
    relative = relative_path(name)
    path = root
    for part in relative.parts:
        path /= part
        if path.is_symlink():
            raise ValueError('Artifact path uses a symlink: ' + name)
    if not path.is_file():
        raise ValueError('Missing artifact: ' + name)
    return path


def schema_references(value):
    if isinstance(value, dict):
        if isinstance(value.get('$ref'), str):
            yield value['$ref']
        for child in value.values():
            yield from schema_references(child)
    elif isinstance(value, list):
        for child in value:
            yield from schema_references(child)


def git(root: Path, *args: str) -> bytes:
    return subprocess.run(['git', '-C', str(root), *args], check=True,
                          capture_output=True).stdout


def verify(root: Path, aml_root: Path | None, snapshot: Path | None) -> dict:
    schema_dir = root / 'audit/schemas'
    pins = {}
    for line in (schema_dir / 'SHA256SUMS').read_text().splitlines():
        match = re.fullmatch(r'([0-9a-f]{64})  ([A-Za-z0-9_.-]+\.json)', line)
        if match is None or match[2] in pins:
            raise ValueError('Invalid or duplicate schema pin')
        pins[match[2]] = match[1]
    if not pins or set(pins) != {p.name for p in schema_dir.glob('*.json')}:
        raise ValueError('Schema pins do not cover the complete schema bundle')
    for name, pin in pins.items():
        raw = regular_file(schema_dir, name).read_bytes()
        if hashlib.sha256(raw).hexdigest() != pin:
            raise ValueError('Schema copy differs from its pin: ' + name)
        schema = json.loads(raw)
        for reference in schema_references(schema):
            target = reference.split('#', 1)[0]
            if target and target not in pins:
                raise ValueError('Schema reference is absent from the pinned bundle: ' + reference)
        if name.endswith('.schema.json'):
            jsonschema.Draft7Validator.check_schema(schema)
        if aml_root is not None and regular_file(aml_root, 'config/' + name).read_bytes() != raw:
            raise ValueError('Schema copy differs from the selected AML owner: ' + name)
    descriptor = json.loads(regular_file(root, 'audit/aml_audit_source.json').read_bytes())
    schema = json.loads((schema_dir / 'audit_repository_source.schema.json').read_bytes())
    jsonschema.Draft7Validator(schema).validate(descriptor)
    rows = descriptor['code_bindings']
    declared = {row['path'] for row in rows}
    if len(declared) != len(rows):
        raise ValueError('Duplicate code binding')
    entries = []
    for item in git(root, 'ls-tree', '-rz', descriptor['code_revision']).split(b'\0'):
        if item:
            metadata, name = item.split(b'\t', 1)
            _mode, kind, sha = metadata.decode().split()
            entries.append({'path': name.decode(), 'type': kind, 'sha': sha})
    selected = lambda name: name.endswith('.lean') and any(
        name == prefix or name.startswith(prefix + '/') for prefix in descriptor['code_roots'])
    pinned = {row['path']: row['sha'] for row in entries
              if row['type'] == 'blob' and selected(row['path'])}
    current = set()
    for prefix in descriptor['code_roots']:
        relative_path(prefix)
        path = root / prefix
        if path.is_dir():
            current.update(p.relative_to(root).as_posix() for p in path.rglob('*.lean'))
        elif path.is_file():
            current.add(prefix)
    if declared != set(pinned) or declared != current:
        raise ValueError('Code bindings do not cover the pinned and current module inventory')
    for row in rows:
        raw = regular_file(root, row['path']).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        if (hashlib.sha256(raw).hexdigest() != row['sha256']
                or blob != row['git_blob_sha1'] or blob != pinned[row['path']]):
            raise ValueError('Code differs from its pinned binding: ' + row['path'])
    if aml_root is not None:
        sys.path.insert(0, str(aml_root))
        from scripts import audit_repository_sources as sources
        from scripts import audit_snapshot_transport as transport
        sources.validate_descriptor(descriptor)
        tree = {'truncated': False, 'tree': entries}
        sources.verify_code_binding(descriptor, tree, snapshot=snapshot)
        if snapshot is not None:
            evidence = descriptor['native_evidence']
            raw = transport.bounded(snapshot, 'snapshot.json').read_bytes()
            manifest = json.loads(raw)
            if (evidence['state'] != 'retained_native_snapshot'
                    or transport.digest(raw) != evidence['snapshot_sha256']
                    or manifest['origin'] != evidence['origin']
                    or manifest['input_refs'] != evidence['input_refs']
                    or manifest['projection_ref']['sha256'] != evidence['projection_sha256']):
                raise ValueError('Private snapshot differs from the public descriptor')
            transport.replay_snapshot(snapshot, trusted_root=aml_root)
    return {'repository': descriptor['repository'], 'code_revision': descriptor['code_revision'],
            'verified_code_files': len(rows), 'verified_schema_files': len(pins),
            'native_evidence_state': descriptor['native_evidence']['state'],
            'native_evidence_replayed': snapshot is not None, 'acceptance_credential': False,
            'new_lean_compilations': 0}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--aml-root', type=Path, help='Checkout of the pinned private AML engine')
    parser.add_argument('--native-snapshot', type=Path, help='Authorized local native snapshot directory')
    args = parser.parse_args()
    if args.native_snapshot is not None and args.aml_root is None:
        parser.error('--native-snapshot requires --aml-root')
    try:
        result = verify(Path(__file__).resolve().parents[1],
                        args.aml_root.resolve() if args.aml_root else None,
                        args.native_snapshot.resolve() if args.native_snapshot else None)
    except (ValueError, OSError, KeyError, subprocess.CalledProcessError,
            jsonschema.exceptions.SchemaError, jsonschema.exceptions.ValidationError) as error:
        print('Audit verification refused: ' + str(error), file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
