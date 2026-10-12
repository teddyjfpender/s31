#!/usr/bin/env python3
"""Matched S31 mixed-context reuse timing; all output stays in --out."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import statistics
import subprocess
import time


def sha(data):
    return hashlib.sha256(data).hexdigest()


def tagged(stderr, tag):
    prefix = (tag + ' ').encode()
    lines = [line[len(prefix):] for line in stderr.splitlines() if line.startswith(prefix)]
    if len(lines) != 1:
        raise RuntimeError(f'expected exactly one {tag} line')
    return json.loads(lines[0])


def run(argv, env):
    start = time.monotonic_ns()
    proc = subprocess.run(argv, env=env, capture_output=True)
    return proc, time.monotonic_ns() - start


def med(rows, key):
    return statistics.median(row[key] for row in rows)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--baseline-prefix', type=Path, required=True)
    ap.add_argument('--optimized-prefix', type=Path, required=True)
    ap.add_argument('--source-dir', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--claims', type=int, default=40)
    ap.add_argument('--baseline-commit', required=True)
    ap.add_argument('--optimized-commit', required=True)
    args = ap.parse_args()
    if args.claims < 1 or args.claims > 80 or args.out.exists():
        raise ValueError('invalid claim count or output already exists')
    args.out.mkdir(parents=True)
    env = os.environ.copy()
    env.pop('STWO_ZIG_POW_WORKERS', None)
    env['S31_MIXED_NATIVE_PHASES'] = '1'
    binaries = {
        'baseline': {'prover': Path(str(args.baseline_prefix) + 'prover'), 'verifier': Path(str(args.baseline_prefix) + 'native-verifier')},
        'optimized': {'prover': Path(str(args.optimized_prefix) + 'prover'), 'verifier': Path(str(args.optimized_prefix) + 'native-verifier')},
    }
    binary_sha = {variant: {role: sha(path.read_bytes()) for role, path in roles.items()} for variant, roles in binaries.items()}
    records = []
    for index in range(args.claims + 1):
        prefix = f'a{index:02d}r0'
        assignment = args.source_dir / f'{prefix}.assignment.json'
        statement = args.source_dir / f'{prefix}.statement.json'
        changed = args.source_dir / f'{prefix}.changed.json'
        if not (assignment.exists() and statement.exists() and changed.exists()):
            raise FileNotFoundError(prefix)
        variants = ['baseline', 'optimized'] if index % 2 == 0 else ['optimized', 'baseline']
        pairs = {}
        for variant in variants:
            roles = binaries[variant]
            out = args.out / f'{prefix}.{variant}'
            proof = Path(str(out) + '.proof')
            emitted = Path(str(out) + '.emitted.json')
            proved, prove_wall = run([str(roles['prover']), str(assignment), str(proof), str(emitted), str(statement)], env)
            Path(str(out) + '.prove.stderr').write_bytes(proved.stderr)
            if proved.returncode or not proof.exists() or emitted.read_bytes() != statement.read_bytes():
                raise RuntimeError(f'{prefix} {variant} prover failed: {proved.stderr[-500:]}')
            verified, verify_wall = run([str(roles['verifier']), str(proof), str(statement)], env)
            Path(str(out) + '.verified.stderr').write_bytes(verified.stderr)
            if verified.returncode or b'verified' not in verified.stderr:
                raise RuntimeError(f'{prefix} {variant} verifier failed: {verified.stderr[-500:]}')
            rejected, _ = run([str(roles['verifier']), str(proof), str(changed)], env)
            Path(str(out) + '.changed.stderr').write_bytes(rejected.stderr)
            if rejected.returncode == 0 or b'InvalidMixedInteractionNonce' not in rejected.stderr:
                raise RuntimeError(f'{prefix} {variant} changed claim was not proof-rejected: {rejected.stderr[-500:]}')
            stage = tagged(proved.stderr, 'S31_MIXED_STAGE_V1')
            phase = tagged(proved.stderr, 'S31_MIXED_NATIVE_PHASE_V1')
            pairs[variant] = {
                'proof_sha256': sha(proof.read_bytes()),
                'proof_bytes': proof.stat().st_size,
                'statement_sha256': sha(emitted.read_bytes()),
                'source_sha256': stage['source_sha256'],
                'circuit_identity_sha256': stage['circuit_identity_sha256'],
                'registry_manifest_sha256': stage['registry_manifest_sha256'],
                'prover_process_wall_ns': prove_wall,
                'verified_process_wall_ns': prove_wall + verify_wall,
                'stages_ns': stage['stages_ns'],
                'native_phase_ns': phase,
            }
        for key in ('proof_sha256','proof_bytes','statement_sha256','source_sha256','circuit_identity_sha256','registry_manifest_sha256'):
            if pairs['baseline'][key] != pairs['optimized'][key]:
                raise RuntimeError(f'{prefix} changed {key}')
        if Path(str(args.out / f'{prefix}.baseline') + '.proof').read_bytes() != Path(str(args.out / f'{prefix}.optimized') + '.proof').read_bytes():
            raise RuntimeError(f'{prefix} changed proof bytes')
        records.append({'claim_index': index, **pairs})
    scored = records[1:]
    measures = ('prover_process_wall_ns','verified_process_wall_ns')
    stages = ('profile_rebuild_ns','package_total_ns','native_prove_including_setup_ns')
    summary = {'claims': args.claims, 'exact_proof_pairs': len(records), 'honest_verified': 2*len(records), 'changed_claim_rejected': 2*len(records)}
    for key in measures:
        left = [r['baseline'][key] for r in scored]
        right = [r['optimized'][key] for r in scored]
        summary[key] = {'baseline_median_ns': statistics.median(left), 'optimized_median_ns': statistics.median(right), 'paired_delta_median_ns': statistics.median(a-b for a,b in zip(left,right)), 'paired_delta_mad_ns': statistics.median(abs((a-b)-statistics.median(x-y for x,y in zip(left,right))) for a,b in zip(left,right))}
    for key in stages:
        left = [r['baseline']['stages_ns'][key] for r in scored]
        right = [r['optimized']['stages_ns'][key] for r in scored]
        summary[key] = {'baseline_median_ns': statistics.median(left), 'optimized_median_ns': statistics.median(right), 'paired_delta_median_ns': statistics.median(a-b for a,b in zip(left,right)), 'paired_delta_mad_ns': statistics.median(abs((a-b)-statistics.median(x-y for x,y in zip(left,right))) for a,b in zip(left,right))}
    report = {'schema':'s31-mixed-context-reuse-matched-v1','baseline_commit':args.baseline_commit,'optimized_commit':args.optimized_commit,'source_dir':str(args.source_dir.resolve()),'binary_sha256':binary_sha,'summary':summary,'records':records}
    raw = json.dumps(report, sort_keys=True, separators=(',',':')).encode()+b'\n'
    (args.out / 'result.json').write_bytes(raw)
    print(json.dumps(summary, sort_keys=True, indent=2))
    print('result_sha256', sha(raw))

if __name__ == '__main__':
    main()
