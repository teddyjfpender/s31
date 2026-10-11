#!/usr/bin/env python3
"""Concrete N=1/N=8 compiler-to-typed-mixed-boundary audit fixture.

This is a source and native-inspector correspondence check, not a proof of
LogUp, PCS, or source compiler soundness. ``--static`` needs no native build.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import tempfile
from pathlib import Path

from source_pinned_general import MODULUS, build, family, run

GATE = 378_353_459
CHIP = 1_395_863_811


def canonical_source(source: dict) -> bytes:
    return json.dumps(source, separators=(",", ":")).encode()


def gate_tuple(address: int, word: int) -> list[int]:
    # Lean: paddedGateTuple address (base word).
    return [GATE, address, word, 0, 0, 0, 0]


def chip_tuple(call_id: int, step: int, words: list[int]) -> list[int]:
    return [CHIP, call_id, step, *words]


def step_many(words: list[int], constant: int, rounds: int) -> list[int]:
    result = words.copy()
    for _ in range(rounds):
        result = [(word * word + constant) % MODULUS for word in result]
    return result


def reviewed_address_schedule(count: int) -> list[list[int]]:
    """Hand-derived allocation for this exact source family and compiler.

    Context initializes 0,1,2 and reserves public outputs 3..10. Four
    scalar M31 input guesses take 11..14. Packing interns i and iu at 15,16,
    then allocates six arithmetic temporaries at 17..22. Each repeat guesses
    four scalar result words and packs them with six new temporaries. Thus the
    first output is 23..26, and each later output advances ten addresses.
    This arithmetic is deliberately independent of inspector call records.
    """
    if count not in (1, 8):
        raise AssertionError("only the reviewed N=1/N=8 family is pinned")
    previous = [11, 12, 13, 14]
    calls = []
    for call_id in range(count):
        output = [23 + 10 * call_id + lane for lane in range(4)]
        calls.append([*previous, *output])
        previous = output
    return calls


def project(count: int, manifest: dict, public_words: list[int]) -> dict:
    """Construct source-shaped Boundary events for the fixed chain family.

    Absolute addresses come from ``reviewed_address_schedule``, independently
    of the native inspector. Chain/freshness alone cannot pin them.
    """
    source, assignment = family(count)
    source_hash = hashlib.sha256(canonical_source(source)).hexdigest()
    if (manifest["schema"] != "s31-mixed-component-inspection-general-v3" or
            manifest["profile"] != "experimental-direct-mixed-general" or
            manifest["source_sha256"] != source_hash or
            manifest["call_count"] != count):
        raise AssertionError("native inspector is not pinned to this source")
    if len(manifest["calls"]) != count or len(manifest["slots"]) != 1 + 2 * count:
        raise AssertionError("native mixed roster length differs")
    expected_addresses = reviewed_address_schedule(count)
    if public_words != [*assignment["public_outputs"]["sum"],
                        *assignment["public_outputs"]["product"]]:
        raise AssertionError("public output words differ from source evaluation")
    if any(type(word) is not int or not 0 <= word < MODULUS for word in public_words):
        raise AssertionError("public output word is not canonical M31")

    initial = assignment["private_inputs"]["x"]
    state = initial.copy()
    events = []
    previous = None
    for call_id, (call, frozen) in enumerate(zip(manifest["calls"], expected_addresses)):
        want = [*call["input"], *call["output"]]
        if (want != frozen or len(want) != 8 or
                any(type(address) is not int or not 2 < address < MODULUS
                    for address in want) or
                call["call_id"] != call_id or
                call["source_node_id"] != call_id + 1 or
                call["input_node_id"] != call_id or
                call["rounds"] != 16 or call["constant"] != 13 + call_id or
                (previous is not None and call["input"] != previous)):
            raise AssertionError("call differs from pinned compiler boundary")
        chip, bridge = manifest["slots"][1 + 2 * call_id:3 + 2 * call_id]
        native_family = "pair" if call_id < 2 else "many"
        if (chip["source_kind"] != f"{native_family}_chip" or
                bridge["source_kind"] != f"{native_family}_bridge" or
                chip["registry_role"] != "chip" or
                bridge["registry_role"] != "bridge" or
                chip["call_id"] != call_id or bridge["call_id"] != call_id or
                chip["relation_ids"] != [CHIP] or
                bridge["relation_ids"] != [GATE, CHIP]):
            raise AssertionError("chip/bridge relation roster differs")
        after = step_many(state, call["constant"], call["rounds"])
        words = [*state, *after]
        events.append({
            "call_id": call_id,
            "rounds": call["rounds"],
            "constant": call["constant"],
            # Lean Boundary.callBridgeGates, with the production seventh zero.
            "bridge_gate_events": [gate_tuple(address, word)
                                   for address, word in zip(want, words)],
            # Lean Boundary.start/finish and sourceBridgeStart/FinishTuple.
            "bridge_start": chip_tuple(call_id, 0, state),
            "bridge_finish": chip_tuple(call_id, call["rounds"], after),
        })
        previous = call["output"]
        state = after
    independently_evaluated = [
        *((word + input_word) % MODULUS for word, input_word in zip(state, initial)),
        *((word * input_word) % MODULUS for word, input_word in zip(state, initial)),
    ]
    if public_words != independently_evaluated:
        raise AssertionError("public feeder differs from the independently evaluated chain")
    if (manifest["slots"][0]["registry_role"] != "circuit" or
            manifest["slots"][0]["call_id"] is not None or
            manifest["slots"][0]["relation_ids"] != [GATE]):
        raise AssertionError("circuit Gate relation differs")
    return {
        "source_sha256": source_hash,
        "calls": events,
        # Lean Boundary.publicFeeder: addresses 3..10 and fixed u at 2.
        "public_feeder": [gate_tuple(3 + i, word)
                          for i, word in enumerate(public_words)] +
                         [[GATE, 2, 0, 0, 1, 0, 0]],
    }


def synthetic(count: int) -> tuple[dict, list[int]]:
    source, assignment = family(count)
    calls = []
    slots = [{"source_kind": "bundled_circuit", "registry_role": "circuit", "call_id": None,
              "relation_ids": [GATE]}]
    for call_id, frozen in enumerate(reviewed_address_schedule(count)):
        previous, outputs = frozen[:4], frozen[4:]
        calls.append({"call_id": call_id, "source_node_id": call_id + 1,
                      "input_node_id": call_id, "rounds": 16,
                      "constant": 13 + call_id, "input": previous,
                      "output": outputs})
        native_family = "pair" if call_id < 2 else "many"
        slots += [{"source_kind": f"{native_family}_chip",
                   "registry_role": "chip", "call_id": call_id,
                   "relation_ids": [CHIP]},
                  {"source_kind": f"{native_family}_bridge",
                   "registry_role": "bridge", "call_id": call_id,
                   "relation_ids": [GATE, CHIP]}]
    return ({"schema": "s31-mixed-component-inspection-general-v3",
             "profile": "experimental-direct-mixed-general",
             "source_sha256": hashlib.sha256(canonical_source(source)).hexdigest(),
             "call_count": count, "calls": calls, "slots": slots},
            [*assignment["public_outputs"]["sum"],
             *assignment["public_outputs"]["product"]])


def static_controls() -> dict:
    if reviewed_address_schedule(8)[7] != [83, 84, 85, 86, 93, 94, 95, 96]:
        raise AssertionError("eighth-call address schedule differs from Lean fixture")
    for count in (1, 8):
        manifest, public = synthetic(count)
        boundary = project(count, manifest, public)
        if (len(boundary["calls"]) != count or
                sum(len(call["bridge_gate_events"]) for call in boundary["calls"]) != 8 * count or
                len(boundary["public_feeder"]) != 9):
            raise AssertionError("typed boundary event count differs")
        if boundary["calls"][0]["bridge_gate_events"][0] != gate_tuple(11, 1):
            raise AssertionError("first bridge tuple differs")
        if boundary["calls"][0]["bridge_start"] != chip_tuple(0, 0, [1, 2, 3, 4]):
            raise AssertionError("first chip start differs")
        if boundary["public_feeder"][-1] != [GATE, 2, 0, 0, 1, 0, 0]:
            raise AssertionError("fixed u feeder differs")
        cases = []
        changed = copy.deepcopy(manifest)
        changed["calls"][0]["input"][0] = 10_000
        changed["calls"][0]["output"][0] = 20_000
        if count > 1:
            changed["calls"][1]["input"][0] = 20_000
        cases.append(("fresh coordinated retarget", changed, public))
        for key in ("rounds", "constant"):
            changed = copy.deepcopy(manifest)
            changed["calls"][0][key] += 1
            cases.append((key, changed, public))
        changed = copy.deepcopy(manifest)
        changed["slots"][2]["relation_ids"] = [CHIP, GATE]
        cases.append(("bridge relations", changed, public))
        changed_public = public.copy()
        changed_public[0] = (changed_public[0] + 1) % MODULUS
        cases.append(("public word", manifest, changed_public))
        for label, changed_manifest, changed_words in cases:
            try:
                project(count, changed_manifest, changed_words)
            except AssertionError:
                continue
            raise AssertionError(f"typed boundary control accepted {label}")
    return {"schema": "s31-typed-mixed-boundary-static-v1", "counts": [1, 8],
            "mutations_rejected_per_count": 5}


def native_inspector_audit() -> dict:
    with tempfile.TemporaryDirectory(prefix="s31-typed-mixed-") as temporary:
        work = Path(temporary)
        for count in (1, 8):
            source, assignment = family(count)
            source_file = work / f"n{count}.s31.json"
            source_file.write_bytes(canonical_source(source))
            prover, verifier, inspector = build(source_file, work / f"build-{count}")
            manifest = json.loads(run(str(inspector)).stdout)
            public = [*assignment["public_outputs"]["sum"],
                      *assignment["public_outputs"]["product"]]
            boundary = project(count, manifest, public)
            if boundary["source_sha256"] != hashlib.sha256(source_file.read_bytes()).hexdigest():
                raise AssertionError("typed boundary source identity differs")
            assignment_file = work / f"n{count}.assignment.json"
            assignment_file.write_text(json.dumps(assignment, separators=(",", ":")))
            proof = work / f"n{count}.proof"
            statement = work / f"n{count}.statement.json"
            run(str(prover), str(assignment_file), str(proof), str(statement))
            run(str(verifier), str(proof), str(statement))
            claimed = json.loads(statement.read_text())
            if claimed["public_words"] != public:
                raise AssertionError("native statement differs from public feeder")
    return {"schema": "s31-typed-mixed-boundary-native-inspector-v1",
            "counts": [1, 8], "exact_endpoint_schedule_checked": True,
            "modeled_bridge_gate_events": 72, "native_proofs_accepted": 2,
            "bridge_trace_values_read": False,
            "compiler_to_lean_event_lists_proven": False}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", action="store_true", help="build, prove and verify N=1/N=8")
    args = parser.parse_args()
    print(json.dumps(static_controls(), sort_keys=True))
    if args.native:
        print(json.dumps(native_inspector_audit(), sort_keys=True))


if __name__ == "__main__":
    main()
