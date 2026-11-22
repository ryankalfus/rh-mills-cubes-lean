# Verification record

Everything below was run on one machine (Apple M3 MacBook, 8 GB RAM, macOS) with Lean v4.35.0
(commit `eb6cafb7`) and Mathlib v4.35.0, on 2026-11-22. Raw logs are in `logs/verify/`; times
in file names are UTC. Nothing has yet been rebuilt by a second party or on a second machine.

## Results

| check | result | log |
|---|---|---|
| `lake build GRHCorollaries Challenge` | success | `build-full-*.log` |
| `#print axioms` on every headline theorem | `[propext, Classical.choice, Quot.sound]` only | `axioms-*.txt` |
| No `sorry`, `native_decide`, `axiom`, `implemented_by`, `extern`, `unsafe` in `GRHCorollaries/` or `vendor-cryptids/` | none (grep) | — |
| Six files in `vendor-cryptids/` vs `google-deepmind/cryptids` @ `3647718b` | byte-identical (`cmp`) | — |
| Statement text of `IsMills`, `IsMinMills`, `lower_bound_of_RH` vs `google-deepmind/formal-conjectures` @ `2207c54` | identical; the elaborated kernel terms in `Challenge` and in the library are identical too | — |
| `lake comparator`, Mills theorems (sources of 17:18 UTC) | accepted ("Your solution is okay!"): Lean kernel, nanoda | `comparator-2026-11-22T1721Z.log` |
| same, `--paranoid` | accepted: Lean, Lean paranoid, lean4lean, nanoda, con-leche, con-ron | `comparator-2026-11-22T1727Z.log` |
| `lake comparator`, all five headline theorems including the cubes theorem (sources of 18:01 UTC) | accepted ("Your solution is okay!", exit 0): nanoda and the Lean kernel, 3,265 s | `comparator-2026-11-22T1801Z.log` |
| All 1,200,000 certificates decoded from the Lean files and re-checked by separate Python code; ranges tile [1, 1200001) | 0 bad | `check-certs-*.txt` |
| Generators reproduce `GRHCorollaries/Cubes/Certs/` and `Cubes/Finite.lean` byte for byte | yes (checked by an independent reviewer) | — |
| Source hashes | recorded | `sha256-*.txt` |

Two independent AI reviewers were asked to attack the statements (fidelity to the sources,
vacuity, hygiene, the certificate checker and its coverage, the documentation). Neither found a
problem with any theorem; their wording corrections are applied.

## Caveats

- **The comparator runs were not sandboxed.** macOS has no bubblewrap, so `lake comparator` ran
  with `--inadvisably-no-sandbox`, and the tool itself prints "Sandbox disabled, this run is not
  trustworthy". The runs show that this build proves exactly the statements of `Challenge.lean`
  and that the listed kernels accept the export; they are not the sandboxed judgment a third
  party should run. To do that on Linux: `lake comparator` (with bubblewrap installed).
- **Mathlib version.** The proof is compiled against Mathlib v4.35.0. formal-conjectures pins
  Mathlib v4.33.1, and the Lean proof of RH announced on 2026-11-20 is also on v4.33.1. The
  statements have not been compiled inside formal-conjectures, and RH has not been discharged.
- After the 18:01 UTC run only comments in `Challenge.lean` and `GRHCorollaries/Cubes/Main.lean`,
  and the removal of an unused library from
  `lakefile.toml`, changed; the final build and axiom audit were rerun on the published tree
  (`build-full-*.log` and `axioms-*.txt` with the latest time stamp).
