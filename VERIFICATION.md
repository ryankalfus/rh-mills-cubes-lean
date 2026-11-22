# Verification record

Unless marked otherwise, everything below was run on one machine (Apple M3 MacBook, 8 GB RAM,
macOS) with Lean v4.35.0 (commit `eb6cafb7`) and Mathlib v4.35.0, on 2026-11-22. Raw logs are in
`logs/verify/`; times in file names are UTC. The GitHub Actions row is a second machine; no
third party has rebuilt it yet.

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
| **GitHub Actions, ubuntu-24.04, fresh clone** (run 45059569955, commit `2a3f476`): build, axiom audit (7 theorems), certificate re-check, and **`lake comparator` inside its bubblewrap sandbox** | all passed; comparator: nanoda and the Lean kernel accept, "Your solution is okay!" (20:01 UTC) | https://github.com/ryankalfus/rh-mills-cubes-lean/actions/runs/45059569955 |

Two independent AI reviewers were asked to attack the statements (fidelity to the sources,
vacuity, hygiene, the certificate checker and its coverage, the documentation). Neither found a
problem with any theorem; their wording corrections are applied.

## Module-system port (2026-11-22 20:04 UTC)

For registration in the Palomar registry every Lean file was converted to the module system
(`module`, `public import`, `@[expose] public section`; no statement or proof changed), the
certificate modules were regenerated in that form, and `comparator.json` was reduced to the keys
Palomar accepts. The full build and axiom audit were rerun (`build-full-2026-11-22T2004Z.log`,
`axioms-2026-11-22T2004Z.txt`, `sha256-2026-11-22T2004Z.txt`); the comparator results above are for
the sources before the port, and the GitHub Actions run on the ported commit repeats them.

## Caveats

- **The local comparator runs were not sandboxed.** macOS has no bubblewrap, so `lake comparator` ran
  with `--inadvisably-no-sandbox`, and the tool itself prints "Sandbox disabled, this run is not
  trustworthy". The runs show that this build proves exactly the statements of `Challenge.lean`
  and that the listed kernels accept the export; they are not the sandboxed judgment a third
  party should run. The sandboxed run is the GitHub Actions one above (`.github/workflows/verify.yml`),
  with the Lean kernel and nanoda; the other external kernels ran only in the unsandboxed local
  `--paranoid` run, and only on the Mills theorems.
- **Mathlib version.** The proof is compiled against Mathlib v4.35.0. formal-conjectures pins
  Mathlib v4.33.1, and the Lean proof of RH announced on 2026-11-20 is also on v4.33.1. The
  statements have not been compiled inside formal-conjectures, and RH has not been discharged.
- After the 18:01 UTC run only comments in `Challenge.lean` and `GRHCorollaries/Cubes/Main.lean`,
  and the removal of an unused library from
  `lakefile.toml`, changed; the final build and axiom audit were rerun on the published tree
  (`build-full-*.log` and `axioms-*.txt` with the latest time stamp).
