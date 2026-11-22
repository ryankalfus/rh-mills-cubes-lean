# Vendored code: google-deepmind/cryptids

The six files under `Cryptids/Semantics/Riemann/` are **unmodified** copies from
https://github.com/google-deepmind/cryptids at commit
`3647718b5df22e1a61462dec0376bd204526285a` (2026-11-12), Apache License 2.0
(see `LICENSE-cryptids`). Copyright belongs to the authors named in each file header.

    Schmidt.lean  VonMangoldtCount.lean  WeightedStieltjes.lean
    DigammaBinet.lean  HorizontalBounds.lean  ExplicitLarge.lean

They prove, from Mathlib's `RiemannHypothesis`, the ingredients of the explicit bound
`|ψ(x) − x| ≤ (7/8) √x (log x)²` for `x ≥ 5000`. Upstream assembles that bound in
`Cryptids/Semantics/Riemann/Analytic.lean`, which also imports the register-machine part of
the project; we do not vendor that file and instead repeat its 25-line assembly in
`GRHCorollaries/PsiBound.lean` with attribution.

Upstream pins Lean v4.35.0-rc4 / Mathlib v4.35.0-rc4; this project builds them on
Lean v4.35.0 / Mathlib v4.35.0. Any change needed for that is listed here (none so far).

Audit before building (grep, 2026-11-22): no `#eval`, `IO`, `unsafe`, `@[extern]`,
`implemented_by`, `elab`/`macro`/`syntax`, `axiom`, `sorry`, `native_decide`,
`maxHeartbeats` or `maxRecDepth` overrides in these six files.
