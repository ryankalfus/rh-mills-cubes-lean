module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Mills numbers: definitions

`IsMills` and `IsMinMills` are copied character for character from
`google-deepmind/formal-conjectures`, `FormalConjectures/Wikipedia/Mills.lean`
(commit 2207c54, Apache-2.0, Copyright 2026 The Formal Conjectures Authors).
-/

@[expose] public section

namespace Mills

/--
Given any real $A$, `IsMills A` encodes the statement that $\lfloor A^{3^n}\rfloor,n > 0$ is prime.
-/
abbrev IsMills (A : ℝ) : Prop := ∀ (n : ℕ+), Prime ⌊A ^ (3 ^ (n : ℕ))⌋₊

/--
For a real $A$, `IsMinMills A` is the smallest value satisfying `IsMills A`.
-/
abbrev IsMinMills (A : ℝ) : Prop := IsLeast {x | x > 1 ∧ IsMills x} A

end Mills
