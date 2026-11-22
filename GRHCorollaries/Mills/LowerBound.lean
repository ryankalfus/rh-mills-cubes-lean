module

public import GRHCorollaries.Mills.Defs
public import Mathlib.NumberTheory.LucasPrimality
public import Mathlib.Tactic

/-!
# Mills numbers: the unconditional lower bound

Every Mills number `A` (that is, `IsMills A` with `1 < A`) satisfies `1.3063778838 < A`.

Put `q n = ⌊A ^ 3 ^ n⌋₊`. Flooring a cube gives `q n ^ 3 ≤ q (n + 1) < (q n + 1) ^ 3`, and every
`q n` is prime, so `q 1 ≥ 2`, `q 2 ≥ 11`, `q 3 ≥ 1361` and `q 4 ≥ 2521008887`: each time the next
prime at or above the cube of the previous bound. Hence
`A ^ 81 ≥ 2521008887 > 1.3063778838 ^ 81`.
-/

@[expose] public section

namespace Mills

/-- Flooring a cube: lower half. -/
theorem floor_pow_three_ge {x : ℝ} (hx : 0 ≤ x) : ⌊x⌋₊ ^ 3 ≤ ⌊x ^ 3⌋₊ := by
  apply Nat.le_floor
  push_cast
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hx) 3

/-- Flooring a cube: upper half. -/
theorem floor_pow_three_lt {x : ℝ} (hx : 0 ≤ x) : ⌊x ^ 3⌋₊ < (⌊x⌋₊ + 1) ^ 3 := by
  rw [Nat.floor_lt (pow_nonneg hx 3)]
  push_cast
  exact pow_lt_pow_left₀ (Nat.lt_floor_add_one x) hx (by norm_num)

theorem prime_ge_eleven_of_ge_eight {p : ℕ} (hp : p.Prime) (h : 8 ≤ p) : 11 ≤ p := by
  by_contra hlt
  rw [not_le] at hlt
  interval_cases p <;> norm_num at hp

theorem prime_ge_1361_of_ge_1331 {p : ℕ} (hp : p.Prime) (h : 1331 ≤ p) : 1361 ≤ p := by
  by_contra hlt
  rw [not_le] at hlt
  interval_cases p <;> norm_num at hp

theorem prime_ge_2521008887_of_ge {p : ℕ} (hp : p.Prime) (h : 2521008881 ≤ p) :
    2521008887 ≤ p := by
  by_contra hlt
  rw [not_le] at hlt
  interval_cases p <;> norm_num at hp

/-- `IsMills` restated with `Nat.Prime` and an evaluated exponent. -/
private theorem prime_floor {A : ℝ} (h : IsMills A) (n : ℕ+) (m : ℕ) (hm : 3 ^ (n : ℕ) = m) :
    Nat.Prime ⌊A ^ m⌋₊ :=
  hm ▸ Nat.prime_iff.mpr (h n)

/-- The fourth floor of a Mills number is at least the fourth Mills prime. -/
theorem le_floor_pow_81 {A : ℝ} (hA : 1 < A) (h : IsMills A) : 2521008887 ≤ ⌊A ^ 81⌋₊ := by
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have p1 : Nat.Prime ⌊A ^ 3⌋₊ := prime_floor h 1 3 (by norm_num)
  have p2 : Nat.Prime ⌊A ^ 9⌋₊ := prime_floor h 2 9 (by norm_num)
  have p3 : Nat.Prime ⌊A ^ 27⌋₊ := prime_floor h 3 27 (by norm_num)
  have p4 : Nat.Prime ⌊A ^ 81⌋₊ := prime_floor h 4 81 (by norm_num)
  have s2 : ⌊A ^ 3⌋₊ ^ 3 ≤ ⌊A ^ 9⌋₊ := by
    rw [show A ^ 9 = (A ^ 3) ^ 3 by ring]
    exact floor_pow_three_ge (pow_nonneg hA0 3)
  have s3 : ⌊A ^ 9⌋₊ ^ 3 ≤ ⌊A ^ 27⌋₊ := by
    rw [show A ^ 27 = (A ^ 9) ^ 3 by ring]
    exact floor_pow_three_ge (pow_nonneg hA0 9)
  have s4 : ⌊A ^ 27⌋₊ ^ 3 ≤ ⌊A ^ 81⌋₊ := by
    rw [show A ^ 81 = (A ^ 27) ^ 3 by ring]
    exact floor_pow_three_ge (pow_nonneg hA0 27)
  have b2 : 11 ≤ ⌊A ^ 9⌋₊ := prime_ge_eleven_of_ge_eight p2 <|
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ ⌊A ^ 3⌋₊ ^ 3 := Nat.pow_le_pow_left p1.two_le 3
      _ ≤ ⌊A ^ 9⌋₊ := s2
  have b3 : 1361 ≤ ⌊A ^ 27⌋₊ := prime_ge_1361_of_ge_1331 p3 <|
    calc 1331 = 11 ^ 3 := by norm_num
      _ ≤ ⌊A ^ 9⌋₊ ^ 3 := Nat.pow_le_pow_left b2 3
      _ ≤ ⌊A ^ 27⌋₊ := s3
  exact prime_ge_2521008887_of_ge p4 <|
    calc 2521008881 = 1361 ^ 3 := by norm_num
      _ ≤ ⌊A ^ 27⌋₊ ^ 3 := Nat.pow_le_pow_left b3 3
      _ ≤ ⌊A ^ 81⌋₊ := s4

theorem pow_81_lower : (1.3063778838 : ℝ) ^ 81 < 2521008887 := by
  norm_num

theorem pow_81_upper : (2521008888 : ℝ) < (1.3063778839 : ℝ) ^ 81 := by
  norm_num

/-- Every Mills number `A > 1` exceeds 1.3063778838. No analytic hypothesis: only `1 < A` and `IsMills A`. -/
theorem lower_bound {A : ℝ} (hA : 1 < A) (h : IsMills A) : (1.3063778838 : ℝ) < A := by
  by_contra hcon
  rw [not_lt] at hcon
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have h1 : A ^ 81 ≤ (1.3063778838 : ℝ) ^ 81 := pow_le_pow_left₀ hA0 hcon 81
  have h2 : (2521008887 : ℝ) ≤ A ^ 81 := by
    have := (Nat.le_floor_iff (pow_nonneg hA0 81)).mp (le_floor_pow_81 hA h)
    exact_mod_cast this
  exact absurd (h2.trans h1) (not_le.mpr pow_81_lower)

theorem prime_1361 : Nat.Prime 1361 := by
  norm_num

/-- A residue that is not `1` modulo `2521008887` is not `1` in `ZMod 2521008887`. -/
private theorem zmod_ne_one {r : ℕ} (hr : r % 2521008887 ≠ 1) :
    ((r : ℕ) : ZMod 2521008887) ≠ 1 := fun h =>
  hr ((ZMod.natCast_eq_natCast_iff' r 1 2521008887).mp (by exact_mod_cast h))

/-- Lucas primality test with primitive root `5`, using `2521008886 = 2 * 11 * 23 * 4982231`.
Trial division (`norm_num`) overflows the kernel's recursion depth for a number this large. -/
theorem prime_2521008887 : Nat.Prime 2521008887 := by
  refine lucas_primality 2521008887 5 ?_ fun q hq hqd => ?_
  · show (5 : ZMod 2521008887) ^ 2521008886 = 1
    reduce_mod_char
  · have hq' : q = 2 ∨ q = 11 ∨ q = 23 ∨ q = 4982231 := by
      rw [show 2521008887 - 1 = 2 * (11 * (23 * 4982231)) by norm_num] at hqd
      rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h)
      rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h))
      rcases (Nat.Prime.dvd_mul hq).mp h with h | h
      · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h)))
      · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h)))
    rcases hq' with rfl | rfl | rfl | rfl
    · show (5 : ZMod 2521008887) ^ 1260504443 ≠ 1
      reduce_mod_char
      exact_mod_cast zmod_ne_one (r := 2521008886) (by norm_num)
    · show (5 : ZMod 2521008887) ^ 229182626 ≠ 1
      reduce_mod_char
      exact_mod_cast zmod_ne_one (r := 2271204653) (by norm_num)
    · show (5 : ZMod 2521008887) ^ 109609082 ≠ 1
      reduce_mod_char
      exact_mod_cast zmod_ne_one (r := 986702572) (by norm_num)
    · show (5 : ZMod 2521008887) ^ 506 ≠ 1
      reduce_mod_char
      exact_mod_cast zmod_ne_one (r := 132792391) (by norm_num)

end Mills
