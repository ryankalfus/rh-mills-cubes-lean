/-
# Certificates for a prime between consecutive cubes: soundness of the checker

The checker of `GRHCorollaries/Cubes/Defs.lean` is sound:

* `pm256_eq`: `pm256 m a n e` is `a ^ e % m` for `e < 256 ^ n`;
* `prime_of_pocklington`: Pocklington's criterion for a factor `2 ^ i * 3 ^ j` of `p - 1` with
  `p < (2 ^ i * 3 ^ j + 1) ^ 2`;
* `exists_prime_of_certOK`: an accepted certificate for `N` gives a prime in `(N ^ 3, (N + 1) ^ 3)`;
* `exists_prime_of_blockOK`: an accepted block of `cnt` certificates starting at `N₀` gives such a
  prime for every `N` with `N₀ ≤ N < N₀ + cnt`.
-/
import GRHCorollaries.Cubes.Defs
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement

namespace GRHCorollaries.Cubes

/-- `pm256` computes modular powers. -/
theorem pm256_eq (m a : ℕ) : ∀ (n e : ℕ), e < 256 ^ n → pm256 m a n e = a ^ e % m
  | 0, e, he => by
      obtain rfl : e = 0 := by simpa using he
      simp [pm256]
  | n + 1, e, he => by
      have hlt : e / 256 < 256 ^ n := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num)]
        rwa [pow_succ] at he
      have key : a ^ e = (a ^ (e / 256)) ^ 256 * a ^ (e % 256) := by
        rw [← pow_mul', ← pow_add, Nat.div_add_mod]
      rw [pm256, pm256_eq m a n _ hlt, key, Nat.mul_mod ((a ^ (e / 256)) ^ 256),
        Nat.pow_mod (a ^ (e / 256))]

/-- If `x ^ M = 1` in `ZMod r` (`r` prime) but `x ^ (M / q) ≠ 1` for a prime `q`, then the full
power of `q` dividing `M` divides `r - 1`: the element `x ^ (M / q ^ k)` has order `q ^ k`. -/
private theorem pow_dvd_sub_one_of_pow_eq_one {r : ℕ} [Fact r.Prime] {x : ZMod r} {q k M : ℕ}
    (hq : q.Prime) (hk : 0 < k) (hdvd : q ^ k ∣ M) (h1 : x ^ M = 1) (h2 : x ^ (M / q) ≠ 1) :
    q ^ k ∣ r - 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk.ne'
  obtain ⟨t, rfl⟩ := hdvd
  have := Fact.mk hq
  have hdiv : q ^ (k + 1) * t / q = q ^ k * t := by
    rw [pow_succ, mul_right_comm, Nat.mul_div_cancel _ hq.pos]
  have hfin : (x ^ t) ^ q ^ (k + 1) = 1 := by rw [← pow_mul, mul_comm]; exact h1
  have hnot : ¬(x ^ t) ^ q ^ k = 1 := by rw [← pow_mul, mul_comm, ← hdiv]; exact h2
  have hne : x ^ t ≠ 0 := by
    intro h0
    rw [h0, zero_pow (pow_ne_zero _ hq.ne_zero)] at hfin
    exact zero_ne_one hfin
  rw [← orderOf_eq_prime_pow hnot hfin]
  exact ZMod.orderOf_dvd_card_sub_one hne

/-- The gcd condition of the certificate, read modulo a prime factor `r` of `p`. -/
private theorem natCast_pow_ne_one {p r a k : ℕ} (hp : 1 < p) (hr : r.Prime) (hrp : r ∣ p)
    (h : Nat.gcd (a ^ k % p + (p - 1)) p = 1) : (a : ZMod r) ^ k ≠ 1 := by
  intro hx
  have hx' : a ^ k ≡ 1 [MOD r] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).1 (by push_cast; exact hx)
  have hmod : a ^ k % p + (p - 1) ≡ 1 + (p - 1) [MOD r] :=
    (((Nat.mod_modEq _ _).of_dvd hrp).trans hx').add_right _
  rw [show 1 + (p - 1) = p by omega] at hmod
  have hd : r ∣ a ^ k % p + (p - 1) :=
    Nat.modEq_zero_iff_dvd.1 (hmod.trans (Nat.modEq_zero_iff_dvd.2 hrp))
  have hr1 : r ∣ 1 := h ▸ Nat.dvd_gcd hd hrp
  exact hr.one_lt.ne' (Nat.dvd_one.1 hr1)

/-- Pocklington's criterion for a 3-smooth factor `2^i * 3^j` of `p - 1` exceeding `√p - 1`. -/
theorem prime_of_pocklington {p a i j : ℕ} (hp : 1 < p) (hi : 0 < i) (hj : 0 < j)
    (hF : 2 ^ i * 3 ^ j ∣ p - 1) (hsize : p < (2 ^ i * 3 ^ j + 1) ^ 2)
    (h1 : a ^ (p - 1) % p = 1)
    (h2 : Nat.gcd (a ^ ((p - 1) / 2) % p + (p - 1)) p = 1)
    (h3 : Nat.gcd (a ^ ((p - 1) / 3) % p + (p - 1)) p = 1) : p.Prime := by
  by_contra hnp
  obtain ⟨r, hr, hrp, hsq⟩ : ∃ r : ℕ, r.Prime ∧ r ∣ p ∧ r ^ 2 ≤ p :=
    ⟨p.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd p,
      Nat.minFac_sq_le_self (by omega) hnp⟩
  have := Fact.mk hr
  have hone : (a : ZMod r) ^ (p - 1) = 1 := by
    have hmod : a ^ (p - 1) ≡ 1 [MOD r] :=
      Nat.ModEq.of_dvd hrp (by unfold Nat.ModEq; rw [h1, Nat.mod_eq_of_lt hp])
    have hcast := (ZMod.natCast_eq_natCast_iff _ _ r).2 hmod
    push_cast at hcast
    exact hcast
  have h2r : 2 ^ i ∣ r - 1 :=
    pow_dvd_sub_one_of_pow_eq_one Nat.prime_two hi (dvd_of_mul_right_dvd hF) hone
      (natCast_pow_ne_one hp hr hrp h2)
  have h3r : 3 ^ j ∣ r - 1 :=
    pow_dvd_sub_one_of_pow_eq_one Nat.prime_three hj (dvd_of_mul_left_dvd hF) hone
      (natCast_pow_ne_one hp hr hrp h3)
  have hcop : Nat.Coprime (2 ^ i) (3 ^ j) := Nat.Coprime.pow i j (by decide)
  have hFr : 2 ^ i * 3 ^ j ∣ r - 1 := hcop.mul_dvd_of_dvd_of_dvd h2r h3r
  have hr1 : 0 < r - 1 := Nat.sub_pos_of_lt hr.one_lt
  have hle : 2 ^ i * 3 ^ j + 1 ≤ r := by
    have := Nat.le_of_dvd hr1 hFr
    omega
  exact absurd (hsize.trans_le ((Nat.pow_le_pow_left hle 2).trans hsq)) (lt_irrefl _)

/-- The arithmetic content of `certOK`, with the unpacked fields as variables. -/
private theorem prime_of_cert {p a i j y : ℕ} (hp : 1 < p) (hp61 : p < 2305843009213693952)
    (hF : (p - 1) % (2 ^ i * 3 ^ j) = 0) (hsize : p < (2 ^ i * 3 ^ j + 1) ^ 2)
    (hi : 0 < i) (hj : 0 < j) (hy : y = pm256 p a 8 ((p - 1) / 6))
    (h1 : y * y % p * y % p * (y * y % p * y % p) % p = 1)
    (h2 : Nat.gcd (y * y % p * y % p + (p - 1)) p = 1)
    (h3 : Nat.gcd (y * y % p + (p - 1)) p = 1) : p.Prime := by
  have hFd : 2 ^ i * 3 ^ j ∣ p - 1 := Nat.dvd_of_mod_eq_zero hF
  obtain ⟨E, hE⟩ : 2 * 3 ∣ p - 1 :=
    (mul_dvd_mul (dvd_pow_self 2 hi.ne') (dvd_pow_self 3 hj.ne')).trans hFd
  have hE8 : E < 256 ^ 8 := by
    rw [show (256 : ℕ) ^ 8 = 18446744073709551616 by norm_num]
    omega
  have hy' : y = a ^ E % p := by
    rw [hy, show (p - 1) / 6 = E by omega, pm256_eq p a 8 E hE8]
  have hy2 : y * y % p = a ^ (2 * E) % p := by
    rw [hy', ← Nat.mul_mod, ← pow_add, ← two_mul]
  have hy3 : y * y % p * y % p = a ^ (3 * E) % p := by
    rw [hy2, hy', ← Nat.mul_mod, ← pow_add, show 2 * E + E = 3 * E by omega]
  rw [hy3, ← Nat.mul_mod, ← pow_add, show 3 * E + 3 * E = p - 1 by omega] at h1
  rw [hy3, show 3 * E = (p - 1) / 2 by omega] at h2
  rw [hy2, show 2 * E = (p - 1) / 3 by omega] at h3
  exact prime_of_pocklington hp hi hj hFd hsize h1 h2 h3

/-- A certificate accepted by the checker yields a prime strictly between the cubes. -/
theorem exists_prime_of_certOK {N c : ℕ} (hN : 1 ≤ N) (h : certOK N c = true) :
    ∃ p : ℕ, p.Prime ∧ N ^ 3 < p ∧ p < (N + 1) ^ 3 := by
  simp only [certOK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hlo, hhi⟩, hF⟩, hsize⟩, hi⟩, hj⟩, h1⟩, h2⟩, h3⟩ := h
  have hp : 1 < c % 2305843009213693952 := lt_of_le_of_lt (Nat.one_le_pow 3 N hN) hlo
  have hp61 : c % 2305843009213693952 < 2305843009213693952 := Nat.mod_lt _ (by norm_num)
  exact ⟨_, prime_of_cert hp hp61 hF hsize hi hj rfl h1 h2 h3, hlo, hhi⟩

/-- A block accepted by the checker covers `cnt` consecutive values of `N`. -/
theorem exists_prime_of_blockOK {data : ℕ} : ∀ {cnt N₀ : ℕ}, 1 ≤ N₀ → blockOK data cnt N₀ = true →
    ∀ N, N₀ ≤ N → N < N₀ + cnt → ∃ p : ℕ, p.Prime ∧ N ^ 3 < p ∧ p < (N + 1) ^ 3 := by
  intro cnt
  induction cnt generalizing data with
  | zero =>
    intro N₀ _ _ N hle hlt
    omega
  | succ cnt ih =>
    intro N₀ hN₀ h N hle hlt
    rw [blockOK, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le hle with rfl | hlt'
    · exact exists_prime_of_certOK hN₀ h.1
    · exact ih (Nat.le_succ_of_le hN₀) h.2 N (Nat.succ_le_of_lt hlt') (by omega)

end GRHCorollaries.Cubes
