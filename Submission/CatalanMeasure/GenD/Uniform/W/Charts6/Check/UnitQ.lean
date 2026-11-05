module
public import Mathlib.NumberTheory.Primorial
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Int.Basic
@[expose] public section
set_option Elab.async false

/-!
# Units modulo large primes: `D ∣ QB^40` and `59 < p` give `D ≠ 0` in `ZMod p`

`QB` is the product of the primes `≤ 59` (the primorial of `59`).
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts6.Check

/-- The product of the primes up to `59`. -/
def QB : ℤ := 1922760350154212639070

theorem QB_eq : QB = ((primorial 59 : ℕ) : ℤ) := by
  have : primorial 59 = 1922760350154212639070 := by decide +kernel
  rw [this]; rfl

theorem prime_dvd_primorial_le {p n : ℕ} (hp : p.Prime) (h : p ∣ primorial n) : p ≤ n := by
  unfold primorial at h
  rw [Prime.dvd_finset_prod_iff hp.prime] at h
  obtain ⟨q, hq, hpq⟩ := h
  simp only [Finset.mem_filter, Finset.mem_range] at hq
  have := (Nat.prime_dvd_prime_iff_eq hp hq.2).mp hpq
  omega

theorem unit_of_dvdQ {p : ℕ} [Fact p.Prime] (D : ℤ) (hD : D ∣ QB ^ 40) (hp : 59 < p) :
    ((D : ℤ) : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have h1 : (p : ℤ) ∣ QB ^ 40 := h.trans hD
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have h2 : (p : ℤ) ∣ QB := hpp.dvd_of_dvd_pow h1
  rw [QB_eq] at h2
  have h3 : p ∣ primorial 59 := by exact_mod_cast h2
  have := prime_dvd_primorial_le (Fact.out : p.Prime) h3
  omega

end CatalanMeasure.GenD.Uniform.W.Charts6.Check
