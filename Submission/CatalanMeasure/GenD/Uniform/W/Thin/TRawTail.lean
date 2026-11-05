module
public import Submission.CatalanMeasure.GenD.Uniform.W.Thin.TRaw
public import Submission.CatalanMeasure.GenD.Uniform.W.Combine
@[expose] public section
set_option Elab.async false

/-!
# The T-raw tail (window `s = 4`, blocks `0..3`, digits `1..3`)

A design-generic instance of `tRaw_le_nullity` with `K = 4`, `k0 = 0`, `S = {(1,4),(2,4),(3,4)}`,
`D = n - 1 - g - 3p` (so no virtual pair), `e0 = H - 4p - b`.  The count is
`(D - e0) * (4 - 3) = p - 1 - (2g + q + h)`.  The window hypotheses are linear in `(n,b,q,g,h,p)`:

    4p ≤ L,  b ≤ p,  D ≤ g,  D ≤ (p-1)/2,  3p + 1 + g ≤ n,  4p + b ≤ H.

Nothing here mentions a particular design.
-/

namespace CatalanMeasure.GenD.Uniform.W.Thin
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Window of the T-raw tail. -/
def TTailApp (P : Parameters) (N p : ℕ) : Prop :=
  4 * p ≤ P.L N ∧ P.b N ≤ p ∧ P.n N - 1 - P.g N - 3 * p ≤ P.g N ∧
    P.n N - 1 - P.g N - 3 * p ≤ (p - 1) / 2 ∧ 3 * p + 1 + P.g N ≤ P.n N ∧
      4 * p + P.b N ≤ P.H N

/-- Value of the T-raw tail. -/
def tTailVal (P : Parameters) (N p : ℕ) : ℕ := p - 1 - (2 * P.g N + P.q N + P.h N)

theorem tTail_virt_zero (hA : TTailApp P N p) :
    virtCount P N p 4 (P.n N - 1 - P.g N - 3 * p) 0 = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hA
  unfold virtCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro dk _
  obtain ⟨d, k⟩ := dk
  have hd := d.isLt
  have hk := k.isLt
  have hp1 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hk0 : (0 : ℤ) ≤ ((k : ℕ) : ℤ) * p := by positivity
  have hk3 : ((k : ℕ) : ℤ) * p ≤ 3 * p := by
    have : ((k : ℕ) : ℤ) ≤ 3 := by exact_mod_cast (by omega : (k : ℕ) ≤ 3)
    nlinarith
  simp only [not_not, Good, InRange, cen, zero_add]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> push_cast <;> omega

theorem tTail_seen (hA : TTailApp P N p) :
    ∀ j e (a : ℤ), P.b N ≤ j → j < P.L N → (P.H N - 4 * p - P.b N) ≤ e →
      e < P.h N + (P.n N - 1 - P.g N - 3 * p) →
      (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e = a * p →
      (j / p, a) ∈ ({(1, 4), (2, 4), (3, 4)} : Finset (ℕ × ℤ)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hA
  intro j e a hb hL he0 heD heq
  have hp1 : 0 < p := (Fact.out : p.Prime).pos
  have hp1' : (0 : ℤ) < p := by exact_mod_cast hp1
  have hjd := Nat.div_add_mod j p
  have hell : j % p < p := Nat.mod_lt _ hp1
  have hHdef : P.H N = P.L N + P.g N + P.h N := by simp [Parameters.H, Parameters.C]
  have ha5 : a < 5 := by
    by_contra hc
    have : (5 : ℤ) * p ≤ a * p := by nlinarith
    omega
  have ha3 : 3 < a := by
    by_contra hc
    have : a * p ≤ 3 * p := by nlinarith
    omega
  have ha : a = 4 := by omega
  subst ha
  have hJ1 : 1 ≤ j / p := by
    by_contra hc
    have h0 : j / p = 0 := Nat.lt_one_iff.mp (not_le.mp hc)
    rw [h0] at hjd
    omega
  have hJ4 : j / p < 4 := by
    by_contra hc
    have : 4 * p ≤ p * (j / p) := by nlinarith
    omega
  have : j / p = 1 ∨ j / p = 2 ∨ j / p = 3 := by omega
  rcases this with h | h | h <;> simp [h]

/-- **Theorem T-raw (tail).** -/
theorem tTail_le_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (hA : TTailApp P N p) : tTailVal P N p ≤ nullity P N p := by
  have h := tRaw_le_nullity (P := P) (N := N) (p := p) hP hN hp2 hH (K := 4)
    (D := P.n N - 1 - P.g N - 3 * p) (e0 := P.H N - 4 * p - P.b N) 0 hA.2.2.2.1
    ({(1, 4), (2, 4), (3, 4)} : Finset (ℕ × ℤ))
    (fun j e a h1 h2 h3 h4 h5 => tTail_seen hA j e a h1 h2 h3 h4 h5)
  rw [tTail_virt_zero hA] at h
  have hc : ({(1, 4), (2, 4), (3, 4)} : Finset (ℕ × ℤ)).card = 3 := by decide
  rw [hc] at h
  have h' : (P.n N - 1 - P.g N - 3 * p) - (P.H N - 4 * p - P.b N) ≤ nullity P N p := by
    simpa using h
  have hHdef : P.H N = P.L N + P.g N + P.h N := by simp [Parameters.H, Parameters.C]
  have hL : P.L N = P.n N + P.b N + P.q N := rfl
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hA
  unfold tTailVal
  omega

/-- The nullity lower bound of the T-raw tail, for any admissible design. -/
def tTailLB (P : Parameters) (hP : Admissible P) : NullityLB P :=
  NullityLB.ofWindow P (TTailApp P) (tTailVal P)
    (fun N p hN hp hp2 hH hA => by
      haveI : Fact p.Prime := ⟨hp⟩
      exact tTail_le_nullity hP hN hp2 hH hA)

#print axioms tTail_le_nullity
end
end CatalanMeasure.GenD.Uniform.W.Thin
