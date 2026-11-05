module
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.CellP
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.LB
public import Submission.CatalanMeasure.GenD.Uniform.W.Combine
@[expose] public section
set_option Elab.async false

/-!
# Theorem C' as a `NullityLB`

`cCondP c P N p lo hi`: linear conditions for the interval `[lo, hi)` of positions of the cell `c`
(`h ≥ p`); `cCountP` is the largest value of `hi - lo - (h - p)`, and `cCellLBP c P hP` the bound
`cCountP - (p - q)` for `p` coprime to `c.modulus`.
-/

namespace CatalanMeasure.GenD.Uniform.W.TheoremC
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.W
noncomputable section

/-- Linear conditions for the interval `[lo, hi)` of positions of the cell `c` (`h ≥ p`). -/
def cCondP (c : CCell2) (P : Parameters) (N p lo hi : ℕ) : Prop :=
  hi ≤ p ∧ p ≤ P.h N ∧ hi - (P.h N - p) ≤ (p - 1) / 2 ∧
  -(P.g N : ℤ) ≤ c.k0 * p - ((hi - (P.h N - p) : ℕ) : ℤ) ∧
  (c.k0 + (c.K : ℤ) - 1) * p + ((hi - (P.h N - p) : ℕ) : ℤ) < (P.n N : ℤ) - P.g N ∧
  ∀ e, lo ≤ e → e < hi →
    c.S * p + e + 1 ≤ P.H N ∧ P.H N ≤ (c.S + 1) * p + e ∧
    (c.Jlo - 1) * p + (P.H N - 1 - e - c.S * p) < P.b N ∧
    P.L N ≤ (c.Jhi + 1) * p + (P.H N - 1 - e - c.S * p)

/-- The largest family dimension `hi - lo - (h - p)`. -/
def cCountP (c : CCell2) (P : Parameters) (N p : ℕ) : ℕ :=
  open Classical in
  ((Finset.range (p + 1) ×ˢ Finset.range (p + 1)).filter
    fun lh => cCondP c P N p lh.1 lh.2).sup fun lh => lh.2 - lh.1 - (P.h N - p)

/-- Theorem C' for the cell `c`, as a nullity lower bound. -/
def cCellLBP (c : CCell2) (P : Parameters) (hP : Admissible P) : NullityLB P :=
  NullityLB.ofWindow P (fun N p => Nat.Coprime p c.modulus ∧ 0 < P.q N)
    (fun N p => cCountP c P N p - (p - P.q N)) (by
    intro N p hN hp hp2 hH hApp
    classical
    obtain ⟨hcop, hq⟩ := hApp
    haveI : Fact p.Prime := ⟨hp⟩
    have hbound : cCountP c P N p ≤ nullity P N p + (p - P.q N) := by
      unfold cCountP
      apply Finset.sup_le
      intro lh hlh
      rw [Finset.mem_filter] at hlh
      obtain ⟨_, h1, h2, h4, h5, h6, h7⟩ := hlh
      by_cases h3 : lh.1 + (P.h N - p) ≤ lh.2
      · have := cellCp_le_nullity hP hN hH hq c hcop h1 h2 h3 h4 h5 h6 h7
        omega
      · omega
    omega)

theorem cCellLBP_kap_ge (c : CCell2) (P : Parameters) (hP : Admissible P) {N p lo hi : ℕ}
    (hcop : Nat.Coprime p c.modulus) (hq : 0 < P.q N) (hc : cCondP c P N p lo hi) :
    hi - lo - (P.h N - p) - (p - P.q N) ≤ (cCellLBP c P hP).kap N p := by
  classical
  unfold cCellLBP NullityLB.ofWindow
  simp only
  rw [if_pos ⟨hcop, hq⟩]
  by_cases hlo : lo ≤ p
  swap
  · have := hc.1; omega
  have hmem : (lo, hi) ∈ (Finset.range (p + 1) ×ˢ Finset.range (p + 1)).filter
      fun lh => cCondP c P N p lh.1 lh.2 := by
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨by omega, by have := hc.1; omega⟩, hc⟩
  have := Finset.le_sup (f := fun lh : ℕ × ℕ => lh.2 - lh.1 - (P.h N - p)) hmem
  unfold cCountP
  simp only at this ⊢
  omega

theorem ZmD_pos : 0 < ZmD := by
  unfold ZmD
  have h : ∀ (l : List ℕ) (a : ℕ), 0 < a → (∀ x ∈ l, 0 < x) → 0 < l.foldl Nat.lcm a := by
    intro l
    induction l with
    | nil => intro a ha _; exact ha
    | cons y l ih =>
      intro a ha hl
      exact ih _ (Nat.lcm_pos ha (hl y (List.mem_cons_self)))
        (fun x hx => hl x (List.mem_cons_of_mem _ hx))
  refine h _ 2 (by norm_num) ?_
  intro x hx
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨u, _, J, _, h | h⟩ := hx <;> rw [h] <;> exact Rat.den_pos _

theorem CCell2.modulus_pos (c : CCell2) (h : c.y c.ky ≠ 0) : 0 < c.modulus := by
  unfold CCell2.modulus
  exact Nat.mul_pos ZmD_pos (Int.natAbs_pos.mpr h)

theorem CCell2.coprime_of_gt (c : CCell2) (h : c.y c.ky ≠ 0) {p : ℕ} (hp : p.Prime)
    (hlt : c.modulus < p) : Nat.Coprime p c.modulus := by
  rw [Nat.coprime_comm, Nat.Coprime]
  rw [← Nat.coprime_iff_gcd_eq_one]
  apply Nat.Coprime.symm
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hd
  have := Nat.le_of_dvd (c.modulus_pos h) hd
  omega

end
end CatalanMeasure.GenD.Uniform.W.TheoremC
