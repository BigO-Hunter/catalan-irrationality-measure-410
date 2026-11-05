module
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.Cell
public import Submission.CatalanMeasure.GenD.Uniform.W.Combine
@[expose] public section
set_option Elab.async false

/-!
# Theorem C as a `NullityLB`

For a rational cell `c`, `cCond c P N p lo hi` collects the (linear) conditions under which the
interval `[lo, hi)` of positions lies in the cell; `cCount` is the largest such interval length and
`cCellLB c P hP` the nullity lower bound `cCount - (p - q)` (for `p` coprime to `c.modulus`).
`cLB P hP` is the pointwise maximum over the cells of Theorem C.
-/

namespace CatalanMeasure.GenD.Uniform.W.TheoremC
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.W
noncomputable section

/-- Linear conditions for the interval `[lo, hi)` of positions of the cell `c` (`h ≤ p`). -/
def cCond (c : CCell) (P : Parameters) (N p lo hi : ℕ) : Prop :=
  lo ≤ hi ∧ hi ≤ p ∧ P.h N ≤ p ∧ hi + (p - P.h N) ≤ (p - 1) / 2 ∧
  -(P.g N : ℤ) ≤ c.k0 * p - ((hi + (p - P.h N) : ℕ) : ℤ) ∧
  (c.k0 + (c.K : ℤ) - 1) * p + ((hi + (p - P.h N) : ℕ) : ℤ) < (P.n N : ℤ) - P.g N ∧
  ∀ e, lo ≤ e → e < hi →
    c.S * p + e + 1 ≤ P.H N ∧ P.H N ≤ (c.S + 1) * p + e ∧
    (c.Jlo - 1) * p + (P.H N - 1 - e - c.S * p) < P.b N ∧
    P.L N ≤ (c.Jhi + 1) * p + (P.H N - 1 - e - c.S * p)

/-- The largest admissible interval length. -/
def cCount (c : CCell) (P : Parameters) (N p : ℕ) : ℕ :=
  open Classical in
  ((Finset.range (p + 1) ×ˢ Finset.range (p + 1)).filter
    fun lh => cCond c P N p lh.1 lh.2).sup fun lh => lh.2 - lh.1

/-- Theorem C for the cell `c`, as a nullity lower bound. -/
def cCellLB (c : CCell) (P : Parameters) (hP : Admissible P) : NullityLB P :=
  NullityLB.ofWindow P (fun N p => Nat.Coprime p c.modulus ∧ 0 < P.q N)
    (fun N p => cCount c P N p - (p - P.q N)) (by
    intro N p hN hp hp2 hH hApp
    classical
    obtain ⟨hcop, hq⟩ := hApp
    haveI : Fact p.Prime := ⟨hp⟩
    have hbound : cCount c P N p ≤ nullity P N p + (p - P.q N) := by
      unfold cCount
      apply Finset.sup_le
      intro lh hlh
      rw [Finset.mem_filter] at hlh
      obtain ⟨_, h1, h2, h3, h4, h5, h6, h7⟩ := hlh
      have := cellC_le_nullity hP hN hH hq c hcop h1 h2 h3 h4 h5 h6 h7
      omega
    omega)

theorem cCellLB_kap_ge (c : CCell) (P : Parameters) (hP : Admissible P) {N p lo hi : ℕ}
    (hcop : Nat.Coprime p c.modulus) (hq : 0 < P.q N) (hc : cCond c P N p lo hi) :
    hi - lo - (p - P.q N) ≤ (cCellLB c P hP).kap N p := by
  classical
  unfold cCellLB NullityLB.ofWindow
  simp only
  rw [if_pos ⟨hcop, hq⟩]
  have hmem : (lo, hi) ∈ (Finset.range (p + 1) ×ˢ Finset.range (p + 1)).filter
      fun lh => cCond c P N p lh.1 lh.2 := by
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨by have := hc.1; have := hc.2.1; omega, by have := hc.2.1; omega⟩, hc⟩
  have := Finset.le_sup (f := fun lh : ℕ × ℕ => lh.2 - lh.1) hmem
  unfold cCount
  simp only at this ⊢
  omega

theorem ZmC_pos : 0 < ZmC := by
  unfold ZmC
  have h : ∀ (l : List ℕ) (a : ℕ), 0 < a → (∀ x ∈ l, 0 < x) → 0 < l.foldl Nat.lcm a := by
    intro l
    induction l with
    | nil => intro a ha _; exact ha
    | cons y l ih =>
      intro a ha hl
      exact ih _ (Nat.lcm_pos ha (hl y (List.mem_cons_self))) (fun x hx => hl x (List.mem_cons_of_mem _ hx))
  refine h _ 2 (by norm_num) ?_
  intro x hx
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨u, _, J, _, h | h⟩ := hx <;> rw [h] <;> exact Rat.den_pos _

theorem CCell.modulus_pos (c : CCell) (h : c.y c.ky ≠ 0) : 0 < c.modulus := by
  unfold CCell.modulus
  exact Nat.mul_pos ZmC_pos (Int.natAbs_pos.mpr h)

/-- A prime above the modulus is coprime to it. -/
theorem CCell.coprime_of_gt (c : CCell) (h : c.y c.ky ≠ 0) {p : ℕ} (hp : p.Prime)
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
