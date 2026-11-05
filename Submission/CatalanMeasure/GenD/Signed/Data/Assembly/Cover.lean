module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith


@[expose] public section

/-!
# 410 assembly: generic cover glue for the cell rows

* `ContigCells a cs b`: the cells `cs = [(l₀,h₀), (l₁,h₁), …]` are consecutive, `l₀ = a`, `hᵢ = lᵢ₊₁`, last `h = b`.
* `cover_eventually`: if every cell satisfies `Q ε N x` for all `x ∈ [l, h]` eventually in `N` (for each `ε > 0`),
  then the whole `[a, b]` does (for a nonempty list).  Lane C's per-cell row theorems plug in as `hcell`.
* `affine_mix_le`: the α-uniformization (certify at the two endpoint values of α, mix).
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open Set Filter

/-- Consecutive cells from `a` to `b`. -/
def ContigCells : ℝ → List (ℝ × ℝ) → ℝ → Prop
  | a, [], b => a = b
  | a, c :: cs, b => c.1 = a ∧ c.1 ≤ c.2 ∧ ContigCells c.2 cs b

theorem contig_cover : ∀ (cs : List (ℝ × ℝ)) (a b : ℝ), ContigCells a cs b →
    ∀ x ∈ Icc a b, (x = a ∧ cs = []) ∨ ∃ c ∈ cs, x ∈ Icc c.1 c.2 := by
  intro cs
  induction cs with
  | nil =>
    intro a b h x hx
    simp only [ContigCells] at h
    subst h
    exact Or.inl ⟨le_antisymm hx.2 hx.1, rfl⟩
  | cons c cs ih =>
    intro a b h x hx
    obtain ⟨h1, h2, h3⟩ := h
    by_cases hxc : x ≤ c.2
    · exact Or.inr ⟨c, List.mem_cons_self, by rw [h1]; exact ⟨hx.1, hxc⟩⟩
    · push_neg at hxc
      rcases ih c.2 b h3 x ⟨hxc.le, hx.2⟩ with ⟨hx2, _⟩ | ⟨d, hd, hxd⟩
      · exact absurd hx2 (ne_of_gt hxc)
      · exact Or.inr ⟨d, List.mem_cons_of_mem _ hd, hxd⟩

theorem eventually_forall_list {α : Type*} (l : List α) (p : α → ℕ → Prop)
    (h : ∀ x ∈ l, ∀ᶠ N : ℕ in atTop, p x N) : ∀ᶠ N : ℕ in atTop, ∀ x ∈ l, p x N := by
  induction l with
  | nil => exact Filter.Eventually.of_forall (by simp)
  | cons y l ih =>
    filter_upwards [h y List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
      with N h1 h2 x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact h1
    · exact h2 x hx'

/-- **Cover glue.**  `Q ε N x` is the cell statement (`field N x ≤ T + ε`, say). -/
theorem cover_eventually {Q : ℝ → ℕ → ℝ → Prop} {cs : List (ℝ × ℝ)} {a b : ℝ}
    (hc : ContigCells a cs b) (hne : cs ≠ [])
    (hcell : ∀ c ∈ cs, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Icc c.1 c.2, Q ε N x) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Icc a b, Q ε N x := by
  intro ε hε
  have hall := eventually_forall_list cs (fun c N => ∀ x ∈ Icc c.1 c.2, Q ε N x)
    (fun c hc' => hcell c hc' ε hε)
  filter_upwards [hall] with N hN x hx
  rcases contig_cover cs a b hc x hx with ⟨_, h⟩ | ⟨d, hd, hxd⟩
  · exact absurd h hne
  · exact hN d hd x hxd

/-- **α-affine mixing**: a quantity affine in `α ∈ [lo, hi]` (`F α = (1-l) F lo + l F hi`,
`l = (α - lo)/(hi - lo)`) with the bound `T` affine likewise is bounded on the whole interval once it
is bounded at the two endpoints. -/
theorem affine_mix_le {F : ℝ → ℝ} {T : ℝ → ℝ} {lo hi α ε : ℝ} (hlo : lo < hi)
    (hα : α ∈ Icc lo hi)
    (hF : F α = (1 - (α - lo) / (hi - lo)) * F lo + (α - lo) / (hi - lo) * F hi)
    (hT : T α = (1 - (α - lo) / (hi - lo)) * T lo + (α - lo) / (hi - lo) * T hi)
    (h0 : F lo ≤ T lo + ε) (h1 : F hi ≤ T hi + ε) : F α ≤ T α + ε := by
  have hd : 0 < hi - lo := sub_pos.2 hlo
  have hl0 : 0 ≤ (α - lo) / (hi - lo) := div_nonneg (by linarith [hα.1]) hd.le
  have hl1 : (α - lo) / (hi - lo) ≤ 1 := (div_le_one hd).2 (by linarith [hα.2])
  rw [hF, hT]
  nlinarith [mul_le_mul_of_nonneg_left h0 (sub_nonneg.2 hl1), mul_le_mul_of_nonneg_left h1 hl0]

end CatalanMeasure.GenD.Signed.Data.Assembly
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.cover_eventually
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.affine_mix_le
