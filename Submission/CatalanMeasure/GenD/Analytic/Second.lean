module

public import Submission.CatalanMeasure.GenD.Analytic.Fields
public import Submission.CatalanMeasure.Parametric.GroupedFieldAssembly
public import Submission.CatalanMeasure.Parametric.PopulationPhysicalValue

@[expose] public section

/-!
# Analytic layer: the second-population trial contract and its energy bound (design-generic)

`SecondTrialBounds P` is the generic form of `SecondTrialBoundsOn`: the actual trial-field facts
needed by the grouped second-population argument, for an arbitrary admissible `P`.  The budget
inequality is stated with the generic constants `gC0 P`, `gC1 P` (the old form with the
`(9/10) a` terms on both sides is equivalent: they cancel).

`second_energy` is the generic form of `second_energy_on`.
-/

namespace CatalanMeasure.GenD
namespace Analytic

open CatalanMeasure.Parametric OAI.InternalCatalan Filter Set
open scoped Topology BigOperators

noncomputable section

/-- Generic second-population trial contract. -/
structure SecondTrialBounds (P : Parameters) (target residual nearCap cost : ℝ)
    (G : ℝ → Prop) where
  p : ℕ → ℝ
  v : ℕ → ℝ
  MX : ℝ
  MY : ℝ
  normCap : ℝ
  fieldCap : ℝ
  p_summable : Summable (fun j => |p j|)
  v_summable : Summable (fun j => |v j|)
  norm_le : 2 * barrierTrialNormSq p + barrierTrialNormSq v / 2 ≤ normCap
  field_sum : MX + MY = fieldCap
  row : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      populationPhysicalFreeField P N x - 4 * barrierTrialT p x - barrierTrialS v x -
        Real.log (1 - x) / (2 * (P.n N : ℝ)) ≤ MX + ε
  column : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ s ∈ Ioo (0 : ℝ) 1,
      populationEndpointColumnField P N 0 s + 2 * barrierTrialT v s -
        Real.log (1 - s) / (P.n N : ℝ) ≤ MY + ε
  marked : ∀ {N : ℕ}, 0 < N → ∀ {x : ℝ}, x ∈ Icc (-1 : ℝ) 1 → G x →
    groupedMarkedField P N x - 2 * barrierTrialT p x ≤
      residual + Real.log 2 / (P.n N : ℝ)
  near : ∀ {N : ℕ}, 0 < N → ∀ {y : ℝ}, y ∈ Ioo (0 : ℝ) 1 →
    groupedNearField P N y - p 1 * y ≤ nearCap + Real.log 2 / (P.n N : ℝ)
  budget : ∀ {a t : ℝ}, 0 ≤ a → 0 ≤ t →
    (-gC0 P + gC1 P * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
      normCap + (1 - a) * fieldCap + a * (1 - a) * Real.log 2 +
      (a - t) * residual + t * nearCap ≤
        -target + Real.log 2 / 2 + cost * a

set_option maxHeartbeats 1600000 in
/-- Generic `second_energy_on`: the grouped second-population energy is at most the target. -/
theorem second_energy {P : Parameters} (hP : Admissible P)
    {target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (D : SecondTrialBounds P target residual nearCap cost G) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ (r a b : ℕ), r + a + b = P.n N →
      ∀ (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) (s : Fin r → ℝ),
      (∀ i, z i ∈ Ioo (-1 : ℝ) 1) → (∀ i, z i ≠ 0) →
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, G (x i)) → (∀ i, y i ∈ Ioo (0 : ℝ) 1) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective z →
      Function.Injective (Fin.append z x) → Function.Injective y → Function.Injective s →
      groupedValueWithFields (P.n N : ℝ) (groupedConstant P N r a b)
        (populationPhysicalFreeField P N) (groupedMarkedField P N)
        (groupedNearField P N) (populationPhysicalColumnField P N (a + b))
        z x y s ≤ -target + Real.log 2 / 2 +
          cost * (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) + δ := by
  let ε : ℝ := δ / 4
  have hε : 0 < ε := by dsimp [ε]; linarith only [hδ]
  obtain ⟨e, he, herr⟩ := grouped_error_eventually hP D.p D.v (by linarith : 0 < δ / 2)
  filter_upwards [D.row hε, D.column hε,
      log_reciprocal_eventually hP hε, herr, eventually_gt_atTop (0 : ℕ)]
    with N hrow hcol hsmall herror hN r a b hcount z x y s hz hz0 hx hxG hy hs hzi hxi hyi hsi
  let ν : ℝ := P.n N
  let α : ℝ := ((a + b : ℕ) : ℝ) / ν
  let β : ℝ := (b : ℝ) / ν
  have hν : 0 < ν := by
    dsimp only [ν]
    exact_mod_cast n_pos hP hN
  have hα : 0 ≤ α := div_nonneg (Nat.cast_nonneg _) hν.le
  have hβ : 0 ≤ β := div_nonneg (Nat.cast_nonneg _) hν.le
  have hfree : (r : ℝ) / ν = 1 - α := by
    have hf := population_fractions hP hN (show r + (a + b) = P.n N by omega)
    dsimp only [α, ν]
    linarith only [hf]
  have hmarked : (a : ℝ) / ν = α - β := by
    dsimp only [α, β]
    rw [Nat.cast_add, add_div]
    ring
  have hy' : ∀ i, y i ∈ Ioo (-1 : ℝ) 1 := fun i => ⟨by linarith [(hy i).1], (hy i).2⟩
  have hb := grouped_field_caps_bound (constant := groupedConstant P N r a b) hν he
    (by dsimp only [ν]; exact_mod_cast (show r + a ≤ P.n N by omega))
    (by dsimp only [ν]; exact_mod_cast (show b ≤ P.n N by omega)) z x y s hz hx hy' hs hzi hxi hyi hsi
    D.p D.p D.v D.p_summable D.p_summable D.v_summable
    (populationPhysicalFreeField P N) (groupedMarkedField P N)
    (groupedNearField P N) (populationPhysicalColumnField P N (a + b))
    (D.MX + ε) (residual + ε)
    (nearCap + ε) (D.MY + ε + α * Real.log 2)
    (fun i => by
      have hz' : z i ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1 := by
        by_cases ht : z i < 0
        · exact Or.inl ⟨(hz i).1.le, ht⟩
        · exact Or.inr ⟨lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm (hz0 i)), (hz i).2⟩
      have hh := hrow (z i) hz'
      linarith only [hh])
    (fun i => by
      have hh := D.marked hN ⟨(hx i).1.le, (hx i).2.le⟩ (hxG i)
      linarith only [hh, hsmall])
    (fun i => by
      have hh := D.near hN (hy i)
      linarith only [hh, hsmall])
    (fun i => by
      have hh := hcol (s i) (hs i)
      have hl : Real.log (1 + s i) ≤ Real.log 2 :=
        Real.log_le_log (by linarith [(hs i).1]) (by linarith [(hs i).2])
      have hm := mul_le_mul_of_nonneg_left hl hα
      have hid : populationPhysicalColumnField P N (a + b) (s i) =
          populationEndpointColumnField P N 0 (s i) + α * Real.log (1 + s i) := by
        unfold populationPhysicalColumnField populationEndpointColumnField α ν
        ring
      rw [hid]
      linarith only [hh, hm])
  have hconst := grouped_constant_le hP hN hcount
  have hbudget := D.budget hα hβ
  have hnorm := D.norm_le
  have hfields := congrArg (fun t : ℝ => (1 - α) * t) D.field_sum
  have hεα := mul_nonneg hε.le hα
  rw [← n_cast] at herror
  rw [hfree, hmarked] at hb
  rw [hfree] at hconst
  dsimp only [α, β, ν, ε] at hb hconst hbudget hfields hεα ⊢
  ring_nf at hb hconst hbudget hfields hnorm herror hεα ⊢
  nlinarith only [hb, hconst, hbudget, hfields, hnorm, herror, hεα]


/-- Second-population trial contract for the endpoint column field (no `α log (1 + s)` term):
identical to `SecondTrialBounds` except that the budget has no `a (1 - a) log 2` term. -/
structure SecondTrialBoundsEnd (P : Parameters) (α1 target residual nearCap cost : ℝ)
    (G : ℝ → Prop) where
  p : ℕ → ℝ
  v : ℕ → ℝ
  MX : ℝ
  MY : ℝ
  normCap : ℝ
  fieldCap : ℝ
  p_summable : Summable (fun j => |p j|)
  v_summable : Summable (fun j => |v j|)
  norm_le : 2 * barrierTrialNormSq p + barrierTrialNormSq v / 2 ≤ normCap
  field_sum : MX + MY = fieldCap
  row : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      populationPhysicalFreeField P N x - 4 * barrierTrialT p x - barrierTrialS v x -
        Real.log (1 - x) / (2 * (P.n N : ℝ)) ≤ MX + ε
  column : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ s ∈ Ioo (0 : ℝ) 1,
      populationEndpointColumnField P N 0 s + 2 * barrierTrialT v s -
        Real.log (1 - s) / (P.n N : ℝ) ≤ MY + ε
  marked : ∀ {N : ℕ}, 0 < N → ∀ {x : ℝ}, x ∈ Icc (-1 : ℝ) 1 → G x →
    groupedMarkedField P N x - 2 * barrierTrialT p x ≤
      residual + Real.log 2 / (P.n N : ℝ)
  near : ∀ {N : ℕ}, 0 < N → ∀ {y : ℝ}, y ∈ Ioo (0 : ℝ) 1 →
    groupedNearField P N y - p 1 * y ≤ nearCap + Real.log 2 / (P.n N : ℝ)
  budget : ∀ {a t : ℝ}, α1 ≤ a → 0 ≤ a → 0 ≤ t →
    (-gC0 P + gC1 P * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
      normCap + (1 - a) * fieldCap + (a - t) * residual + t * nearCap ≤
        -target + Real.log 2 / 2 + cost * a

set_option maxHeartbeats 1600000 in
/-- `second_energy` with the column field `populationEndpointColumnField P N 0`: the grouped
second-population energy is at most the target, with budget lacking `a (1 - a) log 2`. -/
theorem second_energy_end {P : Parameters} (hP : Admissible P)
    {α1 target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (D : SecondTrialBoundsEnd P α1 target residual nearCap cost G) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ (r a b : ℕ), r + a + b = P.n N →
      ∀ (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) (s : Fin r → ℝ),
      (∀ i, z i ∈ Ioo (-1 : ℝ) 1) → (∀ i, z i ≠ 0) →
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, G (x i)) → (∀ i, y i ∈ Ioo (0 : ℝ) 1) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective z →
      Function.Injective (Fin.append z x) → Function.Injective y → Function.Injective s →
      α1 * (P.n N : ℝ) ≤ ((a + b : ℕ) : ℝ) →
      groupedValueWithFields (P.n N : ℝ) (groupedConstant P N r a b)
        (populationPhysicalFreeField P N) (groupedMarkedField P N)
        (groupedNearField P N) (populationEndpointColumnField P N 0)
        z x y s ≤ -target + Real.log 2 / 2 +
          cost * (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) + δ := by
  let ε : ℝ := δ / 4
  have hε : 0 < ε := by dsimp [ε]; linarith only [hδ]
  obtain ⟨e, he, herr⟩ := grouped_error_eventually hP D.p D.v (by linarith : 0 < δ / 2)
  filter_upwards [D.row hε, D.column hε,
      log_reciprocal_eventually hP hε, herr, eventually_gt_atTop (0 : ℕ)]
    with N hrow hcol hsmall herror hN r a b hcount z x y s hz hz0 hx hxG hy hs hzi hxi hyi hsi hα1
  let ν : ℝ := P.n N
  let α : ℝ := ((a + b : ℕ) : ℝ) / ν
  let β : ℝ := (b : ℝ) / ν
  have hν : 0 < ν := by
    dsimp only [ν]
    exact_mod_cast n_pos hP hN
  have hα : 0 ≤ α := div_nonneg (Nat.cast_nonneg _) hν.le
  have hβ : 0 ≤ β := div_nonneg (Nat.cast_nonneg _) hν.le
  have hfree : (r : ℝ) / ν = 1 - α := by
    have hf := population_fractions hP hN (show r + (a + b) = P.n N by omega)
    dsimp only [α, ν]
    linarith only [hf]
  have hmarked : (a : ℝ) / ν = α - β := by
    dsimp only [α, β]
    rw [Nat.cast_add, add_div]
    ring
  have hy' : ∀ i, y i ∈ Ioo (-1 : ℝ) 1 := fun i => ⟨by linarith [(hy i).1], (hy i).2⟩
  have hb := grouped_field_caps_bound (constant := groupedConstant P N r a b) hν he
    (by dsimp only [ν]; exact_mod_cast (show r + a ≤ P.n N by omega))
    (by dsimp only [ν]; exact_mod_cast (show b ≤ P.n N by omega)) z x y s hz hx hy' hs hzi hxi hyi hsi
    D.p D.p D.v D.p_summable D.p_summable D.v_summable
    (populationPhysicalFreeField P N) (groupedMarkedField P N)
    (groupedNearField P N) (populationEndpointColumnField P N 0)
    (D.MX + ε) (residual + ε)
    (nearCap + ε) (D.MY + ε)
    (fun i => by
      have hz' : z i ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1 := by
        by_cases ht : z i < 0
        · exact Or.inl ⟨(hz i).1.le, ht⟩
        · exact Or.inr ⟨lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm (hz0 i)), (hz i).2⟩
      have hh := hrow (z i) hz'
      linarith only [hh])
    (fun i => by
      have hh := D.marked hN ⟨(hx i).1.le, (hx i).2.le⟩ (hxG i)
      linarith only [hh, hsmall])
    (fun i => by
      have hh := D.near hN (hy i)
      linarith only [hh, hsmall])
    (fun i => by
      have hh := hcol (s i) (hs i)
      linarith only [hh])
  have hconst := grouped_constant_le hP hN hcount
  have hα1' : α1 ≤ α := by
    dsimp only [α, ν]
    rw [le_div_iff₀ hν]
    exact hα1
  have hbudget := D.budget hα1' hα hβ
  have hnorm := D.norm_le
  have hfields := congrArg (fun t : ℝ => (1 - α) * t) D.field_sum
  have hεα' : 0 ≤ ((P.n N : ℕ) : ℝ)⁻¹ * ((a + b : ℕ) : ℝ) * δ := by positivity
  rw [← n_cast] at herror
  rw [hfree, hmarked] at hb
  rw [hfree] at hconst
  dsimp only [α, β, ν, ε] at hb hconst hbudget hfields ⊢
  ring_nf at hb hconst hbudget hfields hnorm herror ⊢
  nlinarith only [hb, hconst, hbudget, hfields, hnorm, herror, hεα']

end
end Analytic
end CatalanMeasure.GenD
