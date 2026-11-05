module
public import Submission.CatalanMeasure.GenD.PrimeGrowth
@[expose] public section
namespace CatalanMeasure.GenD.Uniform.Arithmetic.WindowGrowth
open CatalanMeasure.GenD.PrimeGrowth Filter
open OAI.Zeta5.Workers.W14 OAI.Zeta5.W12.ImportedPNTCoreBridge
open scoped Topology BigOperators
noncomputable section
theorem single_growth_eventually {F : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hF : ContinuousOn F (Set.Icc a b)) (e : ℕ → ℕ → ℕ)
    (he : ∀ᶠ N : ℕ in atTop, ∀p : ℕ, p.Prime → a*N<p → (p:ℝ)≤b*N →
      (N : ℝ) * F ((p : ℝ) / N) - 1 ≤ e N p)
    {c : ℝ} (hc : c < ∫ x in a..b, F x) :
    ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ 2 ≤ ∑ p ∈ winPrimes a b N, (e N p : ℝ) * Real.log p := by
  have hw := (PL.weighted_tendsto_of_continuousOn ha hab hF).comp tendsto_natCast_atTop_atTop
  have he' := ((primeIntervalSum_scaled_tendsto theta_ratio_tendsto_one ha hab).comp
      tendsto_natCast_atTop_atTop).mul (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  have hl := hw.sub he'
  simp only [mul_zero, sub_zero] at hl
  have hev := hl.eventually (lt_mem_nhds hc)
  filter_upwards [hev, he, eventually_gt_atTop (0 : ℕ)] with N hbound heN hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : (N : ℝ) * (∑ p ∈ winPrimes a b N, F ((p : ℝ) / N) * Real.log p) -
      ∑ p ∈ winPrimes a b N, Real.log (p : ℝ) ≤
      ∑ p ∈ winPrimes a b N, (e N p : ℝ) * Real.log p := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hp' := (mem_winPrimes ha.le hab.le).mp hp
    have hlog : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hp'.2.2.one_lt.le)
    have := mul_le_mul_of_nonneg_right (heN p hp'.2.2 hp'.1 hp'.2.1) hlog
    nlinarith
  have hW : weightedPrimeIntervalSum F a b (N : ℝ) =
      (∑ p ∈ winPrimes a b N, F ((p : ℝ) / N) * Real.log p) / N := rfl
  have hP : primeIntervalSum (a * (N : ℝ)) (b * (N : ℝ)) =
      ∑ p ∈ winPrimes a b N, Real.log (p : ℝ) := rfl
  simp only [Function.comp_apply] at hbound
  rw [hW, hP] at hbound
  have h2 : c * (N : ℝ) ^ 2 ≤ (N : ℝ) * (∑ p ∈ winPrimes a b N, F ((p : ℝ) / N) * Real.log p) -
      ∑ p ∈ winPrimes a b N, Real.log (p : ℝ) := by
    set A := ∑ p ∈ winPrimes a b N, F ((p : ℝ) / N) * Real.log p
    set B := ∑ p ∈ winPrimes a b N, Real.log (p : ℝ)
    have h3 : c < A / N - B / N * (1 / N) := hbound
    have h4 : A / N - B / N * (1 / N) = (N * A - B) / (N : ℝ) ^ 2 := by
      field_simp
    rw [h4, lt_div_iff₀ (by positivity)] at h3
    exact h3.le
  exact h2.trans hsum


/-- Finite pointwise window certificates need hold only at sufficiently large scales. -/
def GoodEventually (e : ℕ→ℕ→ℕ) (s : Seg) : Prop :=
  0<s.a ∧ s.a<s.b ∧ ContinuousOn s.F (Set.Icc s.a s.b) ∧
    ∀ᶠ N:ℕ in atTop, ∀p:ℕ,p.Prime→s.a*N<p→(p:ℝ)≤s.b*N→
      (N:ℝ)*s.F ((p:ℝ)/N)-1≤e N p

theorem segs_growth_eventually (e : ℕ → ℕ → ℕ) (T : ℕ → Finset ℕ) :
    ∀ (l : List Seg), (∀ s ∈ l, GoodEventually e s) → l.Pairwise (fun s t => s.b ≤ t.a) →
    (∀ᶠ N : ℕ in atTop, ∀ s ∈ l, ∀ p : ℕ, p.Prime → s.a * N < p → (p : ℝ) ≤ s.b * N → p ∈ T N) →
    ∀ {c : ℝ}, c < totalArea l →
    ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ 2 ≤ ∑ p ∈ T N, (e N p : ℝ) * Real.log p
  | [], _, _, _, c, hc => by
    refine Eventually.of_forall fun N => ?_
    have h0 : c < 0 := by simpa [totalArea] using hc
    have : 0 ≤ ∑ p ∈ T N, (e N p : ℝ) * Real.log p := by
      apply Finset.sum_nonneg
      intro p hp
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)
    nlinarith [sq_nonneg (N : ℝ)]
  | s :: rest, hgood, hord, hT, c, hc => by
    have hs := hgood s List.mem_cons_self
    have hrest := fun t ht => hgood t (List.mem_cons_of_mem _ ht)
    rw [List.pairwise_cons] at hord
    have htot : totalArea (s :: rest) = s.area + totalArea rest := by simp [totalArea]
    rw [htot] at hc
    set δ := (s.area + totalArea rest - c) / 2 with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    have h1 := single_growth_eventually (F := s.F) hs.1 hs.2.1 hs.2.2.1 e hs.2.2.2
      (c := s.area - δ) (by unfold Seg.area at *; linarith)
    have h2 := segs_growth_eventually e (fun N => (T N).filter (fun p => s.b * (N : ℝ) < p)) rest hrest
      hord.2 (by
        filter_upwards [hT] with N hTN
        intro t ht p hp hpa hpb
        have hbt := hord.1 t ht
        have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        have hlt : s.b * (N : ℝ) < p :=
          lt_of_le_of_lt (mul_le_mul_of_nonneg_right hbt hN) hpa
        exact Finset.mem_filter.mpr ⟨hTN t (List.mem_cons_of_mem _ ht) p hp hpa hpb, hlt⟩)
      (c := totalArea rest - δ) (by linarith)
    filter_upwards [h1, h2,hT] with N hN1 hN2 hTN
    have hsub1 : winPrimes s.a s.b N ⊆ T N := by
      intro p hp
      have hp' := (mem_winPrimes hs.1.le hs.2.1.le).mp hp
      exact hTN s List.mem_cons_self p hp'.2.2 hp'.1 hp'.2.1
    have hdisj : Disjoint (winPrimes s.a s.b N)
        ((T N).filter (fun p => s.b * (N : ℝ) < p)) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      have h1' := ((mem_winPrimes hs.1.le hs.2.1.le).mp hp1).2.1
      have h2' := (Finset.mem_filter.mp hp2).2
      linarith
    have hsub : winPrimes s.a s.b N ∪ (T N).filter (fun p => s.b * (N : ℝ) < p) ⊆ T N :=
      Finset.union_subset hsub1 (Finset.filter_subset _ _)
    have hnn : ∀ p ∈ T N, p ∉ winPrimes s.a s.b N ∪ (T N).filter (fun p => s.b * (N : ℝ) < p) →
        0 ≤ (e N p : ℝ) * Real.log p := fun p _ _ =>
      mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
    rw [Finset.sum_union hdisj] at hle
    have hexp : c * (N : ℝ) ^ 2 =
        (s.area - δ) * (N : ℝ) ^ 2 + (totalArea rest - δ) * (N : ℝ) ^ 2 := by
      rw [hδ]; ring
    rw [hexp]
    linarith



end
end CatalanMeasure.GenD.Uniform.Arithmetic.WindowGrowth
