module

public import Submission.CatalanMeasure.GenD.PL

@[expose] public section

/-!
# Generic prime-growth engine (module 2 of the G-displacement Lean plan)

Design-free.  Let `e N p` be the exponent of the prime `p` in a content product.  If on a window
`(a N, b N]` one has `e N p ≥ N F(p/N) - 1` with `F` continuous on `[a,b]` (the `-1` is the
integer-rounding loss), then for every `c < ∫_a^b F`, eventually `c N² ≤ ∑ e N p log p`.
For a list of windows ordered by `b_i ≤ a_j` (`i` before `j`) the areas add (the exponent at a
prime is a single best bound, counted once; the windows are the cells on which one bound is used).
-/

namespace CatalanMeasure.GenD
namespace PrimeGrowth

open Filter MeasureTheory intervalIntegral
open OAI.Zeta5.Workers.W14 OAI.Zeta5.W12.ImportedPNTCoreBridge
open scoped Topology BigOperators

noncomputable section

/-- The primes in the window `(aN, bN]`. -/
def winPrimes (a b : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.Ioc ⌊a * (N : ℝ)⌋₊ ⌊b * (N : ℝ)⌋₊).filter Nat.Prime

theorem mem_winPrimes {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {N p : ℕ} :
    p ∈ winPrimes a b N ↔ a * N < p ∧ (p : ℝ) ≤ b * N ∧ p.Prime := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  exact mem_primeInterval_iff (mul_nonneg ha hN) (mul_le_mul_of_nonneg_right hab hN) p

/-- One window: continuous profile `F` on `[a,b]`. -/
theorem single_growth {F : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hF : ContinuousOn F (Set.Icc a b)) (e : ℕ → ℕ → ℕ)
    (he : ∀ N p : ℕ, 0 < N → p.Prime → a * N < p → (p : ℝ) ≤ b * N →
      (N : ℝ) * F ((p : ℝ) / N) - 1 ≤ e N p)
    {c : ℝ} (hc : c < ∫ x in a..b, F x) :
    ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ 2 ≤ ∑ p ∈ winPrimes a b N, (e N p : ℝ) * Real.log p := by
  have hw := (PL.weighted_tendsto_of_continuousOn ha hab hF).comp tendsto_natCast_atTop_atTop
  have he' := ((primeIntervalSum_scaled_tendsto theta_ratio_tendsto_one ha hab).comp
      tendsto_natCast_atTop_atTop).mul (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  have hl := hw.sub he'
  simp only [mul_zero, sub_zero] at hl
  have hev := hl.eventually (lt_mem_nhds hc)
  filter_upwards [hev, eventually_gt_atTop (0 : ℕ)] with N hbound hN
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
    have := mul_le_mul_of_nonneg_right (he N p hN hp'.2.2 hp'.1 hp'.2.1) hlog
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

/-- A window with its profile. -/
structure Seg where
  a : ℝ
  b : ℝ
  F : ℝ → ℝ

/-- Area of a window. -/
def Seg.area (s : Seg) : ℝ := ∫ x in s.a..s.b, s.F x

/-- Hypotheses of one window for the exponent function `e`. -/
def Seg.Good (e : ℕ → ℕ → ℕ) (s : Seg) : Prop :=
  0 < s.a ∧ s.a < s.b ∧ ContinuousOn s.F (Set.Icc s.a s.b) ∧
    ∀ N p : ℕ, 0 < N → p.Prime → s.a * N < p → (p : ℝ) ≤ s.b * N →
      (N : ℝ) * s.F ((p : ℝ) / N) - 1 ≤ e N p

/-- Total area of a list of windows. -/
def totalArea (l : List Seg) : ℝ := (l.map Seg.area).sum

/-- Several windows, ordered `b_i ≤ a_j` for `i` before `j`: the areas add.  `T N` is any finite
set containing the primes of all windows; the exponent is a natural number so partial sums are
monotone. -/
theorem segs_growth (e : ℕ → ℕ → ℕ) (T : ℕ → Finset ℕ) :
    ∀ (l : List Seg), (∀ s ∈ l, Seg.Good e s) → l.Pairwise (fun s t => s.b ≤ t.a) →
    (∀ N : ℕ, ∀ s ∈ l, ∀ p : ℕ, p.Prime → s.a * N < p → (p : ℝ) ≤ s.b * N → p ∈ T N) →
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
    have h1 := single_growth (F := s.F) hs.1 hs.2.1 hs.2.2.1 e hs.2.2.2
      (c := s.area - δ) (by unfold Seg.area at *; linarith)
    have h2 := segs_growth e (fun N => (T N).filter (fun p => s.b * (N : ℝ) < p)) rest hrest
      hord.2 (by
        intro N t ht p hp hpa hpb
        have hbt := hord.1 t ht
        have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        have hlt : s.b * (N : ℝ) < p :=
          lt_of_le_of_lt (mul_le_mul_of_nonneg_right hbt hN) hpa
        exact Finset.mem_filter.mpr ⟨hT N t (List.mem_cons_of_mem _ ht) p hp hpa hpb, hlt⟩)
      (c := totalArea rest - δ) (by linarith)
    filter_upwards [h1, h2] with N hN1 hN2
    have hsub1 : winPrimes s.a s.b N ⊆ T N := by
      intro p hp
      have hp' := (mem_winPrimes hs.1.le hs.2.1.le).mp hp
      exact hT N s List.mem_cons_self p hp'.2.2 hp'.1 hp'.2.1
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


/-! ### The ledger exponent: floor of the profile, one bound per prime (a max, never a sum) -/

/-- Integer rounding: `N x - 1 ≤ ⌊N x⌋₊`. -/
theorem le_floor_sub_one (y : ℝ) : y - 1 ≤ (⌊y⌋₊ : ℝ) := by
  rcases le_or_gt 0 y with hy | hy
  · linarith [Nat.lt_floor_add_one y]
  · rw [Nat.floor_of_nonpos hy.le]; simp; linarith

/-- The exponent attached to a prime by a list of windows: the largest of the rounded window
profiles that apply at `p`.  The ledger counts the best proved bound once. -/
def segExp (l : List Seg) (N p : ℕ) : ℕ :=
  (l.map fun s => if s.a * (N : ℝ) < p ∧ (p : ℝ) ≤ s.b * N then ⌊(N : ℝ) * s.F ((p : ℝ) / N)⌋₊
    else 0).foldr max 0

theorem le_foldr_max {α : Type*} (f : α → ℕ) (l : List α) {s : α} (hs : s ∈ l) :
    f s ≤ (l.map f).foldr max 0 := by
  induction l with
  | nil => simp at hs
  | cons t l ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp hs with rfl | hs'
    · exact le_max_left _ _
    · exact (ih hs').trans (le_max_right _ _)

theorem segExp_ge {l : List Seg} {s : Seg} (hs : s ∈ l) {N p : ℕ}
    (h1 : s.a * (N : ℝ) < p) (h2 : (p : ℝ) ≤ s.b * N) :
    (N : ℝ) * s.F ((p : ℝ) / N) - 1 ≤ segExp l N p := by
  have := le_foldr_max (fun s : Seg => if s.a * (N : ℝ) < p ∧ (p : ℝ) ≤ s.b * N
    then ⌊(N : ℝ) * s.F ((p : ℝ) / N)⌋₊ else 0) l hs
  simp only [h1, h2, and_self, if_true] at this
  have h3 := le_floor_sub_one ((N : ℝ) * s.F ((p : ℝ) / N))
  have h4 : ((⌊(N : ℝ) * s.F ((p : ℝ) / N)⌋₊ : ℕ) : ℝ) ≤ (segExp l N p : ℝ) := by
    exact_mod_cast this
  linarith

/-- End-to-end generic engine: continuous profiles on ordered windows give
`log content ≥ (total area - ε) N²` for the content `∏ p^(segExp l N p)`. -/
theorem growth_segExp (l : List Seg)
    (hgood : ∀ s ∈ l, 0 < s.a ∧ s.a < s.b ∧ ContinuousOn s.F (Set.Icc s.a s.b))
    (hord : l.Pairwise (fun s t => s.b ≤ t.a)) (T : ℕ → Finset ℕ)
    (hT : ∀ N : ℕ, ∀ s ∈ l, ∀ p : ℕ, p.Prime → s.a * N < p → (p : ℝ) ≤ s.b * N → p ∈ T N)
    {c : ℝ} (hc : c < totalArea l) :
    ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ 2 ≤ ∑ p ∈ T N, (segExp l N p : ℝ) * Real.log p :=
  segs_growth (segExp l) T l
    (fun s hs => ⟨(hgood s hs).1, (hgood s hs).2.1, (hgood s hs).2.2,
      fun _ _ _ _ h1 h2 => segExp_ge hs h1 h2⟩) hord hT hc

/-! ### Windows given by profiles with closed-form areas -/

/-- Windows `(a, b, f)` carrying a piecewise-linear profile `f`. -/
def profSegs (l : List (ℝ × ℝ × PL.Prof)) : List Seg :=
  l.map fun t => ⟨t.1, t.2.1, t.2.2.eval⟩

theorem totalArea_profSegs (l : List (ℝ × ℝ × PL.Prof)) (h : ∀ t ∈ l, t.1 ≤ t.2.1) :
    totalArea (profSegs l) = (l.map fun t => t.2.2.area t.1 t.2.1).sum := by
  unfold totalArea profSegs
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  simp only [Function.comp_apply, Seg.area]
  exact t.2.2.integral_eval (h t ht)

/-- The logarithm of a content product is the exponent-weighted prime sum. -/
theorem log_prod_pow (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (e : ℕ → ℕ) :
    Real.log (((∏ p ∈ T, p ^ e p : ℕ) : ℝ)) = ∑ p ∈ T, (e p : ℝ) * Real.log p := by
  rw [Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p _
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    exact Nat.cast_ne_zero.mpr (pow_ne_zero _ (hT p hp).ne_zero)

end
end PrimeGrowth
end CatalanMeasure.GenD
