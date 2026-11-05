module
public import Submission.CatalanMeasure.PopulationFields
@[expose] public section
namespace CatalanMeasure
open Set Filter Real
open scoped Topology
noncomputable section

/-- Finite diagonal corrections preserve a uniform field cap. The logarithmic endpoint
is controlled by its positive leading coefficient, rather than by a sampled cutoff. -/
theorem log_field_correction_eventually {S : Set ℝ} {F : ℝ → ℝ}
    {M K β a b : ℝ} (hβ : 0<β) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hS : ∀ x ∈ S,-1 ≤ x ∧ x<1)
    (hM : ∀ x ∈ S,F x ≤ M) (hK : ∀ x ∈ S,F x ≤ β*Real.log (1-x)+K)
    (t : ℕ → ℝ) (ht0 : ∀ N,0 ≤ t N) (ht : Tendsto t atTop (𝓝 0))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ x ∈ S,F x+t N*(a*Real.log (1+x^2)-b*Real.log (1-x)) ≤ M+ε :=by
  let θ : ℝ :=min ((M-K-1)/(β/2)) (-1)
  let δ : ℝ :=Real.exp θ
  have hδ : 0<δ :=Real.exp_pos _
  have hθ : θ ≤ -1 :=min_le_right _ _
  have hlogδ : Real.log δ=θ :=Real.log_exp _
  have hcut : (β/2)*Real.log δ+K+1 ≤ M :=by
    have hh :=min_le_left ((M-K-1)/(β/2)) (-1:ℝ)
    have hm :=mul_le_mul_of_nonneg_left hh (show 0 ≤ β/2 by positivity)
    have he : (β/2)*((M-K-1)/(β/2))=M-K-1 :=by field_simp
    rw [he] at hm
    rw [hlogδ]
    dsimp only [θ]
    linarith
  have hδ1 : δ ≤ 1 :=by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have h1 :=(tendsto_order.mp (ht.mul_const (a*Real.log 2))).2 (1:ℝ) (by norm_num)
  have h2 :=(tendsto_order.mp (ht.mul_const b)).2 (β/2) (by simpa only [zero_mul] using (show (0:ℝ)<β/2 by positivity))
  have h3 :=(tendsto_order.mp (ht.mul_const (a*Real.log 2-b*Real.log δ))).2 ε (by simpa only [zero_mul] using hε)
  filter_upwards [h1,h2,h3] with N ht1 ht2 ht3 x hx
  obtain ⟨hxl,hxr⟩ :=hS x hx
  have hbase :=hM x hx
  have hend :=hK x hx
  have hlog2 : Real.log (1+x^2) ≤ Real.log 2 :=by
    apply Real.log_le_log (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr hxr.le) (show 0 ≤ 1+x by linarith)]
  have harg : 0<1-x :=by linarith
  have hA :=mul_le_mul_of_nonneg_left hlog2 ha
  by_cases hnear : 1-x ≤ δ
  · have hL : Real.log (1-x) ≤ Real.log δ :=Real.log_le_log harg hnear
    have hL0 : Real.log (1-x) ≤ 0 :=Real.log_nonpos harg.le (hnear.trans hδ1)
    have hB : (β-t N*b)*Real.log (1-x) ≤ (β/2)*Real.log (1-x) :=
      mul_le_mul_of_nonpos_right (by linarith : β/2 ≤ β-t N*b) hL0
    have hA' :=mul_le_mul_of_nonneg_left hA (ht0 N)
    have hL' :=mul_le_mul_of_nonneg_left hL (show 0 ≤ β/2 by positivity)
    nlinarith only [hend,hB,hA',hL',hcut,ht1,hε]
  · have hL : Real.log δ ≤ Real.log (1-x) :=Real.log_le_log hδ (by linarith)
    have hB :=mul_le_mul_of_nonneg_left hL hb
    have hCorr : a*Real.log (1+x^2)-b*Real.log (1-x) ≤ a*Real.log 2-b*Real.log δ :=by linarith
    have hCorr' :=mul_le_mul_of_nonneg_left hCorr (ht0 N)
    linarith

end
end CatalanMeasure
