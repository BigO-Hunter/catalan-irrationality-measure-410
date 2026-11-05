module
public import Submission.CatalanMeasure.Cert.ShiftedDeriv
public import Submission.CatalanMeasure.Cert.Cover
@[expose] public section
namespace CatalanMeasure.Cert
open OAI.InternalCatalan Set Filter
open scoped Topology
noncomputable section

noncomputable def shiftedRowRegular (R : RowWeights) (Pc Vc : List ℤ) (P V : List TailQ)
    (x : ℝ) : ℝ :=
  rowRegular Pc Vc P V x-((R.gamma-65/48:ℚ):ℝ)*Real.log (1+x^2)+
    (R.lam:ℝ)*((R.d0:ℝ)-2*x^2/(1+x^2))

theorem shiftedRowField_split (R : RowWeights) (Pc Vc : List ℤ) (P V : List TailQ) (x : ℝ) :
    shiftedRowField R Pc Vc P V x=(R.alpha:ℝ)*Real.log |x|+
      (R.beta:ℝ)*Real.log (1-x)+shiftedRowRegular R Pc Vc P V x :=by
  unfold shiftedRowField shiftedRowRegular
  rw [rowField_split]
  push_cast
  ring

variable {R : RowWeights} {Pc Vc : List ℤ} {P V : List TailQ}
theorem shiftedRowRegular_continuousOn (hP : tailsInDisk P=true) (hV : tailsInDisk V=true) :
    ContinuousOn (shiftedRowRegular R Pc Vc P V) (Icc (-1:ℝ) 1) :=by
  have hd : Continuous (fun x : ℝ =>1+x^2) :=continuous_const.add (continuous_id.pow 2)
  have hdn (x : ℝ) : 1+x^2≠0 :=by positivity
  have hl :=hd.log hdn
  have hD : Continuous (fun x : ℝ =>(R.d0:ℝ)-2*x^2/(1+x^2)) :=
    continuous_const.sub ((continuous_const.mul (continuous_id.pow 2)).div hd hdn)
  exact ((rowRegular_continuousOn hP hV).sub
    (hl.continuousOn.const_mul _)).add (hD.continuousOn.const_mul _)

theorem shiftedRowField_continuousWithinAt (hP : tailsInDisk P = true) (hV : tailsInDisk V = true)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (h0 : x ≠ 0) (h1 : x ≠ 1) :
    ContinuousWithinAt (shiftedRowField R Pc Vc P V)
      (Icc (-1 : ℝ) 1) x := by
  have hlog : ContinuousAt (fun y : ℝ => Real.log |y|) x := by
    simpa only [Real.log_abs] using Real.continuousAt_log h0
  have hlog1 : ContinuousAt (fun y : ℝ => Real.log (1 - y)) x :=
    (continuousAt_const.sub continuousAt_id).log (sub_ne_zero.mpr (Ne.symm h1))
  have hh := ((hlog.continuousWithinAt.const_mul (R.alpha:ℝ)).add
    (hlog1.continuousWithinAt.const_mul (R.beta:ℝ))).add
    (shiftedRowRegular_continuousOn (R := R) (Pc := Pc) (Vc := Vc) hP hV x hx)
  convert hh using 1
  funext y
  exact shiftedRowField_split R Pc Vc P V y

theorem shiftedRowField_zero_remainder (hP : tailsInDisk P = true) (hV : tailsInDisk V = true) :
    ContinuousAt (fun x : ℝ => (R.beta:ℝ) * Real.log (1 - x) + shiftedRowRegular R Pc Vc P V x) 0 := by
  have hl : ContinuousAt (fun x : ℝ => Real.log (1 - x)) 0 :=
    (continuousAt_const.sub continuousAt_id).log (by norm_num)
  exact (hl.const_mul (R.beta:ℝ)).add
    (continuousOn_continuousAt_zero (shiftedRowRegular_continuousOn (R := R) (Pc := Pc) (Vc := Vc) hP hV))

theorem shiftedRowField_sup_of_cover (hP : tailsInDisk P = true) (hV : tailsInDisk V = true) (hAlpha : 0<R.alpha) (hBeta : 0<R.beta)
    {M : ℝ} {S : Set ℝ}
    (hm1 : shiftedRowField R Pc Vc P V (-1) ≤ M)
    (hcover : ∀ x ∈ Ioo (-1 : ℝ) 0 ∪ Ioo 0 1,
      deriv (shiftedRowField R Pc Vc P V) x = 0 → x ∈ S)
    (hvalues : ∀ x ∈ S, shiftedRowField R Pc Vc P V x ≤ M) :
    ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      shiftedRowField R Pc Vc P V x ≤ M := by
  set F := shiftedRowField R Pc Vc P V with hF
  have hsplit : F = fun x => (R.alpha:ℝ) * Real.log |x| +
      ((R.beta:ℝ) * Real.log (1 - x) + shiftedRowRegular R Pc Vc P V x) := by
    funext x; rw [hF, shiftedRowField_split]; ring
  apply GlobalMaxReduction.le_on_two_components_of_stationary_cover (S := S)
  · intro x hx
    apply (shiftedRowField_continuousWithinAt hP hV ⟨hx.1, by linarith [hx.2]⟩ (ne_of_lt hx.2)
      (by linarith [hx.2])).mono
    intro y hy; exact ⟨hy.1, by linarith [hy.2]⟩
  · intro x hx
    apply (shiftedRowField_continuousWithinAt hP hV ⟨by linarith [hx.1], hx.2.le⟩ (ne_of_gt hx.1)
      (ne_of_lt hx.2)).mono
    intro y hy; exact ⟨by linarith [hy.1], hy.2.le⟩
  · exact hm1
  · rw [hsplit]
    have hl : Tendsto (fun x : ℝ => (R.alpha:ℝ) * Real.log |x|) (𝓝[<] 0) atBot := by
      simpa only [Real.log_abs] using
        (Tendsto.const_mul_atBot (by exact_mod_cast hAlpha : (0 : ℝ) < R.alpha) Real.tendsto_log_nhdsLT_zero)
    exact atBot_add_finite hl ((shiftedRowField_zero_remainder (R := R) (Pc := Pc) (Vc := Vc) hP hV).tendsto.mono_left nhdsWithin_le_nhds)
  · rw [hsplit]
    have hl : Tendsto (fun x : ℝ => (R.alpha:ℝ) * Real.log |x|) (𝓝[>] 0) atBot := by
      simpa only [Real.log_abs] using
        (Tendsto.const_mul_atBot (by exact_mod_cast hAlpha : (0 : ℝ) < R.alpha) Real.tendsto_log_nhdsGT_zero)
    exact atBot_add_finite hl ((shiftedRowField_zero_remainder (R := R) (Pc := Pc) (Vc := Vc) hP hV).tendsto.mono_left nhdsWithin_le_nhds)
  · have hsplit' : F = fun x => (R.beta:ℝ) * Real.log (1 - x) +
        ((R.alpha:ℝ) * Real.log |x| + shiftedRowRegular R Pc Vc P V x) := by
      funext x; rw [hF, shiftedRowField_split]; ring
    rw [hsplit']
    have hl := Tendsto.const_mul_atBot (by exact_mod_cast hBeta : (0 : ℝ) < R.beta) log_one_sub_tendsto
    have hc : ContinuousAt (fun x : ℝ => Real.log |x|) 1 := by
      simpa only [Real.log_abs] using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0))
    have hr := ((hc.tendsto.mono_left nhdsWithin_le_nhds).const_mul (R.alpha:ℝ)).add
      (continuousOn_tendsto_one_left (shiftedRowRegular_continuousOn (R := R) (Pc := Pc) (Vc := Vc) hP hV))
    exact atBot_add_finite hl hr
  · exact hcover
  · exact hvalues


end
end CatalanMeasure.Cert
