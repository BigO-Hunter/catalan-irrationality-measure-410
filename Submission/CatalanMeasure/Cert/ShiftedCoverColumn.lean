module
public import Submission.CatalanMeasure.Cert.ShiftedCoverRow
@[expose] public section
namespace CatalanMeasure.Cert
open OAI.InternalCatalan Set Filter
open scoped Topology
noncomputable section

noncomputable def shiftedColumnRegular (C : ColumnWeights) (Vc : List ℤ) (V : List TailQ)
    (x : ℝ) : ℝ :=2*barrierTrialT (trialSeq Vc V) x+(C.a:ℝ)*Real.log (1+x)

theorem shiftedColumnField_split (C : ColumnWeights) (Vc : List ℤ) (V : List TailQ) (x : ℝ) :
    shiftedColumnField C Vc V x=(C.b:ℝ)*Real.log x+(C.q:ℝ)*Real.log (1-x)+
      shiftedColumnRegular C Vc V x :=by
  unfold shiftedColumnField shiftedColumnRegular realEnergyColumnTrialField realEnergyColumnField
  push_cast
  ring

variable {C : ColumnWeights} {Vc : List ℤ} {V : List TailQ}
theorem shiftedColumnRegular_continuousOn (hV : tailsInDisk V=true) :
    ContinuousOn (shiftedColumnRegular C Vc V) (Icc (0:ℝ) 1) :=by
  have hT :=barrierTrialT_continuousOn (trialSeq Vc V) (trialSeq_summable (cs :=Vc) hV).1
  have ht : ContinuousOn (barrierTrialT (trialSeq Vc V)) (Icc (0:ℝ) 1) :=
    hT.mono (by intro x hx;exact ⟨by linarith [hx.1],hx.2⟩)
  have hl : ContinuousOn (fun x : ℝ =>Real.log (1+x)) (Icc (0:ℝ) 1) :=by
    apply (continuousOn_const.add continuousOn_id).log
    intro x hx
    change 1+x≠0
    exact ne_of_gt (by linarith [hx.1])
  exact (ht.const_mul 2).add (hl.const_mul _)

theorem shiftedColumnRegular_continuousAt_zero (hV : tailsInDisk V=true) :
    ContinuousAt (shiftedColumnRegular C Vc V) 0 :=by
  have ht :=continuousOn_continuousAt_zero
    (barrierTrialT_continuousOn (trialSeq Vc V) (trialSeq_summable (cs :=Vc) hV).1)
  have hl : ContinuousAt (fun x : ℝ =>Real.log (1+x)) 0 :=
    (continuousAt_const.add continuousAt_id).log (by norm_num)
  exact (ht.const_mul 2).add (hl.const_mul _)

theorem shiftedColumnRegular_tendsto_one_left (hV : tailsInDisk V=true) :
    Tendsto (shiftedColumnRegular C Vc V) (𝓝[<] 1) (𝓝 (shiftedColumnRegular C Vc V 1)) :=by
  have ht :=continuousOn_tendsto_one_left
    (barrierTrialT_continuousOn (trialSeq Vc V) (trialSeq_summable (cs :=Vc) hV).1)
  have hl : ContinuousAt (fun x : ℝ =>Real.log (1+x)) 1 :=
    (continuousAt_const.add continuousAt_id).log (by norm_num)
  exact (ht.const_mul 2).add ((hl.tendsto.mono_left nhdsWithin_le_nhds).const_mul _)

theorem shiftedColumnField_sup_of_cover (hV : tailsInDisk V=true)
    (hb : 0<C.b) (hq : 0<C.q) {M : ℝ} {S : Set ℝ}
    (hcover : ∀ x ∈ Ioo (0:ℝ) 1,deriv (shiftedColumnField C Vc V) x=0 → x ∈ S)
    (hvalues : ∀ x ∈ S,shiftedColumnField C Vc V x ≤ M) :
    ∀ x ∈ Ioo (0:ℝ) 1,shiftedColumnField C Vc V x ≤ M :=by
  have hcont : ContinuousOn (shiftedColumnField C Vc V) (Ioo (0:ℝ) 1) :=by
    intro x hx
    exact (shiftedColumnField_hasDerivAt hV hx).2.continuousAt.continuousWithinAt
  apply GlobalMaxReduction.le_on_Ioo_of_stationary_cover (S :=S) hcont
  · have hl :=Tendsto.const_mul_atBot (by exact_mod_cast hb : (0:ℝ)<C.b)
      Real.tendsto_log_nhdsGT_zero
    have hr : ContinuousAt (fun x : ℝ =>(C.q:ℝ)*Real.log (1-x)+
        shiftedColumnRegular C Vc V x) 0 :=by
      have hlog : ContinuousAt (fun x : ℝ =>Real.log (1-x)) 0 :=
        (continuousAt_const.sub continuousAt_id).log (by norm_num)
      exact (hlog.const_mul _).add (shiftedColumnRegular_continuousAt_zero (C :=C) (Vc :=Vc) (V :=V) hV)
    have hh :=atBot_add_finite hl (hr.tendsto.mono_left nhdsWithin_le_nhds)
    convert hh using 1
    funext x
    rw [shiftedColumnField_split]
    ring
  · have hl :=Tendsto.const_mul_atBot (by exact_mod_cast hq : (0:ℝ)<C.q) log_one_sub_tendsto
    have hlog :=(Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] (1:ℝ) ≤ 𝓝 1)
    have hr :=(hlog.const_mul (C.b:ℝ)).add (shiftedColumnRegular_tendsto_one_left (C :=C) (Vc :=Vc) (V :=V) hV)
    have hh :=atBot_add_finite hl hr
    convert hh using 1
    funext x
    rw [shiftedColumnField_split]
    ring
  · exact hcover
  · exact hvalues

end
end CatalanMeasure.Cert
