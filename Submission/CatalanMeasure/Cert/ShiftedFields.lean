module
public import Submission.CatalanMeasure.Cert.Cover
@[expose] public section
namespace CatalanMeasure.Cert
open OAI.InternalCatalan Set
noncomputable section

structure RowWeights where
  alpha : ℚ
  beta : ℚ
  gamma : ℚ
  lam : ℚ
  d0 : ℚ
  deriving DecidableEq

structure ColumnWeights where
  b : ℚ
  q : ℚ
  a : ℚ
  deriving DecidableEq

def shiftedRowField (R : RowWeights) (Pc Vc : List ℤ) (P V : List TailQ) (x : ℝ) : ℝ :=
  realEnergyRowTrialField 2 0 (trialSeq Pc P) (trialSeq Vc V) x+
    ((R.alpha-19/48:ℚ):ℝ)*Real.log |x|+((R.beta-1/12:ℚ):ℝ)*Real.log (1-x)-
    ((R.gamma-65/48:ℚ):ℝ)*Real.log (1+x^2)+(R.lam:ℝ)*((R.d0:ℝ)-2*x^2/(1+x^2))

def shiftedColumnField (C : ColumnWeights) (Vc : List ℤ) (V : List TailQ) (s : ℝ) : ℝ :=
  realEnergyColumnTrialField (trialSeq Vc V) s+
    ((C.b-7/48:ℚ):ℝ)*Real.log s+((C.q-1/12:ℚ):ℝ)*Real.log (1-s)+(C.a:ℝ)*Real.log (1+s)

def shiftedRowTerms (R : RowWeights) (P V : List TailQ) (x : ℚ) : List LogTerm :=
  rowTerms P V x++[⟨R.alpha-19/48,0,x,0⟩,⟨R.beta-1/12,0,1-x,0⟩,
    ⟨-(R.gamma-65/48),0,1+x*x,0⟩]

def shiftedRowRat (R : RowWeights) (Pc Vc : List ℤ) (x : ℚ) : ℚ :=
  rowRat Pc Vc x+R.lam*(R.d0-2*x*x/(1+x*x))

def shiftedColumnTerms (C : ColumnWeights) (V : List TailQ) (s : ℚ) : List LogTerm :=
  colTerms V s++[⟨C.b-7/48,0,s,0⟩,⟨C.q-1/12,0,1-s,0⟩,⟨C.a,0,1+s,0⟩]

theorem shiftedRowField_eq (R : RowWeights) (Pc Vc : List ℤ) (P V : List TailQ)
    (hP : tailsInDisk P=true) (hV : tailsInDisk V=true) {x : ℚ}
    (hx : |(x:ℝ)| ≤ 1) (hx0 : (x:ℝ)≠0) (hx1 : (x:ℝ)≠1) :
    shiftedRowField R Pc Vc P V x=
      ((shiftedRowTerms R P V x).map LogTerm.val).sum+(shiftedRowRat R Pc Vc x:ℝ) :=by
  have h1 : ((1-x:ℚ):ℝ)≠0 :=by push_cast;exact sub_ne_zero.mpr hx1.symm
  have hd : ((1+x*x:ℚ):ℝ)≠0 :=by
    push_cast
    exact ne_of_gt (by nlinarith [mul_self_nonneg (x:ℝ)] : (0:ℝ)<1+(x:ℝ)*x)
  unfold shiftedRowField
  rw [rowField_eq Pc Vc P V hP hV hx hx0 hx1]
  simp only [shiftedRowTerms,List.map_append,List.sum_append,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil]
  rw [realLogTerm _ _ hx0,realLogTerm _ _ h1,realLogTerm _ _ hd]
  unfold shiftedRowRat
  push_cast
  have hxlt : (x:ℝ)<1 :=lt_of_le_of_ne (abs_le.mp hx).2 hx1
  rw [abs_of_pos (by linarith : (0:ℝ)<1-x),abs_of_pos (by nlinarith [mul_self_nonneg (x:ℝ)] : (0:ℝ)<1+(x:ℝ)*x)]
  simp only [pow_two]
  ring

theorem shiftedColumnField_eq (C : ColumnWeights) (Vc : List ℤ) (V : List TailQ)
    (hV : tailsInDisk V=true) {s : ℚ} (hs : (s:ℝ) ∈ Ioo (0:ℝ) 1) :
    shiftedColumnField C Vc V s=
      ((shiftedColumnTerms C V s).map LogTerm.val).sum+(colRat Vc s:ℝ) :=by
  have h0 : (s:ℝ)≠0 :=hs.1.ne'
  have h1 : ((1-s:ℚ):ℝ)≠0 :=by push_cast;exact (sub_pos.mpr hs.2).ne'
  have hp : ((1+s:ℚ):ℝ)≠0 :=by
    push_cast
    exact ne_of_gt (by linarith [hs.1] : (0:ℝ)<1+s)
  unfold shiftedColumnField
  rw [colField_eq Vc V hV hs]
  simp only [shiftedColumnTerms,List.map_append,List.sum_append,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil]
  rw [realLogTerm _ _ h0,realLogTerm _ _ h1,realLogTerm _ _ hp]
  push_cast
  rw [abs_of_pos hs.1,abs_of_pos (sub_pos.mpr hs.2),abs_of_pos (by linarith [hs.1] : (0:ℝ)<1+s)]
  ring

def shiftedRowApprox (R : RowWeights) (Pc Vc : List ℤ) (P V : List TailQ) (x : ℚ) : Option (ℚ×ℚ) :=
  (sumLogs (shiftedRowTerms R P V x)).map (fun ve =>(ve.1+shiftedRowRat R Pc Vc x,ve.2))

def shiftedColumnApprox (C : ColumnWeights) (Vc : List ℤ) (V : List TailQ) (s : ℚ) : Option (ℚ×ℚ) :=
  (sumLogs (shiftedColumnTerms C V s)).map (fun ve =>(ve.1+colRat Vc s,ve.2))

theorem shiftedRowApprox_spec {R : RowWeights} {Pc Vc : List ℤ} {P V : List TailQ}
    (hP : tailsInDisk P=true) (hV : tailsInDisk V=true) {x v e : ℚ}
    (h : shiftedRowApprox R Pc Vc P V x=some (v,e))
    (hx : |(x:ℝ)| ≤ 1) (hx0 : (x:ℝ)≠0) (hx1 : (x:ℝ)≠1) :
    shiftedRowField R Pc Vc P V x ≤ (v:ℝ)+(e:ℝ) :=by
  unfold shiftedRowApprox at h
  simp only [Option.map_eq_some_iff,Prod.mk.injEq] at h
  obtain ⟨⟨v',e'⟩,h1,rfl,rfl⟩ :=h
  have hh :=sumLogs_spec h1
  rw [shiftedRowField_eq R Pc Vc P V hP hV hx hx0 hx1]
  push_cast
  linarith [(abs_le.mp hh).2]

theorem shiftedColumnApprox_spec {C : ColumnWeights} {Vc : List ℤ} {V : List TailQ}
    (hV : tailsInDisk V=true) {s v e : ℚ}
    (h : shiftedColumnApprox C Vc V s=some (v,e)) (hs : (s:ℝ) ∈ Ioo (0:ℝ) 1) :
    shiftedColumnField C Vc V s ≤ (v:ℝ)+(e:ℝ) :=by
  unfold shiftedColumnApprox at h
  simp only [Option.map_eq_some_iff,Prod.mk.injEq] at h
  obtain ⟨⟨v',e'⟩,h1,rfl,rfl⟩ :=h
  have hh :=sumLogs_spec h1
  rw [shiftedColumnField_eq C Vc V hV hs]
  push_cast
  linarith [(abs_le.mp hh).2]

end
end CatalanMeasure.Cert
