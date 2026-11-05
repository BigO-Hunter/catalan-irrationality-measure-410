module
public import Submission.CatalanMeasure.Cert.ShiftedFields
public import Submission.CatalanMeasure.Cert.FieldDeriv
@[expose] public section
namespace CatalanMeasure.Cert
open OAI.InternalCatalan Set
noncomputable section

def shiftedRowFracs (R : RowWeights) (Pc Vc : List ℤ) (P V : List TailQ) :
    List (List ℚ × List ℚ) :=
  [fracSum (rowFracs Pc Vc P V),([R.alpha-19/48],[0,1]),
    ([-(R.beta-1/12)],[1,-1]),([0,-2*(R.gamma-65/48)],[1,0,1]),
    ([0,-4*R.lam],[1,0,2,0,1])]

def shiftedColumnFracs (C : ColumnWeights) (Vc : List ℤ) (V : List TailQ) :
    List (List ℚ × List ℚ) :=
  [fracSum (colFracs Vc V),([C.b-7/48],[0,1]),
    ([-(C.q-1/12)],[1,-1]),([C.a],[1,1])]

theorem shiftedRowField_hasDerivAt {R : RowWeights} {Pc Vc : List ℤ} {P V : List TailQ}
    (hP : tailsInDisk P=true) (hV : tailsInDisk V=true)
    {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) (hx0 : x≠0) :
    lpEval (fracSum (shiftedRowFracs R Pc Vc P V)).2 x≠0 ∧
    HasDerivAt (shiftedRowField R Pc Vc P V)
      (lpEval (fracSum (shiftedRowFracs R Pc Vc P V)).1 x /
        lpEval (fracSum (shiftedRowFracs R Pc Vc P V)).2 x) x :=by
  obtain ⟨hbase,hder⟩ :=rowField_hasDerivAt hP hV hx hx0
  have hd : 1+x^2≠0 :=by positivity
  have h1 : 1-x≠0 :=(sub_pos.mpr hx.2).ne'
  have hden : ∀ f ∈ shiftedRowFracs R Pc Vc P V,lpEval f.2 x≠0 :=by
    intro f hf
    simp only [shiftedRowFracs,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    · exact hbase
    · simpa [lpEval] using hx0
    · simpa [lpEval,sub_eq_add_neg] using h1
    · simpa [lpEval,pow_two] using hd
    · have hh : (1+x^2)^2≠0 :=pow_ne_zero 2 hd
      convert hh using 1 <;> simp [lpEval] <;> ring
  obtain ⟨hQ,hAQ⟩ :=fracSum_spec _ x hden
  refine ⟨hQ,?_⟩
  rw [hAQ]
  have hl0 : HasDerivAt (fun y : ℝ =>Real.log |y|) (1/x) x :=by
    simpa only [Real.log_abs,one_div] using Real.hasDerivAt_log hx0
  have hl1 : HasDerivAt (fun y : ℝ =>Real.log (1-y)) (-1/(1-x)) x :=
    ((hasDerivAt_id x).const_sub (1:ℝ)).log h1
  have hp : HasDerivAt (fun y : ℝ =>1+y^2) (2*x) x :=by
    simpa using (hasDerivAt_pow 2 x).const_add (1:ℝ)
  have hnum : HasDerivAt (fun y : ℝ =>2*y^2) (4*x) x :=by
    convert (hasDerivAt_pow 2 x).const_mul (2:ℝ) using 1 <;> ring
  have hD : HasDerivAt (fun y : ℝ =>(R.d0:ℝ)-2*y^2/(1+y^2))
      (-4*x/(1+x^2)^2) x :=by
    convert ((hnum.div hp hd).const_sub (R.d0:ℝ)) using 1 <;> field_simp <;> ring
  have hall :=(((hder.add (hl0.const_mul ((R.alpha-19/48:ℚ):ℝ))).add
    (hl1.const_mul ((R.beta-1/12:ℚ):ℝ))).sub
    ((hp.log hd).const_mul ((R.gamma-65/48:ℚ):ℝ))).add (hD.const_mul (R.lam:ℝ))
  unfold shiftedRowField
  refine hall.congr_deriv ?_
  simp only [shiftedRowFracs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    lpEval_cons,lpEval_nil]
  push_cast
  have he : 1+x*(0+x*(2+x*(0+x*(1+x*0))))=(1+x^2)^2 :=by ring
  rw [he]
  ring

theorem shiftedColumnField_hasDerivAt {C : ColumnWeights} {Vc : List ℤ} {V : List TailQ}
    (hV : tailsInDisk V=true) {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) :
    lpEval (fracSum (shiftedColumnFracs C Vc V)).2 x≠0 ∧
    HasDerivAt (shiftedColumnField C Vc V)
      (lpEval (fracSum (shiftedColumnFracs C Vc V)).1 x /
        lpEval (fracSum (shiftedColumnFracs C Vc V)).2 x) x :=by
  obtain ⟨hbase,hder⟩ :=colField_hasDerivAt hV hx
  have hx0 : x≠0 :=hx.1.ne'
  have h1 : 1-x≠0 :=(sub_pos.mpr hx.2).ne'
  have hp : 1+x≠0 :=ne_of_gt (by linarith [hx.1])
  have hden : ∀ f ∈ shiftedColumnFracs C Vc V,lpEval f.2 x≠0 :=by
    intro f hf
    simp only [shiftedColumnFracs,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl
    · exact hbase
    · simpa [lpEval] using hx0
    · simpa [lpEval,sub_eq_add_neg] using h1
    · simpa [lpEval] using hp
  obtain ⟨hQ,hAQ⟩ :=fracSum_spec _ x hden
  refine ⟨hQ,?_⟩
  rw [hAQ]
  have hl0 : HasDerivAt Real.log (1/x) x :=by
    simpa only [one_div] using Real.hasDerivAt_log hx0
  have hl1 : HasDerivAt (fun y : ℝ =>Real.log (1-y)) (-1/(1-x)) x :=
    ((hasDerivAt_id x).const_sub (1:ℝ)).log h1
  have hlp : HasDerivAt (fun y : ℝ =>Real.log (1+y)) (1/(1+x)) x :=by
    simpa using ((hasDerivAt_id x).const_add (1:ℝ)).log hp
  have hall :=((hder.add (hl0.const_mul ((C.b-7/48:ℚ):ℝ))).add
    (hl1.const_mul ((C.q-1/12:ℚ):ℝ))).add (hlp.const_mul (C.a:ℝ))
  unfold shiftedColumnField
  refine hall.congr_deriv ?_
  simp only [shiftedColumnFracs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    lpEval_cons,lpEval_nil]
  push_cast
  ring

end
end CatalanMeasure.Cert
