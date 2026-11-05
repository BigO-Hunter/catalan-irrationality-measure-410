module
public import Submission.CatalanMeasure.Cert.FlexibleCover
@[expose] public section

open Set
namespace CatalanMeasure.Cert

def integerGapOK (Z : List ℤ) (p : Piece) : Bool :=
  p.2.2 || ipNoRootCheck Z (p.1.num * (p.2.1.den : ℤ))
    (p.2.1.num * (p.1.den : ℤ)) ((p.1.den : ℤ) * (p.2.1.den : ℤ))

theorem rational_cross_endpoint (a b : ℚ) :
    ((a.num * (b.den : ℤ) : ℤ) : ℝ) / (((a.den : ℤ) * (b.den : ℤ) : ℤ) : ℝ) = a := by
  have ha : (a.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr a.den_nz
  have hb : (b.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr b.den_nz
  simp only [Int.cast_mul, Int.cast_natCast]
  rw [Rat.cast_def]
  field_simp

theorem integerGaps_spec {A : List ℚ} {Z : List ℤ} {c : ℚ} {ps : List Piece}
    (hc : c ≠ 0) (heq : A = lpSmul c (Z.map (fun (z : ℤ) => (z : ℚ))))
    (hg : ps.all (integerGapOK Z) = true) : NoRootGaps A ps := by
  intro p hp hk x hx
  have h := List.all_eq_true.mp hg p hp
  simp only [integerGapOK, hk, Bool.false_or] at h
  have hb : ((p.2.1.num * (p.1.den : ℤ) : ℤ) : ℝ) /
      (((p.1.den : ℤ) * (p.2.1.den : ℤ) : ℤ) : ℝ) = p.2.1 := by
    rw [mul_comm (p.1.den : ℤ)]
    exact rational_cross_endpoint p.2.1 p.1
  have hx' : x ∈ Ioo
      (((p.1.num * (p.2.1.den : ℤ) : ℤ) : ℝ) /
        (((p.1.den : ℤ) * (p.2.1.den : ℤ) : ℤ) : ℝ))
      (((p.2.1.num * (p.1.den : ℤ) : ℤ) : ℝ) /
        (((p.1.den : ℤ) * (p.2.1.den : ℤ) : ℤ) : ℝ)) := by
    rw [rational_cross_endpoint p.1 p.2.1, hb]
    exact hx
  have hn := ipEval_ne_zero_of_noRootCheck h hx'
  rw [heq, lpEval_smul, lpEval_int_cast]
  exact mul_ne_zero (by exact_mod_cast hc) hn

end CatalanMeasure.Cert
