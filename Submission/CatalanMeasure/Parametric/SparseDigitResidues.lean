module
public import Submission.CatalanMeasure.Parametric.SparseDigitConstants
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan
noncomputable section

def sparseDigitRationals (j : Fin 2) : Finset ℚ :=
  let k :=j.val+1
  {3/2,292/59,3281/177,momentRatSigned 0 k,momentRatSigned 1 k,
    momentRatSigned 2 k,momentRatSigned 3 k,
    zetaRat 1 k,zetaRat 2 k,zetaRat 3 k,
    momentRatSigned 1 k-momentRatSigned 3 k,
    momentRatSigned 0 k-momentRatSigned 2 k,
    3*zetaRat 1 k,(3/2)*zetaRat 2 k,(3/2)*zetaRat 3 k,
    2*(momentRatSigned 0 k-momentRatSigned 2 k),
    2*(momentRatSigned 0 k-momentRatSigned 2 k)-3*zetaRat 1 k,
    sparseDigitZero 2 k,sparseDigitOne 1 2 k,sparseDigitTwo 1 2 k,
    (292/59)*sparseDigitOne 1 2 k,(3281/177)*sparseDigitZero 2 k}

theorem sparseDigitRationals_den_bound (j : Fin 2) :
    ∀ q ∈ sparseDigitRationals j, q.den < 1000000 := by
  fin_cases j <;> decide +kernel

theorem rational_residue_den_of_bound {p : ℕ} [Fact p.Prime] (q : ℚ)
    (hq : q.den < p) : (q.den : ZMod p)≠0 := by
  intro hz
  exact (Nat.not_dvd_of_pos_of_lt q.pos hq) ((ZMod.natCast_eq_zero_iff q.den p).mp hz)

def sparseDigitZeroResidue (p j : ℕ) [Fact p.Prime] : ZMod p :=
  -(3/2:ZMod p)*palindromicRatResidue p (zetaRat 3 j)

def sparseDigitOneResidue (p j : ℕ) [Fact p.Prime] : ZMod p :=
  palindromicRatResidue p (momentRatSigned 1 j)-palindromicRatResidue p (momentRatSigned 3 j)-
    (3/2:ZMod p)*palindromicRatResidue p (zetaRat 2 j)

def sparseDigitTwoResidue (p j : ℕ) [Fact p.Prime] : ZMod p :=
  2*(palindromicRatResidue p (momentRatSigned 0 j)-palindromicRatResidue p (momentRatSigned 2 j))-
    3*palindromicRatResidue p (zetaRat 1 j)+(3/2:ZMod p)*palindromicRatResidue p (zetaRat 3 j)

theorem sparseDigit_identity_residue {p : ℕ} [hp : Fact p.Prime]
    (hlarge : 1000000 ≤ p) (j : Fin 2) :
    sparseDigitTwoResidue p (j.val+1)=
      (292/59:ZMod p)*sparseDigitOneResidue p (j.val+1)-
        (3281/177:ZMod p)*sparseDigitZeroResidue p (j.val+1) := by
  let k :=j.val+1
  let R : ℚ → ZMod p :=palindromicRatResidue p
  have hd (q : ℚ) (hq : q ∈ sparseDigitRationals j) : (q.den : ZMod p)≠0 :=
    rational_residue_den_of_bound q ((sparseDigitRationals_den_bound j q hq).trans_le hlarge)
  have hd32 :=hd (3/2) (by simp [sparseDigitRationals])
  have hda :=hd (292/59) (by simp [sparseDigitRationals])
  have hdb :=hd (3281/177) (by simp [sparseDigitRationals])
  have hm (v : Fin 4) : ((momentRatSigned (v.val:ℤ) k).den : ZMod p)≠0 := by
    fin_cases v <;> apply hd <;> simp [sparseDigitRationals,k]
  have hz (v : Fin 3) : ((zetaRat (v.val+1) k).den : ZMod p)≠0 := by
    fin_cases v <;> apply hd <;> simp [sparseDigitRationals,k]
  have hm0 : ((momentRatSigned 0 k).den : ZMod p)≠0 :=by simpa using hm 0
  have hm1 : ((momentRatSigned 1 k).den : ZMod p)≠0 :=by simpa using hm 1
  have hm2 : ((momentRatSigned 2 k).den : ZMod p)≠0 :=by simpa using hm 2
  have hm3 : ((momentRatSigned 3 k).den : ZMod p)≠0 :=by simpa using hm 3
  have hz1 : ((zetaRat 1 k).den : ZMod p)≠0 :=by simpa using hz 0
  have hz2 : ((zetaRat 2 k).den : ZMod p)≠0 :=by simpa using hz 1
  have hz3 : ((zetaRat 3 k).den : ZMod p)≠0 :=by simpa using hz 2
  have hnat (d : ℕ) (hd0 : 0<d) (hdlt : d<p) : (d:ZMod p)≠0 := by
    intro h
    exact (Nat.not_dvd_of_pos_of_lt hd0 hdlt) ((ZMod.natCast_eq_zero_iff d p).mp h)
  have h32 : R (3/2)= (3/2:ZMod p) := by
    exact (nat_fraction_reduced_residue 3 2 (hnat 2 (by decide) (by omega))).2
  have ha : R (292/59)= (292/59:ZMod p) := by
    exact (nat_fraction_reduced_residue 292 59 (hnat 59 (by decide) (by omega))).2
  have hb : R (3281/177)= (3281/177:ZMod p) := by
    exact (nat_fraction_reduced_residue 3281 177 (hnat 177 (by decide) (by omega))).2
  dsimp only [R] at h32 ha hb
  have hzero : R (sparseDigitZero 2 k)=sparseDigitZeroResidue p k := by
    dsimp only [R]
    have h :=palindromicRatResidue_sub (a:=0) (b:=(3/2)*zetaRat 3 k)
      (by simp) (rational_residue_mul hd32 hz3).1
    have he : sparseDigitZero 2 k=0-(3/2)*zetaRat 3 k :=by simp [sparseDigitZero]
    rw [he,h,palindromicRatResidue_mul hd32 hz3,h32]
    simp [R,sparseDigitZeroResidue,palindromicRatResidue]
  have hone : R (sparseDigitOne 1 2 k)=sparseDigitOneResidue p k := by
    dsimp only [R]
    have he : sparseDigitOne 1 2 k=
      (momentRatSigned 1 k-momentRatSigned 3 k)-(3/2)*zetaRat 2 k :=by
        simp [sparseDigitOne]
    rw [he,palindromicRatResidue_sub (rational_residue_sub hm1 hm3).1
      (rational_residue_mul hd32 hz2).1,
      palindromicRatResidue_sub hm1 hm3,palindromicRatResidue_mul hd32 hz2,h32]
    rfl
  have htwo : R (sparseDigitTwo 1 2 k)=sparseDigitTwoResidue p k := by
    dsimp only [R]
    have he : sparseDigitTwo 1 2 k=
      (2*(momentRatSigned 0 k-momentRatSigned 2 k)-3*zetaRat 1 k)+(3/2)*zetaRat 3 k :=by
        simp [sparseDigitTwo]
    rw [he,palindromicRatResidue_add
      (rational_residue_sub (rational_residue_mul (a:=2) (by simp)
        (rational_residue_sub hm0 hm2).1).1
        (rational_residue_mul (a:=3) (by simp) hz1).1).1
      (rational_residue_mul hd32 hz3).1,
      palindromicRatResidue_sub (rational_residue_mul (a:=2) (by simp)
        (rational_residue_sub hm0 hm2).1).1
        (rational_residue_mul (a:=3) (by simp) hz1).1,
      palindromicRatResidue_mul (a:=2) (by simp) (rational_residue_sub hm0 hm2).1,
      palindromicRatResidue_sub hm0 hm2,
      palindromicRatResidue_mul (a:=3) (by simp) hz1,
      palindromicRatResidue_mul hd32 hz3,h32]
    simp [R,palindromicRatResidue,sparseDigitTwoResidue]
  have h :=congrArg R (sparseDigit_identity_pos j)
  change R (sparseDigitTwo 1 2 k)=R ((292/59)*sparseDigitOne 1 2 k-(3281/177)*sparseDigitZero 2 k) at h
  dsimp only [R] at h hzero hone htwo
  have hdz :=hd (sparseDigitZero 2 k) (by simp [sparseDigitRationals,k])
  have hdo :=hd (sparseDigitOne 1 2 k) (by simp [sparseDigitRationals,k])
  rw [palindromicRatResidue_sub
    (rational_residue_mul hda hdo).1 (rational_residue_mul hdb hdz).1,
    palindromicRatResidue_mul hda hdo,palindromicRatResidue_mul hdb hdz,
    htwo,hone,hzero,ha,hb] at h
  exact h

end
end CatalanMeasure.Parametric
