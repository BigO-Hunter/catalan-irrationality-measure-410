module
public import Submission.CatalanMeasure.GenD.RankSeq
public import Submission.CatalanMeasure.GenD.RankBlock
@[expose] public section

/-!
# Coefficient functionals of `Qh` and `Dh` (GenD)
-/

namespace CatalanMeasure.GenD
open Polynomial OAI.InternalCatalan CatalanMeasure.Parametric
noncomputable section

section
variable {P : Parameters} {N p : ℕ} [hp : Fact p.Prime]

/-- `c ↦ Qh_c` as a linear map. -/
def qhLin (P : Parameters) (N p : ℕ) [Fact p.Prime] :
    (Fin (P.n N) → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
  (LinearMap.mulLeft (ZMod p)
    ((X - 1 : (ZMod p)[X]) ^ P.q N * (X * oddPrimeWeight p * (1 - X) ^ P.h N))).comp
    (uS p (P.C N) (P.g N) (P.n N))

/-- `c ↦ Dh_c` as a linear map. -/
def dhLin (P : Parameters) (N p : ℕ) [Fact p.Prime] :
    (Fin (P.n N) → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
  (LinearMap.mulLeft (ZMod p) ((X - 1 : (ZMod p)[X]) ^ P.q N * (1 - X) ^ P.h N)).comp
    (uU p (P.C N) (P.g N) (P.n N))

theorem qhLin_apply (c : Fin (P.n N) → ZMod p) : qhLin P N p c = qhP P N p c := by
  simp only [qhLin, qhP, fP, LinearMap.comp_apply, LinearMap.mulLeft_apply]; ring

theorem dhLin_apply (c : Fin (P.n N) → ZMod p) : dhLin P N p c = dhP P N p c := by
  simp only [dhLin, dhP, gP, LinearMap.comp_apply, LinearMap.mulLeft_apply]; ring

/-- Coefficient `i` of `Qh_c`. -/
def coeffQ (P : Parameters) (N p i : ℕ) [Fact p.Prime] :
    (Fin (P.n N) → ZMod p) →ₗ[ZMod p] ZMod p := (lcoeff (ZMod p) i).comp (qhLin P N p)

/-- Coefficient `i` of `Dh_c`. -/
def coeffD (P : Parameters) (N p i : ℕ) [Fact p.Prime] :
    (Fin (P.n N) → ZMod p) →ₗ[ZMod p] ZMod p := (lcoeff (ZMod p) i).comp (dhLin P N p)

theorem coeffQ_apply (i : ℕ) (c : Fin (P.n N) → ZMod p) :
    coeffQ P N p i c = (qhP P N p c).coeff i := by
  simp [coeffQ, qhLin_apply]

theorem coeffD_apply (i : ℕ) (c : Fin (P.n N) → ZMod p) :
    coeffD P N p i c = (dhP P N p c).coeff i := by
  simp [coeffD, dhLin_apply]

end
end
end CatalanMeasure.GenD
