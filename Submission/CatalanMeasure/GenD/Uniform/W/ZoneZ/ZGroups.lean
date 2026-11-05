module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZVirt
@[expose] public section
set_option Elab.async false

/-!
# The condition groups as linear maps `ZPar → F^m`

Main zone (`h+hp` functionals `(v_2-v_1) . seq[r]`), window `s-1` (`π1[r]`, `eta < r < p`),
digit 0 (`eta+1-b` functionals), digit `s` (`min(max(g,rt),hp) - g` functionals).
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p hp : ℕ} [Fact p.Prime] {K : ℕ}

def mainM (P : Parameters) (N p hp K : ℕ) [Fact p.Prime] (u u2 y1 y2 : Fin K → ZMod p) :
    ZPar p hp →ₗ[ZMod p] (Fin (P.h N + hp) → ZMod p) :=
  LinearMap.pi fun r : Fin (P.h N + hp) =>
    dotL P N p hp (fun c => vv p K (P.H N) u u2 y1 y2 2 c - vv p K (P.H N) u u2 y1 y2 1 c) r

def wM (P : Parameters) (N p hp eta m : ℕ) [Fact p.Prime] :
    ZPar p hp →ₗ[ZMod p] (Fin m → ZMod p) :=
  LinearMap.pi fun j : Fin m => pi1L P N p hp (eta + 1 + j)

def d0M (P : Parameters) (N p hp K m : ℕ) [Fact p.Prime] (u u2 y1 y2 : Fin K → ZMod p) :
    ZPar p hp →ₗ[ZMod p] (Fin m → ZMod p) :=
  LinearMap.pi fun r : Fin m =>
    (fuV p K (P.H N) u 0 ((4 : ℕ) : ℤ) - 1) • foldL P N p hp r +
      dotL P N p hp (vv p K (P.H N) u u2 y1 y2 0) r

def dsM (P : Parameters) (N p hp K g m : ℕ) [Fact p.Prime] (u u2 y1 y2 : Fin K → ZMod p) :
    ZPar p hp →ₗ[ZMod p] (Fin m → ZMod p) :=
  LinearMap.pi fun j : Fin m => dotL P N p hp (vv p K (P.H N) u u2 y1 y2 4) (g + P.h N + j)

theorem mainM_apply (u u2 y1 y2 : Fin K → ZMod p) (a : ZPar p hp) (r : Fin (P.h N + hp)) :
    mainM P N p hp K u u2 y1 y2 a r =
      dotc (fun c => vv p K (P.H N) u u2 y1 y2 2 c - vv p K (P.H N) u u2 y1 y2 1 c)
        (piSeq P N p a.1) (piSeq P N p a.2.1) (laSeq P N p (Aext a.2.2.1))
        (laSeq P N p (Aext a.2.2.2)) p r := by
  simp [mainM, dotL_apply]

theorem wM_apply (eta m : ℕ) (a : ZPar p hp) (j : Fin m) :
    wM P N p hp eta m a j = piSeq P N p a.1 (eta + 1 + j) := by
  simp [wM, pi1L_apply]

theorem d0M_apply (m : ℕ) (u u2 y1 y2 : Fin K → ZMod p) (a : ZPar p hp) (r : Fin m) :
    d0M P N p hp K m u u2 y1 y2 a r =
      (fuV p K (P.H N) u 0 ((4 : ℕ) : ℤ) - 1) * (piSeq P N p a.1 r + piSeq P N p a.1 (r + p)) +
      dotc (vv p K (P.H N) u u2 y1 y2 0) (piSeq P N p a.1) (piSeq P N p a.2.1)
        (laSeq P N p (Aext a.2.2.1)) (laSeq P N p (Aext a.2.2.2)) p r := by
  simp [d0M, foldL_apply, dotL_apply]

theorem dsM_apply (g m : ℕ) (u u2 y1 y2 : Fin K → ZMod p) (a : ZPar p hp) (j : Fin m) :
    dsM P N p hp K g m u u2 y1 y2 a j =
      dotc (vv p K (P.H N) u u2 y1 y2 4) (piSeq P N p a.1) (piSeq P N p a.2.1)
        (laSeq P N p (Aext a.2.2.1)) (laSeq P N p (Aext a.2.2.2)) p (g + P.h N + j) := by
  simp [dsM, dotL_apply]

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
