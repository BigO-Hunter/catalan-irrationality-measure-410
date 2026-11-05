module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZCap3
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZGroups
@[expose] public section
set_option Elab.async false

/-!
# Condition groups of the cap window as linear maps
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p hp : ℕ} [Fact p.Prime] {K : ℕ}

/-- Unshifted coefficient sequences as linear maps. -/
def seqL0 (P : Parameters) (N p hp : ℕ) [Fact p.Prime] (c : ℕ) (r : ℕ) :
    ZPar p hp →ₗ[ZMod p] ZMod p :=
  match c with
  | 0 => (piLin P N p r).comp (LinearMap.fst _ _ _)
  | 1 => (piLin P N p r).comp ((LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _))
  | 2 => (laLin P N p r).comp ((AextL p hp).comp ((LinearMap.fst _ _ _).comp
      ((LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _))))
  | 3 => (laLin P N p r).comp ((AextL p hp).comp ((LinearMap.snd _ _ _).comp
      ((LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _))))
  | _ => 0

def dotL0 (P : Parameters) (N p hp : ℕ) [Fact p.Prime] (v : ℕ → ZMod p) (r : ℕ) :
    ZPar p hp →ₗ[ZMod p] ZMod p :=
  ∑ c ∈ Finset.range 4, v c • seqL0 P N p hp c r

theorem dotL0_apply (v : ℕ → ZMod p) (r : ℕ) (a : ZPar p hp) :
    dotL0 P N p hp v r a = dotc v (piSeq P N p a.1) (piSeq P N p a.2.1)
      (laSeq P N p (Aext a.2.2.1)) (laSeq P N p (Aext a.2.2.2)) 0 r := by
  simp only [dotL0, dotc, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun c hc => ?_
  have : c < 4 := Finset.mem_range.mp hc
  interval_cases c <;> simp [seqL0, seqc, piLin_apply, laLin_apply, AextL_apply]

/-- Offset versions of the window-`s` groups. -/
def mainMo (P : Parameters) (N p hp K off m : ℕ) [Fact p.Prime] (u u2 y1 y2 : Fin K → ZMod p) :
    ZPar p hp →ₗ[ZMod p] (Fin m → ZMod p) :=
  LinearMap.pi fun j : Fin m =>
    dotL P N p hp (fun c => vv p K (P.H N) u u2 y1 y2 2 c - vv p K (P.H N) u u2 y1 y2 1 c) (off + j)

def dsMo (P : Parameters) (N p hp K off m : ℕ) [Fact p.Prime] (u u2 y1 y2 : Fin K → ZMod p) :
    ZPar p hp →ₗ[ZMod p] (Fin m → ZMod p) :=
  LinearMap.pi fun j : Fin m => dotL P N p hp (vv p K (P.H N) u u2 y1 y2 4) (off + j)

def d0Mo (P : Parameters) (N p hp K off m : ℕ) [Fact p.Prime] (u u2 y1 y2 : Fin K → ZMod p) :
    ZPar p hp →ₗ[ZMod p] (Fin m → ZMod p) :=
  LinearMap.pi fun r : Fin m =>
    (fuV p K (P.H N) u 0 ((4 : ℕ) : ℤ) - 1) • foldL P N p hp (off + r) +
      dotL P N p hp (vv p K (P.H N) u u2 y1 y2 0) (off + r)

/-- Window `s+1` zone: `Y`, `C1` (`z_J . seq'`), `C0`. -/
def zM (P : Parameters) (N p hp K m J : ℕ) [Fact p.Prime] (u u2 y1 y2 : Fin K → ZMod p) :
    ZPar p hp →ₗ[ZMod p] (Fin m → ZMod p) :=
  LinearMap.pi fun r : Fin m => dotL0 P N p hp (zz p K (P.H N) u u2 y1 y2 J) r

def c0M (P : Parameters) (N p hp K m : ℕ) [Fact p.Prime] (u u2 y1 y2 : Fin K → ZMod p) :
    ZPar p hp →ₗ[ZMod p] (Fin m → ZMod p) :=
  LinearMap.pi fun r : Fin m =>
    (fuV p K (P.H N) u 0 ((4 : ℕ) : ℤ) - 1) • foldL P N p hp r +
      dotL0 P N p hp (zz p K (P.H N) u u2 y1 y2 0) r

theorem mainMo_apply (off m : ℕ) (u u2 y1 y2 : Fin K → ZMod p) (a : ZPar p hp) (j : Fin m) :
    mainMo P N p hp K off m u u2 y1 y2 a j =
      dotc (fun c => vv p K (P.H N) u u2 y1 y2 2 c - vv p K (P.H N) u u2 y1 y2 1 c)
        (piSeq P N p a.1) (piSeq P N p a.2.1) (laSeq P N p (Aext a.2.2.1))
        (laSeq P N p (Aext a.2.2.2)) p (off + j) := by
  simp [mainMo, dotL_apply]

theorem dsMo_apply (off m : ℕ) (u u2 y1 y2 : Fin K → ZMod p) (a : ZPar p hp) (j : Fin m) :
    dsMo P N p hp K off m u u2 y1 y2 a j =
      dotc (vv p K (P.H N) u u2 y1 y2 4) (piSeq P N p a.1) (piSeq P N p a.2.1)
        (laSeq P N p (Aext a.2.2.1)) (laSeq P N p (Aext a.2.2.2)) p (off + j) := by
  simp [dsMo, dotL_apply]

theorem d0Mo_apply (off m : ℕ) (u u2 y1 y2 : Fin K → ZMod p) (a : ZPar p hp) (r : Fin m) :
    d0Mo P N p hp K off m u u2 y1 y2 a r =
      (fuV p K (P.H N) u 0 ((4 : ℕ) : ℤ) - 1) *
          (piSeq P N p a.1 (off + r) + piSeq P N p a.1 (off + r + p)) +
        dotc (vv p K (P.H N) u u2 y1 y2 0) (piSeq P N p a.1) (piSeq P N p a.2.1)
          (laSeq P N p (Aext a.2.2.1)) (laSeq P N p (Aext a.2.2.2)) p (off + r) := by
  simp [d0Mo, foldL_apply, dotL_apply]

theorem zM_apply (m J : ℕ) (u u2 y1 y2 : Fin K → ZMod p) (a : ZPar p hp) (r : Fin m) :
    zM P N p hp K m J u u2 y1 y2 a r =
      dotc (zz p K (P.H N) u u2 y1 y2 J) (piSeq P N p a.1) (piSeq P N p a.2.1)
        (laSeq P N p (Aext a.2.2.1)) (laSeq P N p (Aext a.2.2.2)) 0 r := by
  simp [zM, dotL0_apply]

theorem c0M_apply (m : ℕ) (u u2 y1 y2 : Fin K → ZMod p) (a : ZPar p hp) (r : Fin m) :
    c0M P N p hp K m u u2 y1 y2 a r =
      (fuV p K (P.H N) u 0 ((4 : ℕ) : ℤ) - 1) * (piSeq P N p a.1 r + piSeq P N p a.1 (r + p)) +
        dotc (zz p K (P.H N) u u2 y1 y2 0) (piSeq P N p a.1) (piSeq P N p a.2.1)
          (laSeq P N p (Aext a.2.2.1)) (laSeq P N p (Aext a.2.2.2)) 0 r := by
  simp [c0M, foldL_apply, dotL0_apply]

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
