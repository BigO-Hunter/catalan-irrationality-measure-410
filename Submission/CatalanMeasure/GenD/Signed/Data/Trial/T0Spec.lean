module

public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T0Data

/-! Trial 0: the data checks of `TrialForm.Spec` (tails, η, positivity and density caps of the species) and the mass. -/

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Trial.T0
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
open CatalanMeasure.Cert (TailQ)

set_option maxRecDepth 1000000
set_option Elab.async false

theorem pcT0_ok : PieceOK pcT0.toPiece :=
  pieceOK_of pcT0 (qlist (raw_ints% [])) (by decide +kernel) (by decide +kernel)

theorem pcT1_ok : PieceOK pcT1.toPiece :=
  pieceOK_of pcT1 (qlist (raw_ints% [409, 131072])) (by decide +kernel) (by decide +kernel)

theorem pcT2_ok : PieceOK pcT2.toPiece :=
  pieceOK_of pcT2 (qlist (raw_ints% [])) (by decide +kernel) (by decide +kernel)

theorem pcT3_ok : PieceOK pcT3.toPiece :=
  pieceOK_of pcT3 (qlist (raw_ints% [])) (by decide +kernel) (by decide +kernel)

theorem pcT4_ok : PieceOK pcT4.toPiece :=
  pieceOK_of pcT4 (qlist (raw_ints% [])) (by decide +kernel) (by decide +kernel)

theorem pcT5_ok : PieceOK pcT5.toPiece :=
  pieceOK_of pcT5 (qlist (raw_ints% [4055, 65536])) (by decide +kernel) (by decide +kernel)

theorem pcT6_ok : PieceOK pcT6.toPiece :=
  pieceOK_of pcT6 (qlist (raw_ints% [77833, 262144, 69635, 131072, 200707, 262144])) (by decide +kernel) (by decide +kernel)

theorem pcF0_ok : PieceOK pcF0.toPiece :=
  pieceOK_of pcF0 (qlist (raw_ints% [])) (by decide +kernel) (by decide +kernel)

theorem pcF1_ok : PieceOK pcF1.toPiece :=
  pieceOK_of pcF1 (qlist (raw_ints% [])) (by decide +kernel) (by decide +kernel)

theorem pcF2_ok : PieceOK pcF2.toPiece :=
  pieceOK_of pcF2 (qlist (raw_ints% [3093, 131072])) (by decide +kernel) (by decide +kernel)

theorem pcF3_ok : PieceOK pcF3.toPiece :=
  pieceOK_of pcF3 (qlist (raw_ints% [])) (by decide +kernel) (by decide +kernel)

theorem pcF4_ok : PieceOK pcF4.toPiece :=
  pieceOK_of pcF4 (qlist (raw_ints% [9257, 131072])) (by decide +kernel) (by decide +kernel)

theorem pcF5_ok : PieceOK pcF5.toPiece :=
  pieceOK_of pcF5 (qlist (raw_ints% [1097, 2048, 3145, 4096])) (by decide +kernel) (by decide +kernel)

theorem pcTn0_ok : PieceOK pcTn0.toPiece :=
  pieceOK_of pcTn0 (qlist (raw_ints% [])) (by decide +kernel) (by decide +kernel)

theorem pcTn1_ok : PieceOK pcTn1.toPiece :=
  pieceOK_of pcTn1 (qlist (raw_ints% [])) (by decide +kernel) (by decide +kernel)

theorem pcTn2_ok : PieceOK pcTn2.toPiece :=
  pieceOK_of pcTn2 (qlist (raw_ints% [])) (by decide +kernel) (by decide +kernel)

theorem pcFn0_ok : PieceOK pcFn0.toPiece :=
  pieceOK_of pcFn0 (qlist (raw_ints% [])) (by decide +kernel) (by decide +kernel)

theorem pcFn1_ok : PieceOK pcFn1.toPiece :=
  pieceOK_of pcFn1 (qlist (raw_ints% [])) (by decide +kernel) (by decide +kernel)

theorem pcFn2_ok : PieceOK pcFn2.toPiece :=
  pieceOK_of pcFn2 (qlist (raw_ints% [])) (by decide +kernel) (by decide +kernel)

def capsT : List (ℚ × List ℚ) := [(((1 : ℚ) / 32), qlist (raw_ints% [])), (((1 : ℚ) / 32), qlist (raw_ints% [])), (((1 : ℚ) / 32), qlist (raw_ints% [])), (((1 : ℚ) / 32), qlist (raw_ints% [])), (((1 : ℚ) / 32), qlist (raw_ints% [])), (((1 : ℚ) / 32), qlist (raw_ints% [])), (((53 : ℚ) / 32), qlist (raw_ints% [69635, 131072, 200707, 262144, 462851, 524288, 987139, 1048576]))]

def capsF : List (ℚ × List ℚ) := [(((1 : ℚ) / 32), qlist (raw_ints% [])), (((5 : ℚ) / 64), qlist (raw_ints% [])), (((1 : ℚ) / 32), qlist (raw_ints% [])), (((3 : ℚ) / 64), qlist (raw_ints% [])), (((1 : ℚ) / 32), qlist (raw_ints% [])), (((35 : ℚ) / 64), qlist (raw_ints% [1243, 4096, 1097, 2048, 3145, 4096]))]

def capsTn : List (ℚ × List ℚ) := [(((1 : ℚ) / 32), qlist (raw_ints% [])), (((1 : ℚ) / 32), qlist (raw_ints% [])), (((1 : ℚ) / 32), qlist (raw_ints% []))]

def capsFn : List (ℚ × List ℚ) := [(((1 : ℚ) / 32), qlist (raw_ints% [])), (((1 : ℚ) / 32), qlist (raw_ints% [])), (((1 : ℚ) / 32), qlist (raw_ints% []))]

theorem capsT_ok : capsOK trial.qT capsT = true := by decide +kernel

theorem capsF_ok : capsOK trial.qF capsF = true := by decide +kernel

theorem capsTn_ok : capsOK trial.qTn capsTn = true := by decide +kernel

theorem capsFn_ok : capsOK trial.qFn capsFn = true := by decide +kernel

/-- The density cap `Cb` of the trial (`BD (μ b) Cb` for both species). -/
def Cb : ℚ := ((59 : ℚ) / 32)

theorem capsT_le : (capsT.map Prod.fst).sum ≤ Cb := by decide +kernel

theorem capsF_le : (capsF.map Prod.fst).sum ≤ Cb := by decide +kernel

theorem capsTn_le : (capsTn.map Prod.fst).sum ≤ Cb := by decide +kernel

theorem capsFn_le : (capsFn.map Prod.fst).sum ≤ Cb := by decide +kernel

theorem dataOK {C : ℝ} (hC : ((Cb : ℚ) : ℝ) ≤ C) : trial.DataOK C where
  hvT := by decide +kernel
  haT := by decide +kernel
  hpT := by decide +kernel
  hη0 := by decide +kernel
  hη1 := by decide +kernel
  hRt := rfl
  pT := List.forall_mem_cons.mpr ⟨pcT0_ok, List.forall_mem_cons.mpr ⟨pcT1_ok, List.forall_mem_cons.mpr ⟨pcT2_ok, List.forall_mem_cons.mpr ⟨pcT3_ok, List.forall_mem_cons.mpr ⟨pcT4_ok, List.forall_mem_cons.mpr ⟨pcT5_ok, List.forall_mem_cons.mpr ⟨pcT6_ok, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
  pF := List.forall_mem_cons.mpr ⟨pcF0_ok, List.forall_mem_cons.mpr ⟨pcF1_ok, List.forall_mem_cons.mpr ⟨pcF2_ok, List.forall_mem_cons.mpr ⟨pcF3_ok, List.forall_mem_cons.mpr ⟨pcF4_ok, List.forall_mem_cons.mpr ⟨pcF5_ok, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
  bdT := BD_mono (polyMeas_BD _ _ capsT_ok).2 (le_trans (by exact_mod_cast capsT_le) hC)
  bdF := BD_mono (polyMeas_BD _ _ capsF_ok).2 (le_trans (by exact_mod_cast capsF_le) hC)
  pTn := List.forall_mem_cons.mpr ⟨pcTn0_ok, List.forall_mem_cons.mpr ⟨pcTn1_ok, List.forall_mem_cons.mpr ⟨pcTn2_ok, List.forall_mem_nil _⟩⟩⟩
  pFn := List.forall_mem_cons.mpr ⟨pcFn0_ok, List.forall_mem_cons.mpr ⟨pcFn1_ok, List.forall_mem_cons.mpr ⟨pcFn2_ok, List.forall_mem_nil _⟩⟩⟩
  hTn := by decide +kernel
  bdTn := BD_mono (polyMeas_BD _ _ capsTn_ok).2 (le_trans (by exact_mod_cast capsTn_le) hC)
  bdFn := BD_mono (polyMeas_BD _ _ capsFn_ok).2 (le_trans (by exact_mod_cast capsFn_le) hC)
  nm := by decide +kernel

/-- **`TrialForm.Spec`** of the trial for a family member with the trial's data. -/
theorem spec (D : SignedData) (hτ : D.τ ∈ Set.Ioo (0 : ℝ) 1)
    (hv : D.v = tseq (fQ trial.v.f) (trial.v.tail.map TailQ.toC))
    (ha : D.a = tseq (fQ trial.a.f) (trial.a.tail.map TailQ.toC))
    (hp : D.p = tseq (fQ trial.p.f) (trial.p.tail.map TailQ.toC))
    (hη : D.η = trial.η) (hR : D.R = fun n => fQ trial.R.f (n + 1)) (hSup : D.Sup = trial.Sup)
    (ht : D.t = mneg D.μ D.τ)
    (hμT : D.μ.P true = polyMeas (trial.qT.map PieceQ.toPiece))
    (hμF : D.μ.P false = polyMeas (trial.qF.map PieceQ.toPiece))
    (hμTn : D.μ.N true = polyMeas (trial.qTn.map PieceQ.toPiece))
    (hμFn : D.μ.N false = polyMeas (trial.qFn.map PieceQ.toPiece))
    (hCb : ((Cb : ℚ) : ℝ) ≤ D.Cb) : trial.form.Spec D :=
  TrialQ.spec trial D hτ hv ha hp hη hR hSup ht hμT hμF hμTn hμFn (dataOK hCb)

/-- The phantom bound of the Λ tilt: `|Σ R_n y^(n+1)/(n+1)| ≤ BRq` for `|y| ≤ 1` (`RefTrial.hBR`, via `hBR_of`). -/
def BRq : ℚ := ((516881 : ℚ) / 524288)

theorem br_le : brQ trial.R.f ≤ BRq := by decide +kernel

/-- The mass of the signed reference `μ = P - N = c_r`: `|P| - |N| = 1 - α/2` (`SRef.mass`). -/
theorem mass : ((trial.qT.map PieceQ.massQ).sum + (trial.qF.map PieceQ.massQ).sum) -
    ((trial.qTn.map PieceQ.massQ).sum + (trial.qFn.map PieceQ.massQ).sum) = 1 - alpha / 2 := by
  decide +kernel

#print axioms spec
#print axioms mass
#print axioms br_le

end CatalanMeasure.GenD.Signed.Data.Trial.T0
