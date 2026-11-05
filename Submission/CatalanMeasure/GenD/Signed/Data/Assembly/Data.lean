module

public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.Family
public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.Nodes
public import Submission.CatalanMeasure.GenD.Signed.Phase2Contract
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T0Spec
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T1Spec
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T2Spec
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.TrialB0
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.TrialB1
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.TrialB2
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.Umin
public import Submission.CatalanMeasure.GenD.D58.Budget590

@[expose] public section

/-!
# 410 assembly: `Phase2Data 2` from the structural data and the row ingredients

`phase2 R : Phase2Data 2` fills every structural field (scale `ncount = 58 N`, the two intervals
`[0, 1/200]`, `[1/200, 1/16]` with endpoint trials `(T0, T1)`, `(T1, T2)` as `famD`, `epsSplit = 1/10`,
`κ` windows, `umin`, the cap geometry `gs, xc, C1`, the problem fields) and takes the remaining rows as
a record `Rows410` whose field TYPES are exactly those of `Phase2Data` for these definitions.  The row
producers (lane C cells with `cover_eventually`, E1b instances, the spike class, the σ-cap constants,
the budget arithmetic) each deliver one field of `Rows410`.
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open Set Filter Topology
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm OAI.InternalCatalan CatalanMeasure.Parametric CatalanMeasure.GenD.Analytic
open CatalanMeasure.GenD CatalanMeasure.GenD.D58
open CatalanMeasure.GenD.Signed.Data.Trial

noncomputable section

def X0 : FamPar := ⟨T0.trial, CatalanMeasure.Signed.Consts.bs0, 21 / 20, T0.Cb⟩
def X1 : FamPar := ⟨T1.trial, CatalanMeasure.Signed.Consts.bs1, 21 / 20, T1.Cb⟩
def X2 : FamPar := ⟨T2.trial, CatalanMeasure.Signed.Consts.bs2, 11 / 10, T2.Cb⟩

def DA410 : Fin 2 → ℕ → SignedData := ![famD X0, famD X1]
def DB410 : Fin 2 → ℕ → SignedData := ![famD X1, famD X2]
def lo410 : Fin 2 → ℝ := ![0, 1 / 200]
def hi410 : Fin 2 → ℝ := ![1 / 200, 1 / 16]
def αA410 : Fin 2 → ℝ := ![0, 1 / 200]
def αB410 : Fin 2 → ℝ := ![1 / 200, 1 / 16]
def κlo410 : Fin 2 → ℝ := ![3 / 10, 27 / 100]
def κhi410 : Fin 2 → ℝ := ![223 / 500, 4431 / 10000]

abbrev P410 : Parameters := CatalanMeasure.GenD.D58.Odd.design

theorem famD_mass (X : FamPar) (hok : ∀ C : ℝ, (X.Cb : ℝ) ≤ C → X.T.DataOK C) (N : ℕ) {c : ℚ}
    (hc : ((X.T.qT.map PieceQ.massQ).sum + (X.T.qF.map PieceQ.massQ).sum) -
      ((X.T.qTn.map PieceQ.massQ).sum + (X.T.qFn.map PieceQ.massQ).sum) = c) :
    (famD X N).μ.mass = (c : ℝ) := by
  have h := hok _ le_rfl
  have hm : ∀ qs : List PieceQ, (∀ q ∈ qs, PieceOK q.toPiece) →
      (polyMeas (qs.map PieceQ.toPiece)).real univ = (((qs.map PieceQ.massQ).sum : ℚ) : ℝ) := by
    intro qs hqs
    have hq' : ∀ q ∈ qs.map PieceQ.toPiece, PieceOK q := by
      intro q hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      exact hqs r hr
    have := integral_const_polyMeas hq'
    rw [MeasureTheory.integral_const, smul_eq_mul, mul_one] at this
    rw [this, polyMass_cast]
  show SRef.mass (famMu X) = _
  unfold SRef.mass famMu
  simp only [Fintype.sum_bool, cond_true, cond_false]
  rw [hm _ h.pT, hm _ h.pF, hm _ h.pTn, hm _ h.pFn, ← hc]
  push_cast
  ring

theorem mass0 (N : ℕ) : (famD X0 N).μ.mass = 1 - 0 / 2 := by
  rw [famD_mass X0 (fun C hC => T0.dataOK hC) N T0.mass]; norm_num [T0.alpha]
theorem mass1 (N : ℕ) : (famD X1 N).μ.mass = 1 - 1 / 200 / 2 := by
  rw [famD_mass X1 (fun C hC => T1.dataOK hC) N T1.mass]; norm_num [T1.alpha]
theorem mass2 (N : ℕ) : (famD X2 N).μ.mass = 1 - 1 / 16 / 2 := by
  rw [famD_mass X2 (fun C hC => T2.dataOK hC) N T2.mass]; norm_num [T2.alpha]

theorem ends410 (i : Fin 2) : IntervalEnds (αA410 i) (αB410 i) (lo410 i) (hi410 i) (DA410 i) (DB410 i) := by
  have hη : (X0.T.η : ℝ) = X1.T.η := by norm_num [X0, X1, T0.trial, T1.trial]
  have hη' : (X1.T.η : ℝ) = X2.T.η := by norm_num [X1, X2, T1.trial, T2.trial]
  have hK : X0.bs.length = X1.bs.length := by decide +kernel
  have hK' : X1.bs.length = X2.bs.length := by decide +kernel
  fin_cases i
  · exact famD_ends X0 X1 (fun C hC => T0.dataOK hC) (fun C hC => T1.dataOK hC)
      (by norm_num [X0, T0.Cb]) (by norm_num [X1, T1.Cb]) hK hη
      (show _ < _ by norm_num [αA410, αB410]) (le_of_eq (by simp [αA410, lo410])) (le_of_eq (by simp [hi410, αB410]))
  · exact famD_ends X1 X2 (fun C hC => T1.dataOK hC) (fun C hC => T2.dataOK hC)
      (by norm_num [X1, T1.Cb]) (by norm_num [X2, T2.Cb]) hK' hη'
      (show _ < _ by norm_num [αA410, αB410]) (le_of_eq (by simp [αA410, lo410])) (le_of_eq (by simp [hi410, αB410]))

/-- **The ingredient rows**: the fields of `Phase2Data 2` that are not structural, with the types
`Phase2Data` demands for the definitions above. -/
structure Rows410 where
  SnA : Fin 2 → ℝ
  SnB : Fin 2 → ℝ
  SpA : Fin 2 → ℝ
  SpB : Fin 2 → ℝ
  SyA : Fin 2 → ℝ
  SyB : Fin 2 → ℝ
  hSnA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-1 : ℝ) 0, (DA410 i N).fNeg x ≤ SnA i + ε
  hSnB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-1 : ℝ) 0, (DB410 i N).fNeg x ≤ SnB i + ε
  hSpA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (0 : ℝ) 1, (DA410 i N).fPosS x ≤ SpA i + ε
  hSpB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (0 : ℝ) 1, (DB410 i N).fPosS x ≤ SpB i + ε
  hSyA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ s ∈ Ioo (0 : ℝ) 1, (DA410 i N).fCol s ≤ SyA i + ε
  hSyB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ s ∈ Ioo (0 : ℝ) 1, (DB410 i N).fCol s ≤ SyB i + ε
  cP : Fin 2 → ℝ → ℝ
  hcP : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), Glue410.constantLim P410 α ≤ cP i α
  rA : Fin 2 → ℝ
  rB : Fin 2 → ℝ
  κc : Fin 2 → ℝ
  hrA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (DA410 i N).constTotal (58 * N) - (DA410 i N).constant ≤ rA i + ε
  hrB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (DB410 i N).constTotal (58 * N) - (DB410 i N).constant ≤ rB i + ε
  hκ : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, κc i - ε ≤ curvQ (DA410 i N) (DB410 i N) (58 * N)
  Clsf : ∀ (_ k q m1 m2 : ℕ), (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → Prop
  cp : Fin 2 → ℕ → ℝ → ℝ
  cp_pos : ∀ i N α, 0 < cp i N α
  cp_le : ∀ i N α, cp i N α ≤ 1
  err_small : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo410 i) (hi410 i),
    ((DA410 i N).withCount (58 * N)).errJ3 (cp i N α) (58 * N) ≤ ε
  cp_theta : ∀ i N α, cp i N α ≤ (DA410 i N).θ
  hCls : ∀ i, ∀ᶠ N : ℕ in atTop, ∀ α k q m1 m2 xn gp yn yp, Clsf N k q m1 m2 xn gp yn yp →
    (0 < (DA410 i N).sp ∧ (DA410 i N).sp + (DA410 i N).g ≤ q + m2) ∧
    Nonempty (PairCls ((DA410 i N).withCount (q + m2 - (DA410 i N).g))
      ((DB410 i N).withCount (q + m2 - (DA410 i N).g)) (cp i N α) xn gp yn yp)
  capE : Fin 2 → CapEnd
  hxc0 : ∀ i, 0 ≤ (capE i).xc
  hxc1 : ∀ i, (capE i).xc < 1
  hC1 : ∀ i, 0 < (capE i).C1
  hrP : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), remC (1 / 10) * α ≤ (capE i).rP α
  hrSA : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α, 0 ≤ (capE i).rSA α β
  hrSB : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α, 0 ≤ (capE i).rSB α β
  Bd : Fin 2 → ℝ
  Rbd : Fin 2 → ℝ
  hBdPA : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), (capE i).gPA α - (capE i).lamPA α ≤ Bd i
  hBdPB : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), (capE i).gPB α - (capE i).lamPB α ≤ Bd i
  hBdSA : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α,
    (capE i).gSA α β - (capE i).lamSA α β ≤ Bd i
  hBdSB : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α,
    (capE i).gSB α β - (capE i).lamSB α β ≤ Bd i
  hRP : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), (capE i).rP α ≤ Rbd i
  hRSA : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α, (capE i).rSA α β ≤ Rbd i
  hRSB : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α, (capE i).rSB α β ≤ Rbd i
  hgs : ∀ i, (capE i).gs ≤ 401 / 2500
  hxc : ∀ i, 999 / 1000 ≤ (capE i).xc
  hC1le : ∀ i, 9631 / 20000 ≤ (capE i).C1
  hnegA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo410 i) (hi410 i),
    ∀ x ∈ Ioo (-1 : ℝ) 0, x ≤ -(capE i).gs →
      (DA410 i N).fNegM (groupedMarkedField P410 N) x ≤ (capE i).lamNA + ε
  hnegB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo410 i) (hi410 i),
    ∀ x ∈ Ioo (-1 : ℝ) 0, x ≤ -(capE i).gs →
      (DB410 i N).fNegM (groupedMarkedField P410 N) x ≤ (capE i).lamNB + ε
  hposA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo410 i) (hi410 i),
    ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).gs ≤ x → x < (capE i).xc →
      (DA410 i N).fPosMR (groupedMarkedField P410 N) (remC (1 / 10)) α x ≤ (capE i).lamPA α + ε
  hposB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo410 i) (hi410 i),
    ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).gs ≤ x → x < (capE i).xc →
      (DB410 i N).fPosMR (groupedMarkedField P410 N) (remC (1 / 10)) α x ≤ (capE i).lamPB α + ε
  hposTopA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo410 i) (hi410 i),
    ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).xc ≤ x →
      (DA410 i N).fPosMS (groupedMarkedField P410 N) x ≤ (capE i).gPA α + ε
  hposTopB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo410 i) (hi410 i),
    ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).xc ≤ x →
      (DB410 i N).fPosMS (groupedMarkedField P410 N) x ≤ (capE i).gPB α + ε
  hnearA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo410 i) (hi410 i),
    ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).gs ≤ x → x < (capE i).xc →
      (DA410 i N).fNearMS (groupedNearField P410 N) α β x ≤ (capE i).lamSA α β + ε
  hnearB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo410 i) (hi410 i),
    ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).gs ≤ x → x < (capE i).xc →
      (DB410 i N).fNearMS (groupedNearField P410 N) α β x ≤ (capE i).lamSB α β + ε
  hnearTopA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo410 i) (hi410 i),
    ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).xc ≤ x →
      (DA410 i N).fNearMS (groupedNearField P410 N) α β x ≤
        (capE i).gSA α β + ε + (capE i).rSA α β * (-Real.log (1 - x ^ 2))
  hnearTopB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo410 i) (hi410 i),
    ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).xc ≤ x →
      (DB410 i N).fNearMS (groupedNearField P410 N) α β x ≤
        (capE i).gSB α β + ε + (capE i).rSB α β * (-Real.log (1 - x ^ 2))
  zb : Fin 2 → ℝ → ℝ
  hZB : ∀ (i : Fin 2) (c d e : ℝ), 0 ≤ c → 0 ≤ d → 0 ≤ e → lo410 i ≤ c + d + e →
    c + d + e ≤ hi410 i →
    zbCap ((capE i).toS (αA410 i) (αB410 i)) c d e ≤ zb i (c + d + e)
  hbudLo : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i),
    interpCInf (αA410 i) (αB410 i) (cP i α) (rA i) (rB i) (κc i) α +
      fixLog2 (1 / 10) α * Real.log 2 +
      κlo410 i * chord (αA410 i) (αB410 i) (SnA i) (SnB i) α +
      (1 - κlo410 i - α) * chord (αA410 i) (αB410 i) (SpA i) (SpB i) α +
      (1 - α) * chord (αA410 i) (αB410 i) (SyA i) (SyB i) α + zb i α ≤
        (-K590.target0 + Real.log 2 / 2) + K590.secondCost' * α
  hbudHi : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i),
    interpCInf (αA410 i) (αB410 i) (cP i α) (rA i) (rB i) (κc i) α +
      fixLog2 (1 / 10) α * Real.log 2 +
      κhi410 i * chord (αA410 i) (αB410 i) (SnA i) (SnB i) α +
      (1 - κhi410 i - α) * chord (αA410 i) (αB410 i) (SpA i) (SpB i) α +
      (1 - α) * chord (αA410 i) (αB410 i) (SyA i) (SyB i) α + zb i α ≤
        (-K590.target0 + Real.log 2 / 2) + K590.secondCost' * α

end

end CatalanMeasure.GenD.Signed.Data.Assembly
