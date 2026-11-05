module

public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.Data
public import Submission.CatalanMeasure.GenD.D58.Budget590

@[expose] public section

/-!
# 410 assembly: the `Phase2Data 2` term
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open Set Filter Topology
open CatalanMeasure.Signed OAI.InternalCatalan CatalanMeasure.Parametric CatalanMeasure.GenD.Analytic

open CatalanMeasure.GenD.D58
open CatalanMeasure.GenD.Signed.Data.S1 CatalanMeasure.GenD.Signed.Data.Trial

noncomputable section

theorem hn_top410 : Tendsto (fun N : ℕ => ((58 * N : ℕ) : ℝ)) atTop atTop :=
  (CatalanMeasure.Signed.Consts.hn_top_lin (n0 := 58) (by norm_num)).congr
    (fun N => by push_cast; rfl)

theorem hlogu410 : Tendsto (fun N : ℕ => -Real.log (umin410 N) / ((58 * N : ℕ) : ℝ)) atTop (𝓝 0) := by
  have h := CatalanMeasure.Signed.Consts.hlogu_lin
    (s := Real.sqrt (1 - aGap ^ 2)) (A := 106) (B := 2) (n0 := 58)
    (Real.sqrt_pos.2 one_sub_aGap_sq_pos) (by norm_num) (by norm_num) (by norm_num)
  refine h.congr (fun N => ?_)
  simp only [umin410]
  push_cast
  rfl

/-- **`Phase2Data 2` of the 410 chain** from the ingredient rows. -/
def phase2 (R : Rows410) : Phase2Data 2 where
  ncount := fun N => 58 * N
  ncount_pos := fun N hN => Nat.mul_pos (by norm_num) hN
  B := -K590.target0 + Real.log 2 / 2
  cost := K590.secondCost'
  α1 := 1 / 16
  α1_nonneg := by norm_num
  lo := lo410
  hi := hi410
  cover := fun α h0 h1 => by
    by_cases h : α ≤ 1 / 200
    · exact ⟨0, (show (0 : ℝ) ≤ α from h0), (show α ≤ 1 / 200 from h)⟩
    · push_neg at h
      exact ⟨1, (show (1 / 200 : ℝ) ≤ α from h.le), (show α ≤ 1 / 16 from h1)⟩
  Rf := fun N => populationPhysicalFreeField P410 N
  Cf := fun N => populationPhysicalColumnField P410 N (0 + 0)
  Rm := fun N => groupedMarkedField P410 N
  Rn := fun N => groupedNearField P410 N
  constant := fun N α => Glue410.constantClosed P410 N α
  αA := αA410
  αB := αB410
  DA := DA410
  DB := DB410
  hends := ends410
  hν := fun i N => by fin_cases i <;> simp [DA410, famD]
  hRf := fun i N => by fin_cases i <;> rfl
  hCf := fun i N => by fin_cases i <;> rfl
  mA := fun i => Eventually.of_forall fun N => by
    fin_cases i
    · show (1 : ℝ) - 0 / 2 = (famD X0 N).μ.mass; rw [mass0]
    · show (1 : ℝ) - 1 / 200 / 2 = (famD X1 N).μ.mass; rw [mass1]
  mB := fun i => Eventually.of_forall fun N => by
    fin_cases i
    · show (1 : ℝ) - 1 / 200 / 2 = (famD X1 N).μ.mass; rw [mass1]
    · show (1 : ℝ) - 1 / 16 / 2 = (famD X2 N).μ.mass; rw [mass2]
  SnA := R.SnA
  SnB := R.SnB
  SpA := R.SpA
  SpB := R.SpB
  SyA := R.SyA
  SyB := R.SyB
  hSnA := R.hSnA
  hSnB := R.hSnB
  hSpA := R.hSpA
  hSpB := R.hSpB
  hSyA := R.hSyA
  hSyB := R.hSyB
  cP := R.cP
  rA := R.rA
  rB := R.rB
  κc := R.κc
  hP := Glue410.hP_closed D58.Odd.design_admissible
    (fun i => by fin_cases i <;> norm_num [lo410])
    (fun i => by fin_cases i <;> norm_num [hi410]) R.hcP
  hrA := R.hrA
  hrB := R.hrB
  hκ := R.hκ
  κlo := κlo410
  κhi := κhi410
  epsSplit := fun _ => 1 / 10
  epsSplit_pos := fun _ => by norm_num
  epsSplit_le := fun _ => by norm_num
  etaA := fun i N => by
    fin_cases i <;> simp [DA410, famD, X0, X1, T0.trial, T1.trial] <;> norm_num
  Clsf := R.Clsf
  LRf := fun N k q m1 m2 xn gp yn yp =>
    logRatioZ (q + m2 - 5 * N) (Fin.append xn yn) (Fin.append gp yp)
  cp := R.cp
  cp_pos := R.cp_pos
  cp_le := R.cp_le
  err_small := R.err_small
  cp_theta := R.cp_theta
  hLR := fun i N k q m1 m2 xn gp yn yp => by fin_cases i <;> rfl
  hCls := R.hCls
  capE := R.capE
  hxc0 := R.hxc0
  hxc1 := R.hxc1
  hC1 := R.hC1
  hlo0 := fun i => by fin_cases i <;> norm_num [lo410]
  hhi1 := fun i => by fin_cases i <;> norm_num [hi410]
  hrP := R.hrP
  hrSA := R.hrSA
  hrSB := R.hrSB
  umin := umin410
  hum0 := umin410_pos
  hum1 := umin410_le_one
  Bd := R.Bd
  Rbd := R.Rbd
  hBdPA := R.hBdPA
  hBdPB := R.hBdPB
  hBdSA := R.hBdSA
  hBdSB := R.hBdSB
  hRP := R.hRP
  hRSA := R.hRSA
  hRSB := R.hRSB
  hn_top := hn_top410
  hlogu := hlogu410
  gs := 401 / 2500
  xc := 999 / 1000
  C1 := 9631 / 20000
  hgs := R.hgs
  hxc := R.hxc
  hC1le := R.hC1le
  hnegA := R.hnegA
  hnegB := R.hnegB
  hposA := R.hposA
  hposB := R.hposB
  hposTopA := R.hposTopA
  hposTopB := R.hposTopB
  hnearA := R.hnearA
  hnearB := R.hnearB
  hnearTopA := R.hnearTopA
  hnearTopB := R.hnearTopB
  zb := R.zb
  hZB := R.hZB
  hbudLo := R.hbudLo
  hbudHi := R.hbudHi

end

end CatalanMeasure.GenD.Signed.Data.Assembly
