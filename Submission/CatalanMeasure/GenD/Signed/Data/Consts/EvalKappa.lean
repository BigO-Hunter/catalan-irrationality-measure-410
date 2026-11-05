module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Core
public import Submission.CatalanMeasure.Cert.FieldEval
public import Submission.CatalanMeasure.GenD.D58.Cert590.Data

@[expose] public section

/-!
# Pole-sum constants of the field identifications (Theorem A, lane E1, item 9)

The constants `cSv cTv cTp cSa cTa` inside `snK … frK` (`Data/Trial/Hid`) are the additive
constants `sConst`, `tConst` of the geometric tails (`FieldForm`):
`sConst tail = -Σ Re[r log (-z)]`, `tConst tail = -(1/2) Σ Re[r log (-2z)]`.
Both are pole potentials at the rational point `c = 0`:

* `sConstE tl = poleF (tl.map sPoleK) 0` with `sPoleK`: weight `-r`, pole `z`;
* `tConstE tl = poleF (tl.map tPoleK) 0` with `tPoleK`: weight `-r/2`, pole `2z`;
* `log 2 = poleF [⟨1, 0, -2, 0⟩] 0`.

`Data/Cells/Core.poleSumI_spec` (IntegerAnchor) evaluates the pole sum to `2^-56`, so
`ivS`, `ivT`, `ivL2` give rational enclosures.  `lin3` is a Boolean check that a linear form
`c0 + c1 x1 + c2 x2 + c3 x3` of three enclosed reals is at most a rational (`lin3_sound`).

This module imports only `Cells.Core` and `Cert.FieldEval`, so it does not depend on `FieldForm`:
`sConstE`/`tConstE` are written as the right-hand sides of `FieldForm.sConst`/`tConst` (the bridge is
`rfl`, in `EvalKappaT`).  Instances for the tails shared by all trials (`Cert590.V`, `Cert590.P`)
are at the end.
-/

namespace CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa
open CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.Data.Cells OAI.InternalCatalan
open CatalanMeasure.Cert (TailQ)

/-! ### 1. The constants as pole sums -/

/-- `ρ = -r`, `p = z`. -/
def sPoleK (t : TailQ) : PoleR := ⟨-t.rr, -t.ri, t.zr, t.zi⟩

/-- `ρ = -r/2`, `p = 2z`. -/
def tPoleK (t : TailQ) : PoleR := ⟨-t.rr / 2, -t.ri / 2, 2 * t.zr, 2 * t.zi⟩

/-- Right-hand side of `FieldForm.sConst (tl.map TailQ.toC)`. -/
noncomputable def sConstE (tl : List TailQ) : ℝ :=
  -((tl.map TailQ.toC).map (fun zr : ℂ × ℂ => (zr.2 * Complex.log (-zr.1)).re)).sum

/-- Right-hand side of `FieldForm.tConst (tl.map TailQ.toC)`. -/
noncomputable def tConstE (tl : List TailQ) : ℝ :=
  -((tl.map TailQ.toC).map (fun zr : ℂ × ℂ => (zr.2 * Complex.log (-2 * zr.1)).re)).sum / 2

theorem poleF_nil : poleF [] 0 = 0 := by simp [poleF]

theorem poleF_cons (q : PoleR) (qs : List PoleR) :
    poleF (q :: qs) 0 = (q.rho * Complex.log (((0 : ℝ) : ℂ) - q.pc)).re + poleF qs 0 := by
  simp [poleF]

theorem sConstE_eq (tl : List TailQ) : sConstE tl = poleF (tl.map sPoleK) 0 := by
  induction tl with
  | nil => simp [sConstE, poleF]
  | cons t ts ih =>
    have e1 : (sPoleK t).rho = -(t.toC.2) := by
      apply Complex.ext <;> simp [PoleR.rho, sPoleK, TailQ.toC, barrierComplex]
    have e2 : ((0 : ℝ) : ℂ) - (sPoleK t).pc = -(t.toC.1) := by
      apply Complex.ext <;> simp [PoleR.pc, sPoleK, TailQ.toC, barrierComplex]
    rw [List.map_cons, poleF_cons, e1, e2, ← ih]
    simp only [sConstE, List.map_cons, List.sum_cons, neg_mul, Complex.neg_re]
    ring

theorem tConstE_eq (tl : List TailQ) : tConstE tl = poleF (tl.map tPoleK) 0 := by
  induction tl with
  | nil => simp [tConstE, poleF]
  | cons t ts ih =>
    have e1 : (tPoleK t).rho = ((-1 / 2 : ℝ) : ℂ) * t.toC.2 := by
      apply Complex.ext <;> simp [PoleR.rho, tPoleK, TailQ.toC, barrierComplex] <;> ring
    have e2 : ((0 : ℝ) : ℂ) - (tPoleK t).pc = -2 * t.toC.1 := by
      apply Complex.ext <;> simp [PoleR.pc, tPoleK, TailQ.toC, barrierComplex]
    rw [List.map_cons, poleF_cons, e1, e2, mul_assoc, Complex.re_ofReal_mul, ← ih]
    simp only [tConstE, List.map_cons, List.sum_cons]
    ring

theorem log_two_eq_poleF : poleF [⟨1, 0, -2, 0⟩] 0 = Real.log 2 := by
  rw [poleF_cons, poleF_nil, add_zero, re_clog_real ⟨1, 0, -2, 0⟩ rfl rfl]
  norm_num

/-! ### 2. Rational enclosures from `poleSumI` -/

/-- Integer enclosure `(S, E)`: `|Σ - S/2^56| ≤ E/2^56` (`poleSumI_spec`). -/
def encS (tl : List TailQ) : Option (ℤ × ℕ) := poleSumI 56 0 (tl.map sPoleK)
def encT (tl : List TailQ) : Option (ℤ × ℕ) := poleSumI 56 0 (tl.map tPoleK)
def encL2 : Option (ℤ × ℕ) := poleSumI 56 0 [⟨1, 0, -2, 0⟩]

/-- The rational interval `[(S - E)/2^56, (S + E)/2^56]`. -/
def ivOf (o : Option (ℤ × ℕ)) : Option (ℚ × ℚ) :=
  o.map fun p => (((p.1 - p.2 : ℤ) : ℚ) / 2 ^ 56, ((p.1 + p.2 : ℤ) : ℚ) / 2 ^ 56)

/-- `x` lies in the interval, whenever the enclosure exists. -/
def Encl (x : ℝ) (o : Option (ℚ × ℚ)) : Prop :=
  ∀ l h : ℚ, o = some (l, h) → (l : ℝ) ≤ x ∧ x ≤ (h : ℝ)

theorem encl_of_poleSumI {x : ℝ} (poles : List PoleR) (hx : x = poleF poles 0) :
    Encl x (ivOf (poleSumI 56 0 poles)) := by
  intro l h hlh
  unfold ivOf at hlh
  rcases e : poleSumI 56 0 poles with _ | ⟨S, E⟩
  · rw [e] at hlh; simp at hlh
  · rw [e] at hlh
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hlh
    obtain ⟨rfl, rfl⟩ := hlh
    have h2 := poleSumI_spec 56 (by norm_num) 0 poles S E e
    simp only [Rat.cast_zero] at h2
    have h3 : x = (poles.map (fun q => (q.rho * Complex.log (((0 : ℝ) : ℂ) - q.pc)).re)).sum := hx
    rw [← h3] at h2
    obtain ⟨hl, hh⟩ := abs_le.mp h2
    push_cast
    constructor <;> linarith

theorem encl_sConst (tl : List TailQ) : Encl (sConstE tl) (ivOf (encS tl)) :=
  encl_of_poleSumI _ (sConstE_eq tl)

theorem encl_tConst (tl : List TailQ) : Encl (tConstE tl) (ivOf (encT tl)) :=
  encl_of_poleSumI _ (tConstE_eq tl)

theorem encl_log2 : Encl (Real.log 2) (ivOf encL2) :=
  encl_of_poleSumI _ log_two_eq_poleF.symm

/-! ### 3. Linear forms of enclosed reals -/

/-- The least upper bound of `c * x` over the interval. -/
def ubTerm (c : ℚ) (o : Option (ℚ × ℚ)) : Option ℚ :=
  o.map fun iv => if 0 ≤ c then c * iv.2 else c * iv.1

theorem ubTerm_sound {c : ℚ} {x : ℝ} {o : Option (ℚ × ℚ)} (h : Encl x o) {u : ℚ}
    (hu : ubTerm c o = some u) : (c : ℝ) * x ≤ (u : ℝ) := by
  rcases o with _ | ⟨l, hi⟩
  · simp [ubTerm] at hu
  · simp only [ubTerm, Option.map_some, Option.some.injEq] at hu
    obtain ⟨hl, hh⟩ := h l hi rfl
    subst hu
    split_ifs with hc
    · have : (0 : ℝ) ≤ c := by exact_mod_cast hc
      push_cast
      exact mul_le_mul_of_nonneg_left hh this
    · have : (c : ℝ) ≤ 0 := by exact_mod_cast (not_le.mp hc).le
      push_cast
      exact mul_le_mul_of_nonpos_left hl this

/-- `c0 + c1 x1 + c2 x2 + c3 x3 ≤ B` for every `xi` in its enclosure. -/
def lin3 (c0 c1 c2 c3 : ℚ) (o1 o2 o3 : Option (ℚ × ℚ)) (B : ℚ) : Bool :=
  match ubTerm c1 o1, ubTerm c2 o2, ubTerm c3 o3 with
  | some u1, some u2, some u3 => decide (c0 + u1 + u2 + u3 ≤ B)
  | _, _, _ => false

theorem lin3_sound {c0 c1 c2 c3 B : ℚ} {o1 o2 o3 : Option (ℚ × ℚ)} {x1 x2 x3 : ℝ}
    (h1 : Encl x1 o1) (h2 : Encl x2 o2) (h3 : Encl x3 o3)
    (h : lin3 c0 c1 c2 c3 o1 o2 o3 B = true) :
    (c0 : ℝ) + c1 * x1 + c2 * x2 + c3 * x3 ≤ (B : ℝ) := by
  unfold lin3 at h
  rcases e1 : ubTerm c1 o1 with _ | u1 <;> rcases e2 : ubTerm c2 o2 with _ | u2 <;>
    rcases e3 : ubTerm c3 o3 with _ | u3 <;> simp [e1, e2, e3] at h
  have a1 := ubTerm_sound h1 e1
  have a2 := ubTerm_sound h2 e2
  have a3 := ubTerm_sound h3 e3
  have hB : ((c0 + u1 + u2 + u3 : ℚ) : ℝ) ≤ (B : ℝ) := by exact_mod_cast h
  push_cast at hB
  linarith

/-- An interval with explicit decimal bounds (for the shared tails). -/
def within (o : Option (ℚ × ℚ)) (lo hi : ℚ) : Bool :=
  match o with
  | some iv => decide (lo ≤ iv.1 ∧ iv.2 ≤ hi)
  | none => false

theorem within_sound {x : ℝ} {o : Option (ℚ × ℚ)} {lo hi : ℚ} (h : Encl x o)
    (hw : within o lo hi = true) : (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ) := by
  rcases o with _ | ⟨l, u⟩
  · simp [within] at hw
  · simp only [within, decide_eq_true_eq] at hw
    obtain ⟨hl, hh⟩ := h l u rfl
    have a1 : (lo : ℝ) ≤ l := by exact_mod_cast hw.1
    have a2 : (u : ℝ) ≤ hi := by exact_mod_cast hw.2
    exact ⟨a1.trans hl, hh.trans a2⟩

/-- An enclosure, as a literal interval, for a real known to lie in it. -/
theorem encl_of_bounds {x : ℝ} {lo hi : ℚ} (h1 : (lo : ℝ) ≤ x) (h2 : x ≤ (hi : ℝ)) :
    Encl x (some (lo, hi)) := by
  intro l h hlh
  simp only [Option.some.injEq, Prod.mk.injEq] at hlh
  obtain ⟨rfl, rfl⟩ := hlh
  exact ⟨h1, h2⟩

/-! ### 4. The tails shared by all trials (`Cert590.V`, `Cert590.P`)

Enclosures to 13 decimals (one `decide +kernel` per value); `EvalKappaT` feeds them to `lin3`. -/

set_option maxRecDepth 1000000
set_option Elab.async false

theorem sV_within :
    within (ivOf (encS CatalanMeasure.GenD.D58.Cert590.V)) (4357640364751 / 10 ^ 13)
      (4357640364752 / 10 ^ 13) = true := by decide +kernel

theorem tV_within :
    within (ivOf (encT CatalanMeasure.GenD.D58.Cert590.V)) (74499681778994 / 10 ^ 13)
      (74499681778995 / 10 ^ 13) = true := by decide +kernel

theorem tP_within :
    within (ivOf (encT CatalanMeasure.GenD.D58.Cert590.P)) (102232284429226 / 10 ^ 13)
      (102232284429227 / 10 ^ 13) = true := by decide +kernel

theorem log2_within :
    within (ivOf encL2) (6931471805599 / 10 ^ 13) (6931471805600 / 10 ^ 13) = true := by
  decide +kernel

/-- `cSv` (S-constant of the `v` tail): `0.4357640364751 ≤ · ≤ 0.4357640364752`. -/
theorem sV_bounds :
    ((4357640364751 / 10 ^ 13 : ℚ) : ℝ) ≤ sConstE CatalanMeasure.GenD.D58.Cert590.V ∧
      sConstE CatalanMeasure.GenD.D58.Cert590.V ≤ ((4357640364752 / 10 ^ 13 : ℚ) : ℝ) :=
  within_sound (encl_sConst _) sV_within

theorem tV_bounds :
    ((74499681778994 / 10 ^ 13 : ℚ) : ℝ) ≤ tConstE CatalanMeasure.GenD.D58.Cert590.V ∧
      tConstE CatalanMeasure.GenD.D58.Cert590.V ≤ ((74499681778995 / 10 ^ 13 : ℚ) : ℝ) :=
  within_sound (encl_tConst _) tV_within

theorem tP_bounds :
    ((102232284429226 / 10 ^ 13 : ℚ) : ℝ) ≤ tConstE CatalanMeasure.GenD.D58.Cert590.P ∧
      tConstE CatalanMeasure.GenD.D58.Cert590.P ≤ ((102232284429227 / 10 ^ 13 : ℚ) : ℝ) :=
  within_sound (encl_tConst _) tP_within

theorem log2_bounds' :
    ((6931471805599 / 10 ^ 13 : ℚ) : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ ((6931471805600 / 10 ^ 13 : ℚ) : ℝ) :=
  within_sound encl_log2 log2_within

/-! ### 5. Literal enclosures used by the trial-level checks (`EvalKappaT`) -/

/-- `sConstE V ∈ [0.4357640364751, 0.4357640364752]`. -/
def ivSV : Option (ℚ × ℚ) := some (4357640364751 / 10 ^ 13, 4357640364752 / 10 ^ 13)
def ivTV : Option (ℚ × ℚ) := some (74499681778994 / 10 ^ 13, 74499681778995 / 10 ^ 13)
def ivTP : Option (ℚ × ℚ) := some (102232284429226 / 10 ^ 13, 102232284429227 / 10 ^ 13)
def ivL2 : Option (ℚ × ℚ) := some (6931471805599 / 10 ^ 13, 6931471805600 / 10 ^ 13)
/-- the dummy enclosure of `0`, for unused slots of `lin3` -/
def ivZero : Option (ℚ × ℚ) := some (0, 0)

theorem encl_sV : Encl (sConstE CatalanMeasure.GenD.D58.Cert590.V) ivSV :=
  encl_of_bounds sV_bounds.1 sV_bounds.2
theorem encl_tV : Encl (tConstE CatalanMeasure.GenD.D58.Cert590.V) ivTV :=
  encl_of_bounds tV_bounds.1 tV_bounds.2
theorem encl_tP : Encl (tConstE CatalanMeasure.GenD.D58.Cert590.P) ivTP :=
  encl_of_bounds tP_bounds.1 tP_bounds.2
theorem encl_log2' : Encl (Real.log 2) ivL2 :=
  encl_of_bounds log2_bounds'.1 log2_bounds'.2
theorem encl_zero : Encl (0 : ℝ) ivZero := encl_of_bounds (by simp) (by simp)

/-! ### 6. The seven κ forms over abstract constants

`snK … frK` (`Data/Trial/Hid`) are these expressions in `cSv … cTa`; `EvalKappaT` applies them
with `exact` (the unfolded constants have exactly this shape). -/

section Forms
variable {η Sup : ℚ} {o1 o2 o3 : Option (ℚ × ℚ)} {B : ℚ}

theorem sn_le {cSv cTp cSa : ℝ} (h1 : Encl cSv o1) (h2 : Encl cTp o2) (h3 : Encl cSa o3)
    (h : lin3 0 (-1) (-4 * η) (-2) o1 o2 o3 B = true) :
    -cSv - 4 * (η : ℝ) * cTp - 2 * cSa ≤ (B : ℝ) := by
  have := lin3_sound h1 h2 h3 h
  push_cast at this; linarith

theorem sp_le {cSv cTp cSa : ℝ} (h1 : Encl cSv o1) (h2 : Encl cTp o2) (h3 : Encl cSa o3)
    (h : lin3 (2 * Sup) (-1) (-4 * η) 2 o1 o2 o3 B = true) :
    -cSv - 4 * (η : ℝ) * cTp + 2 * cSa + 2 * (Sup : ℝ) ≤ (B : ℝ) := by
  have := lin3_sound h1 h2 h3 h
  push_cast at this; linarith

theorem sc_le {cTv : ℝ} (h1 : Encl cTv o1)
    (h : lin3 0 2 0 0 o1 ivZero ivZero B = true) : 2 * cTv ≤ (B : ℝ) := by
  have := lin3_sound h1 encl_zero encl_zero h
  push_cast at this; linarith

theorem sm_le {cTp cSa : ℝ} (h1 : Encl cTp o1) (h2 : Encl cSa o2)
    (h : lin3 0 (-2 * η) (-2) 0 o1 o2 ivZero B = true) :
    -2 * (η : ℝ) * cTp - 2 * cSa ≤ (B : ℝ) := by
  have := lin3_sound h1 h2 encl_zero h
  push_cast at this; linarith

theorem spm_le {cTp cSa : ℝ} (h1 : Encl cTp o1) (h2 : Encl cSa o2)
    (h : lin3 (2 * Sup) (-2 * η) 2 0 o1 o2 ivZero B = true) :
    -2 * (η : ℝ) * cTp + 2 * cSa + 2 * (Sup : ℝ) ≤ (B : ℝ) := by
  have := lin3_sound h1 h2 encl_zero h
  push_cast at this; linarith

/-- `ρ` stands for `remC (1 - 2η)` (`= 11/8` at `η = 9/20`). -/
theorem near_le {cSa ρ : ℝ} (hρ : ρ = 11 / 8) {α β : ℚ} (h1 : Encl cSa o1)
    (h : lin3 (2 * Sup) 2 (11 / 4 * β + η + α / 2) 0 o1 ivL2 ivZero B = true) :
    2 * cSa + ρ * (β : ℝ) * (2 * Real.log 2) + ((η : ℝ) + (α : ℝ) / 2) * Real.log 2 +
      2 * (Sup : ℝ) ≤ (B : ℝ) := by
  have := lin3_sound h1 encl_log2' encl_zero h
  subst hρ
  push_cast at this; nlinarith [this]

theorem fr_le {cTa : ℝ} (h1 : Encl cTa o1)
    (h : lin3 0 (-2) 0 0 o1 ivZero ivZero B = true) : -2 * cTa ≤ (B : ℝ) := by
  have := lin3_sound h1 encl_zero encl_zero h
  push_cast at this; linarith

end Forms

end CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa
