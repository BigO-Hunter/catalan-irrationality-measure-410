module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T0Data
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T1Data
public import Submission.CatalanMeasure.GenD.Signed.Data.Trial.T2Data

@[expose] public section

/-!
# κ ≤ κ_up for every (trial, field) (Theorem A, lane E1, item 9)

`snK spK scK smK spmK nearK frK` (`Data/Trial/Hid`) are linear in the pole-sum constants
`cSv cTv cTp cSa cTa` (`sConst`/`tConst` of the tails), `log 2`, `η`, `Sup` and `α`.
`EvalKappa` encloses the constants of the tails shared by all trials (`Cert590.V`, `Cert590.P`)
to 13 decimals and `log 2`; the trial-specific `a`-tail (20 real poles) is enclosed inside each
kernel check by `poleSumI_spec` (`ivOf (encS …)`), so these theorems do not depend on any
hard-coded value of the `a`-tail.  `κ_up` are the exact rationals of `NOTES-D1`
("Cell campaign - paused"): `κ_up = ⌈κ⌉_{1e-9} + 2^-40`.  Each check is one `decide +kernel`.

Written against `EvalKappa`, which is built; **this module imports `Data/Trial` and is not yet built**
(contract: build once after item 6).  The same `lin3` checks on a copy of the literals were
built in the probe `EvalProbeK` (21 checks, all pass).
-/

namespace CatalanMeasure.GenD.Signed.Data.Consts.EvalKappaT
open CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa
open CatalanMeasure.GenD.Signed.Data.Trial

set_option maxRecDepth 1000000
set_option Elab.async false

/- The rational upper bounds `κ_up` (denominator `2^31 · 10^9`, or `2^32 · 10^8` for the `near` rows 1, 2). -/
namespace Kup
def sn0 : ℚ := -40618411264879768219 / 2147483648000000000
def sn1 : ℚ := -40643792062730351259 / 2147483648000000000
def sn2 : ℚ := -40655167468297400987 / 2147483648000000000
def sp0 : ℚ := -40257959211907035803 / 2147483648000000000
def sp1 : ℚ := -40232347862359487131 / 2147483648000000000
def sp2 : ℚ := -40217791571800765083 / 2147483648000000000
def sc0 : ℚ := 31997369680752659813 / 2147483648000000000
def sc1 : ℚ := 31997369680752659813 / 2147483648000000000
def sc2 : ℚ := 31997369680752659813 / 2147483648000000000
def sm0 : ℚ := -19923820802539139739 / 2147483648000000000
def sm1 : ℚ := -19949201600389722779 / 2147483648000000000
def sm2 : ℚ := -19960577005956772507 / 2147483648000000000
def spm0 : ℚ := -19563368749566407323 / 2147483648000000000
def spm1 : ℚ := -19537757397871375003 / 2147483648000000000
def spm2 : ℚ := -19523201109460136603 / 2147483648000000000
def near0 : ℚ := 865260574548544869 / 2147483648000000000
def near1 : ℚ := 183012082651100641 / 429496729600000000
def near2 : ℚ := 241556859172287969 / 429496729600000000
def fr0 : ℚ := 216847083391274341 / 2147483648000000000
def fr1 : ℚ := 182042815908138341 / 2147483648000000000
def fr2 : ℚ := 177800204263476581 / 2147483648000000000
end Kup

/-! ### Bridges: the constants of `Hid` are the constants of `EvalKappa` -/

section Bridge
variable {T : TrialQ}

theorem cSv_eq (h : T.v.tail = CatalanMeasure.GenD.D58.Cert590.V) :
    cSv T = sConstE CatalanMeasure.GenD.D58.Cert590.V := by
  rw [show cSv T = sConstE T.v.tail from rfl, h]

theorem cTv_eq (h : T.v.tail = CatalanMeasure.GenD.D58.Cert590.V) :
    cTv T = tConstE CatalanMeasure.GenD.D58.Cert590.V := by
  rw [show cTv T = tConstE T.v.tail from rfl, h]

theorem cTp_eq (h : T.p.tail = CatalanMeasure.GenD.D58.Cert590.P) :
    cTp T = tConstE CatalanMeasure.GenD.D58.Cert590.P := by
  rw [show cTp T = tConstE T.p.tail from rfl, h]

theorem cSa_eq : cSa T = sConstE T.a.tail := rfl
theorem cTa_eq : cTa T = tConstE T.a.tail := rfl

/-! ### Generic κ bounds (any trial whose `v`, `p` tails are the shared ones) -/

theorem snK_le (hv : T.v.tail = CatalanMeasure.GenD.D58.Cert590.V)
    (hp : T.p.tail = CatalanMeasure.GenD.D58.Cert590.P) {B : ℚ}
    (h : lin3 0 (-1) (-4 * T.η) (-2) ivSV ivTP (ivOf (encS T.a.tail)) B = true) :
    snK T ≤ (B : ℝ) := by
  have h1 : Encl (cSv T) ivSV := by rw [cSv_eq hv]; exact encl_sV
  have h2 : Encl (cTp T) ivTP := by rw [cTp_eq hp]; exact encl_tP
  have h3 : Encl (cSa T) (ivOf (encS T.a.tail)) := by rw [cSa_eq]; exact encl_sConst _
  exact sn_le h1 h2 h3 h

theorem spK_le (hv : T.v.tail = CatalanMeasure.GenD.D58.Cert590.V)
    (hp : T.p.tail = CatalanMeasure.GenD.D58.Cert590.P) {B : ℚ}
    (h : lin3 (2 * T.Sup) (-1) (-4 * T.η) 2 ivSV ivTP (ivOf (encS T.a.tail)) B = true) :
    spK T ≤ (B : ℝ) := by
  have h1 : Encl (cSv T) ivSV := by rw [cSv_eq hv]; exact encl_sV
  have h2 : Encl (cTp T) ivTP := by rw [cTp_eq hp]; exact encl_tP
  have h3 : Encl (cSa T) (ivOf (encS T.a.tail)) := by rw [cSa_eq]; exact encl_sConst _
  exact sp_le h1 h2 h3 h

theorem scK_le (hv : T.v.tail = CatalanMeasure.GenD.D58.Cert590.V) {B : ℚ}
    (h : lin3 0 2 0 0 ivTV ivZero ivZero B = true) : scK T ≤ (B : ℝ) := by
  have h1 : Encl (cTv T) ivTV := by rw [cTv_eq hv]; exact encl_tV
  exact sc_le h1 h

theorem smK_le (hp : T.p.tail = CatalanMeasure.GenD.D58.Cert590.P) {B : ℚ}
    (h : lin3 0 (-2 * T.η) (-2) 0 ivTP (ivOf (encS T.a.tail)) ivZero B = true) :
    smK T ≤ (B : ℝ) := by
  have h1 : Encl (cTp T) ivTP := by rw [cTp_eq hp]; exact encl_tP
  have h2 : Encl (cSa T) (ivOf (encS T.a.tail)) := by rw [cSa_eq]; exact encl_sConst _
  exact sm_le h1 h2 h

theorem spmK_le (hp : T.p.tail = CatalanMeasure.GenD.D58.Cert590.P) {B : ℚ}
    (h : lin3 (2 * T.Sup) (-2 * T.η) 2 0 ivTP (ivOf (encS T.a.tail)) ivZero B = true) :
    spmK T ≤ (B : ℝ) := by
  have h1 : Encl (cTp T) ivTP := by rw [cTp_eq hp]; exact encl_tP
  have h2 : Encl (cSa T) (ivOf (encS T.a.tail)) := by rw [cSa_eq]; exact encl_sConst _
  exact spm_le h1 h2 h

theorem nearK_le (hη : T.η = 9 / 20) {α β B : ℚ}
    (h : lin3 (2 * T.Sup) 2 (11 / 4 * β + T.η + α / 2) 0 (ivOf (encS T.a.tail)) ivL2 ivZero B
      = true) :
    nearK T α β ≤ (B : ℝ) := by
  have h1 : Encl (cSa T) (ivOf (encS T.a.tail)) := by rw [cSa_eq]; exact encl_sConst _
  have hρ : CatalanMeasure.Signed.remC (1 - 2 * (T.η : ℝ)) = 11 / 8 := by
    rw [hη]; unfold CatalanMeasure.Signed.remC; norm_num
  exact near_le hρ h1 h

theorem frK_le {B : ℚ}
    (h : lin3 0 (-2) 0 0 (ivOf (encT T.a.tail)) ivZero ivZero B = true) : frK T ≤ (B : ℝ) := by
  have h1 : Encl (cTa T) (ivOf (encT T.a.tail)) := by rw [cTa_eq]; exact encl_tConst _
  exact fr_le h1 h

end Bridge

/-! ### The 21 instances -/

section T0
theorem snK_le_0 : snK T0.trial ≤ ((Kup.sn0 : ℚ) : ℝ) :=
  snK_le rfl rfl (by decide +kernel)

theorem spK_le_0 : spK T0.trial ≤ ((Kup.sp0 : ℚ) : ℝ) :=
  spK_le rfl rfl (by decide +kernel)

theorem scK_le_0 : scK T0.trial ≤ ((Kup.sc0 : ℚ) : ℝ) :=
  scK_le rfl (by decide +kernel)

theorem smK_le_0 : smK T0.trial ≤ ((Kup.sm0 : ℚ) : ℝ) :=
  smK_le rfl (by decide +kernel)

theorem spmK_le_0 : spmK T0.trial ≤ ((Kup.spm0 : ℚ) : ℝ) :=
  spmK_le rfl (by decide +kernel)

theorem nearK_le_0 : nearK T0.trial T0.alpha T0.alpha ≤ ((Kup.near0 : ℚ) : ℝ) :=
  nearK_le rfl (by decide +kernel)

theorem frK_le_0 : frK T0.trial ≤ ((Kup.fr0 : ℚ) : ℝ) :=
  frK_le (by decide +kernel)

end T0

section T1
theorem snK_le_1 : snK T1.trial ≤ ((Kup.sn1 : ℚ) : ℝ) :=
  snK_le rfl rfl (by decide +kernel)

theorem spK_le_1 : spK T1.trial ≤ ((Kup.sp1 : ℚ) : ℝ) :=
  spK_le rfl rfl (by decide +kernel)

theorem scK_le_1 : scK T1.trial ≤ ((Kup.sc1 : ℚ) : ℝ) :=
  scK_le rfl (by decide +kernel)

theorem smK_le_1 : smK T1.trial ≤ ((Kup.sm1 : ℚ) : ℝ) :=
  smK_le rfl (by decide +kernel)

theorem spmK_le_1 : spmK T1.trial ≤ ((Kup.spm1 : ℚ) : ℝ) :=
  spmK_le rfl (by decide +kernel)

theorem nearK_le_1 : nearK T1.trial T1.alpha T1.alpha ≤ ((Kup.near1 : ℚ) : ℝ) :=
  nearK_le rfl (by decide +kernel)

theorem frK_le_1 : frK T1.trial ≤ ((Kup.fr1 : ℚ) : ℝ) :=
  frK_le (by decide +kernel)

end T1

section T2
theorem snK_le_2 : snK T2.trial ≤ ((Kup.sn2 : ℚ) : ℝ) :=
  snK_le rfl rfl (by decide +kernel)

theorem spK_le_2 : spK T2.trial ≤ ((Kup.sp2 : ℚ) : ℝ) :=
  spK_le rfl rfl (by decide +kernel)

theorem scK_le_2 : scK T2.trial ≤ ((Kup.sc2 : ℚ) : ℝ) :=
  scK_le rfl (by decide +kernel)

theorem smK_le_2 : smK T2.trial ≤ ((Kup.sm2 : ℚ) : ℝ) :=
  smK_le rfl (by decide +kernel)

theorem spmK_le_2 : spmK T2.trial ≤ ((Kup.spm2 : ℚ) : ℝ) :=
  spmK_le rfl (by decide +kernel)

theorem nearK_le_2 : nearK T2.trial T2.alpha T2.alpha ≤ ((Kup.near2 : ℚ) : ℝ) :=
  nearK_le rfl (by decide +kernel)

theorem frK_le_2 : frK T2.trial ≤ ((Kup.fr2 : ℚ) : ℝ) :=
  frK_le (by decide +kernel)

end T2

end CatalanMeasure.GenD.Signed.Data.Consts.EvalKappaT
