module

public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Gate

@[expose] public section
set_option Elab.async false

/-!
# Gate for the signed (Theorem A) bound: window `w` as a parameter, `B = 417`, `w = 3/5`

`payB_of_w` is `Bank535.payB_of` with the window `w` a parameter and no `460 ≤ B`; its hypotheses
are the `PayW` clauses cleared of the denominator `kappa = B / rho`.  `pay417_w35` is the instance
`w = 3/5`, `B = 417`, `eta = 38.3257` (threshold `53 rho / 417 + 4 * 53 * delta = 38.32562...`).
`gain_ok417`: `eta < tD - gDg g` where `tD = tDelta + A` is the improved decay budget.

`B = 410` (the S1 column cost): `pay410_w35` is the instance `w = 3/5`, `B = 410`,
`rho' = K590.rhoEnd 87.9663 = 296.586094` (`rhoEnd_val`), `eta = 38.33924` (threshold
`53 rho' / 410 + 4 * 53 * delta = 38.33923948...`); `gain_ok410` needs the Theorem A gain
`A = 58^2 (target0 - K590.target) >= 8.29824` (then `eta - A = 30.041 = 22.05325 + 7.98775`).
-/

namespace CatalanMeasure.GenD.Signed
open CatalanMeasure.GenD D58 Uniform Uniform.Bank540.Ledger Uniform.Bank535
noncomputable section

/-- Generic payment gate with window `w`. -/
theorem payB_of_w (w d0 rho eta delta B : ℝ) (hrho : 0 < rho) (hw : 0 < w) (hd : 0 < delta)
    (he : 0 < eta) (he2 : eta < 2 * d0) (hk : 2 * w * rho < B)
    (hwin : rho < 2 * (w * rho - delta * (2 * B - w * rho)))
    (hpay : d0 * rho + 4 * d0 * delta * B < eta * B) :
    PayW w d0 rho eta (B / rho) delta B := by
  have hB : 0 < B := by nlinarith
  have hkap : 0 < B / rho := by positivity
  have e : B / rho * rho = B := by field_simp
  refine ⟨by rw [mul_comm]; exact e, he, hrho, hw, ?_, hd, ?_, he2, ?_⟩
  · rw [lt_div_iff₀ hrho]; exact hk
  · have : 2 * (w - delta * (2 * (B / rho) - w)) * rho = 2 * (w * rho - delta * (2 * B - w * rho)) := by
      field_simp
    have h2 : 1 * rho < 2 * (w - delta * (2 * (B / rho) - w)) * rho := by rw [this]; linarith
    exact lt_of_mul_lt_mul_right h2 hrho.le
  · have : (d0 + 4 * d0 * delta * (B / rho)) * rho = d0 * rho + 4 * d0 * delta * B := by
      field_simp
    have h2 : (d0 + 4 * d0 * delta * (B / rho)) * rho < eta * (B / rho) * rho := by
      have e2 : eta * (B / rho) * rho = eta * B := by field_simp
      rw [this, e2]; exact hpay
    exact lt_of_mul_lt_mul_right h2 hrho.le

/-- `w = 3/5`, `B = 417`, `eta = 38.3257`. -/
theorem pay417_w35 :
    PayW (3 / 5) D58.d0 Bank540.rho (383257 / 10000) (417 / Bank540.rho) D58.delta 417 := by
  have hr : Bank540.rho = 301.54258 := by
    norm_num [Bank540.rho, K590.rho, K590.secondCost, D58.wcap, D58.t]
  have hd : D58.delta = 29 / 100000000 := by norm_num [D58.delta, D58.t, D58.deltaRef]
  have h0 : D58.d0 = 53 := rfl
  rw [hr, hd, h0]
  exact payB_of_w _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Gate inequality for the improved budget `tD = tDelta + A`, with `A >= 8.2847` the Theorem A
gain per `N^2` (`A = 58^2 (target0 - target)`), and `g >= 22.05325` the ledger gain. -/
theorem gain_ok417 (g A tD : ℝ) (hT : tD = Bank540.tDelta + A) (h : 2205325 / 100000 ≤ g)
    (hA : 82847 / 10000 ≤ A) : (383257 / 10000 : ℝ) < tD - gDg g := by
  have := eta_lt_of_gain (383257 / 10000 - A) g (by norm_num; linarith)
  rw [hT]; linarith

/-- `w = 3/5`, `B = 410`, `rho' = K590.rhoEnd 87.9663`, `eta = 38.33924`. -/
theorem pay410_w35 :
    PayW (3 / 5) D58.d0 (K590.rhoEnd (879663 / 10000)) (3833924 / 100000)
      (410 / K590.rhoEnd (879663 / 10000)) D58.delta 410 := by
  have hr : K590.rhoEnd (879663 / 10000) = 296586094 / 1000000 := by
    rw [K590.rhoEnd_val]; norm_num
  have hd : D58.delta = 29 / 100000000 := by norm_num [D58.delta, D58.t, D58.deltaRef]
  have h0 : D58.d0 = 53 := rfl
  rw [hr, hd, h0]
  exact payB_of_w _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Gate inequality for `B = 410`: with the Theorem A gain `A >= 8.29824` per `N^2`
(`A = 58^2 (target0 - K590.target)`) and the ledger gain `g >= 22.05325`. -/
theorem gain_ok410 (g A tD : ℝ) (hT : tD = Bank540.tDelta + A) (h : 2205325 / 100000 ≤ g)
    (hA : 829824 / 100000 ≤ A) : (3833924 / 100000 : ℝ) < tD - gDg g := by
  have := eta_lt_of_gain (3833924 / 100000 - A) g (by norm_num; linarith)
  rw [hT]; linarith

end
end CatalanMeasure.GenD.Signed
#print axioms CatalanMeasure.GenD.Signed.payB_of_w
#print axioms CatalanMeasure.GenD.Signed.pay417_w35
#print axioms CatalanMeasure.GenD.Signed.gain_ok417
#print axioms CatalanMeasure.GenD.Signed.pay410_w35
#print axioms CatalanMeasure.GenD.Signed.gain_ok410
