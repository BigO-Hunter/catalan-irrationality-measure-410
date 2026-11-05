module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Submission.OAI.NumberTheory.Catalan.PrimeLimits.ContinuousWeightedPNT
public import Submission.OAI.NumberTheory.Catalan.PrimeLimits.ImportedPNTCoreBridge

@[expose] public section

/-!
# Piecewise-linear profiles (module 1 of the G-displacement Lean plan)

Design-free.  A *ramp* is `x ↦ max (x - t) 0`.  A profile `Prof` is
`c0 + c1 x + ∑ w_i ramp t_i x`.  Every continuous piecewise-linear function with finitely many
kinks has this form, and its integral over `[a,b]` is given in closed form by
`∫ ramp t = (ramp t b ^ 2 - ramp t a ^ 2) / 2`.  Hence the area of any profile is a finite sum
of rational numbers when the data are rational, and the weighted prime-sum limit
`∑_{aN < p ≤ bN} F (p/N) log p / N → ∫ F` (prime number theorem, via the existing bridge)
holds for it with the closed-form area.
-/

namespace CatalanMeasure.GenD
namespace PL

open Filter MeasureTheory intervalIntegral
open OAI.Zeta5.Workers.W14 OAI.Zeta5.W12.ImportedPNTCoreBridge
open scoped Topology

noncomputable section

/-- The ramp with kink at `t`. -/
def ramp (t x : ℝ) : ℝ := max (x - t) 0

theorem ramp_nonneg (t x : ℝ) : 0 ≤ ramp t x := le_max_right _ _

theorem continuous_ramp (t : ℝ) : Continuous (ramp t) := by
  unfold ramp; fun_prop

theorem ramp_of_le {t x : ℝ} (h : x ≤ t) : ramp t x = 0 :=
  max_eq_right (by linarith)

theorem ramp_of_ge {t x : ℝ} (h : t ≤ x) : ramp t x = x - t :=
  max_eq_left (by linarith)

/-- A weighted sum of ramps; the list entry `(w, t)` is `w * ramp t`. -/
def hinges (L : List (ℝ × ℝ)) (x : ℝ) : ℝ := (L.map fun wt => wt.1 * ramp wt.2 x).sum

@[simp] theorem hinges_nil (x : ℝ) : hinges [] x = 0 := by simp [hinges]

@[simp] theorem hinges_cons (wt : ℝ × ℝ) (L : List (ℝ × ℝ)) (x : ℝ) :
    hinges (wt :: L) x = wt.1 * ramp wt.2 x + hinges L x := by simp [hinges]

theorem continuous_hinges (L : List (ℝ × ℝ)) : Continuous (hinges L) := by
  induction L with
  | nil =>
    have h0 : hinges [] = fun _ => 0 := by funext x; simp
    rw [h0]; exact continuous_const
  | cons wt L ih =>
    have h1 : hinges (wt :: L) = fun x => wt.1 * ramp wt.2 x + hinges L x := by
      funext x; exact hinges_cons wt L x
    rw [h1]
    exact (continuous_const.mul (continuous_ramp _)).add ih

/-- The piecewise-linear profile `c0 + c1 x + ∑ w_i ramp t_i x`. -/
structure Prof where
  c0 : ℝ
  c1 : ℝ
  L : List (ℝ × ℝ)

/-- Value of a profile. -/
def Prof.eval (f : Prof) (x : ℝ) : ℝ := f.c0 + f.c1 * x + hinges f.L x

theorem Prof.continuous (f : Prof) : Continuous f.eval := by
  unfold Prof.eval
  exact (continuous_const.add (continuous_const.mul continuous_id)).add (continuous_hinges _)

/-! ### Integrals -/

theorem integral_ramp {a b : ℝ} (t : ℝ) (hab : a ≤ b) :
    ∫ x in a..b, ramp t x = (ramp t b ^ 2 - ramp t a ^ 2) / 2 := by
  have hlow : ∀ {u v : ℝ}, u ≤ v → v ≤ t → ∫ x in u..v, ramp t x = 0 := by
    intro u v huv hvt
    have : ∫ x in u..v, ramp t x = ∫ x in u..v, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le huv] at hx
      exact ramp_of_le (hx.2.trans hvt)
    simpa using this
  have hhigh : ∀ {u v : ℝ}, t ≤ u → u ≤ v →
      ∫ x in u..v, ramp t x = ((v - t) ^ 2 - (u - t) ^ 2) / 2 := by
    intro u v htu huv
    have h1 : ∫ x in u..v, ramp t x = ∫ x in u..v, (x - t) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le huv] at hx
      exact ramp_of_ge (htu.trans hx.1)
    rw [h1, intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
      intervalIntegrable_const]
    simp only [integral_id, intervalIntegral.integral_const, smul_eq_mul]
    ring
  rcases le_total b t with hbt | htb
  · rw [hlow hab hbt, ramp_of_le hbt, ramp_of_le (hab.trans hbt)]; ring
  · rcases le_total a t with hat | hta
    · rw [← intervalIntegral.integral_add_adjacent_intervals (b := t)
        ((continuous_ramp t).intervalIntegrable _ _) ((continuous_ramp t).intervalIntegrable _ _),
        hlow hat le_rfl, hhigh le_rfl htb, ramp_of_le hat, ramp_of_ge htb]
      ring
    · rw [hhigh hta hab, ramp_of_ge hta, ramp_of_ge (hta.trans hab)]

/-- Closed form for the integral of the ramp part. -/
def hingeInt (L : List (ℝ × ℝ)) (a b : ℝ) : ℝ :=
  (L.map fun wt => wt.1 * ((ramp wt.2 b ^ 2 - ramp wt.2 a ^ 2) / 2)).sum

@[simp] theorem hingeInt_nil (a b : ℝ) : hingeInt [] a b = 0 := by simp [hingeInt]

@[simp] theorem hingeInt_cons (wt : ℝ × ℝ) (L : List (ℝ × ℝ)) (a b : ℝ) :
    hingeInt (wt :: L) a b = wt.1 * ((ramp wt.2 b ^ 2 - ramp wt.2 a ^ 2) / 2) + hingeInt L a b := by
  simp [hingeInt]

theorem integral_hinges (L : List (ℝ × ℝ)) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in a..b, hinges L x = hingeInt L a b := by
  induction L with
  | nil => simp
  | cons wt L ih =>
    simp only [hinges_cons, hingeInt_cons]
    rw [intervalIntegral.integral_add
      (((continuous_ramp _).const_mul _).intervalIntegrable _ _)
      ((continuous_hinges L).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_ramp _ hab, ih]

/-- The area of a profile over `[a,b]`. -/
def Prof.area (f : Prof) (a b : ℝ) : ℝ :=
  f.c0 * (b - a) + f.c1 * ((b ^ 2 - a ^ 2) / 2) + hingeInt f.L a b

theorem Prof.integral_eval (f : Prof) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in a..b, f.eval x = f.area a b := by
  unfold Prof.eval Prof.area
  have hc : Continuous (fun x : ℝ => f.c0 + f.c1 * x) :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hlin : ∫ x in a..b, (f.c0 + f.c1 * x) = f.c0 * (b - a) + f.c1 * ((b ^ 2 - a ^ 2) / 2) := by
    rw [intervalIntegral.integral_add (f := fun _ => f.c0) (g := fun x => f.c1 * x)
      (continuous_const.intervalIntegrable _ _)
      ((continuous_const.mul continuous_id).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_const, smul_eq_mul, integral_id]
    ring
  rw [intervalIntegral.integral_add (hc.intervalIntegrable _ _)
    ((continuous_hinges _).intervalIntegrable _ _), integral_hinges _ hab, hlin]

/-- Weighted prime-sum limit for a profile: `∑_{aN < p ≤ bN} F(p/N) log p / N → area`. -/
theorem Prof.weighted_tendsto (f : Prof) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (weightedPrimeIntervalSum f.eval a b) atTop (𝓝 (f.area a b)) := by
  have h := continuous_weightedPrime_tendsto (F := f.eval) ha hab
    f.continuous.continuousOn theta_ratio_tendsto_one
  rwa [f.integral_eval hab.le] at h

/-! ### Segments: a profile is affine between consecutive kinks -/

/-- Slope contributed by the ramps whose kink is at or left of `u`. -/
def hingeSlope (L : List (ℝ × ℝ)) (u : ℝ) : ℝ :=
  (L.map fun wt => if wt.2 ≤ u then wt.1 else 0).sum

/-- Intercept contributed by the ramps whose kink is at or left of `u`. -/
def hingeIntercept (L : List (ℝ × ℝ)) (u : ℝ) : ℝ :=
  (L.map fun wt => if wt.2 ≤ u then wt.1 * wt.2 else 0).sum

/-- If no kink lies strictly inside `(u,v)`, the ramp part is affine on `[u,v]`.  An instance
evaluates `hingeSlope`/`hingeIntercept` by `norm_num [hingeSlope, hingeIntercept]`. -/
theorem hinges_affine (L : List (ℝ × ℝ)) {u v x : ℝ} (hx : u ≤ x ∧ x ≤ v)
    (hL : ∀ wt ∈ L, wt.2 ≤ u ∨ v ≤ wt.2) :
    hinges L x = hingeSlope L u * x - hingeIntercept L u := by
  induction L with
  | nil => simp [hingeSlope, hingeIntercept]
  | cons wt L ih =>
    have ih' := ih (fun w hw => hL w (List.mem_cons_of_mem _ hw))
    simp only [hinges_cons, hingeSlope, hingeIntercept, List.map_cons, List.sum_cons] at ih' ⊢
    rw [ih']
    rcases hL wt List.mem_cons_self with h | h
    · rw [ramp_of_ge (h.trans hx.1)]
      simp only [h, ↓reduceIte]
      ring
    · by_cases hu : wt.2 ≤ u
      · rw [ramp_of_ge (hu.trans hx.1)]
        simp only [hu, ↓reduceIte]
        ring
      · rw [ramp_of_le (hx.2.trans h)]
        simp only [hu, ↓reduceIte]
        ring

/-- Value of a profile on a segment between kinks. -/
theorem Prof.eval_affine (f : Prof) {u v x : ℝ} (hx : u ≤ x ∧ x ≤ v)
    (hL : ∀ wt ∈ f.L, wt.2 ≤ u ∨ v ≤ wt.2) :
    f.eval x = (f.c1 + hingeSlope f.L u) * x + (f.c0 - hingeIntercept f.L u) := by
  unfold Prof.eval
  rw [hinges_affine f.L hx hL]
  ring

/-- The generic limit for any function continuous on `[a,b]`. -/
theorem weighted_tendsto_of_continuousOn {F : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hF : ContinuousOn F (Set.Icc a b)) :
    Tendsto (weightedPrimeIntervalSum F a b) atTop (𝓝 (∫ x in a..b, F x)) :=
  continuous_weightedPrime_tendsto ha hab hF theta_ratio_tendsto_one

end
end PL
end CatalanMeasure.GenD
