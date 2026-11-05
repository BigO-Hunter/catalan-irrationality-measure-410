module

public import Submission.CatalanMeasure.GenD.Analytic.GapCircleGen
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# S1 data bridge, generic part (lane D3)

Statements shared by every radius cell of the S1 weight cover (`Psi` certificate):

* `rat_le_exp_of_pow`: a rational `E` below `e1^k * (12-term Taylor sum of f)` is below `exp (k + f)`
  (turns the checked integer `E` of a circle cover into the exponent `wc`);
* `gapCircleBound_mono`: a circle cover at radius `r` gives the bound on every circle of radius `<= r`
  (maximum modulus), which lets the radius of the keyhole be nudged by `o(1)` to avoid the node moduli;
* `exists_sep_radius`: a radius in `[r0, r1]` at distance `>= (r1-r0)/(2(K+1))` from `K` points;
* `gapSegBound_triv`: for `a <= r` the segment bound `GapSegBound P a r 1 (416/100)` (there `g = 1`).
-/

namespace CatalanMeasure.GenD.Signed.Data.S1
open Polynomial CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric OAI.InternalCatalan
open Filter Set

noncomputable section

/-- `E <= e1^k * Taylor_12(f)` gives `E <= exp (k + f)`. -/
theorem rat_le_exp_of_pow (E f : ℚ) (k : ℕ) (hf : 0 ≤ f)
    (h : E ≤ (27182818283 / 10 ^ 10 : ℚ) ^ k *
      ∑ i ∈ Finset.range 12, f ^ i / (i.factorial : ℚ)) :
    (E : ℝ) ≤ Real.exp ((k : ℝ) + (f : ℝ)) := by
  have h1 : (2.7182818283 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
  have h2 := Real.sum_le_exp_of_nonneg (x := (f : ℝ)) (by exact_mod_cast hf) 12
  have h3 : (2.7182818283 : ℝ) ^ k ≤ Real.exp k := by
    calc _ ≤ Real.exp 1 ^ k := pow_le_pow_left₀ (by norm_num) h1 k
      _ = _ := by rw [← Real.exp_nat_mul]; simp
  have h4 := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at h4
  rw [Real.exp_add]
  have e1 : ((27182818283 : ℝ) / 10 ^ 10) = 2.7182818283 := by norm_num
  rw [e1] at h4
  calc (E : ℝ) ≤ _ := h4
    _ ≤ Real.exp k * Real.exp (f : ℝ) :=
        mul_le_mul h3 h2 (Finset.sum_nonneg (fun i _ => by
          have : (0 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
          positivity)) (Real.exp_pos _).le

/-- Maximum modulus: a circle cover at radius `r` bounds every smaller circle. -/
theorem gapCircleBound_mono {P : Parameters} {a r C wc ρ : ℝ} (h : GapCircleBound P a r C wc)
    (hρ0 : 0 < ρ) (hρ : ρ ≤ r) : GapCircleBound P a ρ C wc := by
  unfold GapCircleBound at h ⊢
  intro N z hN hz
  have hr0 : 0 < r := lt_of_lt_of_le hρ0 hρ
  set Q : ℂ[X] := ((gapPolyK a (((P.n0 - P.g0) * N + 1) / 2)).map (algebraMap ℝ ℂ)) *
      ((1 : ℂ[X]) - X) ^ (P.h N + P.q N) with hQ
  have hevQ : ∀ w : ℂ, ‖Q.eval w‖ =
      ‖((gapPolyK a (((P.n0 - P.g0) * N + 1) / 2)).map (algebraMap ℝ ℂ)).eval w‖ *
        ‖(1 : ℂ) - w‖ ^ (P.h N + P.q N) := by
    intro w
    simp [hQ, norm_mul, norm_pow]
  have hball : ∀ w : ℂ, ‖w‖ ≤ r → ‖Q.eval w‖ ≤ C * Real.exp (wc * N) := by
    intro w hw
    refine Complex.norm_le_of_forall_mem_frontier_norm_le
      (f := fun w : ℂ => Q.eval w) (U := Metric.ball (0 : ℂ) r) (Metric.isBounded_ball) ?_ ?_ ?_
    · exact (Polynomial.differentiable _).diffContOnCl
    · intro w hw
      rw [frontier_ball _ hr0.ne'] at hw
      have hb := h N w hN (by simpa using hw)
      show ‖Q.eval w‖ ≤ _
      rw [hevQ]
      exact hb
    · rw [closure_ball _ hr0.ne']
      simpa using hw
  have := hball z (by rw [hz]; exact hρ)
  rwa [hevQ] at this

/-- Pigeonhole: among `r0, r0 + s, ..., r0 + K s` (`s = (r1 - r0)/(K+1)`) one candidate is at
distance `>= s/2` from each of `K` points. -/
theorem exists_sep_radius {K : ℕ} (p : Fin K → ℝ) {r0 r1 : ℝ} (h : r0 < r1) :
    ∃ ρ ∈ Icc r0 r1, ∀ i, (r1 - r0) / (2 * ((K : ℝ) + 1)) ≤ |p i - ρ| := by
  classical
  set s : ℝ := (r1 - r0) / ((K : ℝ) + 1) with hs
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hs0 : 0 < s := div_pos (sub_pos.mpr h) hK1
  set m : Fin K → ℕ := fun i => (⌊(p i - r0) / s + 1 / 2⌋).toNat with hm
  have hcard : (Finset.univ.image m).card < (Finset.range (K + 1)).card := by
    calc (Finset.univ.image m).card ≤ (Finset.univ : Finset (Fin K)).card := Finset.card_image_le
      _ = K := by simp
      _ < _ := by simp
  obtain ⟨j, hj, hjn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hjK : j ≤ K := by simpa [Nat.lt_succ_iff] using hj
  refine ⟨r0 + j * s, ⟨by nlinarith only [hs0, Nat.cast_nonneg (α := ℝ) j], ?_⟩, ?_⟩
  · have : (j : ℝ) ≤ K := by exact_mod_cast hjK
    have : r0 + j * s ≤ r0 + K * s := by nlinarith only [hs0, this]
    have e : r0 + K * s = r1 - s := by rw [hs]; field_simp; ring
    linarith only [this, e, hs0]
  · intro i
    have hne : m i ≠ j := fun hh => hjn (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hh⟩)
    set x : ℝ := (p i - r0) / s + 1 / 2 with hx
    set F : ℤ := ⌊x⌋ with hF
    have hF1 : (F : ℝ) ≤ x := Int.floor_le x
    have hF2 : x < F + 1 := Int.lt_floor_add_one x
    have hpi : p i - r0 = (x - 1 / 2) * s := by rw [hx]; field_simp; ring
    have hd : (r1 - r0) / (2 * ((K : ℝ) + 1)) = s / 2 := by rw [hs]; field_simp
    rw [hd]
    have key : s / 2 ≤ |(x - 1 / 2) * s - j * s| := by
      have : |(x - 1 / 2) * s - j * s| = |x - 1 / 2 - j| * s := by
        rw [← sub_mul, abs_mul, abs_of_pos hs0]
      rw [this]
      have : (1 : ℝ) / 2 ≤ |x - 1 / 2 - j| := by
        rcases lt_or_ge F 0 with hneg | hnn
        · have hmz : m i = 0 := by
            simp only [hm]; exact Int.toNat_of_nonpos hneg.le
          have hj1 : (1 : ℝ) ≤ j := by
            have : j ≠ 0 := fun hh => hne (by rw [hmz, hh])
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
          have hF' : (F : ℝ) ≤ -1 := by exact_mod_cast (show F ≤ -1 by omega)
          rw [abs_of_neg (by linarith only [hF2, hF', hj1])]
          linarith only [hF2, hF', hj1]
        · have hmF : ((m i : ℕ) : ℤ) = F := by
            simp only [hm]; exact Int.toNat_of_nonneg hnn
          have hjF : (j : ℤ) ≠ F := fun hh => hne (by
            have : ((m i : ℕ) : ℤ) = (j : ℤ) := by rw [hmF, hh]
            exact_mod_cast this)
          rcases lt_or_gt_of_ne hjF with hlt | hgt
          · have : (j : ℝ) ≤ F - 1 := by exact_mod_cast (show (j : ℤ) ≤ F - 1 by omega)
            rw [abs_of_nonneg (by linarith only [hF1, this])]
            linarith only [hF1, this]
          · have : (F : ℝ) + 1 ≤ j := by exact_mod_cast (show F + 1 ≤ (j : ℤ) by omega)
            rw [abs_of_neg (by linarith only [hF2, this])]
            linarith only [hF2, this]
      nlinarith only [this, hs0]
    have e : p i - (r0 + j * s) = (x - 1 / 2) * s - j * s := by rw [← sub_sub, hpi]
    rw [e]
    exact key

/-- For `a <= r` the real-segment estimate holds with `C' = 1`, `wc' = 416/100`
(`g(H(x)) = 1` on `a <= |x| <= 1`, `|1 - x| <= 2`, `6 log 2 < 4.16`). -/
theorem gapSegBound_triv (P : Parameters) {a r : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (har : a ≤ r)
    (hq : P.h0 + P.q0 = 6) : GapSegBound P a r 1 (416 / 100) := by
  intro N x hN hrx hx1
  have hax : a ≤ |x| := le_trans har hrx
  have hx2 : x ^ 2 ≤ 1 := by
    have := sq_abs x
    nlinarith only [abs_nonneg x, hx1, this]
  have hxa : a ^ 2 ≤ x ^ 2 := by
    have := sq_abs x
    nlinarith only [hax, ha0, this]
  have hd : 0 < 1 - a ^ 2 := by nlinarith only [ha0, ha1]
  have hH : gapHReal a x = 1 := by
    unfold gapHReal
    rw [abs_of_nonpos (by linarith only [hx2]), abs_of_nonneg (by linarith only [hxa])]
    field_simp
    ring
  have hG : gapG (gapHReal a x) = 1 := by
    rw [hH]; unfold gapG; simp
  rw [hG, one_pow, one_mul]
  have hm : P.h N + P.q N = 6 * N := by
    simp only [Parameters.h, Parameters.q]
    rw [← add_mul, hq]
  rw [hm]
  have h1x : |1 - x| ≤ 2 := by
    have := abs_le.mp hx1
    rw [abs_le]; constructor <;> linarith only [this.1, this.2]
  have h2 : |1 - x| ^ (6 * N) ≤ (2 : ℝ) ^ (6 * N) := pow_le_pow_left₀ (abs_nonneg _) h1x _
  have h3 : (2 : ℝ) ^ (6 * N) ≤ Real.exp (416 / 100 * N) := by
    have e : (2 : ℝ) ^ (6 * N) = Real.exp (((6 * N : ℕ) : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [e]
    apply Real.exp_le_exp.mpr
    have hl := Real.log_two_lt_d9
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    push_cast
    nlinarith only [hl, hN0]
  linarith only [h2, h3]

end

end CatalanMeasure.GenD.Signed.Data.S1
