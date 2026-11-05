module

public import Submission.CatalanMeasure.GenD.Signed.Data.S1.Bridge

@[expose] public section

/-!
# S1: column weights of the gap nodes with a nudged keyhole radius (lane D3)

`gap_hW_of_keyhole` needs the keyhole circle `|z| = r` at a constant distance `delta` from the moduli
of the roots of `T_K(arg)`.  For `r > a` (all radii of the S1 cover, `0.45 <= r <= 0.9`, `a = 0.3128`)
the moduli are dense in `[a, 1]`, so no constant `delta` exists.  The paper chooses the radius
`rho_N` in `[r0, r1]` at distance `>= c/N` from every modulus.  Here:

* the circle cover is made at `r1` (`GapCircleBound P a r1 C wc`), extended to every `rho <= r1` by the
  maximum modulus principle (`gapCircleBound_mono`),
* the segment cover and the exponent rate `keyholeRate r0` are those of the lower end `r0`,
* the radius is chosen by pigeonhole (`exists_sep_radius`), `delta_N = (r1 - r0)/(2(K+1))`.

Result `gap_hW_nudged`: the same column bound as `gap_hW_of_keyhole` (`C0 N^5 exp(n omega)`).
-/

namespace CatalanMeasure.GenD.Signed.Data.S1
open Polynomial CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric OAI.InternalCatalan
open Filter Set

noncomputable section

/-- `rho^A / rho^B <= max 1 (r0^A / r0^B)` for `r0 <= rho <= 1`. -/
theorem ratio_mono {r0 ρ : ℝ} (hr0 : 0 < r0) (h1 : r0 ≤ ρ) (h2 : ρ ≤ 1) (A B : ℕ) :
    max 1 (ρ ^ A / ρ ^ B) ≤ max 1 (r0 ^ A / r0 ^ B) := by
  have hρ : 0 < ρ := lt_of_lt_of_le hr0 h1
  rcases le_total A B with hAB | hBA
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hAB
    have e : ∀ x : ℝ, 0 < x → x ^ A / x ^ (A + d) = 1 / x ^ d := by
      intro x hx; rw [pow_add]; field_simp
    rw [e ρ hρ, e r0 hr0]
    exact max_le_max le_rfl (one_div_le_one_div_of_le (pow_pos hr0 d) (pow_le_pow_left₀ hr0.le h1 d))
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hBA
    have e : ρ ^ (B + d) / ρ ^ B = ρ ^ d := by rw [pow_add]; field_simp
    rw [e]
    exact le_trans (max_le le_rfl (pow_le_one₀ hρ.le h2)) (le_max_left _ _)

/-- **Column weight bound for the gap nodes with a nudged keyhole radius.**  Circle cover at `r1`,
segment cover from `r0`, `0 < r0 < r1 <= 1`; the constant is explicit. -/
theorem gap_hW_nudged (P : Parameters) (hg : P.g0 ≤ P.n0) (hn0' : 0 < P.n0)
    {a r0 r1 C wc C' wc' : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (ha4 : 1 - a ^ 2 ≤ 4 * a)
    (hr0 : 0 < r0) (hr01 : r0 < r1) (hr1 : r1 ≤ 1) (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hcirc : GapCircleBound P a r1 C wc) (hseg : GapSegBound P a r0 C' wc') :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, k < P.n N → ∀ j : Fin ((P.n0 - P.g0) * N),
      |(rowCommonFactor P N).eval (gapNodesD P a N j)| *
        |restrictedWeight P N k (gapNodesD P a N) j| ≤
      (4 * (1 + (P.n0 : ℝ)) * (2 * C * (4 * (P.n0 : ℝ) / (r1 - r0)) ^ 2 +
          512 * (P.n0 : ℝ) ^ 4 * Real.exp (gapSegConst a) * C')) * (N : ℝ) ^ 5 *
        Real.exp ((P.n N : ℝ) * (keyholeRate P.g0 P.n0 r0 ((k : ℝ) / P.n N) +
          max wc wc' / P.n0)) := by
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN k hk j
  have hn : (P.n N : ℝ) = (P.n0 : ℝ) * N := by simp [Parameters.n]
  have hn0 : (0 : ℝ) < P.n0 := by exact_mod_cast hn0'
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNn : (0 : ℝ) < N := by linarith
  set Kn : ℕ := ((P.n0 - P.g0) * N + 1) / 2 with hKn
  set L : ℝ := r1 - r0 with hL
  have hL0 : 0 < L := sub_pos.mpr hr01
  have hL1 : L ≤ 1 := by rw [hL]; linarith only [hr0, hr1]
  obtain ⟨ρ, hρmem, hρsep⟩ := exists_sep_radius (posNode a Kn) hr01
  set δ : ℝ := L / (2 * ((Kn : ℝ) + 1)) with hδ
  have hKn1 : (0 : ℝ) < (Kn : ℝ) + 1 := by positivity
  have hδ0 : 0 < δ := div_pos hL0 (by positivity)
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one (by positivity)]
    have : (0 : ℝ) ≤ Kn := Nat.cast_nonneg _
    nlinarith only [hL1, this]
  have hρ0 : 0 < ρ := lt_of_lt_of_le hr0 hρmem.1
  have hcircρ := gapCircleBound_mono hcirc hρ0 hρmem.2
  have hsegρ : GapSegBound P a ρ C' wc' := fun N' x hN' hx hx1 =>
    hseg N' x hN' (le_trans hρmem.1 hx) hx1
  have hmain := gap_weight_joint_keyhole_seg_le P hg ha0 ha1 ha4 hρ0 (hρmem.2.trans hr1) hδ0 hδ1
    hcircρ hsegρ N k j (fun i => hρsep i)
  refine hmain.trans ?_
  set Kc : ℝ := (Kn : ℝ) with hKc
  have hK : Kc ≤ (P.n0 : ℝ) * N := by
    rw [hKc, hKn]
    have : ((P.n0 - P.g0) * N + 1) / 2 ≤ P.n0 * N := by
      have h1 : (P.n0 - P.g0) * N ≤ P.n0 * N := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      have h2 : 1 ≤ P.n0 * N := Nat.mul_pos hn0' hN
      omega
    exact_mod_cast this
  have hK0 : 0 ≤ Kc := Nat.cast_nonneg _
  set wm : ℝ := max wc wc' with hwm
  have hJ : (((P.b N + k + P.q N - P.A N : ℕ)) : ℝ) ≤ (P.n0 : ℝ) * N := by
    have : P.b N + k + P.q N - P.A N ≤ P.n N := by
      simp only [Parameters.A, Parameters.n] at *
      omega
    rw [← hn]; exact_mod_cast this
  have hκ0 := max_one_ratio_le_exp_rate P hn0' hr0 (hr01.le.trans hr1) N k hN
  have hκ : max 1 (ρ ^ P.A N / ρ ^ (P.b N + k + P.q N)) ≤
      Real.exp ((P.n N : ℝ) * keyholeRate P.g0 P.n0 r0 ((k : ℝ) / P.n N)) :=
    (ratio_mono hr0 hρmem.1 (hρmem.2.trans hr1) _ _).trans hκ0
  have hE1 : Real.exp (wc * N) ≤ Real.exp (wm * N) :=
    Real.exp_le_exp.mpr (by nlinarith only [le_max_left wc wc', hNn])
  have hE2 : Real.exp (wc' * N) ≤ Real.exp (wm * N) :=
    Real.exp_le_exp.mpr (by nlinarith only [le_max_right wc wc', hNn])
  have hN2 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
  have hN4 : (1 : ℝ) ≤ (N : ℝ) ^ 4 := one_le_pow₀ hN1
  -- 1 / delta <= 4 n0 N / L
  have hinv : 1 / δ ≤ 4 * (P.n0 : ℝ) * N / L := by
    rw [hδ, one_div_div, div_le_div_iff₀ hL0 hL0]
    have : (Kn : ℝ) + 1 ≤ 2 * ((P.n0 : ℝ) * N) := by
      have hn01 : (1 : ℝ) ≤ P.n0 := by exact_mod_cast hn0'
      have : (1 : ℝ) ≤ (P.n0 : ℝ) * N := by nlinarith only [hn01, hN1]
      linarith only [hK, hKc, this]
    nlinarith only [this, hL0]
  set CsA : ℝ := 2 * C * (4 * (P.n0 : ℝ) / L) ^ 2 with hCsA
  have hCsA0 : 0 ≤ CsA := by positivity
  have hδ2 : 2 * C / δ ^ 2 ≤ CsA * (N : ℝ) ^ 2 := by
    have hδp : 0 < 1 / δ := by positivity
    calc 2 * C / δ ^ 2 = 2 * C * (1 / δ) ^ 2 := by field_simp
      _ ≤ 2 * C * (4 * (P.n0 : ℝ) * N / L) ^ 2 := by gcongr
      _ = CsA * (N : ℝ) ^ 2 := by rw [hCsA]; field_simp
  set Cs0 : ℝ := CsA + 512 * (P.n0 : ℝ) ^ 4 * Real.exp (gapSegConst a) * C' with hCs0
  have hz : 0 ≤ 512 * (P.n0 : ℝ) ^ 4 * Real.exp (gapSegConst a) * C' := by positivity
  have hM : 2 * (C * Real.exp (wc * N)) / δ ^ 2 ≤ Cs0 * ((N : ℝ) ^ 4 * Real.exp (wm * N)) := by
    have h0 : 2 * (C * Real.exp (wc * N)) / δ ^ 2 ≤ CsA * (N : ℝ) ^ 2 * Real.exp (wm * N) := by
      rw [show 2 * (C * Real.exp (wc * N)) / δ ^ 2 = 2 * C / δ ^ 2 * Real.exp (wc * N) by ring]
      calc _ ≤ CsA * (N : ℝ) ^ 2 * Real.exp (wc * N) :=
            mul_le_mul_of_nonneg_right hδ2 (Real.exp_pos _).le
        _ ≤ _ := by gcongr
    have hpos : 0 ≤ (N : ℝ) ^ 4 * Real.exp (wm * N) := by positivity
    calc _ ≤ CsA * (N : ℝ) ^ 2 * Real.exp (wm * N) := h0
      _ ≤ CsA * (N : ℝ) ^ 4 * Real.exp (wm * N) := by gcongr
      _ = CsA * ((N : ℝ) ^ 4 * Real.exp (wm * N)) := by ring
      _ ≤ _ := by nlinarith only [mul_nonneg hz hpos]
  have hB : 512 * Kc ^ 4 * Real.exp (gapSegConst a) * (C' * Real.exp (wc' * N)) ≤
      Cs0 * ((N : ℝ) ^ 4 * Real.exp (wm * N)) := by
    have hK4 : Kc ^ 4 ≤ ((P.n0 : ℝ) * N) ^ 4 := pow_le_pow_left₀ hK0 hK 4
    have h1 : 512 * Kc ^ 4 * Real.exp (gapSegConst a) * (C' * Real.exp (wc' * N)) ≤
        512 * ((P.n0 : ℝ) * N) ^ 4 * Real.exp (gapSegConst a) * (C' * Real.exp (wm * N)) := by
      gcongr
    have h2 : 512 * ((P.n0 : ℝ) * N) ^ 4 * Real.exp (gapSegConst a) * (C' * Real.exp (wm * N)) =
        (512 * (P.n0 : ℝ) ^ 4 * Real.exp (gapSegConst a) * C') *
          ((N : ℝ) ^ 4 * Real.exp (wm * N)) := by ring
    have hpos : 0 ≤ (N : ℝ) ^ 4 * Real.exp (wm * N) := by positivity
    calc _ ≤ _ := h1
      _ = _ := h2
      _ ≤ _ := by nlinarith only [mul_nonneg hCsA0 hpos]
  have hmaxle : max (2 * (C * Real.exp (wc * N)) / δ ^ 2)
      (512 * Kc ^ 4 * Real.exp (gapSegConst a) * (C' * Real.exp (wc' * N))) ≤
      Cs0 * ((N : ℝ) ^ 4 * Real.exp (wm * N)) := max_le hM hB
  have hexp : Real.exp ((P.n N : ℝ) * (keyholeRate P.g0 P.n0 r0 ((k : ℝ) / P.n N) +
        wm / P.n0)) =
      Real.exp ((P.n N : ℝ) * keyholeRate P.g0 P.n0 r0 ((k : ℝ) / P.n N)) *
        Real.exp (wm * N) := by
    rw [← Real.exp_add]; congr 1; rw [hn]; field_simp
  rw [hexp]
  have hCs00 : 0 ≤ Cs0 := by positivity
  have h4 : 4 * (1 + (((P.b N + k + P.q N - P.A N : ℕ)) : ℝ)) ≤
      4 * (1 + (P.n0 : ℝ)) * N := by nlinarith only [hJ, hN1, hn0]
  have hE : 0 ≤ Real.exp ((P.n N : ℝ) * keyholeRate P.g0 P.n0 r0 ((k : ℝ) / P.n N)) :=
    (Real.exp_pos _).le
  calc _ ≤ (4 * (1 + (P.n0 : ℝ)) * N) *
        (Real.exp ((P.n N : ℝ) * keyholeRate P.g0 P.n0 r0 ((k : ℝ) / P.n N)) *
          (Cs0 * ((N : ℝ) ^ 4 * Real.exp (wm * N)))) := by
        apply mul_le_mul h4 _ (by positivity) (by positivity)
        exact mul_le_mul hκ hmaxle (le_max_of_le_left (by positivity)) hE
    _ = _ := by rw [hCs0, hCsA]; ring

end

end CatalanMeasure.GenD.Signed.Data.S1
