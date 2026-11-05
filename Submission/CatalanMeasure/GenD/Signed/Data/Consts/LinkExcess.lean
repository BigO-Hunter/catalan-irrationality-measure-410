module

public import Submission.CatalanMeasure.GenD.Signed.Phase2Contract

/-!
# D2 constants: `Dtop`, `Dcap` of `LinkCert` (the excess is affine in `alpha`)

`excess target cost t0 c2 delta n0 alpha = (t0 - target + delta) + (cost - c2/n0) alpha`, so
* with `c2 = n0 * cost` it is the constant `t0 - target + delta` (`excess_const`);
* in general its supremum over an interval is attained at an endpoint (`excess_le_of_ends`).

B = 410 choice (DRYRUN-410 L2, L9): `Dtop = Dcap = 13/5000` (`excess_le_dtop410`: the excess
`A/3364 + δ` with `A ≤ 8.29824`, `δ ≤ 1.3e-4` is at most `0.0026`), and the spike-count cap
`Mmax N = ⌈s·58N + 1⌉` with slope `s = Dtop/dsp + C1 θ0` (`mmaxOf`): `hMmax` holds for every `N`
(`mmaxOf_ge`), and the piece range `50 (Mmax N + 1) ≤ 57 N` of `hcert_form` holds for all large `N`
as soon as `2900 s < 57` (`mmaxOf_hMm`), i.e. `Dtop < 0.002745` at `dsp = 18/125`; `s410` is the 410 slope
(`dsp = 18/125` (`LinkSup*`), `C1 = 9631/20000`, `θ0 = 1/1000`).
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

open Set CatalanMeasure.Signed

theorem excess_const {target cost t0 c2 δ n0 : ℝ} (α : ℝ) (hn0 : n0 ≠ 0) (hc2 : c2 = n0 * cost) :
    excess target cost t0 c2 δ n0 α = t0 - target + δ := by
  unfold excess
  rw [hc2]
  field_simp
  ring

theorem excess_le_of_ends {target cost t0 c2 δ n0 lo hi α D : ℝ} (hα : α ∈ Icc lo hi)
    (hlo : excess target cost t0 c2 δ n0 lo ≤ D) (hhi : excess target cost t0 c2 δ n0 hi ≤ D) :
    excess target cost t0 c2 δ n0 α ≤ D := by
  unfold excess at *
  obtain ⟨h1, h2⟩ := hα
  set s : ℝ := cost - c2 / n0 with hs
  have e : ∀ x : ℝ, (-target + Real.log 2 / 2 + cost * x + δ) - ((-t0 + Real.log 2 / 2) + c2 * x / n0)
      = (t0 - target + δ) + s * x := fun x => by rw [hs]; ring
  rw [e] at hlo hhi ⊢
  rcases le_total 0 s with hs0 | hs0
  · nlinarith [mul_le_mul_of_nonneg_left h2 hs0]
  · nlinarith [mul_le_mul_of_nonneg_left h1 (neg_nonneg.2 hs0)]

/-- `Dtop = Dcap = 0.0026` for B = 410: with `c2 = n0 cost` the excess is `t0 - target + δ`, and
`3364 (t0 - target) ≤ 8.29824`, `δ ≤ 1.3e-4` give at most `0.0026`. -/
theorem excess_le_dtop410 {target cost t0 c2 δ n0 : ℝ} (α : ℝ) (hn0 : n0 ≠ 0) (hc2 : c2 = n0 * cost)
    (hA : (t0 - target) * 3364 ≤ 829824 / 100000) (hδ : δ ≤ 13 / 100000) :
    excess target cost t0 c2 δ n0 α ≤ 13 / 5000 := by
  rw [excess_const α hn0 hc2]
  linarith

/-- The spike-count cap `Mmax N = ⌈s · 58 N + 1⌉` (`s = Dtop/dsp + C1 θ0`). -/
noncomputable def mmaxOf (s : ℝ) (N : ℕ) : ℕ := ⌈s * (58 * (N : ℝ)) + 1⌉₊

/-- `hMmax` of `LinkCert` (with `P.n N = 58 N`). -/
theorem mmaxOf_ge (s : ℝ) (N : ℕ) : s * (58 * (N : ℝ)) + 1 ≤ (mmaxOf s N : ℝ) :=
  Nat.le_ceil _

/-- The piece range of `hcert_form`, eventually: `50 (Mmax N + 1) ≤ 57 N` for all large `N` when
`2900 s < 57`. -/
theorem mmaxOf_hMm {s : ℝ} (hs : 0 ≤ s) (hs1 : 2900 * s < 57) :
    ∀ᶠ N : ℕ in Filter.atTop, 50 * (mmaxOf s N + 1) ≤ 57 * N := by
  have hd : 0 < 57 - 2900 * s := by linarith
  filter_upwards [Filter.eventually_ge_atTop ⌈150 / (57 - 2900 * s)⌉₊] with N hN
  have hN' : 150 / (57 - 2900 * s) ≤ (N : ℝ) := (Nat.ceil_le).1 hN
  have h1 : 150 ≤ (57 - 2900 * s) * N := by rwa [div_le_iff₀ hd, mul_comm] at hN'
  have hx : 0 ≤ s * (58 * (N : ℝ)) + 1 := by positivity
  have h2 : (mmaxOf s N : ℝ) < s * (58 * (N : ℝ)) + 1 + 1 := Nat.ceil_lt_add_one hx
  have h3 : (50 : ℝ) * ((mmaxOf s N : ℝ) + 1) ≤ 57 * (N : ℝ) := by nlinarith
  exact_mod_cast h3

/-- The B = 410 slope `Dtop/dsp + C1 θ0` with `Dtop = 13/5000`, `dsp = 18/125`,
`C1 = 9631/20000`, `θ0 = 1/1000`. -/
noncomputable def s410 : ℝ := 13 / 5000 / (18 / 125) + 9631 / 20000 * (1 / 1000)

theorem s410_nonneg : 0 ≤ s410 := by unfold s410; norm_num

theorem s410_lt : 2900 * s410 < 57 := by unfold s410; norm_num

theorem mmax410_hMm : ∀ᶠ N : ℕ in Filter.atTop, 50 * (mmaxOf s410 N + 1) ≤ 57 * N :=
  mmaxOf_hMm s410_nonneg s410_lt

end CatalanMeasure.Signed.Consts
