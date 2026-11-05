module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.LinkP
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeC

/-!
# D2 constants: the dual norm `H = certH` of a certificate as a rational sum

`certH_gcert`: `certH g.length (gcertG e g) = Hq g e` for rational `e`;
`certH_mul_le`: from `Hq g e * Dm <= s^2` and `0 <= D <= Dm`, `certH * D <= s^2`
(the field `hsP / hsM / hsT` of `LinkCert` with `Dcap <= Dm`).
`Hq_mono`: `Hq g` is monotone in the damping `e` on `[0, 1)` (`G_k = g_k / (1 - e)^(k+1)`), so
`certH_mul_le_mono` gives the field at every smaller damping `e' <= e` (the `LinkStat*` certificates
at `e = 2^-20` serve `LinkCert` at `e = 2^-30`).
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

open Set CatalanMeasure.Signed

def Hq (g : List ℚ) (e : ℚ) : ℚ :=
  idxSum (fun k x => (x / (1 - e) ^ (k + 1)) ^ 2 * ((k : ℚ) + 1)) g 0

theorem certH_gcert (e : ℚ) (g : List ℚ) : certH g.length (gcertG (e : ℝ) g) = (Hq g e : ℝ) := by
  rw [Hq, idxSum_cast]
  unfold certH
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [gcertG, zero_add]
  push_cast
  ring

theorem Hq_nonneg (e : ℚ) (he : e < 1) (g : List ℚ) : 0 ≤ Hq g e := by
  have key : ∀ (k0 : ℕ) (l : List ℚ),
      0 ≤ idxSum (fun k x => (x / (1 - e) ^ (k + 1)) ^ 2 * ((k : ℚ) + 1)) l k0 := by
    intro k0 l
    induction l generalizing k0 with
    | nil => simp [idxSum]
    | cons x xs ih =>
      simp only [idxSum]
      have : 0 ≤ (x / (1 - e) ^ (k0 + 1)) ^ 2 * ((k0 : ℚ) + 1) := by positivity
      exact add_nonneg this (ih (k0 + 1))
  exact key 0 g

theorem certH_mul_le {e : ℚ} {g : List ℚ} {s Dm D : ℚ} (hD : 0 ≤ D) (hDm : D ≤ Dm)
    (hs : Hq g e * Dm ≤ s ^ 2) (he : e < 1) :
    certH g.length (gcertG (e : ℝ) g) * (D : ℝ) ≤ (s : ℝ) ^ 2 := by
  rw [certH_gcert]
  have h0 := Hq_nonneg e he g
  have : Hq g e * D ≤ s ^ 2 := le_trans (mul_le_mul_of_nonneg_left hDm h0) hs
  exact_mod_cast this

/-- `Hq g` is monotone in the damping: `0 <= e' <= e < 1` gives `Hq g e' <= Hq g e`. -/
theorem Hq_mono {e' e : ℚ} (he' : 0 ≤ e') (hee : e' ≤ e) (he : e < 1) (g : List ℚ) :
    Hq g e' ≤ Hq g e := by
  have term : ∀ (k : ℕ) (x : ℚ), (x / (1 - e') ^ (k + 1)) ^ 2 * ((k : ℚ) + 1) ≤
      (x / (1 - e) ^ (k + 1)) ^ 2 * ((k : ℚ) + 1) := by
    intro k x
    have h0 : 0 < (1 - e) ^ (k + 1) := pow_pos (by linarith) _
    have h1 : (1 - e) ^ (k + 1) ≤ (1 - e') ^ (k + 1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    rw [div_pow, div_pow]
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (sq_nonneg x) (pow_pos h0 2) (pow_le_pow_left₀ h0.le h1 2))
      (by positivity)
  have key : ∀ (k0 : ℕ) (l : List ℚ),
      idxSum (fun k x => (x / (1 - e') ^ (k + 1)) ^ 2 * ((k : ℚ) + 1)) l k0 ≤
        idxSum (fun k x => (x / (1 - e) ^ (k + 1)) ^ 2 * ((k : ℚ) + 1)) l k0 := by
    intro k0 l
    induction l generalizing k0 with
    | nil => simp [idxSum]
    | cons x xs ih =>
      simp only [idxSum]
      exact add_le_add (term k0 x) (ih (k0 + 1))
  exact key 0 g

/-- `certH_mul_le` at a smaller damping: a certificate `Hq g e * Dm <= s^2` (e.g. `LinkStat*` at
`e = 2^-20`) gives the `LinkCert` field at every `e'` with `0 <= e' <= e` (e.g. `e' = 2^-30`). -/
theorem certH_mul_le_mono {e' e : ℚ} {g : List ℚ} {s Dm D : ℚ} (hD : 0 ≤ D) (hDm : D ≤ Dm)
    (hs : Hq g e * Dm ≤ s ^ 2) (he' : 0 ≤ e') (hee : e' ≤ e) (he : e < 1) :
    certH g.length (gcertG (e' : ℝ) g) * (D : ℝ) ≤ (s : ℝ) ^ 2 :=
  certH_mul_le hD hDm
    ((mul_le_mul_of_nonneg_right (Hq_mono he' hee he g) (hD.trans hDm)).trans hs)
    (lt_of_le_of_lt hee he)

end CatalanMeasure.Signed.Consts
