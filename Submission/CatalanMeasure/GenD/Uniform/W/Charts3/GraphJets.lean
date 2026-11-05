module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts3.GraphB
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts3.Flags
@[expose] public section
set_option Elab.async false

/-!
# `hG` from jets at `1`

If the functional `low` (the `@low:raw` coordinate) satisfies the order-`(p-r)` jet conditions at `1`
(`low (taylorJet 1 k x) = 0`, `k < p - r`: these are the packet's `jet_0`/graph rows at the point `1`),
then its coefficient window is a polynomial: `low (x e) = G(η - e)` with `deg G < r`.
This is the `hG` hypothesis of `monoHost`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts3
open Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

theorem coeffPoly_taylor (c : Fin p → Fp) (k : ℕ) :
    (taylor 1 (∑ e : Fin p, C (c e) * X ^ (e : ℕ))).coeff k =
      ∑ e : Fin p, ((e : ℕ).choose k : Fp) * c e := by
  rw [taylor_coeff, map_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Polynomial.C_mul_X_pow_eq_monomial, hasseDeriv_monomial, Polynomial.eval_monomial]
  simp [nsmul_eq_mul, mul_comm]

theorem hG_of_taylor {d : ℕ} (low : (Fin d → Fp) →ₗ[Fp] Fp) (η : Fp) (r : ℕ) (hr : r ≤ p)
    (x : Fin p → Fin d → Fp) (h : ∀ k < p - r, low (taylorJet (1 : Fp) k x) = 0) :
    ∃ G : Fp[X], G.degree < (r : WithBot ℕ) ∧
      ∀ e : Fin p, G.eval (η - ((e : ℕ) : Fp)) = low (x e) := by
  set g : Fp[X] := ∑ e : Fin p, C (low (x e)) * X ^ (e : ℕ) with hg
  have hdeg : g.degree < p := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro e _
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
    exact_mod_cast e.isLt
  have hdvd : (X - 1 : Fp[X]) ^ (p - r) ∣ g := by
    rw [show (X - 1 : Fp[X]) = X - C 1 by simp, pow_dvd_iff_taylor]
    intro k hk
    rw [hg, coeffPoly_taylor]
    have := h k hk
    rw [taylorJet] at this
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, map_sum,
      map_smul, one_pow, mul_one, smul_eq_mul] at this
    rw [← this]
  obtain ⟨G, hGd, hGe⟩ := window_poly η r hr g hdeg hdvd
  refine ⟨G, hGd, fun e => ?_⟩
  rw [← hGe e, hg]
  rw [Polynomial.finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single e]
  · simp
  · intro b _ hb
    have : (e : ℕ) ≠ (b : ℕ) := fun h' => hb (Fin.ext h'.symm)
    simp [this]
  · simp

end
end CatalanMeasure.GenD.Uniform.W.Charts3
