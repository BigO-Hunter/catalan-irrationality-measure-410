module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts3.DomJets
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Roots
@[expose] public section
set_option Elab.async false

/-!
# The `B`-graph encoding: `(y-1)^(p-r) Poly_{<r}` is the set of polynomial coefficient windows

For `q = a p + r` the `B(l)` of the filter (paper §3, §6) is a polynomial of degree `< r` in `l`; it is
carried by one extra coordinate of the packet as the coefficient vector
`g(y) = Σ_{e<p} B(η - e) y^e`.  `window_poly` proves the converse needed by the host: every `g` of
degree `< p` divisible by `(y-1)^(p-r)` is of this form, `g_e = G(η - e)` with `deg G < r`.
(The inclusion `winPoly ⊂ (y-1)^(p-r) Poly_{<r}` is the Hasse-moment computation
`winPoly_dvd`, and the dimension count closes the gap.)
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts3
open Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

/-- `G ↦ Σ_{e<p} G(η - e) X^e`. -/
def winPoly (η : Fp) : Fp[X] →ₗ[Fp] Fp[X] :=
  ∑ e : Fin p, (Polynomial.leval (η - ((e : ℕ) : Fp))).smulRight ((X : Fp[X]) ^ (e : ℕ))

theorem winPoly_apply (η : Fp) (G : Fp[X]) :
    winPoly η G = ∑ e : Fin p, C (G.eval (η - ((e : ℕ) : Fp))) * X ^ (e : ℕ) := by
  simp [winPoly, LinearMap.sum_apply, Polynomial.smul_eq_C_mul]

theorem winPoly_coeff (η : Fp) (G : Fp[X]) (n : ℕ) (hn : n < p) :
    (winPoly η G).coeff n = G.eval (η - (n : Fp)) := by
  rw [winPoly_apply, Polynomial.finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single ⟨n, hn⟩]
  · simp
  · intro b _ hb
    have : n ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
    simp [this]
  · simp

theorem winPoly_degree (η : Fp) (G : Fp[X]) : (winPoly η G).degree < p := by
  rw [winPoly_apply]
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro e _
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
  exact_mod_cast e.isLt

theorem fin_sum_eq_zmod_sum (f : Fp → Fp) :
    ∑ e : Fin p, f ((e : ℕ) : Fp) = ∑ x : Fp, f x := by
  refine Fintype.sum_bijective (fun e : Fin p => ((e : ℕ) : Fp)) ?_ _ _ (fun _ => rfl)
  have hinj : Function.Injective (fun e : Fin p => ((e : ℕ) : Fp)) := by
    intro a b h
    have := (ZMod.natCast_eq_natCast_iff' (a : ℕ) b p).mp h
    rw [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at this
    exact Fin.ext this
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp⟩

/-- Hasse moments of a window polynomial. -/
theorem winPoly_taylor (η : Fp) (G : Fp[X]) (k : ℕ) :
    (taylor 1 (winPoly η G)).coeff k =
      ∑ e : Fin p, ((e : ℕ).choose k : Fp) * G.eval (η - ((e : ℕ) : Fp)) := by
  rw [taylor_coeff, winPoly_apply, map_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Polynomial.C_mul_X_pow_eq_monomial, hasseDeriv_monomial, Polynomial.eval_monomial]
  simp [nsmul_eq_mul]

theorem winPoly_moment (η : Fp) (G : Fp[X]) (r k : ℕ) (hG : G.degree < (r : WithBot ℕ))
    (hk : k + r < p) :
    ∑ e : Fin p, ((e : ℕ).choose k : Fp) * G.eval (η - ((e : ℕ) : Fp)) = 0 := by
  by_cases hG0 : G = 0
  · simp [hG0]
  have hGn : G.natDegree < r := (Polynomial.natDegree_lt_iff_degree_lt hG0).mpr hG
  have hk0 : ((k.factorial : ℕ) : Fp) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff, Nat.Prime.dvd_factorial (Fact.out : Nat.Prime p)] at h
    omega
  set Q : Fp[X] := C (((k.factorial : ℕ) : Fp)⁻¹) * descPochhammer Fp k * G.comp (C η - X) with hQ
  have hev : ∀ e : Fin p, ((e : ℕ).choose k : Fp) * G.eval (η - ((e : ℕ) : Fp)) =
      Q.eval ((e : ℕ) : Fp) := by
    intro e
    simp only [hQ, eval_mul, eval_C, eval_comp, eval_sub, eval_X,
      descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    field_simp
  simp_rw [hev]
  rw [fin_sum_eq_zmod_sum (fun x => Q.eval x)]
  have hlin : (C η - X : Fp[X]).natDegree ≤ 1 := by
    refine (natDegree_sub_le _ _).trans ?_
    simp
  have hdeg : Q.natDegree < p - 1 := by
    have h1 : (G.comp (C η - X)).natDegree ≤ G.natDegree := by
      refine (natDegree_comp_le).trans ?_
      nlinarith
    have h2 : Q.natDegree ≤ 0 + k + G.natDegree := by
      refine (natDegree_mul_le).trans ?_
      refine add_le_add ((natDegree_mul_le).trans (add_le_add (by simp) (descPochhammer_natDegree Fp k).le)) h1
    omega
  rw [show (∑ x : Fp, Q.eval x) = ∑ x : Fp, ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i * x ^ i from
    Finset.sum_congr rfl fun x _ => Q.eval_eq_sum_range x, Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [← Finset.mul_sum, FiniteField.sum_pow_lt_card_sub_one Fp i (by rw [ZMod.card]; have := Finset.mem_range.mp hi; omega), mul_zero]

theorem winPoly_dvd (η : Fp) (G : Fp[X]) (r : ℕ) (hr : r ≤ p) (hG : G.degree < (r : WithBot ℕ)) :
    (X - 1 : Fp[X]) ^ (p - r) ∣ winPoly η G := by
  have h1 : (X - 1 : Fp[X]) = X - C 1 := by simp
  rw [h1, pow_dvd_iff_taylor]
  intro k hk
  rw [winPoly_taylor]
  exact winPoly_moment η G r k hG (by omega)

theorem degree_pow_X_sub_one (m : ℕ) : ((X - 1 : Fp[X]) ^ m).degree = (m : WithBot ℕ) := by
  rw [degree_pow, show (X - 1 : Fp[X]) = X - C 1 by simp, degree_X_sub_C]
  simp

/-- **`G_B` encoding.**  A polynomial of degree `< p` divisible by `(y-1)^(p-r)` has coefficients
`g_e = G(η - e)` for a polynomial `G` of degree `< r`. -/
theorem window_poly (η : Fp) (r : ℕ) (hr : r ≤ p) (g : Fp[X]) (hg : g.degree < p)
    (hd : (X - 1 : Fp[X]) ^ (p - r) ∣ g) :
    ∃ G : Fp[X], G.degree < (r : WithBot ℕ) ∧ ∀ e : Fin p, g.coeff e = G.eval (η - ((e : ℕ) : Fp)) := by
  let U : Submodule Fp Fp[X] := degreeLT Fp r
  haveI : FiniteDimensional Fp U := LinearEquiv.finiteDimensional (degreeLTEquiv Fp r).symm
  have hU : finrank Fp U = r := by
    rw [(degreeLTEquiv Fp r).finrank_eq]; simp
  have hf0 : ((X - 1 : Fp[X]) ^ (p - r)) ≠ 0 := pow_ne_zero _ (by simpa using X_sub_C_ne_zero (1 : Fp))
  let T1 : U →ₗ[Fp] Fp[X] := (winPoly η).domRestrict U
  let W1 : U →ₗ[Fp] Fp[X] := (LinearMap.mulLeft Fp ((X - 1 : Fp[X]) ^ (p - r))).domRestrict U
  have hT1 : Function.Injective T1 := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hu' : winPoly η u.1 = 0 := hu
    have hUdeg : u.1.degree < (r : WithBot ℕ) := mem_degreeLT.mp u.2
    have hz : u.1 = 0 := by
      by_cases h0 : u.1 = 0
      · exact h0
      · have hn : u.1.natDegree < p :=
          lt_of_lt_of_le ((Polynomial.natDegree_lt_iff_degree_lt h0).mpr hUdeg) hr
        refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero u.1 (ι := Fin p)
          (f := fun e : Fin p => η - ((e : ℕ) : Fp)) ?_ (fun e => ?_) (by simpa using hn)
        · intro a b hab
          have := sub_right_injective hab
          have h' := (ZMod.natCast_eq_natCast_iff' (a : ℕ) b p).mp this
          rw [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at h'
          exact Fin.ext h'
        · rw [← winPoly_coeff η u.1 e e.isLt, hu']; simp
    exact Subtype.ext hz
  have hW1 : Function.Injective W1 := by
    intro a b hab
    exact Subtype.ext (mul_left_cancel₀ hf0 hab)
  have hle : LinearMap.range T1 ≤ LinearMap.range W1 := by
    rintro _ ⟨u, rfl⟩
    obtain ⟨h, hh⟩ := winPoly_dvd η u.1 r hr (mem_degreeLT.mp u.2)
    have hdeg := winPoly_degree η u.1
    have hh' : h.degree < (r : WithBot ℕ) := by
      have hfd : ((X - 1 : Fp[X]) ^ (p - r)).degree = ((p - r : ℕ) : WithBot ℕ) := degree_pow_X_sub_one _
      have := (CatalanMeasure.GenD.Uniform.Prefix.native_factor_degree_lt _ h hf0 (p - r) r hfd).mp
        (by
          have e : p - r + r = p := by omega
          rw [e, ← hh]; exact hdeg)
      exact this
    exact ⟨⟨h, mem_degreeLT.mpr hh'⟩, hh.symm⟩
  haveI : FiniteDimensional Fp (LinearMap.range W1) := inferInstance
  have heq : LinearMap.range T1 = LinearMap.range W1 := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    rw [LinearMap.finrank_range_of_inj hT1, LinearMap.finrank_range_of_inj hW1]
  have hmem : g ∈ LinearMap.range W1 := by
    obtain ⟨h, hh⟩ := hd
    have hdg : h.degree < (r : WithBot ℕ) := by
      have hfd : ((X - 1 : Fp[X]) ^ (p - r)).degree = ((p - r : ℕ) : WithBot ℕ) := degree_pow_X_sub_one _
      refine (CatalanMeasure.GenD.Uniform.Prefix.native_factor_degree_lt _ h hf0 (p - r) r hfd).mp ?_
      have e : p - r + r = p := by omega
      rw [e, ← hh]; exact hg
    exact ⟨⟨h, mem_degreeLT.mpr hdg⟩, hh.symm⟩
  rw [← heq] at hmem
  obtain ⟨u, hu⟩ := hmem
  refine ⟨u.1, mem_degreeLT.mp u.2, fun e => ?_⟩
  have : T1 u = g := hu
  rw [← this]
  show (winPoly η u.1).coeff e = _
  exact winPoly_coeff η u.1 e e.isLt

end
end CatalanMeasure.GenD.Uniform.W.Charts3
