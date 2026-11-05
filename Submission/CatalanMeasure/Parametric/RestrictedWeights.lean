module
public import Submission.CatalanMeasure.Parametric.PolynomialFunctional
public import Submission.CatalanMeasure.Parametric.RadiusQuadrature
public import Submission.CatalanMeasure.GenD.Signed.Keyhole
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Finset
noncomputable section

theorem quadBasis_natDegree_le {J : ℕ} {τ : Fin J → ℝ}
    (hτ : Function.Injective τ) (a : Fin J) :
    (OAI.InternalCatalan.quadBasis τ a).natDegree ≤ J-1 := by
  have hh := Lagrange.natDegree_basis (s := (univ:Finset (Fin J))) (v := τ)
    (fun x _ y _ hxy => hτ hxy) (mem_univ a)
  simpa [OAI.InternalCatalan.quadBasis] using hh.le

theorem rowCommonFactor_natDegree_le (P : Parameters) (N : ℕ) :
    (rowCommonFactor P N).natDegree ≤ P.A N+P.h N := by
  have hb : (1-X:ℝ[X]).natDegree ≤ 1 := by
    simpa using natDegree_sub_le (1:ℝ[X]) X
  have hp : ((1-X:ℝ[X])^(P.h N)).natDegree ≤ P.h N*(1-X:ℝ[X]).natDegree := natDegree_pow_le
  unfold rowCommonFactor
  have hh : ((X^(P.A N):ℝ[X])*((1-X)^(P.h N))).natDegree ≤
      (X^(P.A N):ℝ[X]).natDegree+((1-X:ℝ[X])^(P.h N)).natDegree := natDegree_mul_le
  rw [natDegree_X_pow] at hh
  nlinarith

theorem proposed_common_basis_coeff_zero (N : ℕ) (a : Fin (89*N)) (i : ℕ)
    (hi : proposed.H N ≤ i) :
    (rowCommonFactor proposed N *
      OAI.InternalCatalan.quadBasis (CatalanMeasure.chebNode (89*N)) a).coeff i=0 := by
  have hf := rowCommonFactor_natDegree_le proposed N
  have hb := quadBasis_natDegree_le (CatalanMeasure.chebNode_injective (89*N)) a
  have hd : (rowCommonFactor proposed N *
      OAI.InternalCatalan.quadBasis (CatalanMeasure.chebNode (89*N)) a).natDegree ≤
      (rowCommonFactor proposed N).natDegree +
      (OAI.InternalCatalan.quadBasis (CatalanMeasure.chebNode (89*N)) a).natDegree := natDegree_mul_le
  apply coeff_eq_zero_of_natDegree_lt
  rw [proposed_A] at hf
  change (rowCommonFactor proposed N).natDegree ≤ 36*N+5*N at hf
  rw [proposed_H] at hi
  have hN : 0<N := by have := a.isLt; omega
  omega

theorem proposed_restricted_functional_le (N k : ℕ) (a : Fin (89*N)) :
    |polynomialFunctional proposed N k (rowCommonFactor proposed N *
      OAI.InternalCatalan.quadBasis (CatalanMeasure.chebNode (89*N)) a)| ≤
      260000*N*(residualCircleK:ℝ)^N := by
  have hh := polynomialFunctional_common_factor_le proposed N k
    (OAI.InternalCatalan.quadBasis (CatalanMeasure.chebNode (89*N)) a)
    (proposed_common_basis_coeff_zero N a)
    (radius := (residualRadius:ℝ)) (B := 500*(residualCircleK:ℝ)^N)
    (by norm_num [residualRadius]) (fun z hz => by
      simpa only [Parameters.h,Parameters.q,proposed,show 5*N+7*N=12*N by ring] using
        norm_restricted_filtered_basis_le N a z hz)
  rw [proposed_H] at hh
  convert hh using 1 <;> push_cast <;> ring

def restrictedWeight (P : Parameters) (N k : ℕ) {J : ℕ} (τ : Fin J → ℝ) (a : Fin J) : ℝ :=
  polynomialFunctional P N k (rowCommonFactor P N * OAI.InternalCatalan.quadBasis τ a) /
    (rowCommonFactor P N).eval (τ a)

theorem rowCommonFactor_eval_ne_zero (P : Parameters) (N : ℕ) {t : ℝ} (ht : t<0) :
    (rowCommonFactor P N).eval t ≠ 0 := by
  simp only [rowCommonFactor,eval_mul,eval_pow,eval_X,eval_sub,eval_one]
  exact mul_ne_zero (pow_ne_zero _ ht.ne) (pow_ne_zero _ (by linarith))

/-- The weights must be bounded jointly with the common-factor node weight. -/
theorem proposed_restrictedWeight_joint_le (N k : ℕ) (a : Fin (89*N)) :
    |(rowCommonFactor proposed N).eval (CatalanMeasure.chebNode (89*N) a)| *
      |restrictedWeight proposed N k (CatalanMeasure.chebNode (89*N)) a| ≤
      260000*N*(residualCircleK:ℝ)^N := by
  have hn := rowCommonFactor_eval_ne_zero proposed N (CatalanMeasure.chebNode_mem a).2
  rw [restrictedWeight,abs_div,mul_comm,div_mul_cancel₀ _ (abs_ne_zero.mpr hn)]
  exact proposed_restricted_functional_le N k a

theorem pow_le_max_one_mul_pow {r x : ℝ} (hr : 0 < r) (hx : r ≤ |x|) (hx1 : |x| ≤ 1) (A I : ℕ) :
    |x| ^ A ≤ max 1 (r ^ A / r ^ I) * |x| ^ I := by
  have hx0 : 0 < |x| := lt_of_lt_of_le hr hx
  rcases le_total I A with h | h
  · calc |x| ^ A = |x| ^ I * |x| ^ (A - I) := by rw [← pow_add]; congr 1; omega
      _ ≤ |x| ^ I * 1 := by
        gcongr
        exact pow_le_one₀ hx0.le hx1
      _ ≤ _ := by
        rw [mul_one]
        exact le_mul_of_one_le_left (pow_nonneg hx0.le I) (le_max_left _ _)
  · have h1 : r ^ (I - A) ≤ |x| ^ (I - A) := pow_le_pow_left₀ hr.le hx (I - A)
    have hI : |x| ^ I = |x| ^ A * |x| ^ (I - A) := by rw [← pow_add]; congr 1; omega
    have hrI : r ^ I = r ^ A * r ^ (I - A) := by rw [← pow_add]; congr 1; omega
    have hrA : 0 < r ^ A := by positivity
    have hrB : 0 < r ^ (I - A) := by positivity
    have : r ^ A / r ^ I * |x| ^ I = |x| ^ A * (|x| ^ (I - A) / r ^ (I - A)) := by
      rw [hI, hrI]; field_simp
    calc |x| ^ A ≤ |x| ^ A * (|x| ^ (I - A) / r ^ (I - A)) :=
          le_mul_of_one_le_right (by positivity) ((one_le_div hrB).mpr h1)
      _ = r ^ A / r ^ I * |x| ^ I := this.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- **Keyhole form of the joint node weight** (PROOF-RHO Lemma KH, `k`-uniform).  If the cardinal
function `R` satisfies `‖R(z)‖ ‖1-z‖^(h+q) ≤ M₀` on `‖z‖ = r` and
`|R(x)| |1-x|^(h+q) ≤ B₀` on the real segments `r ≤ |x| ≤ 1` (`0 < r ≤ 1`), then for every column
`k` the joint weight satisfies
`|common(τ_a)| |weight_k(τ_a)| ≤ 4 (1 + (k - 2g)) max(1, r^A / r^(b+k+q)) max(M₀, B₀)`. -/
theorem restrictedWeight_joint_le_of_keyhole (P : Parameters) (N k : ℕ) {J : ℕ}
    {τ : Fin J → ℝ} (a : Fin J)
    (hc : (rowCommonFactor P N).eval (τ a) ≠ 0)
    (hdeg : ∀ i, P.H N ≤ i →
      (rowCommonFactor P N * OAI.InternalCatalan.quadBasis τ a).coeff i = 0)
    {r M₀ B₀ : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hcirc : ∀ z : ℂ, ‖z‖ = r →
      ‖((OAI.InternalCatalan.quadBasis τ a).map (algebraMap ℝ ℂ)).eval z‖ *
        ‖(1 : ℂ) - z‖ ^ (P.h N + P.q N) ≤ M₀)
    (hseg : ∀ x : ℝ, r ≤ |x| → |x| ≤ 1 →
      |(OAI.InternalCatalan.quadBasis τ a).eval x| * |1 - x| ^ (P.h N + P.q N) ≤ B₀) :
    |(rowCommonFactor P N).eval (τ a)| * |restrictedWeight P N k τ a| ≤
      4 * (1 + ((P.b N + k + P.q N - P.A N : ℕ) : ℝ)) *
        (max 1 (r ^ P.A N / r ^ (P.b N + k + P.q N)) * max M₀ B₀) := by
  set R := OAI.InternalCatalan.quadBasis τ a with hR
  set I := P.b N + k + P.q N with hI
  set κ : ℝ := max 1 (r ^ P.A N / r ^ I) with hκ
  have hκ1 : 1 ≤ κ := le_max_left _ _
  have hS : ∀ x : ℂ, ‖(((rowCommonFactor P N * R) * (X - 1) ^ (P.q N)).map
      (algebraMap ℝ ℂ)).eval x‖ =
      ‖x‖ ^ P.A N * (‖((R).map (algebraMap ℝ ℂ)).eval x‖ *
        ‖(1 : ℂ) - x‖ ^ (P.h N + P.q N)) := by
    intro x
    simp only [rowCommonFactor, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_one, Polynomial.map_X, eval_mul, eval_pow, eval_sub, eval_one, eval_X,
      norm_mul, norm_pow]
    rw [norm_sub_rev x 1, pow_add]
    ring
  have hSr : ∀ x : ℝ, |((rowCommonFactor P N * R) * (X - 1) ^ (P.q N)).eval x| =
      |x| ^ P.A N * (|R.eval x| * |1 - x| ^ (P.h N + P.q N)) := by
    intro x
    simp only [rowCommonFactor, eval_mul, eval_pow, eval_sub, eval_one, eval_X, abs_mul, abs_pow]
    rw [abs_sub_comm x 1, pow_add]
    ring
  have hM0 : 0 ≤ M₀ := by
    have := hcirc (r : ℂ) (by simp [abs_of_pos hr0])
    exact le_trans (by positivity) this
  have hB0 : 0 ≤ B₀ := by
    have := hseg r (by rw [abs_of_pos hr0]) (by rw [abs_of_pos hr0]; exact hr1)
    exact le_trans (by positivity) this
  have hrI : 0 < r ^ I := by positivity
  have hkey := CatalanMeasure.GenD.Signed.Keyhole.polynomialFunctional_keyhole_le P N k R hdeg (r := r)
    (M := M₀ * (r ^ P.A N / r ^ I)) (B := B₀ * κ) hr0 hr1
    (by
      intro z hz
      rw [hS, hz]
      calc r ^ P.A N * (‖(R.map (algebraMap ℝ ℂ)).eval z‖ * ‖(1 : ℂ) - z‖ ^ (P.h N + P.q N))
          ≤ r ^ P.A N * M₀ := by gcongr; exact hcirc z hz
        _ = M₀ * (r ^ P.A N / r ^ I) * r ^ I := by field_simp)
    (by
      intro x hx hx1
      rw [hSr]
      calc |x| ^ P.A N * (|R.eval x| * |1 - x| ^ (P.h N + P.q N))
          ≤ |x| ^ P.A N * B₀ := by gcongr; exact hseg x hx hx1
        _ ≤ (κ * |x| ^ I) * B₀ := by
            gcongr; exact pow_le_max_one_mul_pow hr0 hx hx1 _ _
        _ = B₀ * κ * |x| ^ I := by ring)
  have hmax : max (M₀ * (r ^ P.A N / r ^ I)) (B₀ * κ) ≤ κ * max M₀ B₀ := by
    apply max_le
    · calc M₀ * (r ^ P.A N / r ^ I) ≤ M₀ * κ := by
            gcongr; exact le_max_right _ _
        _ ≤ κ * max M₀ B₀ := by
            nlinarith [le_max_left M₀ B₀, mul_le_mul_of_nonneg_left (le_max_left M₀ B₀)
              (by linarith : (0 : ℝ) ≤ κ)]
    · calc B₀ * κ = κ * B₀ := mul_comm _ _
        _ ≤ κ * max M₀ B₀ := by gcongr; exact le_max_right _ _
  have hJ : (0 : ℝ) ≤ 4 * (1 + ((P.b N + k + P.q N - P.A N : ℕ) : ℝ)) := by positivity
  have hc' := abs_ne_zero.mpr hc
  rw [restrictedWeight, abs_div]
  rw [show |(rowCommonFactor P N).eval (τ a)| *
      (|polynomialFunctional P N k (rowCommonFactor P N * R)| /
        |(rowCommonFactor P N).eval (τ a)|) =
      |polynomialFunctional P N k (rowCommonFactor P N * R)| by field_simp]
  exact hkey.trans (mul_le_mul_of_nonneg_left hmax hJ)

/-- The reduced quadrature formula uses actual row values, with the shared factor
in the denominator of each weight. This is the form required in determinants. -/
theorem filteredCatalanCoeff_restricted_weights {P : Parameters} (hP : Admissible P)
    {N r : ℕ} (hN : 0<N) (hr : r<P.n N) {J : ℕ} (hJ : P.n N-P.g N ≤ J)
    {τ : Fin J → ℝ} (hτ : Function.Injective τ) (hneg : ∀ a, τ a<0) (k : ℕ) :
    (filteredCatalanCoeffRat P N r k:ℝ) =
      ∑ a, (OAI.InternalCatalan.realPoly (rowP P N r)).eval (τ a) *
        restrictedWeight P N k τ a := by
  rw [filteredCatalanCoeff_restricted_quadrature hP hN hr hJ hτ]
  apply sum_congr rfl
  intro a _
  have he : (OAI.InternalCatalan.realPoly (rowP P N r)).eval (τ a) =
      (rowCommonFactor P N).eval (τ a) *
      (OAI.InternalCatalan.realPoly (rowResidualP P N r)).eval (τ a) := by
    rw [rowP_common_factor hP hN hr]
    simp [OAI.InternalCatalan.realPoly,rowCommonFactor]
  have hn := rowCommonFactor_eval_ne_zero P N (hneg a)
  rw [he,restrictedWeight]
  field_simp

end
end CatalanMeasure.Parametric

#print axioms CatalanMeasure.Parametric.restrictedWeight_joint_le_of_keyhole
