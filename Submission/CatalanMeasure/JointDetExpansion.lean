module
public import Submission.CatalanMeasure.DetExpansion
@[expose] public section
namespace CatalanMeasure
open Finset
open scoped BigOperators

/-- Preserve joint atom weights instead of estimating each separately. -/
theorem abs_det_add_atoms_sub_le_joint {n J : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (Φ : Fin n → Fin J → ℝ)
    (β : Fin J → Fin n → ℝ) (δ : ℝ) {M c : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hD : ∀ f : Fin n → Option (Fin J),
      (∏ k,(f k).elim 1 (fun a =>|β a k|))*|(atomMatrix A Φ f).det| ≤
        M*∏ k,(f k).elim 1 (fun _ =>c)) :
    |(Matrix.of fun r k =>A r k+δ*∑ a,Φ r a*β a k).det-A.det| ≤
      M*((1+J*(|δ| *c))^n-1) :=by
  classical
  set y : ℝ :=|δ| *c with hy
  have hy0 : 0 ≤ y :=by positivity
  let u : Option (Fin J) → ℝ :=fun o =>o.elim 1 (fun _ =>y)
  let T : (Fin n → Option (Fin J)) → ℝ :=fun f =>
    (∏ k,atomWeight β δ (f k) k)*(atomMatrix A Φ f).det
  have hT : ∀ f,|T f| ≤ M*∏ k,u (f k) :=by
    intro f
    have hw (k : Fin n) : |atomWeight β δ (f k) k|=
        (f k).elim 1 (fun _ =>|δ|)*(f k).elim 1 (fun a =>|β a k|) :=by
      rcases f k with _ | a <;> simp [atomWeight,abs_mul]
    calc
      |T f|=(∏ k,(f k).elim 1 (fun _ =>|δ|))*
          ((∏ k,(f k).elim 1 (fun a =>|β a k|))*|(atomMatrix A Φ f).det|) :=by
        simp only [T,abs_mul,abs_prod,hw,prod_mul_distrib,mul_assoc]
      _ ≤ (∏ k,(f k).elim 1 (fun _ =>|δ|))*(M*∏ k,(f k).elim 1 (fun _ =>c)) :=by
        apply mul_le_mul_of_nonneg_left (hD f)
        apply prod_nonneg
        intro k _
        rcases f k with _ | a <;> simp [abs_nonneg]
      _ = M*∏ k,u (f k) :=by
        rw [mul_left_comm,← prod_mul_distrib]
        congr 1
        apply prod_congr rfl
        intro k _
        rcases f k with _ | a <;> simp [u,y]
  let f₀ : Fin n → Option (Fin J) := fun _ => none
  have hT₀ : T f₀ = A.det := by
    simp only [T, f₀, atomWeight, Option.elim, prod_const_one, one_mul]
    congr 1
  have hsum : ∑ f : Fin n → Option (Fin J), ∏ k, u (f k) = (1 + J * y) ^ n := by
    rw [← Fintype.prod_sum (fun _ o => u o)]
    simp only [Fintype.sum_option, u, Option.elim, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, prod_const]
  have hu₀ : ∏ k, u (f₀ k) = 1 := by simp [u, f₀]
  rw [det_add_atoms A Φ β δ]
  change |∑ f, T f - A.det| ≤ _
  rw [← add_sum_erase _ _ (mem_univ f₀), hT₀, add_sub_cancel_left]
  calc |∑ f ∈ univ.erase f₀, T f| ≤ ∑ f ∈ univ.erase f₀, |T f| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ f ∈ univ.erase f₀, M * ∏ k, u (f k) := sum_le_sum fun f _ => hT f
    _ = M * (∑ f : Fin n → Option (Fin J), ∏ k, u (f k) - ∏ k, u (f₀ k)) := by
        rw [← mul_sum, ← sum_erase_add univ (fun f : Fin n → Option (Fin J) => ∏ k, u (f k)) (mem_univ f₀)]
        ring
    _ = M * ((1 + J * y) ^ n - 1) := by rw [hsum, hu₀]


end CatalanMeasure
