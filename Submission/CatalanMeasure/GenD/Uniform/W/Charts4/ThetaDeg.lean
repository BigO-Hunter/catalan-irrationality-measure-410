module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Theta
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.W.Charts4
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.Charts3 Finset
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

local notation "Fp" => ZMod p

theorem mul_rem_degree (Q : Fp[X]) (hQ : Q.degree < p) (r : ℕ) (hr : r < p) :
    ((X - 1) ^ r * Q).degree < ((p + p : ℕ) : WithBot ℕ) := by
  have hd : ((X - 1 : Fp[X])).degree = 1 := by simpa using degree_X_sub_C (1 : Fp)
  by_cases h0 : Q = 0
  · simp [h0]
  · rw [degree_mul, degree_pow, hd, degree_eq_natDegree h0]
    have : Q.natDegree < p := by
      have := hQ; rw [degree_eq_natDegree h0] at this; exact_mod_cast this
    simp only [nsmul_eq_mul, mul_one]
    norm_cast
    omega

theorem QC_degree (hp2 : p ≠ 2) {b : ℕ} (t : TilingCoordinates (K := Fp) b ((p - 1) / 2))
    (k : Fin b) : (QC t k).degree < p := by
  have hm : QC t k ∈ Submodule.span Fp (Set.range (minusVectors (p := p))) := by
    rw [QC_eq]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [minus_native_span hp2] at hm
  obtain ⟨A, hA, hAe⟩ := hm
  have hA' := mem_degreeLT.mp hA
  have hhe := native_half_identity hp2
  change (X + 1) ^ ((p - 1) / 2) * A = QC t k at hAe
  rw [← hAe]
  have hd : ((X + 1 : Fp[X])).degree = 1 := by
    simpa using degree_X_sub_C (-1 : Fp)
  by_cases h0 : A = 0
  · simp [h0]
  · rw [degree_mul, degree_pow, hd, degree_eq_natDegree h0]
    have : A.natDegree < (p - 1) / 2 := by
      have := hA'; rw [degree_eq_natDegree h0] at this; exact_mod_cast this
    simp only [nsmul_eq_mul, mul_one]
    norm_cast
    omega

theorem nativeCenter_degree (hp2 : p ≠ 2) : (nativeCenter (p := p)).degree < p := by
  have hhe := native_half_identity hp2
  have h2 : ((X ^ 2 - 1 : Fp[X])).degree = 2 := by
    simpa using degree_X_pow_sub_C (R := Fp) (by norm_num : 0 < 2) (1 : Fp)
  unfold nativeCenter
  rw [degree_pow, h2]
  simp only [nsmul_eq_mul]
  norm_cast
  omega

theorem zL_degree (hp2 : p ≠ 2) {b : ℕ} (t : TilingCoordinates (K := Fp) b ((p - 1) / 2)) :
    (zL t).degree < p := by
  rw [zL_apply]
  exact lt_of_le_of_lt (degree_smul_le _ _) (nativeCenter_degree hp2)

theorem rem_lt (P : Parameters) (N p : ℕ) [Fact p.Prime] : P.h N % p < p :=
  Nat.mod_lt _ (Fact.out : p.Prime).pos

theorem lamA_degree (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) (k : Fin (bN P N p)) (c : Fin (P.n N) → Fp) :
    (lamA hp2 hn k c).degree < ((p + p : ℕ) : WithBot ℕ) := by
  have := mul_rem_degree (QA (tL hp2 hn c) k) (QA_degree hp2 _ k) (P.h N % p) (rem_lt P N p)
  simpa [lamA, rem, qaL_apply] using this

theorem lamC_degree (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) (k : Fin (bN P N p)) (c : Fin (P.n N) → Fp) :
    (lamC hp2 hn k c).degree < ((p + p : ℕ) : WithBot ℕ) := by
  have := mul_rem_degree (QC (tL hp2 hn c) k) (QC_degree hp2 _ k) (P.h N % p) (rem_lt P N p)
  simpa [lamC, rem, qcL_apply] using this

theorem lamZ_degree (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) (c : Fin (P.n N) → Fp) :
    (lamZ hp2 hn c).degree < ((p + p : ℕ) : WithBot ℕ) := by
  have := mul_rem_degree (zL (tL hp2 hn c)) (zL_degree hp2 _) (P.h N % p) (rem_lt P N p)
  simpa [lamZ, rem] using this

theorem kindPoly_degree (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) {ex : ℕ} (i : CK (bN P N p) ex)
    (c : Fin (P.n N) → Fp) : (kindPoly (P := P) (N := N) hp2 hn i c).degree < p := by
  rcases i with ⟨k, u⟩ | z | _
  · simp only [kindPoly]
    match hu : u.val with
    | 0 => exact fpart_degree _
    | 1 => exact epart_degree _ (lamA_degree hp2 hn k c)
    | 2 => exact fpart_degree _
    | _ + 3 => exact epart_degree _ (lamC_degree hp2 hn k c)
  · simp only [kindPoly]
    split_ifs
    · exact fpart_degree _
    · exact epart_degree _ (lamZ_degree hp2 hn c)
  · simp [kindPoly]

end
end CatalanMeasure.GenD.Uniform.W.Charts4
