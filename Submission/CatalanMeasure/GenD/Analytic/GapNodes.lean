module

public import Submission.CatalanMeasure.ChebyshevNodes
public import Submission.OAI.NumberTheory.Catalan.Estimates.RealEnergyDiagonal

@[expose] public section

/-!
# Analytic layer (group 4): interpolation nodes on `Fin J`, any `J`, design-generic

Generic port of `Parametric.GapNodes`.  The P20 nodes are the `2K = 18N` roots `+-t_j` of
`T_K((2 t^2-(1+a^2))/(1-a^2))`, `K = 9N`; this needs `J = d0*N` even.  For general `J` we take
`K = (J+1)/2` (so `J = K + L`, `L = J/2`, `K - L <= 1`) and keep ALL `K` positive roots and the
first `L` negative roots: for odd `J` exactly one negative root is dropped.  For even `J` the
node set is the P20 set (parity lemma in `GenDBridge/Nodes`).
-/

namespace CatalanMeasure.GenD
namespace Analytic

open Set OAI.InternalCatalan

noncomputable section

theorem gapSq_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < 1 - a ^ 2 := by
  have hh := mul_pos (sub_pos.mpr ha1) (by linarith only [ha0] : 0 < 1 + a)
  nlinarith only [hh]

/-- The positive roots `sqrt (a^2+(1-a^2)(1+s_j)/2)`, `T_K(s_j)=0`. -/
def posNode (a : ℝ) (K : ℕ) (i : Fin K) : ℝ :=
  Real.sqrt (a ^ 2 + (1 - a ^ 2) * (1 + CatalanMeasure.chebX K i) / 2)

/-- All `K` positive roots followed by the negatives of the first `L <= K` of them. -/
def gapNodesKL (a : ℝ) (K L : ℕ) (hL : L ≤ K) : Fin (K + L) → ℝ :=
  Fin.append (posNode a K) (fun i => -posNode a K (Fin.castLE hL i))

/-- The nodes on `Fin J`, `K = (J+1)/2`, `L = J/2`. -/
def gapNodesGen (a : ℝ) (J : ℕ) : Fin J → ℝ :=
  fun i => gapNodesKL a ((J + 1) / 2) (J / 2) (by omega) (Fin.cast (by omega) i)

theorem pos_node_sq {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (K : ℕ) (i : Fin K) :
    (posNode a K i) ^ 2 = a ^ 2 + (1 - a ^ 2) * (1 + CatalanMeasure.chebX K i) / 2 := by
  unfold posNode
  apply Real.sq_sqrt
  have hi := CatalanMeasure.chebX_mem i
  have haa := gapSq_pos ha0 ha1
  have harg : 0 < 1 + CatalanMeasure.chebX K i := by linarith only [hi.1]
  exact add_nonneg (sq_nonneg a) (div_nonneg (mul_nonneg haa.le harg.le) (by norm_num))

theorem pos_node_bounds {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (K : ℕ) (i : Fin K) :
    a < posNode a K i ∧ posNode a K i < 1 := by
  have hsq := pos_node_sq ha0 ha1 K i
  have hi := CatalanMeasure.chebX_mem i
  have hnn : 0 ≤ posNode a K i := Real.sqrt_nonneg _
  have haa := gapSq_pos ha0 ha1
  have hl := mul_pos haa (by linarith only [hi.1] : 0 < 1 + CatalanMeasure.chebX K i)
  have hu := mul_lt_mul_of_pos_left (hi.2) haa
  constructor <;> nlinarith only [hsq, hnn, ha0, ha1, hl, hu]

theorem pos_node_injective {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (K : ℕ) :
    Function.Injective (posNode a K) := by
  intro i j hij
  apply CatalanMeasure.chebX_injective K
  have hi := pos_node_sq ha0 ha1 K i
  have hj := pos_node_sq ha0 ha1 K j
  have haa : 1 - a ^ 2 ≠ 0 := (gapSq_pos ha0 ha1).ne'
  have he : (1 - a ^ 2) * (CatalanMeasure.chebX K i - CatalanMeasure.chebX K j) = 0 := by
    nlinarith only [hi, hj, congrArg (fun x : ℝ => x ^ 2) hij]
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left haa)

theorem gapNodesKL_left (a : ℝ) {K L : ℕ} (hL : L ≤ K) (i : Fin K) :
    gapNodesKL a K L hL (Fin.castAdd L i) = posNode a K i := by
  simp [gapNodesKL]

theorem gapNodesKL_right (a : ℝ) {K L : ℕ} (hL : L ≤ K) (i : Fin L) :
    gapNodesKL a K L hL (Fin.natAdd K i) = -posNode a K (Fin.castLE hL i) := by
  simp [gapNodesKL]

theorem gapNodesKL_injective {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {K L : ℕ} (hL : L ≤ K) :
    Function.Injective (gapNodesKL a K L hL) := by
  have hp := pos_node_injective ha0 ha1 K
  intro i j h
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      rw [gapNodesKL_left, gapNodesKL_left] at h
      exact congrArg (Fin.castAdd L) (hp h)
    | right j =>
      rw [gapNodesKL_left, gapNodesKL_right] at h
      have hi := (pos_node_bounds ha0 ha1 K i).1
      have hj := (pos_node_bounds ha0 ha1 K (Fin.castLE hL j)).1
      linarith only [hi, hj, ha0, h]
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      rw [gapNodesKL_left, gapNodesKL_right] at h
      have hi := (pos_node_bounds ha0 ha1 K (Fin.castLE hL i)).1
      have hj := (pos_node_bounds ha0 ha1 K j).1
      linarith only [hi, hj, ha0, h]
    | right j =>
      rw [gapNodesKL_right, gapNodesKL_right] at h
      have := hp (neg_inj.mp h)
      exact congrArg (Fin.natAdd K) (Fin.castLE_injective hL this)

theorem gapNodesKL_bounds {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {K L : ℕ} (hL : L ≤ K)
    (i : Fin (K + L)) : gapNodesKL a K L hL i ∈ Ioo (-1 : ℝ) 1 ∧ a < |gapNodesKL a K L hL i| := by
  induction i using Fin.addCases with
  | left j =>
    have hj := pos_node_bounds ha0 ha1 K j
    rw [gapNodesKL_left, abs_of_pos (lt_trans ha0 hj.1)]
    exact ⟨⟨by linarith only [ha0, hj.1], hj.2⟩, hj.1⟩
  | right j =>
    have hj := pos_node_bounds ha0 ha1 K (Fin.castLE hL j)
    rw [gapNodesKL_right, abs_neg, abs_of_pos (lt_trans ha0 hj.1)]
    exact ⟨⟨by linarith only [hj.2], by linarith only [ha0, hj.1]⟩, hj.1⟩

theorem gap_nodes_injective {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (J : ℕ) :
    Function.Injective (gapNodesGen a J) := by
  intro i j h
  exact Fin.cast_injective _ (gapNodesKL_injective ha0 ha1 _ h)

theorem gap_nodes_bounds {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (J : ℕ) (i : Fin J) :
    gapNodesGen a J i ∈ Ioo (-1 : ℝ) 1 ∧ a < |gapNodesGen a J i| :=
  gapNodesKL_bounds ha0 ha1 _ _

theorem gap_nodes_ne_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (J : ℕ) (i : Fin J) :
    gapNodesGen a J i ≠ 0 := by
  intro h
  have hh := (gap_nodes_bounds ha0 ha1 J i).2
  rw [h, abs_zero] at hh
  linarith only [hh, ha0]

theorem gap_nodes_ne_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (J : ℕ) (i : Fin J) :
    gapNodesGen a J i ≠ 1 :=
  (gap_nodes_bounds ha0 ha1 J i).1.2.ne

theorem coordinate_gap_of_inverse_gap {g x : ℝ} (hg0 : 0 ≤ g) (hg1 : g < 1)
    (hx : |x| < 1) (hh : 2 * g / (1 + g ^ 2) ≤ |realCoordinateInv x|) : g ≤ |x| := by
  have hdx : 0 < 1 + x ^ 2 := by positivity
  have hdg : 0 < 1 + g ^ 2 := by positivity
  have ha : |realCoordinateInv x| = 2 * |x| / (1 + x ^ 2) := by
    simp [realCoordinateInv, abs_div, abs_mul, abs_of_pos hdx]
  rw [ha, div_le_div_iff₀ hdg hdx] at hh
  rw [← sq_abs x] at hh
  by_contra hn
  have hsmall : |x| < g := lt_of_not_ge hn
  have hgu : g * |x| < 1 :=
    (mul_le_mul_of_nonneg_left hx.le hg0).trans_lt (by simpa using hg1)
  have hprod := mul_pos (sub_pos.mpr hsmall) (sub_pos.mpr hgu)
  nlinarith only [hh, hprod]

/-- The `x`-coordinate gap: with `a = 2g/(1+g^2)`, every node has `g <= |realCoordinate tau|`. -/
theorem gap_nodes_coordinate {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (J : ℕ) (i : Fin J) :
    gapNodesGen (2 * g / (1 + g ^ 2)) J i ∈ Ioo (-1 : ℝ) 1 ∧
      g ≤ |realCoordinate (gapNodesGen (2 * g / (1 + g ^ 2)) J i)| := by
  have hd : 0 < 1 + g ^ 2 := by positivity
  have ha0 : 0 < 2 * g / (1 + g ^ 2) := by positivity
  have ha1 : 2 * g / (1 + g ^ 2) < 1 := by
    rw [div_lt_one hd]; nlinarith only [pow_pos (sub_pos.mpr hg1) 2]
  have hi := gap_nodes_bounds ha0 ha1 J i
  refine ⟨hi.1, ?_⟩
  apply coordinate_gap_of_inverse_gap hg0.le hg1 (abs_lt.mpr (realCoordinate_mem hi.1))
  rw [realCoordinate_right_inverse hi.1]
  exact hi.2.le

end

end Analytic
end CatalanMeasure.GenD
