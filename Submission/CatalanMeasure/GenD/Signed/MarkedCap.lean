module

public import Submission.CatalanMeasure.GenD.Signed.SheetNear
public import Submission.OAI.NumberTheory.Catalan.Estimates.RealEnergyDiagonal
public import Submission.CatalanMeasure.GenD.Analytic.GapNodes

/-!
# `MarkedCap` for marked rows that are quadrature-node images

In the real assembly (`weighted_atom_det`, `WeightedAtomPoint`) the marked rows are
`y j = realCoordinate (τ N (a j))` with `a : Fin m → Fin J` injective, where `τ N : Fin J → ℝ` is
the quadrature node set.  The cap `MarkedCap` of the marked rows therefore follows from the cap of
the whole node image `Z N = realCoordinate ∘ τ N` (`NodeCap`): the three clauses are inherited by
injective sub-families (the top count of a sub-family is at most that of the node set).

`NodeSub τ N m y` is the node-set predicate `Nd` for `SignedNearClassLinkNd` /
`signedSecondSheetNearNd` (SheetNear.lean).
-/

@[expose] public section

namespace CatalanMeasure.Signed

open Set Filter OAI.InternalCatalan

/-- **What `hlink` needs about the actual marked nodes `y`** (all marked rows, both signs): every
node has `|y| ≥ gs` (this is a property of each node: take it into `G`), every node is at
distance `≥ umin` from `1`, and the top count `#{i : y_j ≤ y_i} ≤ C1 n (1 - y_j) + 1` for
`y_j ≥ xc`. -/
def MarkedCap (gs xc C1 n umin : ℝ) {m : ℕ} (y : Fin m → ℝ) : Prop :=
  (∀ j, gs ≤ |y j|) ∧ (∀ j, y j ≤ 1 - umin) ∧
    ∀ j, xc ≤ y j → ((Finset.univ.filter (fun i => y j ≤ y i)).card : ℝ) ≤ C1 * n * (1 - y j) + 1

/-- Cap predicate of a node set `Z : Fin J → ℝ`. -/
def NodeCap (gs xc C1 n umin : ℝ) {J : ℕ} (Z : Fin J → ℝ) : Prop :=
  (∀ a, gs ≤ |Z a|) ∧ (∀ a, Z a ≤ 1 - umin) ∧
    ∀ a, xc ≤ Z a → ((Finset.univ.filter (fun b => Z a ≤ Z b)).card : ℝ) ≤ C1 * n * (1 - Z a) + 1

/-- `MarkedCap` of an injective sub-family of a node set with `NodeCap`. -/
theorem markedCap_of_nodeCap {gs xc C1 n umin : ℝ} {J m : ℕ} {Z : Fin J → ℝ}
    (hZ : NodeCap gs xc C1 n umin Z) {a : Fin m → Fin J} (ha : Function.Injective a) :
    MarkedCap gs xc C1 n umin (fun j => Z (a j)) := by
  obtain ⟨h1, h2, h3⟩ := hZ
  refine ⟨fun j => h1 _, fun j => h2 _, fun j hj => ?_⟩
  have hc : (Finset.univ.filter (fun i : Fin m => Z (a j) ≤ Z (a i))).card ≤
      (Finset.univ.filter (fun b : Fin J => Z (a j) ≤ Z b)).card := by
    apply Finset.card_le_card_of_injOn a
    · intro i hi
      simpa using hi
    · exact ha.injOn
  exact (Nat.cast_le.2 hc).trans (h3 _ hj)

/-- The node-set predicate for the real assembly: the marked rows are `realCoordinate` images of
distinct nodes `τ N (a j)` (exactly the data carried by `WeightedAtomPoint`). -/
def NodeSub {J : ℕ → ℕ} (τ : (N : ℕ) → Fin (J N) → ℝ) (N m : ℕ) (y : Fin m → ℝ) : Prop :=
  ∃ a : Fin m → Fin (J N), Function.Injective a ∧ ∀ j, realCoordinateInv (y j) = τ N (a j)

/-- **`MarkedCap` of the actual marked rows**: for rows `y ∈ (-1,1)` that are node images
(`NodeSub`), `MarkedCap` follows from `NodeCap` of the node image `realCoordinate ∘ τ N`. -/
theorem markedCap_of_nodeSub {gs xc C1 n umin : ℝ} {J : ℕ → ℕ}
    {τ : (N : ℕ) → Fin (J N) → ℝ} {N m : ℕ} {y : Fin m → ℝ}
    (hZ : NodeCap gs xc C1 n umin (fun a => realCoordinate (τ N a)))
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hN : NodeSub τ N m y) :
    MarkedCap gs xc C1 n umin y := by
  obtain ⟨a, ha, hya⟩ := hN
  have hyz : y = fun j => realCoordinate (τ N (a j)) := by
    funext j
    rw [← hya j]
    exact (realCoordinate_left_inverse (hy j)).symm
  rw [hyz]
  exact markedCap_of_nodeCap hZ ha

/-! ### The gap nodes: `NodeCap` of `realCoordinate ∘ gapNodesGen` -/

section Gap

open CatalanMeasure.GenD.Analytic

theorem one_sub_cos_ge {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    2 * θ ^ 2 / Real.pi ^ 2 ≤ 1 - Real.cos θ := by
  have hs : θ / Real.pi ≤ Real.sin (θ / 2) := by
    have h := Real.mul_le_sin (x := θ / 2) (by linarith) (by linarith)
    have e : 2 / Real.pi * (θ / 2) = θ / Real.pi := by field_simp
    linarith
  have hc : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h1 := Real.cos_two_mul (θ / 2)
    have h2 := Real.sin_sq_add_cos_sq (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h1
    nlinarith
  have h0' : 0 ≤ θ / Real.pi := div_nonneg h0 Real.pi_pos.le
  have h3 : (θ / Real.pi) ^ 2 ≤ Real.sin (θ / 2) ^ 2 := pow_le_pow_left₀ h0' hs 2
  have e : 2 * θ ^ 2 / Real.pi ^ 2 = 2 * (θ / Real.pi) ^ 2 := by field_simp
  rw [hc, e]
  nlinarith

theorem posNode_one_sub_sq {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (K : ℕ) (i : Fin K) :
    1 - posNode a K i ^ 2 = (1 - a ^ 2) * (1 - CatalanMeasure.chebX K i) / 2 := by
  rw [pos_node_sq ha0 ha1 K i]; ring

theorem posU_ge {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (K : ℕ) (i : Fin K) :
    Real.sqrt (1 - a ^ 2) * CatalanMeasure.chebAngle K i / Real.pi ≤
      Real.sqrt (1 - posNode a K i ^ 2) := by
  have hθ := CatalanMeasure.chebAngle_mem i.isLt
  have h1 := one_sub_cos_ge hθ.1.le hθ.2.le
  rw [posNode_one_sub_sq ha0 ha1 K i]
  have hc : Real.sqrt (1 - a ^ 2) ^ 2 = 1 - a ^ 2 := Real.sq_sqrt (gapSq_pos ha0 ha1).le
  apply le_trans (le_abs_self _) (Real.abs_le_sqrt _)
  rw [div_pow, mul_pow, hc]
  have hpi : 0 < Real.pi ^ 2 := by positivity
  have hx : CatalanMeasure.chebX K i = Real.cos (CatalanMeasure.chebAngle K i) := rfl
  rw [hx]
  have haa := gapSq_pos ha0 ha1
  have h2 : (CatalanMeasure.chebAngle K i) ^ 2 / Real.pi ^ 2 ≤
      (1 - Real.cos (CatalanMeasure.chebAngle K i)) / 2 := by
    rw [div_le_div_iff₀ hpi (by norm_num)]
    rw [div_le_iff₀ hpi] at h1
    nlinarith
  calc (1 - a ^ 2) * (CatalanMeasure.chebAngle K i) ^ 2 / Real.pi ^ 2
      = (1 - a ^ 2) * ((CatalanMeasure.chebAngle K i) ^ 2 / Real.pi ^ 2) := by ring
    _ ≤ (1 - a ^ 2) * ((1 - Real.cos (CatalanMeasure.chebAngle K i)) / 2) :=
        mul_le_mul_of_nonneg_left h2 haa.le
    _ = _ := by ring

theorem coord_mul {t : ℝ} (ht1 : t < 1) (ht0 : -1 < t) :
    OAI.InternalCatalan.realCoordinate t * (1 + Real.sqrt (1 - t ^ 2)) = t := by
  unfold OAI.InternalCatalan.realCoordinate
  have : 0 < 1 + Real.sqrt (1 - t ^ 2) := by positivity
  field_simp

theorem coord_neg {t : ℝ} (ht : t < 0) : OAI.InternalCatalan.realCoordinate t < 0 := by
  unfold OAI.InternalCatalan.realCoordinate
  exact div_neg_of_neg_of_pos ht (by positivity)

theorem coord_pos {t : ℝ} (ht : 0 < t) : 0 < OAI.InternalCatalan.realCoordinate t := by
  unfold OAI.InternalCatalan.realCoordinate
  positivity

theorem coord_one_sub_ge {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Real.sqrt (1 - t ^ 2) / 2 ≤ 1 - OAI.InternalCatalan.realCoordinate t := by
  have hm := coord_mul ht1 (by linarith)
  set Z := OAI.InternalCatalan.realCoordinate t
  set u := Real.sqrt (1 - t ^ 2) with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu1 : u ≤ 1 := by
    rw [hu]; apply Real.sqrt_le_one.mpr; nlinarith
  by_contra hcon
  push_neg at hcon
  nlinarith

theorem coord_mul_le {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Real.sqrt (1 - t ^ 2) * OAI.InternalCatalan.realCoordinate t ≤
      1 - OAI.InternalCatalan.realCoordinate t := by
  have hm := coord_mul ht1 (by linarith)
  nlinarith

theorem coord_mono {t1 t2 : ℝ} (h1 : t1 ∈ Set.Ioo (-1 : ℝ) 1) (h2 : t2 ∈ Set.Ioo (-1 : ℝ) 1)
    (h : OAI.InternalCatalan.realCoordinate t1 ≤ OAI.InternalCatalan.realCoordinate t2) :
    t1 ≤ t2 := by
  have hx := OAI.InternalCatalan.realCoordinate_mem h1
  have hy := OAI.InternalCatalan.realCoordinate_mem h2
  have e1 := OAI.InternalCatalan.realCoordinate_right_inverse h1
  have e2 := OAI.InternalCatalan.realCoordinate_right_inverse h2
  rw [← e1, ← e2]
  set x := OAI.InternalCatalan.realCoordinate t1
  set y := OAI.InternalCatalan.realCoordinate t2
  unfold OAI.InternalCatalan.realCoordinateInv
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hxy : 0 ≤ 1 - x * y := by
    nlinarith [mul_pos (sub_pos.2 hx.2) (by linarith [hy.1] : 0 < 1 + y),
      mul_pos (by linarith [hx.1] : 0 < 1 + x) (sub_pos.2 hy.2)]
  nlinarith [mul_nonneg (sub_nonneg.2 h) hxy]

end Gap

section GapCap

open CatalanMeasure.GenD.Analytic

theorem klTop {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {K L : ℕ} (hL : L ≤ K) (hKL : K ≤ L + 1)
    {xc : ℝ} (hxc : 0 < xc) (i : Fin K)
    (hi : xc ≤ OAI.InternalCatalan.realCoordinate (posNode a K i)) :
    ((Finset.univ.filter (fun b : Fin (K + L) =>
        OAI.InternalCatalan.realCoordinate (posNode a K i) ≤
          OAI.InternalCatalan.realCoordinate (gapNodesKL a K L hL b))).card : ℝ) ≤
      ((K + L : ℕ) : ℝ) / (2 * xc * Real.sqrt (1 - a ^ 2)) *
        (1 - OAI.InternalCatalan.realCoordinate (posNode a K i)) + 1 := by
  have hb := pos_node_bounds ha0 ha1 K i
  have ht0 : 0 < posNode a K i := lt_trans ha0 hb.1
  have haa := gapSq_pos ha0 ha1
  set t := posNode a K i with ht
  set Z := OAI.InternalCatalan.realCoordinate t with hZ
  set c := Real.sqrt (1 - a ^ 2) with hc
  set u := Real.sqrt (1 - t ^ 2) with hu
  have hcpos : 0 < c := Real.sqrt_pos.2 haa
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have huc : u ≤ c := Real.sqrt_le_sqrt (by nlinarith [hb.1])
  have hZpos : 0 < Z := coord_pos ht0
  -- the count
  have hcnt : (Finset.univ.filter (fun b : Fin (K + L) =>
        Z ≤ OAI.InternalCatalan.realCoordinate (gapNodesKL a K L hL b))).card ≤ (i : ℕ) + 1 := by
    have hsub : (Finset.univ.filter (fun b : Fin (K + L) =>
        Z ≤ OAI.InternalCatalan.realCoordinate (gapNodesKL a K L hL b))).card ≤
        (Finset.range ((i : ℕ) + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun b : Fin (K + L) => (b : ℕ))
      · intro b hbm
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hbm
        simp only [Finset.coe_range, Set.mem_Iio]
        induction b using Fin.addCases with
        | left b' =>
          rw [gapNodesKL_left] at hbm
          have hb' := pos_node_bounds ha0 ha1 K b'
          have hmono := coord_mono (t1 := t) (t2 := posNode a K b')
            ⟨by linarith [hb.1], hb.2⟩ ⟨by linarith [hb'.1], hb'.2⟩ hbm
          have hsq1 := pos_node_sq ha0 ha1 K i
          have hsq2 := pos_node_sq ha0 ha1 K b'
          have hsq : t ^ 2 ≤ posNode a K b' ^ 2 := by
            nlinarith [hb'.1, hb.1]
          have hs : CatalanMeasure.chebX K i ≤ CatalanMeasure.chebX K b' := by
            by_contra hcon; push_neg at hcon
            nlinarith [mul_pos haa (sub_pos.2 hcon)]
          have hθi := CatalanMeasure.chebAngle_mem i.isLt
          have hθb := CatalanMeasure.chebAngle_mem b'.isLt
          have hang : CatalanMeasure.chebAngle K b' ≤ CatalanMeasure.chebAngle K i := by
            by_contra hcon; push_neg at hcon
            have := Real.strictAntiOn_cos (Set.Ioo_subset_Icc_self hθi)
              (Set.Ioo_subset_Icc_self hθb) hcon
            exact absurd hs (not_le.2 this)
          have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by have := i.isLt; omega)
          unfold CatalanMeasure.chebAngle at hang
          rw [div_le_div_iff_of_pos_right (by positivity)] at hang
          have h3 : (2 * ((b' : ℕ) : ℝ) + 1) ≤ 2 * ((i : ℕ) : ℝ) + 1 :=
            le_of_mul_le_mul_right hang Real.pi_pos
          have h4 : ((b' : ℕ) : ℝ) ≤ ((i : ℕ) : ℝ) := by linarith
          have h5 : (b' : ℕ) ≤ (i : ℕ) := by exact_mod_cast h4
          simpa using Nat.lt_succ_of_le h5
        | right b' =>
          exfalso
          rw [gapNodesKL_right] at hbm
          have hb' := pos_node_bounds ha0 ha1 K (Fin.castLE hL b')
          have := coord_neg (t := -posNode a K (Fin.castLE hL b')) (by linarith [hb'.1])
          linarith
      · intro x _ y _ hxy
        exact Fin.ext hxy
    simpa using hsub
  refine (Nat.cast_le.2 hcnt).trans ?_
  rw [Nat.cast_add_one]
  -- real estimates
  have hθ := CatalanMeasure.chebAngle_mem i.isLt
  have hug : c * CatalanMeasure.chebAngle K i / Real.pi ≤ u := posU_ge ha0 ha1 K i
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by have := i.isLt; omega)
  have hθdef : CatalanMeasure.chebAngle K i = (2 * ((i : ℕ) : ℝ) + 1) * Real.pi / (2 * K) := rfl
  have hcθ : c * ((2 * ((i : ℕ) : ℝ) + 1) * Real.pi / (2 * K)) ≤ Real.pi * u := by
    rw [hθdef] at hug
    rw [div_le_iff₀ Real.pi_pos] at hug
    nlinarith
  have hkey : c * (2 * ((i : ℕ) : ℝ) + 1) ≤ 2 * K * u := by
    have e : c * ((2 * ((i : ℕ) : ℝ) + 1) * Real.pi / (2 * K)) * (2 * K) =
        c * (2 * ((i : ℕ) : ℝ) + 1) * Real.pi := by field_simp
    have h1 := mul_le_mul_of_nonneg_right hcθ (by positivity : (0 : ℝ) ≤ 2 * K)
    rw [e] at h1
    nlinarith [Real.pi_pos]
  have h2K : 2 * (K : ℝ) ≤ ((K + L : ℕ) : ℝ) + 1 := by
    push_cast; have : (K : ℝ) ≤ L + 1 := by exact_mod_cast hKL
    linarith
  have hux : u * xc ≤ 1 - Z := by
    have := coord_mul_le ht0 hb.2
    nlinarith
  set Jr : ℝ := ((K + L : ℕ) : ℝ) with hJr
  have hJ0 : 0 ≤ Jr := by positivity
  have hmain : 2 * ((i : ℕ) : ℝ) * (xc * c) ≤ Jr * (1 - Z) := by
    have h1 : xc * (c * (2 * ((i : ℕ) : ℝ) + 1)) ≤ xc * (2 * K * u) :=
      mul_le_mul_of_nonneg_left hkey hxc.le
    have h2 : xc * (2 * K * u) ≤ xc * ((Jr + 1) * u) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2K hu0) hxc.le
    have h3 : xc * u ≤ xc * c := mul_le_mul_of_nonneg_left huc hxc.le
    have h4 : Jr * (u * xc) ≤ Jr * (1 - Z) := mul_le_mul_of_nonneg_left hux hJ0
    nlinarith
  have hden : 0 < 2 * xc * c := by positivity
  have hfin : ((i : ℕ) : ℝ) ≤ Jr / (2 * xc * c) * (1 - Z) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hden]
    nlinarith
  linarith

theorem klGap {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {K L : ℕ} (hL : L ≤ K) (hKL : K ≤ L + 1)
    (b : Fin (K + L)) :
    OAI.InternalCatalan.realCoordinate (gapNodesKL a K L hL b) ≤
      1 - Real.sqrt (1 - a ^ 2) / (2 * (((K + L : ℕ) : ℝ) + 1)) := by
  have haa := gapSq_pos ha0 ha1
  set c := Real.sqrt (1 - a ^ 2) with hc
  have hcpos : 0 < c := Real.sqrt_pos.2 haa
  have hc1 : c ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith)
  have hJ0 : (0 : ℝ) ≤ ((K + L : ℕ) : ℝ) := Nat.cast_nonneg _
  induction b using Fin.addCases with
  | left i =>
    rw [gapNodesKL_left]
    have hb := pos_node_bounds ha0 ha1 K i
    have ht0 : 0 < posNode a K i := lt_trans ha0 hb.1
    have h1 := coord_one_sub_ge ht0 hb.2
    have hug := posU_ge ha0 ha1 K i
    have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by have := i.isLt; omega)
    have hθdef : CatalanMeasure.chebAngle K i =
        (2 * ((i : ℕ) : ℝ) + 1) * Real.pi / (2 * K) := rfl
    have hθ : Real.pi / (2 * K) ≤ CatalanMeasure.chebAngle K i := by
      rw [hθdef]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
      nlinarith [Real.pi_pos]
    have h2 : c * (Real.pi / (2 * K)) / Real.pi ≤ Real.sqrt (1 - posNode a K i ^ 2) := by
      refine le_trans ?_ hug
      apply div_le_div_of_nonneg_right _ Real.pi_pos.le
      exact mul_le_mul_of_nonneg_left hθ hcpos.le
    have e : c * (Real.pi / (2 * K)) / Real.pi = c / (2 * K) := by field_simp
    rw [e] at h2
    have h2K : 2 * (K : ℝ) ≤ ((K + L : ℕ) : ℝ) + 1 := by
      push_cast; have : (K : ℝ) ≤ L + 1 := by exact_mod_cast hKL
      linarith
    have h3 : c / (2 * (((K + L : ℕ) : ℝ) + 1)) ≤ c / (4 * K) := by
      apply div_le_div_of_nonneg_left hcpos.le (by positivity); nlinarith
    have e2 : c / (4 * K) = c / (2 * K) / 2 := by field_simp; ring
    linarith
  | right i =>
    rw [gapNodesKL_right]
    have hb := pos_node_bounds ha0 ha1 K (Fin.castLE hL i)
    have h1 := coord_neg (t := -posNode a K (Fin.castLE hL i)) (by linarith [hb.1])
    have h2 : c / (2 * (((K + L : ℕ) : ℝ) + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    linarith

/-- **`NodeCap` for the actual gap nodes.**  With `a = 2g/(1+g²)` and `J` nodes
`realCoordinate (gapNodesGen a J i)`: `g ≤ |y|`, `y ≤ 1 - umin` with `umin = √(1-a²)/(2(J+1))`
(so `log(1/umin)/n → 0` for `n` of order `J`), and the top count
`#{b : y_i ≤ y_b} ≤ C1 n (1 - y_i) + 1` for `y_i ≥ xc`, `C1 = J/(n · 2 xc √(1-a²))`
(= `((n0-g0)/n0) / (2 xc √(1-a²))` when `J = (n0-g0)N`, `n = n0 N`). -/
theorem nodeCap_gap {g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) {xc n : ℝ} (hxc : 0 < xc) (hn : 0 < n)
    (J : ℕ) :
    NodeCap g xc
      ((J : ℝ) / (n * (2 * xc * Real.sqrt (1 - (2 * g / (1 + g ^ 2)) ^ 2)))) n
      (Real.sqrt (1 - (2 * g / (1 + g ^ 2)) ^ 2) / (2 * ((J : ℝ) + 1)))
      (fun i : Fin J => OAI.InternalCatalan.realCoordinate
        (gapNodesGen (2 * g / (1 + g ^ 2)) J i)) := by
  have hd : 0 < 1 + g ^ 2 := by positivity
  have ha0 : 0 < 2 * g / (1 + g ^ 2) := by positivity
  have ha1 : 2 * g / (1 + g ^ 2) < 1 := by
    rw [div_lt_one hd]; nlinarith only [pow_pos (sub_pos.mpr hg1) 2]
  set a := 2 * g / (1 + g ^ 2) with ha
  have haa := gapSq_pos ha0 ha1
  set c := Real.sqrt (1 - a ^ 2) with hc
  have hcpos : 0 < c := Real.sqrt_pos.2 haa
  set K := (J + 1) / 2 with hK
  set L := J / 2 with hLdef
  have hJ : J = K + L := by omega
  have hL : L ≤ K := by omega
  have hKL : K ≤ L + 1 := by omega
  have hJr : (J : ℝ) = ((K + L : ℕ) : ℝ) := by exact_mod_cast hJ
  have hnode : ∀ i : Fin J, gapNodesGen a J i = gapNodesKL a K L hL (Fin.cast hJ i) := fun i => rfl
  refine ⟨fun i => (gap_nodes_coordinate hg0 hg1 J i).2, fun i => ?_, fun i hi => ?_⟩
  · beta_reduce; rw [hnode, hJr]; exact klGap ha0 ha1 hL hKL _
  · beta_reduce at hi ⊢
    have key : ∀ i' : Fin (K + L), xc ≤ OAI.InternalCatalan.realCoordinate (gapNodesKL a K L hL i') →
        ((Finset.univ.filter (fun b : Fin (K + L) =>
          OAI.InternalCatalan.realCoordinate (gapNodesKL a K L hL i') ≤
            OAI.InternalCatalan.realCoordinate (gapNodesKL a K L hL b))).card : ℝ) ≤
          ((K + L : ℕ) : ℝ) / (2 * xc * c) *
            (1 - OAI.InternalCatalan.realCoordinate (gapNodesKL a K L hL i')) + 1 := by
      intro i'
      induction i' using Fin.addCases with
      | left i0 => rw [gapNodesKL_left]; exact klTop ha0 ha1 hL hKL hxc i0
      | right i0 =>
        intro hh
        exfalso
        rw [gapNodesKL_right] at hh
        have hb := pos_node_bounds ha0 ha1 K (Fin.castLE hL i0)
        have := coord_neg (t := -posNode a K (Fin.castLE hL i0)) (by linarith [hb.1])
        linarith
    rw [hnode] at hi ⊢
    have hk := key _ hi
    have hcard : (Finset.univ.filter (fun b : Fin J =>
        OAI.InternalCatalan.realCoordinate (gapNodesKL a K L hL (Fin.cast hJ i)) ≤
          OAI.InternalCatalan.realCoordinate (gapNodesKL a K L hL (Fin.cast hJ b)))).card ≤
        (Finset.univ.filter (fun b : Fin (K + L) =>
          OAI.InternalCatalan.realCoordinate (gapNodesKL a K L hL (Fin.cast hJ i)) ≤
            OAI.InternalCatalan.realCoordinate (gapNodesKL a K L hL b))).card := by
      apply Finset.card_le_card_of_injOn (Fin.cast hJ)
      · intro b hb; simpa using hb
      · exact (Fin.cast_injective hJ).injOn
    refine (Nat.cast_le.2 hcard).trans (hk.trans ?_)
    rw [← hJr]
    have hn' := hn.ne'
    have hc' := hcpos.ne'
    have hx' := hxc.ne'
    apply le_of_eq
    field_simp

end GapCap
end CatalanMeasure.Signed
#print axioms CatalanMeasure.Signed.klTop
#print axioms CatalanMeasure.Signed.nodeCap_gap
