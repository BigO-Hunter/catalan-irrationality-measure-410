module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.MixRows
@[expose] public section
set_option Elab.async false

/-!
# Sum of two slot systems (mixed slot systems)

`addSystem S1 S2 hsep` has profile coordinates `K1 + K2` and slots `D1 + D2`; a datum `x` lies in the
domain when its `(slots 1, coords 1)` block lies in `S1.dom`, its `(slots 2, coords 2)` block lies in
`S2.dom` and the two off-diagonal blocks vanish.  The rows are `S1.rows (x₁₁) + S2.rows (x₂₂)`;
`hsep` (independence of the two row families) gives injectivity.

* `addSystem_psi`: the source covector is the sum of the two covectors on the two coordinate blocks.
* `finrank_atoms_add_ge`: the atoms `dom ⊓ Π V` for `V = V₁ ⊕ V₂` have dimension at least
  `D₁ dim V₁ + D₂ dim V₂ - |bad₁| - |bad₂|`.
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Restriction of a profile vector to the first / second coordinate block. -/
def fl1 (K1 K2 : ℕ) : (Fin (K1 + K2) → ZMod p) →ₗ[ZMod p] (Fin K1 → ZMod p) :=
  LinearMap.funLeft (ZMod p) (ZMod p) (Fin.castAdd K2)

def fl2 (K1 K2 : ℕ) : (Fin (K1 + K2) → ZMod p) →ₗ[ZMod p] (Fin K2 → ZMod p) :=
  LinearMap.funLeft (ZMod p) (ZMod p) (Fin.natAdd K1)

theorem fl1_apply (K1 K2 : ℕ) (y : Fin (K1 + K2) → ZMod p) (k : Fin K1) :
    fl1 K1 K2 y k = y (Fin.castAdd K2 k) := rfl

theorem fl2_apply (K1 K2 : ℕ) (y : Fin (K1 + K2) → ZMod p) (k : Fin K2) :
    fl2 K1 K2 y k = y (Fin.natAdd K1 k) := rfl

/-- The sum of two profile maps. -/
def profAdd {K1 K2 : ℕ} (F1 : Prof p K1) (F2 : Prof p K2) : Prof p (K1 + K2) where
  Ty := F1.Ty.comp (fl1 K1 K2) + F2.Ty.comp (fl2 K1 K2)
  Gy := F1.Gy.comp (fl1 K1 K2) + F2.Gy.comp (fl2 K1 K2)

/-- The four blocks of a datum. -/
def blk11 (D1 D2 K1 K2 : ℕ) :
    (Fin (D1 + D2) → Fin (K1 + K2) → ZMod p) →ₗ[ZMod p] (Fin D1 → Fin K1 → ZMod p) where
  toFun x d k := x (Fin.castAdd D2 d) (Fin.castAdd K2 k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def blk22 (D1 D2 K1 K2 : ℕ) :
    (Fin (D1 + D2) → Fin (K1 + K2) → ZMod p) →ₗ[ZMod p] (Fin D2 → Fin K2 → ZMod p) where
  toFun x d k := x (Fin.natAdd D1 d) (Fin.natAdd K1 k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def blk12 (D1 D2 K1 K2 : ℕ) :
    (Fin (D1 + D2) → Fin (K1 + K2) → ZMod p) →ₗ[ZMod p] (Fin D1 → Fin K2 → ZMod p) where
  toFun x d k := x (Fin.castAdd D2 d) (Fin.natAdd K1 k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def blk21 (D1 D2 K1 K2 : ℕ) :
    (Fin (D1 + D2) → Fin (K1 + K2) → ZMod p) →ₗ[ZMod p] (Fin D2 → Fin K1 → ZMod p) where
  toFun x d k := x (Fin.natAdd D1 d) (Fin.castAdd K2 k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem intrinsicU_add' (c c' : Fin (P.n N) → ZMod p) :
    intrinsicU P N p (c + c') = intrinsicU P N p c + intrinsicU P N p c' := by
  simp [intrinsicU, add_mul, Finset.sum_add_distrib]

theorem intrinsicT_add' (c c' : Fin (P.n N) → ZMod p) :
    intrinsicT P N p (c + c') = intrinsicT P N p c + intrinsicT P N p c' := by
  simp [intrinsicT, add_mul, Finset.sum_add_distrib]

/-- The domain of the sum system. -/
def addDom (S1 S2 : SlotSystem P N p) :
    Submodule (ZMod p) (Fin (S1.D + S2.D) → Fin (S1.K + S2.K) → ZMod p) :=
  (S1.dom.comap (blk11 S1.D S2.D S1.K S2.K) ⊓ S2.dom.comap (blk22 S1.D S2.D S1.K S2.K)) ⊓
    (LinearMap.ker (blk12 S1.D S2.D S1.K S2.K) ⊓ LinearMap.ker (blk21 S1.D S2.D S1.K S2.K))

theorem mem_addDom (S1 S2 : SlotSystem P N p) (x : Fin (S1.D + S2.D) → Fin (S1.K + S2.K) → ZMod p) :
    x ∈ addDom S1 S2 ↔ blk11 S1.D S2.D S1.K S2.K x ∈ S1.dom ∧ blk22 S1.D S2.D S1.K S2.K x ∈ S2.dom ∧
      blk12 S1.D S2.D S1.K S2.K x = 0 ∧ blk21 S1.D S2.D S1.K S2.K x = 0 := by
  simp [addDom, and_assoc]

/-- A datum with vanishing off-diagonal blocks is determined by its diagonal blocks. -/
theorem eq_zero_of_blocks (S1 S2 : SlotSystem P N p)
    (x : Fin (S1.D + S2.D) → Fin (S1.K + S2.K) → ZMod p)
    (h11 : blk11 S1.D S2.D S1.K S2.K x = 0) (h22 : blk22 S1.D S2.D S1.K S2.K x = 0)
    (h12 : blk12 S1.D S2.D S1.K S2.K x = 0) (h21 : blk21 S1.D S2.D S1.K S2.K x = 0) : x = 0 := by
  funext d k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) d <;>
    refine Fin.addCases (fun a => ?_) (fun b => ?_) k
  · exact congrFun (congrFun h11 i) a
  · exact congrFun (congrFun h12 i) b
  · exact congrFun (congrFun h21 j) a
  · exact congrFun (congrFun h22 j) b

/-- **The sum of two slot systems.** -/
def addSystem (S1 S2 : SlotSystem P N p)
    (hsep : ∀ a ∈ S1.dom, ∀ b ∈ S2.dom, S1.rows a + S2.rows b = 0 → a = 0 ∧ b = 0) :
    SlotSystem P N p where
  K := S1.K + S2.K
  D := S1.D + S2.D
  emax := max S1.emax S2.emax
  prof := profAdd S1.prof S2.prof
  lam := Fin.append S1.lam S2.lam
  rows := S1.rows.comp (blk11 S1.D S2.D S1.K S2.K) + S2.rows.comp (blk22 S1.D S2.D S1.K S2.K)
  dom := addDom S1 S2
  deg := fun d => by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) d
    · rw [Fin.append_left]; exact lt_of_lt_of_le (S1.deg i) (le_max_left _ _)
    · rw [Fin.append_right]; exact lt_of_lt_of_le (S2.deg j) (le_max_right _ _)
  repU := fun x hx => by
    obtain ⟨h1, h2, h3, h4⟩ := (mem_addDom S1 S2 x).mp hx
    simp only [LinearMap.add_apply, LinearMap.comp_apply]
    rw [intrinsicU_add', mul_add, S1.repU _ h1, S2.repU _ h2, Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.append_left]
      congr 2
      show (S1.prof.Ty (blk11 S1.D S2.D S1.K S2.K x i)) = _
      have hz : fl2 S1.K S2.K (x (Fin.castAdd S2.D i)) = 0 := congrFun h3 i
      show _ = (S1.prof.Ty.comp (fl1 S1.K S2.K) + S2.prof.Ty.comp (fl2 S1.K S2.K)) (x (Fin.castAdd S2.D i))
      rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hz, map_zero, add_zero]
      rfl
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fin.append_right]
      congr 2
      have hz : fl1 S1.K S2.K (x (Fin.natAdd S1.D j)) = 0 := congrFun h4 j
      show _ = (S1.prof.Ty.comp (fl1 S1.K S2.K) + S2.prof.Ty.comp (fl2 S1.K S2.K)) (x (Fin.natAdd S1.D j))
      rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hz, map_zero, zero_add]
      rfl
  repT := fun x hx => by
    obtain ⟨h1, h2, h3, h4⟩ := (mem_addDom S1 S2 x).mp hx
    simp only [LinearMap.add_apply, LinearMap.comp_apply]
    rw [intrinsicT_add', mul_add, S1.repT _ h1, S2.repT _ h2, Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.append_left]
      congr 2
      show (S1.prof.Gy (blk11 S1.D S2.D S1.K S2.K x i)) = _
      have hz : fl2 S1.K S2.K (x (Fin.castAdd S2.D i)) = 0 := congrFun h3 i
      show _ = (S1.prof.Gy.comp (fl1 S1.K S2.K) + S2.prof.Gy.comp (fl2 S1.K S2.K)) (x (Fin.castAdd S2.D i))
      rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hz, map_zero, add_zero]
      rfl
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fin.append_right]
      congr 2
      have hz : fl1 S1.K S2.K (x (Fin.natAdd S1.D j)) = 0 := congrFun h4 j
      show _ = (S1.prof.Gy.comp (fl1 S1.K S2.K) + S2.prof.Gy.comp (fl2 S1.K S2.K)) (x (Fin.natAdd S1.D j))
      rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hz, map_zero, zero_add]
      rfl
  inj := fun x hx h0 => by
    obtain ⟨h1, h2, h3, h4⟩ := (mem_addDom S1 S2 x).mp hx
    simp only [LinearMap.add_apply, LinearMap.comp_apply] at h0
    obtain ⟨e1, e2⟩ := hsep _ h1 _ h2 h0
    exact eq_zero_of_blocks S1 S2 x e1 e2 h3 h4

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
