module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.PhysicalCoordinates
@[expose] public section
set_option Elab.async false

/-!
# The full physical tiling as a sum over blocks

For the linear equivalence `physicalTilingEquiv b h p` (tiling coordinates `((sym, asym), centres)` to
the `b p + 1` enlarged physical rows) and ANY family `F : ℕ → M` indexed by the enlarged row index,

    Σ_i (rows i) • F i
      = Σ_{k<b} Σ_{j<h} ( sym_{kj} (F(kp+j+1) + F(kp+p-j-1)) + asym_{kj} (F(kp+j+1) - F(kp+p-j-1)) )
        + u_0 F(0) + Σ_{k<b} u_{k+1} (F(kp) + F((k+1)p)).

(`u` = centre coordinates; the outer centre `u_0` is alone, every other `u_{k+1}` is the edge
between the centres `kp` and `(k+1)p`.)
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts4
open CatalanMeasure.GenD.Uniform.Prefix Finset
noncomputable section

theorem fullRowIndex_val (b h p : ℕ) (hp : p = 2 * h + 1) (i : RowLabels b h) :
    (fullRowIndexEquiv b h p hp i : ℕ) = labelPosition p i := rfl

theorem tiling_sum {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]
    (b h p : ℕ) (hp : p = 2 * h + 1) (h2 : (2 : K) ≠ 0)
    (t : TilingCoordinates (K := K) b h) (F : ℕ → M) :
    ∑ i : Fin (b * p + 1), (physicalTilingEquiv b h p hp h2 t i) • F i =
      (∑ k : Fin b, ∑ j : Fin h,
        (t.1.1 (finProdFinEquiv (k, j)) • (F (k * p + (j + 1)) + F (k * p + (p - (j + 1)))) +
         t.1.2 (finProdFinEquiv (k, j)) • (F (k * p + (j + 1)) - F (k * p + (p - (j + 1)))))) +
      t.2 0 • F 0 + ∑ k : Fin b, t.2 k.succ • (F (k * p) + F ((k + 1) * p)) := by
  have hc : ∑ k : Fin (b + 1), (centerMap (b + 1) t.2 k) • F (k.val * p) =
      t.2 0 • F 0 + ∑ k : Fin b, t.2 k.succ • (F (k * p) + F ((k + 1) * p)) := by
    have e0 : ∀ k : Fin (b + 1), (centerMap (b + 1) t.2 k) • F (k.val * p) =
        t.2 k • F (k.val * p) +
          (if h : k.val + 1 < b + 1 then t.2 ⟨k.val + 1, h⟩ else 0) • F (k.val * p) := by
      intro k; simp only [centerMap, LinearMap.coe_mk, AddHom.coe_mk, add_smul]
    simp_rw [e0]
    rw [Finset.sum_add_distrib, Fin.sum_univ_succ (f := fun k : Fin (b + 1) => t.2 k • F (k.val * p)),
      Fin.sum_univ_castSucc (f := fun k : Fin (b + 1) =>
        (if h : k.val + 1 < b + 1 then t.2 ⟨k.val + 1, h⟩ else 0) • F (k.val * p))]
    have e1 : ∀ k : Fin b, (if h : ((Fin.castSucc k : Fin (b + 1)) : ℕ) + 1 < b + 1 then
        t.2 ⟨((Fin.castSucc k : Fin (b + 1)) : ℕ) + 1, h⟩ else 0) = t.2 k.succ := fun k => by
      rw [dif_pos (by simp)]; rfl
    have e2 : ∑ k : Fin b, (if h : ((Fin.castSucc k : Fin (b + 1)) : ℕ) + 1 < b + 1 then
        t.2 ⟨((Fin.castSucc k : Fin (b + 1)) : ℕ) + 1, h⟩ else 0) • F ((Fin.castSucc k : Fin (b + 1)).val * p)
        = ∑ k : Fin b, t.2 k.succ • F (k.val * p) :=
      Finset.sum_congr rfl fun k _ => by rw [e1 k]; rfl
    rw [e2]
    have e3 : ∀ x : Fin b, F (x.val * p + p) = F ((x.val + 1) * p) := fun x => by rw [Nat.add_mul, one_mul]
    have e4 : ((Fin.last b : Fin (b + 1)) : ℕ) + 1 < b + 1 ↔ False := by simp
    simp only [Fin.val_zero, zero_mul, Fin.val_succ, Fin.val_last, e4, dite_false, zero_smul, add_zero,
      smul_add, Finset.sum_add_distrib]
    simp only [lt_irrefl, dite_false, zero_smul, add_zero, Nat.add_comm 1]
    abel
  have hpair : ∀ (x1 x2 : K) (a b' : M),
      (x1 + x2) • a + (x1 - x2) • b' = x1 • (a + b') + x2 • (a - b') := by
    intro x1 x2 a b'; simp only [add_smul, sub_smul, smul_add, smul_sub]; abel
  rw [← Equiv.sum_comp (fullRowIndexEquiv b h p hp)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool,
    physicalTiling_center, physicalTiling_pair_plus, physicalTiling_pair_minus, fullRowIndex_val,
    labelPosition, labelBlock, labelResidue, Nat.sub_sub, add_zero, hpair]
  rw [hc]
  abel

end
end CatalanMeasure.GenD.Uniform.W.Charts4
