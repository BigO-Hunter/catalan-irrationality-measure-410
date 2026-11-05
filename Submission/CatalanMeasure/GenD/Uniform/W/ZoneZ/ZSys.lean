module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZInj
@[expose] public section
set_option Elab.async false

/-!
# The Theorem Z slot system

Data `x : Fin (D + D) → Fin (K + K) → F_p`: the diagonal blocks are the symmetric data `S`
(first `D` slots, first `K` profile coordinates) and the antisymmetric data `A`; the
off-diagonal blocks vanish.  The domain only asks `ZCons S A` (one condition per missing pair
member) and `A_0 = 0`.  Rows `tpRows S + aRows A`; slot polynomials `zpLam_d` (T+) and
`zaLam_d` (T-).  This is a `SlotSystem`, so `uResp_slot` gives the response formula.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Profile maps of the two pair types (`k0 = 0`). -/
def profTp' (p K : ℕ) [Fact p.Prime] : Prof p K := ⟨uyMap p K 0, tyMap p K 0⟩
def profTm' (p K : ℕ) [Fact p.Prime] : Prof p K := ⟨tyMap p K 0, gyMap p K 0⟩

/-- The domain of the Theorem Z system. -/
def zDom (P : Parameters) (N p K D : ℕ) [Fact p.Prime] :
    Submodule (ZMod p) (Fin (D + D) → Fin (K + K) → ZMod p) where
  carrier := {x | blk12 D D K K x = 0 ∧ blk21 D D K K x = 0 ∧
    ZCons P N p 0 (blk11 D D K K x) (blk22 D D K K x) ∧
    (∀ d : Fin D, (d : ℕ) = 0 → ∀ k, blk22 D D K K x d k = 0)}
  zero_mem' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · intro d k
      refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> simp [blk11, blk22]
    · intro d _ k; simp [blk22]
  add_mem' := by
    rintro x y ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩
    refine ⟨by simp [a1, b1], by simp [a2, b2], ?_, ?_⟩
    · intro d k
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have := (a3 d k).1 h; have := (b3 d k).1 h
        simp only [map_add, Pi.add_apply] at *; linear_combination (a3 d k).1 h + (b3 d k).1 h
      · simp only [map_add, Pi.add_apply] at *; linear_combination (a3 d k).2 h + (b3 d k).2 h
    · intro d hd k
      simp only [map_add, Pi.add_apply]; rw [a4 d hd k, b4 d hd k]; ring
  smul_mem' := by
    rintro c x ⟨a1, a2, a3, a4⟩
    refine ⟨by simp [a1], by simp [a2], ?_, ?_⟩
    · intro d k
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] at *
        linear_combination c * (a3 d k).1 h
      · simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] at *
        linear_combination c * (a3 d k).2 h
    · intro d hd k
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; rw [a4 d hd k]; ring

theorem mem_zDom {K D : ℕ} (x : Fin (D + D) → Fin (K + K) → ZMod p) :
    x ∈ zDom P N p K D ↔ blk12 D D K K x = 0 ∧ blk21 D D K K x = 0 ∧
      ZCons P N p 0 (blk11 D D K K x) (blk22 D D K K x) ∧
      (∀ d : Fin D, (d : ℕ) = 0 → ∀ k, blk22 D D K K x d k = 0) := Iff.rfl

theorem blocks_zero {K D : ℕ} (x : Fin (D + D) → Fin (K + K) → ZMod p)
    (h11 : blk11 D D K K x = 0) (h22 : blk22 D D K K x = 0) (h12 : blk12 D D K K x = 0)
    (h21 : blk21 D D K K x = 0) : x = 0 := by
  funext d k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) d <;>
    refine Fin.addCases (fun a => ?_) (fun b => ?_) k
  · exact congrFun (congrFun h11 i) a
  · exact congrFun (congrFun h12 i) b
  · exact congrFun (congrFun h21 j) a
  · exact congrFun (congrFun h22 j) b

/-- **The Theorem Z slot system.** -/
def zSys (P : Parameters) (N p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (K D : ℕ)
    (hD : D ≤ (p - 1) / 2 + 1) : SlotSystem P N p where
  K := K + K
  D := D + D
  emax := P.h N + (p - 1) + D
  prof := profAdd (profTp' p K) (profTm' p K)
  lam := Fin.append (fun d : Fin D => zpLam P N p d) (fun d : Fin D => zaLam P N p d)
  rows := (tpRows P N p K D 0).comp (blk11 D D K K) + (aRows P N p K D 0).comp (blk22 D D K K)
  dom := zDom P N p K D
  deg := fun d => by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) d
    · rw [Fin.append_left]
      have := zpLam_natDegree_le (P := P) (N := N) hp2 (i : ℕ)
      have := i.isLt
      omega
    · rw [Fin.append_right]
      have := zaLam_natDegree_le (P := P) (N := N) hp2 (j : ℕ)
      have := j.isLt
      omega
  repU := fun x hx => by
    obtain ⟨h3, h4, hc, _⟩ := (mem_zDom x).mp hx
    have key := intrinsicU_zRows (P := P) (N := N) hp2 0 (blk11 D D K K x) (blk22 D D K K x) hc
    have hrow : ((tpRows P N p K D 0).comp (blk11 D D K K) +
        (aRows P N p K D 0).comp (blk22 D D K K)) x =
        zRows P N p K D 0 (blk11 D D K K x) (blk22 D D K K x) := rfl
    rw [hrow, key, Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.append_left]
      congr 2
      have hz : fl2 K K (x (Fin.castAdd D i)) = 0 := congrFun h3 i
      show _ = (profTp' p K).Ty (fl1 K K (x (Fin.castAdd D i))) +
        (profTm' p K).Ty (fl2 K K (x (Fin.castAdd D i)))
      rw [hz, map_zero, add_zero]; rfl
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fin.append_right]
      congr 2
      have hz : fl1 K K (x (Fin.natAdd D j)) = 0 := congrFun h4 j
      show _ = (profTp' p K).Ty (fl1 K K (x (Fin.natAdd D j))) +
        (profTm' p K).Ty (fl2 K K (x (Fin.natAdd D j)))
      rw [hz, map_zero, zero_add]; rfl
  repT := fun x hx => by
    obtain ⟨h3, h4, hc, _⟩ := (mem_zDom x).mp hx
    have key := intrinsicT_zRows (P := P) (N := N) hp2 0 (blk11 D D K K x) (blk22 D D K K x) hc
    have hrow : ((tpRows P N p K D 0).comp (blk11 D D K K) +
        (aRows P N p K D 0).comp (blk22 D D K K)) x =
        zRows P N p K D 0 (blk11 D D K K x) (blk22 D D K K x) := rfl
    rw [hrow, key, Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.append_left]
      congr 2
      have hz : fl2 K K (x (Fin.castAdd D i)) = 0 := congrFun h3 i
      show _ = (profTp' p K).Gy (fl1 K K (x (Fin.castAdd D i))) +
        (profTm' p K).Gy (fl2 K K (x (Fin.castAdd D i)))
      rw [hz, map_zero, add_zero]; rfl
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fin.append_right]
      congr 2
      have hz : fl1 K K (x (Fin.natAdd D j)) = 0 := congrFun h4 j
      show _ = (profTp' p K).Gy (fl1 K K (x (Fin.natAdd D j))) +
        (profTm' p K).Gy (fl2 K K (x (Fin.natAdd D j)))
      rw [hz, map_zero, zero_add]; rfl
  inj := fun x hx h0 => by
    obtain ⟨h3, h4, hc, hA0⟩ := (mem_zDom x).mp hx
    have hrow : ((tpRows P N p K D 0).comp (blk11 D D K K) +
        (aRows P N p K D 0).comp (blk22 D D K K)) x =
        zRows P N p K D 0 (blk11 D D K K x) (blk22 D D K K x) := rfl
    rw [hrow] at h0
    obtain ⟨e1, e2⟩ := zRows_injective hp2 hD 0 _ _ hc hA0 h0
    exact blocks_zero x e1 e2 h3 h4

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
