module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.Relax3
@[expose] public section
set_option Elab.async false

/-!
# The relaxed mixed slot system and its atom count

`mtSystem'` : T- pairs (offsets `1..D1`) and T+ pairs (offsets `0..D1`, period form) about the same
centres, with domain `relaxDom` (one linear condition per missing row, `RelaxOK`).
`mixMiss` is the number of missing rows; `finrank_atoms_relax_ge` is the atom count
`D1 dim V1 + (D1+1) dim V2 ≤ dim atoms + mixMiss`.
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem RelaxOK.zero {K D1 : ℕ} (k0 : ℤ) :
    RelaxOK P N p k0 (0 : Fin D1 → Fin K → ZMod p) (0 : Fin (D1 + 1) → Fin K → ZMod p) :=
  ⟨fun _ _ _ => by simp, fun _ _ _ => by simp, fun _ _ => by simp⟩

theorem RelaxOK.add {K D1 : ℕ} {k0 : ℤ} {a a' : Fin D1 → Fin K → ZMod p}
    {b b' : Fin (D1 + 1) → Fin K → ZMod p} (h : RelaxOK P N p k0 a b) (h' : RelaxOK P N p k0 a' b') :
    RelaxOK P N p k0 (a + a') (b + b') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨fun d k hk => ?_, fun d k hk => ?_, fun k hk => ?_⟩
  · simp only [Pi.add_apply]; linear_combination h1 d k hk + h1' d k hk
  · simp only [Pi.add_apply]; linear_combination h2 d k hk + h2' d k hk
  · simp only [Pi.add_apply]; linear_combination h3 k hk + h3' k hk

theorem RelaxOK.smul {K D1 : ℕ} {k0 : ℤ} {a : Fin D1 → Fin K → ZMod p}
    {b : Fin (D1 + 1) → Fin K → ZMod p} (c : ZMod p) (h : RelaxOK P N p k0 a b) :
    RelaxOK P N p k0 (c • a) (c • b) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun d k hk => ?_, fun d k hk => ?_, fun k hk => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]; linear_combination c * h1 d k hk
  · simp only [Pi.smul_apply, smul_eq_mul]; linear_combination c * h2 d k hk
  · simp only [Pi.smul_apply, smul_eq_mul]; linear_combination c * h3 k hk

/-- The relaxed domain. -/
def relaxDom (P : Parameters) (N p : ℕ) [Fact p.Prime] (K D1 : ℕ) (k0 : ℤ) :
    Submodule (ZMod p) (Fin (D1 + (D1 + 1)) → Fin (K + K) → ZMod p) where
  carrier := {x | blk12 D1 (D1 + 1) K K x = 0 ∧ blk21 D1 (D1 + 1) K K x = 0 ∧
    RelaxOK P N p k0 (blk11 D1 (D1 + 1) K K x) (blk22 D1 (D1 + 1) K K x)}
  add_mem' := fun {x y} hx hy => by
    obtain ⟨a1, a2, a3⟩ := hx
    obtain ⟨b1, b2, b3⟩ := hy
    refine ⟨?_, ?_, ?_⟩
    · rw [map_add, a1, b1, add_zero]
    · rw [map_add, a2, b2, add_zero]
    · rw [map_add, map_add]; exact a3.add b3
  zero_mem' := by
    refine ⟨map_zero _, map_zero _, ?_⟩
    rw [map_zero, map_zero]; exact RelaxOK.zero k0
  smul_mem' := fun c x hx => by
    obtain ⟨a1, a2, a3⟩ := hx
    refine ⟨?_, ?_, ?_⟩
    · rw [map_smul, a1, smul_zero]
    · rw [map_smul, a2, smul_zero]
    · rw [map_smul, map_smul]; exact a3.smul c

theorem mem_relaxDom (K D1 : ℕ) (k0 : ℤ) (x : Fin (D1 + (D1 + 1)) → Fin (K + K) → ZMod p) :
    x ∈ relaxDom P N p K D1 k0 ↔ blk12 D1 (D1 + 1) K K x = 0 ∧ blk21 D1 (D1 + 1) K K x = 0 ∧
      RelaxOK P N p k0 (blk11 D1 (D1 + 1) K K x) (blk22 D1 (D1 + 1) K K x) := Iff.rfl

theorem eq_zero_of_blocks' {D1 D2 K1 K2 : ℕ} (x : Fin (D1 + D2) → Fin (K1 + K2) → ZMod p)
    (h11 : blk11 D1 D2 K1 K2 x = 0) (h22 : blk22 D1 D2 K1 K2 x = 0)
    (h12 : blk12 D1 D2 K1 K2 x = 0) (h21 : blk21 D1 D2 K1 K2 x = 0) : x = 0 := by
  funext d k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) d <;>
    refine Fin.addCases (fun a => ?_) (fun b => ?_) k
  · exact congrFun (congrFun h11 i) a
  · exact congrFun (congrFun h12 i) b
  · exact congrFun (congrFun h21 j) a
  · exact congrFun (congrFun h22 j) b

/-- The relaxed mixed T- / T+ slot system. -/
def mtSystem' (P : Parameters) (N p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hph : p ≤ P.h N + (p - 1) / 2) (K D1 : ℕ) (k0 : ℤ) (hD : D1 ≤ (p - 1) / 2) :
    SlotSystem P N p where
  K := K + K
  D := D1 + (D1 + 1)
  emax := max (P.h N + D1) (P.h N + (D1 + 1))
  prof := profAdd (⟨tyMap p K k0, gyMap p K k0⟩ : Prof p K) (⟨tpTy p K k0, tpGy p K k0⟩ : Prof p K)
  lam := Fin.append (fun d : Fin D1 => Thin.lam P N p (d : ℕ)) (fun d : Fin (D1 + 1) => tpLam P N p (d : ℕ))
  rows := (tRows P N p K D1 k0).comp (blk11 D1 (D1 + 1) K K) +
    (tpRows P N p K (D1 + 1) k0).comp (blk22 D1 (D1 + 1) K K)
  dom := relaxDom P N p K D1 k0
  deg := fun d => by
    have hpo := p_odd_half hp2
    refine Fin.addCases (fun i => ?_) (fun j => ?_) d
    · rw [Fin.append_left]
      have h1 := lam_natDegree_le (P := P) (N := N) hp2 (i : ℕ)
      have h2 : (i : ℕ) < D1 := i.isLt
      exact lt_of_lt_of_le (by omega) (le_max_left _ _)
    · rw [Fin.append_right]
      have h1 := tpLam_natDegree_le (P := P) (N := N) hp2 (j : ℕ)
      have h2 : (j : ℕ) < D1 + 1 := j.isLt
      exact lt_of_lt_of_le (by omega) (le_max_right _ _)
  repU := fun x hx => by
    obtain ⟨h3, h4, hr⟩ := (mem_relaxDom K D1 k0 x).mp hx
    simp only [LinearMap.add_apply, LinearMap.comp_apply]
    rw [intrinsicU_add', mix_repU hp2 hph k0 _ _ hr]
    conv_rhs => rw [Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.append_left]
      congr 2
      have hz : fl2 K K (x (Fin.castAdd (D1 + 1) i)) = 0 := congrFun h3 i
      show _ = (tyMap p K k0 ∘ₗ fl1 K K + tpTy p K k0 ∘ₗ fl2 K K) (x (Fin.castAdd (D1 + 1) i))
      rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hz, map_zero, add_zero]
      rfl
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fin.append_right]
      congr 2
      have hz : fl1 K K (x (Fin.natAdd D1 j)) = 0 := congrFun h4 j
      show _ = (tyMap p K k0 ∘ₗ fl1 K K + tpTy p K k0 ∘ₗ fl2 K K) (x (Fin.natAdd D1 j))
      rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hz, map_zero, zero_add]
      rfl
  repT := fun x hx => by
    obtain ⟨h3, h4, hr⟩ := (mem_relaxDom K D1 k0 x).mp hx
    simp only [LinearMap.add_apply, LinearMap.comp_apply]
    rw [intrinsicT_add', mix_repT hp2 hph k0 _ _ hr]
    conv_rhs => rw [Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.append_left]
      congr 2
      have hz : fl2 K K (x (Fin.castAdd (D1 + 1) i)) = 0 := congrFun h3 i
      show _ = (gyMap p K k0 ∘ₗ fl1 K K + tpGy p K k0 ∘ₗ fl2 K K) (x (Fin.castAdd (D1 + 1) i))
      rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hz, map_zero, add_zero]
      rfl
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fin.append_right]
      congr 2
      have hz : fl1 K K (x (Fin.natAdd D1 j)) = 0 := congrFun h4 j
      show _ = (gyMap p K k0 ∘ₗ fl1 K K + tpGy p K k0 ∘ₗ fl2 K K) (x (Fin.natAdd D1 j))
      rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hz, map_zero, zero_add]
      rfl
  inj := fun x hx h0 => by
    obtain ⟨h3, h4, hr⟩ := (mem_relaxDom K D1 k0 x).mp hx
    simp only [LinearMap.add_apply, LinearMap.comp_apply] at h0
    obtain ⟨e1, e2⟩ := mix_sep_relax hp2 hD k0 _ _ hr (fun r => congrFun h0 r)
    exact eq_zero_of_blocks' x e1 e2 h3 h4

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
