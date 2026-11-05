module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.GlueCount3
@[expose] public section
set_option Elab.async false

/-!
# Theorem MT (b): the count
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem famData_mem_relaxDom (K D1 m η elo : ℕ) (k0 : ℤ) (y u : Fin m → Fin K → ZMod p)
    (a : LinearMap.ker (totalCond P N p K D1 m η elo k0 y u)) :
    famData y u a.1 ∈ relaxDom P N p K D1 k0 := by
  have hΨ := LinearMap.mem_ker.mp a.2
  have hv1 := congrArg Prod.snd hΨ
  rw [mem_relaxDom]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext i k
    show famData y u a.1 (Fin.castAdd (D1 + 1) i) (Fin.natAdd K k) = 0
    rw [famData_left]; exact emb1_natAdd _ k
  · funext j k
    show famData y u a.1 (Fin.natAdd D1 j) (Fin.castAdd K k) = 0
    rw [famData_right]; exact emb2_castAdd _ k
  · intro d k hk
    have h := congrFun (congrArg Prod.fst hv1) ⟨(d, k), by simp [mmP, hk]⟩
    show famData y u a.1 (Fin.castAdd (D1 + 1) d) (Fin.castAdd K k) +
      famData y u a.1 (Fin.natAdd D1 d.succ) (Fin.natAdd K k) = 0
    rw [famData_left, famData_right, emb1_castAdd, emb2_natAdd]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have h' : ∑ i, (y i k * a.1.1 i d + u i k * a.1.2 i d.succ) = 0 := by
      simpa [totalCond, virtCond, cS, cT, LinearMap.sum_apply] using h
    simp only [Finset.sum_add_distrib] at h'
    simp only [mul_comm] at h' ⊢
    exact h'
  · intro d k hk
    have h := congrFun (congrArg Prod.fst (congrArg Prod.snd hv1)) ⟨(d, k), by simp [mmM, hk]⟩
    show famData y u a.1 (Fin.natAdd D1 d.succ) (Fin.natAdd K k) -
      famData y u a.1 (Fin.castAdd (D1 + 1) d) (Fin.castAdd K k) = 0
    rw [famData_left, famData_right, emb1_castAdd, emb2_natAdd]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have h' : ∑ i, (u i k * a.1.2 i d.succ - y i k * a.1.1 i d) = 0 := by
      simpa [totalCond, virtCond, cS, cT, LinearMap.sum_apply] using h
    simp only [Finset.sum_sub_distrib] at h'
    simp only [mul_comm] at h' ⊢
    exact h'
  · intro k hk
    have h := congrFun (congrArg Prod.snd (congrArg Prod.snd hv1)) ⟨k, by simp [mm0, hk]⟩
    show famData y u a.1 (Fin.natAdd D1 0) (Fin.natAdd K k) = 0
    rw [famData_right, emb2_natAdd]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have h' : ∑ i, u i k * a.1.2 i 0 = 0 := by
      simpa [totalCond, virtCond, cS, cT, LinearMap.sum_apply] using h
    simp only [mul_comm] at h' ⊢
    exact h'

theorem famData_injective {K D1 m : ℕ} (y u : Fin m → Fin K → ZMod p)
    (hy : LinearIndependent (ZMod p) y) (hu : LinearIndependent (ZMod p) u) :
    Function.Injective (famData (D1 := D1) y u) := by
  refine Thin.injective_of_zero _ fun a h0 => ?_
  have h1 : ∀ d : Fin D1, ∀ i, a.1 i d = 0 := by
    intro d
    have := congrFun h0 (Fin.castAdd (D1 + 1) d)
    rw [famData_left] at this
    have h2 : ∑ i, a.1 i d • y i = 0 := by
      have := congrArg (fl1 K K) this
      rw [fl1_emb1] at this
      simpa using this
    exact Fintype.linearIndependent_iff.mp hy _ h2
  have h2 : ∀ d : Fin (D1 + 1), ∀ i, a.2 i d = 0 := by
    intro d
    have := congrFun h0 (Fin.natAdd D1 d)
    rw [famData_right] at this
    have h2 : ∑ i, a.2 i d • u i = 0 := by
      have := congrArg (fl2 K K) this
      rw [fl2_emb2] at this
      simpa using this
    exact Fintype.linearIndependent_iff.mp hu _ h2
  refine Prod.ext (funext fun i => funext fun d => h1 d i) (funext fun i => funext fun d => h2 d i)

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
