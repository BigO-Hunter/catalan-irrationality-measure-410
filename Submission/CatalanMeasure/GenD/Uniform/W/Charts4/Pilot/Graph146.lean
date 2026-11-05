module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Hdom146
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts3.GraphJets
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Prof.Pilot146
  CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3 Finset
  CatalanMeasure.GenD.D58.Odd CatalanMeasure.Parametric
noncomputable section
variable {N p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

theorem design_q (N : ℕ) : design.q N = 3 * N := rfl
theorem design_H (N : ℕ) : design.H N = 78 * N := by
  simp [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q,
    Parameters.g, Parameters.h, design]; ring

theorem geom_qmod (h : Win N p) : design.q N % p = 3 * N := by
  rw [design_q]; exact Nat.mod_eq_of_lt (by have := h.2.1; omega)

theorem geom_qdiv (h : Win N p) : design.q N / p = 0 := by
  rw [design_q]; exact Nat.div_eq_of_lt (by have := h.2.1; omega)

/-- The graph functional `jet_0` (coordinate 42). -/
def low146 (p : ℕ) [Fact p.Prime] : (Fin packetO.d → ZMod p) →ₗ[ZMod p] ZMod p :=
  (LinearMap.proj (42 : Fin 44)).comp (emb packetO p 44)

theorem hG_pilot (hW : Win N p) (x : Fin p → Fin packetO.d → Fp) (hker : JetKer N p x) :
    ∃ G : Fp[X], G.degree < ((design.q N % p : ℕ) : WithBot ℕ) ∧
      ∀ e : Fin p, G.eval ((((design.H N : ℤ) - 1 - e : ℤ)) : Fp) = low146 p (x e) := by
  have hq := geom_qmod hW
  have h3 := wd3 hW; have h4 := wd4 hW
  have hj3 : ∀ k, jetP N p 3 k = Charts3.taylorJet (m := p) (d := packetO.d) 1 (0 + k) := by
    intro k; simp [jetP]
  have hj4 : ∀ k, jetP N p 4 k = Charts3.taylorJet (m := p) (d := packetO.d) 1 (wd N p 3 + k) := by
    intro k; simp [jetP]
  have hv : ∀ g, g < 11 → (hasRow g (unitL 42) = true) → ∀ k, k < wd N p g →
      low146 p (jetP N p g k x) = 0 := by
    intro g hg hr k hk
    have := vanish_hasRow x hker g hg k hk (unitL 42) hr
    have e := sum_unitL (42 : Fin 44) (emb packetO p 44 (jetP N p g k x))
    exact e.symm.trans this
  have hchain := chain2 (Q := fun j => low146 p (Charts3.taylorJet (m := p) (d := packetO.d) 1 j x) = 0)
    (a := wd N p 3) (b := wd N p 4)
    (fun k hk => by have := hv 3 (by norm_num) pt1_jet0.1 k hk; rw [hj3 k] at this; simpa using this)
    (fun k hk => by have := hv 4 (by norm_num) pt1_jet0.2 k hk; rw [hj4 k] at this; exact this)
  have := hG_of_taylor (low146 p) (((design.H N : ℤ) - 1 : ℤ) : Fp) (design.q N % p)
    (by have := hW.2.1; omega) x (fun k hk => hchain k (by omega))
  obtain ⟨G, hGd, hGe⟩ := this
  refine ⟨G, hGd, fun e => ?_⟩
  rw [← hGe e]
  congr 1
  push_cast
  ring

end
end CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O
