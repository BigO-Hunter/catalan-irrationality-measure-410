module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.Check.HdomSound
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts3.GraphJets
@[expose] public section
set_option Elab.async false

/-!
# Generic graph polynomial `hG`: a coordinate with a long Taylor order at 1 is a low-degree polynomial in the position
-/
namespace CatalanMeasure.GenD.Uniform.W.Charts6.Check
open Polynomial Finset Module CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W.Prof (Packet emb chartMap Mx)

noncomputable section
variable {p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

theorem hG_sound {pk : Packet} {m : Meta} {win : List Aff} {cs : Cert} {N : ℕ} {x : Fin p → Fin pk.d → Fp}
    (C : Ctx pk m win N x) (idx c0 : ℕ) (hc0 : pcOf m idx = some c0) (hc0n : c0 < pk.n) (req : Aff) (r : ℕ)
    (hr : r ≤ p) (h : tOK pk m win cs Pt.p1 [(1, idx)] req = true)
    (hreq : ((p - r : ℕ) : ℤ) ≤ req.eval (N : ℤ) (((p : ℤ) - 1) / 2)) (η : Fp) :
    ∃ G : Fp[X], G.degree < (r : WithBot ℕ) ∧
      ∀ e : Fin p, G.eval (η - ((e : ℕ) : Fp)) = emb pk p pk.n (x e) ⟨c0, hc0n⟩ := by
  have key := T1_sound C Pt.p1 1 (Or.inl ⟨rfl, rfl⟩) idx req h
  let low : (Fin pk.d → Fp) →ₗ[Fp] Fp := (LinearMap.proj (⟨c0, hc0n⟩ : Fin pk.n)).comp (emb pk p pk.n)
  obtain ⟨G, hGd, hGe⟩ := hG_of_taylor low η r hr x (fun k hk => by
    have h1 := key k (by omega)
    simp only [hc0, polAt, dif_pos hc0n, polx] at h1
    rw [coeffPoly_taylor (fun e => emb pk p pk.n (x e) ⟨c0, hc0n⟩) k] at h1
    simp only [Charts3.taylorJet, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, map_sum,
      map_smul, one_pow, mul_one, smul_eq_mul, low, LinearMap.comp_apply]
    exact h1)
  exact ⟨G, hGd, fun e => by rw [hGe e]; rfl⟩

end
end CatalanMeasure.GenD.Uniform.W.Charts6.Check
