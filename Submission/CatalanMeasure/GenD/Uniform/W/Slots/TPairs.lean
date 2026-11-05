module
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.Count
@[expose] public section
set_option Elab.async false

/-!
# T- pairs as a slot system (the accepted T-raw count, re-derived on the abstraction)

`tSystem` : centred pairs `e_{c+d'} - e_{c-d'}`, `lam d = 2 (X-1)^h U_d`, `Ty = Σ y_k T_{k0+k}`,
`Gy = (X²-1) Σ y_k U_{k0+k-1}`.  `tRaw_le_nullity'` is the T-raw count, now a three-line corollary
of `slot_nullity_pi` and `finrank_atoms_ge`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Slots
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The virtual pairs. -/
def tBad (P : Parameters) (N p : ℕ) [Fact p.Prime] (K D : ℕ) (k0 : ℤ) :
    Finset (Fin D × Fin K) :=
  Finset.univ.filter (fun dk : Fin D × Fin K => ¬ Good P N p k0 dk.1 dk.2)

theorem tBad_card (K D : ℕ) (k0 : ℤ) : (tBad P N p K D k0).card = virtCount P N p K D k0 := rfl

/-- The T- pair slot system. -/
def tSystem (P : Parameters) (N p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (K D : ℕ) (k0 : ℤ)
    (hD : D ≤ (p - 1) / 2) : SlotSystem P N p where
  K := K
  D := D
  emax := P.h N + D
  prof := ⟨tyMap p K k0, gyMap p K k0⟩
  lam := fun d => lam P N p d
  rows := tRows P N p K D k0
  dom := badDom p K D (tBad P N p K D k0)
  deg := fun d => by
    have := lam_natDegree_le (P := P) (N := N) hp2 (d : ℕ)
    have := d.isLt
    omega
  repU := fun x hx => intrinsicU_tRows hp2 k0 x (fun d k hg => hx ⟨d, k⟩ (by simp [tBad, hg]))
  repT := fun x hx => intrinsicT_tRows hp2 k0 x (fun d k hg => hx ⟨d, k⟩ (by simp [tBad, hg]))
  inj := fun x hx h0 => tRows_injective_on hp2 hD k0 x
    (fun d k hg => hx ⟨d, k⟩ (by simp [tBad, hg])) h0

theorem tSystem_psi (hp2 : p ≠ 2) {K D : ℕ} (k0 : ℤ) (hD : D ≤ (p - 1) / 2) (H J : ℕ) (a : ℤ) :
    (tSystem P N p hp2 K D k0 hD).prof.psi H J a = psiLin p K k0 H J a := rfl

/-- **Theorem T-raw** (same statement as `Thin.tRaw_le_nullity`), derived from the slot API. -/
theorem tRaw_le_nullity' (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {K D e0 : ℕ} (k0 : ℤ) (hD : D ≤ (p - 1) / 2) (S : Finset (ℕ × ℤ))
    (hseen : ∀ j e (a : ℤ), P.b N ≤ j → j < P.L N → e0 ≤ e → e < P.h N + D →
      (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e = a * p → (j / p, a) ∈ S) :
    (D - e0) * (K - S.card) - virtCount P N p K D k0 ≤ nullity P N p := by
  classical
  obtain ⟨V, hVdef⟩ : ∃ V : Submodule (ZMod p) (Fin K → ZMod p),
      V = LinearMap.ker (seenMap p K k0 (P.H N) S) := ⟨_, rfl⟩
  have h1 : D * finrank (ZMod p) V ≤ nullity P N p + e0 * finrank (ZMod p) V +
      virtCount P N p K D k0 :=
    (tSystem P N p hp2 K D k0 hD).slot_nullity_dom hP hN hp2 hH V e0
      (fun j e a h1 h2 h3 h4 h5 y hy =>
        seenMap_apply_mem K k0 _ S y (hVdef ▸ hy) _ _ (hseen j e a h1 h2 h3 h4 h5))
      (tBad P N p K D k0) (fun x => Iff.rfl)
  have hk : K - S.card ≤ finrank (ZMod p) V := by
    rw [hVdef]; exact kappa_ge (seenMap p K k0 (P.H N) S)
  have h3 : (D - e0) * (K - S.card) ≤ (D - e0) * finrank (ZMod p) V :=
    Nat.mul_le_mul_left _ hk
  have h4 : (D - e0) * finrank (ZMod p) V = D * finrank (ZMod p) V - e0 * finrank (ZMod p) V :=
    Nat.sub_mul _ _ _
  omega

#print axioms tRaw_le_nullity'
end
end CatalanMeasure.GenD.Uniform.W.Slots
