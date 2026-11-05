module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.QSpan
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Geom
@[expose] public section
set_option Elab.async false

/-!
# Frobenius split of the slot polynomials, and coordinate bookkeeping

* `qY = X^p - 1`; `fpart Λ = Λ %ₘ qY`, `epart Λ = Λ /ₘ qY` (linear), `slot_comb` : `Λ = F + (Y-1) E`.
* `CK b ex` : the profile coordinates `(block, A_F|A_E|C_F|C_E) ⊕ (centre_F|centre_E) ⊕ extras`,
  with `ckEquiv : Fin K ≃ CK b ex` for `K = 4b + 2 + ex` (the packet order: block-major, then centre, then extras).
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts4
open CatalanMeasure.GenD.Uniform.Prefix Polynomial Finset
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def qY (p : ℕ) [Fact p.Prime] : (ZMod p)[X] := X ^ p - 1

theorem qY_monic : (qY p).Monic := by
  have := monic_X_pow_sub_C (1 : ZMod p) (Fact.out : p.Prime).ne_zero
  simpa [qY] using this

theorem qY_degree : (qY p).degree = p := by
  have := degree_X_pow_sub_C (R := ZMod p) (Fact.out : p.Prime).pos (1 : ZMod p)
  simpa [qY] using this

def fpart (p : ℕ) [Fact p.Prime] : (ZMod p)[X] →ₗ[ZMod p] (ZMod p)[X] := modByMonicHom (qY p)
def epart (p : ℕ) [Fact p.Prime] : (ZMod p)[X] →ₗ[ZMod p] (ZMod p)[X] := divByMonicHom (qY p)

theorem fpart_apply (Λ : (ZMod p)[X]) : fpart p Λ = Λ %ₘ qY p := rfl
theorem epart_apply (Λ : (ZMod p)[X]) : epart p Λ = Λ /ₘ qY p := rfl

theorem fpart_epart (Λ : (ZMod p)[X]) : fpart p Λ + (X ^ p - 1) * epart p Λ = Λ :=
  modByMonic_add_div Λ (qY p)

theorem fpart_degree (Λ : (ZMod p)[X]) : (fpart p Λ).degree < p := by
  have := degree_modByMonic_lt Λ (qY_monic (p := p))
  rwa [qY_degree] at this

theorem epart_degree (Λ : (ZMod p)[X]) (hΛ : Λ.degree < ((p + p : ℕ) : WithBot ℕ)) :
    (epart p Λ).degree < p := by
  by_contra hcon
  have hE : (p : WithBot ℕ) ≤ (epart p Λ).degree := not_lt.mp hcon
  have hq : ((X ^ p - 1) * epart p Λ).degree = (p : WithBot ℕ) + (epart p Λ).degree := by
    rw [degree_mul]; change (qY p).degree + _ = _; rw [qY_degree]
  have h1 : (X ^ p - 1) * epart p Λ = Λ - fpart p Λ := by
    have := fpart_epart Λ; linear_combination this
  have h2 : ((X ^ p - 1) * epart p Λ).degree < ((p + p : ℕ) : WithBot ℕ) := by
    rw [h1]
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt hΛ ?_)
    exact lt_trans (fpart_degree Λ) (by exact_mod_cast (by have := (Fact.out : p.Prime).pos; omega))
  rw [hq] at h2
  have h3 : (p : WithBot ℕ) + (p : WithBot ℕ) ≤ (p : WithBot ℕ) + (epart p Λ).degree :=
    add_le_add_right hE _
  have : ((p + p : ℕ) : WithBot ℕ) = (p : WithBot ℕ) + (p : WithBot ℕ) := by push_cast; rfl
  rw [this] at h2
  exact absurd h2 (not_lt.mpr h3)

/-- Splitting identity for a pair `F + (Y-1) E` against any coefficient `B`. -/
theorem slot_comb (Λ B : (ZMod p)[X]) :
    fpart p Λ * B + epart p Λ * (B * (X ^ p - 1)) = B * Λ := by
  have := fpart_epart Λ
  linear_combination B * this

/-- Coordinate kinds of the profile space. -/
abbrev CK (b ex : ℕ) := (Fin b × Fin 4) ⊕ (Fin 2 ⊕ Fin ex)

def ckEquiv {K b ex : ℕ} (hK : K = b * 4 + 2 + ex) : Fin K ≃ CK b ex :=
  (finCongr hK).trans <| finSumFinEquiv.symm.trans <|
    (Equiv.sumCongr (finSumFinEquiv.symm.trans (Equiv.sumCongr finProdFinEquiv.symm (Equiv.refl _)))
      (Equiv.refl _)).trans (Equiv.sumAssoc _ _ _)

end
end CatalanMeasure.GenD.Uniform.W.Charts4
