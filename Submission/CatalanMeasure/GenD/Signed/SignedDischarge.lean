module

public import Submission.CatalanMeasure.GenD.Signed.RealPlace
public import Submission.CatalanMeasure.GenD.Signed.Energy

/-!
# Discharging `SignedClassBound` from a `SignedTrialBounds` instance (lane RP2, item 1)

Relabelling of the sign split `σ : Fin k ⊕ Fin q ≃ Fin n` onto `Fin.append xn gp` and of the
columns onto `Fin (k + q)`, and the proof that `signed_second_energy` gives the energy line of
`SignedClassBound` (the free-point class hypothesis of `signedSecondSheet`).
-/

@[expose] public section

namespace CatalanMeasure.Signed

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  OAI.InternalCatalan Filter Set

noncomputable section

section Relabel

/-- `Fin.append` is `Sum.elim` after `finSumFinEquiv.symm`. -/
theorem fin_append_eq_elim {k q : ℕ} (a : Fin k → ℝ) (b : Fin q → ℝ) (i : Fin (k + q)) :
    Fin.append a b i = Sum.elim a b (finSumFinEquiv.symm i) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- The relabelling `Fin (k + q) ≃ Fin n` of a sign split. -/
def splitEquiv {k q n : ℕ} (σ : Fin k ⊕ Fin q ≃ Fin n) : Fin (k + q) ≃ Fin n :=
  finSumFinEquiv.symm.trans σ

/-- The negatives and positives of a sign split, appended, are the node vector reindexed. -/
theorem append_split_eq {k q n : ℕ} (σ : Fin k ⊕ Fin q ≃ Fin n) (x : Fin n → ℝ) :
    Fin.append (fun b => x (σ (Sum.inl b))) (fun p => x (σ (Sum.inr p))) =
      fun i => x (splitEquiv σ i) := by
  funext i
  rw [fin_append_eq_elim]
  show _ = x (σ (finSumFinEquiv.symm i))
  generalize finSumFinEquiv.symm i = u
  cases u <;> rfl

/-- A sum over ordered pairs `i < j` of a symmetric function is invariant under a relabelling
between index types (`Fin a ≃ Fin b`). -/
theorem sum_Ioi_equiv {a b : ℕ} (g : ℝ → ℝ → ℝ) (hg : ∀ u v, g u v = g v u) (w : Fin b → ℝ)
    (e : Fin a ≃ Fin b) :
    ∑ i, ∑ j ∈ Finset.Ioi i, g (w (e i)) (w (e j)) = ∑ i, ∑ j ∈ Finset.Ioi i, g (w i) (w j) := by
  have h1 := sum_offdiag_eq_two_mul (p := a) (fun i j => g (w (e i)) (w (e j)))
    (fun i j => hg _ _)
  have h2 := sum_offdiag_eq_two_mul (p := b) (fun i j => g (w i) (w j)) (fun i j => hg _ _)
  have h3 : (∑ i : Fin a, ∑ j : Fin a, if i = j then (0 : ℝ) else g (w (e i)) (w (e j))) =
      ∑ i : Fin b, ∑ j : Fin b, if i = j then (0 : ℝ) else g (w i) (w j) := by
    rw [← Equiv.sum_comp e (fun i => ∑ j : Fin b, if i = j then (0 : ℝ) else g (w i) (w j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp e (fun j => if e i = j then (0 : ℝ) else g (w (e i)) (w j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [e.injective.eq_iff]
  linarith

/-- **Relabelling bridge.**  The contract's left side at `(Fin.append xn gp, s ∘ cast)` equals the
left side at the original node vector `x`, `s`. -/
theorem bridge_free {k q n : ℕ} (hkq : k + q = n) (σ : Fin k ⊕ Fin q ≃ Fin n)
    (x s : Fin n → ℝ) (ν c : ℝ) (R C : ℝ → ℝ) :
    c + pinOffDiagonalInteraction ν 1
        (Fin.append (fun b => x (σ (Sum.inl b))) (fun p => x (σ (Sum.inr p))))
        (fun j => s (Fin.cast hkq j)) +
      (∑ i, ∑ j ∈ Finset.Ioi i,
        Real.log |Fin.append (fun b => x (σ (Sum.inl b))) (fun p => x (σ (Sum.inr p))) j -
          Fin.append (fun b => x (σ (Sum.inl b))) (fun p => x (σ (Sum.inr p))) i|) / ν ^ 2 +
      (∑ i, R (Fin.append (fun b => x (σ (Sum.inl b))) (fun p => x (σ (Sum.inr p))) i)) / ν +
      (∑ j, C (s (Fin.cast hkq j))) / ν =
    c + pinOffDiagonalInteraction ν 1 x s +
      (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) / ν ^ 2 +
      (∑ i, R (x i)) / ν + (∑ j, C (s j)) / ν := by
  subst hkq
  rw [append_split_eq]
  have e1 := pinOff_perm ν 1 x s (splitEquiv σ) (Equiv.refl _)
  have e2 := sum_Ioi_perm (fun a b => Real.log |b - a|) (fun a b => by rw [abs_sub_comm]) x
    (splitEquiv σ)
  have e3 := Equiv.sum_comp (splitEquiv σ) (fun i => R (x i))
  simp only [Fin.cast_eq_self, Equiv.refl_apply] at e1 ⊢
  rw [e1, e2, e3]

end Relabel

section Discharge

open CatalanMeasure.GenD.Signed

/-- **Discharge of `SignedClassBound` from a `SignedTrialBounds` instance (lane RP2, item 1).**
The instance `T` (supplied by Phase 2, with `LR = logRatioZ (q - g)`) is matched to the
parameters by the identification hypotheses `hn`, `hconst`, `hRf`, `hCf`, `hLR`, `hB`; the
class `Cls` supplies Lemma T for the free configuration (`hLT`) and, for every sign split,
`0 < k`, `2g < q`, the negative-fraction range of `T` and membership in `T.Cls`
(`hshape`).  The conclusion is the class hypothesis of `signedSecondSheet`. -/
theorem signedClassBound_of_trial {P : Parameters} (T : SignedTrialBounds)
    (Cls : ∀ (N r : ℕ), (Fin r → ℝ) → Prop) (target0 : ℝ)
    (hn : ∀ N, T.ncount N = P.n N)
    (hconst : ∀ N, (T.D N).constant = groupedConstant P N (P.n N) 0 0)
    (hRf : ∀ N, (T.D N).Rf = populationPhysicalFreeField P N)
    (hCf : ∀ N, (T.D N).Cf = populationPhysicalColumnField P N (0 + 0))
    (hLR : ∀ N k q xn gp, T.LR N k q xn gp = logRatioZ (q - P.g N) xn gp)
    (hB : T.B = -target0 + Real.log 2 / 2)
    (hLT : ∀ᶠ N : ℕ in atTop, ∀ x : Fin (P.n N) → ℝ, (∀ i, x i ∈ Ioo (-1 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Cls N (P.n N) x →
      ∀ c : Fin (P.n N) → ℝ, |∑ a ∈ Finset.univ.filter (fun a => 0 < x a),
          bDeriv x a * x a ^ (P.n N - 1 - 2 * P.g N) * c a ^ 2| ≤
          (3 / 2) * ∑ a, ∑ b, c a * c b / (1 - x a * x b))
    (hshape : ∀ᶠ N : ℕ in atTop, ∀ x : Fin (P.n N) → ℝ, (∀ i, x i ∈ Ioo (-1 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Cls N (P.n N) x →
      ∀ (k q : ℕ) (σ : Fin k ⊕ Fin q ≃ Fin (P.n N)),
        (∀ b, x (σ (Sum.inl b)) < 0) → (∀ p, 0 < x (σ (Sum.inr p))) →
        0 < k ∧ 2 * P.g N < q ∧ T.κlo ≤ (k : ℝ) / (T.ncount N : ℝ) ∧
          (k : ℝ) / (T.ncount N : ℝ) ≤ T.κhi ∧
          T.Cls N k q (fun b => x (σ (Sum.inl b))) (fun p => x (σ (Sum.inr p)))) :
    SignedClassBound P Cls target0 := by
  intro ε hε
  filter_upwards [signed_second_energy T hε, hLT, hshape] with N hE hlt hsh x s hx hx0 hinj hs
    hsi hc
  refine ⟨hlt x hx hx0 hinj hc, ?_⟩
  intro k q σ hneg hpos
  obtain ⟨hk, hq, hlo, hhi, hCl⟩ := hsh x hx hx0 hinj hc k q σ hneg hpos
  refine ⟨hk, hq, ?_⟩
  have hcard := Fintype.card_congr σ
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  have hkqN : k + q = T.ncount N := hcard.trans (hn N).symm
  have hν : (T.D N).ν = (P.n N : ℝ) := by rw [T.ν_eq, hn]
  have happ := append_split_eq σ x
  have hinjA : Function.Injective
      (Fin.append (fun b => x (σ (Sum.inl b))) (fun p => x (σ (Sum.inr p)))) := by
    rw [happ]; exact hinj.comp (splitEquiv σ).injective
  have key := hE k q hkqN hlo hhi (fun b => x (σ (Sum.inl b))) (fun p => x (σ (Sum.inr p)))
    (fun j => s (Fin.cast hcard j))
    (fun b => ⟨(hx _).1, hneg b⟩) (fun p => ⟨hpos p, (hx _).2⟩) hinjA
    (fun j => hs _) (fun a b h => Fin.cast_injective hcard (hsi h)) hCl
  have hid := bridge_free hcard σ x s (P.n N : ℝ) (groupedConstant P N (P.n N) 0 0)
    (populationPhysicalFreeField P N) (populationPhysicalColumnField P N (0 + 0))
  rw [hconst, hRf, hCf, hLR, hν, hB] at key
  have hsv : signedValue P N x s = (groupedConstant P N (P.n N) 0 0) +
      pinOffDiagonalInteraction (P.n N : ℝ) 1 x s +
      (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) / (P.n N : ℝ) ^ 2 +
      (∑ i, populationPhysicalFreeField P N (x i)) / (P.n N : ℝ) +
      (∑ j, populationPhysicalColumnField P N (0 + 0) (s j)) / (P.n N : ℝ) := by
    unfold signedValue
    exact groupedValue_free_eq _ _ _ _ _ _ x s e0 e0
  rw [hsv, ← hid]
  linarith

end Discharge

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.bridge_free
#print axioms CatalanMeasure.Signed.signedClassBound_of_trial
