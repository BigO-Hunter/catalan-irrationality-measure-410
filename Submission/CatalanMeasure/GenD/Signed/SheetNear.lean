module

public import Submission.CatalanMeasure.GenD.Signed.EnergyNear
public import Submission.CatalanMeasure.GenD.Signed.MarkedExpansion
public import Submission.CatalanMeasure.GenD.Signed.RealPlaceFixed
public import Submission.CatalanMeasure.GenD.Signed.SheetNearH2
public import Submission.CatalanMeasure.GenD.Signed.SignedDischarge

/-! This module is a continuation shard of `SheetNear` (`catalan-410` peak-RSS split); statements are unchanged. -/

@[expose] public section

namespace CatalanMeasure.Signed

open Set Finset
open scoped BigOperators
open CatalanMeasure.Parametric

noncomputable section

set_option maxRecDepth 100000
theorem pow22_le {q n : ℕ} (hq : q ≤ n) (hn : 1 ≤ n) :
    (22 : ℝ) ^ q ≤ (1 + 10 * Real.exp 12 * (n : ℝ)) ^ n := by
  have h12 : (13 : ℝ) ≤ Real.exp 12 := by
    have := Real.add_one_le_exp (12 : ℝ); linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h22 : (22 : ℝ) ≤ 1 + 10 * Real.exp 12 * (n : ℝ) := by nlinarith
  calc (22 : ℝ) ^ q ≤ 22 ^ n := pow_le_pow_right₀ (by norm_num) hq
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) h22 n


/-! ### The signed second-case sheet bound with first-kind fixed and near-type rows -/

section WrapNear

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic OAI.InternalCatalan Filter
  CatalanMeasure.GenD.Signed

/-- **Class-branch link data** (the Lemma K / Lemma T / `FixAdm` side of the consumer, supplied
with the class `Cls` of free configurations).  For the marked sheet with free rows `x`, marked
rows `y` (all in `G`) and a free class configuration `Cls N p x`:
* Lemma T for ALL positive nodes of the sheet (the exact conclusion of `lemmaT_of_slope`; no
  free-only form and no W term: Lemma 17.43.1 expands the marked positives);
* for every sign split of the free rows and of the marked rows: at least one free negative, more
  than `2g` free positives, the negative-fraction range of every α-interval containing
  `α = (m₁ + m₂')/n`, and for every splitting `τ` of the marked positives into first-kind and
  near rows, membership in `T.Clsf` and `T.FixAdm`.  The link is only asked for marked counts
`m ≤ α₁ n` (the hypothesis `hmle` of the consumer): for larger `m` the free-count clauses
(`2g < q`, the κ-range) are not true of the near-optimal class. -/
def SignedNearClassLinkNd (P : Parameters) {I : ℕ} (T : SignedNearBounds I)
    (Cls : ∀ (N r : ℕ), (Fin r → ℝ) → Prop) (G : ℝ → Prop)
    (Nd : ∀ (N m : ℕ), (Fin m → ℝ) → Prop) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (hpm : p + m = P.n N), (m : ℝ) ≤ T.α1 * (T.ncount N : ℝ) →
    ∀ (x : Fin p → ℝ) (y : Fin m → ℝ),
    (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) → (∀ j, y j ∈ Ioo (-1 : ℝ) 1) →
    (∀ j, y j ≠ 0) → (∀ j, G (y j)) → Nd N m y → Function.Injective (Fin.append x y) →
    Cls N p x →
    (∀ c : Fin (P.n N) → ℝ,
      |∑ a ∈ Finset.univ.filter (fun a => 0 < sheetNodes hpm x y a),
        bDeriv (sheetNodes hpm x y) a * sheetNodes hpm x y a ^ (P.n N - 1 - 2 * P.g N) *
          c a ^ 2| ≤
        (3 / 2) * ∑ a, ∑ b, c a * c b /
          (1 - sheetNodes hpm x y a * sheetNodes hpm x y b)) ∧
    ∀ (k q m1 m2' : ℕ) (σx : Fin k ⊕ Fin q ≃ Fin p) (σy : Fin m1 ⊕ Fin m2' ≃ Fin m),
      (∀ b, x (σx (Sum.inl b)) < 0) → (∀ b, 0 < x (σx (Sum.inr b))) →
      (∀ b, y (σy (Sum.inl b)) < 0) → (∀ b, 0 < y (σy (Sum.inr b))) →
      0 < k ∧ 2 * P.g N < q ∧
      (∀ i, T.lo i ≤ ((m1 + m2' : ℕ) : ℝ) / (T.ncount N : ℝ) →
        ((m1 + m2' : ℕ) : ℝ) / (T.ncount N : ℝ) ≤ T.hi i →
        T.κlo i ≤ (k : ℝ) / (T.ncount N : ℝ) ∧ (k : ℝ) / (T.ncount N : ℝ) ≤ T.κhi i) ∧
      ∀ (r s' : ℕ) (τ : Fin r ⊕ Fin s' ≃ Fin m2'),
        T.Clsf N k q m1 (r + s') (fun b => x (σx (Sum.inl b))) (fun b => x (σx (Sum.inr b)))
          (fun b => y (σy (Sum.inl b)))
          (Fin.append (fun j => y (σy (Sum.inr (τ (Sum.inl j)))))
            (fun j => y (σy (Sum.inr (τ (Sum.inr j)))))) ∧
        T.FixAdm N m1 r s' (fun b => y (σy (Sum.inl b)))
          (fun j => y (σy (Sum.inr (τ (Sum.inl j))))) (fun j => y (σy (Sum.inr (τ (Sum.inr j)))))

/-- The class link with no node-set restriction (`Nd` trivial). -/
def SignedNearClassLink (P : Parameters) {I : ℕ} (T : SignedNearBounds I)
    (Cls : ∀ (N r : ℕ), (Fin r → ℝ) → Prop) (G : ℝ → Prop) : Prop :=
  SignedNearClassLinkNd P T Cls G (fun _ _ _ => True)

/-- `SignedSecondSheetCore` for marked rows restricted by a node-set predicate `Nd N m y`
(in the real assembly: `y = realCoordinate ∘ τ N ∘ a` for an injective `a`, see `MarkedCap.lean`). -/
def SignedSecondSheetCoreNd (P : Parameters) (G : ℝ → Prop)
    (Nd : ∀ (N m : ℕ), (Fin m → ℝ) → Prop) (target0 c2 alpha1 : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ (p m : ℕ) (hpm : p + m = P.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (m : ℝ) ≤ alpha1 * (P.n N : ℝ) →
      (∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Set.Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) → Nd N m y →
      (∀ i, s i ∈ Set.Ioo (0 : ℝ) 1) →
      Function.Injective (Fin.append x y) → Function.Injective s →
      (∑ i : Fin (p + m), paramCaseField P N (Fin.append x y i)) ≤ -1 →
      markedSheetCore P N hpm x y s ≤
        5 ^ m * (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
          Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target0 + Real.log 2 / 2 + ε) + c2 * N * m)

end WrapNear


section WrapNear2

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic OAI.InternalCatalan Filter
  CatalanMeasure.GenD.Signed

/-- **The signed second-case sheet bound with first-kind fixed and near-type rows (`α₁ > 0`)**:
`SignedSecondSheetCore` for the α-interval contract `SignedNearBounds`, from
* the non-class branch (`hnon`: the old energy route, restricted to the complement of `Cls`);
* the class branch: Lemma 17.43.1 (`abs_det_laurent_le_marked_expand`: Lemma T for ALL positives,
  the marked positives expanded over the subsets `S` and each term bounded through the near-type
  energy), the energy theorem `signed_second_energy_near_nodes` for the five lists of every
  splitting, and the EXACT row weights (`log_markedSheetWeight`, no row inequality: the fields
  `Rm = groupedMarkedField`, `Rn = groupedNearField` and the grouped constant at the actual
  counts), the cost being in `budgetFix` (`T.cost * n0 ≤ c2`);
* the identification of `T` with the sheet's data and the class link `hlink`.

This is the form with the non-class branch given directly for the factor-free core (`hnonC`):
the class `Cls` may then be defined by the factor-free product (S1, PROOF-RHO §2.5), so that
Lemma K is measured against the factor-free old route.  `signedSecondSheetNearNd` below is the
corollary with `hnon` for the grouped product with the factor. -/
theorem signedSecondSheetNearNd_core {P : Parameters} (hP : Admissible P) (G : ℝ → Prop)
    (target0 c2 : ℝ) (Cls : ∀ (N r : ℕ), (Fin r → ℝ) → Prop) {I : ℕ}
    (T : SignedNearBounds I)
    (hn : ∀ N, T.ncount N = P.n N)
    (hconst : ∀ N r a b, r + a + b = P.n N →
      T.constant N (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) = groupedConstant P N r a b)
    (hRf : ∀ N, T.Rf N = populationPhysicalFreeField P N)
    (hRm : ∀ N, T.Rm N = groupedMarkedField P N)
    (hRn : ∀ N, T.Rn N = groupedNearField P N)
    (hCf : ∀ N, T.Cf N = populationPhysicalColumnField P N (0 + 0))
    (hLRf : ∀ N k q m1 m2' xn gp yn yp', T.LRf N k q m1 m2' xn gp yn yp' =
      logRatioZ (q + m2' - P.g N) (Fin.append xn yn) (Fin.append gp yp'))
    (hB : T.B = -target0 + Real.log 2 / 2)
    (hcost : T.cost * (P.n0 : ℝ) ≤ c2)
    (hnonC : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ (p m : ℕ) (hpm : p + m = P.n N) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Set.Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) →
      (∀ i, s i ∈ Set.Ioo (0 : ℝ) 1) →
      Function.Injective (Fin.append x y) → Function.Injective s →
      (∑ i : Fin (p + m), paramCaseField P N (Fin.append x y i)) ≤ -1 →
      ¬ Cls N p x →
      markedSheetCore P N hpm x y s ≤
        5 ^ m * (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
          Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target0 + Real.log 2 / 2 + ε) + c2 * N * m))
    (Nd : ∀ (N m : ℕ), (Fin m → ℝ) → Prop)
    (hlink : SignedNearClassLinkNd P T Cls G Nd) :
    SignedSecondSheetCoreNd P G Nd target0 c2 T.α1 := by
  intro ε hε
  filter_upwards [hnonC ε hε,
    signed_second_energy_near_nodes T hε, hlink, eventually_gt_atTop (0 : ℕ)]
    with N hnonN hE hl hN0 p m hpm x y s hmle hx hx0 hy hy0 hyG hNd hs hzi hsi hcase
  by_cases hc : Cls N p x
  · -- class branch
    obtain ⟨hT, hrest⟩ := hl p m hpm (by rw [hn]; exact hmle) x y hx hx0 hy hy0 hyG hNd hzi hc
    obtain ⟨k, q, σx, hxneg, hxpos⟩ := exists_sign_split x hx0
    obtain ⟨m1, m2', σy, hyneg, hypos⟩ := exists_sign_split y hy0
    obtain ⟨hk, hq, hκ, hcl⟩ := hrest k q m1 m2' σx σy hxneg hxpos hyneg hypos
    have hkq := Fintype.card_congr σx
    simp only [Fintype.card_sum, Fintype.card_fin] at hkq
    have hm12 := Fintype.card_congr σy
    simp only [Fintype.card_sum, Fintype.card_fin] at hm12
    subst hkq
    have hn1 : 1 ≤ P.n N := n_pos hP hN0
    have hxi : Function.Injective x := by
      intro a b hab
      have := hzi (show Fin.append x y (Fin.castAdd m a) = Fin.append x y (Fin.castAdd m b) by
        simpa using hab)
      simpa using this
    have hyi : Function.Injective y := by
      intro a b hab
      have := hzi (show Fin.append x y (Fin.natAdd _ a) = Fin.append x y (Fin.natAdd _ b) by
        simpa using hab)
      simpa using this
    have hnR : (P.n N : ℝ) = (P.n0 : ℝ) * N := n_cast P N
    have hinjF : Function.Injective
        (Fin.append (fun b => x (σx (Sum.inl b))) (fun b => x (σx (Sum.inr b)))) := by
      rw [append_split_eq]; exact hxi.comp (splitEquiv σx).injective
    have hcore := near_class_core_le hP hN0 hpm σx σy x s y hx hx0 hy hy0 hs hzi hsi hxneg hxpos
      hyneg hypos hk hq hT
      (-target0 + Real.log 2 / 2 + T.cost * ((m : ℝ) / (P.n N : ℝ)) + ε) (by
        intro r s' τ hinj
        obtain ⟨hCls, hAdm⟩ := hcl r s' τ
        have hM : r + s' = m2' := by simpa using (Fintype.card_congr τ)
        have hcnt : (k + m1) + (q + (r + s')) = T.ncount N := by rw [hn]; omega
        have hα : ((m1 + r + s' : ℕ) : ℝ) ≤ T.α1 * (T.ncount N : ℝ) := by
          have : m1 + r + s' = m := by omega
          rw [this, hn]; exact hmle
        have hκ' : ∀ i, T.lo i ≤ ((m1 + r + s' : ℕ) : ℝ) / (T.ncount N : ℝ) →
            ((m1 + r + s' : ℕ) : ℝ) / (T.ncount N : ℝ) ≤ T.hi i →
            T.κlo i ≤ (k : ℝ) / (T.ncount N : ℝ) ∧ (k : ℝ) / (T.ncount N : ℝ) ≤ T.κhi i := by
          have : m1 + r + s' = m1 + m2' := by omega
          rw [this]; exact hκ
        have hEc := hE k q m1 r s' hcnt hα hκ'
          (fun b => x (σx (Sum.inl b))) (fun b => x (σx (Sum.inr b)))
          (fun b => y (σy (Sum.inl b))) (fun j => y (σy (Sum.inr (τ (Sum.inl j)))))
          (fun j => y (σy (Sum.inr (τ (Sum.inr j))))) s
          (fun b => ⟨(hx _).1, hxneg b⟩) (fun b => ⟨hxpos b, (hx _).2⟩)
          (fun b => ⟨(hy _).1, hyneg b⟩) (fun j => ⟨hypos _, (hy _).2⟩)
          (fun j => ⟨hypos _, (hy _).2⟩) hinjF hinj
          (hyi.comp (σy.injective.comp (Sum.inr_injective.comp (τ.injective.comp Sum.inr_injective))))
          (fun j => hs j) hsi hCls hAdm
        have hcN : (m1 + r + s' : ℕ) = m := by omega
        have hconst' := hconst N (k + q) (m1 + r) s' (by omega)
        rw [hn] at hEc
        rw [hLRf, hconst', hRf, hRm, hRn, hCf, hB] at hEc
        have hαm : ((m1 + r + s' : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast hcN
        rw [hαm] at hEc
        unfold nearLHS
        linarith [hEc])
    have hq' : q + m2' ≤ P.n N := by omega
    have h22 := pow22_le hq' hn1
    have h5 : (1 : ℝ) ≤ 5 ^ m := one_le_pow₀ (by norm_num)
    have hmN : (0 : ℝ) ≤ (N : ℝ) * m := by positivity
    have hexp : Real.exp ((P.n N : ℝ) ^ 2 * (-target0 + Real.log 2 / 2 +
        T.cost * ((m : ℝ) / (P.n N : ℝ)) + ε)) ≤
        Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target0 + Real.log 2 / 2 + ε) + c2 * N * m) := by
      apply Real.exp_le_exp.mpr
      have hn0' : (P.n0 : ℝ) ≠ 0 := (n0_pos hP).ne'
      have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN0.ne'
      have e : (P.n N : ℝ) ^ 2 * (-target0 + Real.log 2 / 2 +
          T.cost * ((m : ℝ) / (P.n N : ℝ)) + ε) =
          ((P.n0 : ℝ) * N) ^ 2 * (-target0 + Real.log 2 / 2 + ε) +
            (T.cost * (P.n0 : ℝ)) * N * m := by
        rw [hnR]
        field_simp
        ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_right hcost hmN]
    calc markedSheetCore P N hpm x y s
        ≤ 22 ^ (q + m2') * Real.exp ((P.n N : ℝ) ^ 2 * (-target0 + Real.log 2 / 2 +
            T.cost * ((m : ℝ) / (P.n N : ℝ)) + ε)) := hcore
      _ ≤ (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
            Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target0 + Real.log 2 / 2 + ε) + c2 * N * m) :=
          mul_le_mul h22 hexp (Real.exp_pos _).le (by positivity)
      _ ≤ 5 ^ m * (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
            Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target0 + Real.log 2 / 2 + ε) + c2 * N * m) := by
          rw [mul_assoc (5 ^ m : ℝ)]
          exact le_mul_of_one_le_left (mul_nonneg (by positivity) (Real.exp_pos _).le) h5
  · -- non-class branch
    exact hnonN p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase hc

/-- `signedSecondSheetNearNd_core` with the non-class branch from the old energy route for the
grouped product WITH the factor `(∏ (1 + s_i))^m` (`hnon`), the factor being dropped (`≥ 1`). -/
theorem signedSecondSheetNearNd {P : Parameters} (hP : Admissible P) (G : ℝ → Prop)
    (target0 c2 : ℝ) (Cls : ∀ (N r : ℕ), (Fin r → ℝ) → Prop) {I : ℕ}
    (T : SignedNearBounds I)
    (hn : ∀ N, T.ncount N = P.n N)
    (hconst : ∀ N r a b, r + a + b = P.n N →
      T.constant N (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) = groupedConstant P N r a b)
    (hRf : ∀ N, T.Rf N = populationPhysicalFreeField P N)
    (hRm : ∀ N, T.Rm N = groupedMarkedField P N)
    (hRn : ∀ N, T.Rn N = groupedNearField P N)
    (hCf : ∀ N, T.Cf N = populationPhysicalColumnField P N (0 + 0))
    (hLRf : ∀ N k q m1 m2' xn gp yn yp', T.LRf N k q m1 m2' xn gp yn yp' =
      logRatioZ (q + m2' - P.g N) (Fin.append xn yn) (Fin.append gp yp'))
    (hB : T.B = -target0 + Real.log 2 / 2)
    (hcost : T.cost * (P.n0 : ℝ) ≤ c2)
    (hnon : GroupedMarkedProductCostOnRestr P target0 c2 G
      (fun N r _ _ z _ _ _ => ¬ Cls N r z))
    (Nd : ∀ (N m : ℕ), (Fin m → ℝ) → Prop)
    (hlink : SignedNearClassLinkNd P T Cls G Nd) :
    SignedSecondSheetCoreNd P G Nd target0 c2 T.α1 := by
  refine signedSecondSheetNearNd_core hP G target0 c2 Cls T hn hconst hRf hRm hRn hCf hLRf hB
    hcost ?_ Nd hlink
  intro ε hε
  filter_upwards [second_marked_sheet_product_on_restr hP target0 c2 G _ hnon hε]
    with N hnonN p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase hc
  · have hb := hnonN p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase
      (fun _ _ _ _ => hc)
    rw [markedSheetProduct_eq_factor_mul_core] at hb
    have hf : (1 : ℝ) ≤ (∏ i, (1 + s i)) ^ m := by
      apply one_le_pow₀
      calc (1 : ℝ) = ∏ _i : Fin p, (1 : ℝ) := by simp
        _ ≤ ∏ i, (1 + s i) :=
          by gcongr with i _; linarith [(hs i).1]
    have hcnn : 0 ≤ markedSheetCore P N hpm x y s := by
      unfold markedSheetCore
      dsimp only
      exact div_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _)
        (Finset.prod_nonneg fun j _ => paramRowNodeWeight_nonneg P N (hy j)))
        (paramPinPrincipal_nonneg P N x s hx hs)) (Finset.prod_nonneg fun j _ => abs_nonneg _)
    exact (le_mul_of_one_le_left hcnn hf).trans hb


/-- The unrestricted statement (`Nd` trivial): `SignedSecondSheetCore` from `SignedNearClassLink`. -/
theorem signedSecondSheetNear {P : Parameters} (hP : Admissible P) (G : ℝ → Prop)
    (target0 c2 : ℝ) (Cls : ∀ (N r : ℕ), (Fin r → ℝ) → Prop) {I : ℕ}
    (T : SignedNearBounds I)
    (hn : ∀ N, T.ncount N = P.n N)
    (hconst : ∀ N r a b, r + a + b = P.n N →
      T.constant N (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) = groupedConstant P N r a b)
    (hRf : ∀ N, T.Rf N = populationPhysicalFreeField P N)
    (hRm : ∀ N, T.Rm N = groupedMarkedField P N)
    (hRn : ∀ N, T.Rn N = groupedNearField P N)
    (hCf : ∀ N, T.Cf N = populationPhysicalColumnField P N (0 + 0))
    (hLRf : ∀ N k q m1 m2' xn gp yn yp', T.LRf N k q m1 m2' xn gp yn yp' =
      logRatioZ (q + m2' - P.g N) (Fin.append xn yn) (Fin.append gp yp'))
    (hB : T.B = -target0 + Real.log 2 / 2)
    (hcost : T.cost * (P.n0 : ℝ) ≤ c2)
    (hnon : GroupedMarkedProductCostOnRestr P target0 c2 G
      (fun N r _ _ z _ _ _ => ¬ Cls N r z))
    (hlink : SignedNearClassLink P T Cls G) :
    SignedSecondSheetCore P G target0 c2 T.α1 := by
  intro ε hε
  filter_upwards [signedSecondSheetNearNd hP G target0 c2 Cls T hn hconst hRf hRm hRn hCf hLRf hB
    hcost hnon (fun _ _ _ => True) hlink ε hε] with N h p m hpm x y s hmle hx hx0 hy hy0 hyG hs hzi
    hsi hcase
  exact h p m hpm x y s hmle hx hx0 hy hy0 hyG trivial hs hzi hsi hcase

end WrapNear2

end
end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.logRatioZ_comp_pos
#print axioms CatalanMeasure.Signed.lamS_transport
#print axioms CatalanMeasure.Signed.exists_split_finset
#print axioms CatalanMeasure.Signed.pow22_le
#print axioms CatalanMeasure.Signed.near_split_data
#print axioms CatalanMeasure.Signed.sheetMarks_quad_free
#print axioms CatalanMeasure.Signed.sheetMarks_quad_marked
#print axioms CatalanMeasure.Signed.near_Sterm_le
#print axioms CatalanMeasure.Signed.near_class_core_le
#print axioms CatalanMeasure.Signed.signedSecondSheetNear
#print axioms CatalanMeasure.Signed.groupedConstant_split
#print axioms CatalanMeasure.Signed.log_msw_eq
#print axioms CatalanMeasure.Signed.near_field_eq
