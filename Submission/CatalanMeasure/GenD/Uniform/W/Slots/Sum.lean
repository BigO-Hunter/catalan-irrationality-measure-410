module
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.FlatCount
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.PCount
@[expose] public section
set_option Elab.async false

/-!
# Sum of a J-flat family and a period family on one slot system

`sum_nullity` : atoms of the J-flat family `lowEmbed (ker jets)` (the first `Dh` slots) and of the
period family `tensorMap` are independent inside the common slot system (the jets of the J-flat
atoms vanish below the window `s`, while the period atoms carry `-P` in window `s+1`), so their
dimensions add:

    Dh · dim V1 + m · dim V2 ≤ ν + e0 · dim V1 + (p - q - v)_+ .
-/

namespace CatalanMeasure.GenD.Uniform.W.Slots
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

namespace SlotSystem
variable (S : SlotSystem P N p)

theorem wv_add (x x' : Fin S.D → Fin S.K → ZMod p) (e : ℕ) :
    wv S.lam (x + x') e = wv S.lam x e + wv S.lam x' e := by
  unfold wv
  simp [smul_add, Finset.sum_add_distrib]

theorem resp_add (J ell : ℕ) (x x' : Fin S.D → Fin S.K → ZMod p) :
    S.resp J ell (x + x') = S.resp J ell x + S.resp J ell x' := by
  unfold resp
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [wv_add]
  split_ifs <;> simp

/-- Data supported on the first `Dh` slots. -/
def lowEmbed (Dh : ℕ) (V : Submodule (ZMod p) (Fin S.K → ZMod p)) :
    (Fin Dh → V) →ₗ[ZMod p] (Fin S.D → Fin S.K → ZMod p) :=
  LinearMap.pi fun t : Fin S.D =>
    if h : t.val < Dh then V.subtype.comp (LinearMap.proj (⟨t.val, h⟩ : Fin Dh)) else 0

theorem lowEmbed_apply (Dh : ℕ) (V : Submodule (ZMod p) (Fin S.K → ZMod p)) (y : Fin Dh → V)
    (t : Fin S.D) :
    S.lowEmbed Dh V y t = if h : t.val < Dh then (y ⟨t.val, h⟩ : Fin S.K → ZMod p) else 0 := by
  unfold lowEmbed
  by_cases h : t.val < Dh <;> simp [h]

theorem lowEmbed_mem (Dh : ℕ) (V : Submodule (ZMod p) (Fin S.K → ZMod p)) (y : Fin Dh → V)
    (t : Fin S.D) : S.lowEmbed Dh V y t ∈ V := by
  rw [lowEmbed_apply]
  split_ifs
  · exact (y _).2
  · exact V.zero_mem

theorem lowEmbed_zero (Dh : ℕ) (V : Submodule (ZMod p) (Fin S.K → ZMod p)) (y : Fin Dh → V)
    (t : Fin S.D) (ht : Dh ≤ t.val) : S.lowEmbed Dh V y t = 0 := by
  rw [lowEmbed_apply, dif_neg (by omega)]

theorem lowEmbed_injective {Dh : ℕ} (hDh : Dh ≤ S.D) (V : Submodule (ZMod p) (Fin S.K → ZMod p)) :
    Function.Injective (S.lowEmbed Dh V) := by
  refine injective_of_zero _ fun y hy => ?_
  funext i
  apply Subtype.ext
  have := congrFun hy ⟨i.val, lt_of_lt_of_le i.isLt hDh⟩
  rw [lowEmbed_apply, dif_pos i.isLt] at this
  simpa using this

theorem wv_lowEmbed_mem (Dh : ℕ) (V : Submodule (ZMod p) (Fin S.K → ZMod p)) (y : Fin Dh → V)
    (e : ℕ) : wv S.lam (S.lowEmbed Dh V y) e ∈ V := by
  unfold wv
  exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (S.lowEmbed_mem Dh V y d)

/-- Low jets of the first-`Dh`-slot atoms. -/
def lowJets (Dh : ℕ) (V : Submodule (ZMod p) (Fin S.K → ZMod p)) (e0 : ℕ) :
    (Fin Dh → V) →ₗ[ZMod p] (Fin e0 → V) :=
  LinearMap.pi fun e : Fin e0 =>
    LinearMap.codRestrict V ((wvL S.lam e).comp (S.lowEmbed Dh V)) (fun y => by
      rw [LinearMap.comp_apply, wvL_apply]
      exact S.wv_lowEmbed_mem Dh V y e)

theorem lowJets_apply (Dh : ℕ) (V : Submodule (ZMod p) (Fin S.K → ZMod p)) (e0 : ℕ)
    (y : Fin Dh → V) (e : Fin e0) :
    ((S.lowJets Dh V e0 y) e : Fin S.K → ZMod p) = wv S.lam (S.lowEmbed Dh V y) e := by
  simp [lowJets, wvL_apply]

theorem finrank_range_lowJets_le (Dh : ℕ) (V : Submodule (ZMod p) (Fin S.K → ZMod p)) (e0 : ℕ) :
    finrank (ZMod p) (LinearMap.range (S.lowJets Dh V e0)) ≤ e0 * finrank (ZMod p) V := by
  have := Submodule.finrank_le (LinearMap.range (S.lowJets Dh V e0))
  simpa [Module.finrank_pi_fintype] using this


/-- The J-flat count with `Φ = 0` and an arbitrary atom space. -/
theorem slot_nullity_jflat0 (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {A : Type*} [AddCommGroup A] [Module (ZMod p) A] [FiniteDimensional (ZMod p) A]
    (ξ : A →ₗ[ZMod p] (Fin S.D → Fin S.K → ZMod p)) (hξ : ∀ a, ξ a ∈ S.dom)
    (hξi : Function.Injective ξ) (v : ℕ) (s : A →ₗ[ZMod p] (ZMod p → ZMod p))
    (hpoly : ∀ a, ∃ G : (ZMod p)[X], G.degree < ((p - v : ℕ) : WithBot ℕ) ∧
      ∀ x, s a x = G.eval x)
    (hresp : ∀ a j, P.b N ≤ j → j < P.L N →
      S.resp (j / p) (j % p) (ξ a) = s a (j : ZMod p)) :
    finrank (ZMod p) A - (p - P.q N - v) ≤ nullity P N p := by
  have h := S.slot_nullity_jflat hP hN hp2 hH ξ hξ hξi (0 : A →ₗ[ZMod p] (Fin 0 → ZMod p)) v
    (s.comp (LinearMap.ker (0 : A →ₗ[ZMod p] (Fin 0 → ZMod p))).subtype)
    (fun u => hpoly u.1) (fun u j h1 h2 => hresp u.1 j h1 h2)
  have hr : finrank (ZMod p) (LinearMap.range (0 : A →ₗ[ZMod p] (Fin 0 → ZMod p))) = 0 := by
    rw [LinearMap.range_zero]; exact finrank_bot _ _
  omega

/-- The J-flat part of a datum on the first `Dh` slots: the residue sequence is a polynomial
function of degree `< p - v`. -/
theorem flat_poly_data (γ : (Fin S.K → ZMod p) →ₗ[ZMod p] ZMod p)
    {eta e0 v dm Dh : ℕ} (hv : v < p) (hdm : dm ≤ eta)
    (hdvd : ∀ d, ((X - 1) ^ v : (ZMod p)[X]) ∣ S.lam d)
    (hdeg : ∀ d : Fin S.D, d.val < Dh → (S.lam d).natDegree ≤ dm) (he0 : eta + 1 ≤ e0 + p)
    (x : Fin S.D → Fin S.K → ZMod p) (hxlow : ∀ d : Fin S.D, Dh ≤ d.val → x d = 0)
    (hjet : ∀ e < e0, wv S.lam x e = 0) :
    ∃ G : (ZMod p)[X], G.degree < ((p - v : ℕ) : WithBot ℕ) ∧
      ∀ ℓ : ZMod p, (if ℓ.val ≤ eta then γ (wv S.lam x (eta - ℓ.val)) else 0) = G.eval ℓ := by
  have hk : ∀ k : Fin S.K, ∃ G : (ZMod p)[X], G.degree < ((p - v : ℕ) : WithBot ℕ) ∧
      ∀ ℓ : ZMod p, (if ℓ.val ≤ eta then wv S.lam x (eta - ℓ.val) k else 0) = G.eval ℓ := by
    intro k
    have := jflat_poly (p := p) hv (∑ d, C (x d k) * S.lam d)
      (Finset.dvd_sum fun d _ => dvd_mul_of_dvd_right (hdvd d) _) eta
      (natDegree_sum_le_of_forall_le _ _ fun d _ => by
        by_cases hd : d.val < Dh
        · exact (natDegree_C_mul_le _ _).trans ((hdeg d hd).trans hdm)
        · rw [hxlow d (by omega)]; simp)
      (fun i hi => by
        rw [← S.wv_coord x i k, hjet i (by omega)]; rfl)
    obtain ⟨G, hG, hGe⟩ := this
    refine ⟨G, hG, fun ℓ => ?_⟩
    rw [← hGe ℓ]
    simp only [S.wv_coord]
  choose Gk hGk using hk
  refine ⟨∑ k, C (γ (fun j => if k = j then 1 else 0)) * Gk k, ?_, fun ℓ => ?_⟩
  · rw [Polynomial.degree_lt_iff_coeff_zero]
    intro i hi
    rw [finset_sum_coeff]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [coeff_C_mul, coeff_eq_zero_of_degree_lt ((hGk k).1.trans_le (by exact_mod_cast hi)),
      mul_zero]
  · rw [eval_finset_sum]
    simp only [eval_mul, eval_C]
    simp_rw [← (hGk _).2 ℓ]
    by_cases hl : ℓ.val ≤ eta
    · simp only [hl, if_true]
      rw [LinearMap.pi_apply_eq_sum_univ γ (wv S.lam x (eta - ℓ.val))]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [smul_eq_mul, mul_comm]
    · simp [hl]

/-- The combined atom map `(u, y) ↦ (lowEmbed u, tensorMap y)` from `ker jets × Π V2` into
pairs of data (plain `Pi`/`Prod` over `F_p`, to keep instance checks cheap). -/
def sumPsi (Dh : ℕ) (V1 : Submodule (ZMod p) (Fin S.K → ZMod p)) (e0 : ℕ) {m : ℕ}
    (V2 : Submodule (ZMod p) (Fin S.K → ZMod p)) (sc : Fin m → Fin S.D → ZMod p) :
    (↥(LinearMap.ker (S.lowJets Dh V1 e0)) × (Fin m → V2)) →ₗ[ZMod p]
      ((Fin S.D → Fin S.K → ZMod p) × (Fin S.D → Fin S.K → ZMod p)) :=
  LinearMap.prod
    ((S.lowEmbed Dh V1).comp ((LinearMap.ker (S.lowJets Dh V1 e0)).subtype.comp
      (LinearMap.fst (ZMod p) (↥(LinearMap.ker (S.lowJets Dh V1 e0))) (Fin m → V2))))
    ((S.tensorMap V2 sc).comp
      (LinearMap.snd (ZMod p) (↥(LinearMap.ker (S.lowJets Dh V1 e0))) (Fin m → V2)))

theorem sumPsi_apply (Dh : ℕ) (V1 : Submodule (ZMod p) (Fin S.K → ZMod p)) (e0 : ℕ) {m : ℕ}
    (V2 : Submodule (ZMod p) (Fin S.K → ZMod p)) (sc : Fin m → Fin S.D → ZMod p)
    (w : ↥(LinearMap.ker (S.lowJets Dh V1 e0)) × (Fin m → V2)) :
    S.sumPsi Dh V1 e0 V2 sc w = (S.lowEmbed Dh V1 w.1.1, S.tensorMap V2 sc w.2) := rfl

/-- The atom map `(x1, x2) ↦ x1 + x2` on the range of `sumPsi`. -/
def sumXi (Dh : ℕ) (V1 : Submodule (ZMod p) (Fin S.K → ZMod p)) (e0 : ℕ) {m : ℕ}
    (V2 : Submodule (ZMod p) (Fin S.K → ZMod p)) (sc : Fin m → Fin S.D → ZMod p) :
    ↥(LinearMap.range (S.sumPsi Dh V1 e0 V2 sc)) →ₗ[ZMod p] (Fin S.D → Fin S.K → ZMod p) :=
  (LinearMap.fst (ZMod p) (Fin S.D → Fin S.K → ZMod p) (Fin S.D → Fin S.K → ZMod p) +
    LinearMap.snd (ZMod p) (Fin S.D → Fin S.K → ZMod p) (Fin S.D → Fin S.K → ZMod p)).comp
    (LinearMap.range (S.sumPsi Dh V1 e0 V2 sc)).subtype

theorem sumXi_apply (Dh : ℕ) (V1 : Submodule (ZMod p) (Fin S.K → ZMod p)) (e0 : ℕ) {m : ℕ}
    (V2 : Submodule (ZMod p) (Fin S.K → ZMod p)) (sc : Fin m → Fin S.D → ZMod p)
    (a : ↥(LinearMap.range (S.sumPsi Dh V1 e0 V2 sc))) :
    S.sumXi Dh V1 e0 V2 sc a = a.1.1 + a.1.2 := rfl

/-- The residue sequence `ℓ ↦ γ(w_{η-ℓ})` of the J-flat component. -/
def sumS (Dh : ℕ) (V1 : Submodule (ZMod p) (Fin S.K → ZMod p)) (e0 : ℕ) {m : ℕ}
    (V2 : Submodule (ZMod p) (Fin S.K → ZMod p)) (sc : Fin m → Fin S.D → ZMod p) (eta : ℕ)
    (γ : (Fin S.K → ZMod p) →ₗ[ZMod p] ZMod p) :
    ↥(LinearMap.range (S.sumPsi Dh V1 e0 V2 sc)) →ₗ[ZMod p] (ZMod p → ZMod p) :=
  LinearMap.pi fun ℓ : ZMod p =>
    if ℓ.val ≤ eta then
      ((γ.comp (wvL S.lam (eta - ℓ.val))).comp
        (LinearMap.fst (ZMod p) (Fin S.D → Fin S.K → ZMod p)
          (Fin S.D → Fin S.K → ZMod p))).comp
        (LinearMap.range (S.sumPsi Dh V1 e0 V2 sc)).subtype
    else 0

theorem sumS_apply (Dh : ℕ) (V1 : Submodule (ZMod p) (Fin S.K → ZMod p)) (e0 : ℕ) {m : ℕ}
    (V2 : Submodule (ZMod p) (Fin S.K → ZMod p)) (sc : Fin m → Fin S.D → ZMod p) (eta : ℕ)
    (γ : (Fin S.K → ZMod p) →ₗ[ZMod p] ZMod p)
    (a : ↥(LinearMap.range (S.sumPsi Dh V1 e0 V2 sc))) (ℓ : ZMod p) :
    S.sumS Dh V1 e0 V2 sc eta γ a ℓ =
      if ℓ.val ≤ eta then γ (wv S.lam a.1.1 (eta - ℓ.val)) else 0 := by
  by_cases h : ℓ.val ≤ eta
  · simp [sumS, h, wvL_apply]
  · simp [sumS, h]

theorem finrank_prod_gen {M M' : Type*} [AddCommGroup M] [Module (ZMod p) M]
    [Module.Finite (ZMod p) M] [AddCommGroup M'] [Module (ZMod p) M'] [Module.Finite (ZMod p) M'] :
    finrank (ZMod p) (M × M') = finrank (ZMod p) M + finrank (ZMod p) M' :=
  Module.finrank_prod

set_option maxHeartbeats 1600000 in
/-- **Sum of a J-flat family and a period family.** -/
theorem sum_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (hdom : ∀ x, x ∈ S.dom)
    {eta s e0 v dm Dh : ℕ}
    (V1 : Submodule (ZMod p) (Fin S.K → ZMod p)) (γ : (Fin S.K → ZMod p) →ₗ[ZMod p] ZMod p)
    (hDh : Dh ≤ S.D) (hv : v < p) (hdm : dm ≤ eta)
    (hdvd : ∀ d, ((X - 1) ^ v : (ZMod p)[X]) ∣ S.lam d)
    (hdeg : ∀ d : Fin S.D, d.val < Dh → (S.lam d).natDegree ≤ dm) (he0 : eta + 1 ≤ e0 + p)
    (heta : (P.H N : ℤ) - 1 - eta = s * p)
    (hpsi : ∀ j, P.b N ≤ j → j < P.L N → e0 + j % p ≤ eta → eta ≤ j % p + dm →
      ∀ y ∈ V1, S.prof.psi (P.H N) (j / p) s y = γ y)
    {m ilo Pmax : ℕ} (V2 : Submodule (ZMod p) (Fin S.K → ZMod p))
    (hPmax : Pmax + p ≤ eta) (hilo : eta + 1 ≤ ilo + 2 * p) (hPe0 : Pmax < e0)
    (hmle : ilo + m ≤ Pmax + 1) (hmp : m ≤ p)
    (sc : Fin m → Fin S.D → ZMod p)
    (hrel : ∀ i : Fin m, ∑ t, C (sc i t) * S.lam t =
      X ^ p * (X ^ (ilo + (i : ℕ)) : (ZMod p)[X]) - X ^ (ilo + (i : ℕ)))
    (hind : ∀ cc : Fin m → ZMod p,
      ∑ i, C (cc i) * (X ^ p * (X ^ (ilo + (i : ℕ)) : (ZMod p)[X]) - X ^ (ilo + (i : ℕ))) = 0 →
        cc = 0)
    (hVpsi : ∀ j, P.b N ≤ j → j < P.L N → p + j % p ≤ eta → ilo ≤ eta - p - j % p →
      eta - p - j % p ≤ Pmax → ∀ y ∈ V2,
        S.prof.psi (P.H N) (j / p) s y = S.prof.psi (P.H N) (j / p) ((s : ℤ) + 1) y) :
    Dh * finrank (ZMod p) V1 + m * finrank (ZMod p) V2 ≤
      nullity P N p + e0 * finrank (ZMod p) V1 + (p - P.q N - v) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨Pp, hPpdef⟩ : ∃ Pp : Fin m → (ZMod p)[X],
      Pp = fun i : Fin m => (X ^ (ilo + (i : ℕ)) : (ZMod p)[X]) := ⟨_, rfl⟩
  have hPdeg : ∀ i, (Pp i).natDegree ≤ Pmax := fun i => by
    rw [hPpdef]; show (X ^ (ilo + (i : ℕ)) : (ZMod p)[X]).natDegree ≤ Pmax
    rw [natDegree_X_pow]; have := i.isLt; omega
  have hPlo : ∀ i e, e < ilo → (Pp i).coeff e = 0 := fun i e he => by
    rw [hPpdef]; show (X ^ (ilo + (i : ℕ)) : (ZMod p)[X]).coeff e = 0
    rw [coeff_X_pow, if_neg (by omega)]
  have hrel' : ∀ i, ∑ t, C (sc i t) * S.lam t = X ^ p * Pp i - Pp i := by
    intro i; rw [hPpdef]; exact hrel i
  have hind' : ∀ cc : Fin m → ZMod p, ∑ i, C (cc i) * (X ^ p * Pp i - Pp i) = 0 → cc = 0 := by
    intro cc; rw [hPpdef]; exact hind cc
  -- jets of the J-flat component vanish
  have hjetU : ∀ u : Fin Dh → V1, S.lowJets Dh V1 e0 u = 0 → ∀ e < e0,
      wv S.lam (S.lowEmbed Dh V1 u) e = 0 := by
    intro u hu e he
    have := congrFun hu ⟨e, he⟩
    have h3 := S.lowJets_apply Dh V1 e0 u ⟨e, he⟩
    rw [this] at h3
    simpa using h3.symm
  have hzero : ∀ (u : Fin Dh → V1) (y : Fin m → V2), S.lowJets Dh V1 e0 u = 0 →
      S.lowEmbed Dh V1 u + S.tensorMap V2 sc y = 0 → u = 0 ∧ y = 0 := by
    intro u y hu ha
    have hy : y = 0 := by
      funext i
      apply Subtype.ext
      funext k
      have hw : ∀ e, e < e0 → wv S.lam (S.tensorMap V2 sc y) e = 0 := by
        intro e he
        have h1 : wv S.lam (S.lowEmbed Dh V1 u + S.tensorMap V2 sc y) e = 0 := by
          rw [ha]; unfold wv; simp
        rw [wv_add, hjetU u hu e he, zero_add] at h1
        exact h1
      have hi : ilo + (i : ℕ) < e0 := by have := i.isLt; omega
      have := congrFun (hw (ilo + (i : ℕ)) hi) k
      rw [S.wv_tensor V2 sc Pp hrel'] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      have hcoef : ∀ i' : Fin m, (X ^ p * Pp i' - Pp i').coeff (ilo + (i : ℕ)) =
          if i' = i then -1 else 0 := by
        intro i'
        rw [hPpdef]
        show (X ^ p * (X ^ (ilo + (i' : ℕ)) : (ZMod p)[X]) - X ^ (ilo + (i' : ℕ))).coeff _ = _
        rw [← pow_add, coeff_sub, coeff_X_pow, coeff_X_pow]
        have hi1 := i.isLt
        have hi2 := i'.isLt
        by_cases hii : i' = i
        · subst hii
          rw [if_neg (by omega), if_pos rfl, if_pos rfl]; simp
        · rw [if_neg (by omega), if_neg (by intro h; apply hii; exact Fin.ext (by omega))]
          simp [hii]
      simp only [hcoef] at this
      simpa using this
    refine ⟨?_, hy⟩
    have h2 : S.lowEmbed Dh V1 u = 0 := by
      rw [hy, map_zero, add_zero] at ha
      exact ha
    exact S.lowEmbed_injective hDh V1 (by rw [h2, map_zero])
  -- atoms in the range of `sumPsi`
  have hatom : ∀ a : ↥(LinearMap.range (S.sumPsi Dh V1 e0 V2 sc)), ∃ (u : Fin Dh → V1)
      (y : Fin m → V2), S.lowJets Dh V1 e0 u = 0 ∧ a.1.1 = S.lowEmbed Dh V1 u ∧
        a.1.2 = S.tensorMap V2 sc y := by
    intro a
    obtain ⟨⟨u, y⟩, hw⟩ := LinearMap.mem_range.mp a.2
    refine ⟨u.1, y, LinearMap.mem_ker.mp u.2, ?_, ?_⟩
    · rw [← hw]; rfl
    · rw [← hw]; rfl
  have hξinj : Function.Injective (S.sumXi Dh V1 e0 V2 sc) := by
    refine injective_of_zero _ fun a ha => ?_
    obtain ⟨u, y, hu, h1, h2⟩ := hatom a
    rw [sumXi_apply, h1, h2] at ha
    obtain ⟨hu0, hy0⟩ := hzero u y hu ha
    apply Subtype.ext
    apply Prod.ext
    · show a.1.1 = 0
      rw [h1, hu0, map_zero]
    · show a.1.2 = 0
      rw [h2, hy0, map_zero]
  have hflat : ∀ a : ↥(LinearMap.range (S.sumPsi Dh V1 e0 V2 sc)),
      ∃ G : (ZMod p)[X], G.degree < ((p - v : ℕ) : WithBot ℕ) ∧
      ∀ ℓ : ZMod p, (if ℓ.val ≤ eta then γ (wv S.lam a.1.1 (eta - ℓ.val)) else 0) = G.eval ℓ := by
    intro a
    obtain ⟨u, y, hu, h1, h2⟩ := hatom a
    rw [h1]
    exact S.flat_poly_data γ hv hdm hdvd hdeg he0 _ (fun d hd => S.lowEmbed_zero Dh V1 _ d hd)
      (hjetU u hu)
  have hpolyS : ∀ a : ↥(LinearMap.range (S.sumPsi Dh V1 e0 V2 sc)),
      ∃ G : (ZMod p)[X], G.degree < ((p - v : ℕ) : WithBot ℕ) ∧
        ∀ x, (S.sumS Dh V1 e0 V2 sc eta γ) a x = G.eval x := fun u => by
    obtain ⟨G, hG, hGe⟩ := hflat u
    exact ⟨G, hG, fun ℓ => (S.sumS_apply Dh V1 e0 V2 sc eta γ u ℓ).trans (hGe ℓ)⟩
  have hrespS : ∀ (a : ↥(LinearMap.range (S.sumPsi Dh V1 e0 V2 sc))) (j : ℕ),
      P.b N ≤ j → j < P.L N →
        S.resp (j / p) (j % p) (S.sumXi Dh V1 e0 V2 sc a) =
          (S.sumS Dh V1 e0 V2 sc eta γ) a (j : ZMod p) := fun a j h1 h2 => by
    obtain ⟨u, y, hu, hx1, hx2⟩ := hatom a
    have hell : j % p < p := Nat.mod_lt _ hp0
    rw [sumXi_apply, hx1, hx2, resp_add]
    rw [S.period_resp_zero V2 heta hPmax hilo Pp hPdeg hPlo sc hrel' hVpsi y j h1 h2,
      add_zero, sumS_apply, hx1]
    have hhi : ∀ e, eta < e → wv S.lam (S.lowEmbed Dh V1 u) e = 0 := by
      intro e he
      unfold wv
      refine Finset.sum_eq_zero fun d _ => ?_
      by_cases hd : d.val < Dh
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ((hdeg d hd).trans hdm) he), zero_smul]
      · rw [S.lowEmbed_zero Dh V1 _ d (by omega), smul_zero]
    rw [S.resp_flat he0 heta (j / p) (j % p) hell _ hhi (hjetU u hu)]
    by_cases hl : j % p ≤ eta
    · simp only [hl, if_true, ZMod.val_natCast]
      by_cases hc : e0 + j % p ≤ eta ∧ eta ≤ j % p + dm
      · exact hpsi j h1 h2 hc.1 hc.2 _ (S.wv_lowEmbed_mem Dh V1 _ _)
      · by_cases hc1 : e0 + j % p ≤ eta
        · have hz : wv S.lam (S.lowEmbed Dh V1 u) (eta - j % p) = 0 := by
            unfold wv
            refine Finset.sum_eq_zero fun d _ => ?_
            by_cases hd : d.val < Dh
            · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg d hd) (by omega)),
                zero_smul]
            · rw [S.lowEmbed_zero Dh V1 _ d (by omega), smul_zero]
          rw [hz, map_zero, map_zero]
        · rw [hjetU u hu (eta - j % p) (by omega), map_zero, map_zero]
    · simp [hl, ZMod.val_natCast]
  have h := S.slot_nullity_jflat0 hP hN hp2 hH (S.sumXi Dh V1 e0 V2 sc) (fun a => hdom _) hξinj v
    (S.sumS Dh V1 e0 V2 sc eta γ) hpolyS hrespS
  -- dimension of the atom space
  have hψinj : Function.Injective (S.sumPsi Dh V1 e0 V2 sc) := by
    intro w w' hww
    rw [sumPsi_apply, sumPsi_apply] at hww
    have h1 : S.lowEmbed Dh V1 w.1.1 = S.lowEmbed Dh V1 w'.1.1 := congrArg Prod.fst hww
    have h2 : S.tensorMap V2 sc w.2 = S.tensorMap V2 sc w'.2 := congrArg Prod.snd hww
    exact Prod.ext (Subtype.ext (S.lowEmbed_injective hDh V1 h1))
      (S.period_injective V2 Pp sc hrel' hind' h2)
  have hA := LinearMap.finrank_range_of_inj hψinj
  have hA2 : finrank (ZMod p) (↥(LinearMap.ker (S.lowJets Dh V1 e0)) × (Fin m → V2)) =
      finrank (ZMod p) (LinearMap.ker (S.lowJets Dh V1 e0)) + m * finrank (ZMod p) V2 := by
    have hpg := finrank_prod_gen (p := p) (M := ↥(LinearMap.ker (S.lowJets Dh V1 e0)))
      (M' := Fin m → V2)
    refine hpg.trans ?_
    rw [Module.finrank_pi_fintype]
    simp
  have hrn := (S.lowJets Dh V1 e0).finrank_range_add_finrank_ker
  have hdim : finrank (ZMod p) (Fin Dh → V1) = Dh * finrank (ZMod p) V1 := by
    simp [Module.finrank_pi_fintype]
  have hjr := S.finrank_range_lowJets_le Dh V1 e0
  omega

#print axioms sum_nullity
end SlotSystem

end
end CatalanMeasure.GenD.Uniform.W.Slots
