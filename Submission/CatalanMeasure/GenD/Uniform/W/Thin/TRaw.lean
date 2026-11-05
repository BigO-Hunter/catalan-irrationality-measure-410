module
public import Submission.CatalanMeasure.GenD.Uniform.W.Thin.TKill
@[expose] public section
set_option Elab.async false

/-!
# Theorem T-raw as a Theorem W instance (design-generic)

Atoms: `T-` pair profiles `x : Fin D → V` (`V = ker E`, `E` the seen functionals
`psiLin … (J, a)`, `(J, a) ∈ S`), centres `(k0 + k) p`, `k < K`, offsets `1 … D ≤ (p-1)/2`.
Jets: the low coefficients `e < e0` of the slot polynomials (`Φ x = (w_e)_{e<e0}`); virtual
pairs are forced to vanish.  Count (cost `0`, all columns killed):

    (D - e0) (K - |S|) - #virtual ≤ ν.

`hseen` is the whole window arithmetic: every raw column `j ∈ [b, L)` and every coefficient index
`e0 ≤ e < h + D` of a slot reaching the window `(J, a)` must be a seen pair.
-/

namespace CatalanMeasure.GenD.Uniform.W.Thin
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem injective_of_zero {M M' : Type*} [AddCommGroup M] [Module (ZMod p) M]
    [AddCommGroup M'] [Module (ZMod p) M'] (f : M →ₗ[ZMod p] M')
    (h : ∀ x, f x = 0 → x = 0) : Function.Injective f :=
  LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr h)

/-- Number of virtual pairs. -/
def virtCount (P : Parameters) (N p : ℕ) (K D : ℕ) (k0 : ℤ) : ℕ :=
  (Finset.univ.filter (fun dk : Fin D × Fin K => ¬ Good P N p k0 dk.1 dk.2)).card

/-- The seen functionals as a map `F_p^K → F_p^{|S|}`. -/
def seenMap (p K : ℕ) [Fact p.Prime] (k0 : ℤ) (H : ℕ) (S : Finset (ℕ × ℤ)) :
    (Fin K → ZMod p) →ₗ[ZMod p] (Fin S.card → ZMod p) :=
  LinearMap.pi fun i => psiLin p K k0 H (S.equivFin.symm i).1.1 (S.equivFin.symm i).1.2

theorem seenMap_apply_mem (K : ℕ) (k0 : ℤ) (H : ℕ) (S : Finset (ℕ × ℤ)) (y : Fin K → ZMod p)
    (hy : y ∈ LinearMap.ker (seenMap p K k0 H S)) (J : ℕ) (a : ℤ) (hJa : (J, a) ∈ S) :
    psiLin p K k0 H J a y = 0 := by
  have := congrFun (LinearMap.mem_ker.mp hy) (S.equivFin ⟨(J, a), hJa⟩)
  simpa [seenMap] using this

/-- **Theorem T-raw (design-generic count lemma).** -/
theorem tRaw_le_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {K D e0 : ℕ} (k0 : ℤ) (hD : D ≤ (p - 1) / 2) (S : Finset (ℕ × ℤ))
    (hseen : ∀ j e (a : ℤ), P.b N ≤ j → j < P.L N → e0 ≤ e → e < P.h N + D →
      (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e = a * p → (j / p, a) ∈ S) :
    (D - e0) * (K - S.card) - virtCount P N p K D k0 ≤ nullity P N p := by
  classical
  have hq : 0 < P.q N := Nat.mul_pos hP.2.2.1 hN
  set E := seenMap p K k0 (P.H N) S with hE
  set V : Submodule (ZMod p) (Fin K → ZMod p) := LinearMap.ker E with hV
  -- jets and virtual-pair map on `Fin D → V`
  let wV : (Fin D → V) →ₗ[ZMod p] (Fin D → Fin K → ZMod p) :=
    LinearMap.pi fun d => V.subtype.comp (LinearMap.proj d)
  let Φ : (Fin D → V) →ₗ[ZMod p] (Fin e0 → V) :=
    LinearMap.pi fun e => ∑ d : Fin D, lamc P N p d e • (LinearMap.proj d : (Fin D → V) →ₗ[ZMod p] V)
  let bad : Finset (Fin D × Fin K) :=
    Finset.univ.filter (fun dk : Fin D × Fin K => ¬ Good P N p k0 dk.1 dk.2)
  let B : (Fin D → V) →ₗ[ZMod p] (bad → ZMod p) :=
    LinearMap.pi fun b => (LinearMap.proj b.1.2 : (Fin K → ZMod p) →ₗ[ZMod p] ZMod p).comp
      (V.subtype.comp (LinearMap.proj b.1.1))
  obtain ⟨S0, hS0def⟩ : ∃ S0 : Submodule (ZMod p) (Fin D → V), S0 = LinearMap.ker B := ⟨_, rfl⟩
  have hS0 : ∀ x ∈ S0, ∀ d k, ¬ Good P N p k0 d k → (x d : Fin K → ZMod p) k = 0 := by
    intro x hx d k hg
    rw [hS0def] at hx
    have := congrFun (LinearMap.mem_ker.mp hx) ⟨(d, k), by simp [bad, hg]⟩
    simpa [B] using this
  let ι : S0 →ₗ[ZMod p] (Fin (P.n N) → ZMod p) :=
    (tRows P N p K D k0).comp (wV.comp S0.subtype)
  have hι : Function.Injective ι := by
    intro a b hab
    have hab' : tRows P N p K D k0 (wV a.1) = tRows P N p K D k0 (wV b.1) := hab
    have h0 : tRows P N p K D k0 (wV a.1 - wV b.1) = 0 := by
      rw [map_sub, hab', sub_self]
    have h1 := tRows_injective_on (P := P) (N := N) hp2 hD k0 (wV a.1 - wV b.1)
      (fun d k hg => by
        have := hS0 a.1 a.2 d k hg
        have := hS0 b.1 b.2 d k hg
        simp [wV, *]) h0
    have h2 : wV a.1 = wV b.1 := sub_eq_zero.mp h1
    apply Subtype.ext
    funext d
    apply Subtype.ext
    simpa [wV] using congrFun h2 d
  have hw : ∀ (x : Fin D → V) (e : ℕ), wvec P N p (wV x) e =
      ((∑ d : Fin D, lamc P N p d e • x d : V) : Fin K → ZMod p) := by
    intro x e
    simp [wvec, wV]
  have hjH : ∀ j, j < P.L N → j < P.H N := by
    intro j hj
    have := hP.2.2.2.1
    have h2 : 0 < P.h N := Nat.mul_pos this hN
    simp only [Parameters.H, Parameters.C]
    omega
  have hraw : ∀ x : S0, (Φ.comp S0.subtype) x = 0 → ∃ F : (ZMod p)[X], F.natDegree < P.q N ∧
      ∀ j, P.b N ≤ j → j < P.L N → uResp P N p j (ι x) = F.eval (j : ZMod p) := by
    intro x hx
    refine ⟨0, by simpa using hq, fun j h1 h2 => ?_⟩
    rw [Polynomial.eval_zero]
    refine uResp_tRows_eq_zero hP hN hp2 hH k0 (wV x.1) (fun d k hg => hS0 x.1 x.2 d k hg)
      (hjH j h2) ?_
    intro e he a hea
    rw [hw]
    by_cases hlt : e < e0
    · have h3 : (Φ x.1) ⟨e, hlt⟩ = 0 := congrFun hx ⟨e, hlt⟩
      have h4 : (Φ x.1) ⟨e, hlt⟩ = ∑ d : Fin D, lamc P N p d e • x.1 d := by simp [Φ]
      rw [h4] at h3
      rw [h3]
      simp
    · have hmem := hseen j e a h1 h2 (not_lt.mp hlt) he hea
      exact seenMap_apply_mem K k0 _ S _ (∑ d : Fin D, lamc P N p d e • x.1 d).2 _ _ hmem
  have hfd : FiniteDimensional (ZMod p) S0 := inferInstance
  have h := @w_raw P N p _ hp2 hH S0 _ _ hfd (Fin e0 → V) _ _ ι hι (Φ.comp S0.subtype) hraw
  -- dimension count
  have hdim : finrank (ZMod p) (Fin D → V) = D * finrank (ZMod p) V := by
    simp [Module.finrank_pi_fintype]
  have hB := LinearMap.finrank_range_add_finrank_ker B
  have hBr : finrank (ZMod p) (LinearMap.range B) ≤ virtCount P N p K D k0 := by
    have := Submodule.finrank_le (LinearMap.range B)
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this
    exact this
  have hr : finrank (ZMod p) (LinearMap.range (Φ.comp S0.subtype)) ≤ e0 * finrank (ZMod p) V := by
    have := Submodule.finrank_le (LinearMap.range (Φ.comp S0.subtype))
    simpa [Module.finrank_pi_fintype] using this
  have hk : K - S.card ≤ finrank (ZMod p) V := kappa_ge E
  have h1 : (D - e0) * finrank (ZMod p) V = D * finrank (ZMod p) V - e0 * finrank (ZMod p) V :=
    Nat.sub_mul _ _ _
  have h2 : (D - e0) * (K - S.card) ≤ (D - e0) * finrank (ZMod p) V :=
    Nat.mul_le_mul_left _ hk
  have hS0d : finrank (ZMod p) S0 = finrank (ZMod p) (LinearMap.ker B) := by rw [hS0def]
  omega

#print axioms tRaw_le_nullity
end
end CatalanMeasure.GenD.Uniform.W.Thin
