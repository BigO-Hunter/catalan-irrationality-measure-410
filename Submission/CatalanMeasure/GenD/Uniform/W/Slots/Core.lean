module
public import Submission.CatalanMeasure.GenD.Uniform.W.Thin.Combine
@[expose] public section
set_option Elab.async false

/-!
# Generic slot systems over Theorem W

A *slot system* packages the pair pipeline shared by every thin-window family:

* atoms (virtual-pair-free profile data) `x : Fin D → F_p^K`, mapped linearly to rows `rows x`;
* slot polynomials `lam d ∈ F_p[X]` and profile maps `Ty, Gy : F_p^K → F_p[Y]` with the two
  identities (`Y = X^p`)

      (X-1)^h · intrinsicU (rows x)               = Σ_d lam d · Ty(x d)(X^p),
      (X-1)^h (X²-1)^((p-1)/2) · intrinsicT (rows x) = Σ_d lam d · Gy(x d)(X^p);

* injectivity of `rows` on the domain `dom`.

From these alone: the raw response of `rows x` is `Σ_e [p ∣ H-1-ℓ-e] ψ(J, a_e)(w_e)`
(`uResp_slot`) with `w_e = Σ_d lam_d[e] x_d`, and Theorem W gives the counts
`slot_nullity_raw`, `slot_nullity_jflat`, `slot_nullity_pi`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Slots
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Profile maps of a slot family: a profile `y ∈ F_p^K` gives the `(Ty, Gy)` polynomials in
`Y = X^p` that multiply the slot polynomials. -/
structure Prof (p K : ℕ) [Fact p.Prime] where
  Ty : (Fin K → ZMod p) →ₗ[ZMod p] (ZMod p)[X]
  Gy : (Fin K → ZMod p) →ₗ[ZMod p] (ZMod p)[X]

variable {K D : ℕ}

/-- The source covector at `(J, a)` of a profile. -/
def Prof.psi (F : Prof p K) (H J : ℕ) (a : ℤ) : (Fin K → ZMod p) →ₗ[ZMod p] ZMod p where
  toFun y := digitPhi H a (sourceM (p := p) J) (sourceZ (p := p) J) (F.Gy y) (F.Ty y) (3 / 2)
  map_add' y z := by
    simp only [map_add]
    unfold digitPhi
    simp only [intrinsicCoeff_add', add_mul, Finset.sum_add_distrib, mul_add]
    ring
  map_smul' c y := by
    simp only [map_smul, RingHom.id_apply, smul_eq_mul]
    unfold digitPhi
    simp only [intrinsicCoeff_smul', mul_assoc, ← Finset.mul_sum]
    ring

/-- Coefficient-`e` profile `w_e = Σ_d lam_d[e] x_d` of a slot datum. -/
def wv (lam : Fin D → (ZMod p)[X]) (x : Fin D → Fin K → ZMod p) (e : ℕ) : Fin K → ZMod p :=
  ∑ d : Fin D, (lam d).coeff e • x d

/-- `wv` as a linear map. -/
def wvL (lam : Fin D → (ZMod p)[X]) (e : ℕ) :
    (Fin D → Fin K → ZMod p) →ₗ[ZMod p] (Fin K → ZMod p) :=
  ∑ d : Fin D, (lam d).coeff e • (LinearMap.proj d : (Fin D → Fin K → ZMod p) →ₗ[ZMod p] _)

theorem wvL_apply (lam : Fin D → (ZMod p)[X]) (e : ℕ) (x : Fin D → Fin K → ZMod p) :
    wvL lam e x = wv lam x e := by
  simp [wvL, wv, LinearMap.sum_apply]

/-- Monomial expansion of `Σ_d lam_d G_d(X^p)`. -/
theorem slot_expand' (emax : ℕ) (lam : Fin D → (ZMod p)[X])
    (hdeg : ∀ d, (lam d).natDegree < emax) (G : Fin D → (ZMod p)[X]) :
    ∑ d : Fin D, lam d * (G d).comp (X ^ p) =
      ∑ e ∈ Finset.range emax, X ^ e *
        (∑ d : Fin D, C ((lam d).coeff e) * G d).comp (X ^ p) := by
  have hlam : ∀ d : Fin D, lam d = ∑ e ∈ Finset.range emax, C ((lam d).coeff e) * X ^ e := by
    intro d
    conv_lhs => rw [Polynomial.as_sum_range' _ _ (hdeg d)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Polynomial.C_mul_X_pow_eq_monomial]
  have : ∀ d : Fin D, lam d * (G d).comp (X ^ p) =
      ∑ e ∈ Finset.range emax, X ^ e * (C ((lam d).coeff e) * G d).comp (X ^ p) := by
    intro d
    conv_lhs => rw [hlam d, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Polynomial.mul_comp, Polynomial.C_comp]
    ring
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [sum_comp', Finset.mul_sum]

/-- A slot system: the abstract pair pipeline (atoms, rows, raw response, kill, count). -/
structure SlotSystem (P : Parameters) (N p : ℕ) [Fact p.Prime] where
  K : ℕ
  D : ℕ
  /-- All slot polynomials have degree `< emax`. -/
  emax : ℕ
  prof : Prof p K
  lam : Fin D → (ZMod p)[X]
  rows : (Fin D → Fin K → ZMod p) →ₗ[ZMod p] (Fin (P.n N) → ZMod p)
  dom : Submodule (ZMod p) (Fin D → Fin K → ZMod p)
  deg : ∀ d, (lam d).natDegree < emax
  repU : ∀ x ∈ dom, (X - 1) ^ P.h N * intrinsicU P N p (rows x) =
    ∑ d, lam d * (prof.Ty (x d)).comp (X ^ p)
  repT : ∀ x ∈ dom, (X - 1) ^ P.h N * (X ^ 2 - 1) ^ ((p - 1) / 2) * intrinsicT P N p (rows x) =
    ∑ d, lam d * (prof.Gy (x d)).comp (X ^ p)
  inj : ∀ x ∈ dom, rows x = 0 → x = 0

namespace SlotSystem
variable (S : SlotSystem P N p)

/-- The raw response (formula (R)) of the datum `x` at column `J p + ℓ`, in slot form. -/
def resp (J ell : ℕ) (x : Fin S.D → Fin S.K → ZMod p) : ZMod p :=
  ∑ e ∈ Finset.range S.emax,
    if (p : ℤ) ∣ (P.H N : ℤ) - 1 - ell - e then
      S.prof.psi (P.H N) J (((P.H N : ℤ) - 1 - ell - e) / p) (wv S.lam x e)
    else 0

theorem Ty_wv (x : Fin S.D → Fin S.K → ZMod p) (e : ℕ) :
    S.prof.Ty (wv S.lam x e) = ∑ d, C ((S.lam d).coeff e) * S.prof.Ty (x d) := by
  simp [wv, map_sum, Polynomial.smul_eq_C_mul]

theorem Gy_wv (x : Fin S.D → Fin S.K → ZMod p) (e : ℕ) :
    S.prof.Gy (wv S.lam x e) = ∑ d, C ((S.lam d).coeff e) * S.prof.Gy (x d) := by
  simp [wv, map_sum, Polynomial.smul_eq_C_mul]

/-- **Response of a slot datum** (formula (R) evaluated on the slots). -/
theorem uResp_slot (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {x : Fin S.D → Fin S.K → ZMod p} (hx : x ∈ S.dom) {j : ℕ} (hj : j < P.H N) :
    uResp P N p j (S.rows x) = S.resp (j / p) (j % p) x := by
  rw [uResp_intrinsicResponse hP hN hp2 hH hj, S.repT x hx, S.repU x hx,
    slot_expand' S.emax S.lam S.deg (fun d => S.prof.Gy (x d)),
    slot_expand' S.emax S.lam S.deg (fun d => S.prof.Ty (x d)), intrinsicResponse_sum]
  unfold resp
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Gy_wv, ← Ty_wv, intrinsicResponse_monomial]
  split_ifs <;> rfl

/-- Kill criterion: `V` annihilated by the seen covectors, jets `e < e0` vanishing. -/
theorem resp_eq_zero_of_seen (V : Submodule (ZMod p) (Fin S.K → ZMod p)) (e0 J ell : ℕ)
    (x : Fin S.D → Fin S.K → ZMod p) (hxV : ∀ d, x d ∈ V) (hjet : ∀ e < e0, wv S.lam x e = 0)
    (hseen : ∀ e (a : ℤ), e0 ≤ e → e < S.emax → (P.H N : ℤ) - 1 - ell - e = a * p →
      ∀ y ∈ V, S.prof.psi (P.H N) J a y = 0) : S.resp J ell x = 0 := by
  unfold resp
  refine Finset.sum_eq_zero fun e he => ?_
  split_ifs with hd
  · obtain ⟨a, ha⟩ := hd
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have : ((P.H N : ℤ) - 1 - ell - e) / p = a := by
      rw [ha]; exact Int.mul_ediv_cancel_left _ hp0
    rw [this]
    by_cases hlt : e < e0
    · rw [hjet e hlt]; simp
    · exact hseen e a (not_lt.mp hlt) (Finset.mem_range.mp he) (by rw [ha]; ring) _
        (by
          unfold wv
          exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (hxV d))
  · rfl

theorem rows_injective_dom {A : Type*} [AddCommGroup A] [Module (ZMod p) A]
    (ξ : A →ₗ[ZMod p] (Fin S.D → Fin S.K → ZMod p)) (hξ : ∀ a, ξ a ∈ S.dom)
    (hξi : Function.Injective ξ) : Function.Injective (S.rows.comp ξ) := by
  refine injective_of_zero _ fun a ha => ?_
  exact hξi (by rw [map_zero]; exact S.inj _ (hξ a) ha)

theorem hjH (hP : Admissible P) (hN : 0 < N) {j : ℕ} (hj : j < P.L N) : j < P.H N := by
  have := hP.2.2.2.1
  have h2 : 0 < P.h N := Nat.mul_pos this hN
  simp only [Parameters.H, Parameters.C]
  omega

/-- **Slot count, raw form.**  Atoms `ξ a` in the domain whose slot response vanishes on
`[b, L)` for `a ∈ ker Φ`. -/
theorem slot_nullity_raw (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {A E : Type*} [AddCommGroup A] [Module (ZMod p) A] [FiniteDimensional (ZMod p) A]
    [AddCommGroup E] [Module (ZMod p) E]
    (ξ : A →ₗ[ZMod p] (Fin S.D → Fin S.K → ZMod p)) (hξ : ∀ a, ξ a ∈ S.dom)
    (hξi : Function.Injective ξ) (Φ : A →ₗ[ZMod p] E)
    (hkill : ∀ a, Φ a = 0 → ∀ j, P.b N ≤ j → j < P.L N → S.resp (j / p) (j % p) (ξ a) = 0) :
    finrank (ZMod p) A - finrank (ZMod p) (LinearMap.range Φ) ≤ nullity P N p := by
  have hq : 0 < P.q N := Nat.mul_pos hP.2.2.1 hN
  refine w_raw hp2 hH (S.rows.comp ξ) (S.rows_injective_dom ξ hξ hξi) Φ fun a ha => ?_
  refine ⟨0, by simpa using hq, fun j h1 h2 => ?_⟩
  rw [Polynomial.eval_zero]
  show uResp P N p j (S.rows (ξ a)) = 0
  rw [S.uResp_slot hP hN hp2 hH (hξ a) (hjH hP hN h2)]
  exact hkill a ha j h1 h2

/-- **Slot count, J-flat form.**  If on `ker Φ` the slot response depends only on `j mod p`
through a polynomial function of degree `< p - v`, the filter cost is `(p - q - v)_+`. -/
theorem slot_nullity_jflat (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {A E : Type*} [AddCommGroup A] [Module (ZMod p) A] [FiniteDimensional (ZMod p) A]
    [AddCommGroup E] [Module (ZMod p) E]
    (ξ : A →ₗ[ZMod p] (Fin S.D → Fin S.K → ZMod p)) (hξ : ∀ a, ξ a ∈ S.dom)
    (hξi : Function.Injective ξ) (Φ : A →ₗ[ZMod p] E) (v : ℕ)
    (s : LinearMap.ker Φ →ₗ[ZMod p] (ZMod p → ZMod p))
    (hpoly : ∀ u : LinearMap.ker Φ, ∃ G : (ZMod p)[X], G.degree < ((p - v : ℕ) : WithBot ℕ) ∧
      ∀ x, s u x = G.eval x)
    (hresp : ∀ (u : LinearMap.ker Φ) j, P.b N ≤ j → j < P.L N →
      S.resp (j / p) (j % p) (ξ u.1) = s u (j : ZMod p)) :
    finrank (ZMod p) A - finrank (ZMod p) (LinearMap.range Φ) - (p - P.q N - v) ≤
      nullity P N p := by
  have hq : 0 < P.q N := Nat.mul_pos hP.2.2.1 hN
  refine w_jflat hp2 hH hq (S.rows.comp ξ) (S.rows_injective_dom ξ hξ hξi) Φ v s hpoly
    fun u j h1 h2 => ?_
  show uResp P N p j (S.rows (ξ u.1)) = _
  rw [S.uResp_slot hP hN hp2 hH (hξ u.1) (hjH hP hN h2)]
  exact hresp u j h1 h2

/-! ### Product atoms: `dom ⊓ Π V` with the low-coefficient jets removed -/

/-- The atoms `Fin D → V` inside the domain. -/
def atoms (V : Submodule (ZMod p) (Fin S.K → ZMod p)) :
    Submodule (ZMod p) (Fin S.D → Fin S.K → ZMod p) :=
  S.dom ⊓ Submodule.pi Set.univ (fun _ => V)

theorem mem_atoms {V : Submodule (ZMod p) (Fin S.K → ZMod p)}
    {x : Fin S.D → Fin S.K → ZMod p} :
    x ∈ S.atoms V ↔ x ∈ S.dom ∧ ∀ d, x d ∈ V := by
  simp [atoms, Submodule.mem_pi]

/-- The low jets `w_e`, `e < e0`, of an atom, as an element of `Fin e0 → V`. -/
def jets (V : Submodule (ZMod p) (Fin S.K → ZMod p)) (e0 : ℕ) :
    S.atoms V →ₗ[ZMod p] (Fin e0 → V) :=
  LinearMap.pi fun e => LinearMap.codRestrict V ((wvL S.lam e).comp (S.atoms V).subtype)
    (fun a => by
      have := ((S.mem_atoms).mp a.2).2
      show wvL S.lam e a.1 ∈ V
      rw [wvL_apply]
      unfold wv
      exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (this d))

theorem jets_apply (V : Submodule (ZMod p) (Fin S.K → ZMod p)) (e0 : ℕ) (a : S.atoms V)
    (e : Fin e0) : ((S.jets V e0 a) e : Fin S.K → ZMod p) = wv S.lam a.1 e := by
  simp [jets, wvL_apply]

theorem finrank_range_jets_le (V : Submodule (ZMod p) (Fin S.K → ZMod p)) (e0 : ℕ) :
    finrank (ZMod p) (LinearMap.range (S.jets V e0)) ≤ e0 * finrank (ZMod p) V := by
  have := Submodule.finrank_le (LinearMap.range (S.jets V e0))
  simpa [Module.finrank_pi_fintype] using this

/-- **Seen-subspace count** (all slot families whose profile space is killed by the seen
covectors; T-raw tail is the case `V = ker (seen map)`). -/
theorem slot_nullity_pi (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (V : Submodule (ZMod p) (Fin S.K → ZMod p)) (e0 : ℕ)
    (hseen : ∀ j e (a : ℤ), P.b N ≤ j → j < P.L N → e0 ≤ e → e < S.emax →
      (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e = a * p →
        ∀ y ∈ V, S.prof.psi (P.H N) (j / p) a y = 0) :
    finrank (ZMod p) (S.atoms V) ≤ nullity P N p + e0 * finrank (ZMod p) V := by
  have h := S.slot_nullity_raw hP hN hp2 hH (S.atoms V).subtype
    (fun a => ((S.mem_atoms).mp a.2).1) (Submodule.subtype_injective _) (S.jets V e0)
    (fun a ha j h1 h2 => by
      refine S.resp_eq_zero_of_seen V e0 (j / p) (j % p) a.1
        (((S.mem_atoms).mp a.2).2) (fun e he => ?_)
        (fun e a' he0 he hdv y hy => hseen j e a' h1 h2 he0 he hdv y hy)
      have := congrFun (LinearMap.mem_ker.mp ha) ⟨e, he⟩
      have h3 := S.jets_apply V e0 a ⟨e, he⟩
      rw [this] at h3
      simpa using h3.symm)
  have := S.finrank_range_jets_le V e0
  omega

end SlotSystem

end
end CatalanMeasure.GenD.Uniform.W.Slots
