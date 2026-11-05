module
public import Submission.CatalanMeasure.GenD.Interface
public import Submission.CatalanMeasure.GenD.Uniform.W.Profile
public import Mathlib.LinearAlgebra.Lagrange
@[expose] public section
set_option Elab.async false

/-!
# Theorem W for the actual G nullity

`gMat P N p` is the scaled residue matrix of the filtered matrix at `z = 0`, so
`nullity P N p = n - rank (gMat P N p)` (`nullity_eq`, by `rfl`).  Responses:

* filtered response at column `k`: `(gMat P N p)ᵀ *ᵥ c` at `k` (`gResp_apply`);
* raw residue response at `j`: `uResp P N p j c` (`RankU`; formula (R) in
  `Prefix/RawResponse.raw_response_intrinsic`).

Kill criteria: a row whose raw responses on the active interval `[b, L)` are a polynomial of
degree `< q` in `j` is in the left kernel (`gKill_of_raw_poly`).

Main statements, each `… ≤ nullity P N p`:
* `w_nullity`        — Theorem W (kill set `K` of filtered columns, cost `n - |K|`);
* `w_nullity_master` — any obstruction `χ`;
* `w_raw`            — every column killed through polynomial raw responses (cost `0`);
* `w_flat`           — polynomial raw responses of degree `< d`, cost `d - q`;
* `w_jflat`          — J-flat: raw responses depend only on `j mod p` through a polynomial
                       function of degree `< p - v`, cost `p - q - v` (= `(p-q-v)_+`);
* `w_prof_nullity`, `w_prof_raw`, `w_prof_flat` — partial-rank forms.
-/

namespace CatalanMeasure.GenD.Uniform.W
open Module Matrix Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD CatalanCore.Uniform.Content
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The G matrix whose left nullity is `nullity`. -/
abbrev gMat (P : Parameters) (N p : ℕ) [Fact p.Prime] :
    Matrix (Fin (P.n N)) (Fin (P.n N)) (ZMod p) :=
  scaledResidueMatrix (p := p)
    (Matrix.of fun r k : Fin (P.n N) => Parametric.filteredEntryRat P 0 N r.val k.val)

theorem nullity_eq : nullity P N p = P.n N - (gMat P N p).rank := rfl

/-- The filtered response of a row combination at column `k`. -/
theorem gResp_apply (c : Fin (P.n N) → ZMod p) (k : Fin (P.n N)) :
    (gMat P N p).transpose.mulVec c k = ∑ r : Fin (P.n N),
      palindromicRatResidue p ((p : ℚ) ^ 2 * Parametric.filteredEntryRat P 0 N r.val k.val) *
        c r := by
  simp [Matrix.mulVec, dotProduct, scaledResidueMatrix, Matrix.transpose_apply]

/-- **Kill criterion.**  Polynomial raw responses of degree `< q` on `[b, L)` put the row in the
left kernel. -/
theorem gKill_of_raw_poly (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) (c : Fin (P.n N) → ZMod p)
    (F : (ZMod p)[X]) (hF : F.natDegree < P.q N)
    (hraw : ∀ j, P.b N ≤ j → j < P.L N → uResp P N p j c = F.eval (j : ZMod p)) :
    (gMat P N p).transpose.mulVec c = 0 := by
  have h := secondaryTent_raw_polynomial_response_kernel (P := P) (p := p) (N := N) hp2 hH 0
    (by simp) c F hF (fun j h1 h2 => hraw j h1 h2)
  exact h

/-- **Theorem W for the G nullity.** -/
theorem w_nullity {A : Type*} [AddCommGroup A] [Module (ZMod p) A] [FiniteDimensional (ZMod p) A]
    {E : Type*} [AddCommGroup E] [Module (ZMod p) E]
    (ι : A →ₗ[ZMod p] (Fin (P.n N) → ZMod p)) (hι : Function.Injective ι)
    (Φ : A →ₗ[ZMod p] E) (Kset : Finset (Fin (P.n N)))
    (hkill : ∀ a, Φ a = 0 → ∀ k ∈ Kset, (gMat P N p).transpose.mulVec (ι a) k = 0) :
    finrank (ZMod p) A - finrank (ZMod p) (LinearMap.range Φ) - (P.n N - Kset.card) ≤
      nullity P N p :=
  w_core (gMat P N p) ι hι Φ Kset hkill

/-- Master form for the G nullity. -/
theorem w_nullity_master {A : Type*} [AddCommGroup A] [Module (ZMod p) A]
    [FiniteDimensional (ZMod p) A] {E Q : Type*} [AddCommGroup E] [Module (ZMod p) E]
    [AddCommGroup Q] [Module (ZMod p) Q]
    (ι : A →ₗ[ZMod p] (Fin (P.n N) → ZMod p)) (hι : Function.Injective ι)
    (Φ : A →ₗ[ZMod p] E) (χ : LinearMap.ker Φ →ₗ[ZMod p] Q)
    (hkill : ∀ u : LinearMap.ker Φ, χ u = 0 → (gMat P N p).transpose.mulVec (ι u) = 0) :
    finrank (ZMod p) A - finrank (ZMod p) (LinearMap.range Φ) -
      finrank (ZMod p) (LinearMap.range χ) ≤ nullity P N p :=
  w_master (gMat P N p) ι hι Φ χ hkill

/-- **Theorem W, raw form** (`K` = all columns): rows of `ker Φ` with polynomial raw responses
of degree `< q`. -/
theorem w_raw (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) {A : Type*} [AddCommGroup A]
    [Module (ZMod p) A] [FiniteDimensional (ZMod p) A] {E : Type*} [AddCommGroup E]
    [Module (ZMod p) E] (ι : A →ₗ[ZMod p] (Fin (P.n N) → ZMod p)) (hι : Function.Injective ι)
    (Φ : A →ₗ[ZMod p] E)
    (hraw : ∀ a, Φ a = 0 → ∃ F : (ZMod p)[X], F.natDegree < P.q N ∧
      ∀ j, P.b N ≤ j → j < P.L N → uResp P N p j (ι a) = F.eval (j : ZMod p)) :
    finrank (ZMod p) A - finrank (ZMod p) (LinearMap.range Φ) ≤ nullity P N p :=
  w_core_all (gMat P N p) ι hι Φ (fun a ha => by
    obtain ⟨F, hF, h⟩ := hraw a ha
    exact gKill_of_raw_poly hp2 hH (ι a) F hF h)

/-- Coefficients `q, …, d-1`: the obstruction of the J-flat form. -/
def topCoeffs (q d : ℕ) : (ZMod p)[X] →ₗ[ZMod p] (Fin (d - q) → ZMod p) :=
  LinearMap.pi fun i => Polynomial.lcoeff (ZMod p) (q + i.val)

theorem natDegree_lt_of_top {q d : ℕ} (hq : 0 < q) (F : (ZMod p)[X])
    (hd : ∀ i, d ≤ i → F.coeff i = 0) (ht : topCoeffs q d F = 0) : F.natDegree < q := by
  have hle : F.natDegree ≤ q - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro i hi
    by_cases hid : d ≤ i
    · exact hd i hid
    · have := congrFun ht ⟨i - q, by omega⟩
      simp only [topCoeffs, LinearMap.pi_apply, Polynomial.lcoeff_apply, Pi.zero_apply] at this
      rwa [show q + (i - q) = i by omega] at this
  omega

/-- **Theorem W-flat (polynomial form).**  If the raw responses of `ker Φ` are given by a
linear family of polynomials supported below `d`, the filter cost is `d - q`. -/
theorem w_flat (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) (hq : 0 < P.q N) {A : Type*}
    [AddCommGroup A] [Module (ZMod p) A] [FiniteDimensional (ZMod p) A] {E : Type*}
    [AddCommGroup E] [Module (ZMod p) E]
    (ι : A →ₗ[ZMod p] (Fin (P.n N) → ZMod p)) (hι : Function.Injective ι)
    (Φ : A →ₗ[ZMod p] E) (d : ℕ) (F : LinearMap.ker Φ →ₗ[ZMod p] (ZMod p)[X])
    (hd : ∀ (u : LinearMap.ker Φ) i, d ≤ i → (F u).coeff i = 0)
    (hraw : ∀ (u : LinearMap.ker Φ) j, P.b N ≤ j → j < P.L N →
      uResp P N p j (ι u.1) = (F u).eval (j : ZMod p)) :
    finrank (ZMod p) A - finrank (ZMod p) (LinearMap.range Φ) - (d - P.q N) ≤
      nullity P N p := by
  let χ := (topCoeffs (p := p) (P.q N) d).comp F
  have h := w_nullity_master ι hι Φ χ (fun u hu =>
    gKill_of_raw_poly hp2 hH (ι u) (F u) (natDegree_lt_of_top hq (F u) (hd u) hu) (hraw u))
  have hr := rank_le_width χ
  omega

/-- Lagrange interpolation on all of `F_p`. -/
def interpAll (p : ℕ) [Fact p.Prime] : (ZMod p → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
  Lagrange.interpolate Finset.univ id

theorem interpAll_eval (s : ZMod p → ZMod p) (x : ZMod p) : (interpAll p s).eval x = s x := by
  have := Lagrange.eval_interpolate_at_node (s := (Finset.univ : Finset (ZMod p)))
    (v := id) s (Set.injOn_id _) (Finset.mem_univ x)
  simpa [interpAll] using this

theorem interpAll_coeff {e : ℕ} (he : e ≤ p) (s : ZMod p → ZMod p) (G : (ZMod p)[X])
    (hG : G.degree < e) (hs : ∀ x, s x = G.eval x) (i : ℕ) (hi : e ≤ i) :
    (interpAll p s).coeff i = 0 := by
  have hcard : (Finset.univ : Finset (ZMod p)).card = p := by
    rw [Finset.card_univ, ZMod.card]
  have hG' : G.degree < (Finset.univ : Finset (ZMod p)).card := by
    rw [hcard]
    exact hG.trans_le (by exact_mod_cast he)
  have heq := Lagrange.eq_interpolate_of_eval_eq (s := (Finset.univ : Finset (ZMod p)))
    (v := id) s (Set.injOn_id _) hG' (fun x _ => (hs x).symm)
  have : interpAll p s = G := heq.symm
  rw [this]
  exact Polynomial.coeff_eq_zero_of_degree_lt (hG.trans_le (by exact_mod_cast hi))

/-- **Theorem W-flat (J-flat form).**  If on `ker Φ` the raw response at `j` depends only on
`j mod p`, through a residue sequence that is a polynomial function of degree `< p - v` (the
residue sequences in `(x-1)^v F_p[x] mod x^p - 1`), the filter cost is `(p - q - v)_+`. -/
theorem w_jflat (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) (hq : 0 < P.q N) {A : Type*}
    [AddCommGroup A] [Module (ZMod p) A] [FiniteDimensional (ZMod p) A] {E : Type*}
    [AddCommGroup E] [Module (ZMod p) E]
    (ι : A →ₗ[ZMod p] (Fin (P.n N) → ZMod p)) (hι : Function.Injective ι)
    (Φ : A →ₗ[ZMod p] E) (v : ℕ) (s : LinearMap.ker Φ →ₗ[ZMod p] (ZMod p → ZMod p))
    (hpoly : ∀ u : LinearMap.ker Φ, ∃ G : (ZMod p)[X], G.degree < ((p - v : ℕ) : WithBot ℕ) ∧
      ∀ x, s u x = G.eval x)
    (hraw : ∀ (u : LinearMap.ker Φ) j, P.b N ≤ j → j < P.L N →
      uResp P N p j (ι u.1) = s u (j : ZMod p)) :
    finrank (ZMod p) A - finrank (ZMod p) (LinearMap.range Φ) - (p - P.q N - v) ≤
      nullity P N p := by
  have h := w_flat hp2 hH hq ι hι Φ (p - v) ((interpAll p).comp s)
    (fun u i hi => by
      obtain ⟨G, hG, hs⟩ := hpoly u
      exact interpAll_coeff (Nat.sub_le p v) (s u) G hG hs i hi)
    (fun u j h1 h2 => by
      rw [hraw u j h1 h2]
      exact (interpAll_eval (s u) (j : ZMod p)).symm)
  have e : p - v - P.q N = p - P.q N - v := by omega
  rwa [e] at h

/-! ### Partial-rank forms for the G nullity -/

section Prof
variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
variable {C : Type*} [Fintype C] {Wc : C → Type*} [∀ c, AddCommGroup (Wc c)]
  [∀ c, Module (ZMod p) (Wc c)]

/-- **Theorem W-prof for the G nullity**, kill-set form. -/
theorem w_prof_nullity {m : ℕ} (width : C → ℕ) (B : ∀ c, V →ₗ[ZMod p] Wc c)
    (jet : ∀ c, Fin (width c) → (Fin m → V) →ₗ[ZMod p] V)
    (ι : (Fin m → V) →ₗ[ZMod p] (Fin (P.n N) → ZMod p)) (hι : Function.Injective ι)
    (Kset : Finset (Fin (P.n N)))
    (hkill : ∀ x, (∀ c k, B c (jet c k x) = 0) → ∀ k ∈ Kset,
      (gMat P N p).transpose.mulVec (ι x) k = 0) :
    m * finrank (ZMod p) V - ∑ c, width c * finrank (ZMod p) (LinearMap.range (B c)) -
      (P.n N - Kset.card) ≤ nullity P N p :=
  w_prof_cols (gMat P N p) width B jet ι hι Kset hkill

/-- **Theorem W-prof for the G nullity**, raw form (every column killed). -/
theorem w_prof_raw (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) {m : ℕ} (width : C → ℕ)
    (B : ∀ c, V →ₗ[ZMod p] Wc c) (jet : ∀ c, Fin (width c) → (Fin m → V) →ₗ[ZMod p] V)
    (ι : (Fin m → V) →ₗ[ZMod p] (Fin (P.n N) → ZMod p)) (hι : Function.Injective ι)
    (hraw : ∀ x, (∀ c k, B c (jet c k x) = 0) → ∃ F : (ZMod p)[X], F.natDegree < P.q N ∧
      ∀ j, P.b N ≤ j → j < P.L N → uResp P N p j (ι x) = F.eval (j : ZMod p)) :
    m * finrank (ZMod p) V - ∑ c, width c * finrank (ZMod p) (LinearMap.range (B c)) ≤
      nullity P N p :=
  w_prof_all (gMat P N p) width B jet ι hι (fun x hx => by
    obtain ⟨F, hF, h⟩ := hraw x hx
    exact gKill_of_raw_poly hp2 hH (ι x) F hF h)

/-- **Theorem W-prof for the G nullity**, J-flat filter cost `d - q`. -/
theorem w_prof_flat (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) (hq : 0 < P.q N) {m : ℕ}
    (width : C → ℕ) (B : ∀ c, V →ₗ[ZMod p] Wc c)
    (jet : ∀ c, Fin (width c) → (Fin m → V) →ₗ[ZMod p] V)
    (ι : (Fin m → V) →ₗ[ZMod p] (Fin (P.n N) → ZMod p)) (hι : Function.Injective ι) (d : ℕ)
    (F : LinearMap.ker (constraintMap width B jet) →ₗ[ZMod p] (ZMod p)[X])
    (hd : ∀ (u : LinearMap.ker (constraintMap width B jet)) i, d ≤ i → (F u).coeff i = 0)
    (hraw : ∀ (u : LinearMap.ker (constraintMap width B jet)) j, P.b N ≤ j → j < P.L N →
      uResp P N p j (ι u.1) = (F u).eval (j : ZMod p)) :
    m * finrank (ZMod p) V - ∑ c, width c * finrank (ZMod p) (LinearMap.range (B c)) -
      (d - P.q N) ≤ nullity P N p := by
  let χ := (topCoeffs (p := p) (P.q N) d).comp F
  have h := w_prof (gMat P N p) width B jet ι hι χ (fun u hu =>
    gKill_of_raw_poly hp2 hH (ι u) (F u) (natDegree_lt_of_top hq (F u) (hd u) hu) (hraw u))
  have hr := rank_le_width χ
  rw [nullity_eq]
  omega

end Prof

end
end CatalanMeasure.GenD.Uniform.W
