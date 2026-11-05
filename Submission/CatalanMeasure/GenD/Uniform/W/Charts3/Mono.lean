module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts3.OfIdent
@[expose] public section
set_option Elab.async false

/-!
# Monomial slot systems: the four-point frame as a `SlotSystem`

In the bank frame the atoms are `Poly_{<p} ⊗ V`: the slot polynomials are the **monomials**
`lam_e = X^e`, `e < p`, and the profile maps `Ty, Gy` carry all the block/type structure
(`(Y-1)^{a_h}(F + (Y-1)E)` times the Chebyshev pair coefficients, mixed A/C/centre types together).
Then the raw response at a column `(J, ℓ)` has **at most one** term per position `e < p`, the
`e ≡ H-1-ℓ (mod p)`, with fixed quotient `a_e = (H-1-ℓ-e)/p`; the jets of the response are
coordinate projections `x ↦ x_e`.  This module records that reduction:

* `MonoData`   : the physical data (rows, `repU`, `repT`, injectivity on a domain `dom`);
* `MonoData.sys` : the `SlotSystem` with `D = emax = p`, `lam e = X^e`;
* `wv_mono`, `sys_resp` : coefficient jets are the atoms; the response is the sum over `e < p`;
* `monoHost` : a `HostIdent` from (i) the domain hypothesis "jet kernel ⊆ dom", (i') the `B`-graph polynomial `hG`, and (ii) the
  window cover `CoverPt` : at every active column and position `e` seen, some group's jet is the
  coordinate projection `x ↦ x_e` and the (`a`-fold `J`-differenced) seen covector vanishes on the
  kernel of that group's chart.

So the whole physical content of the host is exactly `MonoData` + `hdom` + `CoverPt`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts3
open Finset Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Prof
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Physical data of a monomial slot system. -/
structure MonoData (P : Parameters) (N p : ℕ) [Fact p.Prime] (K : ℕ) where
  prof : Prof p K
  rows : (Fin p → Fin K → ZMod p) →ₗ[ZMod p] (Fin (P.n N) → ZMod p)
  dom : Submodule (ZMod p) (Fin p → Fin K → ZMod p)
  repU : ∀ x ∈ dom, (X - 1) ^ P.h N * intrinsicU P N p (rows x) =
    ∑ e : Fin p, X ^ (e : ℕ) * (prof.Ty (x e)).comp (X ^ p)
  repT : ∀ x ∈ dom, (X - 1) ^ P.h N * (X ^ 2 - 1) ^ ((p - 1) / 2) * intrinsicT P N p (rows x) =
    ∑ e : Fin p, X ^ (e : ℕ) * (prof.Gy (x e)).comp (X ^ p)
  inj : ∀ x ∈ dom, rows x = 0 → x = 0

/-- The monomial slot system. -/
@[reducible] def MonoData.sys {K : ℕ} (M : MonoData P N p K) : SlotSystem P N p where
  K := K
  D := p
  emax := p
  prof := M.prof
  lam := fun e => X ^ (e : ℕ)
  rows := M.rows
  dom := M.dom
  deg := fun e => by rw [natDegree_X_pow]; exact e.isLt
  repU := M.repU
  repT := M.repT
  inj := M.inj

theorem wv_mono {K : ℕ} (M : MonoData P N p K) (x : Fin p → Fin K → ZMod p) (e : Fin p) :
    wv M.sys.lam x e = x e := by
  unfold wv
  show ∑ d : Fin p, ((X ^ (d : ℕ) : (ZMod p)[X]).coeff e) • x d = x e
  simp only [coeff_X_pow, Fin.val_inj]
  rw [Finset.sum_eq_single e]
  · simp
  · intro d _ hd; simp [Ne.symm hd]
  · simp

/-- Response of a monomial system: one term per position. -/
theorem sys_resp {K : ℕ} (M : MonoData P N p K) (J ell : ℕ) (x : Fin p → Fin K → ZMod p) :
    M.sys.resp J ell x = ∑ e : Fin p,
      if (p : ℤ) ∣ (P.H N : ℤ) - 1 - ell - e then
        M.sys.prof.psi (P.H N) J (((P.H N : ℤ) - 1 - ell - e) / p) (x e) else 0 := by
  unfold SlotSystem.resp
  rw [← Fin.sum_univ_eq_sum_range (fun e => if (p : ℤ) ∣ (P.H N : ℤ) - 1 - ell - e then
      M.sys.prof.psi (P.H N) J (((P.H N : ℤ) - 1 - ell - e) / p) (wv M.sys.lam x e) else 0) p]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [wv_mono]

/-- Exactly one position `e < p` is seen at a column: `e ≡ z (mod p)`. -/
theorem exists_unique_pos (z : ℤ) : ∃! e : Fin p, (p : ℤ) ∣ z - e := by
  have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine ⟨⟨(z % p).toNat, ?_⟩, ?_, ?_⟩
  · have := Int.emod_lt_of_pos z hp
    have := Int.emod_nonneg z hp.ne'
    omega
  · have h0 := Int.emod_nonneg z hp.ne'
    show (p : ℤ) ∣ z - ((z % p).toNat : ℤ)
    rw [Int.toNat_of_nonneg h0]
    exact Dvd.intro (z / p) (by have := Int.emod_def z p; linarith)
  · intro e he
    have h0 := Int.emod_nonneg z hp.ne'
    have h1 := Int.emod_lt_of_pos z hp
    have h2 : (p : ℤ) ∣ z - (z % p) := Dvd.intro (z / p) (by have := Int.emod_def z p; linarith)
    have h3 : (p : ℤ) ∣ ((z % p : ℤ) - e) := by
      have := dvd_sub he h2
      have e1 : z - (e : ℤ) - (z - z % p) = z % p - e := by ring
      rwa [e1] at this
    have := e.isLt
    have h4 := Int.eq_zero_of_abs_lt_dvd h3 (by rw [abs_lt]; constructor <;> omega)
    apply Fin.ext
    show (e : ℕ) = (z % p).toNat
    omega

/-- The window cover: at every active column and seen position, a group whose jet is the coordinate
projection and whose chart kernel makes the (`a`-fold `J`-differenced) seen covector equal to the
functional `low` (the `B`-graph coordinate; `low = 0` is the plain kill). -/
def CoverPt (pk : Packet) (M : MonoData P N p pk.n) (low : (Fin pk.d → ZMod p) →ₗ[ZMod p] ZMod p)
    (width : Fin pk.charts.length → ℕ) (a : ℕ)
    (jet : ∀ g, Fin (width g) → (Fin p → (Fin pk.d → ZMod p)) →ₗ[ZMod p] (Fin pk.d → ZMod p)) :
    Prop :=
  ∀ j : ℕ, P.b N ≤ j → j + a * p < P.L N → ∀ e : Fin p,
    (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e →
    ∃ g, ∃ k : Fin (width g), jet g k = LinearMap.proj e ∧
      ∀ y : Fin pk.d → ZMod p, chartMap pk (pk.chart g) p pk.n y = 0 →
        ∑ v ∈ range (a + 1), ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) *
          M.sys.prof.psi (P.H N) (j / p + v)
            (((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p) (emb pk p pk.n y) = low y

/-- **The host of a monomial system.**  `hG` : on the jet kernel, the `low` coordinate read at
position `e` is a polynomial `G` of degree `< r` evaluated at `H - 1 - e` (the `G_B ∈
(y-1)^{p-r} Poly_{<r}` encoding of paper §6, to be derived from the jets at `1`). -/
def monoHost {pk : Packet} (M : MonoData P N p pk.n) (hS : pk.Sound) (hpD : ¬ (p : ℤ) ∣ pk.D)
    (low : (Fin pk.d → ZMod p) →ₗ[ZMod p] ZMod p)
    {width : Fin pk.charts.length → ℕ} (a r : ℕ)
    (jet : ∀ g, Fin (width g) → (Fin p → (Fin pk.d → ZMod p)) →ₗ[ZMod p] (Fin pk.d → ZMod p))
    (hdom : ∀ x : Fin p → Fin pk.d → ZMod p,
      (∀ g k, chartMap pk (pk.chart g) p pk.n (jet g k x) = 0) →
        (fun e => emb pk p pk.n (x e)) ∈ M.dom)
    (hG : ∀ x : Fin p → Fin pk.d → ZMod p,
      (∀ g k, chartMap pk (pk.chart g) p pk.n (jet g k x) = 0) →
        ∃ G : (ZMod p)[X], G.degree < (r : WithBot ℕ) ∧
          ∀ e : Fin p, G.eval ((((P.H N : ℤ) - 1 - e : ℤ)) : ZMod p) = low (x e))
    (hcov : CoverPt pk M low width a jet) :
    HostIdent M.sys pk p width a r := by
  refine
    { jet := jet
      xi := LinearMap.pi fun e => (emb pk p pk.n).comp (LinearMap.proj e)
      dom := fun x hx => hdom x hx
      inj := fun x _ h => ?_
      kill := fun x hx => ?_ }
  · have hemb : Function.Injective (emb pk p pk.n) := emb_injective hS rfl (not_dvd_delta hpD)
    funext e
    exact hemb (by simpa using congrFun h e)
  · obtain ⟨G, hGd, hGe⟩ := hG x hx
    refine ⟨G, hGd, fun j h1 h2 => ?_⟩
    have key : ∀ v ∈ range (a + 1),
        ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) *
          M.sys.resp (j / p + v) (j % p) (LinearMap.pi (fun e => (emb pk p pk.n).comp
            (LinearMap.proj e)) x) = ∑ e : Fin p,
          if (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e then
            ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) *
              M.sys.prof.psi (P.H N) (j / p + v)
                (((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p) (emb pk p pk.n (x e)) else 0 := by
      intro v _
      rw [sys_resp, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      split_ifs <;> simp
    rw [Finset.sum_congr rfl key, Finset.sum_comm]
    have hterm : ∀ e ∈ (Finset.univ : Finset (Fin p)), (∑ v ∈ range (a + 1),
        if (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e then
            ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) *
              M.sys.prof.psi (P.H N) (j / p + v)
                (((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p) (emb pk p pk.n (x e)) else 0) =
        if (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e then low (x e) else 0 := by
      intro e _
      by_cases hd : (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e
      · simp only [hd, if_true]
        obtain ⟨g, k, hjet, hv⟩ := hcov j h1 h2 e hd
        exact hv (x e) (by
          have hk := hx g k
          rw [hjet] at hk
          simpa using hk)
      · simp only [hd, if_false]
        exact Finset.sum_const_zero
    rw [Finset.sum_congr rfl hterm]
    obtain ⟨e0, he0, huniq⟩ := exists_unique_pos (p := p) ((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ))
    rw [Finset.sum_eq_single e0]
    · rw [if_pos he0, ← hGe e0]
      congr 1
      have h6 : (((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e0 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr he0
      push_cast [ZMod.natCast_mod] at h6 ⊢
      linear_combination h6
    · intro e _ hne
      rw [if_neg (fun hd => hne (huniq e hd))]
    · intro h; exact absurd (Finset.mem_univ e0) h

end
end CatalanMeasure.GenD.Uniform.W.Charts3
