module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.MonoHost3
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# `monoHost3t`: the host of a monomial system for a packet with `cm ≤ p` atoms

The atoms are the first `cm` positions; they are extended by zero to the `p` positions of the slot system.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts6.Check
open Finset Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Prof
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD.Uniform.W.Thin
  CatalanMeasure.GenD.Uniform.W.Charts3 CatalanMeasure.GenD.Uniform.W.Charts6
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Zero extension of the first `cm` positions. -/
def extL (d p cm : ℕ) : (Fin cm → Fin d → ZMod p) →ₗ[ZMod p] (Fin p → Fin d → ZMod p) :=
  LinearMap.pi fun e => if h : e.val < cm then LinearMap.proj (⟨e.val, h⟩ : Fin cm) else 0

theorem extL_apply (d p cm : ℕ) (x : Fin cm → Fin d → ZMod p) (e : Fin p) :
    extL d p cm x e = if h : e.val < cm then x ⟨e.val, h⟩ else 0 := by
  unfold extL
  simp only [LinearMap.pi_apply]
  split_ifs <;> simp

theorem extL_zero (d p cm : ℕ) (x : Fin cm → Fin d → ZMod p) (e : Fin p) (h : cm ≤ e.val) : extL d p cm x e = 0 := by
  rw [extL_apply, dif_neg (by omega)]

/-- The cover for a packet with `cm` atoms: only the seen positions `e < cm` matter. -/
def CoverPt3t (pk : Packet) {K : ℕ} (M : MonoData P N p K)
    (ins : (Fin pk.n → ZMod p) →ₗ[ZMod p] (Fin K → ZMod p)) (low : (Fin pk.d → ZMod p) →ₗ[ZMod p] ZMod p)
    (width : Fin pk.charts.length → ℕ) (a cm : ℕ)
    (jet : ∀ g, Fin (width g) → (Fin p → (Fin pk.d → ZMod p)) →ₗ[ZMod p] (Fin pk.d → ZMod p)) : Prop :=
  ∀ j : ℕ, P.b N ≤ j → j + a * p < P.L N → ∀ e : Fin p, e.val < cm →
    (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e →
    ∃ g k g' k', jet g k = LinearMap.proj e ∧ jet g' k' = LinearMap.proj e ∧
      ∀ y : Fin pk.d → ZMod p, chartMap pk (pk.chart g) p pk.n y = 0 →
        chartMap pk (pk.chart g') p pk.n y = 0 →
        ∑ v ∈ range (a + 1), ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) *
          M.sys.prof.psi (P.H N) (j / p + v)
            (((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p) (ins (emb pk p pk.n y)) = low y

/-- **The host with `cm` atoms.** -/
def monoHost3t {pk : Packet} {K : ℕ} (M : MonoData P N p K)
    (ins proj : (Fin pk.n → ZMod p) →ₗ[ZMod p] (Fin K → ZMod p))
    (hTy : ∀ y, M.prof.Ty (proj y) = M.prof.Ty (ins y)) (hGy : ∀ y, M.prof.Gy (proj y) = M.prof.Gy (ins y))
    (low : (Fin pk.d → ZMod p) →ₗ[ZMod p] ZMod p)
    {width : Fin pk.charts.length → ℕ} (a r cm : ℕ)
    (jet : ∀ g, Fin (width g) → (Fin p → (Fin pk.d → ZMod p)) →ₗ[ZMod p] (Fin pk.d → ZMod p))
    (hinj : ∀ x : Fin p → Fin pk.d → ZMod p, (∀ e : Fin p, cm ≤ e.val → x e = 0) →
      (∀ g k, chartMap pk (pk.chart g) p pk.n (jet g k x) = 0) →
        (∀ e, proj (emb pk p pk.n (x e)) = 0) → x = 0)
    (hdom : ∀ x : Fin p → Fin pk.d → ZMod p, (∀ e : Fin p, cm ≤ e.val → x e = 0) →
      (∀ g k, chartMap pk (pk.chart g) p pk.n (jet g k x) = 0) →
        (fun e => proj (emb pk p pk.n (x e))) ∈ M.dom)
    (hG : ∀ x : Fin p → Fin pk.d → ZMod p, (∀ e : Fin p, cm ≤ e.val → x e = 0) →
      (∀ g k, chartMap pk (pk.chart g) p pk.n (jet g k x) = 0) →
        ∃ G : (ZMod p)[X], G.degree < (r : WithBot ℕ) ∧
          ∀ e : Fin p, G.eval ((((P.H N : ℤ) - 1 - e : ℤ)) : ZMod p) = low (x e))
    (hcm : cm ≤ p) (hcov : CoverPt3t pk M ins low width a cm jet) :
    HostIdent M.sys pk cm width a r := by
  have hpsi : ∀ H J (s : ℤ) (y : Fin pk.n → ZMod p),
      M.sys.prof.psi H J s (proj y) = M.sys.prof.psi H J s (ins y) := by
    intro H J s y
    show digitPhi H s (sourceM (p := p) J) (sourceZ (p := p) J) (M.prof.Gy (proj y))
      (M.prof.Ty (proj y)) (3 / 2) = digitPhi H s (sourceM (p := p) J) (sourceZ (p := p) J)
      (M.prof.Gy (ins y)) (M.prof.Ty (ins y)) (3 / 2)
    rw [hTy, hGy]
  refine
    { jet := fun g k => (jet g k).comp (extL pk.d p cm)
      xi := (LinearMap.pi fun e => (proj.comp (emb pk p pk.n)).comp (LinearMap.proj e)).comp (extL pk.d p cm)
      dom := fun x hx => hdom (extL pk.d p cm x) (fun e he => extL_zero _ _ _ x e he) hx
      inj := fun x hx h => ?_
      kill := fun x0 hx0 => ?_ }
  · have hz : ∀ e : Fin p, cm ≤ e.val → extL pk.d p cm x e = 0 := fun e he => extL_zero _ _ _ x e he
    have h0 := hinj (extL pk.d p cm x) hz hx (fun e => by simpa using congrFun h e)
    funext e
    have := congrFun h0 ⟨e.val, lt_of_lt_of_le e.isLt hcm⟩
    simpa [extL_apply, e.isLt] using this
  · set x : Fin p → Fin pk.d → ZMod p := extL pk.d p cm x0 with hxdef
    have hxz : ∀ e : Fin p, cm ≤ e.val → x e = 0 := fun e he => extL_zero _ _ _ x0 e he
    have hx : ∀ g k, chartMap pk (pk.chart g) p pk.n (jet g k x) = 0 := hx0
    obtain ⟨G, hGd, hGe⟩ := hG x hxz hx
    refine ⟨G, hGd, fun j h1 h2 => ?_⟩
    change ∑ v ∈ range (a + 1), ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) *
        M.sys.resp (j / p + v) (j % p) ((LinearMap.pi fun e => (proj.comp (emb pk p pk.n)).comp
          (LinearMap.proj e)) x) = _
    have key : ∀ v ∈ range (a + 1),
        ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) *
          M.sys.resp (j / p + v) (j % p) (LinearMap.pi (fun e => (proj.comp (emb pk p pk.n)).comp
            (LinearMap.proj e)) x) = ∑ e : Fin p,
          if (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e then
            ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) *
              M.sys.prof.psi (P.H N) (j / p + v)
                (((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p) (ins (emb pk p pk.n (x e))) else 0 := by
      intro v _
      rw [sys_resp, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      split_ifs
      · simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
        rw [hpsi]
      · simp
    rw [Finset.sum_congr rfl key, Finset.sum_comm]
    have hterm : ∀ e ∈ (Finset.univ : Finset (Fin p)), (∑ v ∈ range (a + 1),
        if (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e then
            ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) *
              M.sys.prof.psi (P.H N) (j / p + v)
                (((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p) (ins (emb pk p pk.n (x e))) else 0) =
        if (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e then low (x e) else 0 := by
      intro e _
      by_cases hd : (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e
      · simp only [hd, if_true]
        by_cases hem : e.val < cm
        · obtain ⟨g, k, g', k', hjet, hjet', hv⟩ := hcov j h1 h2 e hem hd
          exact hv (x e) (by
            have hk := hx g k
            rw [hjet] at hk
            simpa using hk) (by
            have hk := hx g' k'
            rw [hjet'] at hk
            simpa using hk)
        · rw [hxz e (not_lt.mp hem)]
          simp
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
end CatalanMeasure.GenD.Uniform.W.Charts6.Check
