module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.MonoHost
@[expose] public section
set_option Elab.async false

/-!
# `monoHost3`: the host of a monomial system for a packet with a reduced coordinate set

The packet has `pk.n` coordinates; the monomial system lives on `K = 4b + 2 + ex` profile coordinates.
`ins` inserts the packet coordinates into the profile coordinates (the absent ones are zero), `pr = projExtras ∘ ins`.
Compared with `monoHost2` (where `ins = id`): `Ty, Gy` of `pr y` and `ins y` agree, and the cover is stated for `psi (ins (emb y))`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts6
open Finset Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Prof
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD.Uniform.W.Thin
  CatalanMeasure.GenD.Uniform.W.Charts3
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Two-group window cover for a packet with a reduced coordinate set: at every active column and seen position,
two groups whose jets are the coordinate projection `x ↦ x_e` (possibly equal) whose chart kernels together force
`ψ(J-differenced)(ins y) = low y`. -/
def CoverPt3 (pk : Packet) {K : ℕ} (M : MonoData P N p K)
    (ins : (Fin pk.n → ZMod p) →ₗ[ZMod p] (Fin K → ZMod p)) (low : (Fin pk.d → ZMod p) →ₗ[ZMod p] ZMod p)
    (width : Fin pk.charts.length → ℕ) (a : ℕ)
    (jet : ∀ g, Fin (width g) → (Fin p → (Fin pk.d → ZMod p)) →ₗ[ZMod p] (Fin pk.d → ZMod p)) :
    Prop :=
  ∀ j : ℕ, P.b N ≤ j → j + a * p < P.L N → ∀ e : Fin p,
    (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e →
    ∃ g k g' k', jet g k = LinearMap.proj e ∧ jet g' k' = LinearMap.proj e ∧
      ∀ y : Fin pk.d → ZMod p, chartMap pk (pk.chart g) p pk.n y = 0 →
        chartMap pk (pk.chart g') p pk.n y = 0 →
        ∑ v ∈ range (a + 1), ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) *
          M.sys.prof.psi (P.H N) (j / p + v)
            (((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p) (ins (emb pk p pk.n y)) = low y


/-- **The host of a monomial system with graph coordinates.** -/
def monoHost3 {pk : Packet} {K : ℕ} (M : MonoData P N p K)
    (ins proj : (Fin pk.n → ZMod p) →ₗ[ZMod p] (Fin K → ZMod p))
    (hTy : ∀ y, M.prof.Ty (proj y) = M.prof.Ty (ins y)) (hGy : ∀ y, M.prof.Gy (proj y) = M.prof.Gy (ins y))
    (low : (Fin pk.d → ZMod p) →ₗ[ZMod p] ZMod p)
    {width : Fin pk.charts.length → ℕ} (a r : ℕ)
    (jet : ∀ g, Fin (width g) → (Fin p → (Fin pk.d → ZMod p)) →ₗ[ZMod p] (Fin pk.d → ZMod p))
    (hinj : ∀ x : Fin p → Fin pk.d → ZMod p,
      (∀ g k, chartMap pk (pk.chart g) p pk.n (jet g k x) = 0) →
        (∀ e, proj (emb pk p pk.n (x e)) = 0) → x = 0)
    (hdom : ∀ x : Fin p → Fin pk.d → ZMod p,
      (∀ g k, chartMap pk (pk.chart g) p pk.n (jet g k x) = 0) →
        (fun e => proj (emb pk p pk.n (x e))) ∈ M.dom)
    (hG : ∀ x : Fin p → Fin pk.d → ZMod p,
      (∀ g k, chartMap pk (pk.chart g) p pk.n (jet g k x) = 0) →
        ∃ G : (ZMod p)[X], G.degree < (r : WithBot ℕ) ∧
          ∀ e : Fin p, G.eval ((((P.H N : ℤ) - 1 - e : ℤ)) : ZMod p) = low (x e))
    (hcov : CoverPt3 pk M ins low width a jet) :
    HostIdent M.sys pk p width a r := by
  have hpsi : ∀ H J (s : ℤ) (y : Fin pk.n → ZMod p),
      M.sys.prof.psi H J s (proj y) = M.sys.prof.psi H J s (ins y) := by
    intro H J s y
    show digitPhi H s (sourceM (p := p) J) (sourceZ (p := p) J) (M.prof.Gy (proj y))
      (M.prof.Ty (proj y)) (3 / 2) = digitPhi H s (sourceM (p := p) J) (sourceZ (p := p) J)
      (M.prof.Gy (ins y)) (M.prof.Ty (ins y)) (3 / 2)
    rw [hTy, hGy]
  refine
    { jet := jet
      xi := LinearMap.pi fun e => (proj.comp (emb pk p pk.n)).comp (LinearMap.proj e)
      dom := fun x hx => hdom x hx
      inj := fun x hx h => hinj x hx (fun e => by simpa using congrFun h e)
      kill := fun x hx => ?_ }
  obtain ⟨G, hGd, hGe⟩ := hG x hx
  refine ⟨G, hGd, fun j h1 h2 => ?_⟩
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
      obtain ⟨g, k, g', k', hjet, hjet', hv⟩ := hcov j h1 h2 e hd
      exact hv (x e) (by
        have hk := hx g k
        rw [hjet] at hk
        simpa using hk) (by
        have hk := hx g' k'
        rw [hjet'] at hk
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
end CatalanMeasure.GenD.Uniform.W.Charts6
