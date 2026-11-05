module
public import Submission.CatalanMeasure.GenD.Uniform.W.Prof.Slot
public import Submission.CatalanMeasure.GenD.Uniform.W.Lucas.PStep
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts3.PStepPoly
@[expose] public section
set_option Elab.async false

/-!
# The four-point prefix host: a count over the joint jet kernel (any `q`)

`W/Prof` identifies a packet with a slot system by `Ident`, which demands that **every** product
atom `x ↦ (emb x_d)_d` lies in `S.dom` (the same `V` in every slot, `dom` for all `x`).  For mixed
slot systems this forces `V = 0` (`W/Charts2/NoGo`).  The stored bank packets live in a different
frame: atoms are `Poly_{<p} ⊗ V` (`m` polynomial coordinates with values in the constant profile
space `V`), the slot-space membership is imposed as **jets** at the points `-1, 1, ∞`, and the
response windows are jets at `0`; all of them are charged `Σ_j w_j rank(B_j|V)` (cumulative flags).

`HostIdent` is the identification in that frame.  Only the *joint kernel* `K = ker Φ` of all jets is
asked to map into `dom`, injectively, with vanishing (`p`-step) response:

* `jet g k : (Fin m → V) →ₗ V` : the `k`-th jet of group `g` (any linear map: Taylor coefficient at a
  point, a coefficient at `∞`, a window row);  `B_g` is the stored chart of the packet;
* `xi : (Fin m → V) →ₗ (Fin S.D → Fin S.K → F_p)` : the atom map, **arbitrary** linear (typed per slot
  block when the system is mixed); nothing is asked of it off `K`;
* `dom`, `inj`, `kill` : on `K` only.

`host_count` : `m·d - Σ_g width_g · r_g ≤ ν(N,p)` for every prime `p ∤ pk.D` and **every** `q`
(the kill hypothesis is the `a`-fold `p`-difference of `SlotSystem.resp`, `a = ⌊q/p⌋`; for `q < p`
this is the plain response).  `NullityLB.ofPacketHost` / `packet_winCert_host` are the analogues of
`ofPacketWindow` / `packet_winCert` without the restriction `q < p`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts3
open Finset Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Lucas
  CatalanCore.Uniform.Content
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The atoms `Poly_{<p} ⊗ V` of the packet, as `m` coordinates with values in `V = F_p^d`. -/
abbrev Atoms (pk : Packet) (p m : ℕ) : Type := Fin m → (Fin pk.d → ZMod p)

/-- **Host identification** (four-point prefix frame), see the module comment.  `a` is the `p`-step
quotient `⌊q/p⌋`. -/
structure HostIdent (S : SlotSystem P N p) (pk : Packet) (m : ℕ)
    (width : Fin pk.charts.length → ℕ) (a r : ℕ) where
  /-- the jets: Taylor coefficients at `-1, 0, 1`, coefficients at `∞`, window rows -/
  jet : ∀ g, Fin (width g) → Atoms pk p m →ₗ[ZMod p] (Fin pk.d → ZMod p)
  /-- the atom map into the slot coordinates (arbitrary linear) -/
  xi : Atoms pk p m →ₗ[ZMod p] (Fin S.D → Fin S.K → ZMod p)
  /-- on the jet kernel, atoms lie in the slot domain -/
  dom : ∀ x, (∀ g k, chartMap pk (pk.chart g) p pk.n (jet g k x) = 0) → xi x ∈ S.dom
  /-- on the jet kernel, `xi` is injective -/
  inj : ∀ x, (∀ g k, chartMap pk (pk.chart g) p pk.n (jet g k x) = 0) → xi x = 0 → x = 0
  /-- on the jet kernel, the `a`-fold `p`-difference of the slot response is a polynomial `G` of
  degree `< r` in `j` (`q = a p + r`; `G = 0` is the plain kill, a nonzero `G` is the `B`-graph) -/
  kill : ∀ x, (∀ g k, chartMap pk (pk.chart g) p pk.n (jet g k x) = 0) →
    ∃ G : (ZMod p)[X], G.degree < (r : WithBot ℕ) ∧
    ∀ j, P.b N ≤ j → j + a * p < P.L N → ∑ v ∈ range (a + 1),
      ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) * S.resp (j / p + v) (j % p) (xi x) =
        G.eval (j : ZMod p)

/-- **Host count.**  For every `q = a p + r`, `m·d - Σ_g width_g r_g ≤ ν(N,p)`. -/
theorem host_count (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (S : SlotSystem P N p) {pk : Packet} (hS : pk.Sound) (hpD : ¬ (p : ℤ) ∣ pk.D)
    {m : ℕ} {width : Fin pk.charts.length → ℕ} {a r : ℕ} (hq : P.q N = a * p + r)
    (I : HostIdent S pk m width a r) :
    m * pk.d - ∑ g, width g * (pk.chart g).r ≤ nullity P N p := by
  let V := Fin pk.d → ZMod p
  let B : ∀ g : Fin pk.charts.length, V →ₗ[ZMod p] (Fin (pk.chart g).rows.length → ZMod p) :=
    fun g => chartMap pk (pk.chart g) p pk.n
  let Φ := constraintMap width B I.jet
  have hker : ∀ x : Atoms pk p m, Φ x = 0 ↔ ∀ g k, chartMap pk (pk.chart g) p pk.n (I.jet g k x) = 0 :=
    fun x => constraintMap_eq_zero_iff width B I.jet x
  let ξ' : LinearMap.ker Φ →ₗ[ZMod p] (Fin S.D → Fin S.K → ZMod p) := I.xi.comp (LinearMap.ker Φ).subtype
  have h := slot_nullity_pstep_poly S hP hN hp2 hH hq ξ'
    (fun u => I.dom u.1 ((hker u.1).mp u.2))
    (by
      intro u v huv
      refine Subtype.ext (sub_eq_zero.mp ?_)
      refine I.inj (u.1 - v.1) ?_ ?_
      · intro g k
        have := (hker (u.1 - v.1)).mp (Submodule.sub_mem _ u.2 v.2) g k
        exact this
      · simpa [ξ', map_sub, sub_eq_zero] using huv)
    (0 : LinearMap.ker Φ →ₗ[ZMod p] LinearMap.ker Φ)
    (fun u _ => I.kill u.1 ((hker u.1).mp u.2))
  have hr0 : finrank (ZMod p) (LinearMap.range (0 : LinearMap.ker Φ →ₗ[ZMod p] LinearMap.ker Φ)) = 0 := by
    simp
  rw [hr0] at h
  have hrk : finrank (ZMod p) (LinearMap.range Φ) ≤ ∑ g, width g * finrank (ZMod p) (LinearMap.range (B g)) :=
    rank_constraintMap_le (m := m) width B I.jet
  have hb : ∑ g, width g * finrank (ZMod p) (LinearMap.range (B g)) ≤
      ∑ g, width g * (pk.chart g).r := Finset.sum_le_sum fun g _ =>
    Nat.mul_le_mul_left _ (finrank_chartMap_le hS (hS.chart _ (List.get_mem _ _)) rfl
      (not_dvd_qdelta hpD g))
  have hrn := Φ.finrank_range_add_finrank_ker
  have hd : finrank (ZMod p) (Fin m → V) = m * pk.d := by
    simp [V, Module.finrank_pi_fintype]
  rw [hd] at hrn
  show m * pk.d - ∑ g, width g * (pk.chart g).r ≤ nullity P N p
  omega

/-! ### The constructor without `q < p` -/

/-- Window predicate of the host constructor: the window and `p ∤ D` (no restriction on `q`). -/
def HostApp (pk : Packet) (Win : ℕ → ℕ → Prop) (N p : ℕ) : Prop :=
  Win N p ∧ ¬ (p : ℤ) ∣ pk.D

/-- Physical hypothesis of the host frame: a slot system and a host identification at every window
point (with the `p`-step quotient `a = ⌊q/p⌋`). -/
def PhysHost (P : Parameters) (pk : Packet) (Win : ℕ → ℕ → Prop) (c : ℕ → ℕ → ℕ)
    (w : Fin pk.charts.length → ℕ → ℕ → ℕ) : Prop :=
  ∀ N p : ℕ, 0 < N → ∀ hp : p.Prime, p ≠ 2 → P.H N < p ^ 2 → HostApp pk Win N p →
    haveI : Fact p.Prime := ⟨hp⟩
    ∃ S : SlotSystem P N p, Nonempty (HostIdent S pk (c N p) (fun g => w g N p) (P.q N / p) (P.q N % p))

/-- **The generic constructor, any `q`.** -/
def NullityLB.ofPacketHost (hP : Admissible P) (pk : Packet) (hS : pk.Sound)
    (Win : ℕ → ℕ → Prop) (c : ℕ → ℕ → ℕ) (w : Fin pk.charts.length → ℕ → ℕ → ℕ)
    (phys : PhysHost P pk Win c w) : NullityLB P :=
  NullityLB.ofWindow P (HostApp pk Win) (packetVal pk c w)
    (fun N p hN hp hp2 hH hApp => by
      obtain ⟨S, ⟨I⟩⟩ := phys N p hN hp hp2 hH hApp
      have : Fact p.Prime := ⟨hp⟩
      have hq : P.q N = P.q N / p * p + P.q N % p := by
        rw [mul_comm]; exact (Nat.div_add_mod _ _).symm
      exact host_count hP hN hp2 hH S hS hApp.2 hq I)

theorem ofPacketHost_kap (hP : Admissible P) (pk : Packet) (hS : pk.Sound)
    (Win : ℕ → ℕ → Prop) (c : ℕ → ℕ → ℕ) (w : Fin pk.charts.length → ℕ → ℕ → ℕ)
    (phys : PhysHost P pk Win c w) {N p : ℕ} (h : HostApp pk Win N p) :
    (NullityLB.ofPacketHost hP pk hS Win c w phys).kap N p = packetVal pk c w N p := by
  simp [NullityLB.ofPacketHost, NullityLB.ofWindow, h]

/-- The exception condition is automatic for large primes. -/
theorem hostApp_of_large (pk : Packet) (hD : pk.D ≠ 0) {Win : ℕ → ℕ → Prop} {N p : ℕ}
    (hW : Win N p) (hp : pk.D.natAbs < p) : HostApp pk Win N p :=
  ⟨hW, not_dvd_of_gt hD hp⟩

end
end CatalanMeasure.GenD.Uniform.W.Charts3
