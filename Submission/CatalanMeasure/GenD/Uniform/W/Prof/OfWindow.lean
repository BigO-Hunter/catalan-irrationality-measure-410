module
public import Submission.CatalanMeasure.GenD.Uniform.W.Prof.Count
public import Submission.CatalanMeasure.GenD.Uniform.W.Combine
@[expose] public section
set_option Elab.async false

/-!
# The design-generic `NullityLB` constructor for stored packets

* `prof_count` : for a slot system `S` with chart identification `I` and a checked packet,
  `S.D · d - Σ_j width_j · r_j ≤ ν(N,p)` for every prime `p ∤ pk.D`;
* `NullityLB.ofPacketWindow` : the `NullityLB` (via `NullityLB.ofWindow`) whose value is
  `c(N,p) · d - Σ_j w_j(N,p) · r_j` on the window
  `Win N p ∧ q < p ∧ p ∤ pk.D`.  `q < p` is the restriction `a_q = 0` (Lucas case excluded).
* `ofPacketWindow_kap` / `ofPacketWindow_ge` : the value is attained whenever the three
  window conditions hold (this is the shape consumed by `WinCert` / `gate_of_families_windows`);
* `app_of_large` : the exception condition `p ∤ D` holds automatically for `p > |D|`.

Everything about the tiling enters only through the hypothesis `phys` (the existence of a slot
system and a chart identification at every window point).
-/

namespace CatalanMeasure.GenD.Uniform.W.Prof
open Finset Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Slots
  CatalanCore.Uniform.Content
noncomputable section

variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- **Packet count** (Theorem W-prof with stored Lemma C ranks). -/
theorem prof_count (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (S : SlotSystem P N p) {pk : Packet} (hS : pk.Sound) (hpD : ¬ (p : ℤ) ∣ pk.D)
    {width : Fin pk.charts.length → ℕ} (I : Ident S pk width) :
    S.D * pk.d - ∑ g, width g * (pk.chart g).r ≤ nullity P N p := by
  let V := Fin pk.d → ZMod p
  let B : ∀ g : Fin pk.charts.length, V →ₗ[ZMod p] (Fin (pk.chart g).rows.length → ZMod p) :=
    fun g => chartMap pk (pk.chart g) p S.K
  let Φ := constraintMap width B (fun g k => I.jet S g k)
  have hemb : Function.Injective (emb pk p S.K) :=
    emb_injective hS I.hK (not_dvd_delta hpD)
  have hξi : Function.Injective (I.xi S) := by
    intro x y hxy
    funext d'
    exact hemb (congrFun hxy d')
  have h := S.slot_nullity_raw hP hN hp2 hH (I.xi S) (fun x => I.dom x) hξi Φ (by
    intro a ha j h1 h2
    rw [constraintMap_eq_zero_iff] at ha
    exact I.resp_zero S a ha j h1 h2)
  have hr : finrank (ZMod p) (LinearMap.range Φ) ≤
      ∑ g, width g * finrank (ZMod p) (LinearMap.range (B g)) :=
    rank_constraintMap_le (m := S.D) width B (fun g k => I.jet S g k)
  have hb : ∑ g, width g * finrank (ZMod p) (LinearMap.range (B g)) ≤
      ∑ g, width g * (pk.chart g).r := Finset.sum_le_sum fun g _ =>
    Nat.mul_le_mul_left _ (finrank_chartMap_le hS (hS.chart _ (List.get_mem _ _)) I.hK
      (not_dvd_qdelta hpD g))
  have hd : finrank (ZMod p) (Fin S.D → V) = S.D * pk.d := by
    simp [V, Module.finrank_pi_fintype]
  rw [hd] at h
  show S.D * pk.d - ∑ g, width g * (pk.chart g).r ≤ nullity P N p
  omega

/-- The window predicate of the constructor: window, `a_q = 0`, and `p ∤ D`. -/
def PacketApp (P : Parameters) (pk : Packet) (Win : ℕ → ℕ → Prop) (N p : ℕ) : Prop :=
  Win N p ∧ P.q N < p ∧ ¬ (p : ℤ) ∣ pk.D

/-- The value `c d - Σ_j w_j r_j`. -/
def packetVal (pk : Packet) (c : ℕ → ℕ → ℕ) (w : Fin pk.charts.length → ℕ → ℕ → ℕ)
    (N p : ℕ) : ℕ :=
  c N p * pk.d - ∑ g, w g N p * (pk.chart g).r

/-- Physical hypothesis: a slot system and a chart identification at every window point. -/
def PhysWindow (P : Parameters) (pk : Packet) (Win : ℕ → ℕ → Prop) (c : ℕ → ℕ → ℕ)
    (w : Fin pk.charts.length → ℕ → ℕ → ℕ) : Prop :=
  ∀ N p : ℕ, 0 < N → ∀ hp : p.Prime, p ≠ 2 → P.H N < p ^ 2 → PacketApp P pk Win N p →
    haveI : Fact p.Prime := ⟨hp⟩
    ∃ S : SlotSystem P N p, S.D = c N p ∧ Nonempty (Ident S pk (fun g => w g N p))

/-- **The generic constructor.**  Given an admissible design, a checked packet, a window with
affine weights and the chart identification, `ν ≥ c d - Σ w_j r_j` on the window. -/
def NullityLB.ofPacketWindow (hP : Admissible P) (pk : Packet) (hS : pk.Sound)
    (Win : ℕ → ℕ → Prop) (c : ℕ → ℕ → ℕ) (w : Fin pk.charts.length → ℕ → ℕ → ℕ)
    (phys : PhysWindow P pk Win c w) : NullityLB P :=
  NullityLB.ofWindow P (PacketApp P pk Win) (packetVal pk c w)
    (fun N p hN hp hp2 hH hApp => by
      obtain ⟨S, hD, ⟨I⟩⟩ := phys N p hN hp hp2 hH hApp
      have : Fact p.Prime := ⟨hp⟩
      have := prof_count hP hN hp2 hH S hS hApp.2.2 I
      rw [hD] at this
      exact this)

theorem ofPacketWindow_kap (hP : Admissible P) (pk : Packet) (hS : pk.Sound)
    (Win : ℕ → ℕ → Prop) (c : ℕ → ℕ → ℕ) (w : Fin pk.charts.length → ℕ → ℕ → ℕ)
    (phys : PhysWindow P pk Win c w) {N p : ℕ} (h : PacketApp P pk Win N p) :
    (NullityLB.ofPacketWindow hP pk hS Win c w phys).kap N p = packetVal pk c w N p := by
  simp [NullityLB.ofPacketWindow, NullityLB.ofWindow, h]

/-- The exception condition is automatic for large primes. -/
theorem not_dvd_of_gt {D : ℤ} (hD : D ≠ 0) {p : ℕ} (hp : D.natAbs < p) : ¬ (p : ℤ) ∣ D := by
  intro h
  have h1 : (p : ℤ).natAbs ∣ D.natAbs := Int.natAbs_dvd_natAbs.mpr h
  simp only [Int.natAbs_natCast] at h1
  exact absurd (Nat.le_of_dvd (Int.natAbs_pos.mpr hD) h1) (by omega)

/-- For `p` above `|D|`, `a_q = 0`, and the window, the window predicate holds. -/
theorem packetApp_of_large (pk : Packet) (hD : pk.D ≠ 0) {Win : ℕ → ℕ → Prop} {N p : ℕ}
    (hW : Win N p) (hq : P.q N < p) (hp : pk.D.natAbs < p) : PacketApp P pk Win N p :=
  ⟨hW, hq, not_dvd_of_gt hD hp⟩

end
end CatalanMeasure.GenD.Uniform.W.Prof
