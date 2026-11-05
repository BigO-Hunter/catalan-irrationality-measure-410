module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.Check.Cover
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.Check.Graph
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.Check.HdomGen
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# `checkHost` and its soundness: the generic packet host
-/
namespace CatalanMeasure.GenD.Uniform.W.Charts6.Check
open Polynomial Finset Module CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.Parametric CatalanMeasure.GenD.Uniform.W.Charts CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.W.Prof (Packet emb chartMap Mx not_dvd_delta)

/-- The coordinate-kind identification is the expected one. -/
def ckOK (b ex : ℕ) : Bool :=
  decide (∀ k : Fin (b * 4 + 2 + ex), ckEquiv (rfl : b * 4 + 2 + ex = b * 4 + 2 + ex) k = ckOfB b ex k)

/-- The data of a packet host. -/
structure PData where
  m : Meta
  cs : Cert
  cd : CovData
  ztop : Bool := false

def winOf (m : Meta) : List Aff :=
  winHyps m.win.1 m.win.2.1 m.win.2.2.1 m.win.2.2.2.1 m.win.2.2.2.2

def checkHost (pk : Packet) (pd : PData) : Bool :=
  decide (pd.m.pts.length = pk.charts.length) && decide (pd.m.pts.length = pd.m.ws.length) &&
  decide (1 ≤ pd.m.ex) && pd.m.ws.all (fun f => holds (winOf pd.m) pd.cs f) &&
  holds (winOf pd.m) pd.cs ⟨0, 2, -59⟩ && holds (winOf pd.m) pd.cs pd.m.cm &&
  holds (winOf pd.m) pd.cs (pAff.sub pd.m.cm) &&
  geomCheck pd.m (winOf pd.m) pd.cs && hdomCheckG pk pd.m (winOf pd.m) pd.cs pd.ztop &&
  uniqCheck pk pd.m (winOf pd.m) pd.cs &&
  tOK pk pd.m (winOf pd.m) pd.cs Pt.p1 [(1, 4 * pd.m.b + 2)] (pAff.sub rA) &&
  coverCheck pk pd.m (winOf pd.m) pd.cs pd.cd && ckOK pd.m.b pd.m.ex

theorem checkHost_of_parts (pk : Packet) (pd : PData)
    (h1 : decide (pd.m.pts.length = pk.charts.length) = true) (h2 : decide (pd.m.pts.length = pd.m.ws.length) = true)
    (h3 : decide (1 ≤ pd.m.ex) = true) (h4 : pd.m.ws.all (fun f => holds (winOf pd.m) pd.cs f) = true)
    (h5 : holds (winOf pd.m) pd.cs ⟨0, 2, -59⟩ = true) (h6 : holds (winOf pd.m) pd.cs pd.m.cm = true)
    (h7 : holds (winOf pd.m) pd.cs (pAff.sub pd.m.cm) = true) (h8 : geomCheck pd.m (winOf pd.m) pd.cs = true)
    (h9 : hdomCheckG pk pd.m (winOf pd.m) pd.cs pd.ztop = true) (h10 : uniqCheck pk pd.m (winOf pd.m) pd.cs = true)
    (h11 : tOK pk pd.m (winOf pd.m) pd.cs Pt.p1 [(1, 4 * pd.m.b + 2)] (pAff.sub rA) = true)
    (h12 : coverCheck pk pd.m (winOf pd.m) pd.cs pd.cd = true) (h13 : ckOK pd.m.b pd.m.ex = true) :
    checkHost pk pd = true := by
  unfold checkHost
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, Bool.and_self]

noncomputable section
variable {p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

theorem monoProfile_realisesK {N : ℕ} (m : Meta) (hk0 : k0N dsg N p = m.k0) (hb : bN dsg N p = m.b)
    (hdiv : dsg.h N / p = 0) (hck : ckOK m.b m.ex = true) {K : ℕ} (hK : K = bN dsg N p * 4 + 2 + m.ex) :
    (pdK m.k0 m.b).Realises (monoProfile dsg N p hK) := by
  have hck' : ∀ k : Fin (m.b * 4 + 2 + m.ex),
      ckEquiv (rfl : m.b * 4 + 2 + m.ex = m.b * 4 + 2 + m.ex) k = ckOfB m.b m.ex k := by
    simpa [ckOK] using hck
  have h0 := realises_absK (p := p) (k0 := m.k0) hb hK hck'
  unfold monoProfile
  rw [hk0, hdiv]
  exact h0


/-- The window of the packet data. -/
def inWin (m : Meta) (N p : ℕ) : Prop :=
  m.win.1 ≤ N ∧ m.win.2.1 * N < m.win.2.2.1 * p ∧ m.win.2.2.2.1 * p ≤ m.win.2.2.2.2 * N ∧ p % 2 = 1

set_option maxHeartbeats 2000000 in
/-- **The generic packet host at one point.** -/
theorem host_pt (pk : Packet) (pd : PData) (hS : pk.Sound) (N p : ℕ) (hN0 : 0 < N) [hpf : Fact p.Prime]
    (hp2 : p ≠ 2) (hpD : ¬ (p : ℤ) ∣ pk.D) (hin : inWin pd.m N p) (hcheck : checkHost pk pd = true) :
    ∃ S : SlotSystem dsg N p, Nonempty (HostIdent S pk (cmN pd.m N p) (fun g => wdOf pd.m N p g.val)
      (dsg.q N / p) (dsg.q N % p)) := by
  obtain ⟨hN, h1, h2, hodd⟩ := hin
  have hwin : ∀ f ∈ winOf pd.m, 0 ≤ f.eval (N : ℤ) (((p : ℤ) - 1) / 2) :=
    winHyps_sound _ _ _ _ _ N p hN h1 h2 hodd
  simp only [checkHost, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hcheck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlen, hlen2⟩, hex1⟩, hwsAll⟩, h59c⟩, hcmc0⟩, hcmc1⟩, hgeom⟩, hdomC⟩, huniq⟩, hgraph⟩, hcover⟩, hck⟩ := hcheck
  have hnn : WdNonneg pd.m (N : ℤ) (((p : ℤ) - 1) / 2) := fun g hg =>
    holds_sound _ _ _ _ _ hwin (hwsAll _ (by rw [List.getD_eq_getElem _ _ hg]; exact List.getElem_mem hg))
  obtain ⟨hN', hk0, hk1, hb, hrN, hja, hrho⟩ := geom_sound pd.m (winOf pd.m) pd.cs N p hodd hwin hN hgeom
  have hio : iotaOK pk pd.m = true := by
    simp only [uniqCheck, Bool.and_eq_true] at huniq; exact huniq.1.1
  have hn : 1 ≤ dsg.n N := by show 1 ≤ 58 * N; omega
  have h59 : 59 < p := by
    have := holds_sound _ _ _ _ _ hwin h59c
    simp only [Aff.eval] at this; omega
  have hcm0 : 0 ≤ pd.m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2) := holds_sound _ _ _ _ _ hwin hcmc0
  have hcm1 : pd.m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2) ≤ (p : ℤ) := by
    have := holds_sound _ _ _ _ _ hwin hcmc1
    rw [Aff.eval_sub] at this
    have hpe0 : pAff.eval (N : ℤ) (((p : ℤ) - 1) / 2) = (p : ℤ) := by simp only [pAff, Aff.eval]; omega
    rw [hpe0] at this; omega
  have hcmN : cmN pd.m N p ≤ p := by
    have : (cmN pd.m N p : ℤ) = pd.m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2) := by
      unfold cmN; exact Int.toNat_of_nonneg hcm0
    omega
  have h3N : 3 * N < p := by
    have h3 : dsg.h N = 3 * N := rfl
    have := Nat.mod_lt (dsg.h N) (Fact.out : p.Prime).pos
    rw [hrN] at this; exact this
  have hdiv : dsg.h N / p = 0 := Nat.div_eq_of_lt (by show 3 * N < p; exact h3N)
  have hqdiv : dsg.q N / p = 0 := Nat.div_eq_of_lt (by show 3 * N < p; exact h3N)
  have hqmod : dsg.q N % p = 3 * N := Nat.mod_eq_of_lt (by show 3 * N < p; exact h3N)
  let K := bN dsg N p * 4 + 2 + pd.m.ex
  let M : MonoData dsg N p K := monoData hp2 hn rfl
  have hM : (pdK pd.m.k0 pd.m.b).Realises M.prof := monoProfile_realisesK pd.m hk0 hb hdiv hck rfl
  have hlowc := extraC_lt pk pd.m hio 0 hex1
  have mkCtx : ∀ x : Fin p → Fin pk.d → ZMod p, JetKerG pk pd.m N x → (∀ e : Fin p, cmN pd.m N p ≤ e.val → x e = 0) →
      Ctx pk pd.m (winOf pd.m) N x :=
    fun x hker hz => ⟨hker, hlen, hlen2, hnn, hwin, hodd, hz, hcm0, hcm1⟩
  have hpc : pcOf pd.m (4 * pd.m.b + 2) = some (extraC pd.m 0) := by
    obtain ⟨_, _, _, hexi⟩ := iotaOK_sound pk pd.m hio
    have hmem := hexi 0 hex1
    have : 4 * pd.m.b + 2 ∈ pd.m.iota := by simpa using hmem
    unfold pcOf extraC
    rw [if_pos this]
  have hpe : pAff.eval (N : ℤ) (((p : ℤ) - 1) / 2) = (p : ℤ) := by
    simp only [pAff, Aff.eval]; omega
  refine ⟨M.sys, ⟨?_⟩⟩
  exact monoHost3t (width := fun g => wdOf pd.m N p g.val) M (insM pd.m pk.n K)
    ((projExtras (rfl : K = bN dsg N p * 4 + 2 + pd.m.ex)).comp (insM pd.m pk.n K))
    (fun y => sumProf_proj rfl _ (fun j => rfl) (insM pd.m pk.n K y))
    (fun y => sumProf_proj rfl _ (fun j => rfl) (insM pd.m pk.n K y))
    (lowF pk pd.m hlowc) (dsg.q N / p) (dsg.q N % p) (cmN pd.m N p) (fun g k => jetG (d := pk.d) pd.m N p g.val k.val)
    (fun x hz hker hproj => hinj_sound pk pd.m (winOf pd.m) pd.cs x (mkCtx x hker hz) h59 huniq hb hproj hS
      (not_dvd_delta hpD))
    (fun x hz hker => by
      obtain ⟨cc, hcc⟩ := hdom_sound_gen pk pd.m (winOf pd.m) pd.cs pd.ztop x (mkCtx x hker hz) hp2 hN0 hn hb hrN hja hrho hdomC
      exact ⟨cc, hcc⟩)
    (fun x hz hker => by
      obtain ⟨G, hGd, hGe⟩ := hG_sound (mkCtx x hker hz) (4 * pd.m.b + 2) (extraC pd.m 0) hpc hlowc
        (pAff.sub rA) (dsg.q N % p) (by omega) hgraph
        (by rw [Aff.eval_sub, hpe]; simp only [rA, Aff.eval]; omega)
        (((dsg.H N : ℤ) - 1 : ℤ) : ZMod p)
      refine ⟨G, hGd, fun e => ?_⟩
      have := hGe e
      show _ = emb pk p pk.n (x e) ⟨extraC pd.m 0, hlowc⟩
      rw [← this]
      congr 1
      push_cast
      ring)
    hcmN (by
      rw [hqdiv]
      exact cover_sound pk pd.m (winOf pd.m) pd.cs pd.cd hlen hlen2 hnn hwin hodd hcm0 hcm1 hio hex1 (by omega) M hM hcover)


/-- **The generic packet host**, from checked data on a finite list of sub-windows. -/
theorem physHost_of_checks (pk : Packet) (pds : List PData) (hS : pk.Sound) (Win : ℕ → ℕ → Prop)
    (c : ℕ → ℕ → ℕ) (w : Fin pk.charts.length → ℕ → ℕ → ℕ)
    (hWin : ∀ N p, Win N p → ∃ pd ∈ pds, inWin pd.m N p)
    (hc : ∀ pd ∈ pds, ∀ N p, p % 2 = 1 → c N p = cmN pd.m N p)
    (hw : ∀ pd ∈ pds, ∀ (g : Fin pk.charts.length) N p, w g N p = wdOf pd.m N p g.val)
    (hcheck : ∀ pd ∈ pds, checkHost pk pd = true) : PhysHost dsg pk Win c w := by
  intro N p hN0 hp hp2 hH hApp
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hWn, hpD⟩ := hApp
  obtain ⟨pd, hpd, hin⟩ := hWin N p hWn
  rw [hc pd hpd N p hin.2.2.2]
  have hwfun : (fun g : Fin pk.charts.length => w g N p) = fun g => wdOf pd.m N p g.val :=
    funext fun g => hw pd hpd g N p
  rw [hwfun]
  exact host_pt pk pd hS N p hN0 hp2 hpD hin (hcheck pd hpd)

/-- **The generic packet host.** -/
theorem physHost_of_check (pk : Packet) (pd : PData) (hS : pk.Sound) (Win : ℕ → ℕ → Prop) (c : ℕ → ℕ → ℕ)
    (w : Fin pk.charts.length → ℕ → ℕ → ℕ)
    (hWin : ∀ N p, Win N p → inWin pd.m N p)
    (hc : ∀ N p, p % 2 = 1 → c N p = cmN pd.m N p)
    (hw : ∀ (g : Fin pk.charts.length) N p, w g N p = wdOf pd.m N p g.val)
    (hcheck : checkHost pk pd = true) : PhysHost dsg pk Win c w :=
  physHost_of_checks pk [pd] hS Win c w (fun N p h => ⟨pd, List.mem_singleton_self _, hWin N p h⟩)
    (fun pd' hpd' => by rw [List.mem_singleton.mp hpd']; exact hc)
    (fun pd' hpd' => by rw [List.mem_singleton.mp hpd']; exact hw)
    (fun pd' hpd' => by rw [List.mem_singleton.mp hpd']; exact hcheck)

end
end CatalanMeasure.GenD.Uniform.W.Charts6.Check
