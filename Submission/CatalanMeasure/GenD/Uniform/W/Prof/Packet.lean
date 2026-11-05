module
public import Submission.CatalanMeasure.GenD.Uniform.W.Prof.Check
@[expose] public section
set_option Elab.async false

/-!
# Packets: stored Lemma C data and the integer soundness theorem

`Packet.check` is the single `Bool` computed by the kernel for a stored packet;
`Packet.check_sound` extracts the integer identities `Packet.Sound` (no primes involved).
The exception integer is `Packet.D`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Prof
open Finset
noncomputable section

/-- One chart `B_j` with its kernel certificate in `V`-coordinates. -/
structure Chart where
  /-- integerised chart rows (`m × n`) -/
  rows : List (List ℤ)
  /-- rank bound `r_j` -/
  r : ℕ
  /-- `d - r` kernel vectors in `V`-coordinates -/
  ker : List (List ℤ)
  qpiv : List ℕ
  qadj : List (List ℤ)
  qdelta : ℤ

/-- A stored packet: saturated basis `v` (`d × n`), pivot/adjugate data and charts. -/
structure Packet where
  n : ℕ
  d : ℕ
  v : List (List ℤ)
  piv : List ℕ
  adj : List (List ℤ)
  delta : ℤ
  charts : List Chart

def Chart.check (n d : ℕ) (v : List (List ℤ)) (c : Chart) : Bool :=
  (c.ker.length + c.r == d) && indOK c.ker d c.qpiv c.qadj c.qdelta && kerOK v n d c.ker c.rows

def Packet.check (pk : Packet) : Bool :=
  shape pk.v pk.d pk.n && indOK pk.v pk.n pk.piv pk.adj pk.delta &&
    pk.charts.all (Chart.check pk.n pk.d pk.v)

/-- The head of the check (basis `v` and its independence certificate). -/
def Packet.checkHead (pk : Packet) : Bool :=
  shape pk.v pk.d pk.n && indOK pk.v pk.n pk.piv pk.adj pk.delta

/-- The check splits into the head and one independent check per chart (one kernel
declaration each). -/
theorem Packet.check_of_parts {pk : Packet} (h1 : pk.checkHead = true)
    (h2 : ∀ c ∈ pk.charts, c.check pk.n pk.d pk.v = true) : pk.check = true := by
  simp only [Packet.check, Packet.checkHead, Bool.and_eq_true, List.all_eq_true] at h1 ⊢
  exact ⟨h1, h2⟩

/-- The single exception integer: `p ∤ D` suffices for all conclusions. -/
def Packet.D (pk : Packet) : ℤ := pk.delta * (pk.charts.map Chart.qdelta).prod

theorem kerOK_shape {V : List (List ℤ)} {n d : ℕ} {K B : List (List ℤ)}
    (h : kerOK V n d K B = true) : ∀ b ∈ B, b.length = n := by
  simp only [kerOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨_, _⟩, h3⟩, _⟩ := h
  exact fun b hb => by simpa using h3 b hb

/-- Integer content of a chart certificate. -/
structure Chart.Sound (n d : ℕ) (v : List (List ℤ)) (c : Chart) : Prop where
  rank : c.ker.length + c.r = d
  kerw : ∀ k ∈ c.ker, k.length = d
  qlt : ∀ i < c.ker.length, c.qpiv.getD i 0 < d
  qind : ∀ a b, a < c.ker.length → b < c.ker.length →
    ∑ i ∈ range c.ker.length, Mx c.qadj a i * Mx c.ker b (c.qpiv.getD i 0) =
      if a = b then c.qdelta else 0
  roww : ∀ b ∈ c.rows, b.length = n
  kill : ∀ i r, i < c.ker.length → r < c.rows.length →
    ∑ x ∈ range n, Mx c.rows r x * (∑ a ∈ range d, Mx c.ker i a * Mx v a x) = 0

theorem Chart.check_sound {n d : ℕ} {v : List (List ℤ)} {c : Chart}
    (h : c.check n d v = true) : c.Sound n d v := by
  simp only [Chart.check, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨hw, hl, hi⟩ := indOK_sound h2
  exact ⟨h1, hw, hl, hi, kerOK_shape h3, kerOK_sound h3⟩

/-- Integer content of a packet certificate. -/
structure Packet.Sound (pk : Packet) : Prop where
  vlen : pk.v.length = pk.d
  vwid : ∀ r ∈ pk.v, r.length = pk.n
  pivlt : ∀ i < pk.d, pk.piv.getD i 0 < pk.n
  vind : ∀ a b, a < pk.d → b < pk.d →
    ∑ i ∈ range pk.d, Mx pk.adj a i * Mx pk.v b (pk.piv.getD i 0) =
      if a = b then pk.delta else 0
  chart : ∀ c ∈ pk.charts, c.Sound pk.n pk.d pk.v

theorem Packet.check_sound {pk : Packet} (h : pk.check = true) : pk.Sound := by
  simp only [Packet.check, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨hl, hw⟩ := shape_sound h1
  obtain ⟨_, hlt, hind⟩ := indOK_sound h2
  refine ⟨hl, hw, fun i hi => hlt i (by omega), fun a b ha hb => ?_, fun c hc => ?_⟩
  · have := hind a b (by omega) (by omega)
    rw [hl] at this
    exact this
  · exact Chart.check_sound (h3 c hc)

end
end CatalanMeasure.GenD.Uniform.W.Prof
