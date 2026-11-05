module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.Check.Roles
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Orders of row polynomials (generic chain lemma applied to the leading groups)
-/
namespace CatalanMeasure.GenD.Uniform.W.Charts6.Check
open Polynomial Finset CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
open CatalanMeasure.GenD.Uniform.W.Prof (Packet emb chartMap Mx)
noncomputable section
variable {p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

/-- Natural total width of the leading groups. -/
def leadWd (pk : Packet) (m : Meta) (N p : ℕ) (pt0 : Pt) (v : List ℤ) : ℕ :=
  ((lead pk m pt0 v).map (wdOf m N p)).sum

theorem lead_info (pk : Packet) (m : Meta) (pt0 : Pt) (v : List ℤ) (hlen : m.pts.length = pk.charts.length)
    (i : ℕ) (hi : i < (lead pk m pt0 v).length) :
    ∃ hg : (lead pk m pt0 v)[i] < pk.charts.length, m.pts.getD (lead pk m pt0 v)[i] Pt.z0 = pt0 ∧
      v ∈ (pk.chart ⟨(lead pk m pt0 v)[i], hg⟩).rows := by
  have hmem : (lead pk m pt0 v)[i] ∈ lead pk m pt0 v := List.getElem_mem hi
  have hL : (lead pk m pt0 v)[i] ∈ ptGroups m pt0 := (lead_prefix pk m pt0 v).subset hmem
  obtain ⟨h1, h2⟩ := ptGroups_mem m pt0 _ hL
  have hg : (lead pk m pt0 v)[i] < pk.charts.length := by omega
  refine ⟨hg, h2, ?_⟩
  rw [rowsOf_eq pk _ hg]
  exact lead_mem_rows pk m pt0 v _ hmem

theorem order_taylor (pk : Packet) (m : Meta) {N : ℕ} (x : Fin p → Fin pk.d → Fp) (hker : JetKerG pk m N x)
    (hlen : m.pts.length = pk.charts.length) (pt0 : Pt) (a : Fp)
    (hpt : pt0 = Pt.p1 ∧ a = 1 ∨ pt0 = Pt.m1 ∧ a = -1) (v : List ℤ) :
    ∀ j < leadWd pk m N p pt0 v, (taylor a (rowPoly (fun e => emb pk p pk.n (x e)) v)).coeff j = 0 := by
  unfold leadWd
  refine chain_list _ _ ?_
  intro i hi k hk
  simp only [List.length_map] at hi
  simp only [List.getElem_map] at hk
  obtain ⟨hg, h2, h3⟩ := lead_info pk m pt0 v hlen i hi
  have := rowpoly_vanish_taylor pk m x hker _ hg a (by rcases hpt with ⟨h, h'⟩ | ⟨h, h'⟩ <;> [left; right] <;> exact ⟨h2.trans h, h'⟩)
    k hk v h3
  have hb0 : baseOff m N p pt0 = 0 := by rcases hpt with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [baseOff, h]
  rwa [grpOff_lead pk m N p pt0 v i hi, hb0, zero_add] at this

theorem order_z0 (pk : Packet) (m : Meta) {N : ℕ} (x : Fin p → Fin pk.d → Fp) (hker : JetKerG pk m N x)
    (hlen : m.pts.length = pk.charts.length) (v : List ℤ) :
    ∀ j < leadWd pk m N p Pt.z0 v, (rowPoly (fun e => emb pk p pk.n (x e)) v).coeff j = 0 := by
  unfold leadWd
  refine chain_list _ _ ?_
  intro i hi k hk
  simp only [List.length_map] at hi
  simp only [List.getElem_map] at hk
  obtain ⟨hg, h2, h3⟩ := lead_info pk m Pt.z0 v hlen i hi
  have := rowpoly_vanish_z0 pk m x hker _ hg h2 k hk v h3
  have hb0 : baseOff m N p Pt.z0 = 0 := by simp [baseOff]
  rwa [grpOff_lead pk m N p Pt.z0 v i hi, hb0, zero_add] at this

theorem order_inf (pk : Packet) (m : Meta) {N : ℕ} (x : Fin p → Fin pk.d → Fp) (hker : JetKerG pk m N x)
    (hlen : m.pts.length = pk.charts.length) (v : List ℤ)
    (hz : ∀ e : Fin p, cmN m N p ≤ e.val → x e = 0) (hcm : cmN m N p ≤ p)
    (hle : (p - cmN m N p) + leadWd pk m N p Pt.inf v ≤ p) :
    ∀ j < (p - cmN m N p) + leadWd pk m N p Pt.inf v,
      (rowPoly (fun e => emb pk p pk.n (x e)) v).coeff (p - 1 - j) = 0 := by
  intro j hj
  by_cases hj0 : j < p - cmN m N p
  · have hjp : p - 1 - j < p := by omega
    rw [rowPoly_coeff]
    refine Finset.sum_eq_zero fun c _ => ?_
    have this : (polx (fun e => emb pk p pk.n (x e)) c).coeff (p - 1 - j) = emb pk p pk.n (x ⟨p - 1 - j, hjp⟩) c :=
      polx_coeff (fun e => emb pk p pk.n (x e)) c ⟨p - 1 - j, hjp⟩
    rw [this, hz ⟨p - 1 - j, hjp⟩ (show cmN m N p ≤ p - 1 - j by omega)]
    simp
  · have hle' := hle
    simp only [leadWd] at hle' hj
    have key := chain_list (fun j' => (rowPoly (fun e => emb pk p pk.n (x e)) v).coeff (p - 1 - ((p - cmN m N p) + j')) = 0)
      ((lead pk m Pt.inf v).map (wdOf m N p)) (by
        intro i hi k hk
        simp only [List.length_map] at hi
        simp only [List.getElem_map] at hk
        obtain ⟨hg, h2, h3⟩ := lead_info pk m Pt.inf v hlen i hi
        have hoff := grpOff_lead pk m N p Pt.inf v i hi
        have hlt : grpOff m N p (lead pk m Pt.inf v)[i] + k < p := by
          have h1 : offs ((lead pk m Pt.inf v).map (wdOf m N p)) i + (wdOf m N p (lead pk m Pt.inf v)[i]) ≤
              ((lead pk m Pt.inf v).map (wdOf m N p)).sum := by
            have := offs_succ ((lead pk m Pt.inf v).map (wdOf m N p)) i (by simpa using hi)
            have h2 : offs ((lead pk m Pt.inf v).map (wdOf m N p)) (i + 1) ≤ ((lead pk m Pt.inf v).map (wdOf m N p)).sum := by
              unfold offs
              exact List.Sublist.sum_le_sum (List.take_sublist _ _) (fun _ _ => Nat.zero_le _)
            simpa [this] using h2
          have hb : baseOff m N p Pt.inf = p - cmN m N p := by simp [baseOff]
          rw [hoff, hb]
          omega
        have := rowpoly_vanish_inf pk m x hker _ hg h2 k hk hlt v h3
        have hb : baseOff m N p Pt.inf = p - cmN m N p := by simp [baseOff]
        rwa [hoff, hb, Nat.add_assoc] at this)
    have := key (j - (p - cmN m N p)) (by omega)
    rwa [show p - cmN m N p + (j - (p - cmN m N p)) = j by omega] at this

end
end CatalanMeasure.GenD.Uniform.W.Charts6.Check
