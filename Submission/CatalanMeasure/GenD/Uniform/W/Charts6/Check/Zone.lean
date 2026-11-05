module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.Check.Psi
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Zones of the cover: a position range read off one stored row (and a killer row)
-/
namespace CatalanMeasure.GenD.Uniform.W.Charts6.Check
open Polynomial Finset Module CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.Parametric CatalanMeasure.GenD.Uniform.W.Charts CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.ZoneZ
open CatalanMeasure.GenD.Uniform.W.Prof (Packet emb chartMap Mx)

/-- A position range `[lo, hi)`: the row `i` of group `g` (psi-row with signs `eps`), the killer rows in group `g2`. -/
structure Zone where
  lo : Aff
  hi : Aff
  g : ℕ
  i : ℕ
  g2 : ℕ
  eps : List ℤ
  kill : List ℕ

def unitRow (n c : ℕ) : List ℤ := (List.range n).map fun k => if k = c then 1 else 0

/-- Every position of `[lo, hi)` is read by a jet of the group `g`. -/
def actOK (m : Meta) (win : List Aff) (cs : Cert) (g : ℕ) (lo hi : Aff) : Bool :=
  match m.pts.getD g Pt.z0 with
  | Pt.z0 => holds win cs (lo.sub (offAff m g)) && holds win cs (((offAff m g).add (wAff m g)).sub hi)
  | Pt.inf => holds win cs (lo.sub ((pAff.sub (offAff m g)).sub (wAff m g))) &&
      holds win cs ((pAff.sub (offAff m g)).sub hi)
  | _ => false

def zoneOK (pk : Packet) (m : Meta) (win : List Aff) (cs : Cert) (Z : ℕ) (AT BT : List (List ℤ)) (J : ℕ) (S : ℤ) (zn : Zone) : Bool :=
  decide (zn.g < m.pts.length) && decide (zn.g2 < m.pts.length) &&
  rowOKg pk m Z AT BT zn.g zn.i J S zn.eps && actOK m win cs zn.g zn.lo zn.hi && actOK m win cs zn.g2 zn.lo zn.hi &&
  (List.range m.ex).all (fun j => decide (j = 0) || decide (zn.eps.getD j 0 = 0) ||
    (decide (zn.kill.getD j 0 < (rowsOf pk zn.g2).length) &&
      decide (rowAt pk (zn.g2, zn.kill.getD j 0) = unitRow pk.n (extraC m j))))

/-- The zones chain: the first starts below `L`, each next starts below the previous end, the last ends above `P`. -/
def chainOK (win : List Aff) (cs : Cert) (L P : Aff) (zs : List Zone) : Bool :=
  (match zs with | [] => false | z :: _ => holds win cs (L.sub z.lo)) &&
  (zs.zip zs.tail).all (fun ab => holds win cs (ab.1.hi.sub ab.2.lo)) &&
  (match zs.getLast? with | none => false | some z => holds win cs (z.hi.sub P))

noncomputable section
variable {p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

theorem cover_zones (rs : List Zone) (E : Aff → ℤ) (P : ℤ) :
    ∀ (L : ℤ), (match rs with | [] => False | r :: _ => E r.lo ≤ L) →
      (∀ ab ∈ rs.zip rs.tail, E ab.2.lo ≤ E ab.1.hi) →
      (match rs.getLast? with | none => False | some r => P ≤ E r.hi) →
      ∀ e : ℤ, L ≤ e → e < P → ∃ rg ∈ rs, E rg.lo ≤ e ∧ e < E rg.hi := by
  induction rs with
  | nil => intro L h; simp at h
  | cons a t ih =>
    intro L hL hch hend e hLe heP
    by_cases hea : e < E a.hi
    · exact ⟨a, List.mem_cons_self, by simp at hL; omega, hea⟩
    · cases t with
      | nil =>
        simp at hend; omega
      | cons b t' =>
        have hab : E b.lo ≤ E a.hi := hch (a, b) (by simp)
        obtain ⟨rg, hrg, h1, h2⟩ := ih (E a.hi) (by simp; exact hab)
          (fun ab hab' => hch ab (by
            simp only [List.zip_cons_cons, List.tail_cons, List.mem_cons]
            right; simpa using hab'))
          (by simpa [List.getLast?_cons_cons] using hend) e (by omega) heP
        exact ⟨rg, List.mem_cons_of_mem _ hrg, h1, h2⟩

theorem chain_sound (win : List Aff) (cs : Cert) {N : ℕ} (hwin : ∀ f ∈ win, 0 ≤ f.eval (N : ℤ) (((p : ℤ) - 1) / 2))
    (L P : Aff) (zs : List Zone) (h : chainOK win cs L P zs = true) (e : ℤ)
    (hL : L.eval (N : ℤ) (((p : ℤ) - 1) / 2) ≤ e) (hP : e < P.eval (N : ℤ) (((p : ℤ) - 1) / 2)) :
    ∃ z ∈ zs, z.lo.eval (N : ℤ) (((p : ℤ) - 1) / 2) ≤ e ∧ e < z.hi.eval (N : ℤ) (((p : ℤ) - 1) / 2) := by
  simp only [chainOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine cover_zones zs (fun a => a.eval (N : ℤ) (((p : ℤ) - 1) / 2)) (P.eval (N : ℤ) (((p : ℤ) - 1) / 2))
    (L.eval (N : ℤ) (((p : ℤ) - 1) / 2)) ?_ ?_ ?_ e hL hP
  · cases hr : zs with
    | nil => rw [hr] at h1; simp at h1
    | cons z t =>
      rw [hr] at h1
      have := holds_sound win cs _ _ _ hwin h1
      rw [Aff.eval_sub] at this
      show z.lo.eval _ _ ≤ _
      omega
  · intro ab hab
    have := holds_sound win cs _ _ _ hwin (h2 ab hab)
    rw [Aff.eval_sub] at this
    show ab.2.lo.eval _ _ ≤ ab.1.hi.eval _ _
    omega
  · cases hr : zs.getLast? with
    | none => rw [hr] at h3; simp at h3
    | some z =>
      rw [hr] at h3
      have := holds_sound win cs _ _ _ hwin h3
      rw [Aff.eval_sub] at this
      show _ ≤ z.hi.eval _ _
      omega


theorem jet0_proj {d : ℕ} (j : ℕ) (e : Fin p) (h : j = e.val) :
    (jet0 j : (Fin p → Fin d → Fp) →ₗ[Fp] (Fin d → Fp)) = LinearMap.proj e := by
  subst h; simp [jet0, e.isLt]

theorem jetInf_proj {d : ℕ} (j : ℕ) (e : Fin p) (h : j = p - 1 - e.val) :
    (jetInf j : (Fin p → Fin d → Fp) →ₗ[Fp] (Fin d → Fp)) = LinearMap.proj e := by
  have hm : j < p := by have := e.isLt; omega
  simp only [jetInf, dif_pos hm]
  congr 1
  exact Fin.ext (by simp only; omega)

theorem act_sound (pk : Packet) (m : Meta) (win : List Aff) (cs : Cert) {N : ℕ}
    (hlen2 : m.pts.length = m.ws.length) (hnn : WdNonneg m (N : ℤ) (((p : ℤ) - 1) / 2))
    (hwin : ∀ f ∈ win, 0 ≤ f.eval (N : ℤ) (((p : ℤ) - 1) / 2)) (hodd : p % 2 = 1)
    (hcm0 : 0 ≤ m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2)) (hcm1 : m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2) ≤ (p : ℤ))
    (g : ℕ) (hg : g < m.pts.length) (lo hi : Aff) (h : actOK m win cs g lo hi = true) (e : Fin p)
    (hlo : lo.eval (N : ℤ) (((p : ℤ) - 1) / 2) ≤ (e.val : ℤ))
    (hhi : (e.val : ℤ) < hi.eval (N : ℤ) (((p : ℤ) - 1) / 2)) :
    ∃ k, k < wdOf m N p g ∧
      (jetG (d := pk.d) m N p g k : (Fin p → Fin pk.d → Fp) →ₗ[Fp] (Fin pk.d → Fp)) = LinearMap.proj e := by
  have hoff := offAff_eval (p := p) m N g hlen2 hnn hodd hcm0 hcm1
  have hw := wAff_eval (p := p) m N g (by omega) hnn
  have hep := e.isLt
  unfold actOK at h
  cases hpt : m.pts.getD g Pt.z0 with
  | m1 => rw [hpt] at h; simp at h
  | p1 => rw [hpt] at h; simp at h
  | z0 =>
    simp only [hpt, Bool.and_eq_true] at h
    have a1 := holds_sound win cs _ _ _ hwin h.1
    have a2 := holds_sound win cs _ _ _ hwin h.2
    rw [Aff.eval_sub, hoff] at a1
    rw [Aff.eval_sub, Aff.eval_add, hoff, hw] at a2
    refine ⟨e.val - grpOff m N p g, by omega, ?_⟩
    have : (jetG (d := pk.d) m N p g (e.val - grpOff m N p g) : (Fin p → Fin pk.d → Fp) →ₗ[Fp] (Fin pk.d → Fp)) =
        jet0 (grpOff m N p g + (e.val - grpOff m N p g)) := by unfold jetG; rw [hpt]
    rw [this]; exact jet0_proj _ e (by omega)
  | inf =>
    simp only [hpt, Bool.and_eq_true] at h
    have a1 := holds_sound win cs _ _ _ hwin h.1
    have a2 := holds_sound win cs _ _ _ hwin h.2
    have hpe : pAff.eval (N : ℤ) (((p : ℤ) - 1) / 2) = (p : ℤ) := by
      simp only [pAff, Aff.eval]; omega
    rw [Aff.eval_sub, Aff.eval_sub, Aff.eval_sub, hpe, hoff, hw] at a1
    rw [Aff.eval_sub, Aff.eval_sub, hpe, hoff] at a2
    refine ⟨p - 1 - e.val - grpOff m N p g, by omega, ?_⟩
    have : (jetG (d := pk.d) m N p g (p - 1 - e.val - grpOff m N p g) : (Fin p → Fin pk.d → Fp) →ₗ[Fp] (Fin pk.d → Fp)) =
        jetInf (grpOff m N p g + (p - 1 - e.val - grpOff m N p g)) := by unfold jetG; rw [hpt]
    rw [this]; exact jetInf_proj _ e (by omega)

theorem chart_rowsum {pk : Packet} (g : ℕ) (hg : g < pk.charts.length) (r : List ℤ)
    (hr : r ∈ (pk.chart ⟨g, hg⟩).rows) (y : Fin pk.d → Fp)
    (hy : chartMap pk (pk.chart ⟨g, hg⟩) p pk.n y = 0) :
    ∑ c : Fin pk.n, ((r.getD c 0 : ℤ) : Fp) * emb pk p pk.n y c = 0 := by
  obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.mp hr
  have := CatalanMeasure.GenD.Uniform.W.Charts4.row_of_chart (K := pk.n) _ hy i hi
  convert this using 2
  rw [Mx, List.getD_eq_getElem _ _ hi, hir]

theorem rowOKg_pre {pk : Packet} {m : Meta} {Z g i J : ℕ} {AT BT : List (List ℤ)} {S : ℤ} {eps : List ℤ}
    (h : rowOKg pk m Z AT BT g i J S eps = true) : 1 ≤ m.ex ∧ i < (rowsOf pk g).length ∧ eps.getD 0 0 = 1 := by
  simp only [rowOKg, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true]
    at h
  obtain ⟨⟨⟨⟨⟨⟨hex1, hi⟩, hneg⟩, hdvd⟩, hex⟩, hslot⟩, hzero⟩ := h
  refine ⟨hex1, hi, ?_⟩
  have h0 := hex 0 (by omega)
  have : (eps.getD 0 0 - 1) * (rowAt pk (g, i)).getD (extraC m 0) 0 = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · omega
  · omega

theorem rowAt_mem {pk : Packet} (g : ℕ) (hg : g < pk.charts.length) (i : ℕ) (hi : i < (rowsOf pk g).length) :
    rowAt pk (g, i) ∈ (pk.chart ⟨g, hg⟩).rows := by
  rw [rowsOf_eq pk g hg]
  unfold rowAt
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _

theorem unitRow_getD (n c k : ℕ) (hk : k < n) : (unitRow n c).getD k 0 = if k = c then 1 else 0 := by
  unfold unitRow
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

theorem unitRow_sum (n c : ℕ) (hc : c < n) (v : Fin n → Fp) :
    ∑ k : Fin n, (((unitRow n c).getD k 0 : ℤ) : Fp) * v k = v ⟨c, hc⟩ := by
  rw [Finset.sum_eq_single ⟨c, hc⟩]
  · rw [unitRow_getD n c c hc]; simp
  · intro k _ hk
    have : k.val ≠ c := fun h => hk (Fin.ext h)
    rw [unitRow_getD n c k k.isLt, if_neg this]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

theorem zone_sound (pk : Packet) (m : Meta) (win : List Aff) (cs : Cert) {N : ℕ}
    (hlen2 : m.pts.length = m.ws.length) (hnn : WdNonneg m (N : ℤ) (((p : ℤ) - 1) / 2))
    (hwin : ∀ f ∈ win, 0 ≤ f.eval (N : ℤ) (((p : ℤ) - 1) / 2)) (hodd : p % 2 = 1)
    (hcm0 : 0 ≤ m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2)) (hcm1 : m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2) ≤ (p : ℤ))
    (hio : iotaOK pk m = true) (hp : 59 < p) {K : ℕ} (hK : K = 4 * m.b + 2 + m.ex)
    (F : Prof p K) (hF : (pdK m.k0 m.b).Realises F)
    {Ub Jb Z : ℕ} (hZ : Z = Zmom Ub Jb) (hZd : (QB ^ 40 : ℤ) % (Z : ℤ) = 0) {AT BT : List (List ℤ)}
    {J : ℕ} {S : ℤ} {H : ℕ} (hJ : J < Jb) (hS : S.toNat + 3 ≤ Ub) (hH : S.toNat + 3 ≤ H)
    (hA : ∀ u < Ub, (AT.getD J []).getD u 0 = qscale (Q.alphaQ u J) Z)
    (hB : ∀ u < Ub, (BT.getD J []).getD u 0 = qscale (Q.betaQ u J) Z)
    (zn : Zone) (hz : zoneOK pk m win cs Z AT BT J S zn = true) (e : Fin p)
    (hlo : zn.lo.eval (N : ℤ) (((p : ℤ) - 1) / 2) ≤ (e.val : ℤ))
    (hhi : (e.val : ℤ) < zn.hi.eval (N : ℤ) (((p : ℤ) - 1) / 2))
    (hg1 : zn.g < pk.charts.length) (hg2 : zn.g2 < pk.charts.length) (hlowc : extraC m 0 < pk.n) :
    (∃ k, k < wdOf m N p zn.g ∧
      (jetG (d := pk.d) m N p zn.g k : (Fin p → Fin pk.d → Fp) →ₗ[Fp] (Fin pk.d → Fp)) = LinearMap.proj e) ∧
    (∃ k, k < wdOf m N p zn.g2 ∧
      (jetG (d := pk.d) m N p zn.g2 k : (Fin p → Fin pk.d → Fp) →ₗ[Fp] (Fin pk.d → Fp)) = LinearMap.proj e) ∧
    ∀ y : Fin pk.d → Fp, chartMap pk (pk.chart ⟨zn.g, hg1⟩) p pk.n y = 0 →
      chartMap pk (pk.chart ⟨zn.g2, hg2⟩) p pk.n y = 0 →
      F.psi H J S (insM m pk.n K (emb pk p pk.n y)) = emb pk p pk.n y ⟨extraC m 0, hlowc⟩ := by
  simp only [zoneOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true]
    at hz
  obtain ⟨⟨⟨⟨⟨hgl, hg2l⟩, hrow⟩, hact1⟩, hact2⟩, hkill⟩ := hz
  refine ⟨act_sound pk m win cs hlen2 hnn hwin hodd hcm0 hcm1 _ hgl _ _ hact1 e hlo hhi,
    act_sound pk m win cs hlen2 hnn hwin hodd hcm0 hcm1 _ hg2l _ _ hact2 e hlo hhi, ?_⟩
  intro y hy1 hy2
  obtain ⟨hex1, hi, heps0⟩ := rowOKg_pre hrow
  have hrs := chart_rowsum zn.g hg1 _ (rowAt_mem zn.g hg1 zn.i hi) y hy1
  have hpsi := psi_row_g pk m hio hp hK F hF hZ hZd hrow hJ hA hB hS hH (emb pk p pk.n y) hrs
  rw [hpsi]
  rw [Finset.sum_eq_single 0]
  · simp only [heps0, yE, dif_pos hlowc]; simp
  · intro j hj hj0
    have hjl := Finset.mem_range.mp hj
    rcases hkill j hjl with (h | h) | h
    · omega
    · rw [h]; simp
    · obtain ⟨hk1, hk2⟩ := h
      have hs := chart_rowsum zn.g2 hg2 _ (rowAt_mem zn.g2 hg2 _ hk1) y hy2
      rw [hk2] at hs
      unfold yE
      by_cases hc : extraC m j < pk.n
      · rw [dif_pos hc]
        have := unitRow_sum pk.n (extraC m j) hc (fun k => emb pk p pk.n y k)
        rw [this] at hs
        rw [hs]; simp
      · rw [dif_neg hc]; simp
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

end
end CatalanMeasure.GenD.Uniform.W.Charts6.Check
