module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.Check.Geom
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.Check.UnitQ
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Unique146
public import Submission.CatalanMeasure.GenD.Uniform.W.Prof.Count
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Generic unique-graph lemma (`hinj`) by position regions with unit extras systems
-/
namespace CatalanMeasure.GenD.Uniform.W.Charts6.Check
open Polynomial Finset Module CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W.Prof (Packet emb chartMap Mx)

/-- Shape of the insertion list. -/
def iotaOK (pk : Packet) (m : Meta) : Bool :=
  decide (m.iota.length = pk.n) && decide m.iota.Nodup && m.iota.all (fun v => decide (v < 4 * m.b + 2 + m.ex)) &&
  (List.range m.ex).all (fun j => decide (4 * m.b + 2 + j ∈ m.iota))

/-- Packet coordinate of the `j`-th graph coordinate. -/
def extraC (m : Meta) (j : ℕ) : ℕ := m.iota.idxOf (4 * m.b + 2 + j)

/-- `n × n` determinant for `n ≤ 3` on a function of indices. -/
def detSmall {R : Type*} [CommRing R] (n : ℕ) (a : ℕ → ℕ → R) : R :=
  match n with
  | 1 => a 0 0
  | 2 => a 0 0 * a 1 1 - a 0 1 * a 1 0
  | 3 => a 0 0 * a 1 1 * a 2 2 + a 0 1 * a 1 2 * a 2 0 + a 0 2 * a 1 0 * a 2 1
      - a 0 2 * a 1 1 * a 2 0 - a 0 1 * a 1 0 * a 2 2 - a 0 0 * a 1 2 * a 2 1
  | _ => 0

theorem detSmall_cast {R : Type*} [CommRing R] (n : ℕ) (a : ℕ → ℕ → ℤ) :
    detSmall n (fun i j => ((a i j : ℤ) : R)) = ((detSmall n a : ℤ) : R) := by
  unfold detSmall
  split <;> simp

theorem unit_system {R : Type*} [Field R] (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 3) (a : ℕ → ℕ → R)
    (hdet : detSmall n a ≠ 0) (v : ℕ → R) (h : ∀ i, i < n → ∑ j ∈ range n, a i j * v j = 0) :
    ∀ j, j < n → v j = 0 := by
  obtain ⟨h1, h3⟩ := hn
  let M : Matrix (Fin n) (Fin n) R := fun i j => a i j
  have hM : M.det = detSmall n a := by
    interval_cases n
    · rw [Matrix.det_fin_one]; simp [M, detSmall]
    · rw [Matrix.det_fin_two]; simp [M, detSmall]
    · rw [Matrix.det_fin_three]; simp [M, detSmall]; ring
  have hz : M.mulVec (fun j : Fin n => v j) = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, M]
    have := h i i.isLt
    rw [← Fin.sum_univ_eq_sum_range (fun j => a i j * v j) n] at this
    exact this
  have := Matrix.eq_zero_of_mulVec_eq_zero (by rw [hM]; exact hdet) hz
  intro j hj
  exact congrFun this ⟨j, hj⟩


def rowAt (pk : Packet) (gi : ℕ × ℕ) : List ℤ := (rowsOf pk gi.1).getD gi.2 []

/-- Affine offset of a group in its point chain. -/
def offAff (m : Meta) (g : ℕ) : Aff :=
  (if m.pts.getD g Pt.z0 = Pt.inf then pAff.sub m.cm else ⟨0, 0, 0⟩).add
    ((((ptGroups m (m.pts.getD g Pt.z0)).take ((ptGroups m (m.pts.getD g Pt.z0)).idxOf g)).map
      fun g' => m.ws.getD g' ⟨0, 0, 0⟩).foldl Aff.add ⟨0, 0, 0⟩)

def wAff (m : Meta) (g : ℕ) : Aff := m.ws.getD g ⟨0, 0, 0⟩

/-- One position region is admissible: active rows, and a unit system on the graph coordinates. -/
def regionOK (pk : Packet) (m : Meta) (win : List Aff) (cs : Cert) (rg : Region) : Bool :=
  decide (rg.sel.length = m.ex) && decide (1 ≤ m.ex ∧ m.ex ≤ 3) &&
  rg.sel.all (fun gi => decide (gi.2 < (rowsOf pk gi.1).length) && decide (gi.1 < m.pts.length) &&
    (match m.pts.getD gi.1 Pt.z0 with
     | Pt.z0 => holds win cs (rg.lo.sub (offAff m gi.1)) &&
         holds win cs (((offAff m gi.1).add (wAff m gi.1)).sub rg.hi)
     | Pt.inf => holds win cs (rg.lo.sub ((pAff.sub (offAff m gi.1)).sub (wAff m gi.1))) &&
         holds win cs ((pAff.sub (offAff m gi.1)).sub rg.hi)
     | _ => false)) &&
  (let d := detSmall m.ex (fun i j => (rowAt pk (rg.sel.getD i (0, 0))).getD (extraC m j) 0)
   decide (d ≠ 0) && decide ((QB ^ 40 : ℤ) % d = 0))

/-- The regions cover `[0, p)`. -/
def regsCover (m : Meta) (win : List Aff) (cs : Cert) : Bool :=
  (match m.regs with
   | [] => false
   | r :: _ => holds win cs ((⟨0, 0, 0⟩ : Aff).sub r.lo)) &&
  (m.regs.zip m.regs.tail).all (fun ab => holds win cs (ab.1.hi.sub ab.2.lo)) &&
  (match m.regs.getLast? with
   | none => false
   | some r => holds win cs (r.hi.sub m.cm))

def uniqCheck (pk : Packet) (m : Meta) (win : List Aff) (cs : Cert) : Bool :=
  iotaOK pk m && m.regs.all (regionOK pk m win cs) && regsCover m win cs

noncomputable section
variable {p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

theorem emb_jet0_eq (pk : Packet) (x : Fin p → Fin pk.d → Fp) (j : ℕ) (hj : j < p) (c : Fin pk.n) :
    emb pk p pk.n (jet0 j x) c = emb pk p pk.n (x ⟨j, hj⟩) c := by
  rw [emb_jet0, jet0_coord]
  exact polx_coeff (fun e => emb pk p pk.n (x e)) c ⟨j, hj⟩

theorem emb_jetInf_eq (pk : Packet) (x : Fin p → Fin pk.d → Fp) (j : ℕ) (hj : j < p) (c : Fin pk.n) :
    emb pk p pk.n (jetInf j x) c = emb pk p pk.n (x ⟨p - 1 - j, by omega⟩) c := by
  rw [emb_jetInf, jetInf_coord, if_pos hj]
  exact polx_coeff (fun e => emb pk p pk.n (x e)) c ⟨p - 1 - j, by omega⟩

/-- A row of an active group gives a linear relation among the coordinates at the position `e`. -/
theorem rel_at (pk : Packet) (m : Meta) {N : ℕ} (x : Fin p → Fin pk.d → Fp) (hker : JetKerG pk m N x)
    (g : ℕ) (hg : g < pk.charts.length) (r : List ℤ) (hr : r ∈ (pk.chart ⟨g, hg⟩).rows) (e : Fin p) (k : ℕ)
    (hk : k < wdOf m N p g)
    (hact : (m.pts.getD g Pt.z0 = Pt.z0 ∧ grpOff m N p g + k = e.val) ∨
      (m.pts.getD g Pt.z0 = Pt.inf ∧ grpOff m N p g + k = p - 1 - e.val)) :
    ∑ c : Fin pk.n, ((r.getD c 0 : ℤ) : Fp) * emb pk p pk.n (x e) c = 0 := by
  have v := vanish_row pk m x hker g hg k hk r hr
  rcases hact with ⟨hpt, hoff⟩ | ⟨hpt, hoff⟩
  · have hj : jetG (d := pk.d) m N p g k = jet0 (grpOff m N p g + k) := by unfold jetG; rw [hpt]
    have he : (⟨grpOff m N p g + k, by omega⟩ : Fin p) = e := Fin.ext hoff
    rw [hj] at v
    rw [← v]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [emb_jet0_eq pk x _ (by omega) c, he]
  · have hj : jetG (d := pk.d) m N p g k = jetInf (grpOff m N p g + k) := by unfold jetG; rw [hpt]
    have hlt : grpOff m N p g + k < p := by have := e.isLt; omega
    have he : (⟨p - 1 - (grpOff m N p g + k), by omega⟩ : Fin p) = e := Fin.ext (by simp only; omega)
    rw [hj] at v
    rw [← v]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [emb_jetInf_eq pk x _ hlt c, he]


theorem iotaOK_sound (pk : Packet) (m : Meta) (h : iotaOK pk m = true) :
    m.iota.length = pk.n ∧ m.iota.Nodup ∧ (∀ v ∈ m.iota, v < 4 * m.b + 2 + m.ex) ∧
      (∀ j < m.ex, 4 * m.b + 2 + j ∈ m.iota) := by
  simp only [iotaOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem iota_idxOf (m : Meta) (hnd : m.iota.Nodup) (c : ℕ) (hc : c < m.iota.length) :
    m.iota.idxOf m.iota[c] = c := List.get_idxOf hnd ⟨c, hc⟩

theorem pcOf_iota (m : Meta) (hnd : m.iota.Nodup) (c : ℕ) (hc : c < m.iota.length) :
    pcOf m m.iota[c] = some c := by
  unfold pcOf
  rw [if_pos (List.getElem_mem hc), iota_idxOf m hnd c hc]

/-- Vanishing of the slot coordinates. -/
theorem slot_zero (pk : Packet) (m : Meta) (hio : iotaOK pk m = true) {N : ℕ} (hb : bN dsg N p = m.b)
    (x : Fin p → Fin pk.d → Fp)
    (hproj : ∀ e, projExtras (rfl : bN dsg N p * 4 + 2 + m.ex = bN dsg N p * 4 + 2 + m.ex)
      (insM m pk.n (bN dsg N p * 4 + 2 + m.ex) (emb pk p pk.n (x e))) = 0)
    (e : Fin p) (c : ℕ) (hcn : c < pk.n) (hc : m.iota.getD c 0 < 4 * m.b + 2) :
    emb pk p pk.n (x e) ⟨c, hcn⟩ = 0 := by
  obtain ⟨hlen, hnd, hlt, hex⟩ := iotaOK_sound pk m hio
  have hcl : c < m.iota.length := by omega
  have hget : m.iota.getD c 0 = m.iota[c] := List.getD_eq_getElem _ _ hcl
  rw [hget] at hc
  have hv := hlt _ (List.getElem_mem hcl)
  let idx : Fin (bN dsg N p * 4 + 2 + m.ex) := ⟨m.iota[c], by omega⟩
  have h0 := congrFun (hproj e) idx
  rw [projExtras_apply] at h0
  have hne : ¬ isExtra (rfl : bN dsg N p * 4 + 2 + m.ex = bN dsg N p * 4 + 2 + m.ex) idx := by
    rintro ⟨j, hj⟩
    have h := Pilot146O.ck_X_val (rfl : bN dsg N p * 4 + 2 + m.ex = bN dsg N p * 4 + 2 + m.ex) j
    have hc' : idx = (ckEquiv (rfl : bN dsg N p * 4 + 2 + m.ex = bN dsg N p * 4 + 2 + m.ex)).symm
        (Sum.inr (Sum.inr j)) := by rw [← hj]; simp
    have : idx.val = bN dsg N p * 4 + 2 + j.val := by rw [hc']; exact h
    simp only [idx] at this
    omega
  rw [if_neg hne] at h0
  have hins : insM m pk.n (bN dsg N p * 4 + 2 + m.ex) (emb pk p pk.n (x e)) idx = emb pk p pk.n (x e) ⟨c, hcn⟩ := by
    unfold insM
    simp only [LinearMap.pi_apply]
    have : pcOf m idx.val = some c := pcOf_iota m hnd c hcl
    rw [this]
    simp [hcn]
  rw [← hins]; exact h0


theorem extraC_lt (pk : Packet) (m : Meta) (hio : iotaOK pk m = true) (j : ℕ) (hj : j < m.ex) : extraC m j < pk.n := by
  obtain ⟨hlen, hnd, hlt, hex⟩ := iotaOK_sound pk m hio
  have := List.idxOf_lt_length_iff.mpr (hex j hj)
  unfold extraC; omega

theorem extraC_get (pk : Packet) (m : Meta) (hio : iotaOK pk m = true) (j : ℕ) (hj : j < m.ex) :
    m.iota.getD (extraC m j) 0 = 4 * m.b + 2 + j := by
  obtain ⟨hlen, hnd, hlt, hex⟩ := iotaOK_sound pk m hio
  have h1 : extraC m j < m.iota.length := by have := extraC_lt pk m hio j hj; omega
  rw [List.getD_eq_getElem _ _ h1]
  exact List.getElem_idxOf h1

theorem extraC_inj (pk : Packet) (m : Meta) (hio : iotaOK pk m = true) (j1 j2 : ℕ) (h1 : j1 < m.ex) (h2 : j2 < m.ex)
    (h : extraC m j1 = extraC m j2) : j1 = j2 := by
  have a := extraC_get pk m hio j1 h1
  have b := extraC_get pk m hio j2 h2
  rw [h] at a
  omega

/-- The sum over all coordinates reduces to the graph coordinates when the slot coordinates vanish. -/
theorem extras_sum (pk : Packet) (m : Meta) (hio : iotaOK pk m = true) (y : Fin pk.n → Fp) (r : List ℤ)
    (hy : ∀ c : Fin pk.n, m.iota.getD c 0 < 4 * m.b + 2 → y c = 0) :
    ∑ c : Fin pk.n, ((r.getD c 0 : ℤ) : Fp) * y c =
      ∑ j ∈ range m.ex, ((r.getD (extraC m j) 0 : ℤ) : Fp) *
        (if h : extraC m j < pk.n then y ⟨extraC m j, h⟩ else 0) := by
  obtain ⟨hlen, hnd, hlt, hex⟩ := iotaOK_sound pk m hio
  let F : ℕ → Fp := fun c => if h : c < pk.n then ((r.getD c 0 : ℤ) : Fp) * y ⟨c, h⟩ else 0
  have e1 : ∑ c : Fin pk.n, ((r.getD c 0 : ℤ) : Fp) * y c = ∑ c ∈ range pk.n, F c := by
    rw [← Fin.sum_univ_eq_sum_range F pk.n]
    exact Finset.sum_congr rfl fun c _ => by simp [F, c.isLt]
  rw [e1]
  have himg : (range m.ex).image (extraC m) ⊆ range pk.n := by
    intro c hc
    simp only [Finset.mem_image, Finset.mem_range] at hc ⊢
    obtain ⟨j, hj, rfl⟩ := hc
    exact extraC_lt pk m hio j hj
  rw [← Finset.sum_subset himg ?_]
  · rw [Finset.sum_image (fun j1 h1 j2 h2 h => extraC_inj pk m hio j1 j2 (Finset.mem_range.mp h1) (Finset.mem_range.mp h2) h)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := extraC_lt pk m hio j (Finset.mem_range.mp hj)
    simp [F, this]
  · intro c hc hnot
    have hcn : c < pk.n := Finset.mem_range.mp hc
    simp only [F, dif_pos hcn]
    by_cases hslot : m.iota.getD c 0 < 4 * m.b + 2
    · rw [hy ⟨c, hcn⟩ hslot, mul_zero]
    · exfalso
      apply hnot
      have hcl : c < m.iota.length := by omega
      have hv := hlt _ (List.getElem_mem hcl)
      rw [List.getD_eq_getElem _ _ hcl] at hslot
      simp only [Finset.mem_image, Finset.mem_range]
      refine ⟨m.iota[c] - (4 * m.b + 2), by omega, ?_⟩
      unfold extraC
      rw [show 4 * m.b + 2 + (m.iota[c] - (4 * m.b + 2)) = m.iota[c] by omega]
      exact iota_idxOf m hnd c hcl


theorem offAff_eval (m : Meta) (N : ℕ) (g : ℕ) (hlen2 : m.pts.length = m.ws.length)
    (hnn : WdNonneg m (N : ℤ) (((p : ℤ) - 1) / 2)) (hodd : p % 2 = 1)
    (hcm0 : 0 ≤ m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2)) (hcm1 : m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2) ≤ (p : ℤ)) :
    (offAff m g).eval (N : ℤ) (((p : ℤ) - 1) / 2) = (grpOff m N p g : ℤ) := by
  have hsum : ((((ptGroups m (m.pts.getD g Pt.z0)).take ((ptGroups m (m.pts.getD g Pt.z0)).idxOf g)).map
      fun g' => m.ws.getD g' ⟨0, 0, 0⟩).foldl Aff.add ⟨0, 0, 0⟩).eval (N : ℤ) (((p : ℤ) - 1) / 2) =
      (((((ptGroups m (m.pts.getD g Pt.z0)).take ((ptGroups m (m.pts.getD g Pt.z0)).idxOf g)).map
        (wdOf m N p)).sum : ℕ) : ℤ) := by
    apply sum_eval_list m N p hnn
    intro g' hg'
    have h1 := List.mem_of_mem_take hg'
    have := (ptGroups_mem m _ g' h1).1
    omega
  have hpe : pAff.eval (N : ℤ) (((p : ℤ) - 1) / 2) = (p : ℤ) := by simp only [pAff, Aff.eval]; omega
  have hcmN : (cmN m N p : ℤ) = m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2) := by
    unfold cmN; exact Int.toNat_of_nonneg hcm0
  unfold offAff grpOff baseOff
  rw [Aff.eval_add, hsum]
  push_cast
  by_cases hinf : m.pts.getD g Pt.z0 = Pt.inf
  · simp only [hinf, if_true, Aff.eval_sub, hpe]
    rw [Nat.cast_sub (by omega), hcmN]
  · simp only [hinf, if_false]
    simp [Aff.eval]

theorem wAff_eval (m : Meta) (N g : ℕ) (hg : g < m.ws.length)
    (hnn : WdNonneg m (N : ℤ) (((p : ℤ) - 1) / 2)) :
    (wAff m g).eval (N : ℤ) (((p : ℤ) - 1) / 2) = (wdOf m N p g : ℤ) := by
  unfold wAff wdOf
  rw [Int.toNat_of_nonneg (hnn g hg)]

theorem cover_regions (rs : List Region) (E : Aff → ℤ) (P : ℤ) :
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


theorem region_zero (pk : Packet) (m : Meta) (win : List Aff) (cs : Cert) {N : ℕ} (x : Fin p → Fin pk.d → Fp)
    (C : Ctx pk m win N x) (h59 : 59 < p) (hio : iotaOK pk m = true) (rg : Region)
    (hok : regionOK pk m win cs rg = true) (e : Fin p)
    (hlo : rg.lo.eval (N : ℤ) (((p : ℤ) - 1) / 2) ≤ (e.val : ℤ)) (hhi : (e.val : ℤ) < rg.hi.eval (N : ℤ) (((p : ℤ) - 1) / 2))
    (hy : ∀ c : Fin pk.n, m.iota.getD c 0 < 4 * m.b + 2 → emb pk p pk.n (x e) c = 0) :
    ∀ j < m.ex, (if h : extraC m j < pk.n then emb pk p pk.n (x e) ⟨extraC m j, h⟩ else 0) = 0 := by
  simp only [regionOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨hsl, hex13⟩, hall⟩, hdet, hdvd⟩ := hok
  have hdet' := hdet
  set d := detSmall m.ex (fun i j => (rowAt pk (rg.sel.getD i (0, 0))).getD (extraC m j) 0) with hd
  have hdu : ((d : ℤ) : Fp) ≠ 0 := unit_of_dvdQ d (Int.dvd_of_emod_eq_zero hdvd) h59
  let v : ℕ → Fp := fun j => if h : extraC m j < pk.n then emb pk p pk.n (x e) ⟨extraC m j, h⟩ else 0
  have hsys : ∀ i, i < m.ex → ∑ j ∈ range m.ex, ((((rowAt pk (rg.sel.getD i (0, 0))).getD (extraC m j) 0 : ℤ)) : Fp) * v j = 0 := by
    intro i hi
    have hmem : rg.sel.getD i (0, 0) ∈ rg.sel := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    obtain ⟨⟨hrow, hg⟩, hact⟩ := hall _ hmem
    set gi := rg.sel.getD i (0, 0) with hgi
    have hgc : gi.1 < pk.charts.length := by rw [← C.hlen]; exact hg
    have hrowm : rowAt pk gi ∈ (pk.chart ⟨gi.1, hgc⟩).rows := by
      rw [rowsOf_eq pk gi.1 hgc]
      unfold rowAt
      rw [List.getD_eq_getElem _ _ hrow]; exact List.getElem_mem _
    have hnnw : gi.1 < m.ws.length := by rw [← C.hlen2]; exact hg
    have hoff := offAff_eval (p := p) m N gi.1 C.hlen2 C.hnn C.hodd C.hcm0 C.hcm1
    have hw := wAff_eval (p := p) m N gi.1 hnnw C.hnn
    have hrel : ∑ c : Fin pk.n, ((((rowAt pk gi).getD c 0 : ℤ)) : Fp) * emb pk p pk.n (x e) c = 0 := by
      cases hpt : m.pts.getD gi.1 Pt.z0 with
      | m1 => rw [hpt] at hact; simp at hact
      | p1 => rw [hpt] at hact; simp at hact
      | z0 =>
        simp only [hpt, Bool.and_eq_true] at hact
        have a1 := holds_sound win cs _ _ _ C.hwin hact.1
        have a2 := holds_sound win cs _ _ _ C.hwin hact.2
        rw [Aff.eval_sub, hoff] at a1
        rw [Aff.eval_sub, Aff.eval_add, hoff, hw] at a2
        exact rel_at pk m x C.hker gi.1 hgc _ hrowm e (e.val - grpOff m N p gi.1) (by omega)
          (Or.inl ⟨hpt, by omega⟩)
      | inf =>
        simp only [hpt, Bool.and_eq_true] at hact
        have a1 := holds_sound win cs _ _ _ C.hwin hact.1
        have a2 := holds_sound win cs _ _ _ C.hwin hact.2
        have hpe : pAff.eval (N : ℤ) (((p : ℤ) - 1) / 2) = (p : ℤ) := by
          simp only [pAff, Aff.eval]; have := C.hodd; omega
        rw [Aff.eval_sub, Aff.eval_sub, Aff.eval_sub, hpe, hoff, hw] at a1
        rw [Aff.eval_sub, Aff.eval_sub, hpe, hoff] at a2
        have hep := e.isLt
        exact rel_at pk m x C.hker gi.1 hgc _ hrowm e (p - 1 - e.val - grpOff m N p gi.1) (by omega)
          (Or.inr ⟨hpt, by omega⟩)
    rw [extras_sum pk m hio _ _ hy] at hrel
    exact hrel
  have := unit_system (R := Fp) m.ex hex13 (fun i j => ((((rowAt pk (rg.sel.getD i (0, 0))).getD (extraC m j) 0 : ℤ)) : Fp))
    (by rw [detSmall_cast, ← hd]; exact hdu) v hsys
  intro j hj
  exact this j hj


theorem regs_cover_sound (m : Meta) (win : List Aff) (cs : Cert) {N : ℕ} (hwin : ∀ f ∈ win, 0 ≤ f.eval (N : ℤ) (((p : ℤ) - 1) / 2))
    (hodd : p % 2 = 1) (h : regsCover m win cs = true) (e : Fin p)
    (he : (e.val : ℤ) < m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2)) :
    ∃ rg ∈ m.regs, rg.lo.eval (N : ℤ) (((p : ℤ) - 1) / 2) ≤ (e.val : ℤ) ∧
      (e.val : ℤ) < rg.hi.eval (N : ℤ) (((p : ℤ) - 1) / 2) := by
  simp only [regsCover, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hpe : pAff.eval (N : ℤ) (((p : ℤ) - 1) / 2) = (p : ℤ) := by
    simp only [pAff, Aff.eval]; omega
  refine cover_regions m.regs (fun a => a.eval (N : ℤ) (((p : ℤ) - 1) / 2)) (m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2)) 0
    ?_ ?_ ?_ e.val (by omega) he
  · cases hr : m.regs with
    | nil => rw [hr] at h1; simp at h1
    | cons r t =>
      rw [hr] at h1
      have := holds_sound win cs _ _ _ hwin h1
      rw [Aff.eval_sub] at this
      simp only [Aff.eval] at this ⊢
      omega
  · intro ab hab
    have := holds_sound win cs _ _ _ hwin (h2 ab hab)
    rw [Aff.eval_sub] at this
    show ab.2.lo.eval _ _ ≤ ab.1.hi.eval _ _ 
    omega
  · cases hr : m.regs.getLast? with
    | none => rw [hr] at h3; simp at h3
    | some r =>
      rw [hr] at h3
      have := holds_sound win cs _ _ _ hwin h3
      rw [Aff.eval_sub] at this
      show _ ≤ r.hi.eval _ _
      omega

theorem hinj_sound (pk : Packet) (m : Meta) (win : List Aff) (cs : Cert) {N : ℕ} (x : Fin p → Fin pk.d → Fp)
    (C : Ctx pk m win N x) (h59 : 59 < p) (hu : uniqCheck pk m win cs = true) (hb : bN dsg N p = m.b)
    (hproj : ∀ e, projExtras (rfl : bN dsg N p * 4 + 2 + m.ex = bN dsg N p * 4 + 2 + m.ex)
      (insM m pk.n (bN dsg N p * 4 + 2 + m.ex) (emb pk p pk.n (x e))) = 0)
    (hS : pk.Sound) (hpD : ¬ (p : ℤ) ∣ pk.delta) : x = 0 := by
  simp only [uniqCheck, Bool.and_eq_true, List.all_eq_true] at hu
  obtain ⟨⟨hio, hregs⟩, hcov⟩ := hu
  obtain ⟨hlen, hnd, hlt, hex⟩ := iotaOK_sound pk m hio
  funext e
  by_cases hem : cmN m N p ≤ e.val
  · rw [Pi.zero_apply]; exact C.hz e hem
  have hcmN : (cmN m N p : ℤ) = m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2) := by
    unfold cmN; exact Int.toNat_of_nonneg C.hcm0
  have he : (e.val : ℤ) < m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2) := by
    rw [← hcmN]; exact_mod_cast not_le.mp hem
  apply CatalanMeasure.GenD.Uniform.W.Prof.emb_injective hS (rfl : pk.n = pk.n) hpD
  rw [Pi.zero_apply, map_zero]
  obtain ⟨rg, hrg, hlo, hhi⟩ := regs_cover_sound m win cs C.hwin C.hodd hcov e he
  have hy : ∀ c : Fin pk.n, m.iota.getD c 0 < 4 * m.b + 2 → emb pk p pk.n (x e) c = 0 :=
    fun c hc => slot_zero pk m hio hb x hproj e c.val c.isLt hc
  have hz := region_zero pk m win cs x C h59 hio rg (hregs rg hrg) e hlo hhi hy
  funext c
  by_cases hc : m.iota.getD c 0 < 4 * m.b + 2
  · exact hy c hc
  · have hcl : c.val < m.iota.length := by omega
    have hget : m.iota.getD c 0 = m.iota[c.val] := List.getD_eq_getElem _ _ hcl
    have hv := hlt _ (List.getElem_mem hcl)
    rw [hget] at hc
    have hj : m.iota[c.val] - (4 * m.b + 2) < m.ex := by omega
    have hz' := hz _ hj
    have hec : extraC m (m.iota[c.val] - (4 * m.b + 2)) = c.val := by
      unfold extraC
      have : 4 * m.b + 2 + (m.iota[c.val] - (4 * m.b + 2)) = m.iota[c.val] := by omega
      rw [this]; exact iota_idxOf m hnd c.val hcl
    rw [dif_pos (by rw [hec]; exact c.isLt)] at hz'
    have : (⟨extraC m (m.iota[c.val] - (4 * m.b + 2)), by rw [hec]; exact c.isLt⟩ : Fin pk.n) = c := Fin.ext hec
    rw [this] at hz'
    simpa using hz'

end
end CatalanMeasure.GenD.Uniform.W.Charts6.Check
