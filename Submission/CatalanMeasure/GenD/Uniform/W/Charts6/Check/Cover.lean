module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.Check.Zone
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.Check.MonoT
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# The generic cover (`CoverPt3`) from zone data
-/
namespace CatalanMeasure.GenD.Uniform.W.Charts6.Check
open Polynomial Finset Module CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.Parametric CatalanMeasure.GenD.Uniform.W.Charts CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.ZoneZ
open CatalanMeasure.GenD.Uniform.W.Prof (Packet emb chartMap Mx)

/-- Cover data: the window rank of `H - 1` in units of `p`, the first `J`, the zones for each `J` and each side,
and the position bounds `(lo, hi)` used for each side. -/
structure CovData where
  S0 : ℕ
  Jlo : ℕ
  Z : ℕ
  hiZ : List (List Zone)
  loZ : List (List Zone)
  hiB : List (Aff × Aff)
  loB : List (Aff × Aff)
  /-- the scaled moments `qscale α(u,J) Z`, `qscale β(u,J) Z` (tables, checked once) -/
  AT : List (List ℤ) := []
  BT : List (List ℤ) := []

/-- `T = H - S0 p`. -/
def tAff (S0 : ℕ) : Aff := ⟨78, -2 * (S0 : ℤ), -(S0 : ℤ)⟩

/-- One side of the cover: bounds, then zones chained over the bounds, or an empty range. -/
def sideOK (pk : Packet) (m : Meta) (win : List Aff) (cs : Cert) (Z : ℕ) (AT BT : List (List ℤ)) (J : ℕ) (S : ℤ) (L0 Lc P0 Pc : Aff)
    (b : Aff × Aff) (zs : List Zone) : Bool :=
  decide (b.1 = L0 ∨ b.1 = Lc) && decide (b.2 = P0 ∨ b.2 = Pc ∨ b.2 = m.cm) &&
  ((zs.all (zoneOK pk m win cs Z AT BT J S) && chainOK win cs b.1 b.2 zs) ||
    (decide (zs = []) && holds win cs (b.1.sub b.2)))

/-- The valid extra position bounds, for `J`: `e ≥ T - 70N + J p` and `e < T - 9N + J p` on the high side. -/
def hiLc (S0 J : ℕ) : Aff := ⟨8, 2 * ((J : ℤ) - S0), (J : ℤ) - S0⟩
def hiPc (S0 J : ℕ) : Aff := ⟨69, 2 * ((J : ℤ) - S0), (J : ℤ) - S0⟩
def loLc (S0 J : ℕ) : Aff := ⟨8, 2 * ((J : ℤ) - S0) + 2, (J : ℤ) - S0 + 1⟩
def loPc (S0 J : ℕ) : Aff := ⟨69, 2 * ((J : ℤ) - S0) + 2, (J : ℤ) - S0 + 1⟩

/-- The tables of scaled moments are correct. -/
def tabOK (Z Ub Jlo Jb : ℕ) (AT BT : List (List ℤ)) : Bool :=
  (List.range Jb).all (fun J => decide (J < Jlo) || (List.range Ub).all (fun u =>
    decide ((AT.getD J []).getD u 0 = qscale (Q.alphaQ u J) Z) &&
      decide ((BT.getD J []).getD u 0 = qscale (Q.betaQ u J) Z)))

theorem tabOK_sound {Z Ub Jlo Jb : ℕ} {AT BT : List (List ℤ)} (h : tabOK Z Ub Jlo Jb AT BT = true) (J : ℕ)
    (hJ : Jlo ≤ J) (hJb : J < Jb) :
    (∀ u < Ub, (AT.getD J []).getD u 0 = qscale (Q.alphaQ u J) Z) ∧
      (∀ u < Ub, (BT.getD J []).getD u 0 = qscale (Q.betaQ u J) Z) := by
  simp only [tabOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
  rcases h J hJb with h1 | h2
  · omega
  · exact ⟨fun u hu => (h2 u hu).1, fun u hu => (h2 u hu).2⟩

def coverScalar (pk : Packet) (m : Meta) (win : List Aff) (cs : Cert) (cd : CovData) : Bool :=
  decide (1 ≤ cd.S0) && decide (cd.loZ.length = cd.hiZ.length) &&
  decide (cd.Z = Zmom (cd.S0 + 3) (cd.Jlo + cd.hiZ.length)) &&
  decide ((QB ^ 40 : ℤ) % (cd.Z : ℤ) = 0) &&
  tabOK cd.Z (cd.S0 + 3) cd.Jlo (cd.Jlo + cd.hiZ.length) cd.AT cd.BT &&
  holds win cs ⟨78, -2 * (cd.S0 : ℤ), -(cd.S0 : ℤ) - 1⟩ &&
  holds win cs ⟨-78, 2 * ((cd.S0 : ℤ) + 1), (cd.S0 : ℤ) + 1⟩ &&
  holds win cs ⟨9, -2 * (cd.Jlo : ℤ), -(cd.Jlo : ℤ)⟩ &&
  holds win cs ⟨-70, 2 * ((cd.Jlo + cd.hiZ.length : ℕ) : ℤ), ((cd.Jlo + cd.hiZ.length : ℕ) : ℤ)⟩ &&
  holds win cs ⟨78, 0, -((cd.S0 : ℤ) + 3)⟩ && holds win cs ⟨0, 2, -59⟩

/-- Both sides of the cover for the `t`-th `J`. -/
def sidesAt (pk : Packet) (m : Meta) (win : List Aff) (cs : Cert) (cd : CovData) (t : ℕ) : Bool :=
  sideOK pk m win cs cd.Z cd.AT cd.BT (cd.Jlo + t) (cd.S0 : ℤ) ⟨0, 0, 0⟩ (hiLc cd.S0 (cd.Jlo + t)) (tAff cd.S0)
    (hiPc cd.S0 (cd.Jlo + t)) (cd.hiB.getD t (⟨0, 0, 0⟩, tAff cd.S0)) (cd.hiZ.getD t []) &&
  sideOK pk m win cs cd.Z cd.AT cd.BT (cd.Jlo + t) ((cd.S0 : ℤ) - 1) (tAff cd.S0) (loLc cd.S0 (cd.Jlo + t)) pAff
    (loPc cd.S0 (cd.Jlo + t)) (cd.loB.getD t (tAff cd.S0, pAff)) (cd.loZ.getD t [])

def coverCheck (pk : Packet) (m : Meta) (win : List Aff) (cs : Cert) (cd : CovData) : Bool :=
  coverScalar pk m win cs cd && (List.range cd.hiZ.length).all (sidesAt pk m win cs cd)

/-- Chunks `(start, length)` of a range are contiguous from `a` to `n`. -/
def contig : ℕ → ℕ → List (ℕ × ℕ) → Bool
  | a, n, [] => decide (a = n)
  | a, n, (s, k) :: rest => decide (s = a) && contig (a + k) n rest

def chunksOK (f : ℕ → Bool) (chk : List (ℕ × ℕ)) : Bool := chk.all fun ab => (List.range' ab.1 ab.2).all f

theorem forall_of_chunks (f : ℕ → Bool) : ∀ (chk : List (ℕ × ℕ)) (a n : ℕ), contig a n chk = true →
    chunksOK f chk = true → ∀ t, a ≤ t → t < n → f t = true := by
  intro chk
  induction chk with
  | nil => intro a n h1 h2 t h3 h4; simp [contig] at h1; omega
  | cons ab rest ih =>
    intro a n h1 h2 t h3 h4
    obtain ⟨s, k⟩ := ab
    simp only [contig, Bool.and_eq_true, decide_eq_true_eq] at h1
    simp only [chunksOK, List.all_cons, Bool.and_eq_true] at h2
    by_cases ht : t < a + k
    · have h5 := h2.1
      rw [List.all_eq_true] at h5
      exact h5 t (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    · exact ih (a + k) n h1.2 h2.2 t (by omega) h4

theorem coverCheck_of_chunks (pk : Packet) (m : Meta) (win : List Aff) (cs : Cert) (cd : CovData)
    (hsc : coverScalar pk m win cs cd = true) (chk : List (ℕ × ℕ)) (hc : contig 0 cd.hiZ.length chk = true)
    (hk : chunksOK (sidesAt pk m win cs cd) chk = true) : coverCheck pk m win cs cd = true := by
  unfold coverCheck
  rw [hsc, Bool.true_and, List.all_eq_true]
  intro t ht
  exact forall_of_chunks _ chk 0 _ hc hk t (Nat.zero_le _) (List.mem_range.mp ht)

theorem zoneOK_lt {pk : Packet} {m : Meta} {win : List Aff} {cs : Cert} {Z J : ℕ} {AT BT : List (List ℤ)} {S : ℤ} {zn : Zone}
    (h : zoneOK pk m win cs Z AT BT J S zn = true) : zn.g < m.pts.length ∧ zn.g2 < m.pts.length := by
  simp only [zoneOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1

noncomputable section
variable {p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

/-- The graph functional: the coordinate of the first extra. -/
def lowF (pk : Packet) (m : Meta) (h : extraC m 0 < pk.n) : (Fin pk.d → Fp) →ₗ[Fp] Fp :=
  (LinearMap.proj (⟨extraC m 0, h⟩ : Fin pk.n)).comp (emb pk p pk.n)


theorem side_sound (pk : Packet) (m : Meta) (win : List Aff) (cs : Cert) {N : ℕ}
    (hwin : ∀ f ∈ win, 0 ≤ f.eval (N : ℤ) (((p : ℤ) - 1) / 2)) (Z : ℕ) (AT BT : List (List ℤ)) (J : ℕ) (S : ℤ) (L0 Lc P0 Pc : Aff)
    (b : Aff × Aff) (zs : List Zone) (h : sideOK pk m win cs Z AT BT J S L0 Lc P0 Pc b zs = true) (e : ℤ)
    (hL0 : L0.eval (N : ℤ) (((p : ℤ) - 1) / 2) ≤ e) (hLc : Lc.eval (N : ℤ) (((p : ℤ) - 1) / 2) ≤ e)
    (hP0 : e < P0.eval (N : ℤ) (((p : ℤ) - 1) / 2)) (hPc : e < Pc.eval (N : ℤ) (((p : ℤ) - 1) / 2))
    (hCm : e < m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2)) :
    ∃ z ∈ zs, z.lo.eval (N : ℤ) (((p : ℤ) - 1) / 2) ≤ e ∧ e < z.hi.eval (N : ℤ) (((p : ℤ) - 1) / 2) ∧
      zoneOK pk m win cs Z AT BT J S z = true := by
  simp only [sideOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hl, hu⟩, hz⟩ := h
  have hlow : b.1.eval (N : ℤ) (((p : ℤ) - 1) / 2) ≤ e := by
    rcases hl with h | h <;> rw [h] <;> assumption
  have hup : e < b.2.eval (N : ℤ) (((p : ℤ) - 1) / 2) := by
    rcases hu with h | h | h <;> rw [h] <;> assumption
  rcases hz with ⟨hzs, hch⟩ | ⟨hnil, hvoid⟩
  · obtain ⟨z, hzm, h1, h2⟩ := chain_sound win cs hwin b.1 b.2 zs hch e hlow hup
    exact ⟨z, hzm, h1, h2, hzs z hzm⟩
  · exfalso
    have := holds_sound win cs _ _ _ hwin hvoid
    rw [Aff.eval_sub] at this
    linarith

theorem key_mul (P h' q : ℤ) (hpz : P = 2 * h' + 1) : q * P = 2 * q * h' + q := by subst hpz; ring

theorem dsg_b (N : ℕ) : dsg.b N = 9 * N := by
  simp [Parameters.b, Parameters.C, Parameters.L, Parameters.n, Parameters.q,
    Parameters.g, Parameters.h, CatalanMeasure.GenD.D58.Odd.design]; try ring

set_option maxHeartbeats 2000000 in
theorem cover_sound (pk : Packet) (m : Meta) (win : List Aff) (cs : Cert) (cd : CovData) {N : ℕ}
    (hlen : m.pts.length = pk.charts.length) (hlen2 : m.pts.length = m.ws.length)
    (hnn : WdNonneg m (N : ℤ) (((p : ℤ) - 1) / 2)) (hwin : ∀ f ∈ win, 0 ≤ f.eval (N : ℤ) (((p : ℤ) - 1) / 2))
    (hodd : p % 2 = 1) (hcm0 : 0 ≤ m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2))
    (hcm1 : m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2) ≤ (p : ℤ))
    (hio : iotaOK pk m = true) (hex1 : 1 ≤ m.ex) {K : ℕ} (hK : K = 4 * m.b + 2 + m.ex)
    (M : MonoData dsg N p K) (hF : (pdK m.k0 m.b).Realises M.sys.prof) (hc : coverCheck pk m win cs cd = true) :
    CoverPt3t pk M (insM m pk.n K) (lowF pk m (extraC_lt pk m hio 0 hex1)) (fun g => wdOf m N p g)
      0 (cmN m N p) (fun g k => jetG (d := pk.d) m N p g k) := by
  have hlowc := extraC_lt pk m hio 0 hex1
  simp only [coverCheck, coverScalar, sidesAt, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hS1, hlenlo⟩, hZe⟩, hZd⟩, htab⟩, w1⟩, w2⟩, w3⟩, w4⟩, w5⟩, w6⟩, hall⟩ := hc
  have hpz : (p : ℤ) = 2 * (((p : ℤ) - 1) / 2) + 1 := by omega
  have e1 := holds_sound win cs _ _ _ hwin w1
  have e2 := holds_sound win cs _ _ _ hwin w2
  have e3 := holds_sound win cs _ _ _ hwin w3
  have e4 := holds_sound win cs _ _ _ hwin w4
  have e5 := holds_sound win cs _ _ _ hwin w5
  have e6 := holds_sound win cs _ _ _ hwin w6
  simp only [Aff.eval] at e1 e2 e3 e4 e5 e6
  have F1 : (cd.S0 : ℤ) * p + 1 ≤ 78 * N := by
    have k := key_mul (p : ℤ) (((p : ℤ) - 1) / 2) cd.S0 hpz; linarith
  have F2 : 78 * (N : ℤ) ≤ ((cd.S0 : ℤ) + 1) * p := by
    have k := key_mul (p : ℤ) (((p : ℤ) - 1) / 2) ((cd.S0 : ℤ) + 1) hpz; linarith
  have F3 : (cd.Jlo : ℤ) * p ≤ 9 * N := by
    have k := key_mul (p : ℤ) (((p : ℤ) - 1) / 2) cd.Jlo hpz; linarith
  have F4 : 70 * (N : ℤ) ≤ ((cd.Jlo + cd.hiZ.length : ℕ) : ℤ) * p := by
    have k := key_mul (p : ℤ) (((p : ℤ) - 1) / 2) ((cd.Jlo + cd.hiZ.length : ℕ) : ℤ) hpz; linarith
  have F5 : (cd.S0 : ℤ) + 3 ≤ 78 * N := by linarith
  have hp59 : 59 < p := by omega
  have hp0 : 0 < p := by omega
  have hp0z : (p : ℤ) ≠ 0 := by omega
  unfold CoverPt3t
  intro j hj1 hj2 e hem hdiv
  have hcmN : (cmN m N p : ℤ) = m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2) := by
    unfold cmN; exact Int.toNat_of_nonneg hcm0
  have hecm : (e.val : ℤ) < m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2) := by
    rw [← hcmN]; exact_mod_cast hem
  rw [dsg_b] at hj1
  rw [CatalanMeasure.GenD.D58.Odd.design_L] at hj2
  have hHN := CatalanMeasure.GenD.D58.Odd.design_H N
  have hHz : (dsg.H N : ℤ) = 78 * N := by rw [hHN]; push_cast; ring
  have hjp : p * (j / p) + j % p = j := Nat.div_add_mod j p
  have hl : j % p < p := Nat.mod_lt _ hp0
  have hj1' : (9 * N : ℤ) ≤ j := by exact_mod_cast hj1
  have hj2' : (j : ℤ) < 70 * N := by
    have : j < 70 * N := by omega
    exact_mod_cast this
  have hJlo : cd.Jlo ≤ j / p := by
    rw [Nat.le_div_iff_mul_le hp0]
    have : (cd.Jlo : ℤ) * p ≤ j := by linarith
    exact_mod_cast this
  have hJhi : j / p < cd.Jlo + cd.hiZ.length := by
    rw [Nat.div_lt_iff_lt_mul hp0]
    have : (j : ℤ) < ((cd.Jlo + cd.hiZ.length : ℕ) : ℤ) * p := by linarith
    exact_mod_cast this
  obtain ⟨q, hq⟩ := hdiv
  have hSv : ((dsg.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p = q := by
    rw [hq]; exact Int.mul_ediv_cancel_left _ hp0z
  have hep : (e.val : ℤ) < p := by exact_mod_cast e.isLt
  have hlp : ((j % p : ℕ) : ℤ) < p := by exact_mod_cast hl
  have hl0 : (0 : ℤ) ≤ ((j % p : ℕ) : ℤ) := by positivity
  have he0 : (0 : ℤ) ≤ (e.val : ℤ) := by positivity
  have hq1 : q ≤ cd.S0 := by
    by_contra hcon
    have h1 : (cd.S0 : ℤ) + 1 ≤ q := by omega
    have h2 : (p : ℤ) * ((cd.S0 : ℤ) + 1) ≤ p * q := mul_le_mul_of_nonneg_left h1 (by omega)
    linarith
  have hq2 : (cd.S0 : ℤ) - 1 ≤ q := by
    by_contra hcon
    have h1 : q ≤ (cd.S0 : ℤ) - 2 := by omega
    have h2 : (p : ℤ) * q ≤ p * ((cd.S0 : ℤ) - 2) := mul_le_mul_of_nonneg_left h1 (by omega)
    linarith
  have hqc : q = cd.S0 ∨ q = (cd.S0 : ℤ) - 1 := by omega
  have hkT := key_mul (p : ℤ) (((p : ℤ) - 1) / 2) cd.S0 hpz
  have hTe : (tAff cd.S0).eval (N : ℤ) (((p : ℤ) - 1) / 2) = 78 * N - cd.S0 * p := by
    simp only [tAff, Aff.eval]; linarith
  have hpe : pAff.eval (N : ℤ) (((p : ℤ) - 1) / 2) = (p : ℤ) := by
    simp only [pAff, Aff.eval]; omega
  have hzero : (⟨0, 0, 0⟩ : Aff).eval (N : ℤ) (((p : ℤ) - 1) / 2) = 0 := by simp [Aff.eval]
  set t := j / p - cd.Jlo with ht
  have htl : t < cd.hiZ.length := by omega
  have hJt : cd.Jlo + t = j / p := by omega
  have hh := hall t htl
  obtain ⟨hhi, hlo⟩ := hh
  have hJc : (((cd.Jlo + t : ℕ) : ℤ)) * p = 2 * ((cd.Jlo + t : ℕ) : ℤ) * (((p : ℤ) - 1) / 2) + ((cd.Jlo + t : ℕ) : ℤ) :=
    key_mul (p : ℤ) (((p : ℤ) - 1) / 2) _ hpz
  have hjJ : (j : ℤ) = p * ((j / p : ℕ) : ℤ) + ((j % p : ℕ) : ℤ) := by exact_mod_cast hjp.symm
  have hJt' : (((cd.Jlo + t : ℕ) : ℤ)) = ((j / p : ℕ) : ℤ) := by exact_mod_cast hJt
  rw [hJt'] at hJc
  obtain ⟨z, hz, hzlo, hzhi, hzo⟩ : ∃ z ∈ (if q = cd.S0 then cd.hiZ.getD t [] else cd.loZ.getD t []),
      z.lo.eval (N : ℤ) (((p : ℤ) - 1) / 2) ≤ (e.val : ℤ) ∧ (e.val : ℤ) < z.hi.eval (N : ℤ) (((p : ℤ) - 1) / 2) ∧
      zoneOK pk m win cs cd.Z cd.AT cd.BT (cd.Jlo + t) (if q = cd.S0 then (cd.S0 : ℤ) else (cd.S0 : ℤ) - 1) z = true := by
    rcases hqc with h | h
    · rw [if_pos h, if_pos h]
      rw [h] at hq
      refine side_sound pk m win cs hwin cd.Z cd.AT cd.BT (cd.Jlo + t) (cd.S0 : ℤ) ⟨0, 0, 0⟩ (hiLc cd.S0 (cd.Jlo + t)) (tAff cd.S0)
        (hiPc cd.S0 (cd.Jlo + t)) _ _ hhi (e.val : ℤ) ?_ ?_ ?_ ?_ hecm
      · rw [hzero]; exact he0
      · simp only [hiLc, Aff.eval]; rw [hJt']; linarith [hkT, hJc, hjJ, hj2', hq, hHz]
      · rw [hTe]; linarith
      · simp only [hiPc, Aff.eval]; rw [hJt']; linarith [hkT, hJc, hjJ, hj1', hq, hHz]
    · have hne : q ≠ cd.S0 := by omega
      rw [if_neg hne, if_neg hne]
      rw [h] at hq
      refine side_sound pk m win cs hwin cd.Z cd.AT cd.BT (cd.Jlo + t) ((cd.S0 : ℤ) - 1) (tAff cd.S0) (loLc cd.S0 (cd.Jlo + t)) pAff
        (loPc cd.S0 (cd.Jlo + t)) _ _ hlo (e.val : ℤ) ?_ ?_ ?_ ?_ hecm
      · rw [hTe]; linarith
      · simp only [loLc, Aff.eval]; rw [hJt']; linarith [hkT, hJc, hjJ, hj2', hq, hHz]
      · rw [hpe]; exact hep
      · simp only [loPc, Aff.eval]; rw [hJt']; linarith [hkT, hJc, hjJ, hj1', hq, hHz]
  obtain ⟨hgl, hg2l⟩ := zoneOK_lt hzo
  have hg1 : z.g < pk.charts.length := by omega
  have hg2 : z.g2 < pk.charts.length := by omega
  rw [hJt] at hzo
  have F5' : cd.S0 + 3 ≤ 78 * N := by exact_mod_cast F5
  have hSq : (if q = cd.S0 then (cd.S0 : ℤ) else (cd.S0 : ℤ) - 1) = q := by
    split_ifs with hh <;> omega
  have hSle : (if q = cd.S0 then (cd.S0 : ℤ) else (cd.S0 : ℤ) - 1).toNat ≤ cd.S0 := by
    split_ifs <;> omega
  obtain ⟨⟨k, hk, hjk⟩, ⟨k2, hk2, hjk2⟩, hpsi⟩ := zone_sound pk m win cs hlen2 hnn hwin hodd hcm0 hcm1 hio hp59 hK
    M.sys.prof hF (Ub := cd.S0 + 3) (Jb := cd.Jlo + cd.hiZ.length) (Z := cd.Z) hZe hZd (J := j / p)
    (S := if q = cd.S0 then (cd.S0 : ℤ) else (cd.S0 : ℤ) - 1)
    (H := dsg.H N) hJhi (by omega) (by omega) (AT := cd.AT) (BT := cd.BT)
    (tabOK_sound htab (j / p) (by omega) hJhi).1 (tabOK_sound htab (j / p) (by omega) hJhi).2 z hzo e hzlo hzhi hg1 hg2 hlowc
  refine ⟨⟨z.g, hg1⟩, ⟨k, hk⟩, ⟨z.g2, hg2⟩, ⟨k2, hk2⟩, hjk, hjk2, ?_⟩
  intro y h1 h2
  have := hpsi y h1 h2
  rw [hSv, ← hSq]
  simp only [zero_add, Finset.sum_range_one, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one,
    one_mul, add_zero]
  exact this

end
end CatalanMeasure.GenD.Uniform.W.Charts6.Check
