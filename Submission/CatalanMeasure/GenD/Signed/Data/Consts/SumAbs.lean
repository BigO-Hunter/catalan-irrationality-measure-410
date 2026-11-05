module

public import Submission.CatalanMeasure.CellCert.RawInts
public import Submission.CatalanMeasure.GenD.D58.Cert590.Data
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.MeanEval

/-!
# D2 constants: `hec` of `LinkCert` (absolute sums of the K590 trials `p`, `v`)

`tsum_abs_trialSeqS_le`: for `u = trialSeqS cs tail` and a rational radius `rho_j < 1` per pole with
`zr_j^2 + zi_j^2 <= rho_j^2`,
`sum' |u_k| <= sum |cs| / 2^40 + sum_j (|rr_j| + |ri_j|) rho_j / (1 - rho_j)`.
(The bound `SpikeA.tsum_abs_tseq_le` needs `|zr| + |zi| < 1`, which 38 of the 75 poles of K590 `P` and
`V` violate; the radius is the Euclidean norm, rounded up on the grid `2^-60`.)

`hec_K590`: `e (4 sum' |p| + 4 sum' |v| + |p 1| + 20) < delta / 2` for `p = trialSeqS Pc P`,
`v = trialSeqS Vc V`, `0 <= e <= 2^-30`, `delta >= 13/100000`.
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

open Set CatalanMeasure.Cert CatalanMeasure.CellCert

/-- The bound `sum |cs| / 2^40 + sum_j (|rr_j| + |ri_j|) rho_j / (1 - rho_j)`. -/
def radBound (cs : List ℤ) (tail : List TailQ) (rho : List ℚ) : ℚ :=
  (cs.map fun c : ℤ => |(c : ℚ)|).sum / 1099511627776 +
    ((tail.zip rho).map fun p => (|p.1.rr| + |p.1.ri|) * p.2 / (1 - p.2)).sum

/-- The radius check: `0 <= rho_j < 1` and `zr_j^2 + zi_j^2 <= rho_j^2`, one radius per pole. -/
def radOK (tail : List TailQ) (rho : List ℚ) : Bool :=
  decide (tail.length = rho.length) &&
    (tail.zip rho).all fun p =>
      decide (0 ≤ p.2 ∧ p.2 < 1 ∧ p.1.zr * p.1.zr + p.1.zi * p.1.zi ≤ p.2 * p.2)

theorem zip_fst_snd : ∀ L : List (TailQ × ℚ), (L.map Prod.fst).zip (L.map Prod.snd) = L
  | [] => rfl
  | q :: L => by simp only [List.map_cons, List.zip_cons_cons, zip_fst_snd L]

theorem listSum_getD (h : ℤ → ℝ) : ∀ cs : List ℤ,
    ∑ j ∈ Finset.range cs.length, h (cs.getD j 0) = (cs.map h).sum
  | [] => by simp
  | c :: cs => by
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.sum_cons]
    rw [listSum_getD h cs, add_comm]

/-- Pole terms of the majorant: `(|rr| + |ri|) rho^k`. -/
theorem tail_term_le_rad (L : List (TailQ × ℚ))
    (hL : ∀ p ∈ L, 0 ≤ p.2 ∧ p.2 < 1 ∧ p.1.zr * p.1.zr + p.1.zi * p.1.zi ≤ p.2 * p.2) (k : ℕ) :
    |((((L.map Prod.fst).map TailQ.toC).map
        (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum).re| ≤
      (L.map fun p => (((|p.1.rr| + |p.1.ri| : ℚ)) : ℝ) * ((p.2 : ℚ) : ℝ) ^ k).sum := by
  induction L with
  | nil => simp
  | cons q L ih =>
    obtain ⟨h0, h1, h2⟩ := hL q (by simp)
    have ih' := ih (fun p hp => hL p (List.mem_cons_of_mem _ hp))
    simp only [List.map_cons, List.sum_cons, Complex.add_re]
    refine (abs_add_le _ _).trans (add_le_add ?_ ih')
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_pow]
    have hw : ‖(TailQ.toC q.1).2‖ ≤ (((|q.1.rr| + |q.1.ri| : ℚ)) : ℝ) := by
      have h := Complex.norm_le_abs_re_add_abs_im (TailQ.toC q.1).2
      simpa [TailQ.toC, OAI.InternalCatalan.barrierComplex] using h
    have hz : ‖(TailQ.toC q.1).1‖ ≤ ((q.2 : ℚ) : ℝ) := by
      have hn : ‖(TailQ.toC q.1).1‖ ^ 2 =
          (q.1.zr : ℝ) * q.1.zr + (q.1.zi : ℝ) * q.1.zi := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp [TailQ.toC, OAI.InternalCatalan.barrierComplex]
      have h2' : (q.1.zr : ℝ) * q.1.zr + (q.1.zi : ℝ) * q.1.zi ≤
          ((q.2 : ℚ) : ℝ) * ((q.2 : ℚ) : ℝ) := by
        exact_mod_cast h2
      have h0' : (0 : ℝ) ≤ ((q.2 : ℚ) : ℝ) := by exact_mod_cast h0
      by_contra hcon
      push_neg at hcon
      nlinarith [norm_nonneg (TailQ.toC q.1).1]
    exact mul_le_mul hw (pow_le_pow_left₀ (norm_nonneg _) hz k) (by positivity) (by positivity)

theorem hasSum_rad_geom (L : List (TailQ × ℚ))
    (hL : ∀ p ∈ L, 0 ≤ p.2 ∧ p.2 < 1 ∧ p.1.zr * p.1.zr + p.1.zi * p.1.zi ≤ p.2 * p.2) :
    HasSum (fun j : ℕ => (L.map fun p => (((|p.1.rr| + |p.1.ri| : ℚ)) : ℝ) *
        ((p.2 : ℚ) : ℝ) ^ (j + 1)).sum)
      (L.map fun p => (((|p.1.rr| + |p.1.ri| : ℚ)) : ℝ) * ((p.2 : ℚ) : ℝ) *
        (1 - ((p.2 : ℚ) : ℝ))⁻¹).sum := by
  induction L with
  | nil => simpa using hasSum_zero
  | cons q L ih =>
    obtain ⟨h0, h1, _⟩ := hL q (by simp)
    have ht' : ((q.2 : ℚ) : ℝ) < 1 := by exact_mod_cast h1
    have h0' : (0 : ℝ) ≤ ((q.2 : ℚ) : ℝ) := by exact_mod_cast h0
    have hg := (hasSum_geometric_of_lt_one h0' ht').mul_left
      ((((|q.1.rr| + |q.1.ri| : ℚ)) : ℝ) * ((q.2 : ℚ) : ℝ))
    have hg' : HasSum (fun j : ℕ => (((|q.1.rr| + |q.1.ri| : ℚ)) : ℝ) * ((q.2 : ℚ) : ℝ) ^ (j + 1))
        ((((|q.1.rr| + |q.1.ri| : ℚ)) : ℝ) * ((q.2 : ℚ) : ℝ) * (1 - ((q.2 : ℚ) : ℝ))⁻¹) := by
      convert hg using 1
      funext j; rw [pow_succ]; ring
    have := hg'.add (ih (fun p hp => hL p (List.mem_cons_of_mem _ hp)))
    simp only [List.map_cons, List.sum_cons]
    exact this

theorem cs_sum_cast (cs : List ℤ) :
    (((cs.map fun c : ℤ => |(c : ℚ)|).sum : ℚ) : ℝ) = (cs.map fun c : ℤ => |((c : ℤ) : ℝ)|).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, Rat.cast_add, ih]
    push_cast
    rfl

theorem pole_sum_cast (L : List (TailQ × ℚ)) :
    ((((L.map fun p => (|p.1.rr| + |p.1.ri|) * p.2 / (1 - p.2)).sum : ℚ)) : ℝ) =
      (L.map fun p => (((|p.1.rr| + |p.1.ri| : ℚ)) : ℝ) * ((p.2 : ℚ) : ℝ) *
        (1 - ((p.2 : ℚ) : ℝ))⁻¹).sum := by
  induction L with
  | nil => simp
  | cons q L ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, Rat.cast_add, ih]
    push_cast
    simp [div_eq_mul_inv]

theorem radBound_cast (cs : List ℤ) (L : List (TailQ × ℚ)) :
    ((radBound cs (L.map Prod.fst) (L.map Prod.snd) : ℚ) : ℝ) =
      (cs.map fun c => |((c : ℤ) : ℝ)|).sum / 1099511627776 +
      (L.map fun p => (((|p.1.rr| + |p.1.ri| : ℚ)) : ℝ) * ((p.2 : ℚ) : ℝ) *
        (1 - ((p.2 : ℚ) : ℝ))⁻¹).sum := by
  unfold radBound
  rw [zip_fst_snd, Rat.cast_add, Rat.cast_div, cs_sum_cast, pole_sum_cast]
  norm_num

theorem finSum_hasSum (cs : List ℤ) :
    HasSum (fun j : ℕ => |finCoeffS cs (j + 1)|)
      ((cs.map fun c => |((c : ℤ) : ℝ)|).sum / 1099511627776) := by
  have hfin : ∀ j ∉ Finset.range cs.length, |finCoeffS cs (j + 1)| = 0 := by
    intro j hj
    rw [finCoeffS_eq_zero (by simpa using hj)]; simp
  have h : HasSum (fun j : ℕ => |finCoeffS cs (j + 1)|)
      (∑ j ∈ Finset.range cs.length, |finCoeffS cs (j + 1)|) := hasSum_sum_of_ne_finset_zero hfin
  have e1 : ∀ j, |finCoeffS cs (j + 1)| =
      (fun c : ℤ => |(c : ℝ)| / 1099511627776) (cs.getD j 0) := by
    intro j
    rw [finCoeffS_succ, abs_div]
    simp
  have e2 : ∑ j ∈ Finset.range cs.length, |finCoeffS cs (j + 1)| =
      (cs.map fun c => |((c : ℤ) : ℝ)|).sum / 1099511627776 := by
    rw [Finset.sum_congr rfl (fun j _ => e1 j), listSum_getD (fun c : ℤ => |(c : ℝ)| / 1099511627776) cs]
    clear e1 h hfin
    induction cs with
    | nil => simp
    | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons, add_div]
      rw [ih]
  rwa [e2] at h

theorem tsum_abs_trialSeqS_le_aux (cs : List ℤ) (L : List (TailQ × ℚ))
    (hL : ∀ p ∈ L, 0 ≤ p.2 ∧ p.2 < 1 ∧ p.1.zr * p.1.zr + p.1.zi * p.1.zi ≤ p.2 * p.2) :
    ∑' j : ℕ, |trialSeqS cs (L.map Prod.fst) j| ≤
      ((radBound cs (L.map Prod.fst) (L.map Prod.snd) : ℚ) : ℝ) := by
  rw [radBound_cast]
  set tl := L.map Prod.fst with htl
  have hM := (finSum_hasSum cs).add (hasSum_rad_geom L hL)
  have hle : ∀ j, |trialSeqS cs tl (j + 1)| ≤ |finCoeffS cs (j + 1)| +
      (L.map fun p => (((|p.1.rr| + |p.1.ri| : ℚ)) : ℝ) * ((p.2 : ℚ) : ℝ) ^ (j + 1)).sum := by
    intro j
    unfold trialSeqS
    rw [if_neg (Nat.succ_ne_zero j)]
    exact (abs_add_le _ _).trans (add_le_add_right (tail_term_le_rad L hL (j + 1)) _)
  have hs : Summable (fun j : ℕ => |trialSeqS cs tl (j + 1)|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hle hM.summable
  have hs0 : Summable (fun j : ℕ => |trialSeqS cs tl j|) := (summable_nat_add_iff 1).mp hs
  rw [hs0.tsum_eq_zero_add]
  have h0 : trialSeqS cs tl 0 = 0 := by simp [trialSeqS]
  rw [h0, abs_zero, zero_add]
  have h1 := hasSum_le hle hs.hasSum hM
  rw [← hs.hasSum.tsum_eq] at h1 ⊢
  linarith [h1, hM.tsum_eq]

/-- **Absolute sum with a rational radius per pole.** -/
theorem tsum_abs_trialSeqS_le (cs : List ℤ) (tail : List TailQ) (rho : List ℚ)
    (h : radOK tail rho = true) :
    ∑' j : ℕ, |trialSeqS cs tail j| ≤ ((radBound cs tail rho : ℚ) : ℝ) := by
  unfold radOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  have hL : ∀ p ∈ tail.zip rho,
      0 ≤ p.2 ∧ p.2 < 1 ∧ p.1.zr * p.1.zr + p.1.zi * p.1.zi ≤ p.2 * p.2 := by
    intro p hp
    simpa using hall p hp
  have h1 : (tail.zip rho).map Prod.fst = tail := List.map_fst_zip (by omega)
  have h2 : (tail.zip rho).map Prod.snd = rho := List.map_snd_zip (by omega)
  have := tsum_abs_trialSeqS_le_aux cs (tail.zip rho) hL
  rwa [h1, h2] at this

/-! ### K590 -/

def rhoPN : List ℤ := raw_ints% [922337203685477581, 922337203685477581, 1037629354146162279, 1037629354146162279, 1095275429376504628, 1095275429376504628, 1118333859468641567, 1118333859468641567, 1129863074514710037, 1129863074514710037, 1141392289560778507, 1141392289560778507, 1147156897083812742, 1147156897083812742, 1149462740093026436, 1149462740093026436, 1151768583102240130, 1151768583102240130, 1152114459553622184, 1152114459553622184, 1152575628155464922, 1152575628155464922, 1152806212456386292, 1152806212456386292, 1152840800101524497, 1152840800101524497, 1152886916961708771, 1152886916961708771, 1152909975391800908, 1152909975391800908, 1152913434156314729, 1152913434156314729, 1152918045842333156, 1152918045842333156, 1141300995009501838, 1141315772774106430, 1141329740635914514, 1141342907095778583, 1141355280119334082, 1141366867148052173, 1141377675112146410, 1141387710442167141, 1141396979080027681, 1141405486492624839, 1141413237671953241, 1141420237153621579, 1141426489017857466, 1141431996896148360, 1141436763983530734, 1141440793033429512, 1141444086372789608, 1141446645896871923, 1141448473078900188, 1141449568968458831, 1141449934194856968, 1141449568968458831, 1141448473078900188, 1141446645896871923, 1141444086372789608, 1141440793033429512, 1141436763983530734, 1141431996896148360, 1141426489017857466, 1141420237153621579, 1141413237671953241, 1141405486492624839, 1141396979080027681, 1141387710442167141, 1141377675112146410, 1141366867148052173, 1141355280119334082, 1141342907095778583, 1141329740635914514, 1141315772774106430, 1141300995009501838]
def rhoVN : List ℤ := raw_ints% [922337203685477581, 922337203685477581, 1037629354146162279, 1037629354146162279, 1095275429376504628, 1095275429376504628, 1118333859468641567, 1118333859468641567, 1129863074514710037, 1129863074514710037, 1141392289560778507, 1141392289560778507, 1147156897083812742, 1147156897083812742, 1149462740093026436, 1149462740093026436, 1151768583102240130, 1151768583102240130, 1152114459553622184, 1152114459553622184, 1152575628155464922, 1152575628155464922, 1152806212456386292, 1152806212456386292, 1152840800101524497, 1152840800101524497, 1152886916961708771, 1152886916961708771, 1152909975391800908, 1152909975391800908, 1152913434156314729, 1152913434156314729, 1152918045842333156, 1152918045842333156, 1141300995009501838, 1141315772774106430, 1141329740635914514, 1141342907095778583, 1141355280119334082, 1141366867148052173, 1141377675112146410, 1141387710442167141, 1141396979080027681, 1141405486492624839, 1141413237671953241, 1141420237153621579, 1141426489017857466, 1141431996896148360, 1141436763983530734, 1141440793033429512, 1141444086372789608, 1141446645896871923, 1141448473078900188, 1141449568968458831, 1141449934194856968, 1141449568968458831, 1141448473078900188, 1141446645896871923, 1141444086372789608, 1141440793033429512, 1141436763983530734, 1141431996896148360, 1141426489017857466, 1141420237153621579, 1141413237671953241, 1141405486492624839, 1141396979080027681, 1141387710442167141, 1141377675112146410, 1141366867148052173, 1141355280119334082, 1141342907095778583, 1141329740635914514, 1141315772774106430, 1141300995009501838]
def rhoP : List ℚ := rhoPN.map fun n => (n : ℚ) / 2 ^ 60
def rhoV : List ℚ := rhoVN.map fun n => (n : ℚ) / 2 ^ 60

open CatalanMeasure.GenD.D58.Cert590 in
theorem radOK_P : radOK P rhoP = true := by decide +kernel
open CatalanMeasure.GenD.D58.Cert590 in
theorem radOK_V : radOK V rhoV = true := by decide +kernel

open CatalanMeasure.GenD.D58.Cert590 in
theorem radBound_P : radBound Pc P rhoP ≤ 1951 := by decide +kernel
open CatalanMeasure.GenD.D58.Cert590 in
theorem radBound_V : radBound Vc V rhoV ≤ 7465 := by decide +kernel

open CatalanMeasure.GenD.D58.Cert590 in
theorem p1_bound : |(((Pc.getD 0 0 : ℤ) : ℚ) / 1099511627776 + tailValQ P 1)| ≤ 1 / 5 := by
  decide +kernel

open CatalanMeasure.GenD.D58.Cert590 in
theorem tsum_abs_p_K590 : ∑' j : ℕ, |trialSeqS Pc P j| ≤ 1951 := by
  have := tsum_abs_trialSeqS_le Pc P rhoP radOK_P
  have h2 : ((radBound Pc P rhoP : ℚ) : ℝ) ≤ 1951 := by exact_mod_cast radBound_P
  linarith

open CatalanMeasure.GenD.D58.Cert590 in
theorem tsum_abs_v_K590 : ∑' j : ℕ, |trialSeqS Vc V j| ≤ 7465 := by
  have := tsum_abs_trialSeqS_le Vc V rhoV radOK_V
  have h2 : ((radBound Vc V rhoV : ℚ) : ℝ) ≤ 7465 := by exact_mod_cast radBound_V
  linarith

open CatalanMeasure.GenD.D58.Cert590 in
theorem abs_p1_K590 : |trialSeqS Pc P 1| ≤ 1 / 5 := by
  have h := trialSeqS_succ_eq Pc P 0
  have h1 : trialSeqS Pc P 1 =
      ((((Pc.getD 0 0 : ℤ) : ℚ) / 1099511627776 + tailValQ P 1 : ℚ) : ℝ) := h
  rw [h1, ← Rat.cast_abs]
  calc _ ≤ ((1 / 5 : ℚ) : ℝ) := Rat.cast_le.mpr p1_bound
    _ = 1 / 5 := by norm_num

open CatalanMeasure.GenD.D58.Cert590 in
/-- **`hec` (L1) for K590** with `e = 2^-30` (any `0 <= e <= 2^-30`) and `delta >= 1.3e-4`. -/
theorem hec_K590 {e δ : ℝ} (he0 : 0 ≤ e) (he : e ≤ 1 / 2 ^ 30) (hδ : (13 / 100000 : ℝ) ≤ δ)
    {p v : ℕ → ℝ} (hp : p = trialSeqS Pc P) (hv : v = trialSeqS Vc V) :
    e * (4 * (∑' j, |p j|) + 4 * (∑' j, |v j|) + |p 1| + 20) < δ / 2 := by
  subst hp hv
  have h1 := tsum_abs_p_K590
  have h2 := tsum_abs_v_K590
  have h3 := abs_p1_K590
  have hb : 4 * (∑' j, |trialSeqS Pc P j|) + 4 * (∑' j, |trialSeqS Vc V j|) + |trialSeqS Pc P 1| + 20
      ≤ 4 * 1951 + 4 * 7465 + 1 / 5 + 20 := by linarith
  have hnn : 0 ≤ 4 * (∑' j, |trialSeqS Pc P j|) + 4 * (∑' j, |trialSeqS Vc V j|) +
      |trialSeqS Pc P 1| + 20 := by
    have : 0 ≤ ∑' j, |trialSeqS Pc P j| := tsum_nonneg (fun j => abs_nonneg _)
    have : 0 ≤ ∑' j, |trialSeqS Vc V j| := tsum_nonneg (fun j => abs_nonneg _)
    positivity
  calc e * _ ≤ (1 / 2 ^ 30) * (4 * 1951 + 4 * 7465 + 1 / 5 + 20) :=
        mul_le_mul he hb hnn (by positivity)
    _ < δ / 2 := by norm_num; linarith

end CatalanMeasure.Signed.Consts

#print axioms CatalanMeasure.Signed.Consts.tsum_abs_trialSeqS_le
#print axioms CatalanMeasure.Signed.Consts.hec_K590
