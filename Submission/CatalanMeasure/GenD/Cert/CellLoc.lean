module

public import Submission.CatalanMeasure.CellCert.Cell

@[expose] public section

open Set Nat CatalanMeasure.Cert
namespace CatalanMeasure.CellCert
set_option maxRecDepth 100000
theorem ptZ_localL (D : PolyData) (hD : D.Ok) (cc hh : ℤ) (m L : ℕ) (MGL : ℤ)
    (hMGL : ∀ y : ℝ, |y - (cc : ℝ) / TT| ≤ (hh : ℝ) / TT → (SC : ℝ) * |ptZ D.Z (m + L) y| ≤ (MGL : ℝ))
    (hm : m + L ≤ D.LV.length) (hh0 : 0 ≤ hh) (hlow : -TT ≤ cc - hh) (hhigh : cc + hh ≤ TT) :
    ∀ y : ℝ, |y - (cc : ℝ) / TT| ≤ (hh : ℝ) / TT →
      (SC : ℝ) * |ptZ D.Z m y| ≤ (PbV D.N cc hh (polyValsD D cc (m + L)) m L MGL : ℤ) := by
  intro y hy
  have hT : (0 : ℝ) < TT := by exact_mod_cast TT_pos
  have hS : (0 : ℝ) < SC := by exact_mod_cast SC_pos
  have hh0R : (0 : ℝ) ≤ hh := by exact_mod_cast hh0
  set c : ℝ := (cc : ℝ) / TT with hc
  set hR : ℝ := (hh : ℝ) / TT with hhR
  have hhR0 : 0 ≤ hR := by positivity
  have hlow' : (-(TT : ℝ)) ≤ (cc : ℝ) - hh := by exact_mod_cast hlow
  have hhigh' : (cc : ℝ) + hh ≤ TT := by exact_mod_cast hhigh
  have e1 : c - hR = ((cc : ℝ) - hh) / TT := by simp only [hc, hhR]; ring
  have e2 : c + hR = ((cc : ℝ) + hh) / TT := by simp only [hc, hhR]; ring
  have g1 : (-1 : ℝ) ≤ c - hR := by rw [e1, le_div_iff₀ hT]; linarith
  have g2 : c + hR ≤ 1 := by rw [e2, div_le_iff₀ hT]; linarith
  have hyI : ∀ z ∈ Icc (c - hR) (c + hR), |z| ≤ 1 := by
    intro z hz; rw [abs_le]; constructor <;> linarith [hz.1, hz.2]
  have hxI : y ∈ Icc (c - hR) (c + hR) := by
    have := abs_le.mp hy
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hcont : ∀ j ≤ L, ContinuousOn (fun z => ptZ D.Z (m + j) z) (Icc (c - hR) (c + hR)) := by
    intro j _ z _
    exact (hasDerivAt_ptZ D.Z (m + j) z).continuousAt.continuousWithinAt
  have hder : ∀ j < L, ∀ z ∈ Ioo (c - hR) (c + hR),
      HasDerivAt (fun z => ptZ D.Z (m + j) z) ((fun z => ptZ D.Z (m + (j + 1)) z) z) z := by
    intro j _ z _
    exact hasDerivAt_ptZ D.Z (m + j) z
  have hbd : ∀ z ∈ Icc (c - hR) (c + hR), |ptZ D.Z (m + L) z| ≤ (MGL : ℝ) / SC := by
    intro z hz
    rw [le_div_iff₀ hS, mul_comm]
    exact hMGL z (abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩)
  have htay := taylor_tower' c hR ((MGL : ℝ) / SC) L (fun j z => ptZ D.Z (m + j) z)
    hcont hder hbd y hxI
  simp only [add_zero] at htay
  set S : ℝ := ∑ j ∈ Finset.range L, ptZ D.Z (m + j) c * (y - c) ^ j / (j ! : ℝ) with hSdef
  have hdx : |y - c| ≤ hR := abs_le.mpr ⟨by linarith [hxI.1], by linarith [hxI.2]⟩
  have hSb : (SC : ℝ) * |S| ≤ (((List.range L).map (fun k =>
      cdiv ((zabs ((polyValsD D cc (m + L)).getD (m + k) 0 * SC / (K40 * TPN D.N)) + 1) * zpw hh k)
        (tf k))).sum : ℤ) := by
    rw [cast_list_sum_map, list_range_map_sum (fun a => ((cdiv ((zabs ((polyValsD D cc (m + L)).getD (m + a) 0 * SC / (K40 * TPN D.N)) + 1) * zpw hh a) (tf a) : ℤ) : ℝ))]
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hS.le) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j hjm => ?_)
    have hj : j < L := Finset.mem_range.mp hjm
    have hf : (0 : ℝ) < (j ! : ℝ) := by positivity
    have hd : (0 : ℤ) < tf j := by
      rw [tf_eq j]
      have := TT_pos
      positivity
    obtain ⟨s1, s2⟩ := ptZ_scaled D hD cc (m + L) (m + j) hm (by omega)
    set q : ℤ := (polyValsD D cc (m + L)).getD (m + j) 0 * SC / (K40 * TPN D.N) with hq
    have hA : (SC : ℝ) * |ptZ D.Z (m + j) c| ≤ ((zabs q + 1 : ℤ) : ℝ) := by
      push_cast; rw [zabs_cast]
      have e : (SC : ℝ) * |ptZ D.Z (m + j) c| = |(SC : ℝ) * ptZ D.Z (m + j) c| := by
        rw [abs_mul, abs_of_pos hS]
      rw [e, abs_le]
      constructor <;> cases abs_cases (q : ℝ) <;>
        linarith [neg_abs_le (q : ℝ), le_abs_self (q : ℝ)]
    have hp : |y - c| ^ j ≤ hR ^ j := pow_le_pow_left₀ (abs_nonneg _) hdx _
    have hAnn : (0 : ℝ) ≤ ((zabs q + 1 : ℤ) : ℝ) := by
      have : 0 ≤ zabs q := by unfold zabs; split_ifs <;> omega
      exact_mod_cast (by omega : (0 : ℤ) ≤ zabs q + 1)
    have h1 : (SC : ℝ) * |ptZ D.Z (m + j) c * (y - c) ^ j / (j ! : ℝ)| ≤
        ((zabs q + 1 : ℤ) : ℝ) * (hh : ℝ) ^ j / ((TT : ℝ) ^ j * (j ! : ℝ)) := by
      rw [abs_div, abs_mul, abs_pow, Nat.abs_cast]
      have e : (SC : ℝ) * (|ptZ D.Z (m + j) c| * |y - c| ^ j / (j ! : ℝ)) =
          ((SC : ℝ) * |ptZ D.Z (m + j) c|) * |y - c| ^ j / (j ! : ℝ) := by ring
      rw [e]
      calc ((SC : ℝ) * |ptZ D.Z (m + j) c|) * |y - c| ^ j / (j ! : ℝ)
          ≤ ((zabs q + 1 : ℤ) : ℝ) * hR ^ j / (j ! : ℝ) := by
            apply div_le_div_of_nonneg_right _ hf.le
            exact mul_le_mul hA hp (by positivity) hAnn
        _ = _ := by simp only [hhR]; rw [div_pow]; field_simp
    refine le_trans h1 ?_
    obtain ⟨Cq, hCq⟩ : ∃ Cq : ℤ, Cq = cdiv ((zabs q + 1) * zpw hh j) (tf j) := ⟨_, rfl⟩
    rw [← hCq]
    have hdc := cdiv_cast_ge ((zabs q + 1) * zpw hh j) (tf j) hd
    rw [← hCq, zpw_eq hh j hh0, tf_eq j] at hdc
    push_cast at hdc
    push_cast
    rw [div_le_iff₀ (by positivity)]
    linarith [hdc]
  have hMn : 0 ≤ (MGL : ℝ) / SC := (abs_nonneg _).trans (hbd c ⟨by linarith, by linarith⟩)
  have hrem : (SC : ℝ) * |ptZ D.Z m y - S| ≤ (cdiv (MGL * zpw hh L) (tf L) : ℤ) := by
    have hf : (0 : ℝ) < (L ! : ℝ) := by positivity
    have hd : (0 : ℤ) < tf L := by
      rw [tf_eq L]
      have := TT_pos
      positivity
    obtain ⟨Cq, hCq⟩ : ∃ Cq : ℤ, Cq = cdiv (MGL * zpw hh L) (tf L) := ⟨_, rfl⟩
    rw [← hCq]
    have hdc := cdiv_cast_ge (MGL * zpw hh L) (tf L) hd
    rw [← hCq, zpw_eq hh L hh0, tf_eq L] at hdc
    push_cast at hdc
    have hp : |y - c| ^ L ≤ hR ^ L := pow_le_pow_left₀ (abs_nonneg _) hdx _
    have h2 : |ptZ D.Z m y - S| ≤ ((MGL : ℝ) / SC) * hR ^ L / (L ! : ℝ) := by
      refine htay.trans (div_le_div_of_nonneg_right ?_ hf.le)
      exact mul_le_mul_of_nonneg_left hp hMn
    have h3 : (SC : ℝ) * (((MGL : ℝ) / SC) * hR ^ L / (L ! : ℝ)) =
        (MGL : ℝ) * (hh : ℝ) ^ L / ((TT : ℝ) ^ L * (L ! : ℝ)) := by
      simp only [hhR]; rw [div_pow]; field_simp
    calc (SC : ℝ) * |ptZ D.Z m y - S| ≤ (SC : ℝ) * (((MGL : ℝ) / SC) * hR ^ L / (L ! : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 hS.le
      _ = _ := h3
      _ ≤ _ := by
          rw [div_le_iff₀ (by positivity)]
          linarith [hdc]
  have hb1 : |ptZ D.Z m y| ≤ |S| + |ptZ D.Z m y - S| := by
    calc |ptZ D.Z m y| = |S + (ptZ D.Z m y - S)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  unfold PbV
  push_cast
  have := mul_le_mul_of_nonneg_left hb1 hS.le
  push_cast at hSb hrem
  linarith
theorem cellVal_soundL (F : ℝ → ℝ) (ev : ℚ → Option (ℚ × ℚ)) (D : PolyData) (hD : D.Ok)
    (poles : List PoleR) (m L : ℕ) (MGL : ℤ)
    (pe : Option ℚ) (cap : ℚ)
    (hev : ∀ q v e, ev q = some (v, e) → |(q : ℝ)| ≤ 1 → (∀ p ∈ poles, ((q : ℝ) : ℂ) ≠ p.pc) →
      F q ≤ (v : ℝ) + e)
    (hFc : ContinuousOn F {y : ℝ | |y| ≤ 1 ∧ ∀ q ∈ poles, (y : ℂ) ≠ q.pc})
    (hFd : ∀ y ∈ Ioo (-1 : ℝ) 1, (∀ p : ℚ, pe = some p → y ≠ (p : ℝ)) →
      (∀ q ∈ poles, (y : ℂ) ≠ q.pc) → HasDerivAt F (ftZ D.Z poles 0 y) y)
    (cc hh : ℤ) (hMGL : ∀ y : ℝ, |y - (cc : ℝ) / TT| ≤ (hh : ℝ) / TT → (SC : ℝ) * |ptZ D.Z (m + L) y| ≤ (MGL : ℝ))
    (h : cellVal ev D poles m L MGL pe cap (cc, hh) = true) :
    ∀ x : ℝ, |x - (cc : ℝ) / TT| ≤ (hh : ℝ) / TT → F x ≤ (cap : ℝ) := by
  intro x hx
  unfold cellVal at h
  simp only at h
  split at h
  · simp at h
  rename_i ve hve
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hmLV, hh0⟩, hlow⟩, hhigh⟩, hpeb⟩, hpos⟩, hineq⟩ := h
  have hT : (0 : ℝ) < TT := by exact_mod_cast TT_pos
  have hS : (0 : ℝ) < SC := by exact_mod_cast SC_pos
  have hh0R : (0 : ℝ) ≤ hh := by exact_mod_cast hh0
  set V := polyValsD D cc (m + L) with hV
  set lo : ℚ := ((cc - hh : ℤ) : ℚ) / (TT : ℚ) with hlo
  set hi : ℚ := ((cc + hh : ℤ) : ℚ) / (TT : ℚ) with hhi
  set c : ℝ := (cc : ℝ) / TT with hc
  set hR : ℝ := (hh : ℝ) / TT with hhR
  have hloR : ((lo : ℚ) : ℝ) = c - hR := by
    simp only [hlo, hc, hhR]; push_cast; ring
  have hhiR : ((hi : ℚ) : ℝ) = c + hR := by
    simp only [hhi, hc, hhR]; push_cast; ring
  have hhR0 : 0 ≤ hR := by positivity
  set PB : ℤ := PbV D.N cc hh V m L MGL with hPB
  have hpe' : ∀ p : ℚ, pe = some p → ∀ y ∈ Ioo (c - hR) (c + hR), y ≠ (p : ℝ) := by
    intro p hp y hy hyp
    subst hp
    simp only [peOK, Bool.or_eq_true, decide_eq_true_eq] at hpeb
    rcases hpeb with h1 | h1
    · have : (p : ℝ) ≤ c - hR := by rw [← hloR]; exact_mod_cast h1
      linarith [hy.1]
    · have : c + hR ≤ (p : ℝ) := by rw [← hhiR]; exact_mod_cast h1
      linarith [hy.2]
  have hxI : x ∈ Icc (c - hR) (c + hR) := by
    have := abs_le.mp hx
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hcI : c ∈ Icc (c - hR) (c + hR) := ⟨by linarith, by linarith⟩
  have hgeo : ∀ y ∈ Icc (c - hR) (c + hR), ∀ q ∈ poles,
      0 < ((poleDl q lo hi : ℚ) : ℝ) ∧ ((poleDl q lo hi : ℚ) : ℝ) ≤ ‖(y : ℂ) - q.pc‖ := by
    intro y hy q hq
    refine ⟨by exact_mod_cast hpos q hq, dl_le_norm q lo hi y ?_ ?_⟩
    · rw [hloR]; exact hy.1
    · rw [hhiR]; exact hy.2
  have hne : ∀ y ∈ Icc (c - hR) (c + hR), ∀ q ∈ poles, (y : ℂ) ≠ q.pc := by
    intro y hy q hq heq
    have := hgeo y hy q hq
    rw [heq, sub_self, norm_zero] at this
    linarith [this.1, this.2]
  have hlow' : (-(TT : ℝ)) ≤ (cc : ℝ) - hh := by exact_mod_cast hlow
  have hhigh' : (cc : ℝ) + hh ≤ TT := by exact_mod_cast hhigh
  have e1 : c - hR = ((cc : ℝ) - hh) / TT := by simp only [hc, hhR]; ring
  have e2 : c + hR = ((cc : ℝ) + hh) / TT := by simp only [hc, hhR]; ring
  have g1 : (-1 : ℝ) ≤ c - hR := by rw [e1, le_div_iff₀ hT]; linarith
  have g2 : c + hR ≤ 1 := by rw [e2, div_le_iff₀ hT]; linarith
  have hyI : ∀ y ∈ Icc (c - hR) (c + hR), |y| ≤ 1 := by
    intro y hy
    rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
  have hsub : Icc (c - hR) (c + hR) ⊆ Icc (-1 : ℝ) 1 :=
    fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  -- the tower
  let fT : ℕ → ℝ → ℝ := fun j => match j with | 0 => F | j + 1 => ftZ D.Z poles j
  have hcontT : ∀ j ≤ m + 1, ContinuousOn (fT j) (Icc (c - hR) (c + hR)) := by
    intro j _
    cases j with
    | zero => exact hFc.mono (fun y hy => ⟨hyI y hy, hne y hy⟩)
    | succ j =>
      intro y hy
      exact (hasDerivAt_ftZ D.Z poles j y (hne y hy)).continuousAt.continuousWithinAt
  have hderT : ∀ j < m + 1, ∀ y ∈ Ioo (c - hR) (c + hR), HasDerivAt (fT j) (fT (j + 1) y) y := by
    intro j _ y hy
    have hyc : y ∈ Icc (c - hR) (c + hR) := ⟨hy.1.le, hy.2.le⟩
    cases j with
    | zero =>
      exact hFd y ⟨by linarith [hy.1], by linarith [hy.2]⟩ (fun p hp => hpe' p hp y hy) (hne y hyc)
    | succ j => exact hasDerivAt_ftZ D.Z poles j y (hne y hyc)
  -- bound on ft m
  have hKm : ∀ y ∈ Icc (c - hR) (c + hR), (SC : ℝ) * |ptZ D.Z m y| ≤ (PB : ℤ) :=
    fun y hy => ptZ_localL D hD cc hh m L MGL hMGL hmLV hh0 hlow hhigh y
      (abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩)
  have hKq : ∀ y ∈ Icc (c - hR) (c + hR),
      (SC : ℝ) * |(poles.map (fun q => qt q m y)).sum| ≤ (MpoleV poles m lo hi : ℤ) := by
    intro y hy
    unfold MpoleV
    refine le_trans (mul_le_mul_of_nonneg_left (abs_list_sum_le poles _) hS.le) ?_
    rw [← List.sum_map_mul_left]
    refine list_sum_le_cast poles _ _ (fun q hq => ?_)
    obtain ⟨hdl, hle⟩ := hgeo y hy q hq
    have hb := qt_bound q m y _ hdl hle
    have hc' := le_qceil (SC * (qabs' q.rr + qabs' q.ri) * ((m ! : ℕ) : ℚ) / (poleDl q lo hi) ^ (m + 1))
    have hcR := (Rat.cast_le (K := ℝ)).mpr hc'
    rw [Rat.cast_intCast] at hcR
    refine le_trans ?_ hcR
    push_cast
    rw [qabs'_cast, qabs'_cast]
    have : (SC : ℝ) * (|(q.rr : ℝ)| + |(q.ri : ℝ)|) * (m ! : ℝ) / (((poleDl q lo hi : ℚ) : ℝ)) ^ (m + 1) =
        (SC : ℝ) * ((|(q.rr : ℝ)| + |(q.ri : ℝ)|) * (m ! : ℝ) / (((poleDl q lo hi : ℚ) : ℝ)) ^ (m + 1)) := by
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hb hS.le
  have hMb : ∀ y ∈ Icc (c - hR) (c + hR),
      |fT (m + 1) y| ≤ ((MpoleV poles m lo hi + PB : ℤ) : ℝ) / SC := by
    intro y hy
    have h1 := hKm y hy
    have h2 := hKq y hy
    rw [le_div_iff₀ hS]
    show |ftZ D.Z poles m y| * SC ≤ _
    unfold ftZ
    have := abs_add_le (ptZ D.Z m y) ((poles.map (fun q => qt q m y)).sum)
    push_cast
    nlinarith [this, mul_le_mul_of_nonneg_left this hS.le]
  have htay := taylor_tower' c hR (((MpoleV poles m lo hi + PB : ℤ) : ℝ) / SC) (m + 1) fT hcontT hderT hMb x hxI
  rw [Finset.sum_range_succ'] at htay
  simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one, div_one] at htay
  set Mre : ℝ := ((MpoleV poles m lo hi + PB : ℤ) : ℝ) / SC with hMre
  set S : ℝ := ∑ j ∈ Finset.range m, ftZ D.Z poles j c * (x - c) ^ (j + 1) / ((j + 1)! : ℝ) with hS'
  have hdx : |x - c| ≤ hR := abs_le.mpr ⟨by linarith [hxI.1], by linarith [hxI.2]⟩
  -- error of fhat
  have herr : ∀ j < m, |(SC : ℝ) * ftZ D.Z poles j c| ≤ |(fhatV D.N poles cc V j : ℝ)| + EcntV poles := by
    intro j hj
    obtain ⟨e1, e2⟩ := fhatV_err D hD poles cc (m + L) j hmLV (by omega)
    have hE : (0 : ℝ) ≤ EcntV poles := by unfold EcntV; positivity
    rw [abs_le]; constructor <;> cases abs_cases (fhatV D.N poles cc V j : ℝ) <;>
      linarith [neg_abs_le (fhatV D.N poles cc V j : ℝ), le_abs_self (fhatV D.N poles cc V j : ℝ)]
  -- bound S
  have hSb : (SC : ℝ) * |S| ≤ (BsumV D.N poles cc hh V m : ℤ) := by
    unfold BsumV
    rw [cast_list_sum_map, list_range_map_sum (fun a => (((cdiv ((zabs (fhatV D.N poles cc V a) + EcntV poles) *
      zpw hh (a + 1)) (tf (a + 1)) : ℤ)) : ℝ))]
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hS.le) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j hjm => ?_)
    have hj : j < m := Finset.mem_range.mp hjm
    have hf : (0 : ℝ) < ((j + 1)! : ℝ) := by positivity
    have hd : (0 : ℤ) < tf (j + 1) := by
      rw [tf_eq (j + 1)]
      have := TT_pos
      positivity
    have hdc' : ((|(fhatV D.N poles cc V j : ℝ)| + EcntV poles) * (hh : ℝ) ^ (j + 1)) /
        ((TT : ℝ) ^ (j + 1) * ((j + 1)! : ℝ)) ≤
        ((cdiv ((zabs (fhatV D.N poles cc V j) + EcntV poles) * zpw hh (j + 1)) (tf (j + 1)) : ℤ) : ℝ) := by
      obtain ⟨Cq, hCq⟩ : ∃ Cq : ℤ, Cq = cdiv ((zabs (fhatV D.N poles cc V j) + EcntV poles) * zpw hh (j + 1))
        (tf (j + 1)) := ⟨_, rfl⟩
      rw [← hCq, div_le_iff₀ (by positivity)]
      have e := cdiv_cast_ge ((zabs (fhatV D.N poles cc V j) + EcntV poles) * zpw hh (j + 1))
        (tf (j + 1)) hd
      rw [← hCq, zpw_eq hh (j + 1) hh0, tf_eq (j + 1)] at e
      push_cast at e
      rw [zabs_cast] at e
      linarith [e]
    have h1 : (SC : ℝ) * |ftZ D.Z poles j c * (x - c) ^ (j + 1) / ((j + 1)! : ℝ)| ≤
        (|(fhatV D.N poles cc V j : ℝ)| + EcntV poles) * (hh : ℝ) ^ (j + 1) /
          ((TT : ℝ) ^ (j + 1) * ((j + 1)! : ℝ)) := by
      rw [abs_div, abs_mul, abs_pow, Nat.abs_cast]
      have e : (SC : ℝ) * (|ftZ D.Z poles j c| * |x - c| ^ (j + 1) / ((j + 1)! : ℝ)) =
          |(SC : ℝ) * ftZ D.Z poles j c| * |x - c| ^ (j + 1) / ((j + 1)! : ℝ) := by
        rw [abs_mul, abs_of_pos hS]; ring
      have hp : |x - c| ^ (j + 1) ≤ hR ^ (j + 1) := pow_le_pow_left₀ (abs_nonneg _) hdx _
      rw [e]
      calc |(SC : ℝ) * ftZ D.Z poles j c| * |x - c| ^ (j + 1) / ((j + 1)! : ℝ)
          ≤ (|(fhatV D.N poles cc V j : ℝ)| + EcntV poles) * hR ^ (j + 1) / ((j + 1)! : ℝ) := by
            apply div_le_div_of_nonneg_right _ hf.le
            exact mul_le_mul (herr j hj) hp (by positivity) (by
              have := abs_nonneg (fhatV D.N poles cc V j : ℝ)
              have : (0 : ℝ) ≤ EcntV poles := by unfold EcntV; positivity
              linarith)
        _ = _ := by
            simp only [hhR]; rw [div_pow]; field_simp
    exact le_trans h1 hdc'
  -- remainder
  have hMn : 0 ≤ Mre := by
    have := (abs_nonneg (fT (m + 1) c)).trans (hMb c hcI)
    exact this
  have hRb : (SC : ℝ) * |F x - (S + F c)| ≤
      (cdiv ((MpoleV poles m lo hi + PB) * zpw hh (m + 1)) (tf (m + 1)) : ℤ) := by
    have hf : (0 : ℝ) < ((m + 1)! : ℝ) := by positivity
    have hd : (0 : ℤ) < tf (m + 1) := by
      rw [tf_eq (m + 1)]
      have := TT_pos
      positivity
    obtain ⟨Cq, hCq⟩ : ∃ Cq : ℤ, Cq = cdiv ((MpoleV poles m lo hi + PB) * zpw hh (m + 1)) (tf (m + 1)) :=
      ⟨_, rfl⟩
    rw [← hCq]
    have hdc := cdiv_cast_ge ((MpoleV poles m lo hi + PB) * zpw hh (m + 1)) (tf (m + 1)) hd
    rw [← hCq, zpw_eq hh (m + 1) hh0, tf_eq (m + 1)] at hdc
    push_cast at hdc
    have hp : |x - c| ^ (m + 1) ≤ hR ^ (m + 1) := pow_le_pow_left₀ (abs_nonneg _) hdx _
    have h2 : |F x - (S + F c)| ≤ Mre * hR ^ (m + 1) / ((m + 1)! : ℝ) := by
      have : |F x - (S + F c)| ≤ Mre * |x - c| ^ (m + 1) / ((m + 1)! : ℝ) := by
        simpa [fT] using htay
      exact this.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hMn) hf.le)
    have h3 : (SC : ℝ) * (Mre * hR ^ (m + 1) / ((m + 1)! : ℝ)) =
        ((MpoleV poles m lo hi + PB : ℤ) : ℝ) * (hh : ℝ) ^ (m + 1) /
          ((TT : ℝ) ^ (m + 1) * ((m + 1)! : ℝ)) := by
      simp only [hMre, hhR]; push_cast; rw [div_pow]; field_simp
    calc (SC : ℝ) * |F x - (S + F c)| ≤ (SC : ℝ) * (Mre * hR ^ (m + 1) / ((m + 1)! : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 hS.le
      _ = _ := h3
      _ ≤ _ := by
          rw [div_le_iff₀ (by positivity)]
          push_cast at hdc ⊢
          linarith [hdc]
  -- the value at the centre
  have hFcv : F c ≤ (ve.1 : ℝ) + ve.2 := by
    have e : (((cc : ℚ) / (TT : ℚ) : ℚ) : ℝ) = c := by simp only [hc]; push_cast; rfl
    have hq : |(((cc : ℚ) / (TT : ℚ) : ℚ) : ℝ)| ≤ 1 := by
      rw [e]; exact hyI c hcI
    have hnp : ∀ p ∈ poles, ((((cc : ℚ) / (TT : ℚ) : ℚ) : ℝ) : ℂ) ≠ p.pc := by
      intro p hp; rw [e]; exact hne c hcI p hp
    have := hev _ ve.1 ve.2 hve hq hnp
    rw [e] at this
    exact this
  have hq1 := le_qceil (SC * (ve.1 + ve.2))
  have hq1R : ((SC * (ve.1 + ve.2) : ℚ) : ℝ) ≤ ((qceil (SC * (ve.1 + ve.2)) : ℤ) : ℝ) := by
    exact_mod_cast hq1
  have hq2 := qfloor_le (SC * cap)
  have hq2R : ((qfloor (SC * cap) : ℤ) : ℝ) ≤ ((SC * cap : ℚ) : ℝ) := by
    have : (((qfloor (SC * cap) : ℤ) : ℚ) : ℝ) ≤ ((SC * cap : ℚ) : ℝ) := by exact_mod_cast hq2
    simpa using this
  have hineqR : ((qceil (SC * (ve.1 + ve.2)) : ℤ) : ℝ) + (BsumV D.N poles cc hh V m : ℤ) +
      (cdiv ((MpoleV poles m lo hi + PB) * zpw hh (m + 1)) (tf (m + 1)) : ℤ) ≤
        ((qfloor (SC * cap) : ℤ) : ℝ) := by exact_mod_cast hineq
  -- conclude
  have hb1 : F x ≤ F c + |S| + |F x - (S + F c)| := by
    have := le_abs_self (F x - (S + F c))
    have := le_abs_self S
    linarith
  have hb2 : (SC : ℝ) * F x ≤ (SC : ℝ) * F c + (SC : ℝ) * |S| + (SC : ℝ) * |F x - (S + F c)| := by
    have := mul_le_mul_of_nonneg_left hb1 hS.le
    nlinarith [this]
  have hb3 : (SC : ℝ) * F c ≤ (SC : ℝ) * ((ve.1 : ℝ) + ve.2) := mul_le_mul_of_nonneg_left hFcv hS.le
  have hb4 : (SC : ℝ) * ((ve.1 : ℝ) + ve.2) = ((SC * (ve.1 + ve.2) : ℚ) : ℝ) := by push_cast; ring
  have hb5 : ((SC * cap : ℚ) : ℝ) = (SC : ℝ) * cap := by push_cast; ring
  have : (SC : ℝ) * F x ≤ (SC : ℝ) * cap := by linarith
  exact le_of_mul_le_mul_left this hS



/-- BlockSup: a Taylor tower at a block `[cB-HB, cB+HB]` bounds `SC |P^(m')|` on every sub-cell. -/
theorem block_sup (D : PolyData) (hD : D.Ok) (cB HB cc hh : ℤ) (m' LB : ℕ) (MGL BB : ℤ)
    (hMGL : ∀ y : ℝ, |y| ≤ 1 → (SC : ℝ) * |ptZ D.Z (m' + LB) y| ≤ (MGL : ℝ))
    (hm : m' + LB ≤ D.LV.length) (hH0 : 0 ≤ HB) (hlow : -TT ≤ cB - HB) (hhigh : cB + HB ≤ TT)
    (hcell : |cc - cB| + hh ≤ HB)
    (hBB : PbV D.N cB HB (polyValsD D cB (m' + LB)) m' LB MGL ≤ BB) :
    ∀ y : ℝ, |y - (cc : ℝ) / TT| ≤ (hh : ℝ) / TT → (SC : ℝ) * |ptZ D.Z m' y| ≤ (BB : ℝ) := by
  intro y hy
  have hT : (0 : ℝ) < TT := by exact_mod_cast TT_pos
  have hc : (|cc - cB| : ℤ) + hh ≤ HB := hcell
  have hcR : (|((cc : ℝ) - cB)|) + hh ≤ HB := by exact_mod_cast hc
  have hy' : |y - (cB : ℝ) / TT| ≤ (HB : ℝ) / TT := by
    have h1 : |y - (cB : ℝ) / TT| ≤ |y - (cc : ℝ) / TT| + |((cc : ℝ) - cB)| / TT := by
      have : y - (cB : ℝ) / TT = (y - (cc : ℝ) / TT) + ((cc : ℝ) - cB) / TT := by ring
      rw [this]
      calc _ ≤ |y - (cc : ℝ) / TT| + |((cc : ℝ) - cB) / TT| := abs_add_le _ _
        _ = _ := by rw [abs_div, abs_of_pos hT]
    have h2 : |y - (cc : ℝ) / TT| ≤ (hh : ℝ) / TT := hy
    calc _ ≤ (hh : ℝ) / TT + |((cc : ℝ) - cB)| / TT := by linarith
      _ = (|((cc : ℝ) - cB)| + hh) / TT := by ring
      _ ≤ (HB : ℝ) / TT := by gcongr
  have := ptZ_local D hD cB HB m' LB MGL hMGL hm hH0 hlow hhigh y hy'
  have hB : ((PbV D.N cB HB (polyValsD D cB (m' + LB)) m' LB MGL : ℤ) : ℝ) ≤ (BB : ℝ) := by
    exact_mod_cast hBB
  linarith

end CatalanMeasure.CellCert

#print axioms CatalanMeasure.CellCert.block_sup
#print axioms CatalanMeasure.CellCert.cellVal_soundL
