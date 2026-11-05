module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.LinkSupXg
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.LinkSupXs
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.LinkSupLim
public import Submission.CatalanMeasure.GenD.D58.OddProfile

@[expose] public section

/-!
# D2 constants: `LinkCert.hgap` and `LinkCert.hsup` of the K590 free field

Window sups of the K590 limit row field `rowFieldG (11/29) (3/29) (39/29) U V`
(`U = trialSeqS Pc P`, `V = trialSeqS Vc V`, the `Cert590` data), at finite `N` by
`LinkSupLim.link_cap_of_region`:

* gap window `0 < |x| < 7/100`: limit field `≤ MX - 41/1000`, so `hgap` holds with `dgap = 1/25`;
* spike window `(1 - 1/1000, 1)`: limit field `≤ MX - 289/2000`, so `hsup` holds with `dsp = 18/125`.

`link_hgap_K590`, `link_hsup_K590` are stated for any admissible `P` with the three row weights
`11/29, 3/29, 39/29`; `link_hgap_odd`, `link_hsup_odd` for `Odd.design`.  `D0.p`, `D0.v`, `D0.MX`
of the K590 trial are `trialSeqS Pc P`, `trialSeqS Vc V`, `(Cert590.MX : ℝ)` (`TrialFields`).
-/

namespace CatalanMeasure.Signed.Consts
open CatalanMeasure.CellCert CatalanMeasure.Cert CatalanMeasure.GenD.D58.Cert590 CatalanMeasure.GenD
  CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric OAI.InternalCatalan Set Filter
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem sound_X' (t : ℕ) : (rowSpecW R Pc Vc P V t).Sound D_X.toD (rowFieldS R Pc Vc P V) :=
  rowSpecW_sound R tailsP tailsV P_nonzero V_nonzero D_X.toD hZ_X (by norm_num [R]) (by norm_num [R]) t

theorem TT_real' : ((TT : ℤ) : ℝ) = 1099511627776 := by unfold TT; norm_num

theorem peel_pt_X' (t : ℕ) (pr : ℚ × ℚ) (h : rowPeel R t = some pr) : pr.2 = 0 ∨ pr.2 = 1 := by
  unfold rowPeel at h
  split at h <;> first | (cases h; simp) | simp_all

theorem cover_Gn : coverFrom 0 (-82587648064) (blocksCells [LGn]) = true := by decide +kernel
theorem cover_Gp : coverFrom (7 / 100) 0 (blocksCells [LGp0, LGp1, LGp2]) = true := by decide +kernel
theorem cover_S : coverFrom 1 1098400434566 (blocksCells [LS0, LS1]) = true := by decide +kernel

theorem rowS_eq_G : rowFieldS R Pc Vc P V =
    rowFieldG (11 / 29) (3 / 29) (39 / 29) (trialSeqS Pc P) (trialSeqS Vc V) := by
  unfold rowFieldS; norm_num [R]

theorem gap_neg_S : ∀ x : ℝ, -(7 / 100 : ℝ) < x → x < 0 → rowFieldS R Pc Vc P V x ≤ (capG : ℝ) := by
  intro x h1 h2
  refine field_le_of_blocks _ (rowSpecW R Pc Vc P V) D_X.toD D_X_ok 5 65 MGL_X hMGL_X capG [LGn]
    (fun c _ => sound_X' c.2.2) (-82587648064) 0 cover_Gn
    (by intro b hb; simp only [List.mem_singleton] at hb; subst hb; exact LGn_ok) x ?_ ?_ ?_
  · rw [TT_real', div_le_iff₀ (by norm_num)]; push_cast; linarith
  · simpa using h2.le
  · intro c _ pr h
    rcases peel_pt_X' c.2.2 pr h with h0 | h1'
    · rw [h0]; simpa using h2.ne
    · rw [h1']; simp; linarith

theorem gap_pos_S : ∀ x : ℝ, 0 < x → x < 7 / 100 → rowFieldS R Pc Vc P V x ≤ (capG : ℝ) := by
  intro x h1 h2
  refine field_le_of_blocks _ (rowSpecW R Pc Vc P V) D_X.toD D_X_ok 5 65 MGL_X hMGL_X capG
    [LGp0, LGp1, LGp2] (fun c _ => sound_X' c.2.2) 0 (7 / 100) cover_Gp
    (by
      intro b hb
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact LGp0_ok
      · exact LGp1_ok
      · exact LGp2_ok) x ?_ ?_ ?_
  · simpa using h1.le
  · push_cast; exact h2.le
  · intro c _ pr h
    rcases peel_pt_X' c.2.2 pr h with h0 | h1'
    · rw [h0]; simpa using h1.ne'
    · rw [h1']; simp; linarith

theorem spike_S : ∀ x : ℝ, 999 / 1000 < x → x < 1 → rowFieldS R Pc Vc P V x ≤ (capS : ℝ) := by
  intro x h1 h2
  refine field_le_of_blocks _ (rowSpecW R Pc Vc P V) D_X.toD D_X_ok 5 65 MGL_X hMGL_X capS
    [LS0, LS1] (fun c _ => sound_X' c.2.2) 1098400434566 1 cover_S
    (by
      intro b hb
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl
      · exact LS0_ok
      · exact LS1_ok) x ?_ ?_ ?_
  · rw [TT_real', div_le_iff₀ (by norm_num)]; push_cast; linarith
  · push_cast; exact h2.le
  · intro c _ pr h
    rcases peel_pt_X' c.2.2 pr h with h0 | h1'
    · rw [h0]; simp; linarith
    · rw [h1']; simp; linarith

theorem capG_real : (capG : ℝ) = ((MX : ℚ) : ℝ) - 41 / 1000 := by unfold capG; push_cast; ring
theorem capS_real : (capS : ℝ) = ((MX : ℚ) : ℝ) - 289 / 2000 := by unfold capS; push_cast; ring

/-- The K590 limit field is `≤ MX - 41/1000` on `0 < |x| < 7/100`. -/
theorem gap_limit : ∀ x ∈ {x : ℝ | 0 < |x| ∧ |x| < 7 / 100},
    rowFieldG (11 / 29) (3 / 29) (39 / 29) (trialSeqS Pc P) (trialSeqS Vc V) x ≤
      ((MX : ℚ) : ℝ) - 41 / 1000 := by
  rintro x ⟨h0, h1⟩
  rw [← rowS_eq_G, ← capG_real]
  rcases lt_trichotomy x 0 with h | h | h
  · exact gap_neg_S x (by rw [abs_of_neg h] at h1; linarith) h
  · subst h; simp at h0
  · exact gap_pos_S x h (by rw [abs_of_pos h] at h1; exact h1)

theorem spike_limit : ∀ x ∈ Ioo (1 - 1 / 1000 : ℝ) 1,
    rowFieldG (11 / 29) (3 / 29) (39 / 29) (trialSeqS Pc P) (trialSeqS Vc V) x ≤
      ((MX : ℚ) : ℝ) - 289 / 2000 := by
  rintro x ⟨h1, h2⟩
  rw [← rowS_eq_G, ← capS_real]
  exact spike_S x (by linarith) h2

theorem gap_sub : {x : ℝ | 0 < |x| ∧ |x| < 7 / 100} ⊆ Ico (-1 : ℝ) 0 ∪ Ioo 0 1 := by
  rintro x ⟨h0, h1⟩
  rcases lt_or_gt_of_ne (abs_pos.mp h0) with h | h
  · left; rw [abs_of_neg h] at h1; exact ⟨by linarith, h⟩
  · right; rw [abs_of_pos h] at h1; exact ⟨h, by linarith⟩

theorem spike_sub : Ioo (1 - 1 / 1000 : ℝ) 1 ⊆ Ico (-1 : ℝ) 0 ∪ Ioo 0 1 :=
  fun x hx => Or.inr ⟨by linarith [hx.1], hx.2⟩

/-- **`LinkCert.hgap`** for the K590 free field: `a0 = 7/100`, `dgap = 1/25`. -/
theorem link_hgap_K590 {P : Parameters} (hP : Admissible P)
    (hα : (11 / 29 : ℝ) = ((P.b0 : ℝ) + P.q0 + 2 * P.g0) / P.n0)
    (hβ : (3 / 29 : ℝ) = 2 * (P.h0 : ℝ) / P.n0)
    (hγ : (39 / 29 : ℝ) = ((P.n0 : ℝ) + P.b0 + P.q0 + P.g0 + P.h0) / P.n0) {δ : ℝ} (hδ : 0 ≤ δ)
    {p v : ℕ → ℝ} (hp : p = trialSeqS Pc CatalanMeasure.GenD.D58.Cert590.P)
    (hv : v = trialSeqS Vc V) {MXr : ℝ} (hM : MXr = ((MX : ℚ) : ℝ)) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, 0 < |x| → |x| < 7 / 100 →
      freeRowX P N p v x ≤ MXr + δ / 4 - 1 / 25 := by
  subst hp hv hM
  have := link_cap_of_region hP (trialSeqS_summable tailsP).1 (trialSeqS_summable tailsV).1 hα hβ hγ
    gap_sub gap_limit (d := 1 / 25) (by norm_num) hδ
  filter_upwards [this] with N hN x h0 h1 using hN x ⟨h0, h1⟩

/-- **`LinkCert.hsup`** for the K590 free field: `θ0 = 1/1000`, `dsp = 18/125`. -/
theorem link_hsup_K590 {P : Parameters} (hP : Admissible P)
    (hα : (11 / 29 : ℝ) = ((P.b0 : ℝ) + P.q0 + 2 * P.g0) / P.n0)
    (hβ : (3 / 29 : ℝ) = 2 * (P.h0 : ℝ) / P.n0)
    (hγ : (39 / 29 : ℝ) = ((P.n0 : ℝ) + P.b0 + P.q0 + P.g0 + P.h0) / P.n0) {δ : ℝ} (hδ : 0 ≤ δ)
    {p v : ℕ → ℝ} (hp : p = trialSeqS Pc CatalanMeasure.GenD.D58.Cert590.P)
    (hv : v = trialSeqS Vc V) {MXr : ℝ} (hM : MXr = ((MX : ℚ) : ℝ)) :
    ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (1 - 1 / 1000 : ℝ) 1,
      freeRowX P N p v x ≤ MXr + δ / 4 - 18 / 125 := by
  subst hp hv hM
  exact link_cap_of_region hP (trialSeqS_summable tailsP).1 (trialSeqS_summable tailsV).1 hα hβ hγ
    spike_sub spike_limit (d := 18 / 125) (by norm_num) hδ

theorem link_hgap_odd {δ : ℝ} (hδ : 0 ≤ δ) {p v : ℕ → ℝ}
    (hp : p = trialSeqS Pc CatalanMeasure.GenD.D58.Cert590.P) (hv : v = trialSeqS Vc V) {MXr : ℝ}
    (hM : MXr = ((MX : ℚ) : ℝ)) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, 0 < |x| → |x| < 7 / 100 →
      freeRowX D58.Odd.design N p v x ≤ MXr + δ / 4 - 1 / 25 :=
  link_hgap_K590 D58.Odd.design_admissible (by norm_num [D58.Odd.design])
    (by norm_num [D58.Odd.design]) (by norm_num [D58.Odd.design]) hδ hp hv hM

theorem link_hsup_odd {δ : ℝ} (hδ : 0 ≤ δ) {p v : ℕ → ℝ}
    (hp : p = trialSeqS Pc CatalanMeasure.GenD.D58.Cert590.P) (hv : v = trialSeqS Vc V) {MXr : ℝ}
    (hM : MXr = ((MX : ℚ) : ℝ)) :
    ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (1 - 1 / 1000 : ℝ) 1,
      freeRowX D58.Odd.design N p v x ≤ MXr + δ / 4 - 18 / 125 :=
  link_hsup_K590 D58.Odd.design_admissible (by norm_num [D58.Odd.design])
    (by norm_num [D58.Odd.design]) (by norm_num [D58.Odd.design]) hδ hp hv hM

end CatalanMeasure.Signed.Consts

#print axioms CatalanMeasure.Signed.Consts.link_hgap_odd
#print axioms CatalanMeasure.Signed.Consts.link_hsup_odd
