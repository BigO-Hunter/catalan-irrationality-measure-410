module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts5.Cover2
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.W.Charts5
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Prof.Pilot146
  CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O CatalanMeasure.GenD.D58.Odd CatalanMeasure.Parametric
  CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Charts Finset
noncomputable section
variable {N p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

theorem lt_wNatO {k : ℕ} (g : ℕ) (hg : g < 11) (hk : k < wd N p g) :
    k < wNatO (⟨g, by rw [packetO_len]; exact hg⟩ : Fin packetO.charts.length) N p := hk

theorem jet1_eq (hW : Win N p) (e : Fin p) (he : e.val < wd N p 1) :
    (fun (g : Fin packetO.charts.length) (k : Fin (wNatO g N p)) => jetP N p g.val k.val)
      ⟨1, by rw [packetO_len]; norm_num⟩ ⟨e.val, he⟩ = LinearMap.proj e := by
  show jetP N p 1 e.val = _
  simp only [jetP]; exact jet0_eq _ e rfl

theorem jet2_eq (hW : Win N p) (e : Fin p) (he : wd N p 1 ≤ e.val) (he2 : e.val - wd N p 1 < wd N p 2) :
    (fun (g : Fin packetO.charts.length) (k : Fin (wNatO g N p)) => jetP N p g.val k.val)
      ⟨2, by rw [packetO_len]; norm_num⟩ ⟨e.val - wd N p 1, lt_wNatO _ (by norm_num) he2⟩ = LinearMap.proj e := by
  show jetP N p 2 (e.val - wd N p 1) = _
  simp only [jetP]; exact jet0_eq _ e (by omega)

theorem jet6_eq (hW : Win N p) (e : Fin p) (he : p - 1 - e.val < wd N p 6) :
    (fun (g : Fin packetO.charts.length) (k : Fin (wNatO g N p)) => jetP N p g.val k.val)
      ⟨6, by rw [packetO_len]; norm_num⟩ ⟨p - 1 - e.val, lt_wNatO _ (by norm_num) he⟩ = LinearMap.proj e := by
  show jetP N p 6 (p - 1 - e.val) = _
  simp only [jetP]; exact jetInf_eq _ e rfl

theorem jetS_eq (e : Fin p) (g k : ℕ) (hg : g < 11) (hk : k < wd N p g)
    (h : jetP N p g k = LinearMap.proj e) :
    (fun (g : Fin packetO.charts.length) (k : Fin (wNatO g N p)) => jetP N p g.val k.val)
      ⟨g, by rw [packetO_len]; exact hg⟩ ⟨k, lt_wNatO _ hg hk⟩ = LinearMap.proj e := h

theorem cover_pilot (hW : Win N p) (M : MonoData design N p packetO.n) (hM : pd146.Realises M.prof) :
    CoverPt2 packetO M (low146 p) (fun g => wNatO g N p) (design.q N / p)
      (fun g k => jetP N p g.val k.val) := by
  have hN := hW.1; have hp6 := hW.2.1; have hp152 := hW.2.2.1
  have hp13 : 13 < p := by omega
  have hq0 : design.q N / p = 0 := geom_qdiv hW
  have hH : design.H N = 78 * N := Pilot146O.design_H N
  have w1 := wd1 hW; have w2 := wd2 hW; have w6 := wd6 hW
  have hpne : (p : ℤ) ≠ 0 := by have := (Fact.out : p.Prime).pos; omega
  unfold CoverPt2
  intro j hj1 hj2 e hdvd
  rw [hq0] at hj2 ⊢
  rw [design_b] at hj1
  rw [design_L] at hj2
  have hj2' : j < 70 * N := by omega
  obtain ⟨s, hs0⟩ := hdvd
  have hs := hs0
  rw [hH] at hs
  have hjl : p * (j / p) + j % p = j := Nat.div_add_mod j p
  have hl : j % p < p := Nat.mod_lt _ (Fact.out : p.Prime).pos
  generalize j / p = J at hjl ⊢
  generalize j % p = l at hjl hl hs0 hs ⊢
  have he := e.isLt
  have hpz : (0 : ℤ) ≤ p := by positivity
  have hJ12 : J < 12 := by
    by_contra h; push_neg at h
    have := Nat.mul_le_mul_left p h; omega
  have hJ1 : 1 ≤ J := by
    by_contra h
    have h0 : J = 0 := by omega
    rw [h0] at hjl; omega
  have hs13 : s ≤ 12 := by
    by_contra h; push_neg at h
    have := Int.mul_le_mul_of_nonneg_left (show (13:ℤ) ≤ s by omega) hpz
    omega
  have hs11 : 11 ≤ s := by
    by_contra h; push_neg at h
    have := Int.mul_le_mul_of_nonneg_left (show s ≤ 10 by omega) hpz
    omega
  have fin : ∀ (S : ℤ) (y : Fin packetO.d → Fp),
      M.sys.prof.psi (design.H N) (J) S (emb packetO p packetO.n y) = emb packetO p 44 y 42 →
      ∑ v ∈ range (0 + 1), ((-1 : ZMod p) ^ (0 - v) * ((Nat.choose 0 v : ℕ) : ZMod p)) *
        M.sys.prof.psi (design.H N) (J + v) S (emb packetO p packetO.n y) = low146 p y := by
    intro S y h; simp [low146_apply, h]
  have hden : ((design.H N : ℤ) - 1 - ((l : ℕ) : ℤ) - (e : ℕ)) / (p : ℤ) = s := by
    rw [hs0, Int.mul_ediv_cancel_left _ hpne]
  have hs12 : s = 11 ∨ s = 12 := by omega
  rcases hs12 with h11 | h12
  · -- S = 11 : group 6, reversed jet
    subst h11
    have hJ10 : J ≤ 10 := by
      by_contra h; push_neg at h
      have := Nat.mul_le_mul_left p (show 11 ≤ J by omega); omega
    have hk6 : p - 1 - e.val < wd N p 6 := by omega
    refine ⟨⟨6, by rw [packetO_len]; norm_num⟩, ⟨p - 1 - e.val, lt_wNatO _ (by norm_num) hk6⟩,
      ⟨6, by rw [packetO_len]; norm_num⟩, ⟨p - 1 - e.val, lt_wNatO _ (by norm_num) hk6⟩,
      jet6_eq hW e hk6, jet6_eq hW e hk6, ?_⟩
    intro y hy _
    rw [hden]
    apply fin
    have hok := rows_ok.2.2.2.2.2 ⟨J - 1, by omega⟩
    simp only [show J - 1 + 1 = J by omega] at hok
    rw [cover_row M hM hp13 (g := 6) (i := J - 1) (J := J) (S := 11) (ε := 0) (by norm_num) hok
      (by omega) (by norm_num) (by rw [hH]; omega) y hy]
    simp
  · -- S = 12
    subst h12
    by_cases hJ11 : J = 11
    · have helo : 8 * N - p ≤ e.val := by rw [hJ11] at hjl; omega
      have hew2 : e.val < wd N p 1 + wd N p 2 := by omega
      obtain ⟨g', k', hg', hk', hjet', hrow'⟩ := slack_jet hW e helo
      by_cases hew : e.val < wd N p 1
      · refine ⟨⟨1, by rw [packetO_len]; norm_num⟩, ⟨e.val, lt_wNatO _ (by norm_num) hew⟩,
          ⟨g', by rw [packetO_len]; exact hg'⟩, ⟨k', lt_wNatO _ hg' hk'⟩,
          jet1_eq hW e hew, jetS_eq e g' k' hg' hk' hjet', ?_⟩
        intro y hy hy'
        rw [hden]
        apply fin
        rw [hJ11]
        rw [cover_row M hM hp13 (g := 1) (i := 10) (J := 11) (S := 12) (ε := 1) (by norm_num)
          rows_ok.2.2.2.1 (by norm_num) (by norm_num) (by rw [hH]; omega) y hy,
          chart_unit43 g' hg' hrow' y hy']
        simp
      · refine ⟨⟨2, by rw [packetO_len]; norm_num⟩, ⟨e.val - wd N p 1, lt_wNatO _ (by norm_num) (by omega)⟩,
          ⟨g', by rw [packetO_len]; exact hg'⟩, ⟨k', lt_wNatO _ hg' hk'⟩,
          jet2_eq hW e (by omega) (by omega), jetS_eq e g' k' hg' hk' hjet', ?_⟩
        intro y hy hy'
        rw [hden]
        apply fin
        rw [hJ11]
        rw [cover_row M hM hp13 (g := 2) (i := 9) (J := 11) (S := 12) (ε := 1) (by norm_num)
          rows_ok.2.2.2.2.1 (by norm_num) (by norm_num) (by rw [hH]; omega) y hy,
          chart_unit43 g' hg' hrow' y hy']
        simp
    · have hJ10 : J ≤ 10 := by omega
      by_cases hJ1' : J = 1
      · have hew : e.val < wd N p 1 := by rw [hJ1'] at hjl; omega
        refine ⟨⟨1, by rw [packetO_len]; norm_num⟩, ⟨e.val, lt_wNatO _ (by norm_num) hew⟩,
          ⟨1, by rw [packetO_len]; norm_num⟩, ⟨e.val, lt_wNatO _ (by norm_num) hew⟩,
          jet1_eq hW e hew, jet1_eq hW e hew, ?_⟩
        intro y hy _
        rw [hden]
        apply fin
        rw [hJ1']
        rw [cover_row M hM hp13 (g := 1) (i := 0) (J := 1) (S := 12) (ε := 0) (by norm_num)
          rows_ok.1 (by norm_num) (by norm_num) (by rw [hH]; omega) y hy]
        simp
      · by_cases hew : e.val < wd N p 1
        · refine ⟨⟨1, by rw [packetO_len]; norm_num⟩, ⟨e.val, lt_wNatO _ (by norm_num) hew⟩,
            ⟨1, by rw [packetO_len]; norm_num⟩, ⟨e.val, lt_wNatO _ (by norm_num) hew⟩,
            jet1_eq hW e hew, jet1_eq hW e hew, ?_⟩
          intro y hy _
          rw [hden]
          apply fin
          have hok := rows_ok.2.2.1 ⟨J - 2, by omega⟩
          simp only [show J - 2 + 2 = J by omega] at hok
          rw [cover_row M hM hp13 (g := 1) (i := J - 2 + 1) (J := J) (S := 12) (ε := 0)
            (by norm_num) hok (by omega) (by norm_num) (by rw [hH]; omega) y hy]
          simp
        · refine ⟨⟨2, by rw [packetO_len]; norm_num⟩, ⟨e.val - wd N p 1, lt_wNatO _ (by norm_num) (by omega)⟩,
            ⟨2, by rw [packetO_len]; norm_num⟩, ⟨e.val - wd N p 1, lt_wNatO _ (by norm_num) (by omega)⟩,
            jet2_eq hW e (by omega) (by omega), jet2_eq hW e (by omega) (by omega), ?_⟩
          intro y hy _
          rw [hden]
          apply fin
          have hok := rows_ok.2.1 ⟨J - 2, by omega⟩
          simp only [show J - 2 + 2 = J by omega] at hok
          rw [cover_row M hM hp13 (g := 2) (i := J - 2) (J := J) (S := 12) (ε := 0)
            (by norm_num) hok (by omega) (by norm_num) (by rw [hH]; omega) y hy]
          simp

end
end CatalanMeasure.GenD.Uniform.W.Charts5
