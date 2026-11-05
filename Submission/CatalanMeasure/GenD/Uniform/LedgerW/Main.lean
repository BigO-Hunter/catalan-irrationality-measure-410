module

public import Submission.CatalanMeasure.GenD.Uniform.LedgerW.Growth

@[expose] public section

/-!
# `D_growth_of_nullityLB` (lane G4)

The design-generic `D_growth` for the canonical normalizer of any `NullityLB`.
-/

namespace CatalanMeasure.GenD.Uniform.LedgerW

open CatalanMeasure.Parametric OAI.InternalCatalan Filter
open CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.Arithmetic
open scoped Topology BigOperators

noncomputable section

theorem one_lt_H1 (P : Parameters) (hP : Admissible P) : 1 < P.H 1 := by
  have hn := hP.1
  have hb := hP.2.1
  have hq := hP.2.2.1
  simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b,
    Parameters.q, Parameters.g, Parameters.h, Nat.mul_one]
  omega

/-- **Denominator growth from a nullity profile.**  For every admissible design `P`, every
nullity lower bound `lb` (for instance `NullityLB.supList` of the W families), and finitely many
ordered positive windows (disjoint from the recycling band `1 < x <= 2`) carrying PL lower
profiles of `kap` (up to a finitely supported exceptional charge) and of the safe pool, the
canonical normalizer satisfies `log D_N <= (gD + eps) N^2` eventually. -/
theorem D_growth_of_nullityLB (P : Parameters) (hP : Admissible P) (lb : NullityLB P)
    (N0 : ℕ) (hN0 : P.H 1 < N0)
    (f : PL.Prof) (κ0 : ℝ)
    (hloss : ∀ N p : ℕ, 0 < N → p ≤ P.H N →
      (safeOddLoss P N p : ℝ) ≤ N * f.eval ((p : ℝ) / N))
    (hf0 : ∀ x : ℝ, x ≤ 1 → f.eval x = κ0)
    (charge : ℕ → ℕ → ℕ) (E : ℕ → Finset ℕ) (M : ℕ) (cch : ℝ) (hcch : 0 ≤ cch)
    (hE : ∀ N, (E N).card ≤ M) (hsupport : ∀ N p, p ∉ E N → charge N p = 0)
    (hcharge : ∀ N p, (charge N p : ℝ) ≤ cch * N)
    (ws : List KapWindow) (c : ℝ) (hc : 0 ≤ c)
    (hpos : ∀ w ∈ ws, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ (P.H 1 : ℝ))
    (hord : ws.Pairwise (fun s t => s.b ≤ t.a))
    (hrec : ∀ w ∈ ws, w.b ≤ 1 ∨ 2 ≤ w.a)
    (hcert : ∀ w ∈ ws, ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, p.Prime → w.a * N < p →
      (p : ℝ) ≤ w.b * N →
        (N : ℝ) * w.K.eval ((p : ℝ) / N) - c ≤ (lb.kap N p : ℝ) + charge N p ∧
        (N : ℝ) * w.G.eval ((p : ℝ) / N) - c ≤ (safeOddLoss P N p : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (((canonicalNormalizer P hP lb N0 hN0).D N : ℕ) : ℝ) ≤
        (gD P f κ0 ws + ε) * (N : ℝ) ^ 2 := by
  have hH1 := one_lt_H1 P hP
  have hH1R : (1 : ℝ) ≤ (P.H 1 : ℝ) := by exact_mod_cast hH1.le
  have hseg : ∀ s ∈ ws.map (KapWindow.seg (P.n0 : ℝ)),
      WindowGrowth.GoodEventually
        (fun N p => saving P (recyclingSafeLB P lb) N p + ⌈2 * c⌉₊ + charge N p) s := by
    intro s hs
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hs
    obtain ⟨ha, hab, hb⟩ := hpos w hw
    refine ⟨ha, hab, KapWindow.seg_continuousOn _ w, ?_⟩
    filter_upwards [hcert w hw, Arithmetic.window_in_oddBranch_eventually P ha (hb.trans le_rfl),
      eventually_gt_atTop (0 : ℕ)] with N hcN hodd hN
    intro p hp h1 h2
    have h1 : w.a * N < p := h1
    have h2 : (p : ℝ) ≤ w.b * N := h2
    obtain ⟨hp2, hsq, -⟩ := hodd p hp h1 h2
    obtain ⟨hK, hG⟩ := hcN p hp h1 h2
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hnb : ¬ (N < p ∧ p ≤ 2 * N) := by
      rintro ⟨hl, hu⟩
      rcases hrec w hw with hr | hr
      · have : (p : ℝ) ≤ N := by
          have := mul_le_mul_of_nonneg_right hr hNR.le
          linarith only [h2, this]
        have : N < p := hl
        have h3 : (N : ℝ) < p := by exact_mod_cast this
        linarith
      · have h3 : (p : ℝ) ≤ 2 * N := by exact_mod_cast hu
        have := mul_le_mul_of_nonneg_right hr hNR.le
        linarith only [h1, h3, this]
    have hk := recyclingSafeLB_kap_of_not_band P lb hnb
    have hsv := saving_window_cert P (recyclingSafeLB P lb) hN hp hp2 hsq
      (w.K.eval ((p : ℝ) / N)) (w.G.eval ((p : ℝ) / N)) c hc (charge N p)
      (by rw [hk]; exact hK) hG
    have : (N : ℝ) * (w.seg (P.n0 : ℝ)).F ((p : ℝ) / N) - 1 ≤
        (saving P (recyclingSafeLB P lb) N p : ℝ) + (⌈2 * c⌉₊ : ℝ) + charge N p := by
      simpa [KapWindow.seg] using hsv
    exact_mod_cast this
  have hord' : (ws.map (KapWindow.seg (P.n0 : ℝ))).Pairwise (fun s t => s.b ≤ t.a) := by
    rw [List.pairwise_map]
    exact hord
  have hwin : ∀ᶠ N : ℕ in atTop, ∀ s ∈ ws.map (KapWindow.seg (P.n0 : ℝ)), ∀ p : ℕ, p.Prime →
      s.a * N < p → (p : ℝ) ≤ s.b * N → p ≠ 2 ∧ P.H N < p ^ 2 ∧ p ≤ P.H N := by
    have hfin : {s | s ∈ ws.map (KapWindow.seg (P.n0 : ℝ))}.Finite := List.finite_toSet _
    refine (Filter.eventually_all_finite hfin).mpr ?_
    intro s hs
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hs
    obtain ⟨ha, hab, hb⟩ := hpos w hw
    exact Arithmetic.window_in_oddBranch_eventually P ha hb
  have key := denom_growth_corrected P hP (recyclingSafeLB P lb) f
    (ws.map (KapWindow.seg (P.n0 : ℝ))) κ0 ⌈2 * c⌉₊ hloss hf0 hH1 charge E M cch hcch hE hsupport
    hcharge hseg hord' hwin hε
  have hint : ∫ x in (1 : ℝ)..(P.H 1 : ℝ), f.eval x = f.area 1 (P.H 1 : ℝ) :=
    f.integral_eval hH1R
  have hareas := totalArea_kapSegs (P.n0 : ℝ) ws (fun w hw => (hpos w hw).2.1.le)
  filter_upwards [key] with N hN
  rw [hint, hareas] at hN
  unfold gD
  exact hN

end

end CatalanMeasure.GenD.Uniform.LedgerW
