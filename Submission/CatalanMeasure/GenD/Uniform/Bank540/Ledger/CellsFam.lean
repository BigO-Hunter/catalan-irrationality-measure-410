module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger.CellsHP
public import Submission.CatalanMeasure.GenD.Uniform.W.Thin.Combine
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsA.LB
public import Submission.CatalanMeasure.GenD.Uniform.W.FrobInst.CBank

@[expose] public section
set_option Elab.async false

/-!
# Cell certificates: T-raw tail, family A, Frobenius product (lane G5c)

* `tail_cell`  : the T-raw tail, `K = x - 16` on `(16, 118/7]`.
* `A_cell`     : family A (truncated U6g), `K = 5x - 59` on `(59/5, 12]`.
* `frobLB`     : the Frobenius-product bank on the cell `26 N < p`, `2p + 2 <= 53 N`
                 (`K = 3`, `lo = 0`, `k0 = 0`, `dP + 1 = 53 N - 2p - 1`); `seen_card` is the
                 `seen ⊆ {(0,2),(1,2)}` lemma (|seen| <= 2) and `frob_cell` the certificate
                 `K = 53 - 2x` on `(26, 53/2)`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger
open CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Thin
  CatalanMeasure.GenD.Uniform.W.SlotsA CatalanMeasure.GenD.Uniform.W.FrobInst
noncomputable section

abbrev adm : Admissible design := D58.Odd.design_admissible

theorem tail_app {N p : ℕ} (hN : 100 ≤ N) (h1 : 16 * N < p) (h2 : 7 * p ≤ 118 * N) :
    TTailApp design N p := by
  unfold TTailApp
  des_unfold
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem tail_cell {N p : ℕ} (hN : 100 ≤ N) (h1 : 16 * N < p) (h2 : 7 * p ≤ 118 * N) :
    (-16 : ℤ) * N + 1 * p ≤ 1 * (((tTailLB design adm).kap N p : ℕ) : ℤ) + 2 := by
  have hA := tail_app hN h1 h2
  have hk : (tTailLB design adm).kap N p = tTailVal design N p := by
    simp [tTailLB, NullityLB.ofWindow, hA]
  rw [hk]
  unfold tTailVal
  des_unfold
  omega

theorem A_app {N p : ℕ} (hN : 100 ≤ N) (h1 : 59 * N < 5 * p) (h2 : p ≤ 12 * N) :
    aApp design N p := by
  unfold aApp uM0
  des_unfold
  refine ⟨?_, ?_⟩ <;> omega

theorem A_cell {N p : ℕ} (hN : 100 ≤ N) (h1 : 59 * N < 5 * p) (h2 : p ≤ 12 * N) :
    (-59 : ℤ) * N + 5 * p ≤ 1 * (((aLB design adm).kap N p : ℕ) : ℤ) + 2 := by
  have hA := A_app hN h1 h2
  have hk : (aLB design adm).kap N p = aVal design N p := by
    simp [aLB, NullityLB.ofWindow, hA]
  rw [hk]
  unfold aVal uM1 uM0 sE
  des_unfold
  omega

/-! ### Frobenius product on the cell `26 N < p`, `2p + 2 <= 53 N` -/

def frobApp (N p : ℕ) : Prop := 26 * N < p ∧ 2 * p + 2 ≤ 53 * N

def frobVal (N p : ℕ) : ℕ := 53 * N - 2 * p - 1

theorem seen_card {N p : ℕ} (h1 : 26 * N < p) (h2 : 2 * p + 2 ≤ 53 * N) :
    (seenSet design N p 0 (0 + (53 * N - 2 * p - 2 + 1))).card ≤ 2 := by
  have hp0 : 0 < p := by omega
  have hp0' : (0 : ℤ) < p := by exact_mod_cast hp0
  have hsub : seenSet design N p 0 (0 + (53 * N - 2 * p - 2 + 1)) ⊆
      ({(0, 2), (1, 2)} : Finset (ℕ × ℤ)) := by
    intro y hy
    unfold seenSet at hy
    obtain ⟨⟨j, e⟩, hmem, rfl⟩ := Finset.mem_image.mp hy
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hmem
    obtain ⟨⟨⟨hj1, hj2⟩, ⟨he1, he2⟩⟩, a, ha⟩ := hmem
    have hjd := Nat.div_add_mod j p
    have hell : j % p < p := Nat.mod_lt _ hp0
    des_unfold at hj1 hj2 he2 ha
    push_cast at ha
    have hJ : (design.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e = p * a := ha
    have hdiv : ((design.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p = a := by
      rw [hJ]; exact Int.mul_ediv_cancel_left _ (ne_of_gt hp0')
    simp only
    rw [hdiv]
    have hH : (design.H N : ℤ) = 78 * N := by des_unfold; push_cast; ring
    rw [hH] at hJ
    have ha1 : 1 < a := by
      by_contra hc
      have : (p : ℤ) * a ≤ p := by nlinarith
      omega
    have ha3 : a < 3 := by
      by_contra hc
      have : 3 * (p : ℤ) ≤ p * a := by nlinarith
      omega
    have ha2 : a = 2 := by omega
    subst ha2
    have hj : j / p < 2 := by
      by_contra hc
      have : 2 * p ≤ p * (j / p) := by nlinarith
      omega
    have h0 := Nat.zero_le (j / p)
    have : j / p = 0 ∨ j / p = 1 := by omega
    rcases this with h | h <;> simp [h]
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

theorem frob_win {N p : ℕ} (hA : frobApp N p) :
    0 + (53 * N - 2 * p - 2 + 1) ≤ (p - 1) / 2 ∧
      FrobGood design N p 3 0 (53 * N - 2 * p - 2 + 1) 0 := by
  obtain ⟨h1, h2⟩ := hA
  refine ⟨by omega, ?_⟩
  intro k hk
  refine ⟨?_, ?_⟩ <;> (interval_cases k <;> (des_unfold; push_cast; omega))

def frobLB : NullityLB design :=
  frobInstLB design adm frobApp frobVal (fun _ _ => 3) (fun _ _ => 0)
    (fun N p => 53 * N - 2 * p - 2) (fun _ _ => 0)
    (fun N p hN hp hp2 hH hA => frob_win hA)
    (fun N p hA => by
      obtain ⟨h1, h2⟩ := hA
      have hc := seen_card h1 h2
      unfold frobVal
      generalize (seenSet design N p 0 (0 + (53 * N - 2 * p - 2 + 1))).card = c at hc ⊢
      have h3 : 1 ≤ 3 - c := by omega
      calc 53 * N - 2 * p - 1 = (53 * N - 2 * p - 2 + 1) * 1 := by omega
        _ ≤ _ := Nat.mul_le_mul_left _ h3)

theorem frob_cell {N p : ℕ} (h1 : 26 * N < p) (h2 : 2 * p ≤ 53 * N) :
    (53 : ℤ) * N + (-2) * p ≤ 1 * ((frobLB.kap N p : ℕ) : ℤ) + 2 := by
  by_cases hA : frobApp N p
  · have hk : frobLB.kap N p = frobVal N p := by
      simp [frobLB, frobInstLB, frobProductLB, NullityLB.ofWindow, hA]
    rw [hk]
    unfold frobVal
    omega
  · have hk : frobLB.kap N p = 0 := by
      simp [frobLB, frobInstLB, frobProductLB, NullityLB.ofWindow, hA]
    rw [hk]
    have : ¬ (26 * N < p ∧ 2 * p + 2 ≤ 53 * N) := hA
    omega

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger
