module
public import Submission.CatalanMeasure.GenD.OddProfile
public import Submission.CatalanMeasure.GenD.Interface
@[expose] public section
namespace CatalanMeasure.GenD.Uniform.Arithmetic
open CatalanMeasure.Parametric OAI.InternalCatalan
noncomputable section

/-- Precisely the hypotheses under which the upper pool is available. -/
def UpperAvailable (P : Parameters) (N p : ℕ) : Prop :=
  p ≤ P.H N ∧ P.H N ≤ 2*p ∧ OddProfile.UpperSide P N p

/-- Retain the universally valid lower pool, and improve it only when the
actual upper-pool theorem applies. -/
def safeOddLoss (P : Parameters) (N p : ℕ) : ℕ := by
  classical
  exact if UpperAvailable P N p then min (lowerPrimeLoss P N p) (upperPrimeLoss P N p)
    else lowerPrimeLoss P N p

theorem safeOddLoss_le_lower (P : Parameters) (N p : ℕ) :
    safeOddLoss P N p ≤ lowerPrimeLoss P N p := by
  unfold safeOddLoss
  split_ifs <;> simp [min_le_left]


theorem safeOddLoss_le_upper (P : Parameters) (N p : ℕ) (h : UpperAvailable P N p) :
    safeOddLoss P N p≤upperPrimeLoss P N p := by
  unfold safeOddLoss
  rw [if_pos h]
  exact min_le_right _ _

theorem safeOddLoss_eq_lower (P : Parameters) (N p : ℕ) (h : ¬UpperAvailable P N p) :
    safeOddLoss P N p=lowerPrimeLoss P N p := by simp [safeOddLoss,h]


/-- Reuse a legacy profile only after supplying its real upper-side conditions. -/
theorem safeOddLoss_le_old (P : Parameters) (N p : ℕ) (hpH : p≤P.H N)
    (hside : P.H N≤2*p→OddProfile.UpperSide P N p) :
    safeOddLoss P N p≤OddProfile.oddLossNat P N p := by
  unfold OddProfile.oddLossNat
  split_ifs with h
  · exact safeOddLoss_le_lower P N p
  · exact safeOddLoss_le_upper P N p ⟨hpH,by omega,hside (by omega)⟩

theorem safeOddLoss_le_twice (P : Parameters) (N p : ℕ) :
    safeOddLoss P N p ≤ 2*P.n N :=
  (safeOddLoss_le_lower P N p).trans (Nat.sub_le _ _)

theorem safeOdd_valuation (P : Parameters) (hP : Admissible P) {N p : ℕ}
    [Fact p.Prime] (hN : 0<N) (hp2 : p≠2) (hHsq : P.H N<p^2)
    (z : ℚ) (hz : (z.den : ZMod p)≠0) :
    -(safeOddLoss P N p : ℤ) ≤ padicValRat p (determinantRat P z N) := by
  have hzp : (((p : ℚ)*z).den : ZMod p)≠0 :=
    (rational_residue_mul (a := (p : ℚ)) (by simp) hz).1
  have hlo := determinantRat_lower_prime_valuation hP hp2 hN hHsq z hzp
  unfold safeOddLoss
  split_ifs with h
  · have hup := determinantRat_upper_prime_valuation P hP hp2 hN hHsq h.1 h.2.1
      h.2.2.hA h.2.2.hLH h.2.2.hbp h.2.2.hJL z hz
    rcases le_total (lowerPrimeLoss P N p) (upperPrimeLoss P N p) with hle|hle
    · rw [min_eq_left hle]; exact hlo
    · rw [min_eq_right hle]; exact hup
  · exact hlo

/-- The actual combined odd price. -/
def oddPrice (P : Parameters) (lb : NullityLB P) (N p : ℕ) : ℕ :=
  min (safeOddLoss P N p) (2*P.n N-lb.kap N p)

/-- The improvement relative to this pool, rather than relative to the raw 2n price. -/
def saving (P : Parameters) (lb : NullityLB P) (N p : ℕ) : ℕ :=
  safeOddLoss P N p-oddPrice P lb N p

theorem oddPrice_add_saving (P : Parameters) (lb : NullityLB P) (N p : ℕ) :
    oddPrice P lb N p+saving P lb N p=safeOddLoss P N p :=
  Nat.add_sub_of_le (min_le_left _ _)

theorem saving_le_pool (P : Parameters) (lb : NullityLB P) (N p : ℕ) :
    saving P lb N p≤safeOddLoss P N p := Nat.sub_le _ _

theorem saving_eq_excess (P : Parameters) (lb : NullityLB P) (N p : ℕ)
    (hk : lb.kap N p≤2*P.n N) :
    saving P lb N p=lb.kap N p-(2*P.n N-safeOddLoss P N p) := by
  have hp := safeOddLoss_le_twice P N p
  unfold saving oddPrice
  omega

theorem oddPrice_valuation (P : Parameters) (hP : Admissible P) (lb : NullityLB P)
    {N p : ℕ} [hpp : Fact p.Prime] (hN : 0<N) (hp2 : p≠2)
    (hHsq : P.H N<p^2) (z : ℚ) (hz : (z.den : ZMod p)≠0) :
    -(oddPrice P lb N p : ℤ) ≤ padicValRat p (determinantRat P z N) := by
  have hpool := safeOdd_valuation P hP hN hp2 hHsq z hz
  have hrank := det_valuation_of_nullity P hp2 hHsq
    (lb.ok N p hN hpp.out hp2 hHsq) z hz
  unfold oddPrice
  rcases le_total (safeOddLoss P N p) (2*P.n N-lb.kap N p) with h|h
  · rw [min_eq_left h]; exact hpool
  · rw [min_eq_right h]; exact hrank


/-- On recycling primes, the universal lower pool is exactly the raw budget;
the upper branch is impossible once the scale exceeds one. -/
theorem recycling_pool (P : Parameters) (hP : Admissible P) {N p : ℕ}
    (hN : 1<N) (hp : p.Prime) (hNp : N<p) (hpN : p≤2*N) :
    safeOddLoss P N p=2*P.n N := by
  have hb : N≤P.b N := by
    change N≤P.b0*N
    simpa using Nat.mul_le_mul_right N (Nat.succ_le_of_lt hP.2.1)
  have hq : N≤P.q N := by
    change N≤P.q0*N
    simpa using Nat.mul_le_mul_right N (Nat.succ_le_of_lt hP.2.2.1)
  have hA : 2*N≤P.A N := by unfold Parameters.A; omega
  have hne : p≠2*N := by
    intro heq
    have hd : p∣2*N := by rw [heq]
    rcases hp.dvd_mul.mp hd with hd|hd
    · have := Nat.le_of_dvd (by decide : 0<2) hd
      omega
    · have := Nat.le_of_dvd (by omega : 0<N) hd
      omega
  have hna : ¬UpperAvailable P N p := by
    intro h
    have hh := h.2.2.hA
    omega
  unfold safeOddLoss
  rw [if_neg hna,OddProfile.lowerPrimeLoss_eq]
  have hm := min_le_left (min p (P.L N-p)) (P.A N)
  have hm2 := min_le_left p (P.L N-p)
  have hb2 := le_max_left (P.b N) (P.H N-2*p)
  omega

end
end CatalanMeasure.GenD.Uniform.Arithmetic
