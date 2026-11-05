module
public import Submission.CatalanMeasure.PinSupDual
@[expose] public section
open Set Finset Real
open scoped BigOperators
namespace OAI.InternalCatalan
noncomputable section

def populationOffDiagonalInteraction (ν : ℝ) {p m : ℕ}
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) : ℝ :=
  pinOffDiagonalInteraction ν 1 x s +
    (∑ i : Fin (p+m), ∑ j ∈ Ioi i,
      Real.log |Fin.append x y j - Fin.append x y i|) / ν ^ 2

def populationDampedInteraction (ν e : ℝ) {p m : ℕ}
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) : ℝ :=
  pinDampedInteraction ν 1 e x s +
    (∑ i : Fin (p+m), ∑ j : Fin (p+m),
      realEnergyCosineKernel (realEnergyTau e ^ 2) (Fin.append x y i) (Fin.append x y j)) /
      (2 * ν ^ 2)

def populationRegularizationError (ν e : ℝ) : ℝ :=
  (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) / ν +
    (Real.log 2 - Real.log e) / (2 * ν) +
    (Real.log 2 - 2 * Real.log e) / ν + 16 * e

theorem population_cosine_regularization {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {n : ℕ} (hn : (n : ℝ) ≤ ν)
    {z : Fin n → ℝ} (hz : ∀ i, z i ∈ Ioo (-1 : ℝ) 1)
    (hzi : Function.Injective z) :
    (∑ i : Fin n, ∑ j ∈ Ioi i, Real.log |z j - z i|) / ν ^ 2 ≤
      (∑ i : Fin n, ∑ j : Fin n,
        realEnergyCosineKernel (realEnergyTau e ^ 2) (z i) (z j)) / (2 * ν ^ 2) +
      (Real.log 2 - 2 * Real.log (1 - realEnergyTau e ^ 2)) / (2 * ν) + 2 * e := by
  have he0 : 0 ≤ e := he.1.le
  let F : Fin n → Fin n → ℝ := fun i j =>
    realEnergyCosineKernel (realEnergyTau e ^ 2) (z i) (z j)
  have hpairs := energy_sum_pairs_le_of_le_add n
    (fun i j => Real.log |z j - z i|) F (4 * e) (fun i j hij => by
      dsimp [F]
      rw [abs_sub_comm (z j) (z i)]
      exact realEnergy_cosine_tau_le he ⟨(hz i).1.le, (hz i).2.le⟩
        ⟨(hz j).1.le, (hz j).2.le⟩ (fun h => (ne_of_lt hij) (hzi h)))
  have ht := realEnergyTau_bounds he
  have htr : realEnergyTau e ^ 2 ∈ Ico (0 : ℝ) 1 := by
    refine ⟨sq_nonneg _, ?_⟩
    nlinarith [mul_pos ht.1 (sub_pos.mpr ht.2)]
  have hsym (i j : Fin n) : F i j = F j i :=
    realEnergyCosineKernel_symm htr ⟨(hz i).1.le, (hz i).2.le⟩
      ⟨(hz j).1.le, (hz j).2.le⟩
  have hsplit : (∑ i, ∑ j ∈ Ioi i, F i j) =
      ((∑ i, ∑ j, F i j) - ∑ i, F i i) / 2 := by
    linarith [energy_sum_pairs_of_symmetric n F hsym]
  have hdiag := pin_tau_diagonal_sum hν he (by norm_num : (0 : ℝ) ≤ 1) hn hz
  have hc : ((n.choose 2 : ℕ) : ℝ) ≤ ν ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    nlinarith only [hn, hν, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hcost : 4 * e * ((n.choose 2 : ℕ) : ℝ) / ν ^ 2 ≤ 2 * e := by
    rw [div_le_iff₀ (sq_pos_of_pos hν)]
    nlinarith [mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 4 * e)]
  have hbound := div_le_div_of_nonneg_right hpairs (sq_nonneg ν)
  rw [hsplit] at hbound
  dsimp only [F] at hbound
  norm_num only [one_mul] at hdiag
  ring_nf at hbound hdiag hcost ⊢
  linarith only [hbound, hdiag, hcost]

theorem populationOffDiagonalInteraction_le_regularized {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p m : ℕ} (hpm : ((p+m : ℕ) : ℝ) ≤ ν)
    {x : Fin p → ℝ} {y : Fin m → ℝ} {s : Fin p → ℝ}
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (hzi : Function.Injective (Fin.append x y)) (hsi : Function.Injective s) :
    populationOffDiagonalInteraction ν x y s ≤
      populationDampedInteraction ν e x y s -
      (∑ i : Fin p, Real.log (1 - x i)) / (2 * ν ^ 2) -
      (∑ j : Fin p, Real.log (1 - s j)) / ν ^ 2 + populationRegularizationError ν e := by
  have he0 : 0 ≤ e := he.1.le
  have hp : (p : ℝ) ≤ ν := by
    push_cast at hpm
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hz : ∀ i, Fin.append x y i ∈ Ioo (-1 : ℝ) 1 := by
    intro i
    exact Fin.addCases (fun i => by simpa using hx i) (fun j => by simpa using hy j) i
  have hxi : Function.Injective x := by
    intro i j hij
    have h := hzi (show Fin.append x y (Fin.castAdd m i) = Fin.append x y (Fin.castAdd m j) by simpa using hij)
    apply Fin.ext
    exact congrArg (fun k : Fin (p+m) => k.val) h
  have hinteraction := pinOffDiagonalInteraction_le_damped hν (by norm_num : (0 : ℝ) ≤ 1) he hx hs hxi hsi
  have htau := pin_tau_diagonal_sum hν he (by norm_num : (0 : ℝ) ≤ 1) hp hx
  have hpower := pin_power_diagonal_sum hν he hp hx
  have hsigma := pin_sigma_diagonal_sum hν he hp hs
  have hcos := population_cosine_regularization hν he hpm hz hzi
  have hc : ((p.choose 2 : ℕ) : ℝ) ≤ ν ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    nlinarith only [hp, hν, (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  have hsq : (p : ℝ) ^ 2 ≤ ν ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg p) hp 2
  have hpair : 16 * e * ((p.choose 2 : ℕ) : ℝ) / ν ^ 2 +
      6 * e * (p : ℝ) ^ 2 / ν ^ 2 ≤ 14 * e := by
    have h1 := mul_le_mul_of_nonneg_left hc (show 0 ≤ 16 * e by positivity)
    have h2 := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 6 * e by positivity)
    rw [← add_div, div_le_iff₀ (sq_pos_of_pos hν)]
    nlinarith only [h1, h2]
  norm_num only [one_mul, mul_one, Nat.reduceAdd, Nat.reduceMul] at hinteraction htau
  simp only [mul_pow] at hinteraction
  simp only [neg_mul] at htau
  simp only [neg_div] at hpower hsigma
  unfold populationOffDiagonalInteraction populationDampedInteraction populationRegularizationError
  ring_nf at hinteraction htau hpower hsigma hcos hpair ⊢
  linarith only [hinteraction, htau, hpower, hsigma, hcos, hpair]

theorem population_damped_canonical_bound {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p m : ℕ} (hpm : ((p+m : ℕ) : ℝ) ≤ ν)
    {x : Fin p → ℝ} {y : Fin m → ℝ} {s : Fin p → ℝ}
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (pp v : ℕ → ℝ) (hpp : Summable (fun j => |pp j|)) (hv : Summable (fun j => |v j|)) :
    populationDampedInteraction ν e x y s ≤
      -(3 / 2 : ℝ) * ((p : ℝ) / ν) ^ 2 * Real.log 2 -
      (1 / 2 : ℝ) * (((p+m : ℕ) : ℝ) / ν) ^ 2 * Real.log 2 +
      2 * barrierTrialNormSq pp + barrierTrialNormSq v / 2 +
      (∑ i, (-4 * barrierTrialT pp (x i) - barrierTrialS v (x i))) / ν +
      (∑ j, -2 * barrierTrialT pp (y j)) / ν +
      (∑ j, 2 * barrierTrialT v (s j)) / ν +
      4 * e * (∑' j, |pp j|) + 4 * e * (∑' j, |v j|) := by
  have hp : (p : ℝ) ≤ ν := by push_cast at hpm; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hz : ∀ i, Fin.append x y i ∈ Ioo (-1 : ℝ) 1 := by
    intro i
    exact Fin.addCases (fun i => by simpa using hx i) (fun j => by simpa using hy j) i
  have hfree := pinDampedInteraction_le_canonicalTrials hν (by norm_num : (0 : ℝ) ≤ 1)
    he hp hx hs pp v hpp hv
  have hall := pin_first_tangent hν he hpm hz pp hpp
  rw [(pin_hasSum_trialTau_average pp hpp ν he hz).tsum_eq] at hall
  have he0 : 0 ≤ e := he.1.le
  have hpsum : (0 : ℝ) ≤ ∑' j, |pp j| := tsum_nonneg (fun _ => abs_nonneg _)
  have happrox := pin_average_le_of_le_add hν hpm
    (fun i => -2 * realEnergyTrialTau pp e (Fin.append x y i))
    (fun i => -2 * barrierTrialT pp (Fin.append x y i))
    (c := 2 * e * (∑' j, |pp j|)) (by positivity)
    (fun i => by
      have h := (abs_le.mp (realEnergyTrialTau_sub_le pp hpp he (hz i))).1
      linarith)
  have hsplit : (∑ i : Fin (p+m), -2 * barrierTrialT pp (Fin.append x y i)) / ν =
      (∑ i : Fin p, -2 * barrierTrialT pp (x i)) / ν +
      (∑ j : Fin m, -2 * barrierTrialT pp (y j)) / ν := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, add_div]
  have hjoin : (∑ i : Fin p, (-2 * 1 * barrierTrialT pp (x i) - barrierTrialS v (x i))) / ν +
      (∑ i : Fin p, -2 * barrierTrialT pp (x i)) / ν =
      (∑ i : Fin p, (-4 * barrierTrialT pp (x i) - barrierTrialS v (x i))) / ν := by
    rw [← add_div, ← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro i _
    ring
  rw [hsplit] at happrox
  have hsum : -2 * ((∑ i : Fin (p+m), realEnergyTrialTau pp e (Fin.append x y i)) / ν) =
      (∑ i : Fin (p+m), -2 * realEnergyTrialTau pp e (Fin.append x y i)) / ν := by
    rw [← mul_sum]
    ring
  unfold populationDampedInteraction
  have hcos : (∑ i : Fin (p+m), ∑ j : Fin (p+m), realEnergyCosineKernel (realEnergyTau e ^ 2)
      (Fin.append x y i) (Fin.append x y j)) / (2 * ν ^ 2) =
      ((∑ i : Fin (p+m), ∑ j : Fin (p+m), realEnergyCosineKernel (realEnergyTau e ^ 2)
      (Fin.append x y i) (Fin.append x y j)) / ν ^ 2) / 2 := by ring
  have htmp := add_le_add hfree (show
      (∑ i : Fin (p+m), ∑ j : Fin (p+m), realEnergyCosineKernel (realEnergyTau e ^ 2)
        (Fin.append x y i) (Fin.append x y j)) / (2 * ν ^ 2) ≤
      -(1/2 : ℝ) * (((p+m : ℕ) : ℝ)/ν)^2 * Real.log 2 + barrierTrialNormSq pp +
      (∑ i : Fin p, -2 * barrierTrialT pp (x i))/ν +
      (∑ j : Fin m, -2 * barrierTrialT pp (y j))/ν + 2*e*(∑' j, |pp j|) by
        rw [hcos]
        linarith only [hall, happrox, hsum])
  norm_num only at htmp
  linarith [hjoin]

theorem population_undamped_canonical_bound {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p m : ℕ} (hpm : ((p+m : ℕ) : ℝ) ≤ ν)
    {x : Fin p → ℝ} {y : Fin m → ℝ} {s : Fin p → ℝ}
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (hzi : Function.Injective (Fin.append x y)) (hsi : Function.Injective s)
    (pp v : ℕ → ℝ) (hpp : Summable (fun j => |pp j|)) (hv : Summable (fun j => |v j|)) :
    populationOffDiagonalInteraction ν x y s ≤
      -(3 / 2 : ℝ) * ((p : ℝ) / ν) ^ 2 * Real.log 2 -
      (1 / 2 : ℝ) * (((p+m : ℕ) : ℝ) / ν) ^ 2 * Real.log 2 +
      2 * barrierTrialNormSq pp + barrierTrialNormSq v / 2 +
      (∑ i, (-4 * barrierTrialT pp (x i) - barrierTrialS v (x i))) / ν +
      (∑ j, -2 * barrierTrialT pp (y j)) / ν +
      (∑ j, 2 * barrierTrialT v (s j)) / ν -
      (∑ i, Real.log (1 - x i)) / (2 * ν ^ 2) -
      (∑ j, Real.log (1 - s j)) / ν ^ 2 +
      4 * e * (∑' j, |pp j|) + 4 * e * (∑' j, |v j|) + populationRegularizationError ν e := by
  have hr := populationOffDiagonalInteraction_le_regularized hν he hpm hx hy hs hzi hsi
  have hd := population_damped_canonical_bound hν he hpm hx hy hs pp v hpp hv
  linarith only [hr, hd]

/-- The actual case constraint couples the missing rows to the free-row field. -/
theorem population_case_coupling {ν lam : ℝ} (hν : 0 < ν) (hlam : 0 ≤ lam)
    {p m : ℕ} (D : ℝ → ℝ) (x : Fin p → ℝ) (y : Fin m → ℝ)
    (hcase : -(1 : ℝ) < ∑ i : Fin (p+m), D (Fin.append x y i)) :
    -lam * ((∑ i, D (x i)) / ν) ≤
      lam / ν + lam * ((∑ j, D (y j)) / ν) := by
  rw [Fin.sum_univ_add] at hcase
  simp only [Fin.append_left, Fin.append_right] at hcase
  have h := mul_le_mul_of_nonneg_left hcase.le (div_nonneg hlam hν.le)
  ring_nf at h ⊢
  linarith only [h]

end
end OAI.InternalCatalan
