module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.EvalRefLog

@[expose] public section

/-!
# Moments of the reference and the `ip(mpos, mpos)` bounds (Theorem A, lane E1b, items 16 and 17)

For a signed reference `μ = P − N` given by rational piece lists (`RefQ`, `SRef.IsQ`) the species moments
`mpos μ τ n = ∫ (τ y)^(n+1) dP_true − ∫ (τ y)^(n+1) dN_true` and `mneg` are `τ^(n+1)` times an exact rational
(`mposQ`, `mnegQ`; `momQ q k = ∫_lo^hi dens(t) t^k dt`, a finite sum of powers of the endpoints).

* **Item 16** (`ip_mpos_lower_eventually`): for `τ_N → 1` and every `K`, eventually
  `ipPartQ R K − ε ≤ ip (mpos μ τ_N) (mpos μ τ_N)`, `ipPartQ R K = Σ_{n<K} (mposQ R n)² / (n+1)` rational
  (the terms of `ip` are nonnegative; the dropped tail is `≈ d₁²/(2K²)`, `d₁` the density at `1`).
* **Item 17** (`ip_le_partial_add_tail`, `ip_mposDiff_le`): for `|c_n| ≤ M/(n+2)` the tail of `ip c c`
  is at most `M² / ((K+1)(K+2))`; for `Δ = mpos μA τ − mpos μB τ`, any `τ ∈ (0,1)`, `μA, μB` with density
  cap `C`: `ip Δ Δ ≤ Σ_{n<K} (mposQ RA n − mposQ RB n)²/(n+1) + (2C)²/((K+1)(K+2))`
  (uses `BD.integral_le`: `0 ≤ ∫ (τ y)^k dm ≤ C τ^k/(k+1)`).
-/

namespace CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.ReflectionEnergy
open CatalanMeasure.GenD.Signed.TaylorCell
open MeasureTheory Set Filter Topology

noncomputable section

/-! ### 1. Moments of a piece -/

/-- `Σ_i l_i/(i+j+k+1) (b^(i+j+k+1) − a^(i+j+k+1))`: exact `∫_a^b t^j (Σ l_i t^i) t^k dt`. -/
def momAux (b a : ℚ) (k : ℕ) : ℕ → List ℚ → ℚ
  | _, [] => 0
  | j, x :: xs =>
    x / ((j + k + 1 : ℕ) : ℚ) * (b ^ (j + k + 1) - a ^ (j + k + 1)) + momAux b a k (j + 1) xs

/-- `∫_lo^hi dens(t) t^k dt`. -/
def momQ (q : PieceQ) (k : ℕ) : ℚ := momAux q.hi q.lo k 0 q.p

theorem int_pow_polyTow (a b : ℚ) (k : ℕ) : ∀ (l : List ℚ) (j : ℕ),
    ∫ t in (a : ℝ)..(b : ℝ), t ^ j * polyTow l 0 t * t ^ k = ((momAux b a k j l : ℚ) : ℝ)
  | [], j => by simp [momAux, polyTow_zero_nil]
  | x :: xs, j => by
    have e : ∫ t in (a : ℝ)..(b : ℝ), t ^ j * polyTow (x :: xs) 0 t * t ^ k =
        ∫ t in (a : ℝ)..(b : ℝ), ((x : ℝ) * t ^ (j + k) + t ^ (j + 1) * polyTow xs 0 t * t ^ k) :=
      intervalIntegral.integral_congr (fun t _ => by
        simp only [polyTow_zero_cons]; ring)
    have ii1 : IntervalIntegrable (fun t : ℝ => (x : ℝ) * t ^ (j + k)) volume (a : ℝ) (b : ℝ) :=
      (by fun_prop : Continuous fun t : ℝ => (x : ℝ) * t ^ (j + k)).intervalIntegrable _ _
    have ii2 : IntervalIntegrable (fun t : ℝ => t ^ (j + 1) * polyTow xs 0 t * t ^ k) volume
        (a : ℝ) (b : ℝ) :=
      (((continuous_pow (j + 1)).mul (continuous_polyTow0 xs)).mul
        (continuous_pow k)).intervalIntegrable _ _
    rw [e, intervalIntegral.integral_add ii1 ii2, intervalIntegral.integral_const_mul, integral_pow,
      int_pow_polyTow a b k xs (j + 1)]
    simp only [momAux]
    push_cast
    ring

theorem int_dens_pow (q : PieceQ) (k : ℕ) :
    ∫ t in (q.lo : ℝ)..(q.hi : ℝ), polyTow q.p 0 t * t ^ k = ((momQ q k : ℚ) : ℝ) := by
  have h := int_pow_polyTow q.lo q.hi k q.p 0
  simp only [pow_zero, one_mul] at h
  exact h

/-- `Σ_{q ∈ L} momQ q k`. -/
def sumMom : List PieceQ → ℕ → ℚ
  | [], _ => 0
  | q :: L, k => momQ q k + sumMom L k

theorem mom_piece (q : PieceQ) (τ : ℝ) (k : ℕ) :
    ∫ t in q.toPiece.lo..q.toPiece.hi, q.toPiece.dens t * (τ * t) ^ k =
      τ ^ k * ((momQ q k : ℚ) : ℝ) := by
  have h := int_dens_pow q k
  calc ∫ t in q.toPiece.lo..q.toPiece.hi, q.toPiece.dens t * (τ * t) ^ k
      = ∫ t in (q.lo : ℝ)..(q.hi : ℝ), τ ^ k * (polyTow q.p 0 t * t ^ k) :=
        intervalIntegral.integral_congr (fun t _ => by simp only [dens_eq]; ring)
    _ = τ ^ k * ∫ t in (q.lo : ℝ)..(q.hi : ℝ), polyTow q.p 0 t * t ^ k :=
        intervalIntegral.integral_const_mul _ _
    _ = τ ^ k * ((momQ q k : ℚ) : ℝ) := by rw [h]

theorem mom_polyMeas (τ : ℝ) (k : ℕ) : ∀ (L : List PieceQ), (∀ q ∈ L, PieceOK q.toPiece) →
    ∫ y, (τ * y) ^ k ∂(polyMeas (L.map PieceQ.toPiece)) = τ ^ k * ((sumMom L k : ℚ) : ℝ)
  | [], _ => by simp [polyMeas, sumMom]
  | q :: L, hL => by
    have hq : PieceOK q.toPiece := hL q List.mem_cons_self
    have hL' : ∀ q' ∈ L, PieceOK q'.toPiece := fun q' h => hL q' (List.mem_cons_of_mem _ h)
    have hf : Continuous fun y : ℝ => (τ * y) ^ k := by fun_prop
    have hint := integrable_piece (g := fun y : ℝ => (τ * y) ^ k) hq hf.integrableOn_Icc
    have hrest : Integrable (fun y : ℝ => (τ * y) ^ k) (polyMeas (L.map PieceQ.toPiece)) :=
      (integrable_polyMeas (g := fun y : ℝ => (τ * y) ^ k) (qs := L.map PieceQ.toPiece)
        (fun q' hq' => ⟨mem_toPiece_ok hL' q' hq', hf.integrableOn_Icc⟩)).1
    have e : polyMeas ((q :: L).map PieceQ.toPiece) =
        q.toPiece.meas + polyMeas (L.map PieceQ.toPiece) := by
      simp [polyMeas]
    rw [e, integral_add_measure hint.1 hrest, hint.2, mom_polyMeas τ k L hL', mom_piece q τ k]
    simp only [sumMom]
    push_cast
    ring

/-! ### 2. The species moments of `P − N` -/

def mposQ (R : RefQ) (n : ℕ) : ℚ := sumMom R.pT (n + 1) - sumMom R.nT (n + 1)

def mnegQ (R : RefQ) (n : ℕ) : ℚ := (-1) ^ (n + 1) * (sumMom R.pF (n + 1) - sumMom R.nF (n + 1))

theorem mpos_eq (μ : SRef) (R : RefQ) (hμ : IsRefQ μ R) (hR : R.OK) (τ : ℝ) (n : ℕ) :
    mpos μ τ n = τ ^ (n + 1) * ((mposQ R n : ℚ) : ℝ) := by
  obtain ⟨h1, -, h3, -⟩ := hμ
  obtain ⟨hR1, -, hR3, -⟩ := hR
  unfold mpos
  rw [h1, h3, mom_polyMeas τ (n + 1) R.pT hR1, mom_polyMeas τ (n + 1) R.nT hR3]
  unfold mposQ
  push_cast
  ring

theorem mneg_eq (μ : SRef) (R : RefQ) (hμ : IsRefQ μ R) (hR : R.OK) (τ : ℝ) (n : ℕ) :
    mneg μ τ n = τ ^ (n + 1) * ((mnegQ R n : ℚ) : ℝ) := by
  obtain ⟨-, h2, -, h4⟩ := hμ
  obtain ⟨-, hR2, -, hR4⟩ := hR
  unfold mneg
  rw [h2, h4, mom_polyMeas τ (n + 1) R.pF hR2, mom_polyMeas τ (n + 1) R.nF hR4]
  unfold mnegQ
  push_cast
  ring

/-! ### 3. Item 16: the lower bound for `ip (mpos μ τ) (mpos μ τ)` -/

/-- `Σ_{n<K} (mposQ R n)² / (n+1)`. -/
def ipPartQ (R : RefQ) (K : ℕ) : ℚ :=
  ∑ n ∈ Finset.range K, (mposQ R n) ^ 2 / ((n : ℚ) + 1)

theorem ip_mpos_ge_partial (μ : SRef) (R : RefQ) (hμ : IsRefQ μ R) (hR : R.OK) {C : ℝ}
    (hOK : μ.OK C) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (K : ℕ) :
    ∑ n ∈ Finset.range K, (τ ^ (n + 1) * ((mposQ R n : ℚ) : ℝ)) ^ 2 / ((n : ℝ) + 1) ≤
      ip (mpos μ τ) (mpos μ τ) := by
  have hg := isGeom_mpos hOK hτ.1
  have hs := hasSum_ip hτ hg hg
  have e : ∀ n ∈ Finset.range K, (τ ^ (n + 1) * ((mposQ R n : ℚ) : ℝ)) ^ 2 / ((n : ℝ) + 1) =
      mpos μ τ n * mpos μ τ n / ((n : ℝ) + 1) := fun n _ => by
    rw [mpos_eq μ R hμ hR]; ring
  rw [Finset.sum_congr rfl e]
  exact sum_le_hasSum (Finset.range K)
    (fun n _ => div_nonneg (mul_self_nonneg _) (by positivity)) hs

/-- **Item 16.**  For `τ_N → 1` (and `τ_N ∈ (0,1)`), a fixed reference with density cap `C` and every `K`:
eventually `ipPartQ R K − ε ≤ ip (mpos μ τ_N) (mpos μ τ_N)`. -/
theorem ip_mpos_lower_eventually (R : RefQ) (hR : R.OK) {C : ℕ → ℝ} (μ : ℕ → SRef)
    (hμ : ∀ N, IsRefQ (μ N) R) (hOK : ∀ N, (μ N).OK (C N)) (τ : ℕ → ℝ)
    (hτ : Tendsto τ atTop (𝓝 1)) (hτ1 : ∀ N, τ N ∈ Ioo (0 : ℝ) 1) (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ((ipPartQ R K : ℚ) : ℝ) - ε ≤ ip (mpos (μ N) (τ N)) (mpos (μ N) (τ N)) := by
  have h : Tendsto (fun N => ∑ n ∈ Finset.range K,
      (τ N ^ (n + 1) * ((mposQ R n : ℚ) : ℝ)) ^ 2 / ((n : ℝ) + 1)) atTop
      (𝓝 (∑ n ∈ Finset.range K, (1 ^ (n + 1) * ((mposQ R n : ℚ) : ℝ)) ^ 2 / ((n : ℝ) + 1))) :=
    tendsto_finset_sum (Finset.range K) (fun n _ =>
      (((hτ.pow (n + 1)).mul_const ((mposQ R n : ℚ) : ℝ)).pow 2).div_const ((n : ℝ) + 1))
  have hlim : Tendsto (fun N => ∑ n ∈ Finset.range K,
      (τ N ^ (n + 1) * ((mposQ R n : ℚ) : ℝ)) ^ 2 / ((n : ℝ) + 1)) atTop
      (𝓝 ((ipPartQ R K : ℚ) : ℝ)) := by
    simpa [ipPartQ] using h
  have hev := hlim.eventually_const_lt (show ((ipPartQ R K : ℚ) : ℝ) - ε < ((ipPartQ R K : ℚ) : ℝ)
    by linarith)
  filter_upwards [hev] with N hN
  exact le_of_lt (lt_of_lt_of_le hN (ip_mpos_ge_partial (μ N) R (hμ N) hR (hOK N) (hτ1 N) K))

/-! ### 4. Item 17: tails -/

theorem bd_moment_le {m : Measure ℝ} {C : ℝ} (h : BD m C) (hC : 0 ≤ C) {τ : ℝ} (hτ : 0 ≤ τ)
    (k : ℕ) : ∫ y, (τ * y) ^ k ∂m ≤ C * (τ ^ k / ((k : ℝ) + 1)) := by
  have hf : Continuous fun y : ℝ => (τ * y) ^ k := by fun_prop
  have hf0 : ∀ᵐ y ∂(volume.restrict (Ioo (0 : ℝ) 1)), 0 ≤ (τ * y) ^ k :=
    (ae_restrict_iff' measurableSet_Ioo).mpr
      (Filter.Eventually.of_forall (fun y hy => pow_nonneg (mul_nonneg hτ hy.1.le) _))
  have hfi : Integrable (fun y : ℝ => (τ * y) ^ k) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    hf.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have h1 := h.integral_le hC hf0 hfi
  have e : ∫ y in Ioo (0 : ℝ) 1, (τ * y) ^ k = τ ^ k / ((k : ℝ) + 1) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    simp only [mul_pow]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp [div_eq_mul_inv]
  rw [e] at h1
  exact h1

theorem bd_moment_nonneg {m : Measure ℝ} {C : ℝ} (h : BD m C) {τ : ℝ} (hτ : 0 ≤ τ) (k : ℕ) :
    0 ≤ ∫ y, (τ * y) ^ k ∂m :=
  integral_nonneg_of_ae (h.ae_mem.mono (fun y hy => pow_nonneg (mul_nonneg hτ hy.1.le) _))

/-- `|mpos μ τ n| ≤ C τ^(n+1)/(n+2)`. -/
theorem abs_mpos_le {μ : SRef} {C : ℝ} (h : μ.OK C) (hC : 0 ≤ C) {τ : ℝ} (hτ : 0 ≤ τ) (n : ℕ) :
    |mpos μ τ n| ≤ C * (τ ^ (n + 1) / (((n + 1 : ℕ) : ℝ) + 1)) := by
  unfold mpos
  have a1 := bd_moment_nonneg (h.hP true) hτ (n + 1)
  have a2 := bd_moment_le (h.hP true) hC hτ (n + 1)
  have b1 := bd_moment_nonneg (h.hN true) hτ (n + 1)
  have b2 := bd_moment_le (h.hN true) hC hτ (n + 1)
  rw [abs_le]
  constructor <;> linarith

/-- For `τ ≤ 1`: `|mpos μ τ n| ≤ C/(n+2)`. -/
theorem abs_mpos_le' {μ : SRef} {C : ℝ} (h : μ.OK C) (hC : 0 ≤ C) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    (n : ℕ) : |mpos μ τ n| ≤ C / ((n : ℝ) + 2) := by
  refine (abs_mpos_le h hC hτ.1.le n).trans ?_
  have h1 : τ ^ (n + 1) ≤ 1 := pow_le_one₀ hτ.1.le hτ.2.le
  have h2 : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
  rw [h2]
  have h3 : 0 < (n : ℝ) + 2 := by positivity
  calc C * (τ ^ (n + 1) / ((n : ℝ) + 2)) ≤ C * (1 / ((n : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1 h3.le) hC
    _ = C / ((n : ℝ) + 2) := by ring

theorem tail_term_le (D : ℝ) (hD : 0 ≤ D) (K i : ℕ) :
    D / (((i + K : ℕ) : ℝ) + 2) ^ 2 / (((i + K : ℕ) : ℝ) + 1) ≤
      D / ((K : ℝ) + 2) * (1 / (((i + K : ℕ) : ℝ) + 1) - 1 / (((i + K : ℕ) : ℝ) + 2)) := by
  set x : ℝ := ((i + K : ℕ) : ℝ) with hx
  have hxK : (K : ℝ) ≤ x := by
    rw [hx]; exact_mod_cast Nat.le_add_left K i
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hx1 : 0 < x + 1 := by linarith
  have hx2 : 0 < x + 2 := by linarith
  have hK2 : 0 < (K : ℝ) + 2 := by linarith
  have hx1' : x + 1 ≠ 0 := hx1.ne'
  have hx2' : x + 2 ≠ 0 := hx2.ne'
  have hK2' : (K : ℝ) + 2 ≠ 0 := hK2.ne'
  have e : D / ((K : ℝ) + 2) * (1 / (x + 1) - 1 / (x + 2)) =
      D / (((K : ℝ) + 2) * ((x + 1) * (x + 2))) := by
    field_simp
    try ring
  rw [div_div, e]
  apply div_le_div_of_nonneg_left hD (mul_pos hK2 (mul_pos hx1 hx2))
  nlinarith [mul_nonneg (mul_pos hx1 hx2).le (sub_nonneg.mpr hxK)]

theorem tail_sum_closed (D : ℝ) (K : ℕ) : ∀ m : ℕ,
    ∑ i ∈ Finset.range m, D / ((K : ℝ) + 2) *
        (1 / (((i + K : ℕ) : ℝ) + 1) - 1 / (((i + K : ℕ) : ℝ) + 2)) =
      D / ((K : ℝ) + 2) * (1 / ((K : ℝ) + 1) - 1 / (((m + K : ℕ) : ℝ) + 1))
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_range_succ, tail_sum_closed D K m]
    push_cast
    ring

theorem tail_bound (D : ℝ) (hD : 0 ≤ D) (K m : ℕ) :
    ∑ i ∈ Finset.range m, D / (((i + K : ℕ) : ℝ) + 2) ^ 2 / (((i + K : ℕ) : ℝ) + 1) ≤
      D / (((K : ℝ) + 1) * ((K : ℝ) + 2)) := by
  calc ∑ i ∈ Finset.range m, D / (((i + K : ℕ) : ℝ) + 2) ^ 2 / (((i + K : ℕ) : ℝ) + 1)
      ≤ ∑ i ∈ Finset.range m, D / ((K : ℝ) + 2) *
        (1 / (((i + K : ℕ) : ℝ) + 1) - 1 / (((i + K : ℕ) : ℝ) + 2)) :=
        Finset.sum_le_sum (fun i _ => tail_term_le D hD K i)
    _ = D / ((K : ℝ) + 2) * (1 / ((K : ℝ) + 1) - 1 / (((m + K : ℕ) : ℝ) + 1)) :=
        tail_sum_closed D K m
    _ ≤ D / ((K : ℝ) + 2) * (1 / ((K : ℝ) + 1)) := by
        have h0 : 0 ≤ D / ((K : ℝ) + 2) := by positivity
        have h1 : 0 ≤ 1 / (((m + K : ℕ) : ℝ) + 1) := by positivity
        exact mul_le_mul_of_nonneg_left (by linarith) h0
    _ = D / (((K : ℝ) + 1) * ((K : ℝ) + 2)) := by
        rw [div_mul_div_comm, mul_one, mul_comm]

/-- **Item 17, generic form.**  If `c_n² ≤ D/(n+2)²` and `Σ c_n²/(n+1)` converges, the tail of `ip c c`
after `K` terms is at most `D/((K+1)(K+2))`. -/
theorem ip_le_partial_add_tail {c : ℕ → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hc : ∀ n : ℕ, c n ^ 2 ≤ D / ((n : ℝ) + 2) ^ 2)
    (hs : Summable fun n : ℕ => c n * c n / ((n : ℝ) + 1)) (K : ℕ) :
    ip c c ≤ ∑ n ∈ Finset.range K, c n * c n / ((n : ℝ) + 1) + D / (((K : ℝ) + 1) * ((K : ℝ) + 2)) := by
  unfold ip
  have hsplit := Summable.sum_add_tsum_nat_add K hs
  have htail : ∑' i : ℕ, c (i + K) * c (i + K) / (((i + K : ℕ) : ℝ) + 1) ≤
      D / (((K : ℝ) + 1) * ((K : ℝ) + 2)) := by
    refine Real.tsum_le_of_sum_range_le (fun i => div_nonneg (mul_self_nonneg _) (by positivity))
      (fun m => ?_)
    refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) (tail_bound D hD K m)
    have h1 : c (i + K) * c (i + K) ≤ D / (((i + K : ℕ) : ℝ) + 2) ^ 2 := by
      have := hc (i + K)
      rw [sq] at this
      exact this
    exact div_le_div_of_nonneg_right h1 (by positivity)
  linarith

/-- **Item 17.**  `Δ = mpos μA τ − mpos μB τ` for two references with density cap `C`, any `τ ∈ (0,1)`:
`ip Δ Δ ≤ Σ_{n<K} (mposQ RA n − mposQ RB n)²/(n+1) + (2C)²/((K+1)(K+2))`. -/
theorem ip_mposDiff_le (μA μB : SRef) (RA RB : RefQ) (hA : IsRefQ μA RA) (hB : IsRefQ μB RB)
    (hRA : RA.OK) (hRB : RB.OK) {C : ℝ} (hCA : μA.OK C) (hCB : μB.OK C) (hC : 0 ≤ C)
    {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (K : ℕ) :
    ip (fun n => mpos μA τ n - mpos μB τ n) (fun n => mpos μA τ n - mpos μB τ n) ≤
      ((∑ n ∈ Finset.range K, (mposQ RA n - mposQ RB n) ^ 2 / ((n : ℚ) + 1) : ℚ) : ℝ) +
        (2 * C) ^ 2 / (((K : ℝ) + 1) * ((K : ℝ) + 2)) := by
  set c : ℕ → ℝ := fun n => mpos μA τ n - mpos μB τ n with hc
  have hgA := isGeom_mpos hCA hτ.1
  have hgB := isGeom_mpos hCB hτ.1
  have hgc : IsGeom τ c := hgA.sub hgB
  have hs : Summable fun n : ℕ => c n * c n / ((n : ℝ) + 1) := hgc.summable_mul hτ hgc
  have hbound : ∀ n : ℕ, c n ^ 2 ≤ (2 * C) ^ 2 / ((n : ℝ) + 2) ^ 2 := by
    intro n
    have h1 := abs_mpos_le' hCA hC hτ n
    have h2 := abs_mpos_le' hCB hC hτ n
    have h3 : |c n| ≤ 2 * C / ((n : ℝ) + 2) := by
      have h1' := abs_le.mp h1
      have h2' := abs_le.mp h2
      have e : 2 * C / ((n : ℝ) + 2) = C / ((n : ℝ) + 2) + C / ((n : ℝ) + 2) := by ring
      rw [abs_le, e]
      simp only [hc]
      constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]
    have h4 : c n ^ 2 ≤ (2 * C / ((n : ℝ) + 2)) ^ 2 := by
      rw [← sq_abs (c n)]
      exact pow_le_pow_left₀ (abs_nonneg _) h3 2
    rwa [div_pow] at h4
  have h1 := ip_le_partial_add_tail (c := c) (D := (2 * C) ^ 2) (by positivity) hbound hs K
  have h2 : ∑ n ∈ Finset.range K, c n * c n / ((n : ℝ) + 1) ≤
      ((∑ n ∈ Finset.range K, (mposQ RA n - mposQ RB n) ^ 2 / ((n : ℚ) + 1) : ℚ) : ℝ) := by
    push_cast
    refine Finset.sum_le_sum (fun n _ => ?_)
    have e : c n = τ ^ (n + 1) * (((mposQ RA n : ℚ) : ℝ) - ((mposQ RB n : ℚ) : ℝ)) := by
      simp only [hc]
      rw [mpos_eq μA RA hA hRA, mpos_eq μB RB hB hRB]
      ring
    rw [e]
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hτ1 : τ ^ (n + 1) ≤ 1 := pow_le_one₀ hτ.1.le hτ.2.le
    have hτn : (τ ^ (n + 1)) ^ 2 ≤ 1 := pow_le_one₀ (pow_nonneg hτ.1.le (n + 1)) hτ1
    apply div_le_div_of_nonneg_right _ hn.le
    nlinarith [mul_le_mul_of_nonneg_right hτn
      (sq_nonneg (((mposQ RA n : ℚ) : ℝ) - ((mposQ RB n : ℚ) : ℝ)))]
  linarith

end

end CatalanMeasure.GenD.Signed.Data.Consts.EvalRef

#print axioms CatalanMeasure.GenD.Signed.Data.Consts.EvalRef.ip_mpos_lower_eventually
#print axioms CatalanMeasure.GenD.Signed.Data.Consts.EvalRef.ip_mposDiff_le
