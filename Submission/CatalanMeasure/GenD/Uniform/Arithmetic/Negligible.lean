module
public import Submission.CatalanMeasure.GenD.PrimeGrowth
public import Submission.CatalanMeasure.Parametric.Parameters
public import Submission.OAI.NumberTheory.Catalan.Arithmetic.SmallOddPrimePartition
@[expose] public section
namespace CatalanMeasure.GenD.Uniform.Arithmetic
open Filter
open scoped Topology BigOperators
noncomputable section


/-- An affine rational guard wall, including its fixed integral offset. -/
structure AffineWall where
  slope : ℤ
  offset : ℤ
  denominator : ℕ
  denominator_pos : 0<denominator
  deriving DecidableEq

def AffineWall.point (w : AffineWall) (N : ℕ) : ℕ :=
  ((w.slope*N+w.offset)/(w.denominator:ℤ)).toNat

theorem AffineWall.point_eq (w : AffineWall) {N p : ℕ}
    (h : (w.denominator:ℤ)*(p:ℤ)=w.slope*N+w.offset) : w.point N=p := by
  unfold AffineWall.point
  rw [←h,Int.mul_ediv_cancel_left _ (by exact_mod_cast w.denominator_pos.ne')]
  exact Int.toNat_natCast p

def affineWallSet (W : Finset AffineWall) (N : ℕ) : Finset ℕ :=
  W.image (fun w => w.point N)

theorem affineWallSet_card (W : Finset AffineWall) (N : ℕ) :
    (affineWallSet W N).card≤W.card := Finset.card_image_le

theorem mem_affineWallSet {W : Finset AffineWall} {w : AffineWall} (hw : w∈W)
    {N p : ℕ} (h : (w.denominator:ℤ)*(p:ℤ)=w.slope*N+w.offset) :
    p∈affineWallSet W N :=
  Finset.mem_image.mpr ⟨w,hw,w.point_eq h⟩

/-- Every fixed collection of rational walls contributes at most one prime per wall. -/
def wallSet (W : Finset (ℕ × ℕ)) (N : ℕ) : Finset ℕ :=
  W.image (fun w => w.1*N/w.2)

theorem wallSet_card (W : Finset (ℕ × ℕ)) (N : ℕ) :
    (wallSet W N).card≤W.card := Finset.card_image_le

theorem mem_wallSet {W : Finset (ℕ × ℕ)} {a b N p : ℕ}
    (hw : (a,b)∈W) (hb : 0<b) (heq : b*p=a*N) : p∈wallSet W N := by
  apply Finset.mem_image.mpr
  refine ⟨(a,b),hw,?_⟩
  simp only
  rw [←heq, Nat.mul_div_cancel_left _ hb]

/-- Source exceptions together with all wall points have uniformly bounded cardinality. -/
def exceptionWalls (J : Finset ℕ) (W : Finset (ℕ × ℕ)) (N : ℕ) : Finset ℕ :=
  J∪wallSet W N

theorem exceptionWalls_card (J : Finset ℕ) (W : Finset (ℕ × ℕ)) (N : ℕ) :
    (exceptionWalls J W N).card≤J.card+W.card :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add_left (wallSet_card W N) _)

/-- The concrete O(N log N) error from finitely many lost prime contributions. -/
theorem bounded_support_cost (E : Finset ℕ) (M : ℕ) (c H N : ℝ)
    (hc : 0≤c) (hN : 0≤N) (hH : 1≤H*N) (hcard : E.card≤M)
    (e : ℕ→ℝ) (he : ∀p∈E, e p≤c*N) (hp : ∀p∈E, (p:ℝ)≤H*N) :
    ∑p∈E, e p*Real.log p ≤ (M:ℝ)*c*N*Real.log (H*N) := by
  have hlog := Real.log_nonneg hH
  have hterm (p : ℕ) (h : p∈E) : e p*Real.log p≤c*N*Real.log (H*N) := by
    have hlp := Real.log_natCast_nonneg p
    have hmono : Real.log (p:ℝ)≤Real.log (H*N) := by
      by_cases hz : p=0
      · subst p; simpa using hlog
      · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz) (hp p h)
    exact (mul_le_mul_of_nonneg_right (he p h) hlp).trans
      (mul_le_mul_of_nonneg_left hmono (mul_nonneg hc hN))
  calc
    _ ≤ ∑_p∈E,c*N*Real.log (H*N) := Finset.sum_le_sum hterm
    _ = (E.card:ℝ)*(c*N*Real.log (H*N)) := by simp [nsmul_eq_mul]
    _ ≤ (M:ℝ)*(c*N*Real.log (H*N)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := by ring

theorem linear_log_negligible (K H : ℝ) (hH : 0<H) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, K*(N:ℝ)*Real.log (H*N)≤ε*(N:ℝ)^2 := by
  have hi : Tendsto (fun N:ℕ => (N:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun N:ℕ => Real.log (N:ℝ)/(N:ℝ)) atTop (𝓝 0) := by
    exact (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun N:ℕ => (N:ℝ)) atTop atTop)
  have ht := ((hi.const_mul (Real.log H)).add hl).const_mul K
  simp only [mul_zero,add_zero] at ht
  have hv := (tendsto_order.mp ht).2 ε hε
  filter_upwards [hv,eventually_gt_atTop (0:ℕ)] with N hv hN
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have he : K*(Real.log H*(N:ℝ)⁻¹+Real.log (N:ℝ)/(N:ℝ))=
      K*Real.log (H*N)/(N:ℝ) := by
    rw [Real.log_mul hH.ne' hn.ne']
    field_simp
  rw [he,div_lt_iff₀ hn] at hv
  have hm := mul_le_mul_of_nonneg_right hv.le hn.le
  nlinarith only [hm]

/-- A discarded interval near zero costs at most its explicit linear width.
This permits taking that width to zero after the finite prime-sum estimate. -/
theorem lowBand_cost (e : ℕ→ℝ) (c ε N : ℝ) (hc : 0≤c) (hε : 0≤ε) (hN : 0≤N)
    (he : ∀p, p.Prime→e p≤c*N) :
    ∑p∈(Finset.Ioc 0 ⌊ε*N⌋₊).filter Nat.Prime,e p*Real.log p ≤
      c*Real.log 4*ε*N^2 := by
  have hs : ∑p∈(Finset.Ioc 0 ⌊ε*N⌋₊).filter Nat.Prime,e p*Real.log p ≤
      c*N*Chebyshev.theta (ε*N) := by
    calc
      _ ≤ ∑p∈(Finset.Ioc 0 ⌊ε*N⌋₊).filter Nat.Prime,c*N*Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        exact mul_le_mul_of_nonneg_right (he p (Finset.mem_filter.mp hp).2)
          (Real.log_natCast_nonneg p)
      _ ≤ c*N*Chebyshev.theta (ε*N) := by
        rw [Chebyshev.theta_eq_sum_Icc,Finset.mul_sum]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
            ⟨Nat.zero_le _,(Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2⟩,
            (Finset.mem_filter.mp hp).2⟩
        · intro p hp _
          exact mul_nonneg (mul_nonneg hc hN) (Real.log_natCast_nonneg p)
  have ht := Chebyshev.theta_le_log4_mul_x (mul_nonneg hε hN)
  have hm := mul_le_mul_of_nonneg_left ht (mul_nonneg hc hN)
  nlinarith only [hs,hm]

/-- Exact finite charge for a source-prime exception or an affine wall point. -/
def exceptionCharge (P : CatalanMeasure.Parametric.Parameters) (J : Finset ℕ)
    (W : Finset (ℕ×ℕ)) (N p : ℕ) : ℕ :=
  if p∈exceptionWalls J W N then 2*P.n N else 0

theorem exceptionCharge_support (P : CatalanMeasure.Parametric.Parameters) (J : Finset ℕ)
    (W : Finset (ℕ×ℕ)) (N p : ℕ) (hp : p∉exceptionWalls J W N) :
    exceptionCharge P J W N p=0 := by simp [exceptionCharge,hp]

theorem exceptionCharge_bound (P : CatalanMeasure.Parametric.Parameters) (J : Finset ℕ)
    (W : Finset (ℕ×ℕ)) (N p : ℕ) :
    (exceptionCharge P J W N p:ℝ)≤(2*P.n0:ℝ)*(N:ℝ) := by
  unfold exceptionCharge
  split_ifs
  · simp [CatalanMeasure.Parametric.Parameters.n,Nat.cast_mul,mul_assoc]
  · exact_mod_cast (Nat.zero_le ((2*P.n0)*N))

end
end CatalanMeasure.GenD.Uniform.Arithmetic
