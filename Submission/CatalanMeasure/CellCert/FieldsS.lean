module

public import Submission.CatalanMeasure.CellCert.ScaledSeries
public import Submission.CatalanMeasure.LogFieldStability
public import Submission.CatalanMeasure.Cert.ShiftedFields

@[expose] public section

/-!
# The 728 fields (row, column, residual) of a trial pair

`rowFieldG α β γ u v` is the row field of the trial pair `(u, v)` with logarithmic weights
`α log |x| + β log (1 - x) - γ log (1 + x²)`:
`α log|x| + β log(1-x) - γ log(1+x²) - 4 T(u,x) - S(v,x)`  (the case `lam = 0`), and similarly for the
column field `b log s + q log(1-s) + 2 T(v,s)` (case `a = 0`) and the residual field
`-(9/10) log(1+x²) - 2 T(u,x)`.  Everything is generic in the sequences; the scaled instances are
`rowFieldS`, `colFieldS`, `resFieldS` (sequences `trialSeqS`).

Peeled versions `rowFieldGP`/`colFieldGP` remove the singular logarithm terms
(`α log|x|` when `f0`, `β log(1-x)` when `f1`; `b log s` / `q log(1-s)` for the column).
-/

open OAI.InternalCatalan Set Filter
open scoped Topology

namespace CatalanMeasure.CellCert
open CatalanMeasure.Cert
noncomputable section

/-! ### generic fields -/

def rowRegG (γ : ℝ) (u v : ℕ → ℝ) (x : ℝ) : ℝ :=
  -γ * Real.log (1 + x ^ 2) - 4 * barrierTrialT u x - barrierTrialS v x

def rowFieldGP (α β γ : ℝ) (f0 f1 : Bool) (u v : ℕ → ℝ) (x : ℝ) : ℝ :=
  (if f0 then 0 else α * Real.log |x|) + (if f1 then 0 else β * Real.log (1 - x)) +
    rowRegG γ u v x

def rowFieldG (α β γ : ℝ) (u v : ℕ → ℝ) (x : ℝ) : ℝ :=
  α * Real.log |x| + β * Real.log (1 - x) + rowRegG γ u v x

theorem rowFieldGP_false (α β γ : ℝ) (u v : ℕ → ℝ) :
    rowFieldGP α β γ false false u v = rowFieldG α β γ u v := by
  funext x; simp [rowFieldGP, rowFieldG]

theorem rowFieldG_eq (α β γ : ℝ) (u v : ℕ → ℝ) (x : ℝ) :
    rowFieldG α β γ u v x =
      α * Real.log |x| + β * Real.log (1 - x) - γ * Real.log (1 + x ^ 2) -
        4 * barrierTrialT u x - barrierTrialS v x := by
  unfold rowFieldG rowRegG; ring

def colRegG (v : ℕ → ℝ) (s : ℝ) : ℝ := 2 * barrierTrialT v s

def colFieldGP (b q : ℝ) (f0 f1 : Bool) (v : ℕ → ℝ) (s : ℝ) : ℝ :=
  (if f0 then 0 else b * Real.log s) + (if f1 then 0 else q * Real.log (1 - s)) + colRegG v s

def colFieldG (b q : ℝ) (v : ℕ → ℝ) (s : ℝ) : ℝ :=
  b * Real.log s + q * Real.log (1 - s) + colRegG v s

theorem colFieldGP_false (b q : ℝ) (v : ℕ → ℝ) :
    colFieldGP b q false false v = colFieldG b q v := by
  funext x; simp [colFieldGP, colFieldG]

def resFieldG (u : ℕ → ℝ) (x : ℝ) : ℝ :=
  -(9 / 10 : ℝ) * Real.log (1 + x ^ 2) - 2 * barrierTrialT u x

/-! ### continuity -/

theorem log_one_add_sq_continuous : Continuous (fun x : ℝ => Real.log (1 + x ^ 2)) :=
  Continuous.log (continuous_const.add (continuous_id.pow 2))
    (fun x => ne_of_gt (by positivity : (0 : ℝ) < 1 + x ^ 2))

theorem rowRegG_continuousOn (γ : ℝ) {u v : ℕ → ℝ} (hu : Summable (fun k => |u k|))
    (hv : Summable (fun k => |v k|)) : ContinuousOn (rowRegG γ u v) (Icc (-1 : ℝ) 1) :=
  (((log_one_add_sq_continuous.continuousOn.const_mul _).sub
    ((barrierTrialT_continuousOn u hu).const_mul _))).sub (barrierTrialS_continuousOn v hv)

theorem colRegG_continuousOn {v : ℕ → ℝ} (hv : Summable (fun k => |v k|)) :
    ContinuousOn (colRegG v) (Icc (-1 : ℝ) 1) :=
  (barrierTrialT_continuousOn v hv).const_mul _

theorem resFieldG_continuousOn {u : ℕ → ℝ} (hu : Summable (fun k => |u k|)) :
    ContinuousOn (resFieldG u) (Icc (-1 : ℝ) 1) :=
  ((log_one_add_sq_continuous.continuousOn.const_mul _)).sub
    ((barrierTrialT_continuousOn u hu).const_mul _)

theorem continuousOn_log_abs {S : Set ℝ} (h : (0 : ℝ) ∉ S) (c : ℝ) :
    ContinuousOn (fun x : ℝ => c * Real.log |x|) S := by
  intro x hx
  have hx0 : x ≠ 0 := fun h0 => h (h0 ▸ hx)
  have : ContinuousAt (fun y : ℝ => Real.log |y|) x := by
    simpa only [Real.log_abs] using Real.continuousAt_log hx0
  exact (this.continuousWithinAt).const_mul c

theorem continuousOn_log_one_sub {S : Set ℝ} (h : (1 : ℝ) ∉ S) (c : ℝ) :
    ContinuousOn (fun x : ℝ => c * Real.log (1 - x)) S := by
  intro x hx
  have hx1 : 1 - x ≠ 0 := fun h0 => h (by
    have : x = 1 := by linarith
    exact this ▸ hx)
  have : ContinuousAt (fun y : ℝ => Real.log (1 - y)) x :=
    (continuousAt_const.sub continuousAt_id).log hx1
  exact (this.continuousWithinAt).const_mul c

theorem continuousOn_log_id {S : Set ℝ} (h : (0 : ℝ) ∉ S) (c : ℝ) :
    ContinuousOn (fun x : ℝ => c * Real.log x) S := by
  intro x hx
  have hx0 : x ≠ 0 := fun h0 => h (h0 ▸ hx)
  exact ((Real.continuousAt_log hx0).continuousWithinAt).const_mul c

/-- The (peeled) row field is continuous on any `S ⊆ [-1,1]` avoiding the singularities that
are not peeled. -/
theorem rowFieldGP_continuousOn (α β γ : ℝ) (f0 f1 : Bool) {u v : ℕ → ℝ}
    (hu : Summable (fun k => |u k|)) (hv : Summable (fun k => |v k|)) {S : Set ℝ}
    (hS : S ⊆ Icc (-1 : ℝ) 1) (h0 : f0 = true ∨ (0 : ℝ) ∉ S) (h1 : f1 = true ∨ (1 : ℝ) ∉ S) :
    ContinuousOn (rowFieldGP α β γ f0 f1 u v) S := by
  have hr := (rowRegG_continuousOn γ hu hv).mono hS
  have a0 : ContinuousOn (fun x : ℝ => if f0 then (0 : ℝ) else α * Real.log |x|) S := by
    cases f0
    · simpa using continuousOn_log_abs (h0.resolve_left (by simp)) α
    · simpa using continuousOn_const
  have a1 : ContinuousOn (fun x : ℝ => if f1 then (0 : ℝ) else β * Real.log (1 - x)) S := by
    cases f1
    · simpa using continuousOn_log_one_sub (h1.resolve_left (by simp)) β
    · simpa using continuousOn_const
  exact (a0.add a1).add hr

theorem colFieldGP_continuousOn (b q : ℝ) (f0 f1 : Bool) {v : ℕ → ℝ}
    (hv : Summable (fun k => |v k|)) {S : Set ℝ}
    (hS : S ⊆ Icc (-1 : ℝ) 1) (h0 : f0 = true ∨ (0 : ℝ) ∉ S) (h1 : f1 = true ∨ (1 : ℝ) ∉ S) :
    ContinuousOn (colFieldGP b q f0 f1 v) S := by
  have hr := (colRegG_continuousOn hv).mono hS
  have a0 : ContinuousOn (fun x : ℝ => if f0 then (0 : ℝ) else b * Real.log x) S := by
    cases f0
    · simpa using continuousOn_log_id (h0.resolve_left (by simp)) b
    · simpa using continuousOn_const
  have a1 : ContinuousOn (fun x : ℝ => if f1 then (0 : ℝ) else q * Real.log (1 - x)) S := by
    cases f1
    · simpa using continuousOn_log_one_sub (h1.resolve_left (by simp)) q
    · simpa using continuousOn_const
  exact (a0.add a1).add hr

/-! ### endpoint behaviour and stability under the diagonal corrections -/

theorem rowFieldG_endpoint_bound {α β γ : ℝ} {u v : ℕ → ℝ} (hu : Summable (fun k => |u k|))
    (hv : Summable (fun k => |v k|)) (hα : 0 ≤ α) :
    ∃ K : ℝ, ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1, rowFieldG α β γ u v x ≤ β * Real.log (1 - x) + K := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (rowRegG_continuousOn γ hu hv)
  refine ⟨K, ?_⟩
  intro x hx
  have hxi : x ∈ Icc (-1 : ℝ) 1 := by
    rcases hx with hx | hx
    · exact ⟨hx.1, by linarith only [hx.2]⟩
    · exact ⟨by linarith only [hx.1], hx.2.le⟩
  have hlog : Real.log |x| ≤ 0 := Real.log_nonpos (abs_nonneg _) (abs_le.mpr hxi)
  have hterm : α * Real.log |x| ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hα hlog
  have hreg : rowRegG γ u v x ≤ K :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hK x hxi)
  unfold rowFieldG
  linarith only [hterm, hreg]

theorem rowFieldG_corrected_eventually {α β γ : ℝ} {u v : ℕ → ℝ} (hu : Summable (fun k => |u k|))
    (hv : Summable (fun k => |v k|)) (hα : 0 ≤ α) (hβ : 0 < β) {M a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hM : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1, rowFieldG α β γ u v x ≤ M)
    (t : ℕ → ℝ) (ht0 : ∀ N, 0 ≤ t N) (ht : Tendsto t atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      rowFieldG α β γ u v x + t N * (a * Real.log (1 + x ^ 2) - b * Real.log (1 - x)) ≤ M + ε := by
  obtain ⟨K, hK⟩ := rowFieldG_endpoint_bound (γ := γ) (β := β) hu hv hα
  apply CatalanMeasure.log_field_correction_eventually hβ ha hb ?_ hM hK t ht0 ht hε
  intro x hx
  rcases hx with hx | hx
  · exact ⟨hx.1, by linarith only [hx.2]⟩
  · exact ⟨by linarith only [hx.1], hx.2⟩

theorem colFieldG_endpoint_bound {b q : ℝ} {v : ℕ → ℝ} (hv : Summable (fun k => |v k|))
    (hb : 0 ≤ b) :
    ∃ K : ℝ, ∀ x ∈ Ioo (0 : ℝ) 1, colFieldG b q v x ≤ q * Real.log (1 - x) + K := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (colRegG_continuousOn hv)
  refine ⟨K, ?_⟩
  intro x hx
  have hlog : Real.log x ≤ 0 := Real.log_nonpos hx.1.le hx.2.le
  have hterm : b * Real.log x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hlog
  have hx' : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith only [hx.1], hx.2.le⟩
  have hreg : colRegG v x ≤ K :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hK x hx')
  unfold colFieldG
  linarith only [hterm, hreg]

theorem colFieldG_corrected_eventually {b q : ℝ} {v : ℕ → ℝ} (hv : Summable (fun k => |v k|))
    (hb : 0 ≤ b) (hq : 0 < q) {M : ℝ} (hM : ∀ x ∈ Ioo (0 : ℝ) 1, colFieldG b q v x ≤ M)
    (t : ℕ → ℝ) (ht0 : ∀ N, 0 ≤ t N) (ht : Tendsto t atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (0 : ℝ) 1, colFieldG b q v x - t N * Real.log (1 - x) ≤ M + ε := by
  obtain ⟨K, hK⟩ := colFieldG_endpoint_bound (q := q) hv hb
  have hh := CatalanMeasure.log_field_correction_eventually hq (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : (0 : ℝ) ≤ 1) (fun x hx => ⟨by linarith only [hx.1], hx.2⟩) hM hK t ht0 ht hε
  simpa only [zero_mul, one_mul, zero_sub, zero_add, mul_neg, sub_eq_add_neg] using hh

/-! ### the scaled instances -/

def rowFieldS (R : RowWeights) (Pc Vc : List ℤ) (P V : List TailQ) : ℝ → ℝ :=
  rowFieldG (R.alpha : ℝ) (R.beta : ℝ) (R.gamma : ℝ) (trialSeqS Pc P) (trialSeqS Vc V)

def rowFieldSP (R : RowWeights) (Pc Vc : List ℤ) (P V : List TailQ) (f0 f1 : Bool) : ℝ → ℝ :=
  rowFieldGP (R.alpha : ℝ) (R.beta : ℝ) (R.gamma : ℝ) f0 f1 (trialSeqS Pc P) (trialSeqS Vc V)

def colFieldS (C : ColumnWeights) (Vc : List ℤ) (V : List TailQ) : ℝ → ℝ :=
  colFieldG (C.b : ℝ) (C.q : ℝ) (trialSeqS Vc V)

def colFieldSP (C : ColumnWeights) (Vc : List ℤ) (V : List TailQ) (f0 f1 : Bool) : ℝ → ℝ :=
  colFieldGP (C.b : ℝ) (C.q : ℝ) f0 f1 (trialSeqS Vc V)

def resFieldS (Pc : List ℤ) (P : List TailQ) : ℝ → ℝ := resFieldG (trialSeqS Pc P)

theorem rowFieldSP_false (R : RowWeights) (Pc Vc : List ℤ) (P V : List TailQ) :
    rowFieldSP R Pc Vc P V false false = rowFieldS R Pc Vc P V :=
  rowFieldGP_false _ _ _ _ _

theorem colFieldSP_false (C : ColumnWeights) (Vc : List ℤ) (V : List TailQ) :
    colFieldSP C Vc V false false = colFieldS C Vc V :=
  colFieldGP_false _ _ _

theorem rowFieldSP_continuousOn (R : RowWeights) {Pc Vc : List ℤ} {P V : List TailQ}
    (hP : tailsInDisk P = true) (hV : tailsInDisk V = true) (f0 f1 : Bool) {S : Set ℝ}
    (hS : S ⊆ Icc (-1 : ℝ) 1) (h0 : f0 = true ∨ (0 : ℝ) ∉ S) (h1 : f1 = true ∨ (1 : ℝ) ∉ S) :
    ContinuousOn (rowFieldSP R Pc Vc P V f0 f1) S :=
  rowFieldGP_continuousOn _ _ _ f0 f1 (trialSeqS_summable hP).1 (trialSeqS_summable hV).1 hS h0 h1

theorem colFieldSP_continuousOn (C : ColumnWeights) {Vc : List ℤ} {V : List TailQ}
    (hV : tailsInDisk V = true) (f0 f1 : Bool) {S : Set ℝ}
    (hS : S ⊆ Icc (-1 : ℝ) 1) (h0 : f0 = true ∨ (0 : ℝ) ∉ S) (h1 : f1 = true ∨ (1 : ℝ) ∉ S) :
    ContinuousOn (colFieldSP C Vc V f0 f1) S :=
  colFieldGP_continuousOn _ _ f0 f1 (trialSeqS_summable hV).1 hS h0 h1

theorem resFieldS_continuousOn {Pc : List ℤ} {P : List TailQ} (hP : tailsInDisk P = true) :
    ContinuousOn (resFieldS Pc P) (Icc (-1 : ℝ) 1) :=
  resFieldG_continuousOn (trialSeqS_summable hP).1

end
end CatalanMeasure.CellCert
