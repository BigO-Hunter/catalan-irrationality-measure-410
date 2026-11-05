module

public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.EvalRefLog

@[expose] public section

/-!
# `refBil` depends only on the signed density (Theorem A, lane E1b, route (g))

The lifted references of the regenerated trial data have `P` and `N` pieces whose difference `P - N` is,
on each species, one (or two) polynomial piece(s).  The bilinear energy `refBil` only sees the signed
density `P - N`, so its log form can be computed on the *merged* pieces `Rm` (the pair jobs of
`refPlan Rm Sm` instead of `refPlan R S`).

* `sgnT R = R.pT ++ R.nT.map negQ`, `sgnF R`: the signed piece lists (`negQ` negates the coefficients).
* `sdens X` is the density of a piece list a.e. (`indicator (Ioc lo hi) p`), `Sfun X f = Σ ∫_X p f`.
* `RefinesOK cuts X Y` (decidable): all endpoints are in `cuts`, and for every pair `u < v` of consecutive
  cuts the covering polynomials of `X` and `Y` on `(u, v)` agree (exact rational coefficients).  It implies
  `sdens X = sdens Y` a.e. (`sameDens_of_refines`).
* `MergeOK cT cF R Rm` = `RefinesOK` for the `T` and the `F` species.
* `refBilLF_merge`: `(refBilLF R S).eval = (refBilLF Rm Sm).eval` under `MergeOK`; consumers
  `refBil_enc_merged`, `refEnergy_enc_merged` (same as `refBil_enc`/`refEnergy_enc` with `refPlan Rm Sm`,
  `Rm` need not have nonnegative densities: only `lo ≤ hi`, which `MergeOK` gives).
* For `Rm` with empty negative parts `refPlan_merged` reduces the plan to `jobsBil (-1) mT mF mT' mF'`.
-/

namespace CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.ReflectionEnergy
open CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval
open CatalanMeasure.Cert (qabs)
open MeasureTheory Set

noncomputable section

/-! ### 1. Negation of a piece -/

def negQ (q : PieceQ) : PieceQ := ⟨q.lo, q.hi, q.p.map (fun a => -a)⟩

@[simp] theorem negQ_lo (q : PieceQ) : (negQ q).lo = q.lo := rfl
@[simp] theorem negQ_hi (q : PieceQ) : (negQ q).hi = q.hi := rfl

theorem polyTow_map_neg (c : List ℚ) (x : ℝ) :
    polyTow (c.map (fun a => -a)) 0 x = - polyTow c 0 x := by
  have e : c.map (fun a => -a) = c.map (fun t => (-1 : ℚ) * t) := by
    apply List.map_congr_left
    intro a _
    ring
  rw [e, polyTow_zero_map_mul]
  simp

theorem polyTow_negQ (q : PieceQ) (x : ℝ) : polyTow (negQ q).p 0 x = - polyTow q.p 0 x :=
  polyTow_map_neg q.p x

theorem cast_le_of (q : PieceQ) (h : q.lo ≤ q.hi) : (q.lo : ℝ) ≤ q.hi := by
  exact_mod_cast h

/-! ### 2. `Sfun`: the piece sum of integrals against a function -/

/-- `Σ_{q ∈ X} ∫_{q.lo}^{q.hi} p_q(t) f(t) dt`. -/
def Sfun (X : List PieceQ) (f : ℝ → ℝ) : ℝ :=
  (X.map (fun q => ∫ t in (q.lo : ℝ)..(q.hi : ℝ), polyTow q.p 0 t * f t)).sum

theorem Sfun_cons (q : PieceQ) (X : List PieceQ) (f : ℝ → ℝ) :
    Sfun (q :: X) f = (∫ t in (q.lo : ℝ)..(q.hi : ℝ), polyTow q.p 0 t * f t) + Sfun X f := by
  simp only [Sfun, List.map_cons, List.sum_cons]

theorem Sfun_map_negQ (f : ℝ → ℝ) : ∀ X : List PieceQ, Sfun (X.map negQ) f = - Sfun X f
  | [] => by simp [Sfun]
  | q :: X => by
    have ih := Sfun_map_negQ f X
    have e : (∫ t in ((negQ q).lo : ℝ)..((negQ q).hi : ℝ), polyTow (negQ q).p 0 t * f t) =
        -∫ t in (q.lo : ℝ)..(q.hi : ℝ), polyTow q.p 0 t * f t := by
      rw [← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_congr (fun t _ => by
        show polyTow (negQ q).p 0 t * f t = -(polyTow q.p 0 t * f t)
        rw [polyTow_negQ]
        ring)
    rw [List.map_cons, Sfun_cons, Sfun_cons, ih, e]
    ring

theorem Sfun_neg_fun (g : ℝ → ℝ) : ∀ X : List PieceQ, Sfun X (fun x => - g x) = - Sfun X g
  | [] => by simp [Sfun]
  | q :: X => by
    have ih := Sfun_neg_fun g X
    have e : (∫ t in (q.lo : ℝ)..(q.hi : ℝ), polyTow q.p 0 t * (-g t)) =
        -∫ t in (q.lo : ℝ)..(q.hi : ℝ), polyTow q.p 0 t * g t := by
      rw [← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_congr (fun t _ => by
        show polyTow q.p 0 t * (-g t) = -(polyTow q.p 0 t * g t)
        ring)
    rw [Sfun_cons, Sfun_cons, ih, e]
    ring

/-- The log form of `entLF` is `Sfun A (Gsum r B)` (pieces with `lo ≤ hi`). -/
theorem ent_eval (B : List PieceQ) (r : Bool) :
    ∀ A : List PieceQ, (∀ q ∈ A, q.lo ≤ q.hi) → (entLF A B r).eval = Sfun A (Gsum r B)
  | [], _ => by simp [entLF, LF.sumL, LF.eval, termsEval, Sfun]
  | q :: A, h => by
    have ih := ent_eval B r A (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))
    have h1 := int_dens_Gsum q (h q List.mem_cons_self) r B
    have hc : entLF (q :: A) B r = (rowLF q B r).add (entLF A B r) := rfl
    rw [hc, LF.eval_add, Sfun_cons, ih, h1]

/-! ### 3. Density of a piece list, almost-everywhere equality -/

/-- The (a.e.) density of a piece list. -/
def sdens (X : List PieceQ) (t : ℝ) : ℝ :=
  (X.map (fun q => Set.indicator (Ioc (q.lo : ℝ) (q.hi : ℝ)) (fun s => polyTow q.p 0 s) t)).sum

theorem sdens_cons (q : PieceQ) (X : List PieceQ) (t : ℝ) :
    sdens (q :: X) t =
      Set.indicator (Ioc (q.lo : ℝ) (q.hi : ℝ)) (fun s => polyTow q.p 0 s) t + sdens X t := by
  simp only [sdens, List.map_cons, List.sum_cons]

theorem sdens_cons_mul (q : PieceQ) (X : List PieceQ) (f : ℝ → ℝ) (t : ℝ) :
    sdens (q :: X) t * f t =
      Set.indicator (Ioc (q.lo : ℝ) (q.hi : ℝ)) (fun s => polyTow q.p 0 s) t * f t +
        sdens X t * f t := by
  rw [sdens_cons]
  ring

theorem ind_mul (q : PieceQ) (f : ℝ → ℝ) (t : ℝ) :
    Set.indicator (Ioc (q.lo : ℝ) (q.hi : ℝ)) (fun s => polyTow q.p 0 s) t * f t =
      Set.indicator (Ioc (q.lo : ℝ) (q.hi : ℝ)) (fun s => polyTow q.p 0 s * f s) t := by
  by_cases h : t ∈ Ioc (q.lo : ℝ) (q.hi : ℝ)
  · rw [Set.indicator_apply, Set.indicator_apply, if_pos h, if_pos h]
  · rw [Set.indicator_apply, Set.indicator_apply, if_neg h, if_neg h]
    ring

theorem integrable_ind (q : PieceQ) (hle : q.lo ≤ q.hi) (f : ℝ → ℝ)
    (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b) :
    Integrable (fun t => Set.indicator (Ioc (q.lo : ℝ) (q.hi : ℝ))
      (fun s => polyTow q.p 0 s) t * f t) := by
  have h1 : IntervalIntegrable (fun s => polyTow q.p 0 s * f s) volume (q.lo : ℝ) (q.hi : ℝ) :=
    (hf _ _).continuousOn_mul (continuous_polyTow0 q.p).continuousOn
  have h2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le (cast_le_of q hle)).mp h1
  have h3 : Integrable (Set.indicator (Ioc (q.lo : ℝ) (q.hi : ℝ))
      (fun s => polyTow q.p 0 s * f s)) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr h2
  exact h3.congr (Filter.Eventually.of_forall (fun t => (ind_mul q f t).symm))

theorem integrable_sdens (f : ℝ → ℝ) (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b) :
    ∀ X : List PieceQ, (∀ q ∈ X, q.lo ≤ q.hi) → Integrable (fun t => sdens X t * f t)
  | [], _ => by
    refine (integrable_zero ℝ ℝ volume).congr (Filter.Eventually.of_forall (fun t => ?_))
    show (0 : ℝ) = sdens [] t * f t
    simp [sdens]
  | q :: X, h => by
    have hh := (integrable_ind q (h q List.mem_cons_self) f hf).add
      (integrable_sdens f hf X (fun q' hq' => h q' (List.mem_cons_of_mem _ hq')))
    exact hh.congr (Filter.Eventually.of_forall (fun t => (sdens_cons_mul q X f t).symm))

theorem Sfun_eq_integral (f : ℝ → ℝ) (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b) :
    ∀ X : List PieceQ, (∀ q ∈ X, q.lo ≤ q.hi) → Sfun X f = ∫ t, sdens X t * f t
  | [], _ => by simp [Sfun, sdens]
  | q :: X, h => by
    have hq := h q List.mem_cons_self
    have hX : ∀ q' ∈ X, q'.lo ≤ q'.hi := fun q' hq' => h q' (List.mem_cons_of_mem _ hq')
    have ih := Sfun_eq_integral f hf X hX
    have hi1 := integrable_ind q hq f hf
    have hi2 := integrable_sdens f hf X hX
    have e1 : (∫ t in (q.lo : ℝ)..(q.hi : ℝ), polyTow q.p 0 t * f t) =
        ∫ t, Set.indicator (Ioc (q.lo : ℝ) (q.hi : ℝ)) (fun s => polyTow q.p 0 s) t * f t := by
      rw [intervalIntegral.integral_of_le (cast_le_of q hq),
        ← integral_indicator measurableSet_Ioc]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun t => (ind_mul q f t).symm))
    have e3 : (∫ t, sdens (q :: X) t * f t) =
        (∫ t, Set.indicator (Ioc (q.lo : ℝ) (q.hi : ℝ)) (fun s => polyTow q.p 0 s) t * f t) +
          ∫ t, sdens X t * f t := by
      rw [← integral_add hi1 hi2]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun t => sdens_cons_mul q X f t))
    rw [Sfun_cons, e1, ih, e3]

theorem Sfun_congr_ae {X Y : List PieceQ} (hX : ∀ q ∈ X, q.lo ≤ q.hi) (hY : ∀ q ∈ Y, q.lo ≤ q.hi)
    (f : ℝ → ℝ) (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (h : ∀ᵐ t : ℝ, sdens X t = sdens Y t) : Sfun X f = Sfun Y f := by
  rw [Sfun_eq_integral f hf X hX, Sfun_eq_integral f hf Y hY]
  exact integral_congr_ae (h.mono (fun t ht => by
    show sdens X t * f t = sdens Y t * f t
    rw [ht]))

/-! ### 4. The inner potential `Gsum` as a piece sum -/

theorem pot_eq_integral (q : PieceQ) (hle : q.lo ≤ q.hi) (w : ℝ) :
    q.toPiece.pot w = ∫ t in (q.lo : ℝ)..(q.hi : ℝ), polyTow q.p 0 t * Real.log |t - w| := by
  have h := polyPot q.toPiece.n q.toPiece.p (cast_le_of q hle) w
  calc q.toPiece.pot w
      = ∫ t in (q.lo : ℝ)..(q.hi : ℝ), pc q.toPiece.n q.toPiece.p t * Real.log |t - w| := h.symm
    _ = ∫ t in (q.lo : ℝ)..(q.hi : ℝ), polyTow q.p 0 t * Real.log |t - w| :=
        intervalIntegral.integral_congr (fun t _ => by
          show q.toPiece.dens t * _ = polyTow q.p 0 t * _
          rw [dens_eq])

theorem logPot_eq_Sfun (w : ℝ) : ∀ B : List PieceQ, (∀ q ∈ B, q.lo ≤ q.hi) →
    logPot (B.map PieceQ.toPiece) w = Sfun B (fun y => Real.log |y - w|)
  | [], _ => by simp [logPot, Sfun]
  | q :: B, h => by
    have ih := logPot_eq_Sfun w B (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))
    have h1 := pot_eq_integral q (h q List.mem_cons_self) w
    simp only [logPot, List.map_cons, List.sum_cons, Sfun_cons] at ih ⊢
    linarith

/-- The centre of the logarithm: `x` (same species) or `-x` (opposite species, reflection). -/
def ctr : Bool → ℝ → ℝ
  | false, x => x
  | true, x => -x

theorem Gsum_eq_Sfun (r : Bool) (B : List PieceQ) (hB : ∀ q ∈ B, q.lo ≤ q.hi) (x : ℝ) :
    Gsum r B x = Sfun B (fun y => Real.log |y - ctr r x|) := by
  cases r
  · show Gsum false B x = Sfun B (fun y => Real.log |y - x|)
    rw [← logPot_Gsum0, logPot_eq_Sfun x B hB]
  · show Gsum true B x = Sfun B (fun y => Real.log |y - -x|)
    rw [← logPot_Gsum1, logPot_eq_Sfun (-x) B hB]

theorem Gsum_congr_ae (r : Bool) {X Y : List PieceQ} (hX : ∀ q ∈ X, q.lo ≤ q.hi)
    (hY : ∀ q ∈ Y, q.lo ≤ q.hi) (h : ∀ᵐ t : ℝ, sdens X t = sdens Y t) (x : ℝ) :
    Gsum r X x = Gsum r Y x := by
  rw [Gsum_eq_Sfun r X hX x, Gsum_eq_Sfun r Y hY x]
  exact Sfun_congr_ae hX hY (fun y => Real.log |y - ctr r x|)
    (fun a b => intervalIntegrable_log_abs_sub (ctr r x) a b) h

theorem le_map_negQ {B : List PieceQ} (hB : ∀ q ∈ B, q.lo ≤ q.hi) :
    ∀ q ∈ B.map negQ, q.lo ≤ q.hi := by
  intro q hq
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  exact hB q0 hq0

theorem Gsum_map_negQ (r : Bool) {B : List PieceQ} (hB : ∀ q ∈ B, q.lo ≤ q.hi) (x : ℝ) :
    Gsum r (B.map negQ) x = - Gsum r B x := by
  rw [Gsum_eq_Sfun r _ (le_map_negQ hB) x, Gsum_eq_Sfun r _ hB x, Sfun_map_negQ]

/-! ### 5. Bilinearity of `entLF` -/

theorem ent_append_left (A A' B : List PieceQ) (r : Bool) :
    (entLF (A ++ A') B r).eval = (entLF A B r).eval + (entLF A' B r).eval := by
  simp only [entLF, List.map_append, LF.eval_sumL_append]

theorem ent_append_right (A B B' : List PieceQ) (r : Bool) :
    (entLF A (B ++ B') r).eval = (entLF A B r).eval + (entLF A B' r).eval := by
  induction A with
  | nil => simp [entLF, LF.sumL, LF.eval, termsEval]
  | cons q A ih =>
    have hrow : (rowLF q (B ++ B') r).eval = (rowLF q B r).eval + (rowLF q B' r).eval := by
      simp only [rowLF, List.map_append, LF.eval_sumL_append]
    have hc : ∀ B'' : List PieceQ, entLF (q :: A) B'' r = (rowLF q B'' r).add (entLF A B'' r) :=
      fun _ => rfl
    rw [hc, hc, hc, LF.eval_add, LF.eval_add, LF.eval_add, ih, hrow]
    ring

theorem ent_map_negQ_left (A B : List PieceQ) (r : Bool) (hA : ∀ q ∈ A, q.lo ≤ q.hi) :
    (entLF (A.map negQ) B r).eval = - (entLF A B r).eval := by
  rw [ent_eval B r _ (le_map_negQ hA), ent_eval B r _ hA, Sfun_map_negQ]

theorem ent_map_negQ_right (A B : List PieceQ) (r : Bool) (hA : ∀ q ∈ A, q.lo ≤ q.hi)
    (hB : ∀ q ∈ B, q.lo ≤ q.hi) :
    (entLF A (B.map negQ) r).eval = - (entLF A B r).eval := by
  rw [ent_eval (B.map negQ) r A hA, ent_eval B r A hA]
  have hG : Gsum r (B.map negQ) = fun x => - Gsum r B x := funext (Gsum_map_negQ r hB)
  rw [hG]
  exact Sfun_neg_fun (Gsum r B) A

theorem ent_signed (P N P' N' : List PieceQ) (r : Bool) (hP : ∀ q ∈ P, q.lo ≤ q.hi)
    (hN : ∀ q ∈ N, q.lo ≤ q.hi) (hP' : ∀ q ∈ P', q.lo ≤ q.hi) (hN' : ∀ q ∈ N', q.lo ≤ q.hi) :
    (entLF (P ++ N.map negQ) (P' ++ N'.map negQ) r).eval =
      (entLF P P' r).eval - (entLF P N' r).eval - (entLF N P' r).eval + (entLF N N' r).eval := by
  have e1 := ent_append_left P (N.map negQ) (P' ++ N'.map negQ) r
  have e2 := ent_append_right P P' (N'.map negQ) r
  have e3 := ent_append_right (N.map negQ) P' (N'.map negQ) r
  have e4 := ent_map_negQ_left N P' r hN
  have e5 := ent_map_negQ_left N (N'.map negQ) r hN
  have e6 := ent_map_negQ_right P N' r hP hN'
  have e7 := ent_map_negQ_right N N' r hN hN'
  linarith

/-! ### 6. Signed lists and the expansion of `refBilLF` -/

def sgnT (R : RefQ) : List PieceQ := R.pT ++ R.nT.map negQ
def sgnF (R : RefQ) : List PieceQ := R.pF ++ R.nF.map negQ

/-- All pieces of `R` have `lo ≤ hi`. -/
abbrev RefQ.LE (R : RefQ) : Prop :=
  (∀ q ∈ R.pT, q.lo ≤ q.hi) ∧ (∀ q ∈ R.pF, q.lo ≤ q.hi) ∧
  (∀ q ∈ R.nT, q.lo ≤ q.hi) ∧ (∀ q ∈ R.nF, q.lo ≤ q.hi)

theorem bil_eval (A1 A0 B1 B0 : List PieceQ) :
    (bilLF A1 A0 B1 B0).eval = (entLF A1 B1 false).eval + (entLF A1 B0 true).eval +
      (entLF A0 B1 true).eval + (entLF A0 B0 false).eval := by
  simp only [bilLF, LF.eval_add]
  ring

theorem refBilLF_eval_expand (R S : RefQ) : (refBilLF R S).eval =
    -(bilLF R.pT R.pF S.pT S.pF).eval + (bilLF R.pT R.pF S.nT S.nF).eval +
      (bilLF R.nT R.nF S.pT S.pF).eval - (bilLF R.nT R.nF S.nT S.nF).eval := by
  simp only [refBilLF, LF.eval_sumL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    LF.eval_smul]
  push_cast
  ring

/-- `refBil` is minus the energy bilinear form of the signed lists. -/
theorem refBilLF_signed (R S : RefQ) (hR : R.LE) (hS : S.LE) :
    (refBilLF R S).eval = -(bilLF (sgnT R) (sgnF R) (sgnT S) (sgnF S)).eval := by
  have s1 := ent_signed R.pT R.nT S.pT S.nT false hR.1 hR.2.2.1 hS.1 hS.2.2.1
  have s2 := ent_signed R.pT R.nT S.pF S.nF true hR.1 hR.2.2.1 hS.2.1 hS.2.2.2
  have s3 := ent_signed R.pF R.nF S.pT S.nT true hR.2.1 hR.2.2.2 hS.1 hS.2.2.1
  have s4 := ent_signed R.pF R.nF S.pF S.nF false hR.2.1 hR.2.2.2 hS.2.1 hS.2.2.2
  rw [refBilLF_eval_expand]
  simp only [bil_eval, sgnT, sgnF]
  linarith

/-! ### 7. The decidable refinement check and the a.e. equality of densities -/

/-- Coefficients of the sum of the polynomials of the pieces of `X` covering `[u, v]`. -/
def covPoly (X : List PieceQ) (u v : ℚ) : List ℚ :=
  X.foldr (fun q acc => if q.lo ≤ u ∧ v ≤ q.hi then vecAdd q.p acc else acc) []

def covDiff (X Y : List PieceQ) (u v : ℚ) : List ℚ :=
  vecAdd (covPoly X u v) ((covPoly Y u v).map (fun a => -a))

theorem covPoly_cons (q : PieceQ) (X : List PieceQ) (u v : ℚ) :
    covPoly (q :: X) u v =
      if q.lo ≤ u ∧ v ≤ q.hi then vecAdd q.p (covPoly X u v) else covPoly X u v := by
  simp only [covPoly, List.foldr_cons]

theorem polyTow_covDiff (X Y : List PieceQ) (u v : ℚ) (x : ℝ) :
    polyTow (covDiff X Y u v) 0 x = polyTow (covPoly X u v) 0 x - polyTow (covPoly Y u v) 0 x := by
  unfold covDiff
  rw [polyTow_zero_vecAdd, polyTow_map_neg]
  ring

theorem polyTow_zero_of_zero : ∀ (l : List ℚ), (∀ a ∈ l, a = 0) → ∀ x : ℝ, polyTow l 0 x = 0
  | [], _, x => polyTow_zero_nil x
  | a :: l, h, x => by
    have ha : a = 0 := h a List.mem_cons_self
    have hl := polyTow_zero_of_zero l (fun b hb => h b (List.mem_cons_of_mem _ hb)) x
    rw [polyTow_zero_cons, hl, ha]
    simp

/-- **The refinement check.**  `cuts` contains every endpoint, and on every pair of consecutive cuts
the covering polynomials of `X` and `Y` have the same coefficients. -/
def RefinesOK (cuts : List ℚ) (X Y : List PieceQ) : Prop :=
  (∀ q ∈ X ++ Y, q.lo ∈ cuts ∧ q.hi ∈ cuts ∧ q.lo ≤ q.hi) ∧
  ∀ u ∈ cuts, ∀ v ∈ cuts, u < v → (∀ c ∈ cuts, ¬ (u < c ∧ c < v)) →
    ∀ a ∈ covDiff X Y u v, a = 0

instance (cuts : List ℚ) (X Y : List PieceQ) : Decidable (RefinesOK cuts X Y) := by
  unfold RefinesOK
  infer_instance

theorem RefinesOK.le_left {cuts : List ℚ} {X Y : List PieceQ} (h : RefinesOK cuts X Y) :
    ∀ q ∈ X, q.lo ≤ q.hi := fun q hq => (h.1 q (List.mem_append_left _ hq)).2.2

theorem RefinesOK.le_right {cuts : List ℚ} {X Y : List PieceQ} (h : RefinesOK cuts X Y) :
    ∀ q ∈ Y, q.lo ≤ q.hi := fun q hq => (h.1 q (List.mem_append_right _ hq)).2.2

theorem sdens_eq_zero (t : ℝ) : ∀ X : List PieceQ, (∀ q ∈ X, t ∉ Ioc (q.lo : ℝ) (q.hi : ℝ)) →
    sdens X t = 0
  | [], _ => rfl
  | q :: X, h => by
    have h0 := sdens_eq_zero t X (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))
    have h1 : Set.indicator (Ioc (q.lo : ℝ) (q.hi : ℝ)) (fun s => polyTow q.p 0 s) t = 0 := by
      rw [Set.indicator_apply, if_neg (h q List.mem_cons_self)]
    rw [sdens_cons, h0, h1, add_zero]

theorem sdens_eq_cov (u v : ℚ) (t : ℝ) :
    ∀ X : List PieceQ, (∀ q ∈ X, (t ∈ Ioc (q.lo : ℝ) (q.hi : ℝ) ↔ (q.lo ≤ u ∧ v ≤ q.hi))) →
      sdens X t = polyTow (covPoly X u v) 0 t
  | [], _ => by
    show (0 : ℝ) = polyTow [] 0 t
    rw [polyTow_zero_nil]
  | q :: X, h => by
    have ih := sdens_eq_cov u v t X (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))
    have hq := h q List.mem_cons_self
    rw [sdens_cons, ih, covPoly_cons]
    by_cases hc : q.lo ≤ u ∧ v ≤ q.hi
    · rw [if_pos hc, polyTow_zero_vecAdd, Set.indicator_apply, if_pos (hq.mpr hc)]
    · have hn : t ∉ Ioc (q.lo : ℝ) (q.hi : ℝ) := fun hm => hc (hq.mp hm)
      rw [if_neg hc, Set.indicator_apply, if_neg hn, zero_add]

theorem exists_cut_below (cuts : List ℚ) (t : ℝ) (h : ∃ c ∈ cuts, (c : ℝ) < t) :
    ∃ u ∈ cuts, (u : ℝ) < t ∧ ∀ c ∈ cuts, (c : ℝ) < t → c ≤ u := by
  classical
  have hne : (cuts.toFinset.filter (fun c : ℚ => (c : ℝ) < t)).Nonempty := by
    obtain ⟨c, hc, hct⟩ := h
    exact ⟨c, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hc, hct⟩⟩
  refine ⟨(cuts.toFinset.filter (fun c : ℚ => (c : ℝ) < t)).max' hne, ?_, ?_, ?_⟩
  · exact List.mem_toFinset.mp (Finset.mem_filter.mp (Finset.max'_mem _ hne)).1
  · exact (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
  · intro c hc hct
    exact Finset.le_max' _ c (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hc, hct⟩)

theorem exists_cut_above (cuts : List ℚ) (t : ℝ) (h : ∃ c ∈ cuts, t < (c : ℝ)) :
    ∃ v ∈ cuts, t < (v : ℝ) ∧ ∀ c ∈ cuts, t < (c : ℝ) → v ≤ c := by
  classical
  have hne : (cuts.toFinset.filter (fun c : ℚ => t < (c : ℝ))).Nonempty := by
    obtain ⟨c, hc, hct⟩ := h
    exact ⟨c, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hc, hct⟩⟩
  refine ⟨(cuts.toFinset.filter (fun c : ℚ => t < (c : ℝ))).min' hne, ?_, ?_, ?_⟩
  · exact List.mem_toFinset.mp (Finset.mem_filter.mp (Finset.min'_mem _ hne)).1
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
  · intro c hc hct
    exact Finset.min'_le _ c (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hc, hct⟩)

/-- Away from the cuts the two densities agree. -/
theorem sdens_eq_of_not_cut {cuts : List ℚ} {X Y : List PieceQ} (h : RefinesOK cuts X Y) (t : ℝ)
    (ht : t ∉ cuts.map (fun c : ℚ => (c : ℝ))) : sdens X t = sdens Y t := by
  have hcut : ∀ c ∈ cuts, (c : ℝ) ≠ t := fun c hc hct => ht (List.mem_map.mpr ⟨c, hc, hct⟩)
  by_cases hL : ∃ c ∈ cuts, (c : ℝ) < t
  · by_cases hU : ∃ c ∈ cuts, t < (c : ℝ)
    · obtain ⟨u, hu, hut, huc⟩ := exists_cut_below cuts t hL
      obtain ⟨v, hv, hvt, hvc⟩ := exists_cut_above cuts t hU
      have huv : u < v := Rat.cast_lt.mp (hut.trans hvt)
      have hnone : ∀ c ∈ cuts, ¬ (u < c ∧ c < v) := by
        rintro c hc ⟨h1, h2⟩
        rcases lt_trichotomy (c : ℝ) t with hlt | heq | hgt
        · exact absurd (huc c hc hlt) (not_le.mpr h1)
        · exact hcut c hc heq
        · exact absurd (hvc c hc hgt) (not_le.mpr h2)
      have hz := h.2 u hu v hv huv hnone
      have hzero : polyTow (covDiff X Y u v) 0 t = 0 := polyTow_zero_of_zero _ hz t
      have hiff : ∀ q ∈ X ++ Y, (t ∈ Ioc (q.lo : ℝ) (q.hi : ℝ) ↔ (q.lo ≤ u ∧ v ≤ q.hi)) := by
        intro q hq
        obtain ⟨hlo, hhi, -⟩ := h.1 q hq
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨huc q.lo hlo h1, ?_⟩
          have h3 : t < (q.hi : ℝ) := lt_of_le_of_ne h2 (fun e => hcut q.hi hhi e.symm)
          exact hvc q.hi hhi h3
        · rintro ⟨h1, h2⟩
          have h1' : (q.lo : ℝ) ≤ u := by exact_mod_cast h1
          have h2' : (v : ℝ) ≤ q.hi := by exact_mod_cast h2
          exact ⟨lt_of_le_of_lt h1' hut, le_trans hvt.le h2'⟩
      have hX := sdens_eq_cov u v t X (fun q hq => hiff q (List.mem_append_left _ hq))
      have hY := sdens_eq_cov u v t Y (fun q hq => hiff q (List.mem_append_right _ hq))
      rw [polyTow_covDiff] at hzero
      rw [hX, hY]
      linarith
    · push_neg at hU
      have hz : ∀ Z : List PieceQ, (∀ q ∈ Z, q.hi ∈ cuts) → sdens Z t = 0 := by
        intro Z hZ
        refine sdens_eq_zero t Z (fun q hq hm => ?_)
        have h3 : (q.hi : ℝ) < t := lt_of_le_of_ne (hU _ (hZ q hq)) (hcut _ (hZ q hq))
        exact absurd hm.2 (not_le.mpr h3)
      rw [hz X (fun q hq => (h.1 q (List.mem_append_left _ hq)).2.1),
        hz Y (fun q hq => (h.1 q (List.mem_append_right _ hq)).2.1)]
  · push_neg at hL
    have hz : ∀ Z : List PieceQ, (∀ q ∈ Z, q.lo ∈ cuts) → sdens Z t = 0 := by
      intro Z hZ
      refine sdens_eq_zero t Z (fun q hq hm => ?_)
      exact absurd hm.1 (not_lt.mpr (hL _ (hZ q hq)))
    rw [hz X (fun q hq => (h.1 q (List.mem_append_left _ hq)).1),
      hz Y (fun q hq => (h.1 q (List.mem_append_right _ hq)).1)]

theorem ae_not_mem_list (l : List ℝ) : ∀ᵐ t : ℝ, t ∉ l := by
  rw [ae_iff]
  have h0 := Set.Finite.measure_zero (List.finite_toSet l) (volume : Measure ℝ)
  have e : {a : ℝ | ¬ a ∉ l} = {x | x ∈ l} := Set.ext fun a => not_not
  rw [e]
  exact h0

/-- A successful refinement check gives a.e. equality of the densities. -/
theorem sameDens_of_refines {cuts : List ℚ} {X Y : List PieceQ} (h : RefinesOK cuts X Y) :
    ∀ᵐ t : ℝ, sdens X t = sdens Y t := by
  filter_upwards [ae_not_mem_list (cuts.map (fun c : ℚ => (c : ℝ)))] with t ht
  exact sdens_eq_of_not_cut h t ht

/-! ### 8. The merge theorem -/

/-- `Rm` has the same signed density as `R` on each species (`cT`, `cF`: the cuts of the check). -/
def MergeOK (cT cF : List ℚ) (R Rm : RefQ) : Prop :=
  RefinesOK cT (sgnT R) (sgnT Rm) ∧ RefinesOK cF (sgnF R) (sgnF Rm)

instance (cT cF : List ℚ) (R Rm : RefQ) : Decidable (MergeOK cT cF R Rm) := by
  unfold MergeOK
  infer_instance

theorem MergeOK.leL {cT cF : List ℚ} {R Rm : RefQ} (h : MergeOK cT cF R Rm) : R.LE := by
  obtain ⟨hT, hF⟩ := h
  refine ⟨fun q hq => hT.le_left q (List.mem_append_left _ hq),
    fun q hq => hF.le_left q (List.mem_append_left _ hq), ?_, ?_⟩
  · intro q hq
    exact hT.le_left (negQ q) (List.mem_append_right _ (List.mem_map.mpr ⟨q, hq, rfl⟩))
  · intro q hq
    exact hF.le_left (negQ q) (List.mem_append_right _ (List.mem_map.mpr ⟨q, hq, rfl⟩))

theorem MergeOK.leR {cT cF : List ℚ} {R Rm : RefQ} (h : MergeOK cT cF R Rm) : Rm.LE := by
  obtain ⟨hT, hF⟩ := h
  refine ⟨fun q hq => hT.le_right q (List.mem_append_left _ hq),
    fun q hq => hF.le_right q (List.mem_append_left _ hq), ?_, ?_⟩
  · intro q hq
    exact hT.le_right (negQ q) (List.mem_append_right _ (List.mem_map.mpr ⟨q, hq, rfl⟩))
  · intro q hq
    exact hF.le_right (negQ q) (List.mem_append_right _ (List.mem_map.mpr ⟨q, hq, rfl⟩))

theorem ent_congr (r : Bool) {X X' Y Y' : List PieceQ} (hX : ∀ q ∈ X, q.lo ≤ q.hi)
    (hX' : ∀ q ∈ X', q.lo ≤ q.hi) (hY : ∀ q ∈ Y, q.lo ≤ q.hi) (hY' : ∀ q ∈ Y', q.lo ≤ q.hi)
    (hx : ∀ᵐ t : ℝ, sdens X t = sdens X' t) (hy : ∀ᵐ t : ℝ, sdens Y t = sdens Y' t) :
    (entLF X Y r).eval = (entLF X' Y' r).eval := by
  rw [ent_eval Y r X hX, ent_eval Y' r X' hX']
  have hG : Gsum r Y = Gsum r Y' := funext (Gsum_congr_ae r hY hY' hy)
  rw [hG]
  exact Sfun_congr_ae hX hX' _ (fun a b => ii_Gsum r a b Y') hx

/-- **`refBil` depends only on the signed density.**  If `Rm` (resp. `Sm`) has the same signed
density as `R` (resp. `S`) on each species (decidable check `MergeOK`), the log forms of `refBil` agree. -/
theorem refBilLF_merge (R S Rm Sm : RefQ) {cT cF cT' cF' : List ℚ}
    (hm : MergeOK cT cF R Rm) (hn : MergeOK cT' cF' S Sm) :
    (refBilLF R S).eval = (refBilLF Rm Sm).eval := by
  rw [refBilLF_signed R S hm.leL hn.leL, refBilLF_signed Rm Sm hm.leR hn.leR]
  have dT := sameDens_of_refines hm.1
  have dF := sameDens_of_refines hm.2
  have dT' := sameDens_of_refines hn.1
  have dF' := sameDens_of_refines hn.2
  have c1 := ent_congr false hm.1.le_left hm.1.le_right hn.1.le_left hn.1.le_right dT dT'
  have c2 := ent_congr true hm.1.le_left hm.1.le_right hn.2.le_left hn.2.le_right dT dF'
  have c3 := ent_congr true hm.2.le_left hm.2.le_right hn.1.le_left hn.1.le_right dF dT'
  have c4 := ent_congr false hm.2.le_left hm.2.le_right hn.2.le_left hn.2.le_right dF dF'
  simp only [bil_eval]
  linarith

/-- `refBil_enc` with the pair jobs of the merged lists. -/
theorem refBil_enc_merged (μ ν : SRef) (R S Rm Sm : RefQ) {cT cF cT' cF' : List ℚ}
    (hμ : IsRefQ μ R) (hν : IsRefQ ν S) (hR : R.OK) (hS : S.OK)
    (hm : MergeOK cT cF R Rm) (hn : MergeOK cT' cF' S Sm)
    {lits : List LF} (hl : List.Forall₂ (fun (j : Job) (l : LF) => j.lf = l) (refPlan Rm Sm) lits)
    (n : ℕ) {p : ℚ × ℚ} (h : (LF.sumL lits).enc n = some p) : Enc (refBil μ ν) p := by
  have hv := LF.enc_spec n _ p h
  rw [← map_lf_eq hl, eval_refPlan, ← refBilLF_merge R S Rm Sm hm hn] at hv
  rwa [refBil_eval μ ν R S hμ hν hR hS]

/-- `refEnergy_enc` with the pair jobs of the merged list. -/
theorem refEnergy_enc_merged (μ : SRef) (R Rm : RefQ) {cT cF : List ℚ}
    (hμ : IsRefQ μ R) (hR : R.OK) (hm : MergeOK cT cF R Rm)
    {lits : List LF} (hl : List.Forall₂ (fun (j : Job) (l : LF) => j.lf = l) (refPlan Rm Rm) lits)
    (n : ℕ) {p : ℚ × ℚ} (h : (LF.sumL lits).enc n = some p) : Enc (refEnergy μ) p := by
  rw [refEnergy_eq_refBil]
  exact refBil_enc_merged μ μ R R Rm Rm hμ hμ hR hR hm hm hl n h

/-! ### 9. The plan of a merged reference (empty negative parts) -/

theorem jobsEnt_nil_inner (sg : ℚ) (r : Bool) : ∀ A : List PieceQ, jobsEnt sg r [] A = []
  | [] => rfl
  | qa :: A => by
    have ih := jobsEnt_nil_inner sg r A
    simp only [jobsEnt, jobsRow, List.nil_append, ih]

/-- For `Rm = ⟨mT, mF, [], []⟩`, `Sm = ⟨mT', mF', [], []⟩` only the `P P` jobs remain. -/
theorem refPlan_merged (a b c d : List PieceQ) :
    refPlan ⟨a, b, [], []⟩ ⟨c, d, [], []⟩ = jobsBil (-1) a b c d := by
  simp [refPlan, jobsBil, jobsEnt_nil_inner, jobsEnt]

/-! ### 10. Sanity example of the check (kernel-decidable) -/

example : RefinesOK [0, 1 / 2, 1]
    [⟨0, 1 / 2, [1, 1]⟩, ⟨1 / 2, 1, [1, 1]⟩, negQ ⟨0, 1 / 2, [1 / 2]⟩]
    [⟨0, 1 / 2, [1 / 2, 1]⟩, ⟨1 / 2, 1, [1, 1]⟩] := by
  decide +kernel

end

end CatalanMeasure.GenD.Signed.Data.Consts.EvalRef

#print axioms CatalanMeasure.GenD.Signed.Data.Consts.EvalRef.refBilLF_merge
#print axioms CatalanMeasure.GenD.Signed.Data.Consts.EvalRef.refBil_enc_merged
#print axioms CatalanMeasure.GenD.Signed.Data.Consts.EvalRef.refEnergy_enc_merged
#print axioms CatalanMeasure.GenD.Signed.Data.Consts.EvalRef.sameDens_of_refines
