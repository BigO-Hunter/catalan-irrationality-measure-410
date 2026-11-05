module

public import Submission.CatalanMeasure.GenD.Signed.Data.S1.Nudge
public import Submission.CatalanMeasure.GenD.Signed.Data.S1.Cells
public import Submission.CatalanMeasure.GenD.Signed.Data.S1.Gap

@[expose] public section

/-!
# S1: assembly of the weight side from kappa-cells (lane D3)

Given a contiguous list of cells `[0, 1]` (each with a circle cover at `r1 > r0`, a certified
`CellStmt`), the combined bound

  `|common(tau_a)| |weight_k(tau_a)| binomBeta p m k <= 108000 N exp(w N)`,  `w > 58 Psi`,

holds for all splits `p + m = n`, eventually in `N` (`s1_hweights_gen`): exactly the hypothesis
`hweights` of `weighted_atom_point_of_sheet_binom` / `weighted_atom_point_binom_of_signed`.
-/

namespace CatalanMeasure.GenD.Signed.Data.S1
open CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric Filter Set

noncomputable section

/-- Contiguity of the cell list: starts at `x`, consecutive, ends at `1`. -/
def Contig : ℚ → List S1Cell → Bool
  | x, [] => decide (x = 1)
  | x, c :: cs => decide (c.lo = x ∧ c.lo ≤ c.hi) && Contig c.hi cs

theorem contig_cover : ∀ (cs : List S1Cell) (x : ℚ), Contig x cs = true → cs ≠ [] →
    ∀ κ : ℝ, (x : ℝ) ≤ κ → κ ≤ 1 → ∃ c ∈ cs, (c.lo : ℝ) ≤ κ ∧ κ ≤ c.hi := by
  intro cs
  induction cs with
  | nil => intro x _ h; exact absurd rfl h
  | cons c cs ih =>
    intro x h _ κ hxκ hκ1
    simp only [Contig, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hlo, hlh⟩, hrest⟩ := h
    by_cases hκ : κ ≤ c.hi
    · exact ⟨c, List.mem_cons_self, by rw [hlo]; exact hxκ, hκ⟩
    · push_neg at hκ
      cases cs with
      | nil =>
        simp only [Contig, decide_eq_true_eq] at hrest
        rw [hrest] at hκ
        push_cast at hκ
        linarith only [hκ, hκ1]
      | cons c' cs' =>
        obtain ⟨d, hd, h1, h2⟩ := ih c.hi hrest (by simp) κ hκ.le hκ1
        exact ⟨d, List.mem_cons_of_mem _ hd, h1, h2⟩

/-- The exponent per `n` selected by the cell containing `κ`. -/
def omegaC (g0 n0 : ℕ) (cells : List S1Cell) (κ : ℝ) : ℝ :=
  if h : ∃ c ∈ cells, (c.lo : ℝ) ≤ κ ∧ κ ≤ c.hi then
    keyholeRate g0 n0 ((Classical.choose h).r0 : ℝ) κ +
      max ((Classical.choose h).wc : ℝ) (416 / 100) / (n0 : ℝ)
  else 0

/-- The constant of one cell (`gap_hW_nudged` with `C = 3`, `C' = 1`). -/
def cellConst (n0 a : ℝ) (c : S1Cell) : ℝ :=
  4 * (1 + n0) * (2 * 3 * (4 * n0 / ((c.r1 : ℝ) - c.r0)) ^ 2 +
    512 * n0 ^ 4 * Real.exp (gapSegConst a) * 1)

theorem cellConst_nonneg {n0 : ℝ} (hn0 : 0 ≤ n0) (a : ℝ) (c : S1Cell) : 0 ≤ cellConst n0 a c := by
  unfold cellConst; positivity

theorem le_list_sum {α : Type*} (l : List α) (f : α → ℝ) (hf : ∀ x ∈ l, 0 ≤ f x) :
    ∀ x ∈ l, f x ≤ (l.map f).sum := by
  induction l with
  | nil => intro x hx; simp at hx
  | cons y l ih =>
    intro x hx
    simp only [List.map_cons, List.sum_cons]
    have hs : 0 ≤ (l.map f).sum :=
      List.sum_nonneg (fun z hz => by
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
        exact hf w (List.mem_cons_of_mem _ hw))
    rcases List.mem_cons.mp hx with rfl | hx'
    · linarith only [hs]
    · have := ih (fun z hz => hf z (List.mem_cons_of_mem _ hz)) x hx'
      have := hf y List.mem_cons_self
      linarith only [this, ih (fun z hz => hf z (List.mem_cons_of_mem _ hz)) x hx']

theorem eventually_forall_mem {α : Type*} (l : List α) (p : α → ℕ → Prop)
    (h : ∀ x ∈ l, ∀ᶠ N : ℕ in atTop, p x N) : ∀ᶠ N : ℕ in atTop, ∀ x ∈ l, p x N := by
  induction l with
  | nil => exact Filter.Eventually.of_forall (by simp)
  | cons y l ih =>
    have h1 := h y List.mem_cons_self
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    filter_upwards [h1, h2] with N hN1 hN2 x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hN1
    · exact hN2 x hx'

/-- **Weight side of S1.**  `P` has `n0 = 58`, `g0 = 5`, `h0 + q0 = 6`. -/
theorem s1_hweights_gen (P : Parameters) (hn : P.n0 = 58) (hg5 : P.g0 = 5)
    (hhq : P.h0 + P.q0 = 6) (cells : List S1Cell) (Ψ a w : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (ha4 : 1 - a ^ 2 ≤ 4 * a)
    (hcont : Contig 0 cells = true) (hne : cells ≠ [])
    (hrad : ∀ c ∈ cells, 0 < (c.r0 : ℝ) ∧ (c.r0 : ℝ) < c.r1 ∧ (c.r1 : ℝ) ≤ 1 ∧ a ≤ c.r0)
    (hcirc : ∀ c ∈ cells, GapCircleBound P a (c.r1 : ℝ) 3 (c.wc : ℝ))
    (hcell : ∀ c ∈ cells, CellStmt Ψ (c.r0 : ℝ) (c.wc : ℝ) (c.lo : ℝ) (c.hi : ℝ))
    (hw : 58 * Ψ < w) :
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ), p + m = P.n N →
      ∀ (k : ℕ), k < P.n N → ∀ (j : Fin ((P.n0 - P.g0) * N)),
      |(rowCommonFactor P N).eval (gapNodesD P a N j)| *
        |restrictedWeight P N k (gapNodesD P a N) j| *
        (CatalanMeasure.binomBeta p m k : ℝ) ≤ 108000 * (N : ℝ) * Real.exp (w * N) := by
  have hn0' : 0 < P.n0 := by omega
  have hg : P.g0 ≤ P.n0 := by omega
  have hnR : (P.n0 : ℝ) = 58 := by rw [hn]; norm_num
  have hn0R : (0 : ℝ) ≤ P.n0 := Nat.cast_nonneg _
  -- per-cell eventual bounds
  have hcellW : ∀ c ∈ cells, ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, k < P.n N → ∀ j : Fin ((P.n0 - P.g0) * N),
      |(rowCommonFactor P N).eval (gapNodesD P a N j)| *
        |restrictedWeight P N k (gapNodesD P a N) j| ≤
      cellConst (P.n0 : ℝ) a c * (N : ℝ) ^ 5 * Real.exp ((P.n N : ℝ) *
        (keyholeRate P.g0 P.n0 (c.r0 : ℝ) ((k : ℝ) / P.n N) +
          max (c.wc : ℝ) (416 / 100) / P.n0)) := by
    intro c hc
    obtain ⟨hr0, hr01, hr1, har⟩ := hrad c hc
    have hseg := gapSegBound_triv P ha0 ha1 har hhq
    have hfin := gap_hW_nudged P hg hn0' ha0 ha1 ha4 hr0 hr01 hr1 (by norm_num : (0 : ℝ) ≤ 3)
      (by norm_num : (0 : ℝ) ≤ 1) (hcirc c hc) hseg
    filter_upwards [hfin] with N hN k hk j
    exact hN k hk j
  have hall := eventually_forall_mem cells _ hcellW
  have hC0 : 0 ≤ (cells.map (cellConst (P.n0 : ℝ) a)).sum :=
    List.sum_nonneg (fun z hz => by
      obtain ⟨w', _, rfl⟩ := List.mem_map.mp hz
      exact cellConst_nonneg hn0R a w')
  have hW : ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, k < P.n N → ∀ j : Fin ((P.n0 - P.g0) * N),
      |(rowCommonFactor P N).eval (gapNodesD P a N j)| *
        |restrictedWeight P N k (gapNodesD P a N) j| ≤
      (cells.map (cellConst (P.n0 : ℝ) a)).sum * (N : ℝ) ^ 5 *
        Real.exp ((P.n N : ℝ) * omegaC P.g0 P.n0 cells ((k : ℝ) / P.n N)) := by
    filter_upwards [hall] with N hN k hk j
    have hnpos : (0 : ℝ) < P.n N := by
      have : 0 < P.n N := by
        have : 0 < N ∨ N = 0 := by omega
        rcases this with h | h
        · simp [Parameters.n]; omega
        · subst h; simp [Parameters.n] at hk
      exact_mod_cast this
    have hκ0 : (0 : ℝ) ≤ (k : ℝ) / P.n N := by positivity
    have hκ1 : (k : ℝ) / P.n N ≤ 1 := (div_le_one hnpos).mpr (by exact_mod_cast hk.le)
    have hex := contig_cover cells 0 hcont hne ((k : ℝ) / P.n N) (by simpa using hκ0) hκ1
    have hdef : omegaC P.g0 P.n0 cells ((k : ℝ) / P.n N) =
        keyholeRate P.g0 P.n0 ((Classical.choose hex).r0 : ℝ) ((k : ℝ) / P.n N) +
          max ((Classical.choose hex).wc : ℝ) (416 / 100) / P.n0 := by
      unfold omegaC; rw [dif_pos hex]
    rw [hdef]
    have hcm := (Classical.choose_spec hex).1
    have hb := hN _ hcm k hk j
    refine hb.trans ?_
    have hle := le_list_sum cells (cellConst (P.n0 : ℝ) a)
      (fun x _ => cellConst_nonneg hn0R a x) _ hcm
    have h5 : (0 : ℝ) ≤ (N : ℝ) ^ 5 * Real.exp ((P.n N : ℝ) *
        (keyholeRate P.g0 P.n0 ((Classical.choose hex).r0 : ℝ) ((k : ℝ) / P.n N) +
          max ((Classical.choose hex).wc : ℝ) (416 / 100) / P.n0)) := by positivity
    nlinarith only [mul_le_mul_of_nonneg_right hle h5]
  have hΨ : ∀ κ ∈ Icc (0 : ℝ) 1, omegaC P.g0 P.n0 cells κ + binomRate κ ≤ Ψ := by
    intro κ hκ
    have hex := contig_cover cells 0 hcont hne κ (by simpa using hκ.1) hκ.2
    have hdef : omegaC P.g0 P.n0 cells κ =
        keyholeRate P.g0 P.n0 ((Classical.choose hex).r0 : ℝ) κ +
          max ((Classical.choose hex).wc : ℝ) (416 / 100) / P.n0 := by
      unfold omegaC; rw [dif_pos hex]
    rw [hdef, hg5, hn]
    have hcm := (Classical.choose_spec hex).1
    have hr := (Classical.choose_spec hex).2
    have := hcell _ hcm κ ⟨hr.1, hr.2⟩
    have e58 : ((58 : ℕ) : ℝ) = 58 := by norm_num
    rw [e58]
    exact this
  have hwn : (P.n0 : ℝ) * Ψ < w := by rw [hnR]; exact hw
  exact binom_hweights_of_column_bound P (gapNodesD P a) (C₀ := (cells.map (cellConst (P.n0 : ℝ) a)).sum)
    (Ψ := Ψ) (w := w) 5 (omegaC P.g0 P.n0 cells) hC0 hW hΨ hwn

end

end CatalanMeasure.GenD.Signed.Data.S1
