module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.L1Series

@[expose] public section

/-!
# Entries of the series window at `c` from a Laurent list (lane L1, 31 Oct 2026)

`l1EsOf nl ts` is the entry list of `l1_series_sound` for a raw Laurent list `ts`: equal factors merged
(`mergeL`), terms with an all-zero coefficient list dropped (`l1Prune`), and for every factor `log|αx - β|`
with `|α| ∉ {0, 1}` the rational `lam` of `log|α|` with its error from the kernel logarithm `logAbsQ nl`.
`l1_series_soundM` is `l1_series_sound` stated for the raw list `ts`.
-/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

/-- `log|α|` as `(lam, eta)`: exact `0` for `α ∈ {0, ±1}`, else the kernel logarithm -/
def l1Lg (nl : ℕ) (α : ℚ) : ℚ × ℚ :=
  if α = 0 ∨ α = 1 ∨ α = -1 then (0, 0) else (logAbsQ nl α).getD (0, 0)

def l1LgOk (nl : ℕ) (α : ℚ) : Bool :=
  decide (α = 0 ∨ α = 1 ∨ α = -1) || (logAbsQ nl α).isSome

theorem l1Lg_spec (nl : ℕ) (α : ℚ) (h : l1LgOk nl α = true) :
    |Real.log |(α : ℝ)| - ((l1Lg nl α).1 : ℝ)| ≤ ((l1Lg nl α).2 : ℝ) := by
  by_cases h0 : α = 0 ∨ α = 1 ∨ α = -1
  · have e : l1Lg nl α = (0, 0) := by rw [l1Lg, if_pos h0]
    rw [e]
    rcases h0 with rfl | rfl | rfl <;> simp
  · have hs : (logAbsQ nl α).isSome = true := by
      unfold l1LgOk at h
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h
      · exact absurd h h0
      · exact h
    obtain ⟨⟨v, e⟩, hv⟩ := Option.isSome_iff_exists.mp hs
    have e' : l1Lg nl α = (v, e) := by rw [l1Lg, if_neg h0, hv]; rfl
    rw [e']
    exact (logAbsQ_spec hv).2

def l1LgT (nl : ℕ) : Option (ℚ × ℚ) → ℚ × ℚ
  | none => (0, 0)
  | some (α, _) => l1Lg nl α

def l1Ent (nl : ℕ) (t : LTerm) : L1Ent := (t, l1LgT nl t.2)

def l1Ents (nl : ℕ) (ts : List LTerm) : List L1Ent := ts.map (l1Ent nl)

def l1LogsOk (nl : ℕ) (ts : List LTerm) : Bool :=
  ts.all (fun t => match t.2 with
    | none => true
    | some (α, _) => l1LgOk nl α)

theorem l1Ents_hlog (nl : ℕ) (ts : List LTerm) (h : l1LogsOk nl ts = true) :
    ∀ e ∈ l1Ents nl ts, ∀ (α β : ℚ), e.1.2 = some (α, β) →
      |Real.log |(α : ℝ)| - (e.2.1 : ℝ)| ≤ (e.2.2 : ℝ) := by
  intro e he α β hF
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
  have hc := List.all_eq_true.mp h t ht
  have hF' : t.2 = some (α, β) := hF
  have hc' : l1LgOk nl α = true := by
    rw [hF'] at hc
    exact hc
  have e1 : (l1Ent nl t).2 = l1Lg nl α := by
    unfold l1Ent
    simp only [hF', l1LgT]
  rw [e1]
  exact l1Lg_spec nl α hc'

theorem l1Ents_map (nl : ℕ) (ts : List LTerm) : (l1Ents nl ts).map Prod.fst = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [l1Ents, List.map_cons] at ih ⊢; rw [ih]; rfl

/-- drop the terms whose coefficient list is identically zero -/
def l1Prune (ts : List LTerm) : List LTerm :=
  ts.filter (fun t => !(t.1.all (fun q => decide (q = 0))))

theorem lfieldTower_l1Prune (x : ℝ) : ∀ ts : List LTerm,
    lfieldTower (l1Prune ts) 0 x = lfieldTower ts 0 x
  | [] => by simp [l1Prune]
  | t :: ts => by
      have ih := lfieldTower_l1Prune x ts
      by_cases hz : t.1.all (fun q => decide (q = 0)) = true
      · have h0 : polyTow t.1 0 x⁻¹ = 0 :=
          l0_zeros t.1 (fun q hq => of_decide_eq_true (List.all_eq_true.mp hz q hq)) _
        have e : l1Prune (t :: ts) = l1Prune ts := by simp [l1Prune, List.filter_cons, hz]
        rw [e, ih, lf_cons, h0]
        ring
      · have e : l1Prune (t :: ts) = t :: l1Prune ts := by simp [l1Prune, List.filter_cons, hz]
        rw [e, lf_cons, lf_cons, ih]

/-- the entries of the window for the raw Laurent list `ts` -/
def l1EsOf (nl : ℕ) (ts : List LTerm) : List L1Ent := l1Ents nl (l1Prune (mergeL ts))

/-- **Series window at `c` for a raw Laurent list** -/
theorem l1_series_soundM (fq fq' : FieldQ) (ts : List LTerm) (nl : ℕ) (c ρ : ℚ) (n : ℕ) (δ T : ℚ)
    (hlogs : l1LogsOk nl (l1Prune (mergeL ts)) = true)
    (h : l1OK c ρ (l1EsOf nl ts) = true)
    (hpl : fq'.plogs = fq.plogs ++ l1Plogs c n (l1EsOf nl ts)) (hpo : fq'.poles = fq.poles)
    (hD : polyAB (vecAdd (vecAdd fq.poly (l1Poly c n (l1EsOf nl ts)))
      (fq'.poly.map (fun t => (-1 : ℚ) * t))) c ρ ≤ δ)
    (S : Set ℝ) (hS : ∀ x ∈ S, (c : ℝ) - ρ ≤ x ∧ x ≤ (c : ℝ))
    (hcell : ∀ x ∈ S, fieldTower fq' (poleF fq'.poles) 0 x ≤ (T : ℝ)) :
    ∀ x ∈ S, fieldTower fq (poleF fq.poles) 0 x + lfieldTower ts 0 x ≤
      ((T + δ + l1Err c ρ n (l1EsOf nl ts) : ℚ) : ℝ) := by
  intro x hx
  have key := l1_series_sound fq fq' (l1EsOf nl ts) c ρ n δ T h (l1Ents_hlog nl _ hlogs) hpl hpo hD S hS hcell x hx
  have e : lfieldTower ((l1EsOf nl ts).map Prod.fst) 0 x = lfieldTower ts 0 x := by
    rw [l1EsOf, l1Ents_map, lfieldTower_l1Prune, lfieldTower_mergeL]
  rw [e] at key
  exact key

#print axioms l1_series_soundM

/-- `l1_series_soundM` with a pointwise bound `g` (end windows: `g x = TR + U + c log|x - e|`) -/
theorem l1_series_soundMG (fq fq' : FieldQ) (ts : List LTerm) (nl : ℕ) (c ρ : ℚ) (n : ℕ) (δ : ℚ) (g : ℝ → ℝ)
    (hlogs : l1LogsOk nl (l1Prune (mergeL ts)) = true)
    (h : l1OK c ρ (l1EsOf nl ts) = true)
    (hpl : fq'.plogs = fq.plogs ++ l1Plogs c n (l1EsOf nl ts)) (hpo : fq'.poles = fq.poles)
    (hD : polyAB (vecAdd (vecAdd fq.poly (l1Poly c n (l1EsOf nl ts)))
      (fq'.poly.map (fun t => (-1 : ℚ) * t))) c ρ ≤ δ)
    (S : Set ℝ) (hS : ∀ x ∈ S, (c : ℝ) - ρ ≤ x ∧ x ≤ (c : ℝ))
    (hcell : ∀ x ∈ S, fieldTower fq' (poleF fq'.poles) 0 x ≤ g x) :
    ∀ x ∈ S, fieldTower fq (poleF fq.poles) 0 x + lfieldTower ts 0 x ≤
      g x + ((δ + l1Err c ρ n (l1EsOf nl ts) : ℚ) : ℝ) := by
  intro x hx
  have key := l1_series_soundG fq fq' (l1EsOf nl ts) c ρ n δ g h (l1Ents_hlog nl _ hlogs) hpl hpo hD S hS hcell x hx
  have e : lfieldTower ((l1EsOf nl ts).map Prod.fst) 0 x = lfieldTower ts 0 x := by
    rw [l1EsOf, l1Ents_map, lfieldTower_l1Prune, lfieldTower_mergeL]
  rw [e] at key
  exact key

#print axioms l1_series_soundMG

end CatalanMeasure.GenD.Signed.Data.Cells
