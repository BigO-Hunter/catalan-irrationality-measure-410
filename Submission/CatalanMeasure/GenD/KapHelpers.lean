module

public import Submission.CatalanMeasure.GenD.Interface
public import Submission.CatalanMeasure.GenD.PrimeGrowth

@[expose] public section

/-!
# Helpers for instantiating `kap` from a window list (module 4, instance support)

* `tVal_le_famKap`, ... : each family value is below `famKap` inside its window;
* `floor_aux`: `⌊N (c0 + c1 p/N)⌋₊ ≤ v + 1` from the cleared linear inequality
  `A N + B p < d (v + 2)` (so the instance reduces each window to an `omega` problem);
* `segExp_le`: `segExp l N p ≤ m` window by window.
-/

namespace CatalanMeasure.GenD

open PrimeGrowth CatalanMeasure.Parametric

noncomputable section

theorem tVal_le_famKap {P : Parameters} {N p : ℕ} (h : TApp P N p) : tVal P N p ≤ famKap P N p := by
  classical
  unfold famKap
  refine le_max_of_le_left (le_max_of_le_left ?_)
  rw [if_pos h]

theorem uVal_le_famKap {P : Parameters} {N p : ℕ} (h : UApp P N p) : uVal P N p ≤ famKap P N p := by
  classical
  unfold famKap
  refine le_max_of_le_left (le_max_of_le_right ?_)
  rw [if_pos h]

theorem sVal_le_famKap {P : Parameters} {N p : ℕ} (h : SApp P N p) : sVal P N p ≤ famKap P N p := by
  classical
  unfold famKap
  refine le_max_of_le_right (le_max_of_le_left ?_)
  rw [if_pos h]

theorem u6Val_le_famKap {P : Parameters} {N p : ℕ} (h : U6App P N p) :
    u6Val P N p ≤ famKap P N p := by
  classical
  unfold famKap
  refine le_max_of_le_right (le_max_of_le_right ?_)
  rw [if_pos h]

/-- Floor of an affine window profile from a cleared linear inequality. -/
theorem floor_aux {N p v d : ℕ} {A B : ℤ} (hN : 0 < N) (hd : 0 < d)
    (h : A * (N : ℤ) + B * (p : ℤ) < (d : ℤ) * ((v : ℤ) + 2)) {c0 c1 : ℝ}
    (hc0 : c0 * d = A) (hc1 : c1 * d = B) :
    ⌊(N : ℝ) * (c0 + c1 * ((p : ℝ) / N))⌋₊ ≤ v + 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hr : (N : ℝ) * (c0 + c1 * ((p : ℝ) / N)) = c0 * N + c1 * p := by
    field_simp
  have hh : (A : ℝ) * N + B * p < (d : ℝ) * ((v : ℝ) + 2) := by exact_mod_cast h
  have h2 : (c0 * N + c1 * p) * d < d * ((v : ℝ) + 2) := by
    have : (c0 * N + c1 * p) * d = (A : ℝ) * N + B * p := by
      rw [← hc0, ← hc1]; ring
    rw [this]; exact hh
  have h3 : c0 * N + c1 * p < (v : ℝ) + 2 := by
    have := h2; nlinarith
  rw [hr]
  have h4 : ⌊c0 * N + c1 * p⌋₊ < v + 2 := by
    rw [Nat.floor_lt' (by omega)]
    exact_mod_cast h3
  omega

theorem foldr_max_le {α : Type*} (f : α → ℕ) (l : List α) {m : ℕ}
    (h : ∀ x ∈ l, f x ≤ m) : (l.map f).foldr max 0 ≤ m := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le (h t (List.mem_cons_self)) (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem segExp_le {l : List Seg} {N p m : ℕ}
    (h : ∀ s ∈ l, (s.a * (N : ℝ) < p ∧ (p : ℝ) ≤ s.b * N) →
      ⌊(N : ℝ) * s.F ((p : ℝ) / N)⌋₊ ≤ m) : segExp l N p ≤ m := by
  unfold segExp
  apply foldr_max_le
  intro s hs
  by_cases hc : s.a * (N : ℝ) < p ∧ (p : ℝ) ≤ s.b * N
  · rw [if_pos hc]
    exact h s hs hc
  · rw [if_neg hc]
    exact Nat.zero_le _

theorem prof_eval_nil (c0 c1 x : ℝ) : (PL.Prof.mk c0 c1 []).eval x = c0 + c1 * x := by
  simp [PL.Prof.eval]

end

end CatalanMeasure.GenD
