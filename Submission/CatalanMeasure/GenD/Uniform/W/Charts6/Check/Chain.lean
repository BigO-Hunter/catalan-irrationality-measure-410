module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.Check.Affine
@[expose] public section
set_option Elab.async false

/-!
# Generic chain lemma over a list of widths (replaces `chain2 .. chain5`)

`offs ws i` is the sum of the first `i` widths.  If `Q (offs ws i + k)` holds for `k < ws[i]` for every `i`, then `Q j` holds for all `j < sum ws`.
-/
namespace CatalanMeasure.GenD.Uniform.W.Charts6.Check

def offs (ws : List ℕ) (i : ℕ) : ℕ := (ws.take i).sum

theorem offs_succ (ws : List ℕ) (i : ℕ) (h : i < ws.length) : offs ws (i + 1) = offs ws i + ws[i] := by
  unfold offs
  rw [List.take_succ, List.getElem?_eq_getElem h, List.sum_append]
  simp

theorem chain_list (Q : ℕ → Prop) (ws : List ℕ)
    (h : ∀ i (hi : i < ws.length), ∀ k < ws[i], Q (offs ws i + k)) : ∀ j < ws.sum, Q j := by
  intro j hj
  have key : ∀ n, n ≤ ws.length → ∀ j < offs ws n, Q j := by
    intro n
    induction n with
    | zero => intro _ j hj; simp [offs] at hj
    | succ n ih =>
      intro hn j hj
      have hn' : n < ws.length := hn
      rw [offs_succ ws n hn'] at hj
      by_cases hjn : j < offs ws n
      · exact ih (by omega) j hjn
      · have := h n hn' (j - offs ws n) (by omega)
        rwa [show offs ws n + (j - offs ws n) = j by omega] at this
  have := key ws.length le_rfl j (by simpa [offs] using hj)
  exact this

end CatalanMeasure.GenD.Uniform.W.Charts6.Check
