module

public import Submission.CatalanMeasure.GenD.Uniform.Bank532.Table

@[expose] public section
set_option Elab.async false

/-!
# Merge utilities (lane G10; see evidence/claude/G10/PAPER.md section 2)

* `Chain`: consecutive windows are ordered, `chain_pairwise` gives `Pairwise (b <= a)`.
* `old_cert`: a sub-window (shrink) of a window of `W13 = wins13` is certified against `fams13`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank532
open CatalanMeasure.GenD D58 Filter CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.LedgerW CatalanMeasure.GenD.Uniform.Arithmetic
open CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger3
  CatalanMeasure.GenD.Uniform.Bank540.Ledger4 CatalanMeasure.GenD.Uniform.Bank535.Ledger10
noncomputable section

/-- Consecutive windows are ordered. -/
def Chain : List KapWindow → Prop
  | [] => True
  | [_] => True
  | s :: t :: r => s.b ≤ t.a ∧ Chain (t :: r)

theorem chain_head_le {s : KapWindow} {r : List KapWindow} (hab : ∀ w ∈ s :: r, w.a ≤ w.b)
    (hc : Chain (s :: r)) : ∀ y ∈ r, s.b ≤ y.a := by
  induction r generalizing s with
  | nil => intro y hy; simp at hy
  | cons t r ih =>
    intro y hy
    obtain ⟨h1, h2⟩ := hc
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h1
    · have := ih (s := t) (fun w hw => hab w (List.mem_cons_of_mem _ hw)) h2 y hy
      have ht := hab t (by simp)
      linarith

theorem chain_pairwise : ∀ ws : List KapWindow, (∀ w ∈ ws, w.a ≤ w.b) → Chain ws →
    ws.Pairwise (fun s t => s.b ≤ t.a)
  | [], _, _ => List.Pairwise.nil
  | s :: r, hab, hc => by
    refine List.Pairwise.cons (chain_head_le hab hc) (chain_pairwise r (fun w hw => hab w (List.mem_cons_of_mem _ hw)) ?_)
    cases r with
    | nil => trivial
    | cons t r => exact hc.2

theorem old_cert {k : ℕ} {a b c0 c1 a' b' : ℝ} (h : W13[k]? = some (cw a b c0 c1))
    (ha : a ≤ a') (hb : b' ≤ b) : ∃ lb ∈ fams13, WinCert lb (cw a' b' c0 c1) := by
  obtain ⟨lb, hl, hc⟩ := W13_cert (cw a b c0 c1) (List.mem_of_getElem? h)
  exact ⟨lb, hl, WinCert.shrink hc ha hb⟩

end
end CatalanMeasure.GenD.Uniform.Bank532
#print axioms CatalanMeasure.GenD.Uniform.Bank532.chain_pairwise
#print axioms CatalanMeasure.GenD.Uniform.Bank532.old_cert
