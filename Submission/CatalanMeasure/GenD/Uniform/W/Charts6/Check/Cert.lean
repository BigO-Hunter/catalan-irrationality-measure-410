module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.Check.Affine
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
@[expose] public section
set_option Elab.async false

/-!
# Certified inequalities on the window

`holds win cs goal` is a computable test: some certificate of `cs` derives a form dominating `goal` from the window hypotheses.
-/
namespace CatalanMeasure.GenD.Uniform.W.Charts6.Check

def Aff.add (f g : Aff) : Aff := ⟨f.a + g.a, f.b + g.b, f.c + g.c⟩
def Aff.sub (f g : Aff) : Aff := ⟨f.a - g.a, f.b - g.b, f.c - g.c⟩
def Aff.scl (k : ℤ) (f : Aff) : Aff := ⟨k * f.a, k * f.b, k * f.c⟩

theorem Aff.eval_add (f g : Aff) (N hp : ℤ) : (f.add g).eval N hp = f.eval N hp + g.eval N hp := by
  simp only [Aff.add, Aff.eval]; ring
theorem Aff.eval_sub (f g : Aff) (N hp : ℤ) : (f.sub g).eval N hp = f.eval N hp - g.eval N hp := by
  simp only [Aff.sub, Aff.eval]; ring
theorem Aff.eval_scl (k : ℤ) (f : Aff) (N hp : ℤ) : (f.scl k).eval N hp = k * f.eval N hp := by
  simp only [Aff.scl, Aff.eval]; ring

abbrev Cert := List (Aff × List Step)

def holds (win : List Aff) (cs : Cert) (goal : Aff) : Bool :=
  cs.any fun gs => decide (gs.1.a = goal.a ∧ gs.1.b = goal.b ∧ gs.1.c ≤ goal.c) && certOK win gs.2 gs.1

theorem holds_sound (win : List Aff) (cs : Cert) (goal : Aff) (N hp : ℤ)
    (hw : ∀ f ∈ win, 0 ≤ f.eval N hp) (h : holds win cs goal = true) : 0 ≤ goal.eval N hp := by
  simp only [holds, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨g, st⟩, _, ⟨ha, hb, hc⟩, hcert⟩ := h
  have := cert_sound win st g N hp hw hcert
  simp only [Aff.eval] at *
  rw [← ha, ← hb]; linarith

/-- Window hypotheses `N ≥ N0`, `a N < b p`, `c p ≤ d N` with `p = 2 hp + 1`. -/
def winHyps (N0 a b c d : ℕ) : List Aff :=
  [⟨1, 0, -(N0 : ℤ)⟩, ⟨-(a : ℤ), 2 * b, (b : ℤ) - 1⟩, ⟨d, -2 * (c : ℤ), -(c : ℤ)⟩]

theorem winHyps_sound (N0 a b c d N p : ℕ) (hN : N0 ≤ N) (h1 : a * N < b * p) (h2 : c * p ≤ d * N)
    (hodd : p % 2 = 1) : ∀ f ∈ winHyps N0 a b c d, 0 ≤ f.eval (N : ℤ) (((p : ℤ) - 1) / 2) := by
  have hp : (p : ℤ) = 2 * (((p : ℤ) - 1) / 2) + 1 := by omega
  set hp' : ℤ := ((p : ℤ) - 1) / 2 with hhp
  have e1 : ((a : ℤ)) * N < (b : ℤ) * p := by exact_mod_cast h1
  have e2 : ((c : ℤ)) * p ≤ (d : ℤ) * N := by exact_mod_cast h2
  have e3 : (N0 : ℤ) ≤ N := by exact_mod_cast hN
  intro f hf
  simp only [winHyps, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl <;> simp only [Aff.eval]
  · linarith
  · rw [hp] at e1; nlinarith
  · rw [hp] at e2; nlinarith

end CatalanMeasure.GenD.Uniform.W.Charts6.Check
