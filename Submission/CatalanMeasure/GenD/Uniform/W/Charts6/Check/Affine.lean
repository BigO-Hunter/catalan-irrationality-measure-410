module
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Tactic.NormNum
@[expose] public section
set_option Elab.async false

/-!
# Affine forms in `(N, hp)` and a checkable Chvatal-Gomory derivation system

`Aff a b c` is `a*N + b*hp + c` (`p = 2*hp + 1`).  A `Deriv` list derives forms that are `≥ 0` on every integer point
satisfying the window constraints; `derivOK` is computable, `deriv_sound` is the soundness theorem.
-/
namespace CatalanMeasure.GenD.Uniform.W.Charts6.Check

structure Aff where
  a : ℤ
  b : ℤ
  c : ℤ
deriving DecidableEq, Repr

def Aff.eval (f : Aff) (N hp : ℤ) : ℤ := f.a * N + f.b * hp + f.c

inductive Step
  | hyp (i : ℕ)
  | add (i j : ℕ)
  | scale (k : ℕ) (i : ℕ)
  | tighten (d : ℕ) (i : ℕ)
  | const (k : ℕ)

/-- the form produced by a step, given the earlier derived forms and the hypotheses -/
def Step.apply (hyps : List Aff) (ds : List Aff) : Step → Option Aff
  | .hyp i => hyps[i]?
  | .add i j => do
      let f ← ds[i]?; let g ← ds[j]?
      pure ⟨f.a + g.a, f.b + g.b, f.c + g.c⟩
  | .scale k i => do
      let f ← ds[i]?
      pure ⟨k * f.a, k * f.b, k * f.c⟩
  | .tighten d i => do
      let f ← ds[i]?
      if 0 < d ∧ (d : ℤ) ∣ f.a ∧ (d : ℤ) ∣ f.b then
        pure ⟨f.a / d, f.b / d, f.c / d⟩
      else none
  | .const k => some ⟨0, 0, k⟩

/-- Process steps in order. -/
def deriveAll (hyps : List Aff) (steps : List Step) : Option (List Aff) :=
  steps.foldlM (fun ds s => do let f ← s.apply hyps ds; pure (ds ++ [f])) []

/-- `goal ≥ 0` is certified: some derived form has the same variable part and a smaller constant. -/
def certOK (hyps : List Aff) (steps : List Step) (goal : Aff) : Bool :=
  match deriveAll hyps steps with
  | none => false
  | some ds => ds.any fun d => d.a == goal.a && d.b == goal.b && decide (d.c ≤ goal.c)

theorem step_sound (hyps : List Aff) (N hp : ℤ) (hh : ∀ f ∈ hyps, 0 ≤ f.eval N hp)
    (ds : List Aff) (hd : ∀ f ∈ ds, 0 ≤ f.eval N hp) (s : Step) (f : Aff)
    (hs : s.apply hyps ds = some f) : 0 ≤ f.eval N hp := by
  cases s with
  | hyp i => simp [Step.apply] at hs; exact hh f (List.mem_of_getElem? hs)
  | add i j =>
    simp only [Step.apply, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hs
    obtain ⟨f1, h1, f2, h2, rfl⟩ := hs
    have := hd f1 (List.mem_of_getElem? h1); have := hd f2 (List.mem_of_getElem? h2)
    simp only [Aff.eval] at *; linarith
  | scale k i =>
    simp only [Step.apply, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hs
    obtain ⟨f1, h1, rfl⟩ := hs
    have := hd f1 (List.mem_of_getElem? h1)
    simp only [Aff.eval] at *
    have hk : (0:ℤ) ≤ k := by positivity
    nlinarith
  | tighten d i =>
    simp only [Step.apply, bind, Option.bind_eq_some_iff, pure] at hs
    obtain ⟨f1, h1, hs⟩ := hs
    split_ifs at hs with hc
    · obtain rfl := Option.some.inj hs
      have h0 := hd f1 (List.mem_of_getElem? h1)
      obtain ⟨hd0, ⟨x, hx⟩, ⟨y, hy⟩⟩ := hc
      simp only [Aff.eval] at *
      have hdpos : (0:ℤ) < d := by exact_mod_cast hd0
      rw [hx, hy] at h0 ⊢
      rw [Int.mul_ediv_cancel_left _ hdpos.ne', Int.mul_ediv_cancel_left _ hdpos.ne']
      have : 0 ≤ (d:ℤ) * (x * N + y * hp) + f1.c := by nlinarith
      have h2 : -f1.c ≤ (d:ℤ) * (x * N + y * hp) := by linarith
      have h3 : -(f1.c / d) ≤ x * N + y * hp := by
        by_contra hlt; push_neg at hlt
        have h4 : x * N + y * hp ≤ -(f1.c / d) - 1 := by linarith
        have h5 := Int.emod_add_mul_ediv f1.c d
        have h6 := Int.emod_lt_of_pos f1.c hdpos
        have h7 := Int.emod_nonneg f1.c hdpos.ne'
        nlinarith
      linarith
  | const k =>
    simp [Step.apply] at hs; subst hs; simp [Aff.eval]

theorem cert_sound (hyps : List Aff) (steps : List Step) (goal : Aff) (N hp : ℤ)
    (hh : ∀ f ∈ hyps, 0 ≤ f.eval N hp) (h : certOK hyps steps goal = true) : 0 ≤ goal.eval N hp := by
  unfold certOK at h
  generalize hd : deriveAll hyps steps = r at h
  cases r with
  | none => simp at h
  | some ds =>
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
    obtain ⟨d, hdm, ha, hb, hc⟩ := h
    have key : ∀ (ss : List Step) (acc : List Aff), (∀ f ∈ acc, 0 ≤ f.eval N hp) →
        ∀ r, ss.foldlM (fun ds s => do let f ← s.apply hyps ds; pure (ds ++ [f])) acc = some r →
          ∀ f ∈ r, 0 ≤ f.eval N hp := by
      intro ss
      induction ss with
      | nil => intro acc hacc r hr; simp at hr; subst hr; exact hacc
      | cons s ss ih =>
        intro acc hacc r hr
        simp only [List.foldlM, bind, Option.bind_eq_some_iff, pure] at hr
        obtain ⟨a, ⟨f, hf, ha⟩, hr⟩ := hr
        have ha' := Option.some.inj ha
        subst ha'
        refine ih _ ?_ r hr
        intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hacc g hg
        · simp at hg; subst hg; exact step_sound hyps N hp hh acc hacc s _ hf
    have := key steps [] (by simp) ds hd d hdm
    simp only [Aff.eval] at *
    rw [← ha, ← hb]; linarith
end CatalanMeasure.GenD.Uniform.W.Charts6.Check
