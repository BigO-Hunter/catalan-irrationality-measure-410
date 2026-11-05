module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts3.Host
@[expose] public section
set_option Elab.async false

/-!
# The old identification is a special case of the host

`Ident` (W/Prof) gives a `HostIdent` with `m = S.D`, the product atom map `xi` and the coefficient jets
of the slot polynomials; its `dom` hypothesis (asked for ALL atoms) is stronger than the host's
(asked on the jet kernel only), which is exactly the room the four-point frame needs.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts3
open Finset Module CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Prof
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- `Ident` (with `q < p`, so `a = 0`) is a `HostIdent`. -/
def Ident.toHost {S : SlotSystem P N p} {pk : Packet} {width : Fin pk.charts.length → ℕ}
    (I : Ident S pk width) (hS : pk.Sound) (hpD : ¬ (p : ℤ) ∣ pk.D) :
    HostIdent S pk S.D width 0 (P.q N) where
  jet := fun g k => I.jet S g k
  xi := I.xi S
  dom := fun x _ => I.dom x
  inj := fun x _ h => by
    have hemb : Function.Injective (emb pk p S.K) := emb_injective hS I.hK (not_dvd_delta hpD)
    funext d'
    exact hemb (by simpa [Ident.xi] using congrFun h d')
  kill := fun x hx => by
    refine ⟨0, by simp, fun j h1 h2 => ?_⟩
    have hx2 : ∀ g k, chartMap pk (pk.chart g) p S.K (I.jet S g k x) = 0 := by
      rw [I.hK]; exact hx
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_zero, pow_zero,
      Nat.choose_self, Nat.cast_one, mul_one, one_mul, add_zero, Polynomial.eval_zero]
    exact I.resp_zero S x hx2 j h1 (by simpa using h2)

end
end CatalanMeasure.GenD.Uniform.W.Charts3
