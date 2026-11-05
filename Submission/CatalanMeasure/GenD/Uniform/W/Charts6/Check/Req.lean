module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.Check.Vec
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.Check.Cert
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Order requirements: computable tests and their soundness
-/
namespace CatalanMeasure.GenD.Uniform.W.Charts6.Check
open Polynomial Finset CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
open CatalanMeasure.GenD.Uniform.W.Prof (Packet emb chartMap Mx)

def pAff : Aff := ⟨0, 2, 1⟩

/-- Affine total width of the leading groups of `pt0` for the row `v` (computable). -/
def leadAff' (m : Meta) (pk : Packet) (pt0 : Pt) (v : List ℤ) : Aff :=
  ((lead pk m pt0 v).map fun g => m.ws.getD g ⟨0, 0, 0⟩).foldl Aff.add ⟨0, 0, 0⟩

theorem foldl_add_eval (L : List Aff) (init : Aff) (N hp : ℤ) :
    (L.foldl Aff.add init).eval N hp = init.eval N hp + (L.map fun f => f.eval N hp).sum := by
  induction L generalizing init with
  | nil => simp
  | cons f L ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, Aff.eval_add]; ring

/-- All widths are nonnegative on the window point. -/
def WdNonneg (m : Meta) (N hp : ℤ) : Prop := ∀ g < m.ws.length, 0 ≤ (m.ws.getD g ⟨0, 0, 0⟩).eval N hp

theorem sum_eval_list (m : Meta) (N p : ℕ) (hnn : WdNonneg m (N : ℤ) (((p : ℤ) - 1) / 2)) (L : List ℕ)
    (hL : ∀ g ∈ L, g < m.ws.length) :
    ((L.map fun g => m.ws.getD g ⟨0, 0, 0⟩).foldl Aff.add ⟨0, 0, 0⟩).eval (N : ℤ) (((p : ℤ) - 1) / 2) =
      (((L.map (wdOf m N p)).sum : ℕ) : ℤ) := by
  rw [foldl_add_eval]
  simp only [Aff.eval, zero_mul, add_zero]
  induction L with
  | nil => simp
  | cons g L ih =>
    have hg := hL g (List.mem_cons_self)
    have hnn' := hnn g hg
    have ih' := ih (fun g' hg' => hL g' (List.mem_cons_of_mem _ hg'))
    simp only [List.map_cons, List.sum_cons, Nat.cast_add] at ih' ⊢
    rw [← ih']
    unfold wdOf
    rw [Int.toNat_of_nonneg (by simpa [Aff.eval] using hnn')]
    simp [Aff.eval, List.map_map]

theorem leadAff'_eval (m : Meta) (pk : Packet) (N p : ℕ) (pt0 : Pt) (v : List ℤ)
    (hlen : m.pts.length = m.ws.length)
    (hnn : WdNonneg m (N : ℤ) (((p : ℤ) - 1) / 2)) :
    (leadAff' m pk pt0 v).eval (N : ℤ) (((p : ℤ) - 1) / 2) = (((lead pk m pt0 v).map (wdOf m N p)).sum : ℕ) := by
  apply sum_eval_list m N p hnn
  intro g hg
  have := (ptGroups_mem m pt0 g ((lead_prefix pk m pt0 v).subset hg)).1
  omega

def tOK (pk : Packet) (m : Meta) (win : List Aff) (cs : Cert) (pt0 : Pt) (ts : List (ℤ × ℕ)) (req : Aff) : Bool :=
  holds win cs ((leadAff' m pk pt0 (vecOf m pk.n ts)).sub req)

/-- The base offset `p - cm` of the `inf` chain. -/
def omAff (m : Meta) : Aff := pAff.sub m.cm

def iOK (pk : Packet) (m : Meta) (win : List Aff) (cs : Cert) (ts : List (ℤ × ℕ)) (lo : Aff) : Bool :=
  holds win cs (((leadAff' m pk Pt.inf (vecOf m pk.n ts)).add (omAff m)).sub (pAff.sub lo)) &&
    holds win cs (pAff.sub ((leadAff' m pk Pt.inf (vecOf m pk.n ts)).add (omAff m)))

noncomputable section
variable {p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

theorem rowPoly_degree {n : ℕ} (X : Fin p → Fin n → ZMod p) (v : List ℤ) : (rowPoly X v).degree < p := by
  unfold rowPoly
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro c _
  rw [Polynomial.C_mul']
  exact lt_of_le_of_lt (degree_smul_le _ _) (polx_degree X c)

theorem tOK_sound (pk : Packet) (m : Meta) (win : List Aff) (cs : Cert) {N : ℕ} (x : Fin p → Fin pk.d → Fp)
    (hker : JetKerG pk m N x) (hlen : m.pts.length = pk.charts.length) (hlen2 : m.pts.length = m.ws.length)
    (hnn : WdNonneg m (N : ℤ) (((p : ℤ) - 1) / 2)) (hwin : ∀ f ∈ win, 0 ≤ f.eval (N : ℤ) (((p : ℤ) - 1) / 2))
    (pt0 : Pt) (a : Fp) (hpt : pt0 = Pt.p1 ∧ a = 1 ∨ pt0 = Pt.m1 ∧ a = -1) (ts : List (ℤ × ℕ)) (req : Aff)
    (h : tOK pk m win cs pt0 ts req = true) :
    ∀ j : ℕ, (j : ℤ) < req.eval (N : ℤ) (((p : ℤ) - 1) / 2) →
      (taylor a (rowPoly (fun e => emb pk p pk.n (x e)) (vecOf m pk.n ts))).coeff j = 0 := by
  intro j hj
  have h1 := holds_sound win cs _ _ _ hwin h
  rw [Aff.eval_sub, leadAff'_eval m pk N p pt0 _ hlen2 hnn] at h1
  apply order_taylor pk m x hker hlen pt0 a hpt
  unfold leadWd
  omega

theorem iOK_sound (pk : Packet) (m : Meta) (win : List Aff) (cs : Cert) {N : ℕ} (x : Fin p → Fin pk.d → Fp)
    (hker : JetKerG pk m N x) (hlen : m.pts.length = pk.charts.length) (hlen2 : m.pts.length = m.ws.length)
    (hnn : WdNonneg m (N : ℤ) (((p : ℤ) - 1) / 2)) (hwin : ∀ f ∈ win, 0 ≤ f.eval (N : ℤ) (((p : ℤ) - 1) / 2))
    (hp2 : p % 2 = 1) (hz : ∀ e : Fin p, cmN m N p ≤ e.val → x e = 0)
    (hcm0 : 0 ≤ m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2)) (hcm1 : m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2) ≤ (p : ℤ))
    (ts : List (ℤ × ℕ)) (lo : Aff)
    (h : iOK pk m win cs ts lo = true) :
    ∀ i : ℕ, lo.eval (N : ℤ) (((p : ℤ) - 1) / 2) ≤ (i : ℤ) →
      (rowPoly (fun e => emb pk p pk.n (x e)) (vecOf m pk.n ts)).coeff i = 0 := by
  intro i hi
  simp only [iOK, Bool.and_eq_true] at h
  have h1 := holds_sound win cs _ _ _ hwin h.1
  have h2 := holds_sound win cs _ _ _ hwin h.2
  have hpe : pAff.eval (N : ℤ) (((p : ℤ) - 1) / 2) = (p : ℤ) := by simp only [pAff, Aff.eval]; omega
  have hom : (omAff m).eval (N : ℤ) (((p : ℤ) - 1) / 2) = (p : ℤ) - m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2) := by
    simp only [omAff, Aff.eval_sub, hpe]
  have hcmN : (cmN m N p : ℤ) = m.cm.eval (N : ℤ) (((p : ℤ) - 1) / 2) := by
    unfold cmN; exact Int.toNat_of_nonneg hcm0
  rw [Aff.eval_sub, Aff.eval_sub, Aff.eval_add, leadAff'_eval m pk N p Pt.inf _ hlen2 hnn, hom, hpe] at h1
  rw [Aff.eval_sub, Aff.eval_add, leadAff'_eval m pk N p Pt.inf _ hlen2 hnn, hom, hpe] at h2
  have hcm' : cmN m N p ≤ p := by omega
  have hord := order_inf pk m x hker hlen (vecOf m pk.n ts) hz hcm' (by unfold leadWd; omega)
  by_cases hip : i < p
  · have := hord (p - 1 - i) (by unfold leadWd; omega)
    rwa [show p - 1 - (p - 1 - i) = i by omega] at this
  · exact coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (rowPoly_degree _ _) (by exact_mod_cast not_lt.mp hip))

end
end CatalanMeasure.GenD.Uniform.W.Charts6.Check
