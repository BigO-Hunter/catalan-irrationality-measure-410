module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.Check.Req
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.DomHigh
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.DomVLow
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Hdom146
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Generic `hdom`: the jet kernel lies in the image of `Theta`
-/
namespace CatalanMeasure.GenD.Uniform.W.Charts6.Check
open Polynomial Finset Module CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W.Prof (Packet emb chartMap Mx)

noncomputable section
variable {p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

/-- Insertion of the packet coordinates into the `K` profile coordinates. -/
def insM (m : Meta) (n K : ℕ) : (Fin n → Fp) →ₗ[Fp] (Fin K → Fp) :=
  LinearMap.pi fun idx => match pcOf m idx.val with
    | some c => if h : c < n then LinearMap.proj ⟨c, h⟩ else 0
    | none => 0

theorem polx_insM (m : Meta) {n K : ℕ} (X : Fin p → Fin n → Fp) (idx : Fin K) :
    polx (fun e => insM m n K (X e)) idx = polAt X (pcOf m idx.val) := by
  unfold polx polAt
  rcases h : pcOf m idx.val with _ | c
  · simp [insM, h]
  · by_cases hc : c < n
    · simp [insM, h, hc]; rfl
    · simp [insM, h, hc]

/-- The atoms of the jet kernel, in profile coordinates, graph coordinates forgotten. -/
def X' (m : Meta) (pk : Packet) {b ex K : ℕ} (hK : K = b * 4 + 2 + ex) (x : Fin p → Fin pk.d → Fp) :
    Fin p → Fin K → Fp :=
  fun e => projExtras hK (insM m pk.n K (emb pk p pk.n (x e)))

theorem polxX'_blk (m : Meta) (pk : Packet) {b ex K : ℕ} (hK : K = b * 4 + 2 + ex) (x : Fin p → Fin pk.d → Fp)
    (k : Fin b) (u : Fin 4) :
    polx (X' m pk hK x) ((ckEquiv hK).symm (Sum.inl (k, u))) =
      polAt (fun e => emb pk p pk.n (x e)) (pcOf m (4 * k.val + u.val)) := by
  unfold X'
  rw [Pilot146O.polx_proj _ _ _ (Pilot146O.not_extra_inl _ k u), polx_insM,
    Pilot146O.ck_inl_val]

theorem polxX'_Z (m : Meta) (pk : Packet) {b ex K : ℕ} (hK : K = b * 4 + 2 + ex) (x : Fin p → Fin pk.d → Fp)
    (z : Fin 2) :
    polx (X' m pk hK x) ((ckEquiv hK).symm (Sum.inr (Sum.inl z))) =
      polAt (fun e => emb pk p pk.n (x e)) (pcOf m (b * 4 + z.val)) := by
  unfold X'
  rw [Pilot146O.polx_proj _ _ _ (Pilot146O.not_extra_Z _ z), polx_insM, Pilot146O.ck_Z_val]

theorem rowPoly_single (m : Meta) {n : ℕ} (X : Fin p → Fin n → Fp) (idx : ℕ) :
    rowPoly X (vecOf m n [(1, idx)]) = polAt X (pcOf m idx) := by
  rw [rowPoly_vecOf]; simp

theorem rowPoly_diff (m : Meta) {n : ℕ} (X : Fin p → Fin n → Fp) (i j : ℕ) :
    rowPoly X (vecOf m n [(1, i), (-2, j)]) = polAt X (pcOf m i) - 2 * polAt X (pcOf m j) := by
  rw [rowPoly_vecOf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.cast_one, Int.cast_neg, Int.cast_ofNat,
    map_one, one_mul, add_zero]
  have : (C (-(2 : Fp)) : Fp[X]) = -2 := by rw [map_neg, map_ofNat]
  rw [this]; ring

theorem rowPoly_virt3 (m : Meta) {n : ℕ} (X : Fin p → Fin n → Fp) (i j k : ℕ) :
    rowPoly X (vecOf m n [(1, i), (-1, j), (1, k)]) = polAt X (pcOf m i) - polAt X (pcOf m j) + polAt X (pcOf m k) := by
  rw [rowPoly_vecOf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.cast_one, Int.cast_neg,
    map_one, one_mul, add_zero]
  have : (C (-(1 : Fp)) : Fp[X]) = -1 := by simp
  rw [this]; ring

theorem rowPoly_virt2 (m : Meta) {n : ℕ} (X : Fin p → Fin n → Fp) (i j : ℕ) :
    rowPoly X (vecOf m n [(1, i), (1, j)]) = polAt X (pcOf m i) + polAt X (pcOf m j) := by
  rw [rowPoly_vecOf]; simp

end
end CatalanMeasure.GenD.Uniform.W.Charts6.Check
