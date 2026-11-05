module
public import Submission.CatalanMeasure.GenD.Uniform.W.Prof.Packet
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
@[expose] public section
set_option Elab.async false

/-!
# Lemma C modulo `p`

For a checked packet and a prime `p ∤ pk.D`:

* `emb` : the `V`-coordinate embedding `(Fin d → F_p) → (Fin n → F_p)`, `c ↦ Σ_a c_a v_a`, is
  injective (`emb_injective`): `dim V_p = d`;
* for each chart, the chart matrix `B_j` reduced mod `p` and composed with `emb` has rank at
  most `r_j` (`finrank_chartMap_le`).

Both follow from integer identities only (`Packet.Sound`): independence of rows of an integer
matrix modulo `p` from an adjugate certificate `W · P(rows)ᵀ = δ I` with `p ∤ δ` (`indep_zmod`).
-/

namespace CatalanMeasure.GenD.Uniform.W.Prof
open Finset Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- Adjugate certificate gives independence of the (mod `p`) rows. -/
theorem indep_zmod {d : ℕ} (Wm Vm : ℕ → ℕ → ℤ) (δ : ℤ)
    (hind : ∀ a b, a < d → b < d → ∑ i ∈ range d, Wm a i * Vm b i = if a = b then δ else 0)
    (hδ : ((δ : ℤ) : ZMod p) ≠ 0) (c : Fin d → ZMod p)
    (hc : ∀ i, i < d → ∑ b : Fin d, c b * (Vm b i : ZMod p) = 0) : c = 0 := by
  funext a
  have h1 : ∑ i ∈ range d, (Wm a i : ZMod p) * ∑ b : Fin d, c b * (Vm b i : ZMod p) = 0 :=
    Finset.sum_eq_zero fun i hi => by rw [hc i (Finset.mem_range.mp hi), mul_zero]
  have h2 : ∑ i ∈ range d, (Wm a i : ZMod p) * ∑ b : Fin d, c b * (Vm b i : ZMod p) =
      ∑ b : Fin d, c b * ((∑ i ∈ range d, Wm a i * Vm b i : ℤ) : ZMod p) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h2] at h1
  have h3 : ∑ b : Fin d, c b * ((∑ i ∈ range d, Wm a i * Vm b i : ℤ) : ZMod p) =
      c a * (δ : ZMod p) := by
    rw [Finset.sum_eq_single a]
    · rw [hind a a a.2 a.2]; simp
    · intro b _ hb
      have : (a : ℕ) ≠ b := fun h => hb (Fin.ext h.symm)
      rw [hind a b a.2 b.2, ite_eq_right_iff.mpr (fun h => absurd h this)]; simp
    · simp
  rw [h3] at h1
  have h4 : c a = 0 := (mul_eq_zero.mp h1).resolve_right hδ
  simpa using h4

/-- The coordinate embedding `c ↦ Σ_a c_a v_a` (mod `p`). -/
def embMat (pk : Packet) (p : ℕ) [Fact p.Prime] (K : ℕ) : Matrix (Fin pk.d) (Fin K) (ZMod p) :=
  fun a k => ((Mx pk.v a k : ℤ) : ZMod p)

def emb (pk : Packet) (p : ℕ) [Fact p.Prime] (K : ℕ) :
    (Fin pk.d → ZMod p) →ₗ[ZMod p] (Fin K → ZMod p) :=
  Matrix.vecMulLinear (embMat pk p K)

theorem emb_apply (pk : Packet) (K : ℕ) (c : Fin pk.d → ZMod p) (k : Fin K) :
    emb pk p K c k = ∑ a : Fin pk.d, c a * ((Mx pk.v a k : ℤ) : ZMod p) := by
  simp [emb, embMat, Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct]

/-- `dim V_p = d`: the embedding is injective for `p ∤ δ`. -/
theorem emb_injective {pk : Packet} (hS : pk.Sound) {K : ℕ} (hK : K = pk.n)
    (hp : ¬ (p : ℤ) ∣ pk.delta) : Function.Injective (emb pk p K) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  refine indep_zmod (p := p) (fun a i => Mx pk.adj a i)
    (fun b i => Mx pk.v b (pk.piv.getD i 0)) pk.delta (fun a b ha hb => hS.vind a b ha hb)
    (by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]) c fun i hi => ?_
  have := congrFun hc ⟨pk.piv.getD i 0, by have := hS.pivlt i hi; omega⟩
  rw [emb_apply] at this
  simpa using this

/-- The chart matrix mod `p`. -/
def chartMat (ch : Chart) (p : ℕ) [Fact p.Prime] (K : ℕ) :
    Matrix (Fin ch.rows.length) (Fin K) (ZMod p) :=
  fun r k => ((Mx ch.rows r k : ℤ) : ZMod p)

/-- The chart map `B_j` mod `p` on profile coordinates. -/
def chartLin (ch : Chart) (p : ℕ) [Fact p.Prime] (K : ℕ) :
    (Fin K → ZMod p) →ₗ[ZMod p] (Fin ch.rows.length → ZMod p) :=
  Matrix.mulVecLin (chartMat ch p K)

/-- The chart map in `V`-coordinates. -/
def chartMap (pk : Packet) (ch : Chart) (p : ℕ) [Fact p.Prime] (K : ℕ) :
    (Fin pk.d → ZMod p) →ₗ[ZMod p] (Fin ch.rows.length → ZMod p) :=
  (chartLin ch p K).comp (emb pk p K)

/-- **Lemma C (rank part).**  The restriction of the chart to `V_p` has rank at most `r_j`,
for `p` not dividing the chart's kernel-independence integer. -/
theorem finrank_chartMap_le {pk : Packet} {ch : Chart} (hS : pk.Sound) (hc : ch.Sound pk.n pk.d pk.v)
    {K : ℕ} (hK : K = pk.n) (hq : ¬ (p : ℤ) ∣ ch.qdelta) :
    finrank (ZMod p) (LinearMap.range (chartMap pk ch p K)) ≤ ch.r := by
  set κ := ch.ker.length with hκ
  let kv : Fin κ → (Fin pk.d → ZMod p) := fun i a => ((Mx ch.ker i a : ℤ) : ZMod p)
  have hli : LinearIndependent (ZMod p) kv := by
    rw [Fintype.linearIndependent_iff]
    intro c hc0
    have := indep_zmod (p := p) (fun a i => Mx ch.qadj a i)
      (fun b i => Mx ch.ker b (ch.qpiv.getD i 0)) ch.qdelta
      (fun a b ha hb => hc.qind a b ha hb)
      (by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]) c fun i hi => by
        have := congrFun hc0 ⟨ch.qpiv.getD i 0, hc.qlt i hi⟩
        simpa [kv, Finset.sum_apply] using this
    intro i; exact congrFun this i
  have hker : ∀ i, chartMap pk ch p K (kv i) = 0 := by
    intro i
    funext r
    simp only [chartMap, LinearMap.comp_apply, chartLin, Matrix.mulVecLin_apply, Matrix.mulVec,
      dotProduct, Pi.zero_apply]
    have := hc.kill i r i.2 r.2
    have hz : (((∑ x ∈ range pk.n, Mx ch.rows r x *
        (∑ a ∈ range pk.d, Mx ch.ker i a * Mx pk.v a x) : ℤ)) : ZMod p) = 0 := by
      rw [this]; simp
    push_cast at hz
    subst hK
    rw [← Fin.sum_univ_eq_sum_range (fun x => (Mx ch.rows r x : ZMod p) *
      ∑ a ∈ range pk.d, (Mx ch.ker i a : ZMod p) * (Mx pk.v a x : ZMod p)) pk.n] at hz
    rw [← hz]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [chartMat, emb_apply]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun a => (Mx ch.ker i a : ZMod p) * (Mx pk.v a x : ZMod p)) pk.d]
  have hmem : ∀ i, kv i ∈ LinearMap.ker (chartMap pk ch p K) := fun i => hker i
  let kv' : Fin κ → LinearMap.ker (chartMap pk ch p K) := fun i => ⟨kv i, hmem i⟩
  have hli' : LinearIndependent (ZMod p) kv' :=
    LinearIndependent.of_comp (LinearMap.ker (chartMap pk ch p K)).subtype hli
  have hcard := LinearIndependent.fintype_card_le_finrank hli'
  rw [Fintype.card_fin] at hcard
  have hrn := (chartMap pk ch p K).finrank_range_add_finrank_ker
  rw [Module.finrank_fin_fun] at hrn
  have := hc.rank
  omega

end
end CatalanMeasure.GenD.Uniform.W.Prof
