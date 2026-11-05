module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.SlotsToTiling
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts3.Flags
public import Submission.CatalanMeasure.GenD.Uniform.W.Prof.LemmaC
@[expose] public section
set_option Elab.async false

/-!
# Jets of coordinate polynomials (generic)

* `jet0 j`, `jetInf j` : coordinate jets at `0` and `∞` (`x ↦ x_j`, `x ↦ x_{p-1-j}`, `0` outside `[0,p)`);
* coordinatewise: Taylor jets / coefficient jets are coefficients of the coordinate polynomial `polx`;
* `row_of_chart` : a vanishing chart image kills every stored row.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts4
open Module Polynomial Finset CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Charts3
noncomputable section
variable {p : ℕ} [Fact p.Prime]

local notation "Fp" => ZMod p

/-- Coefficient jet at `0`. -/
def jet0 {d : ℕ} (j : ℕ) : (Fin p → (Fin d → Fp)) →ₗ[Fp] (Fin d → Fp) :=
  if h : j < p then LinearMap.proj ⟨j, h⟩ else 0

/-- Coefficient jet at `∞` (reversed). -/
def jetInf {d : ℕ} (j : ℕ) : (Fin p → (Fin d → Fp)) →ₗ[Fp] (Fin d → Fp) :=
  if h : j < p then LinearMap.proj ⟨p - 1 - j, by omega⟩ else 0

theorem jet0_coord {d : ℕ} (j : ℕ) (x : Fin p → Fin d → Fp) (c : Fin d) :
    jet0 j x c = (polx x c).coeff j := by
  unfold jet0
  by_cases h : j < p
  · rw [dif_pos h]
    have := polx_coeff x c ⟨j, h⟩
    simpa using this.symm
  · rw [dif_neg h]
    simp only [LinearMap.zero_apply, Pi.zero_apply]
    exact (coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (polx_degree x c)
      (by exact_mod_cast not_lt.mp h))).symm

theorem jetInf_coord {d : ℕ} (j : ℕ) (x : Fin p → Fin d → Fp) (c : Fin d) :
    jetInf j x c = if j < p then (polx x c).coeff (p - 1 - j) else 0 := by
  unfold jetInf
  by_cases h : j < p
  · rw [dif_pos h, if_pos h]
    have := polx_coeff x c ⟨p - 1 - j, by omega⟩
    simpa using this.symm
  · rw [dif_neg h, if_neg h]; simp

theorem taylorJet_coord {d : ℕ} (a : Fp) (j : ℕ) (x : Fin p → Fin d → Fp) (c : Fin d) :
    Charts3.taylorJet (m := p) (d := d) a j x c = (taylor a (polx x c)).coeff j := by
  rw [Charts3.taylorJet_coeff]; rfl

theorem emb_comm {pk : Packet} {K : ℕ} (L : (Fin p → (Fin pk.d → Fp)) →ₗ[Fp] (Fin pk.d → Fp))
    (L' : (Fin p → (Fin K → Fp)) →ₗ[Fp] (Fin K → Fp))
    (h : ∀ x, emb pk p K (L x) = L' (fun e => emb pk p K (x e))) (x : Fin p → Fin pk.d → Fp) :
    emb pk p K (L x) = L' (fun e => emb pk p K (x e)) := h x

theorem emb_taylorJet {pk : Packet} {K : ℕ} (a : Fp) (j : ℕ) (x : Fin p → Fin pk.d → Fp) :
    emb pk p K (Charts3.taylorJet (m := p) (d := pk.d) a j x) = Charts3.taylorJet (m := p) (d := K) a j (fun e => emb pk p K (x e)) := by
  simp only [Charts3.taylorJet, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, map_sum,
    map_smul]

theorem emb_jet0 {pk : Packet} {K : ℕ} (j : ℕ) (x : Fin p → Fin pk.d → Fp) :
    emb pk p K (jet0 j x) = jet0 j (fun e => emb pk p K (x e)) := by
  unfold jet0
  by_cases h : j < p <;> simp [h]

theorem emb_jetInf {pk : Packet} {K : ℕ} (j : ℕ) (x : Fin p → Fin pk.d → Fp) :
    emb pk p K (jetInf j x) = jetInf j (fun e => emb pk p K (x e)) := by
  unfold jetInf
  by_cases h : j < p <;> simp [h]

/-- A vanishing chart image kills every stored row. -/
theorem row_of_chart {pk : Packet} {ch : Chart} {K : ℕ} (y : Fin pk.d → Fp)
    (hy : chartMap pk ch p K y = 0) (i : ℕ) (hi : i < ch.rows.length) :
    ∑ c : Fin K, ((Mx ch.rows i c : ℤ) : Fp) * emb pk p K y c = 0 := by
  have := congrFun hy ⟨i, hi⟩
  simpa [chartMap, chartLin, chartMat, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using this

end
end CatalanMeasure.GenD.Uniform.W.Charts4
