module
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Int.Basic
@[expose] public section
set_option Elab.async false

/-!
# Stored packets (Lemma C data) and their integer checker

A *packet* is the stored form of Lemma C for one leaf piece:

* `v` : `d` integer rows of length `n` (a saturated basis of the rational subspace `V ⊂ ℚⁿ`);
* `piv`, `adj`, `delta` : `d` pivot columns and an integer matrix `adj` with
  `adj · V_Pᵀ = delta · I` (`V_P[b][i] = v[b][piv i]`).  So `delta` is a nonzero `d × d` minor
  multiple and the rows of `v` stay independent modulo every `p ∤ delta`;
* for each chart `j`: integerised chart rows `rows` (`m_j × n`), the rank bound `r`, and
  `d - r` kernel vectors `ker` in `V`-coordinates, with
  `Σ_a ker[i][a] · v[a]` annihilated by every chart row (exact integer identity),
  together with independence data `qpiv`, `qadj`, `qdelta` of the same shape as for `v`.

`Packet.check` is a `Bool` computed with big-`Int` arithmetic on lists; `Packet.check_sound`
turns `check = true` into the indexed integer identities `Packet.Sound`, with no primes involved.
-/

namespace CatalanMeasure.GenD.Uniform.W.Prof
open Finset
noncomputable section

/-- Dot product of integer lists. -/
def dot (a b : List ℤ) : ℤ := (List.zipWith (· * ·) a b).sum

theorem dot_eq : ∀ (a b : List ℤ) (n : ℕ), a.length = n → b.length = n →
    dot a b = ∑ i ∈ range n, a.getD i 0 * b.getD i 0
  | [], [], 0, _, _ => by simp [dot]
  | [], _, n + 1, h, _ => by simp at h
  | _ :: _, [], 0, h, _ => by simp at h
  | _ :: _, _, 0, h, _ => by simp at h
  | x :: a, [], n + 1, _, h => by simp at h
  | x :: a, y :: b, n + 1, ha, hb => by
    have ha' : a.length = n := by simpa using ha
    have hb' : b.length = n := by simpa using hb
    have ih := dot_eq a b n ha' hb'
    rw [Finset.sum_range_succ']
    simp only [dot, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    simp [ih, add_comm]

/-- Matrix entry of a list-of-lists matrix (zero outside). -/
def Mx (A : List (List ℤ)) (i j : ℕ) : ℤ := (A.getD i []).getD j 0

/-- `A · Btᵀ`: entry `(i,j)` is the dot product of row `i` of `A` with row `j` of `Bt`. -/
def lmul (A Bt : List (List ℤ)) : List (List ℤ) := A.map fun a => Bt.map (dot a)

theorem Mx_lmul (A Bt : List (List ℤ)) (s : ℕ) (hA : ∀ a ∈ A, a.length = s)
    (hB : ∀ b ∈ Bt, b.length = s) {i j : ℕ} (hi : i < A.length) (hj : j < Bt.length) :
    Mx (lmul A Bt) i j = ∑ c ∈ range s, Mx A i c * Mx Bt j c := by
  have h1 : A.getD i [] = A[i] := by simp [List.getD_eq_getElem?_getD, hi]
  have h2 : Bt.getD j [] = Bt[j] := by simp [List.getD_eq_getElem?_getD, hj]
  have h3 : (lmul A Bt).getD i [] = Bt.map (dot A[i]) := by
    simp [lmul, List.getD_eq_getElem?_getD, hi]
  unfold Mx
  rw [h3, h1, h2]
  have : (Bt.map (dot A[i])).getD j 0 = dot A[i] Bt[j] := by
    simp [List.getD_eq_getElem?_getD, hj]
  rw [this]
  exact dot_eq _ _ s (hA _ (List.getElem_mem hi)) (hB _ (List.getElem_mem hj))

/-- The `k × k` matrix `δ · I`. -/
def idScaled (k : ℕ) (δ : ℤ) : List (List ℤ) :=
  (List.range k).map fun i => (List.range k).map fun j => if i = j then δ else 0

/-- The columns `piv` of `rows`. -/
def pivCols (rows : List (List ℤ)) (piv : List ℕ) : List (List ℤ) :=
  rows.map fun r => piv.map fun c => r.getD c 0

/-- Rectangular shape check. -/
def shape (A : List (List ℤ)) (r s : ℕ) : Bool :=
  A.length == r && A.all fun a => a.length == s

theorem shape_sound {A : List (List ℤ)} {r s : ℕ} (h : shape A r s = true) :
    A.length = r ∧ ∀ a ∈ A, a.length = s := by
  simp only [shape, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1, fun a ha => by simpa using h.2 a ha⟩

/-- Independence certificate: `W · P(rows)ᵀ = δ I` for pivot columns `piv` of `rows`. -/
def indOK (rows : List (List ℤ)) (m : ℕ) (piv : List ℕ) (W : List (List ℤ)) (δ : ℤ) : Bool :=
  shape rows rows.length m && piv.length == rows.length && piv.all (· < m) &&
    shape W rows.length rows.length &&
    lmul W (pivCols rows piv) == idScaled rows.length δ

theorem Mx_pivCols (rows : List (List ℤ)) (piv : List ℕ) {b i : ℕ} (hb : b < rows.length)
    (hi : i < piv.length) : Mx (pivCols rows piv) b i = Mx rows b (piv.getD i 0) := by
  simp [Mx, pivCols, List.getD_eq_getElem?_getD, hb, hi]

theorem Mx_idScaled {k : ℕ} (δ : ℤ) {a b : ℕ} (ha : a < k) (hb : b < k) :
    Mx (idScaled k δ) a b = if a = b then δ else 0 := by
  simp [Mx, idScaled, List.getD_eq_getElem?_getD, ha, hb]

/-- Integer content of an independence certificate. -/
theorem indOK_sound {rows : List (List ℤ)} {m : ℕ} {piv : List ℕ} {W : List (List ℤ)} {δ : ℤ}
    (h : indOK rows m piv W δ = true) :
    (∀ r ∈ rows, r.length = m) ∧ (∀ i < rows.length, piv.getD i 0 < m) ∧
    ∀ a b, a < rows.length → b < rows.length →
      ∑ i ∈ range rows.length, Mx W a i * Mx rows b (piv.getD i 0) =
        if a = b then δ else 0 := by
  simp only [indOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  obtain ⟨_, hr⟩ := shape_sound h1
  obtain ⟨hWl, hW⟩ := shape_sound h4
  refine ⟨hr, fun i hi => h3 _ ?_, fun a b ha hb => ?_⟩
  · rw [List.getD_eq_getElem?_getD]
    simp [h2, hi]
  · have hP : ∀ x ∈ pivCols rows piv, x.length = rows.length := by
      intro x hx
      simp only [pivCols, List.mem_map] at hx
      obtain ⟨r, _, rfl⟩ := hx
      simp [h2]
    have hlen : (pivCols rows piv).length = rows.length := by simp [pivCols]
    have := Mx_lmul W (pivCols rows piv) rows.length hW hP (i := a) (j := b) (by omega)
      (by omega)
    rw [h5, Mx_idScaled δ ha hb] at this
    rw [this]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Mx_pivCols rows piv hb (by simpa [h2] using Finset.mem_range.mp hi)]

/-- Chart kernel certificate: `Σ_c B[r][c] · (Σ_a K[i][a] V[a][c]) = 0`. -/
def kerOK (V : List (List ℤ)) (n d : ℕ) (K B : List (List ℤ)) : Bool :=
  shape V d n && K.all (fun k => k.length == d) && B.all (fun b => b.length == n) &&
    (lmul (lmul K ((List.range n).map fun c => V.map fun row => row.getD c 0)) B).all
      (fun r => r.all (· == 0))

theorem Mx_cols (V : List (List ℤ)) (n : ℕ) {c a : ℕ} (hc : c < n) (ha : a < V.length) :
    Mx ((List.range n).map fun c => V.map fun row => row.getD c 0) c a = Mx V a c := by
  simp [Mx, List.getD_eq_getElem?_getD, hc, ha]

theorem kerOK_sound {V : List (List ℤ)} {n d : ℕ} {K B : List (List ℤ)}
    (h : kerOK V n d K B = true) :
    ∀ i r, i < K.length → r < B.length →
      ∑ c ∈ range n, Mx B r c * (∑ a ∈ range d, Mx K i a * Mx V a c) = 0 := by
  simp only [kerOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  obtain ⟨hVl, hV⟩ := shape_sound h1
  intro i r hi hr
  set Vt : List (List ℤ) := (List.range n).map fun c => V.map fun row => row.getD c 0 with hVt
  have hVtl : ∀ x ∈ Vt, x.length = d := by
    intro x hx
    simp only [hVt, List.mem_map] at hx
    obtain ⟨c, _, rfl⟩ := hx
    simp [hVl]
  have hKl : ∀ k ∈ K, k.length = d := fun k hk => by simpa using h2 k hk
  have hBl : ∀ b ∈ B, b.length = n := fun b hb => by simpa using h3 b hb
  have hVtn : Vt.length = n := by simp [hVt]
  set X : List (List ℤ) := lmul K Vt with hX
  have hXl : ∀ x ∈ X, x.length = n := by
    intro x hx
    simp only [hX, lmul, List.mem_map] at hx
    obtain ⟨k, _, rfl⟩ := hx
    simp [hVtn]
  have hXlen : X.length = K.length := by simp [hX, lmul]
  have hiY : i < (lmul X B).length := by simp [lmul, hXlen]; exact hi
  have hYr : Mx (lmul X B) i r = 0 := by
    have hrow : (lmul X B)[i] ∈ lmul X B := List.getElem_mem hiY
    have h5 := h4 _ hrow
    try simp only [List.all_eq_true, beq_iff_eq] at h5
    have hr' : r < ((lmul X B)[i]).length := by
      simp [lmul]; exact hr
    have h6 := h5 _ (List.getElem_mem hr')
    have : Mx (lmul X B) i r = ((lmul X B)[i])[r]'hr' := by
      simp [Mx, List.getD_eq_getElem?_getD, hiY, hr']
    rw [this]; exact h6
  rw [Mx_lmul X B n hXl hBl (by omega) hr] at hYr
  rw [← hYr]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hc' : c < Vt.length := by simpa [hVtn] using Finset.mem_range.mp hc
  have hMX : Mx X i c = ∑ a ∈ range d, Mx K i a * Mx Vt c a :=
    Mx_lmul K Vt d hKl hVtl hi hc'
  rw [hMX, mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Mx_cols V n (by simpa [hVtn] using hc') (by simpa [hVl] using Finset.mem_range.mp ha)]

end
end CatalanMeasure.GenD.Uniform.W.Prof
