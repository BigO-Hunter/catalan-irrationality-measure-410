module

public import Submission.CatalanMeasure.CellCert.CellW
public import Submission.CatalanMeasure.CellCert.CellPieces

@[expose] public section

open Set Nat CatalanMeasure.Cert
namespace CatalanMeasure.CellCert
set_option maxRecDepth 100000

/-! # 2-adically normalised level tables (R8)

The level table `LV j` of `PolyData` holds `wlist j B`, which carries the factorial factors `ff i j`; many
entries are multiples of `2^64`, and the kernel hashes `Nat` literals by their low 64 bits.  Here the table
stores `wlist j B / 2^(sh j)` (per-level 2-adic content), and a transfer lemma recovers `PolyData`. -/

def scP (c : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (p.1 * c, p.2 * c)

theorem zval_scP (c : ℕ) (p : ℕ × ℕ) : zval (scP c p) = (c : ℤ) * zval p := by
  simp only [zval, scP]; push_cast; ring

theorem hP_scP (neg : Bool) (y T c : ℕ) : ∀ (l : List (ℕ × ℕ)) (tp : ℕ),
    hP neg y T tp (l.map (scP c)) = scP c (hP neg y T tp l) := by
  intro l
  induction l with
  | nil => intro tp; simp [hP, scP]
  | cons a t ih =>
    intro tp
    simp only [List.map_cons, hP, ih]
    rcases h : hP neg y T (tp / T) t with ⟨u, v⟩
    simp only [scP]
    split_ifs
    · ext <;> simp <;> ring
    · ext <;> simp <;> ring

structure PolyDataS where
  B : List ℤ
  LV : List (List (ℕ × ℕ))
  sh : List ℕ
  lam : ℕ
  Tb : ℕ

namespace PolyDataS
def pw (D : PolyDataS) (j : ℕ) : ℕ := 2 ^ D.sh.getD j 0
def N (D : PolyDataS) : ℕ := D.B.length - 1
/-- the unscaled `PolyData` (used only in proofs; never evaluated) -/
def toD (D : PolyDataS) : PolyData :=
  ⟨D.B, (List.range D.LV.length).map (fun j => (D.LV.getD j []).map (scP (D.pw j))), D.lam, D.Tb⟩

theorem toD_N (D : PolyDataS) : D.toD.N = D.N := rfl
theorem toD_Z (D : PolyDataS) : D.toD.Z = shl (D.lam : ℤ) D.B := rfl
theorem toD_len (D : PolyDataS) : D.toD.LV.length = D.LV.length := by simp [toD]

theorem toD_getD (D : PolyDataS) (j : ℕ) :
    D.toD.LV.getD j [] = (D.LV.getD j []).map (scP (D.pw j)) := by
  by_cases h : j < D.LV.length
  · simp [toD, List.getD_eq_getElem?_getD, List.getElem?_range h, List.getElem?_eq_getElem h]
  · have h' : D.LV.length ≤ j := not_lt.mp h
    have h2 : ¬ j < D.toD.LV.length := by rw [toD_len]; exact h
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h', List.getElem?_eq_none (not_lt.mp h2)]

/-- the one-off Boolean check on the literal tables -/
def tab (D : PolyDataS) : Bool :=
  (List.range D.LV.length).all (fun j =>
    decide (wlist j D.B = zsc (D.pw j : ℤ) ((D.LV.getD j []).map zval)))

theorem toD_ok (D : PolyDataS) (hT : D.lam * D.Tb = 1099511627776) (hlam : 0 < D.lam)
    (htab : D.tab = true) : D.toD.Ok := by
  refine ⟨hT, hlam, fun j hj => ?_⟩
  rw [toD_len] at hj
  have h := List.all_eq_true.mp htab j (List.mem_range.mpr hj)
  have h2 := of_decide_eq_true h
  rw [toD_getD, List.map_map]
  change wlist j D.B = _
  rw [h2, zsc, List.map_map]
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply, zval_scP]

end PolyDataS

/-- scaled exact levels: `2^sh_j * lam^(N+j) * zval (hP ...)` -/
def polyValsS (D : PolyDataS) (cc : ℤ) (m : ℕ) : List ℤ :=
  (List.range m).map (fun j => ((D.pw j : ℕ) : ℤ) * (((D.lam ^ (D.N + j) : ℕ) : ℤ) *
    zval (hP (decide (cc < 0)) cc.natAbs D.Tb (D.Tb ^ D.N) (D.LV.getD j []))))

theorem polyValsD_toD (D : PolyDataS) (cc : ℤ) (m : ℕ) : polyValsD D.toD cc m = polyValsS D cc m := by
  unfold polyValsD polyValsS
  apply List.map_congr_left
  intro j _
  rw [PolyDataS.toD_getD, hP_scP, zval_scP]
  have e1 : D.toD.Tb = D.Tb := rfl
  have e2 : D.toD.N = D.N := rfl
  have e3 : D.toD.lam = D.lam := rfl
  rw [e1, e2, e3]
  ring

/-- `poly_sup_of` with the coefficient list divided by `2^t` (R8): `2^t * tcomb Bs = 2^N' * wlist m Z` -/
theorem poly_sup_of_sh (Z : List ℤ) (m : ℕ) (Bs : List ℤ) (MG : ℤ) (t N' : ℕ)
    (hid : zsc (2 ^ t) (tcomb Bs) = zsc (2 ^ N') (wlist m Z))
    (hMG : decide (SC * ((Bs.map zabs).sum * 2 ^ t) ≤ MG * (2 ^ N' * K40)) = true)
    (y : ℝ) (hy : |y| ≤ 1) : (SC : ℝ) * |ptZ Z m y| ≤ (MG : ℝ) := by
  have hS : (0 : ℝ) < SC := by exact_mod_cast SC_pos
  have h1 := tcomb_bound Bs y hy
  obtain ⟨Sz, hSz⟩ : ∃ Sz, (Bs.map zabs).sum = Sz := ⟨_, rfl⟩
  rw [hSz] at hMG
  have hw : lev (wlist m Z) y = lev (lder^[m] Z) y := by rw [wlist_eq m Z]
  have he := congrArg (fun l => lev l y) hid
  simp only [lev_zsc] at he
  rw [hw] at he
  rw [zl1_eq, hSz] at h1
  have hpt : ptZ Z m y = lev (lder^[m] Z) y / 1099511627776 := rfl
  have h2 : (SC * (Sz * 2 ^ t) : ℤ) ≤ MG * (2 ^ N' * K40) := of_decide_eq_true hMG
  have h2R : (SC : ℝ) * ((Sz : ℝ) * 2 ^ t) ≤ (MG : ℝ) * (2 ^ N' * 1099511627776) := by
    have := (Int.cast_le (R := ℝ)).mpr h2
    push_cast at this
    have hK : (K40 : ℝ) = 1099511627776 := by unfold K40; norm_num
    rw [hK] at this
    exact this
  have hp2 : (0 : ℝ) < 2 ^ N' := by positivity
  have hpt2 : (0 : ℝ) < 2 ^ t := by positivity
  push_cast at he
  have h3 : (2 : ℝ) ^ N' * |lev (lder^[m] Z) y| ≤ (Sz : ℝ) * 2 ^ t := by
    have : |(2 : ℝ) ^ N' * lev (lder^[m] Z) y| = |(2 : ℝ) ^ t * lev (tcomb Bs) y| := by rw [he]
    rw [abs_mul, abs_mul, abs_of_pos hp2, abs_of_pos hpt2] at this
    rw [this]
    nlinarith [h1, hpt2]
  rw [hpt, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 1099511627776)]
  rw [mul_div_assoc', div_le_iff₀ (by norm_num : (0 : ℝ) < 1099511627776)]
  nlinarith [h2R, h3, hp2, hS, mul_le_mul_of_nonneg_left h3 hS.le]

end CatalanMeasure.CellCert

#print axioms CatalanMeasure.CellCert.poly_sup_of_sh
#print axioms CatalanMeasure.CellCert.PolyDataS.toD_ok
#print axioms CatalanMeasure.CellCert.polyValsD_toD
