module

public import Submission.CatalanMeasure.GenD.Signed.Data.Cells.Core

@[expose] public section

/-! # Split polynomial check of a cell block

The block check `absLeL (shiftLK cb CbP.length fq.poly) CbP` of `blockOK4` needs bounds on all
Taylor coefficients of the degree-`N` field polynomial at the block centre `cb`.  Two facts make it
cheap:

* only the first `K + 1` coefficients need exact values: for `|cb| ≤ 1` every coefficient is
  dominated by the coefficient of `Σ |p_i| x^i` at `1` (`shiftL_dom`), a table `C` checked once per
  row; the block bound uses `C_k` beyond `K`;
* the exact part is computed after removing the power of two from the denominator of `cb`
  (`shiftLKs`): with `cb = n / (2^a m)` the Horner scheme runs at `n / m` on `p(x / 2^a)`, whose
  integer coefficients are `A_k 2^(a (N - k))`.  The plain form stores `t_k D d^(j-k)`, which is
  divisible by `2^64` for every entry once `d` carries a large power of two (block centres near a
  pole cluster), and the kernel's 64-bit literal hashes then collide.

`polySplit_ok` gives back the unchanged statement `absLeL (shiftLK cb CbP.length p) CbP = true`. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert

/-- `2`-adic valuation with fuel (any value with `2 ^ v2F f d ∣ d` is sound) -/
def v2F : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, d => if d % 2 = 0 ∧ d ≠ 0 then v2F f (d / 2) + 1 else 0

theorem pow_v2F_dvd : ∀ (f d : ℕ), 2 ^ v2F f d ∣ d := by
  intro f
  induction f with
  | zero => intro d; simp [v2F]
  | succ f ih =>
    intro d
    unfold v2F
    split_ifs with h
    · have h2 := ih (d / 2)
      have e : d = 2 * (d / 2) := by omega
      rw [pow_succ, mul_comm]
      calc 2 * 2 ^ v2F f (d / 2) ∣ 2 * (d / 2) := Nat.mul_dvd_mul_left 2 h2
        _ = d := e.symm
    · simp

/-- `A_k 2^(a e_k)` with exponents `e, e - 1, …` (structural, no `mapIdx`) -/
def scA (a : ℕ) : ℕ → List ℤ → List ℤ
  | _, [] => []
  | e, x :: xs => x * ((2 ^ (a * e) : ℕ) : ℤ) :: scA a (e - 1) xs

/-- the Kronecker shift of `shiftLKc` with the descaling base `e` separate from the Horner base `d` -/
def shiftLKcE (n : ℤ) (d e M : ℕ) (A : List ℤ) (D : ℕ) : List ℚ :=
  match bdN n d A with
  | (S, pw) => descaleL e ((D * pw : ℕ) : ℚ) 0
      (unpkS (Nat.log2 S + 2) (M + 1)
        (hzC n d (n + ((2 ^ (Nat.log2 S + 2) : ℕ) : ℤ)) ((2 ^ ((Nat.log2 S + 2) * (M + 1)) : ℕ) : ℤ) A).1)

/-- the entrywise form of `shiftLKcE` -/
def shZdesc (n : ℤ) (d e M : ℕ) (A : List ℤ) (D : ℕ) : List ℚ :=
  match shZ n d (M + 1) A with
  | (L, pw) => descaleL e ((D * pw : ℕ) : ℚ) 0 (L ++ List.replicate (M + 1 - L.length) 0)

/-- **Rescaled exact Taylor shift**: the first `M + 1` coefficients of `p` at `c` (`shiftLKs_getD`). -/
def shiftLKs (c : ℚ) (M : ℕ) (p : List ℚ) : List ℚ :=
  shiftLKcE c.num (c.den / 2 ^ v2F 128 c.den) c.den M
    (scA (v2F 128 c.den) (p.length - 1) (p.map (toZ (polyD p))))
    (polyD p * 2 ^ (v2F 128 c.den * (p.length - 1)))

theorem shiftLKcE_eq (n : ℤ) (d e M : ℕ) (A : List ℤ) (D : ℕ) :
    shiftLKcE n d e M A D = shZdesc n d e M A D := by
  unfold shiftLKcE shZdesc
  have hS := bdN_snd n d A
  have hsn := shZ_snd n d (M + 1) A
  rcases hb : bdN n d A with ⟨S, pw⟩
  rcases hs : shZ n d (M + 1) A with ⟨L, pw'⟩
  rw [hb] at hS
  rw [hs] at hsn
  simp only at hS hsn ⊢
  subst hS hsn
  have hlenL := shZ_fst_length_le' n d (M + 1) A
  have hlenL2 := shZ_fst_length_le n d (M + 1) A
  rw [hs] at hlenL hlenL2
  simp only at hlenL hlenL2
  have hpk := hzB_pack n d (Nat.log2 S + 2) A (A.length + 1) (Nat.lt_succ_self _)
  have hpk1 : (hzB n d (n + ((2 ^ (Nat.log2 S + 2) : ℕ) : ℤ)) A).1 =
      packZ (Nat.log2 S + 2) (shZ n d (A.length + 1) A).1 := by
    have := hpk.1
    simpa [Nat.cast_pow] using this
  have hcongr := unpkS_congr (Nat.log2 S + 2) (by omega) (M + 1)
    (hzC n d (n + ((2 ^ (Nat.log2 S + 2) : ℕ) : ℤ)) ((2 ^ ((Nat.log2 S + 2) * (M + 1)) : ℕ) : ℤ) A).1
    (hzB n d (n + ((2 ^ (Nat.log2 S + 2) : ℕ) : ℤ)) A).1
    (by simpa [Nat.cast_pow] using (hzC_modEq n d (n + ((2 ^ (Nat.log2 S + 2) : ℕ) : ℤ)) ((2 ^ ((Nat.log2 S + 2) * (M + 1)) : ℕ) : ℤ) A).1)
  rw [hcongr, hpk1]
  -- digit bounds
  have hSlt : S < 2 ^ (Nat.log2 S + 1) := Nat.lt_log2_self
  have hdig : ∀ y ∈ (shZ n d (A.length + 1) A).1,
      -(2 : ℤ) ^ (Nat.log2 S + 2 - 1) ≤ y ∧ y < (2 : ℤ) ^ (Nat.log2 S + 2 - 1) := by
    intro y hy
    have hb' := shZ_bound n d (A.length + 1) A y hy
    rw [hb] at hb'
    simp only at hb'
    have : (S : ℤ) < (2 : ℤ) ^ (Nat.log2 S + 2 - 1) := by
      have := hSlt
      have e : Nat.log2 S + 2 - 1 = Nat.log2 S + 1 := by omega
      rw [e]; exact_mod_cast this
    have hy' : |y| ≤ (S : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hb'
    constructor
    · have := neg_abs_le y; linarith [abs_le.mp hy']
    · linarith [(abs_le.mp hy').2]
  apply descaleL_congr
  · rw [unpkS_length]
    simp only [List.length_append, List.length_replicate]
    omega
  · intro k hk
    rw [unpkS_length] at hk
    rw [unpkS_pack (Nat.log2 S + 2) (by omega) _ hdig (M + 1) k hk]
    rw [getD_pad L (M + 1) k hlenL2]
    by_cases hk2 : k < A.length + 1
    · have e1 := shZ_cap_getD n d A (min (M + 1) (A.length + 1)) (M + 1) k (lt_min hk hk2) (min_le_left _ _)
      have e2 := shZ_cap_getD n d A (min (M + 1) (A.length + 1)) (A.length + 1) k (lt_min hk hk2) (min_le_right _ _)
      rw [hs] at e1
      simp only at e1
      exact e2.symm.trans e1
    · have h0 : L.getD k 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      have hfull := shZ_fst_length_le' n d (A.length + 1) A
      have h1 : (shZ n d (A.length + 1) A).1.getD k 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      rw [h0, h1]



/-! ### Scaling, prefix and domination lemmas for `shiftL` -/

theorem getD_map_div (L : List ℚ) (s : ℚ) (k : ℕ) :
    (L.map (fun x => x / s)).getD k 0 = L.getD k 0 / s := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[k]? <;> simp

theorem shiftStep_map_div (c s : ℚ) : ∀ (T : List ℚ) (x : ℚ),
    shiftStep c (T.map (fun y => y / s)) (x / s) = (shiftStep c T x).map (fun y => y / s) := by
  intro T
  induction T with
  | nil => intro x; simp [shiftStep]
  | cons t ts ih =>
    intro x
    simp only [List.map_cons, shiftStep, ih t]
    congr 1
    ring

theorem shiftL_map_div (c s : ℚ) (M : ℕ) : ∀ q : List ℚ,
    shiftL c M (q.map (fun y => y / s)) = (shiftL c M q).map (fun y => y / s) := by
  intro q
  induction q with
  | nil => simp [shiftL, List.map_replicate]
  | cons a as ih =>
    simp only [List.map_cons, shiftL, ih, shiftStep_map_div]

/-- the coefficient list of `p(x / 2^a)`: entry `i` is `p_i / 2^(a i)` -/
def scQ (a : ℕ) : List ℚ → List ℚ
  | [] => []
  | x :: xs => x :: (scQ a xs).map (fun y => y / 2 ^ a)

theorem shiftL_scale (a : ℕ) (c : ℚ) (M : ℕ) : ∀ (p : List ℚ) (k : ℕ), k ≤ M →
    (shiftL (2 ^ a * c) M (scQ a p)).getD k 0 = (shiftL c M p).getD k 0 / 2 ^ (a * k) := by
  intro p
  induction p with
  | nil =>
    intro k hk
    simp [shiftL, scQ, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> simp
  | cons x xs ih =>
    intro k hk
    have hl1 := shiftL_length (2 ^ a * c) M ((scQ a xs).map (fun y => y / 2 ^ a))
    have hl2 := shiftL_length c M xs
    simp only [scQ, shiftL]
    rw [shiftStep_getD _ _ _ k (by omega), shiftStep_getD _ _ _ k (by omega), shiftL_map_div,
      getD_map_div, ih k hk]
    have hp : (2 : ℚ) ^ a ≠ 0 := by positivity
    cases k with
    | zero => simp; field_simp
    | succ j =>
      simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
      rw [getD_map_div, ih j (by omega), show a * (j + 1) = a * j + a by ring, pow_add]
      have hq : (2 : ℚ) ^ (a * j) ≠ 0 := by positivity
      field_simp

theorem scA_map (a D : ℕ) : ∀ (xs : List ℤ) (e : ℕ), (xs = [] ∨ xs.length = e + 1) →
    (scA a e xs).map (fun z : ℤ => (z : ℚ) / ((D * 2 ^ (a * e) : ℕ) : ℚ)) =
      scQ a (xs.map (fun z : ℤ => (z : ℚ) / (D : ℚ))) := by
  intro xs
  induction xs with
  | nil => intro e _; simp [scA, scQ]
  | cons x xs ih =>
    intro e he
    rcases he with he | he
    · simp at he
    simp only [List.length_cons, add_left_inj] at he
    simp only [scA, scQ, List.map_cons]
    congr 1
    · push_cast
      have : (2 : ℚ) ^ (a * e) ≠ 0 := by positivity
      by_cases hD : (D : ℚ) = 0
      · simp [hD]
      · field_simp
    · rcases Nat.eq_zero_or_pos e with h0 | hpos
      · subst h0
        have : xs = [] := List.eq_nil_of_length_eq_zero he
        subst this; simp [scA, scQ]
      · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
        rw [← ih e' (Or.inr he), List.map_map]
        simp only [Nat.add_sub_cancel]
        apply List.map_congr_left
        intro z _
        simp only [Function.comp]
        push_cast
        rw [show a * (e' + 1) = a * e' + a by ring, pow_add]
        by_cases hD : (D : ℚ) = 0
        · simp [hD]
        · have : (2 : ℚ) ^ (a * e') ≠ 0 := by positivity
          have : (2 : ℚ) ^ a ≠ 0 := by positivity
          field_simp

/-- **The rescaled shift is exact**: its entries are the Taylor coefficients of `p` at `c`. -/
theorem shiftLKs_getD (c : ℚ) (M : ℕ) (p : List ℚ) (k : ℕ) (hk : k ≤ M) :
    (shiftLKs c M p).getD k 0 = (shiftL c M p).getD k 0 := by
  set d := c.den with hd
  set a := v2F 128 d with ha
  set m := d / 2 ^ a with hmdef
  set N := p.length - 1 with hN
  set D := polyD p with hDdef
  set A : List ℤ := p.map (toZ D) with hA
  have hdm : d = 2 ^ a * m := (Nat.mul_div_cancel' (pow_v2F_dvd 128 d)).symm
  have hd0 : 0 < d := c.den_pos
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hdm; omega
    · exact h
  have hD := polyD_pos p
  have hD' : 0 < D * 2 ^ (a * N) := Nat.mul_pos hD (by positivity)
  have hpA : A.map (fun z : ℤ => (z : ℚ) / (D : ℚ)) = p := by
    rw [hA, List.map_map]
    conv_rhs => rw [← List.map_id p]
    apply List.map_congr_left
    intro x hx
    simp only [Function.comp, id]
    exact toZ_spec D x hD (polyD_dvd p x hx)
  have hAl : A = [] ∨ A.length = N + 1 := by
    rcases p with _ | ⟨x, xs⟩
    · left; simp [hA]
    · right; simp [hA, hN]
  have hsc := scA_map a D A N hAl
  rw [hpA] at hsc
  have hcq : (2 : ℚ) ^ a * c = (c.num : ℚ) / (m : ℚ) := by
    have hcd : c * (d : ℚ) = c.num := Rat.mul_den_eq_num c
    rw [eq_div_iff (by exact_mod_cast hm.ne'), ← hcd, hdm]
    push_cast; ring
  have hmain := shiftL_main ((c.num : ℚ) / (m : ℚ)) M c.num m hm rfl (D * 2 ^ (a * N)) hD'
    (scA a N A) k hk
  rw [hsc, ← hcq, shiftL_scale a c M p k hk] at hmain
  have hlenL := shZ_fst_length_le c.num m (M + 1) (scA a N A)
  have hpw := shZ_snd c.num m (M + 1) (scA a N A)
  unfold shiftLKs
  rw [shiftLKcE_eq]
  unfold shZdesc
  rcases hh : shZ c.num m (M + 1) (scA a N A) with ⟨L, pw⟩
  rw [hh] at hlenL hpw hmain
  simp only at hlenL hpw hmain
  rcases descaleL_getD d (((D * 2 ^ (a * N)) * pw : ℕ) : ℚ) (L ++ List.replicate (M + 1 - L.length) 0) 0 k with h | h
  · rw [h, getD_pad L (M + 1) k hlenL, zero_add, hpw]
    have h2 : (2 : ℚ) ^ (a * k) ≠ 0 := by positivity
    have e2 : (shiftL c M p).getD k 0 = 2 ^ (a * k) * ((shiftL c M p).getD k 0 / 2 ^ (a * k)) := by
      field_simp
    rw [e2, hmain, hdm]
    push_cast
    rw [mul_pow, ← pow_mul]
    have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    have : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    field_simp
  · simp only [List.length_append, List.length_replicate] at h
    omega

theorem shiftL_prefix (c : ℚ) : ∀ (p : List ℚ) (K M k : ℕ), k ≤ K → K ≤ M →
    (shiftL c K p).getD k 0 = (shiftL c M p).getD k 0 := by
  intro p
  induction p with
  | nil =>
    intro K M k hk hKM
    simp [shiftL, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl
  | cons x xs ih =>
    intro K M k hk hKM
    have h1 := shiftL_length c K xs
    have h2 := shiftL_length c M xs
    simp only [shiftL]
    rw [shiftStep_getD _ _ _ k (by omega), shiftStep_getD _ _ _ k (by omega), ih K M k hk hKM]
    cases k with
    | zero => simp
    | succ j => simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, ih K M j (by omega) hKM]

theorem shiftL_dom (c : ℚ) (hc : |c| ≤ 1) (M : ℕ) : ∀ (p : List ℚ) (k : ℕ),
    |(shiftL c M p).getD k 0| ≤ (shiftL 1 M (p.map (fun x => |x|))).getD k 0 := by
  intro p
  induction p with
  | nil =>
    intro k
    simp [shiftL, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> simp
  | cons x xs ih =>
    intro k
    have h1 := shiftL_length c M xs
    have h2 := shiftL_length 1 M (xs.map (fun x => |x|))
    simp only [List.map_cons, shiftL]
    by_cases hk : k < M + 1
    · rw [shiftStep_getD _ _ _ k (by omega), shiftStep_getD _ _ _ k (by omega)]
      have hck : |c * (shiftL c M xs).getD k 0| ≤ (shiftL 1 M (xs.map (fun x => |x|))).getD k 0 := by
        rw [abs_mul]
        calc |c| * |(shiftL c M xs).getD k 0| ≤ 1 * |(shiftL c M xs).getD k 0| :=
              mul_le_mul_of_nonneg_right hc (abs_nonneg _)
          _ ≤ _ := by rw [one_mul]; exact ih k
      have hprev : |(if k = 0 then x else (shiftL c M xs).getD (k - 1) 0)| ≤
          (if k = 0 then |x| else (shiftL 1 M (xs.map (fun x => |x|))).getD (k - 1) 0) := by
        split_ifs
        · exact le_rfl
        · exact ih (k - 1)
      calc |c * (shiftL c M xs).getD k 0 + (if k = 0 then x else (shiftL c M xs).getD (k - 1) 0)|
          ≤ |c * (shiftL c M xs).getD k 0| + |(if k = 0 then x else (shiftL c M xs).getD (k - 1) 0)| :=
            abs_add_le _ _
        _ ≤ _ := by rw [one_mul]; exact add_le_add hck hprev
    · have e1 : (shiftStep c (shiftL c M xs) x).getD k 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [shiftStep_length]; omega)]; rfl
      have e2 : (shiftStep 1 (shiftL 1 M (xs.map (fun x => |x|))) |x|).getD k 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [shiftStep_length]; omega)]; rfl
      rw [e1, e2, abs_zero]

/-! ### The split check -/

theorem absLeAll_of (T : List ℚ) : ∀ (Bl : List ℚ) (k : ℕ),
    (∀ i < Bl.length, qabs' (T.getD (k + i) 0) ≤ Bl.getD i 0) → absLeAll T k Bl = true := by
  intro Bl
  induction Bl with
  | nil => intro k _; rfl
  | cons b bs ih =>
    intro k h
    simp only [absLeAll, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨by simpa using h 0 (by simp), ih (k + 1) (fun i hi => ?_)⟩
    have := h (i + 1) (by simpa using hi)
    rw [show k + (i + 1) = k + 1 + i by omega] at this
    simpa using this

/-- pairwise `C_i ≤ B_i` (missing `C` entries read as `0`) -/
def tailLe : List ℚ → List ℚ → Bool
  | _, [] => true
  | [], b :: bs => decide (0 ≤ b) && tailLe [] bs
  | c :: cs, b :: bs => decide (c ≤ b) && tailLe cs bs

theorem tailLe_spec : ∀ (C B : List ℚ), tailLe C B = true → ∀ i < B.length, C.getD i 0 ≤ B.getD i 0 := by
  intro C B
  induction B generalizing C with
  | nil => intro _ i hi; simp at hi
  | cons b bs ih =>
    intro h i hi
    cases C with
    | nil =>
      simp only [tailLe, Bool.and_eq_true, decide_eq_true_eq] at h
      cases i with
      | zero => simpa using h.1
      | succ j => simpa using ih [] h.2 j (by simpa using hi)
    | cons c cs =>
      simp only [tailLe, Bool.and_eq_true, decide_eq_true_eq] at h
      cases i with
      | zero => simpa using h.1
      | succ j => simpa using ih cs h.2 j (by simpa using hi)

theorem getD_drop' (L : List ℚ) (n j : ℕ) : (L.drop n).getD j 0 = L.getD (n + j) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **Split polynomial check.**  Exact rescaled coefficients up to order `K` (`hex`), the row table
`C` of the coefficients of `Σ |p_i| x^i` at `1` (`hC`, checked once per row) and `C_k ≤ B_k` beyond
`K` (`htail`) give the block check of `blockOK4` for any centre with `|cb| ≤ 1`. -/
theorem polySplit_ok (cb : ℚ) (K L : ℕ) (p C B : List ℚ) (hcb : qabs' cb ≤ 1) (hL : B.length = L)
    (hK : K ≤ L) (hC : absLeL (shiftLK 1 L (p.map qabs')) C = true) (hCl : L ≤ C.length)
    (hex : absLeL (shiftLKs cb K p) B = true)
    (htail : tailLe (C.drop (K + 1)) (B.drop (K + 1)) = true) :
    absLeL (shiftLK cb B.length p) B = true := by
  subst hL
  have e0 := absLeAll_eq B (shiftLK cb B.length p) 0
  rw [List.drop_zero] at e0
  rw [← e0]
  apply absLeAll_of
  intro i hi
  rw [zero_add, shiftLK_eq']
  have hexs : ∀ j < B.length, qabs' ((shiftLKs cb K p).getD j 0) ≤ B.getD j 0 := by
    have e1 := absLeAll_eq B (shiftLKs cb K p) 0
    rw [List.drop_zero, hex] at e1
    intro j hj
    simpa using absLeAll_spec _ B 0 e1 j hj
  by_cases hiK : i ≤ K
  · rw [← shiftL_prefix cb p K B.length i hiK hK, ← shiftLKs_getD cb K p i hiK]
    exact hexs i hi
  · have hcs : ∀ j < C.length, qabs' ((shiftLK 1 B.length (p.map qabs')).getD j 0) ≤ C.getD j 0 := by
      have e1 := absLeAll_eq C (shiftLK 1 B.length (p.map qabs')) 0
      rw [List.drop_zero, hC] at e1
      intro j hj
      simpa using absLeAll_spec _ C 0 e1 j hj
    have hdom := shiftL_dom cb (by rw [← qabs'_eq_abs]; exact hcb) B.length p i
    have hq : (p.map qabs') = p.map (fun x => |x|) := by
      apply List.map_congr_left; intro x _; exact qabs'_eq_abs x
    have h1 := hcs i (by omega)
    rw [shiftLK_eq', hq, qabs'_eq_abs] at h1
    have h2 := tailLe_spec _ _ htail (i - (K + 1)) (by rw [List.length_drop]; omega)
    rw [getD_drop', getD_drop', show K + 1 + (i - (K + 1)) = i by omega] at h2
    rw [qabs'_eq_abs]
    linarith [le_abs_self ((shiftL 1 B.length (p.map (fun x => |x|))).getD i 0)]

end CatalanMeasure.GenD.Signed.Data.Cells
