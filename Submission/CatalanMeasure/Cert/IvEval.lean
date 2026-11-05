module

public import Submission.CatalanMeasure.Cert.Norm

@[expose] public section

/-!
# Fixed-point interval evaluation of long rational sums

Exact rational evaluation in the kernel costs a gcd per operation, and the numbers grow with the
sum: a pole tail `c z^k` at `k = 1000` has 50k-bit numerator and denominator. Here every value `x`
is carried as an integer enclosure `[lo, hi]` of `x · S` for a fixed scale `S`, rounded outwards at
each step, so the operands stay near `log₂ S` bits and no gcd is taken.

* `Enc S I x`: `lo ≤ x S ≤ hi`; closed under `add`, multiplication by a rational constant (`mulC`),
  division by a positive integer (`divN`), squaring (`sq`, scale `S²`) and rational inputs
  (`ofQ`, `ofQdiv`).
* `seqLoop`: `Σ_{k<n} φ_k(u_k)` for `u_k = g_k + Σ_i c_i z_i^(k+1)` (finite part plus pole tails),
  the poles carried by the recurrence `c z^(k+2) = (c z^(k+1)) · z` (`seqLoop_enc`).
* `momLoop`: `Σ_{k<n} φ_k(v_k)` for values with a stateless enclosure, e.g. the moments
  `mom1 p m = Σ_j p_j / (m + j)` (`momIv`).
* `le_of_enc`, `le_of_enc'`: a rational bound from an enclosure, checked by one integer comparison.
-/

namespace CatalanMeasure.Cert.Iv

set_option linter.dupNamespace false

/-- An integer interval; at scale `S` it encloses `x` when `lo ≤ x S ≤ hi`. -/
structure Iv where
  lo : ℤ
  hi : ℤ

def Enc (S : ℚ) (I : Iv) (x : ℚ) : Prop := (I.lo : ℚ) ≤ x * S ∧ x * S ≤ (I.hi : ℚ)

/-! ### Rounded division -/

/-- `⌊a / d⌋`. -/
def fdiv (a : ℤ) (d : ℕ) : ℤ := a / (d : ℤ)

/-- `⌈a / d⌉`. -/
def cdiv (a : ℤ) (d : ℕ) : ℤ := -((-a) / (d : ℤ))

theorem fdiv_mul_le (a : ℤ) {d : ℕ} (hd : 0 < d) : ((fdiv a d : ℤ) : ℚ) * d ≤ a := by
  have h : a / (d : ℤ) * (d : ℤ) ≤ a := Int.ediv_mul_le a (by exact_mod_cast hd.ne')
  unfold fdiv
  exact_mod_cast h

theorem le_cdiv_mul (a : ℤ) {d : ℕ} (hd : 0 < d) : (a : ℚ) ≤ ((cdiv a d : ℤ) : ℚ) * d := by
  have h : -a / (d : ℤ) * (d : ℤ) ≤ -a := Int.ediv_mul_le (-a) (by exact_mod_cast hd.ne')
  have h' : ((-a / (d : ℤ) : ℤ) : ℚ) * d ≤ -(a : ℚ) := by exact_mod_cast h
  unfold cdiv
  push_cast
  linarith

theorem fdiv_le_div (a : ℤ) {d : ℕ} (hd : 0 < d) {y : ℚ} (h : (a : ℚ) ≤ y) :
    ((fdiv a d : ℤ) : ℚ) ≤ y / d := by
  rw [le_div_iff₀ (by exact_mod_cast hd)]
  exact (fdiv_mul_le a hd).trans h

theorem div_le_cdiv (a : ℤ) {d : ℕ} (hd : 0 < d) {y : ℚ} (h : y ≤ (a : ℚ)) :
    y / d ≤ ((cdiv a d : ℤ) : ℚ) := by
  rw [div_le_iff₀ (by exact_mod_cast hd)]
  exact h.trans (le_cdiv_mul a hd)

/-! ### Operations -/

def zero : Iv := ⟨0, 0⟩

def add (I J : Iv) : Iv := ⟨I.lo + J.lo, I.hi + J.hi⟩

/-- `x ↦ x c` for a rational constant `c`. -/
def mulC (I : Iv) (c : ℚ) : Iv :=
  if 0 ≤ c.num then ⟨fdiv (I.lo * c.num) c.den, cdiv (I.hi * c.num) c.den⟩
  else ⟨fdiv (I.hi * c.num) c.den, cdiv (I.lo * c.num) c.den⟩

/-- `x ↦ x / m`. -/
def divN (I : Iv) (m : ℕ) : Iv := ⟨fdiv I.lo m, cdiv I.hi m⟩

/-- The rational `q / m` at scale `S`. -/
def ofQdiv (S : ℕ) (q : ℚ) (m : ℕ) : Iv := ⟨fdiv (q.num * S) (q.den * m), cdiv (q.num * S) (q.den * m)⟩

/-- The rational `q` at scale `S`. -/
def ofQ (S : ℕ) (q : ℚ) : Iv := ofQdiv S q 1

def sqLo (I : Iv) : ℤ := if 0 < I.lo then I.lo * I.lo else if I.hi < 0 then I.hi * I.hi else 0

def sqHi (I : Iv) : ℤ := max (I.lo * I.lo) (I.hi * I.hi)

/-- `x ↦ x²`, from scale `S` to scale `S²`. -/
def sq (I : Iv) : Iv := ⟨sqLo I, sqHi I⟩

def sumIv : List Iv → Iv
  | [] => zero
  | I :: Is => add I (sumIv Is)

theorem enc_zero (S : ℚ) : Enc S zero 0 := by simp [Enc, zero]

theorem enc_add {S : ℚ} {I J : Iv} {x y : ℚ} (hI : Enc S I x) (hJ : Enc S J y) :
    Enc S (add I J) (x + y) := by
  obtain ⟨h1, h2⟩ := hI
  obtain ⟨h3, h4⟩ := hJ
  constructor <;> simp only [add] <;> push_cast <;> linarith

theorem num_div_den_mul (y c : ℚ) : y * c = y * c.num / c.den := by
  conv_lhs => rw [← Rat.num_div_den c]
  ring

theorem enc_mulC {S : ℚ} {I : Iv} {x : ℚ} (h : Enc S I x) (c : ℚ) : Enc S (mulC I c) (x * c) := by
  obtain ⟨h1, h2⟩ := h
  have hd : 0 < c.den := c.den_pos
  have e : x * c * S = x * S * c.num / c.den := by rw [mul_right_comm, num_div_den_mul]
  unfold mulC
  split_ifs with hn
  · have hn' : (0 : ℚ) ≤ c.num := by exact_mod_cast hn
    refine ⟨?_, ?_⟩ <;> simp only [e]
    · exact fdiv_le_div _ hd (by push_cast; exact mul_le_mul_of_nonneg_right h1 hn')
    · exact div_le_cdiv _ hd (by push_cast; exact mul_le_mul_of_nonneg_right h2 hn')
  · have hn' : (c.num : ℚ) ≤ 0 := by exact_mod_cast (not_le.mp hn).le
    refine ⟨?_, ?_⟩ <;> simp only [e]
    · exact fdiv_le_div _ hd (by push_cast; exact mul_le_mul_of_nonpos_right h2 hn')
    · exact div_le_cdiv _ hd (by push_cast; exact mul_le_mul_of_nonpos_right h1 hn')

theorem enc_divN {S : ℚ} {I : Iv} {x : ℚ} (h : Enc S I x) {m : ℕ} (hm : 0 < m) :
    Enc S (divN I m) (x / m) := by
  obtain ⟨h1, h2⟩ := h
  have e : x / m * S = x * S / m := by ring
  refine ⟨?_, ?_⟩ <;> simp only [divN, e]
  · exact fdiv_le_div _ hm h1
  · exact div_le_cdiv _ hm h2

theorem enc_ofQdiv (S : ℕ) (q : ℚ) {m : ℕ} (hm : 0 < m) : Enc (S : ℚ) (ofQdiv S q m) (q / m) := by
  have hd : 0 < q.den * m := Nat.mul_pos q.den_pos hm
  have e : q / m * S = ((q.num * S : ℤ) : ℚ) / ((q.den * m : ℕ) : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den q]
    push_cast
    field_simp
  refine ⟨?_, ?_⟩ <;> simp only [ofQdiv, e]
  · exact fdiv_le_div _ hd le_rfl
  · exact div_le_cdiv _ hd le_rfl

theorem enc_ofQ (S : ℕ) (q : ℚ) : Enc (S : ℚ) (ofQ S q) q := by
  unfold ofQ
  simpa using enc_ofQdiv S q (m := 1) one_pos

theorem enc_sq {S : ℚ} {I : Iv} {x : ℚ} (h : Enc S I x) : Enc (S * S) (sq I) (x ^ 2) := by
  obtain ⟨h1, h2⟩ := h
  have e : x ^ 2 * (S * S) = (x * S) * (x * S) := by ring
  set y := x * S
  rw [Enc, e]
  refine ⟨?_, ?_⟩
  · simp only [sq, sqLo]
    split_ifs with ha hb
    · have ha' : (0 : ℚ) < I.lo := by exact_mod_cast ha
      push_cast; nlinarith
    · have hb' : (I.hi : ℚ) < 0 := by exact_mod_cast hb
      push_cast; nlinarith
    · push_cast; nlinarith
  · simp only [sq, sqHi]
    push_cast
    rcases le_total 0 y with hy | hy
    · exact le_max_of_le_right (by nlinarith)
    · exact le_max_of_le_left (by nlinarith)

/-! ### Rational bounds from an enclosure -/

theorem le_of_enc {T : ℕ} (hT : 0 < T) {I : Iv} {x : ℚ} (h : Enc (T : ℚ) I x) (L : ℚ)
    (hc : L.num * (T : ℤ) ≤ I.lo * L.den) : L ≤ x := by
  have hT' : (0 : ℚ) < T := by exact_mod_cast hT
  have hd : (0 : ℚ) < L.den := by exact_mod_cast L.den_pos
  have hc' : (L.num : ℚ) * T ≤ (I.lo : ℚ) * L.den := by exact_mod_cast hc
  have e : L * T = L.num * T / L.den := by
    conv_lhs => rw [← Rat.num_div_den L]
    ring
  have hL : L * T ≤ I.lo := by
    rw [e, div_le_iff₀ hd]
    linarith
  exact le_of_mul_le_mul_right (hL.trans h.1) hT'

theorem le_of_enc' {T : ℕ} (hT : 0 < T) {I : Iv} {x : ℚ} (h : Enc (T : ℚ) I x) (U : ℚ)
    (hc : I.hi * U.den ≤ U.num * (T : ℤ)) : x ≤ U := by
  have hT' : (0 : ℚ) < T := by exact_mod_cast hT
  have hd : (0 : ℚ) < U.den := by exact_mod_cast U.den_pos
  have hc' : (I.hi : ℚ) * U.den ≤ (U.num : ℚ) * T := by exact_mod_cast hc
  have e : U * T = U.num * T / U.den := by
    conv_lhs => rw [← Rat.num_div_den U]
    ring
  have hU : (I.hi : ℚ) ≤ U * T := by
    rw [e, le_div_iff₀ hd]
    linarith
  exact le_of_mul_le_mul_right (h.2.trans hU) hT'

/-! ### Sequences with pole tails -/

/-- `Σ_i c_i z_i^k` for poles `(z_i, c_i)`. -/
def pv (ps : List (ℚ × ℚ)) (k : ℕ) : ℚ := (ps.map fun p => p.2 * p.1 ^ k).sum

/-- `u_k = g_k + Σ_i c_i z_i^(k+1)`. -/
def useq (g : List ℚ) (ps : List (ℚ × ℚ)) (k : ℕ) : ℚ := g.getD k 0 + pv ps (k + 1)

def initIv (S : ℕ) (ps : List (ℚ × ℚ)) : List Iv := ps.map fun p => ofQ S (p.2 * p.1)

def stepIv : List (ℚ × ℚ) → List Iv → List Iv
  | p :: ps, I :: Is => mulC I p.1 :: stepIv ps Is
  | _, _ => []

/-- The pole states at index `k` enclose `c_i z_i^(k+1)`. -/
def PolesEnc (S : ℚ) (ps : List (ℚ × ℚ)) (k : ℕ) (Is : List Iv) : Prop :=
  List.Forall₂ (fun I p => Enc S I (p.2 * p.1 ^ (k + 1))) Is ps

theorem polesEnc_init (S : ℕ) : ∀ ps : List (ℚ × ℚ), PolesEnc (S : ℚ) ps 0 (initIv S ps)
  | [] => List.Forall₂.nil
  | p :: ps => List.Forall₂.cons (by simpa using enc_ofQ S (p.2 * p.1)) (polesEnc_init S ps)

theorem polesEnc_step {S : ℚ} {k : ℕ} : ∀ {ps : List (ℚ × ℚ)} {Is : List Iv},
    PolesEnc S ps k Is → PolesEnc S ps (k + 1) (stepIv ps Is)
  | [], [], _ => List.Forall₂.nil
  | p :: ps, I :: Is, List.Forall₂.cons h hs => by
    refine List.Forall₂.cons ?_ (polesEnc_step hs)
    have e : p.2 * p.1 ^ (k + 1 + 1) = p.2 * p.1 ^ (k + 1) * p.1 := by ring
    rw [e]
    exact enc_mulC h p.1

theorem polesEnc_sum {S : ℚ} {k : ℕ} : ∀ {ps : List (ℚ × ℚ)} {Is : List Iv},
    PolesEnc S ps k Is → Enc S (sumIv Is) (pv ps (k + 1))
  | [], [], _ => by simpa [pv, sumIv] using enc_zero S
  | p :: ps, I :: Is, List.Forall₂.cons h hs => by
    have e : pv (p :: ps) (k + 1) = p.2 * p.1 ^ (k + 1) + pv ps (k + 1) := by simp [pv]
    rw [e]
    exact enc_add h (polesEnc_sum hs)

theorem headD_drop : ∀ (l : List ℚ) (k : ℕ), (l.drop k).headD 0 = l.getD k 0
  | [], k => by simp
  | a :: l, 0 => by simp
  | a :: l, k + 1 => by simp

/-- `acc + Σ_{j<n} φ_{k+j}(u_{k+j})`, with the finite part `g` consumed from the front. -/
def seqLoop (S : ℕ) (ps : List (ℚ × ℚ)) (φ : ℕ → Iv → Iv) :
    ℕ → ℕ → List ℚ → List Iv → Iv → Iv
  | 0, _, _, _, acc => acc
  | n + 1, k, g, Is, acc =>
    seqLoop S ps φ n (k + 1) g.tail (stepIv ps Is) (add acc (φ k (add (ofQ S (g.headD 0)) (sumIv Is))))

theorem sum_shift (f : ℕ → ℚ) (k n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), f (k + j) = f k + ∑ j ∈ Finset.range n, f (k + 1 + j) := by
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show k + (j + 1) = k + 1 + j by omega]

theorem seqLoop_enc {S : ℕ} {S' : ℚ} (ps : List (ℚ × ℚ)) (φ : ℕ → Iv → Iv) (ψ : ℕ → ℚ → ℚ)
    (hφ : ∀ k I x, Enc (S : ℚ) I x → Enc S' (φ k I) (ψ k x)) (g : List ℚ) :
    ∀ (n k : ℕ) (Is : List Iv) (acc : Iv) (a : ℚ), PolesEnc (S : ℚ) ps k Is → Enc S' acc a →
      Enc S' (seqLoop S ps φ n k (g.drop k) Is acc)
        (a + ∑ j ∈ Finset.range n, ψ (k + j) (useq g ps (k + j)))
  | 0, k, Is, acc, a, _, hacc => by simpa [seqLoop] using hacc
  | n + 1, k, Is, acc, a, hI, hacc => by
    have hD : Enc (S : ℚ) (add (ofQ S ((g.drop k).headD 0)) (sumIv Is)) (useq g ps k) := by
      rw [headD_drop]
      exact enc_add (enc_ofQ S _) (polesEnc_sum hI)
    have h := seqLoop_enc ps φ ψ hφ g n (k + 1) (stepIv ps Is) _ _ (polesEnc_step hI)
      (enc_add hacc (hφ k _ _ hD))
    simp only [seqLoop]
    rw [List.tail_drop, sum_shift (fun j => ψ j (useq g ps j)) k n, ← add_assoc]
    exact h

/-! ### Stateless terms and moments -/

/-- `acc + Σ_{j<n} φ_{k+j}(T_{k+j})`. -/
def momLoop (φ : ℕ → Iv → Iv) (T : ℕ → Iv) : ℕ → ℕ → Iv → Iv
  | 0, _, acc => acc
  | n + 1, k, acc => momLoop φ T n (k + 1) (add acc (φ k (T k)))

theorem momLoop_enc {S S' : ℚ} (φ : ℕ → Iv → Iv) (ψ : ℕ → ℚ → ℚ)
    (hφ : ∀ k I x, Enc S I x → Enc S' (φ k I) (ψ k x)) (T : ℕ → Iv) (v : ℕ → ℚ)
    (hT : ∀ k, Enc S (T k) (v k)) :
    ∀ (n k : ℕ) (acc : Iv) (a : ℚ), Enc S' acc a →
      Enc S' (momLoop φ T n k acc) (a + ∑ j ∈ Finset.range n, ψ (k + j) (v (k + j)))
  | 0, k, acc, a, hacc => by simpa [momLoop] using hacc
  | n + 1, k, acc, a, hacc => by
    have h := momLoop_enc φ ψ hφ T v hT n (k + 1) _ _ (enc_add hacc (hφ k _ _ (hT k)))
    simp only [momLoop]
    rw [sum_shift (fun j => ψ j (v j)) k n, ← add_assoc]
    exact h

/-- `Σ_j p_j / (m + j)`. -/
def mom1 : List ℚ → ℕ → ℚ
  | [], _ => 0
  | x :: xs, m => x / (m : ℚ) + mom1 xs (m + 1)

def momIv (S : ℕ) : List ℚ → ℕ → Iv
  | [], _ => zero
  | x :: xs, m => add (ofQdiv S x m) (momIv S xs (m + 1))

theorem enc_momIv (S : ℕ) : ∀ (l : List ℚ) {m : ℕ}, 0 < m → Enc (S : ℚ) (momIv S l m) (mom1 l m)
  | [], m, _ => by simpa [momIv, mom1] using enc_zero (S : ℚ)
  | x :: xs, m, hm => by
    simp only [momIv, mom1]
    exact enc_add (enc_ofQdiv S x hm) (enc_momIv S xs (Nat.succ_pos m))

/-- `−b`, entrywise. -/
def negL : List ℚ → List ℚ
  | [] => []
  | b :: bs => -b :: negL bs

/-- The padded difference of two lists, structural in the first list (the kernel does not unfold
well-founded recursion). -/
def dl : List ℚ → List ℚ → List ℚ
  | [], bs => negL bs
  | a :: as, [] => a :: dl as []
  | a :: as, b :: bs => (a - b) :: dl as bs

theorem negL_getD : ∀ (bs : List ℚ) (k : ℕ), (negL bs).getD k 0 = -bs.getD k 0
  | [], k => by simp [negL]
  | b :: bs, 0 => by simp [negL]
  | b :: bs, k + 1 => by simpa [negL] using negL_getD bs k

theorem dl_getD : ∀ (a b : List ℚ) (k : ℕ), (dl a b).getD k 0 = a.getD k 0 - b.getD k 0
  | [], ys, k => by simp only [dl, negL_getD]; simp
  | x :: xs, [], 0 => by simp [dl]
  | x :: xs, [], k + 1 => by simpa [dl] using dl_getD xs [] k
  | x :: xs, y :: ys, 0 => by simp [dl]
  | x :: xs, y :: ys, k + 1 => by simpa [dl] using dl_getD xs ys k

theorem mom1_negL : ∀ (bs : List ℚ) (m : ℕ), mom1 (negL bs) m = -mom1 bs m
  | [], m => by simp [negL, mom1]
  | b :: bs, m => by simp only [negL, mom1, mom1_negL bs (m + 1)]; ring

theorem mom1_dl : ∀ (a b : List ℚ) (m : ℕ), mom1 (dl a b) m = mom1 a m - mom1 b m
  | [], ys, m => by simp only [dl, mom1_negL]; simp [mom1]
  | x :: xs, [], m => by simp [dl, mom1, mom1_dl xs [] (m + 1)]
  | x :: xs, y :: ys, m => by simp only [dl, mom1, mom1_dl xs ys (m + 1)]; ring

/-- `φ_k(I) = I² / (k + 1)`: the weighted square of the norms. -/
def sqDiv (k : ℕ) (I : Iv) : Iv := divN (sq I) (k + 1)

theorem enc_sqDiv {S : ℚ} (k : ℕ) (I : Iv) (x : ℚ) (h : Enc S I x) :
    Enc (S * S) (sqDiv k I) (x ^ 2 / ((k : ℚ) + 1)) := by
  have := enc_divN (enc_sq h) (Nat.succ_pos k)
  simpa [sqDiv] using this

/-- The scale `3⁸¹` (odd, so scaled literals do not share their low 64 bits). -/
def ivS : ℕ := 443426488243037769948249630619149892803

theorem ivS_pos : 0 < ivS := by decide

theorem ivS2_cast : ((ivS * ivS : ℕ) : ℚ) = (ivS : ℚ) * (ivS : ℚ) := by push_cast; ring

end CatalanMeasure.Cert.Iv
