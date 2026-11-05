module

public import Submission.CatalanMeasure.CellCert.Scaled
public import Submission.CatalanMeasure.Cert.Norm

/-!
# D2 constants: exact evaluator of `certMean` on a trial `trialSeqS cs tail`

`certMean K G pp = Σ_{k<K} G_k pp_{k+1}` (Phase2Contract) with `G = gcertG e g` and `pp = D0.p =
trialSeqS Pc P` is a finite exact rational.  The pole powers are carried as a state updated once per
index (`polePow`, 75 complex multiplications per step instead of a fresh `cpowQ` per index), the
values are `tailValQ` (`tailValQ_spec`), the finite part is `finCoeffS`.

* `ppTab cs tail n`: the rationals `pp_1 .. pp_n` (`ppTab_getD`).
* `meanGo e 0 g (ppTab cs tail n)`, `n ≥ g.length`: the exact mean (`certMean_eval`); one table
  `ppTab cs tail 60` serves every row.
* `row_ge`, `row_le`: a row that is affine in `alpha` follows from its two interval endpoints.

The statements avoid `certMean` and `gcertG` (they live in Phase2Contract, which this module does not
import): `certMean K G pp` unfolds to the sum below and `gcertG e g k` to the quotient in `hG`, so
callers pass `fun k => rfl`.
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

open Set CatalanMeasure.Cert CatalanMeasure.CellCert

/-! ### The pole-power table -/

/-- One step of every pole power: `w ↦ w * z`. -/
def polePow (tail : List TailQ) (st : List (ℚ × ℚ)) : List (ℚ × ℚ) :=
  List.zipWith (fun t w => cmulQ w (t.zr, t.zi)) tail st

/-- `Re Σ_j r_j w_j` for the pole powers `w_j`. -/
def stVal (tail : List TailQ) (st : List (ℚ × ℚ)) : ℚ :=
  (List.zipWith (fun t w => (cmulQ (t.rr, t.ri) w).1) tail st).sum

def tabAux : ℕ → List TailQ → List (ℚ × ℚ) → List ℚ
  | 0, _, _ => []
  | n + 1, tail, st => stVal tail (polePow tail st) :: tabAux n tail (polePow tail st)

/-- `[tailValQ tail 1, …, tailValQ tail n]`. -/
def tailTab (tail : List TailQ) (n : ℕ) : List ℚ :=
  tabAux n tail (tail.map fun _ => ((1 : ℚ), (0 : ℚ)))

theorem polePow_pow (tail : List TailQ) (k : ℕ) :
    polePow tail (tail.map fun t => cpowQ (t.zr, t.zi) k) =
      tail.map fun t => cpowQ (t.zr, t.zi) (k + 1) := by
  induction tail with
  | nil => rfl
  | cons t tl ih =>
    simp only [polePow, List.map_cons, List.zipWith_cons_cons, cpowQ] at ih ⊢
    rw [ih]

theorem stVal_pow (tail : List TailQ) (k : ℕ) :
    stVal tail (tail.map fun t => cpowQ (t.zr, t.zi) k) = tailValQ tail k := by
  induction tail with
  | nil => rfl
  | cons t tl ih =>
    simp only [stVal, tailValQ, List.map_cons, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [ih]

theorem tabAux_getD (tail : List TailQ) :
    ∀ (n k i : ℕ), i < n →
      (tabAux n tail (tail.map fun t => cpowQ (t.zr, t.zi) k)).getD i 0 = tailValQ tail (k + i + 1)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k, 0, _ => by
    simp only [tabAux, polePow_pow, stVal_pow, List.getD_cons_zero]
  | n + 1, k, i + 1, h => by
    simp only [tabAux, polePow_pow, List.getD_cons_succ]
    rw [tabAux_getD tail n (k + 1) i (by omega)]
    congr 1; omega

theorem tailTab_getD (tail : List TailQ) {n i : ℕ} (h : i < n) :
    (tailTab tail n).getD i 0 = tailValQ tail (i + 1) := by
  have h0 : (tail.map fun _ => ((1 : ℚ), (0 : ℚ))) = tail.map fun t => cpowQ (t.zr, t.zi) 0 := rfl
  unfold tailTab
  rw [h0, tabAux_getD tail n 0 i h, Nat.zero_add]

/-- Add the finite part `cs_k / 2^40` to the tail values. -/
def addFin : List ℤ → List ℚ → List ℚ
  | [], vs => vs
  | _ :: _, [] => []
  | c :: cs, v :: vs => ((c : ℚ) / 1099511627776 + v) :: addFin cs vs

theorem addFin_getD : ∀ (cs : List ℤ) (vs : List ℚ) (i : ℕ), i < vs.length →
    (addFin cs vs).getD i 0 = ((cs.getD i 0 : ℤ) : ℚ) / 1099511627776 + vs.getD i 0
  | [], vs, i, _ => by simp [addFin]
  | _ :: _, [], i, h => absurd h (by simp)
  | c :: cs, v :: vs, 0, _ => by simp [addFin]
  | c :: cs, v :: vs, i + 1, h => by
    simp only [addFin, List.getD_cons_succ]
    exact addFin_getD cs vs i (by simpa using h)

/-- `[pp_1, …, pp_n]` for `pp = trialSeqS cs tail`. -/
def ppTab (cs : List ℤ) (tail : List TailQ) (n : ℕ) : List ℚ := addFin cs (tailTab tail n)

theorem tailTab_length (tail : List TailQ) (n : ℕ) : (tailTab tail n).length = n := by
  have : ∀ (n : ℕ) (st : List (ℚ × ℚ)), (tabAux n tail st).length = n := by
    intro n
    induction n with
    | zero => intro st; rfl
    | succ n ih => intro st; simp [tabAux, ih]
  exact this n _

theorem trialSeqS_succ_eq (cs : List ℤ) (tail : List TailQ) (k : ℕ) :
    trialSeqS cs tail (k + 1) =
      (((cs.getD k 0 : ℤ) : ℚ) / 1099511627776 + tailValQ tail (k + 1) : ℚ) := by
  unfold trialSeqS
  rw [if_neg (Nat.succ_ne_zero k), finCoeffS_succ, ← tailValQ_spec]
  push_cast
  rfl

theorem ppTab_getD (cs : List ℤ) (tail : List TailQ) {n k : ℕ} (hk : k < n) :
    (((ppTab cs tail n).getD k 0 : ℚ) : ℝ) = trialSeqS cs tail (k + 1) := by
  unfold ppTab
  rw [addFin_getD cs _ k (by rw [tailTab_length]; exact hk), tailTab_getD tail hk,
    trialSeqS_succ_eq]

/-! ### The exact mean -/

/-- `Σ_i g_i / (1-e)^(k+i+1) * pp_i`. -/
def meanGo (e : ℚ) : ℕ → List ℚ → List ℚ → ℚ
  | _, [], _ => 0
  | k, x :: g, pp => x / (1 - e) ^ (k + 1) * pp.headD 0 + meanGo e (k + 1) g pp.tail

theorem meanGo_eq (e : ℚ) : ∀ (g pp : List ℚ) (k : ℕ),
    meanGo e k g pp = ∑ i ∈ Finset.range g.length, g.getD i 0 / (1 - e) ^ (k + i + 1) * pp.getD i 0
  | [], pp, k => by simp [meanGo]
  | x :: g, pp, k => by
    rw [meanGo, meanGo_eq e g pp.tail (k + 1), List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, add_zero]
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      cases pp with
      | nil => simp
      | cons y ys => simp only [List.tail_cons, List.getD_cons_succ]; congr 3; omega
    · cases pp <;> simp

/-- **The evaluator.**  For `G_k = g_k / (1-e)^(k+1)` and `pp = trialSeqS cs tail`:
`Σ_{k<|g|} G_k pp_{k+1} = meanGo e 0 g (ppTab cs tail n)` for every `n ≥ |g|`, an exact rational. -/
theorem certMean_eval (e : ℚ) (g : List ℚ) (cs : List ℤ) (tail : List TailQ) {n : ℕ}
    (hn : g.length ≤ n) {eR : ℝ} (he : eR = (e : ℝ)) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((g.getD k 0 : ℚ) : ℝ) / (1 - eR) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS cs tail k) :
    ∑ k ∈ Finset.range g.length, G k * pp (k + 1) =
      ((meanGo e 0 g (ppTab cs tail n) : ℚ) : ℝ) := by
  rw [meanGo_eq]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < g.length := Finset.mem_range.mp hk
  rw [hG, hpp, ppTab_getD cs tail (lt_of_lt_of_le hk' hn), he]
  simp

/-! ### Rows that are affine in `alpha` -/

theorem aff_le {A B κ lo hi α : ℝ} (hlo : lo ≤ α) (hhi : α ≤ hi)
    (h1 : A * lo + B ≤ κ) (h2 : A * hi + B ≤ κ) : A * α + B ≤ κ := by
  rcases le_total 0 A with hA | hA
  · nlinarith [mul_nonneg hA (sub_nonneg.2 hhi)]
  · nlinarith [mul_nonneg (neg_nonneg.2 hA) (sub_nonneg.2 hlo)]

theorem aff_ge {A B κ lo hi α : ℝ} (hlo : lo ≤ α) (hhi : α ≤ hi)
    (h1 : κ ≤ A * lo + B) (h2 : κ ≤ A * hi + B) : κ ≤ A * α + B := by
  rcases le_total 0 A with hA | hA
  · nlinarith [mul_nonneg hA (sub_nonneg.2 hlo)]
  · nlinarith [mul_nonneg (neg_nonneg.2 hA) (sub_nonneg.2 hhi)]

/-- `κ ≤ (1-α) c0 + mean - s` on `[lo, hi]` from the two endpoints, the mean being the exact
rational `m = meanGo …` (a `def` evaluated once by the kernel and shared by all endpoint checks). -/
theorem row_ge (e : ℚ) (g : List ℚ) (cs : List ℤ) (tail : List TailQ) (c0 s κ lo hi m : ℚ)
    {n : ℕ} (hn : g.length ≤ n) (hm : m = meanGo e 0 g (ppTab cs tail n))
    (hend : κ ≤ (1 - lo) * c0 + m - s ∧ κ ≤ (1 - hi) * c0 + m - s)
    {eR : ℝ} (he : eR = (e : ℝ)) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((g.getD k 0 : ℚ) : ℝ) / (1 - eR) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS cs tail k) {α : ℝ} (hα : α ∈ Icc (lo : ℝ) hi) :
    (κ : ℝ) ≤ (1 - α) * (c0 : ℝ) + ∑ k ∈ Finset.range g.length, G k * pp (k + 1) - (s : ℝ) := by
  rw [certMean_eval e g cs tail hn he hG hpp, ← hm]
  obtain ⟨h1, h2⟩ := hend
  have h1' : (κ : ℝ) ≤ (1 - (lo : ℝ)) * (c0 : ℝ) + (m : ℝ) - (s : ℝ) := by exact_mod_cast h1
  have h2' : (κ : ℝ) ≤ (1 - (hi : ℝ)) * (c0 : ℝ) + (m : ℝ) - (s : ℝ) := by exact_mod_cast h2
  have := aff_ge (A := -(c0 : ℝ)) (B := (c0 : ℝ) + (m : ℝ) - (s : ℝ)) (κ := (κ : ℝ))
    hα.1 hα.2 (by linarith) (by linarith)
  linarith

/-- `(1-α) - ((1-α) c0 + mean - s) ≤ κ` on `[lo, hi]` from the two endpoints (the field `hκhi`). -/
theorem row_le (e : ℚ) (g : List ℚ) (cs : List ℤ) (tail : List TailQ) (c0 s κ lo hi m : ℚ)
    {n : ℕ} (hn : g.length ≤ n) (hm : m = meanGo e 0 g (ppTab cs tail n))
    (hend : (1 - lo) - ((1 - lo) * c0 + m - s) ≤ κ ∧ (1 - hi) - ((1 - hi) * c0 + m - s) ≤ κ)
    {eR : ℝ} (he : eR = (e : ℝ)) {G pp : ℕ → ℝ}
    (hG : ∀ k, G k = ((g.getD k 0 : ℚ) : ℝ) / (1 - eR) ^ (k + 1))
    (hpp : ∀ k, pp k = trialSeqS cs tail k) {α : ℝ} (hα : α ∈ Icc (lo : ℝ) hi) :
    (1 - α) - ((1 - α) * (c0 : ℝ) + ∑ k ∈ Finset.range g.length, G k * pp (k + 1) - (s : ℝ)) ≤ κ := by
  rw [certMean_eval e g cs tail hn he hG hpp, ← hm]
  obtain ⟨h1, h2⟩ := hend
  have h1' : (1 - (lo : ℝ)) - ((1 - (lo : ℝ)) * (c0 : ℝ) + (m : ℝ) - (s : ℝ)) ≤ (κ : ℝ) := by
    exact_mod_cast h1
  have h2' : (1 - (hi : ℝ)) - ((1 - (hi : ℝ)) * (c0 : ℝ) + (m : ℝ) - (s : ℝ)) ≤ (κ : ℝ) := by
    exact_mod_cast h2
  have := aff_le (A := (c0 : ℝ) - 1) (B := 1 - (c0 : ℝ) - (m : ℝ) + (s : ℝ)) (κ := (κ : ℝ))
    hα.1 hα.2 (by linarith) (by linarith)
  linarith

end CatalanMeasure.Signed.Consts

#print axioms CatalanMeasure.Signed.Consts.certMean_eval
#print axioms CatalanMeasure.Signed.Consts.row_ge
#print axioms CatalanMeasure.Signed.Consts.row_le
