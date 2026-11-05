module

public import Submission.CatalanMeasure.GenD.ResRec

@[expose] public section

/-!
# Nat-level checkers for the residue tables (generic)

Every check is a `Bool` computed from small natural numbers (kernel-friendly); each soundness
lemma turns `check = true` into the `ZMod ℓ` statements consumed by `ResRec` and `CertMod`.
-/

namespace CatalanMeasure.GenD
namespace ResCheck

open OAI.InternalCatalan CatalanMeasure.Parametric ResRec

def allLt (n : ℕ) (f : ℕ → Bool) : Bool := (List.range n).all f

theorem allLt_spec {n : ℕ} {f : ℕ → Bool} (h : allLt n f = true) :
    ∀ i, i < n → f i = true := by
  intro i hi
  unfold allLt at h
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

theorem or_ble {B x : ℕ} {c : Bool} (h : (Nat.ble B x || c) = true) (hx : x < B) : c = true := by
  simp only [Bool.or_eq_true, Nat.ble_eq] at h
  rcases h with h | h
  · omega
  · exact h

theorem or_ble2 {B x B' y : ℕ} {c : Bool} (h : (Nat.ble B x || Nat.ble B' y || c) = true)
    (hx : x < B) (hy : y < B') : c = true := by
  simp only [Bool.or_eq_true, Nat.ble_eq] at h
  rcases h with (h | h) | h
  · omega
  · omega
  · exact h

variable {l : ℕ}

theorem modc {a b : ℕ} (h : (a % l == b % l) = true) : (a : ZMod l) = (b : ZMod l) :=
  cast_eq_of_modeq h

/-! ## checks for `ResRec` -/

def chkIV (l N : ℕ) (IV : List ℕ) : Bool :=
  allLt N fun n => (n == 0) || ((n * tl IV n) % l == 1 % l)

theorem chkIV_sound {N : ℕ} {IV : List ℕ} (h : chkIV l N IV = true) :
    ∀ n, 0 < n → n < N → ((n * tl IV n : ℕ) : ZMod l) = 1 := by
  intro n h0 hn
  have := allLt_spec h n hn
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with h1 | h1
  · omega
  · have := modc (l := l) (a := n * tl IV n) (b := 1) (by simpa using h1)
    simpa using this

def chkMS (l N : ℕ) (MS : List ℕ) : Bool :=
  (tl MS 0 % l == 2 % l) &&
  allLt N (fun i => (i % 2 != 1) || (tl MS i % l == 0 % l)) &&
  allLt N (fun m => Nat.ble N (2 * m + 2) ||
    (((2 * m + 3) * tl MS (2 * m + 2)) % l == ((2 * m + 2) * tl MS (2 * m)) % l))

theorem chkMS_sound [Fact l.Prime] {N : ℕ} (hN : N + 2 < l) {MS : List ℕ}
    (h : chkMS l N MS = true) :
    ∀ i, i < N → Gd l (momentScalar i) (tl MS i : ZMod l) := by
  simp only [chkMS, Bool.and_eq_true] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  refine ms_sound N hN MS ?_ ?_ ?_
  · have := modc (l := l) (a := tl MS 0) (b := 2) (by simpa using h0)
    simpa using this
  · intro i hi hi2
    have := allLt_spec h1 i hi
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at this
    rcases this with h | h
    · omega
    · have := modc (l := l) (a := tl MS i) (b := 0) (by simpa using h)
      simpa using this
  · intro m hm
    have := or_ble (allLt_spec h2 m (by omega)) hm
    exact modc this

def chkBM (l N : ℕ) (MS BM : List ℕ) : Bool :=
  (tl BM 0 % l == 0 % l) && (tl BM 1 % l == 2 % l) &&
  allLt N (fun d => Nat.ble N (d + 2) ||
    (((d + 2) * tl BM (d + 2)) % l == ((d + 1) * tl BM d + tl MS d + tl MS (d + 1)) % l))

theorem chkBM_sound [Fact l.Prime] {N : ℕ} (hN : N + 2 < l) {MS BM : List ℕ}
    (hms : ∀ i, i < N → Gd l (momentScalar i) (tl MS i : ZMod l))
    (h : chkBM l N MS BM = true) :
    ∀ d, d < N → Gd l (boundaryMinus d) (tl BM d : ZMod l) := by
  simp only [chkBM, Bool.and_eq_true] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  refine bm_sound N hN MS BM hms ?_ ?_ ?_
  · have := modc (l := l) (a := tl BM 0) (b := 0) (by simpa using h0)
    simpa using this
  · have := modc (l := l) (a := tl BM 1) (b := 2) (by simpa using h1)
    simpa using this
  · intro d hd
    exact modc (or_ble (allLt_spec h2 d (by omega)) hd)

def chkBP (l N : ℕ) (BP IV : List ℕ) : Bool :=
  (tl BP 0 % l == 0 % l) && (tl BP 1 % l == 0 % l) &&
  allLt N (fun d => Nat.ble N (d + 2) ||
    (((d + 1) * tl BP (d + 2)) % l == (d * tl BP d + 2 * tl IV (d + 1)) % l))

theorem chkBP_sound [Fact l.Prime] {N : ℕ} (hN : N + 2 < l) {BP IV : List ℕ}
    (hIV : ∀ n, 0 < n → n < N → ((n * tl IV n : ℕ) : ZMod l) = 1)
    (h : chkBP l N BP IV = true) :
    ∀ d, d < N → Gd l (boundaryPlus d) (tl BP d : ZMod l) := by
  simp only [chkBP, Bool.and_eq_true] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  refine bp_sound N hN BP IV hIV ?_ ?_ ?_
  · have := modc (l := l) (a := tl BP 0) (b := 0) (by simpa using h0)
    simpa using this
  · have := modc (l := l) (a := tl BP 1) (b := 0) (by simpa using h1)
    simpa using this
  · intro d hd
    exact modc (or_ble (allLt_spec h2 d (by omega)) hd)

def chkH1 (l N : ℕ) (H1 IV : List ℕ) : Bool :=
  (tl H1 0 % l == 0 % l) &&
  allLt N (fun n => (tl H1 (n + 1)) % l == (tl H1 n + tl IV (n + 1)) % l)

theorem chkH1_sound [Fact l.Prime] {N : ℕ} (hN : N < l) {H1 IV : List ℕ}
    (hIV : ∀ n, 0 < n → n < N + 1 → ((n * tl IV n : ℕ) : ZMod l) = 1)
    (h : chkH1 l N H1 IV = true) :
    ∀ n, n < N + 1 → Gd l (harmonicRat 1 n) (tl H1 n : ZMod l) := by
  simp only [chkH1, Bool.and_eq_true] at h
  obtain ⟨h0, h1⟩ := h
  refine h1_sound N hN H1 IV hIV ?_ ?_
  · have := modc (l := l) (a := tl H1 0) (b := 0) (by simpa using h0)
    simpa using this
  · intro n hn
    exact modc (allLt_spec h1 n (by omega))

def chkMT (l H L : ℕ) (MS BM BP IV : List ℕ) (MT : List (List ℕ)) : Bool :=
  allLt H (fun i => tg MT i 0 % l == tl BM i % l) &&
  allLt L (fun j => tg MT 0 j % l == tl BP j % l) &&
  allLt H (fun i => allLt L (fun j => Nat.ble H (i + 1) || Nat.ble L (j + 1) ||
    ((tg MT (i + 1) (j + 1) + tl MS i * tl IV (j + 1)) % l == tg MT i j % l)))

theorem moment_table_sound [Fact l.Prime] (H L : ℕ) (hH : H + 3 < l) (hLH : L ≤ H)
    (MS BM BP IV : List ℕ) (MT : List (List ℕ))
    (cIV : chkIV l (H + 1) IV = true) (cMS : chkMS l H MS = true)
    (cBM : chkBM l H MS BM = true) (cBP : chkBP l L BP IV = true)
    (cMT : chkMT l H L MS BM BP IV MT = true) :
    ∀ i j, i < H → j < L →
      palindromicRatResidue l (momentRat i j) = CertMod.entry l MT i j := by
  have hIV := chkIV_sound cIV
  have hms := chkMS_sound (by omega) cMS
  simp only [chkMT, Bool.and_eq_true] at cMT
  obtain ⟨⟨c1, c2⟩, c3⟩ := cMT
  refine moment_sound H L hH hLH MS BM BP IV MT hms (chkBM_sound (by omega) hms cBM)
    (chkBP_sound (by omega) (fun n h0 hn => hIV n h0 (by omega)) cBP) hIV ?_ ?_ ?_
  · intro i hi; exact modc (allLt_spec c1 i hi)
  · intro j hj; exact modc (allLt_spec c2 j hj)
  · intro i j hi hj
    exact modc (or_ble2 (allLt_spec (allLt_spec c3 i (by omega)) j (by omega)) hi hj)

def chkZT (l H L : ℕ) (H1 IV : List ℕ) (ZT : List (List ℕ)) : Bool :=
  (tg ZT 0 0 % l == 0 % l) &&
  allLt H (fun i => (i == 0) || ((tg ZT i 0 * i) % l == tl H1 i % l)) &&
  allLt L (fun j => tg ZT 0 j % l == tg ZT j 0 % l) &&
  allLt H (fun i => allLt L (fun j => Nat.ble H (i + 1) || Nat.ble L (j + 1) ||
    ((tg ZT (i + 1) (j + 1) + tl IV (i + 1) * tl IV (j + 1)) % l == tg ZT i j % l)))

theorem zeta_table_sound [Fact l.Prime] (H L : ℕ) (hH : H + 3 < l) (hLH : L ≤ H)
    (H1 IV : List ℕ) (ZT : List (List ℕ))
    (cIV : chkIV l (H + 1) IV = true) (cH1 : chkH1 l H H1 IV = true)
    (cZT : chkZT l H L H1 IV ZT = true) :
    ∀ i j, i < H → j < L →
      palindromicRatResidue l (zetaRat i j) = CertMod.entry l ZT i j := by
  have hIV := chkIV_sound cIV
  simp only [chkZT, Bool.and_eq_true] at cZT
  obtain ⟨⟨⟨c0, c1⟩, c2⟩, c3⟩ := cZT
  refine zeta_sound H L hH hLH H1 IV ZT (chkH1_sound (by omega) hIV cH1) hIV ?_ ?_ ?_ ?_
  · have := modc (l := l) (a := tg ZT 0 0) (b := 0) (by simpa using c0)
    simpa using this
  · intro i hi0 hi
    have := allLt_spec c1 i hi
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    rcases this with h | h
    · omega
    · exact modc (by simpa using h)
  · intro j hj; exact modc (allLt_spec c2 j hj)
  · intro i j hi hj
    exact modc (or_ble2 (allLt_spec (allLt_spec c3 i (by omega)) j (by omega)) hi hj)

end ResCheck
end CatalanMeasure.GenD
