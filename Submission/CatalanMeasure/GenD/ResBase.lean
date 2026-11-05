module

public import Submission.CatalanMeasure.GenD.ResCheck

@[expose] public section

/-!
# From residue tables to the C3 certificate (generic)

Dot products of residue lists, the polynomial-row check against `intRowP`/`intRowD`, the filtered
tables, the base-row check, and the row-by-row inverse check, each with its soundness lemma;
`c3_of_tables` assembles the three determinant statements.
-/

namespace CatalanMeasure.GenD
namespace ResBase

open OAI.InternalCatalan CatalanMeasure.Parametric ResRec ResCheck

variable {l : ℕ}

def sumR (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumR f n + f n

theorem sumR_cast {R : Type*} [CommSemiring R] (f : ℕ → ℕ) (n : ℕ) :
    ((sumR f n : ℕ) : R) = ∑ i ∈ Finset.range n, (f i : R) := by
  induction n with
  | zero => simp [sumR]
  | succ n ih => simp [sumR, Finset.sum_range_succ, ih]

def dotN : List ℕ → List ℕ → ℕ
  | a :: as, b :: bs => a * b + dotN as bs
  | _, _ => 0

theorem dotN_cast {R : Type*} [CommSemiring R] (as bs : List ℕ) (n : ℕ)
    (h1 : as.length = n) (h2 : bs.length = n) :
    ((dotN as bs : ℕ) : R) = ∑ j ∈ Finset.range n, (nth as j : R) * (nth bs j : R) := by
  induction as generalizing bs n with
  | nil =>
    simp only [List.length_nil] at h1; subst h1
    cases bs with
    | nil => simp [dotN]
    | cons b bs => simp at h2
  | cons a as ih =>
    cases bs with
    | nil => simp at h2; subst h2; simp at h1
    | cons b bs =>
      simp only [List.length_cons] at h1 h2
      subst h1
      have h2' : bs.length = as.length := by omega
      rw [Finset.sum_range_succ']
      have := ih bs as.length rfl h2'
      simp only [dotN, nth, Nat.cast_add, Nat.cast_mul, this]
      ring

def dotS (s : ℕ) : List ℕ → List ℕ → List ℕ → ℕ
  | a :: as, b :: bs, c :: cs => (a + s * b) * c + dotS s as bs cs
  | _, _, _ => 0

theorem dotS_cast {R : Type*} [CommSemiring R] (s : ℕ) (as bs cs : List ℕ) (n : ℕ)
    (h1 : as.length = n) (h2 : bs.length = n) (h3 : cs.length = n) :
    ((dotS s as bs cs : ℕ) : R) =
      ∑ j ∈ Finset.range n, ((nth as j : R) + (s : R) * (nth bs j : R)) * (nth cs j : R) := by
  induction as generalizing bs cs n with
  | nil =>
    simp only [List.length_nil] at h1; subst h1
    cases bs with
    | nil => cases cs with
      | nil => simp [dotS]
      | cons c cs => simp at h3
    | cons b bs => simp at h2
  | cons a as ih =>
    cases bs with
    | nil => simp at h2; subst h2; simp at h1
    | cons b bs =>
      cases cs with
      | nil => simp at h3; subst h3; simp at h1
      | cons c cs =>
        simp only [List.length_cons] at h1 h2 h3
        subst h1
        have h2' : bs.length = as.length := by omega
        have h3' : cs.length = as.length := by omega
        rw [Finset.sum_range_succ']
        have := ih bs cs as.length rfl h2' h3'
        simp only [dotS, nth, Nat.cast_add, Nat.cast_mul, this]
        ring

/-! ### Integer lists against residues -/

def zerosR (l : ℕ) : List ℕ → Bool
  | [] => true
  | b :: bs => ((0 : ℤ) % (l : ℤ) == (b : ℤ) % (l : ℤ)) && zerosR l bs

def zerosL (l : ℕ) : List ℤ → Bool
  | [] => true
  | a :: as => (a % (l : ℤ) == (0 : ℤ) % (l : ℤ)) && zerosL l as

/-- Structural in the first list (kernel-friendly). -/
def modEqL (l : ℕ) : List ℤ → List ℕ → Bool
  | [], R => zerosR l R
  | a :: as, [] => (a % (l : ℤ) == (0 : ℤ) % (l : ℤ)) && zerosL l as
  | a :: as, b :: bs => (a % (l : ℤ) == (b : ℤ) % (l : ℤ)) && modEqL l as bs

theorem intmod {a b : ℤ} (h : (a % (l : ℤ) == b % (l : ℤ)) = true) :
    (a : ZMod l) = (b : ZMod l) := by
  have h' : a % (l : ℤ) = b % (l : ℤ) := by simpa using h
  rw [← ZMod.intCast_mod a l, ← ZMod.intCast_mod b l, h']

theorem zerosR_sound : ∀ (R : List ℕ), zerosR l R = true → ∀ u, (0 : ZMod l) = (nth R u : ZMod l) := by
  intro R
  induction R with
  | nil => intro _ u; simp [nth]
  | cons b bs ih =>
    intro h u
    simp only [zerosR, Bool.and_eq_true] at h
    cases u with
    | zero => simpa [nth] using (intmod h.1)
    | succ u => simpa [nth] using ih h.2 u

theorem zerosL_sound : ∀ (L : List ℤ), zerosL l L = true → ∀ u, ((L.getD u 0 : ℤ) : ZMod l) = 0 := by
  intro L
  induction L with
  | nil => intro _ u; simp
  | cons a as ih =>
    intro h u
    simp only [zerosL, Bool.and_eq_true] at h
    cases u with
    | zero => simpa using (intmod h.1)
    | succ u => simpa using ih h.2 u

theorem modEqL_sound : ∀ (L : List ℤ) (R : List ℕ), modEqL l L R = true →
    ∀ u, ((L.getD u 0 : ℤ) : ZMod l) = (nth R u : ZMod l) := by
  intro L
  induction L with
  | nil =>
    intro R h u
    simpa using (zerosR_sound R h u)
  | cons a as ih =>
    intro R
    cases R with
    | nil =>
      intro h u
      simp only [modEqL, Bool.and_eq_true] at h
      cases u with
      | zero => simpa [nth] using (intmod h.1)
      | succ u => simpa [nth] using zerosL_sound as h.2 u
    | cons b bs =>
      intro h u
      simp only [modEqL, Bool.and_eq_true] at h
      cases u with
      | zero => simpa [nth] using (intmod h.1)
      | succ u => simpa [nth] using ih bs h.2 u

def chkPoly (P : Parameters) (l : ℕ) (PR DR : List (List ℕ)) : Bool :=
  allLt (P.n0 + 1) fun r => modEqL l (intRowP P 1 r) (nthL PR r) && modEqL l (intRowD P 1 r) (nthL DR r)

/-! ### Filtered tables -/

def chkF (l q0 b0 n0 H1 : ℕ) (W : List ℕ) (MT FMt : List (List ℕ)) : Bool :=
  allLt n0 fun k => allLt H1 fun u =>
    tg FMt k u % l == (sumR (fun v => nth W v * tg MT u (b0 + k + v)) (q0 + 1)) % l

theorem tg_cast' {n : ℕ} (T : List (List ℕ)) (i j : ℕ) :
    ((tg T i j : ℕ) : ZMod n) = CertMod.entry n T i j := by
  simp [tg, CertMod.entry, nth_eq, nthL_eq]

theorem chkF_sound {q0 b0 n0 H1 : ℕ} {W : List ℕ} {MT FMt : List (List ℕ)}
    (h : chkF l q0 b0 n0 H1 W MT FMt = true) :
    ∀ k, k < n0 → ∀ u, u < H1 → (tg FMt k u : ZMod l) =
      ∑ v ∈ Finset.range (q0 + 1), (nth W v : ZMod l) * CertMod.entry l MT u (b0 + k + v) := by
  intro k hk u hu
  have := modc (allLt_spec (allLt_spec h k hk) u hu)
  rw [this, sumR_cast]
  simp only [Nat.cast_mul, tg_cast']

def chkLen (n0 H1 : ℕ) (PR DR FMt FZt : List (List ℕ)) : Bool :=
  allLt (n0 + 1) (fun r => (nthL PR r).length == H1 && (nthL DR r).length == H1) &&
  allLt n0 (fun k => (nthL FMt k).length == H1 && (nthL FZt k).length == H1)

def chkBase (l n0 cN : ℕ) (rows PR DR FMt FZt : List (List ℕ)) (r : ℕ) : Bool :=
  allLt n0 fun k =>
    tg rows r k % l ==
      (dotN (nthL PR r) (nthL FMt k) + cN * dotN (nthL DR r) (nthL FZt k)) % l

theorem tab_regroup {R : Type*} [CommRing R] (V U : Finset ℕ) (w : ℕ → R) (P D : ℕ → R)
    (m z : ℕ → ℕ → R) (c : R) :
    ∑ v ∈ V, w v * ((∑ u ∈ U, P u * m u v) - c * ∑ u ∈ U, D u * z u v) =
      ∑ u ∈ U, P u * ∑ v ∈ V, w v * m u v + (-c) * ∑ u ∈ U, D u * ∑ v ∈ V, w v * z u v := by
  have h1 : ∑ v ∈ V, w v * ∑ u ∈ U, P u * m u v = ∑ u ∈ U, P u * ∑ v ∈ V, w v * m u v := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intros; apply Finset.sum_congr rfl; intros; ring
  have h2 : ∑ v ∈ V, w v * ∑ u ∈ U, D u * z u v = ∑ u ∈ U, D u * ∑ v ∈ V, w v * z u v := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intros; apply Finset.sum_congr rfl; intros; ring
  calc ∑ v ∈ V, w v * ((∑ u ∈ U, P u * m u v) - c * ∑ u ∈ U, D u * z u v)
      = (∑ v ∈ V, w v * ∑ u ∈ U, P u * m u v) - c * ∑ v ∈ V, w v * ∑ u ∈ U, D u * z u v := by
        simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl; intros; apply Finset.sum_congr rfl; intros; ring
    _ = _ := by rw [h1, h2]; ring

/-- **Base rows from tables.** -/
theorem base_sound (P : Parameters) (l : ℕ) [Fact l.Prime] (hl2 : l ≠ 2)
    (hH : P.H 1 + 3 < l) (hLH : P.L 1 ≤ P.H 1)
    (MS BM BP IV H1 W : List ℕ) (MT ZT FMt FZt PR DR rows : List (List ℕ)) (cN : ℕ)
    (hW : ∀ v, v < P.q0 + 1 → (nth W v : ZMod l) = baseFilterWeight P l v)
    (hcN : ((2 * cN + 3) % l == 0 % l) = true)
    (cIV : chkIV l (P.H 1 + 1) IV = true) (cMS : chkMS l (P.H 1) MS = true)
    (cBM : chkBM l (P.H 1) MS BM = true) (cBP : chkBP l (P.L 1) BP IV = true)
    (cMT : chkMT l (P.H 1) (P.L 1) MS BM BP IV MT = true)
    (cH1 : chkH1 l (P.H 1) H1 IV = true) (cZT : chkZT l (P.H 1) (P.L 1) H1 IV ZT = true)
    (cPoly : chkPoly P l PR DR = true)
    (cFM : chkF l P.q0 P.b0 P.n0 (P.H 1) W MT FMt = true)
    (cFZ : chkF l P.q0 P.b0 P.n0 (P.H 1) W ZT FZt = true)
    (cLen : chkLen P.n0 (P.H 1) PR DR FMt FZt = true)
    (cBase : ∀ r, r < P.n0 + 1 → chkBase l P.n0 cN rows PR DR FMt FZt r = true) :
    ∀ (r k : ℕ) (hk : k < P.n0), r < P.n0 + 1 →
      baseFilteredContraction P l r ⟨k, hk⟩ = CertMod.entry l rows r k := by
  intro r k hk hr
  have hM := moment_table_sound (P.H 1) (P.L 1) hH hLH MS BM BP IV MT cIV cMS cBM cBP cMT
  have hZ := zeta_table_sound (P.H 1) (P.L 1) hH hLH H1 IV ZT cIV cH1 cZT
  rw [CertMod.baseFilteredContraction_eq_tabEntry P l MT ZT
    (fun u j hu hj => hM u j hu hj) (fun u j hu hj => hZ u j hu hj) r ⟨k, hk⟩]
  have hpoly := allLt_spec cPoly r hr
  simp only [Bool.and_eq_true] at hpoly
  have hP := modEqL_sound _ _ hpoly.1
  have hD := modEqL_sound _ _ hpoly.2
  have hl2' : (2 : ZMod l) ≠ 0 := by
    have := natCast_ne_zero_of_lt (p := l) (n := 2) (by norm_num) (by omega)
    simpa using this
  have hc : (cN : ZMod l) = -(3 / 2 : ZMod l) := by
    have := modc (l := l) (a := 2 * cN + 3) (b := 0) hcN
    push_cast at this
    field_simp
    linear_combination this
  simp only [chkLen, Bool.and_eq_true] at cLen
  obtain ⟨cL1, cL2⟩ := cLen
  have hlen := allLt_spec cL1 r hr
  have hlen2 := allLt_spec cL2 k hk
  simp only [Bool.and_eq_true, beq_iff_eq] at hlen hlen2
  have hb := modc (allLt_spec (cBase r hr) k hk)
  have hFMk := chkF_sound cFM k hk
  have hFZk := chkF_sound cFZ k hk
  have inner1 : ∀ u ∈ Finset.range (P.H 1),
      ∑ v ∈ Finset.range (P.q0 + 1), baseFilterWeight P l v * CertMod.entry l MT u (P.b0 + k + v) =
        (nth (nthL FMt k) u : ZMod l) := by
    intro u hu
    show _ = (tg FMt k u : ZMod l)
    rw [hFMk u (Finset.mem_range.mp hu)]
    exact Finset.sum_congr rfl (fun v hv => by rw [hW v (by simpa using hv)])
  have inner2 : ∀ u ∈ Finset.range (P.H 1),
      ∑ v ∈ Finset.range (P.q0 + 1), baseFilterWeight P l v * CertMod.entry l ZT u (P.b0 + k + v) =
        (nth (nthL FZt k) u : ZMod l) := by
    intro u hu
    show _ = (tg FZt k u : ZMod l)
    rw [hFZk u (Finset.mem_range.mp hu)]
    exact Finset.sum_congr rfl (fun v hv => by rw [hW v (by simpa using hv)])
  unfold CertMod.tabEntry
  simp only [hP, hD]
  refine (tab_regroup (Finset.range (P.q0 + 1)) (Finset.range (P.H 1))
    (fun v => baseFilterWeight P l v) (fun u => (nth (nthL PR r) u : ZMod l))
    (fun u => (nth (nthL DR r) u : ZMod l))
    (fun u v => CertMod.entry l MT u (P.b0 + k + v))
    (fun u v => CertMod.entry l ZT u (P.b0 + k + v)) (3 / 2 : ZMod l)).trans ?_
  have s1 : (∑ u ∈ Finset.range (P.H 1), (nth (nthL PR r) u : ZMod l) *
      ∑ v ∈ Finset.range (P.q0 + 1), baseFilterWeight P l v * CertMod.entry l MT u (P.b0 + k + v)) =
      ∑ u ∈ Finset.range (P.H 1), (nth (nthL PR r) u : ZMod l) * (nth (nthL FMt k) u : ZMod l) :=
    Finset.sum_congr rfl (fun u hu => by rw [inner1 u hu])
  have s2 : (∑ u ∈ Finset.range (P.H 1), (nth (nthL DR r) u : ZMod l) *
      ∑ v ∈ Finset.range (P.q0 + 1), baseFilterWeight P l v * CertMod.entry l ZT u (P.b0 + k + v)) =
      ∑ u ∈ Finset.range (P.H 1), (nth (nthL DR r) u : ZMod l) * (nth (nthL FZt k) u : ZMod l) :=
    Finset.sum_congr rfl (fun u hu => by rw [inner2 u hu])
  rw [s1, s2,
    ← dotN_cast _ _ _ hlen.1 hlen2.1, ← dotN_cast _ _ _ hlen.2 hlen2.2,
    ← tg_cast', hb]
  push_cast
  rw [hc]

end ResBase
end CatalanMeasure.GenD
