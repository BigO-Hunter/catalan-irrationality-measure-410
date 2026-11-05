module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger4.GlueGen

@[expose] public section
set_option Elab.async false

/-!
# MT (b) glue windows (lane G5g)

Cells `s = 18` (`K = 15`, `x in (4.06, 4.1]`) and `s = 17` (`K = 14`, `x in (4.2951, 4.33]`) of `mtGlueLB'`,
with `D1 = 5N - p` (so the low block reaches exactly `-g`), `elo = 0` resp. `69 N - 16 p`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger4
open CatalanMeasure.Parametric OAI.InternalCatalan Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.LedgerW
open CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger3
open CatalanMeasure.GenD.Uniform.W.MTGlue CatalanMeasure.GenD.Uniform.W.SlotsT
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section

theorem foldl_lcm_ne_zero2 (l : List ℕ) (a : ℕ) (ha : a ≠ 0) (hl : ∀ x ∈ l, x ≠ 0) :
    l.foldl Nat.lcm a ≠ 0 := by
  induction l generalizing a with
  | nil => simpa using ha
  | cons x t ih =>
    simp only [List.foldl_cons]
    exact ih _ (Nat.lcm_ne_zero ha (hl x (List.mem_cons_self)))
      (fun y hy => hl y (List.mem_cons_of_mem _ hy))

theorem ZmG_ne : ZmG ≠ 0 := by
  unfold ZmG
  refine foldl_lcm_ne_zero2 _ _ two_ne_zero ?_
  intro x hx
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨u, -, J, -, rfl | rfl⟩ := hx
  · exact Rat.den_nz _
  · exact Rat.den_nz _

theorem cell17_mod_ne : cell17.modulus ≠ 0 := by
  have h := cell17_ky
  unfold GlueCell.modulus
  exact Nat.mul_ne_zero (Nat.mul_ne_zero ZmG_ne (by simpa [cell17] using h.1))
    (by simpa [cell17] using h.2)

theorem cell18_mod_ne : cell18.modulus ≠ 0 := by
  have h := cell18_ky
  unfold GlueCell.modulus
  exact Nat.mul_ne_zero (Nat.mul_ne_zero ZmG_ne (by simpa [cell18] using h.1))
    (by simpa [cell18] using h.2)

theorem cop_of_lt {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) (h : m < p) : Nat.Coprime p m :=
  (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd =>
    absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hd) (by omega)

theorem cen_top18 (p : ℕ) : cen p cell18.K cell18.k0 ⟨cell18.K - 1, by simp [cell18]⟩ = 13 * (p : ℤ) := by
  simp [cen, cell18]

theorem cen_top17 (p : ℕ) : cen p cell17.K cell17.k0 ⟨cell17.K - 1, by simp [cell17]⟩ = 12 * (p : ℤ) := by
  simp [cen, cell17]

theorem cen_18 (p : ℕ) (k : Fin cell18.K) : cen p cell18.K cell18.k0 k = (-1 + (k.val : ℤ)) * p := rfl
theorem cen_17 (p : ℕ) (k : Fin cell17.K) : cen p cell17.K cell17.k0 k = (-1 + (k.val : ℤ)) * p := rfl

theorem gval18 {N p : ℕ} (hp : p.Prime) (hM : cell18.modulus < N) (hN : 1000 ≤ N)
    (h1 : 203 * N < 50 * p) (h2 : 10 * p ≤ 41 * N) :
    (2 * (5 * N - p) + 1) - (78 * N - 1 - 18 * p - p + 1) - (((5 * N - p) - (53 * N - 13 * p - 1)) +
      (13 * p - 53 * N) + 1) - (p - 3 * N - (3 * N + (p - 1) / 2 - p)) ≤ (mtGlueLB' design adm).kap N p := by
  have hcop := cop_of_lt hp cell18_mod_ne (by omega : cell18.modulus < p)
  have hw : GlueWin design N p cell18 (5 * N - p) 0 := by
    have hs : cell18.s = 18 := rfl
    unfold GlueWin
    rw [hs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · (try des_unfold); omega
    · (try des_unfold); omega
    · (try des_unfold); omega
    · (try des_unfold); omega
    · (try des_unfold); omega
    · (try des_unfold); omega
    · (try des_unfold); omega
    · (try des_unfold); omega
    · exact cov1_gen (P := design) (lo := 2) (hi := 16)
        (T := design.H N - 1 - 18 * p - (design.h N + (5 * N - p) - 1)) (by omega)
        (by des_unfold; omega) (by des_unfold; omega) (by des_unfold; omega)
    · exact cov2_gen (P := design) (lo' := 2) (hi := 17) (elo := 0) (eta := design.H N - 1 - 18 * p)
        (by omega) (by des_unfold; omega) (by des_unfold; omega)
  have hlow : ∀ k : Fin cell18.K, -(design.g N : ℤ) ≤ cen p cell18.K cell18.k0 k - ((5 * N - p : ℕ) : ℤ) := by
    intro k
    have hk : k.val < 15 := k.isLt
    rw [cen_18]
    have c1 : (-1 : ℤ) * p ≤ (-1 + (k.val : ℤ)) * p := by
      have : (0 : ℤ) ≤ k.val := Int.natCast_nonneg _
      nlinarith [(Int.natCast_nonneg p : (0 : ℤ) ≤ p)]
    des_unfold; push_cast; omega
  have hmid : ∀ k : Fin cell18.K, k.val + 1 < cell18.K →
      cen p cell18.K cell18.k0 k + ((5 * N - p : ℕ) : ℤ) < (design.n N : ℤ) - design.g N := by
    intro k hk'
    have hk : k.val < 14 := by have : cell18.K = 15 := rfl; omega
    rw [cen_18]
    have c1 : (-1 + (k.val : ℤ)) * p ≤ 12 * p := by
      have : (k.val : ℤ) ≤ 13 := by exact_mod_cast (by omega : k.val ≤ 13)
      nlinarith [(Int.natCast_nonneg p : (0 : ℤ) ≤ p)]
    des_unfold; push_cast; omega
  have key := glue_ge adm hp cell18 hcop hw hlow hmid (r1 := 53 * N - 13 * p - 1) (u := 13 * p - 53 * N)
    (by rw [cen_top18]; des_unfold; omega) (by rw [cen_top18]; des_unfold; omega)
  have hs : cell18.s = 18 := rfl
  rw [hs] at key
  refine le_trans ?_ (le_trans key (glueCell18_le design adm N p))
  des_unfold
  omega

theorem gval17 {N p : ℕ} (hp : p.Prime) (hM : cell17.modulus < N) (hN : 1000 ≤ N)
    (h1 : 42951 * N < 10000 * p) (h2 : 100 * p ≤ 433 * N) :
    (2 * (5 * N - p) + 1) - ((78 * N - 1 - 17 * p - p + 1) + (69 * N - 16 * p)) - 1 -
      (p - 3 * N - (3 * N + (p - 1) / 2 - p)) ≤ (mtGlueLB' design adm).kap N p := by
  have hcop := cop_of_lt hp cell17_mod_ne (by omega : cell17.modulus < p)
  have hw : GlueWin design N p cell17 (5 * N - p) (69 * N - 16 * p) := by
    have hs : cell17.s = 17 := rfl
    unfold GlueWin
    rw [hs]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · (try des_unfold); omega
    · (try des_unfold); omega
    · (try des_unfold); omega
    · (try des_unfold); omega
    · (try des_unfold); omega
    · (try des_unfold); omega
    · (try des_unfold); omega
    · (try des_unfold); omega
    · exact cov1_gen (P := design) (lo := 2) (hi := 15)
        (T := design.H N - 1 - 17 * p - (design.h N + (5 * N - p) - 1)) (by omega)
        (by des_unfold; omega) (by des_unfold; omega) (by des_unfold; omega)
    · exact cov2_gen (P := design) (lo' := 2) (hi := 16) (elo := 69 * N - 16 * p)
        (eta := design.H N - 1 - 17 * p)
        (by omega) (by des_unfold; omega) (by des_unfold; omega)
  have hlow : ∀ k : Fin cell17.K, -(design.g N : ℤ) ≤ cen p cell17.K cell17.k0 k - ((5 * N - p : ℕ) : ℤ) := by
    intro k
    have hk : k.val < 14 := k.isLt
    rw [cen_17]
    have c1 : (-1 : ℤ) * p ≤ (-1 + (k.val : ℤ)) * p := by
      have : (0 : ℤ) ≤ k.val := Int.natCast_nonneg _
      nlinarith [(Int.natCast_nonneg p : (0 : ℤ) ≤ p)]
    des_unfold; push_cast; omega
  have hmid : ∀ k : Fin cell17.K, k.val + 1 < cell17.K →
      cen p cell17.K cell17.k0 k + ((5 * N - p : ℕ) : ℤ) < (design.n N : ℤ) - design.g N := by
    intro k hk'
    have hk : k.val < 13 := by have : cell17.K = 14 := rfl; omega
    rw [cen_17]
    have c1 : (-1 + (k.val : ℤ)) * p ≤ 11 * p := by
      have : (k.val : ℤ) ≤ 12 := by exact_mod_cast (by omega : k.val ≤ 12)
      nlinarith [(Int.natCast_nonneg p : (0 : ℤ) ≤ p)]
    des_unfold; push_cast; omega
  have key := glue_ge adm hp cell17 hcop hw hlow hmid (r1 := 53 * N - 12 * p - 1) (u := 12 * p - 53 * N)
    (by rw [cen_top17]; des_unfold; omega) (by rw [cen_top17]; des_unfold; omega)
  have hs : cell17.s = 17 := rfl
  rw [hs] at key
  refine le_trans ?_ (le_trans key (glueCell17_le design adm N p))
  des_unfold
  omega

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger4
