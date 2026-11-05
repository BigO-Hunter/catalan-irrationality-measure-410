module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZResp
@[expose] public section
set_option Elab.async false

/-!
# Two coefficients per residue

For a slot system with `emax ≤ 2p` the response at residue `ℓ` only sees the coefficients
`e = r` and `e = r + p`, where `r = (T mod p)` and `T = H - 1 - ℓ`:

    Σ_{e<emax} [p ∣ T - e] g e = [r < emax] g r + [r + p < emax] g (r + p).
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
noncomputable section

theorem sum_two_coeffs {p : ℕ} (hp : 0 < p) (T : ℤ) (emax : ℕ) (hemax : emax ≤ 2 * p)
    {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ e ∈ Finset.range emax, (if (p : ℤ) ∣ T - e then g e else 0) =
      (if (T % p).toNat < emax then g (T % p).toNat else 0) +
      (if (T % p).toNat + p < emax then g ((T % p).toNat + p) else 0) := by
  have hp1 : (0 : ℤ) < p := by exact_mod_cast hp
  set r : ℕ := (T % p).toNat with hr
  have hr0 : (0 : ℤ) ≤ T % p := Int.emod_nonneg _ hp1.ne'
  have hrlt : (T % p) < p := Int.emod_lt_of_pos _ hp1
  have hrp : (r : ℤ) = T % p := Int.toNat_of_nonneg hr0
  have hrp' : r < p := by omega
  have hdv : (p : ℤ) ∣ T - r := ⟨T / p, by rw [hrp, Int.emod_def]; ring⟩
  have hterm : ∀ e ∈ Finset.range emax, (if (p : ℤ) ∣ T - e then g e else 0) =
      (if e = r then g e else 0) + (if e = r + p then g e else 0) := by
    intro e he
    have he' := Finset.mem_range.mp he
    by_cases h1 : e = r
    · subst h1
      rw [if_pos hdv, if_pos rfl, if_neg (by omega)]; simp
    by_cases h2 : e = r + p
    · subst h2
      have : (p : ℤ) ∣ T - ((r + p : ℕ) : ℤ) := by
        have : T - ((r + p : ℕ) : ℤ) = (T - r) - p := by push_cast; ring
        rw [this]
        exact dvd_sub hdv dvd_rfl
      rw [if_pos this, if_neg h1, if_pos rfl]; simp
    · rw [if_neg h1, if_neg h2]
      simp only [add_zero]
      split_ifs with hd
      · exfalso
        have hmod : (e : ℤ) % p = T % p := by
          have := Int.emod_emod_of_dvd (T : ℤ) (dvd_refl (p : ℤ))
          exact (Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
            (Int.emod_eq_zero_of_dvd (by
              have : (e : ℤ) - T = -(T - e) := by ring
              rw [this]; exact (dvd_neg).mpr hd)))
        have hen : e % p = r := by
          have h3 : ((e % p : ℕ) : ℤ) = (e : ℤ) % p := by exact_mod_cast Int.natCast_mod e p
          omega
        have hdiv : e / p < 2 := by
          rw [Nat.div_lt_iff_lt_mul hp]; omega
        have : e = e % p + p * (e / p) := (Nat.mod_add_div e p).symm
        interval_cases h : e / p
        · omega
        · omega
      · rfl
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_ite_eq' (Finset.range emax) r g]
    simp [Finset.mem_range]
  · rw [Finset.sum_ite_eq' (Finset.range emax) (r + p) g]
    simp [Finset.mem_range]

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
