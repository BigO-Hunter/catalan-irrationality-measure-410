module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Virtual
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.SlotsToTiling
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.ThetaInj
@[expose] public section
set_option Elab.async false

/-!
# `hdom`, polynomial form: slot conditions on the atoms give physical rows

If the polynomial coordinates of atoms `x` satisfy the slot conditions (each `Λ = F + (Y-1) E` is
`(X-1)^{r_h}` times an element of the native span, the centre is a multiple of the centre generator,
and the two virtual-row degree bounds hold), then `x = Θ c` for physical rows `c`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts4
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.Charts3 CatalanMeasure.GenD.Uniform.W.Thin Finset
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

local notation "Fp" => ZMod p

/-- Relative offset of the last actual row inside the last block. -/
def grho (n g p : ℕ) : ℕ := (((n : ℤ) - 1 - g) - gk1 n g p * p).toNat

theorem grho_spec {n g p : ℕ} (hp : 0 < p) :
    ((grho n g p : ℕ) : ℤ) = (n : ℤ) - 1 - g - gk1 n g p * p ∧ grho n g p < p := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have h1 := Int.emod_add_mul_ediv ((n : ℤ) - 1 - g) p
  have h2 := Int.emod_nonneg ((n : ℤ) - 1 - g) hp'.ne'
  have h3 := Int.emod_lt_of_pos ((n : ℤ) - 1 - g) hp'
  have hc : gk1 n g p * p = p * gk1 n g p := mul_comm _ _
  have hk : gk1 n g p = ((n : ℤ) - 1 - g) / p := rfl
  have hnn : 0 ≤ ((n : ℤ) - 1 - g) - gk1 n g p * p := by rw [hk] at hc ⊢; linarith
  unfold grho
  constructor
  · rw [Int.toNat_of_nonneg hnn]
  · have hlt : ((n : ℤ) - 1 - g) - gk1 n g p * p < p := by rw [hk] at hc ⊢; linarith
    omega

theorem geom_rel {n g p : ℕ} (hp : 0 < p) (hn : 1 ≤ n) :
    gja g p + n = (gb n g p - 1) * p + grho n g p + 1 := by
  obtain ⟨hja, _⟩ := gja_spec (g := g) hp
  obtain ⟨hle, hb⟩ := gb_spec (g := g) (n := n) hp hn
  obtain ⟨hrho, _⟩ := grho_spec (n := n) (g := g) hp
  have hb1 : 1 ≤ gb n g p := by
    have : (1 : ℤ) ≤ gb n g p := by rw [hb]; omega
    exact_mod_cast this
  zify [hb1]
  rw [hja, hrho, hb]
  ring

theorem degree_lt_of_rem_mul (Q : Fp[X]) (r s : ℕ)
    (h : ((X - 1 : Fp[X]) ^ r * Q).degree < ((r + s : ℕ) : WithBot ℕ)) : Q.degree < s := by
  have hd : ((X - 1 : Fp[X])).degree = 1 := by simpa using degree_X_sub_C (1 : Fp)
  by_cases hQ : Q = 0
  · simp [hQ]
  · rw [degree_mul, degree_pow, hd, degree_eq_natDegree hQ] at h
    rw [degree_eq_natDegree hQ]
    simp only [nsmul_eq_mul, mul_one] at h
    norm_cast at h ⊢
    omega

/-- `Λ`-polynomials of the atoms: the F/E splits of A_k, C_k and the centre. -/
def LamA {ex K : ℕ} (hK : K = bN P N p * 4 + 2 + ex) (x : Fin p → Fin K → Fp)
    (k : Fin (bN P N p)) : Fp[X] :=
  polx x ((ckEquiv hK).symm (Sum.inl (k, 0))) + (X ^ p - 1) * polx x ((ckEquiv hK).symm (Sum.inl (k, 1)))
def LamC {ex K : ℕ} (hK : K = bN P N p * 4 + 2 + ex) (x : Fin p → Fin K → Fp)
    (k : Fin (bN P N p)) : Fp[X] :=
  polx x ((ckEquiv hK).symm (Sum.inl (k, 2))) + (X ^ p - 1) * polx x ((ckEquiv hK).symm (Sum.inl (k, 3)))
def LamZ {ex K : ℕ} (hK : K = bN P N p * 4 + 2 + ex) (x : Fin p → Fin K → Fp) : Fp[X] :=
  polx x ((ckEquiv hK).symm (Sum.inr (Sum.inl 0))) +
    (X ^ p - 1) * polx x ((ckEquiv hK).symm (Sum.inr (Sum.inl 1)))

/-- **`hdom`, polynomial form.** -/
theorem exists_rows_of_slots (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) {ex K : ℕ}
    (hK : K = bN P N p * 4 + 2 + ex) (hb : 0 < bN P N p) (x : Fin p → Fin K → Fp)
    (hX : ∀ (e : Fin p) (j : Fin ex), x e ((ckEquiv hK).symm (Sum.inr (Sum.inr j))) = 0)
    (hA : ∀ k, ∃ A ∈ Submodule.span Fp (Set.range (plusVectors (p := p))),
      LamA (P := P) (N := N) hK x k = (X - 1) ^ (P.h N % p) * A)
    (hC : ∀ k, ∃ A ∈ Submodule.span Fp (Set.range (minusVectors (p := p))),
      LamC (P := P) (N := N) hK x k = (X - 1) ^ (P.h N % p) * A)
    (hZ : ∃ z : Fp, LamZ (P := P) (N := N) hK x = (X - 1) ^ (P.h N % p) * (z • nativeCenter (p := p)))
    (hVb : (LamA (P := P) (N := N) hK x ⟨0, hb⟩ - LamC (P := P) (N := N) hK x ⟨0, hb⟩ +
        LamZ (P := P) (N := N) hK x).degree <
      ((P.h N % p + (p - gja (P.g N) p) : ℕ) : WithBot ℕ))
    (hVt : (LamA (P := P) (N := N) hK x ⟨bN P N p - 1, by omega⟩ +
        LamC (P := P) (N := N) hK x ⟨bN P N p - 1, by omega⟩).degree <
      ((P.h N % p + grho (P.n N) (P.g N) p : ℕ) : WithBot ℕ)) :
    ∃ c : Fin (P.n N) → Fp, Theta hp2 hn hK c = x := by
  have hp := (Fact.out : p.Prime).pos
  haveI : NeZero (2 : Fp) := ⟨native_two_ne_zero hp2⟩
  choose A hAm hAe using hA
  choose B hBm hBe using hC
  choose gA' hgA using fun k => (Submodule.mem_span_range_iff_exists_fun Fp).mp (hAm k)
  choose gC' hgC using fun k => (Submodule.mem_span_range_iff_exists_fun Fp).mp (hBm k)
  obtain ⟨z, hz⟩ := hZ
  set t := tilingOfSlots gA' gC' z with ht
  have hQA : ∀ k, LamA (P := P) (N := N) hK x k = rem P N p * QA t k := by
    intro k; rw [hAe k, ht, QA_tilingOfSlots, hgA k]; rfl
  have hQC : ∀ k, LamC (P := P) (N := N) hK x k = rem P N p * QC t k := by
    intro k; rw [hBe k, ht, QC_tilingOfSlots, hgC k]; rfl
  have hQZ : LamZ (P := P) (N := N) hK x = rem P N p * (t.2 0 • nativeCenter (p := p)) := by
    rw [hz, ht, z_tilingOfSlots]; rfl
  set ĉ := physicalTilingEquiv (bN P N p) ((p - 1) / 2) p (native_half_identity hp2)
    (native_two_ne_zero hp2) t with hĉ
  have hja := (gja_spec (g := P.g N) hp)
  have hrel : gja (P.g N) p + P.n N = (bN P N p - 1) * p + grho (P.n N) (P.g N) p + 1 :=
    geom_rel (n := P.n N) (g := P.g N) hp hn
  have hrho := (grho_spec (n := P.n N) (g := P.g N) hp).2
  have hbp : p ≤ bN P N p * p := Nat.le_mul_of_pos_left p hb
  have hmp : (bN P N p - 1) * p + p = bN P N p * p := by
    have : bN P N p = (bN P N p - 1) + 1 := by omega
    conv_rhs => rw [this]
    ring
  generalize hmdef : (bN P N p - 1) * p = m at hrel hmp
  generalize hMdef : bN P N p * p = M at hmp
  -- bottom support
  have hbot : (QA t ⟨0, hb⟩ - QC t ⟨0, hb⟩ + t.2 0 • nativeCenter (p := p)).degree <
      ((p - gja (P.g N) p : ℕ) : WithBot ℕ) := by
    apply degree_lt_of_rem_mul _ (P.h N % p)
    have : LamA (P := P) (N := N) hK x ⟨0, hb⟩ - LamC (P := P) (N := N) hK x ⟨0, hb⟩ +
        LamZ (P := P) (N := N) hK x =
        (X - 1) ^ (P.h N % p) * (QA t ⟨0, hb⟩ - QC t ⟨0, hb⟩ + t.2 0 • nativeCenter (p := p)) := by
      rw [hQA, hQC, hQZ]; unfold rem; ring
    rw [← this]; exact hVb
  have hbot' := (bottomEndpoint_cut p (gja (P.g N) p) hja.2.le (fun i : Fin p => ĉ
    ⟨i.val, by have := i.isLt; omega⟩)).mp (by rw [← bottom_identity hp2 hb t]; exact hbot)
  have htop : (QA t ⟨bN P N p - 1, by omega⟩ + QC t ⟨bN P N p - 1, by omega⟩).degree <
      ((grho (P.n N) (P.g N) p : ℕ) : WithBot ℕ) := by
    apply degree_lt_of_rem_mul _ (P.h N % p)
    have : LamA (P := P) (N := N) hK x ⟨bN P N p - 1, by omega⟩ +
        LamC (P := P) (N := N) hK x ⟨bN P N p - 1, by omega⟩ =
        (X - 1) ^ (P.h N % p) * (QA t ⟨bN P N p - 1, by omega⟩ + QC t ⟨bN P N p - 1, by omega⟩) := by
      rw [hQA, hQC]; unfold rem; ring
    rw [← this]; exact hVt
  have htop' := (topEndpoint_cut p (grho (P.n N) (P.g N) p) (fun i : Fin (p + 1) => ĉ
    ⟨(bN P N p - 1) * p + i.val, by have := i.isLt; omega⟩)).mp
    (by rw [← top_identity hp2 hb t]; exact htop)
  have hsupp : ĉ ∈ intervalRows (K := Fp) (gja (P.g N) p) (P.n N) (bN P N p * p + 1) := by
    intro i hi
    rcases hi with hi | hi
    · have := hbot' ⟨i.val, by have := hja.2; omega⟩ hi
      simpa using this
    · have h1 := i.isLt
      have := htop' ⟨i.val - (bN P N p - 1) * p, by omega⟩ (by simp only; omega)
      have e : (bN P N p - 1) * p + (i.val - (bN P N p - 1) * p) = i.val := by omega
      simpa [e] using this
  let c := (intervalRowsEquiv (K := Fp) (gja (P.g N) p) (P.n N) (bN P N p * p + 1)
    (gja_len hp hn)).symm ⟨ĉ, hsupp⟩
  have hrow : rowsExt (P.n N) (P.g N) p hp hn c = ĉ := by
    unfold rowsExt
    simp [c]
  have htL : tL hp2 hn c = t := by
    unfold tL
    simp [hrow, hĉ]
  refine ⟨c, ?_⟩
  funext e idx
  rw [Theta_apply]
  obtain ⟨i, hi⟩ : ∃ i, ckEquiv hK idx = i := ⟨_, rfl⟩
  have hidx : idx = (ckEquiv hK).symm i := by rw [← hi]; simp
  rw [hi]
  subst hidx
  have hF : ∀ (F E : Fp[X]), F.degree < p → (F + (X ^ p - 1) * E) = F + (X ^ p - 1) * E := fun _ _ _ => rfl
  rcases i with ⟨k, u⟩ | z' | j
  · rcases (by omega : u.val = 0 ∨ u.val = 1 ∨ u.val = 2 ∨ u.val = 3) with h | h | h | h
    · have hu : u = 0 := Fin.ext h
      subst hu
      rw [kp_A0, htL, ← hQA k, LamA]
      rw [(fpart_epart_of _ _ (polx_degree _ _)).1, polx_coeff]
    · have hu : u = 1 := Fin.ext h
      subst hu
      rw [kp_A1, htL, ← hQA k, LamA]
      rw [(fpart_epart_of _ _ (polx_degree _ _)).2, polx_coeff]
    · have hu : u = 2 := Fin.ext h
      subst hu
      rw [kp_C0, htL, ← hQC k, LamC]
      rw [(fpart_epart_of _ _ (polx_degree _ _)).1, polx_coeff]
    · have hu : u = 3 := Fin.ext h
      subst hu
      rw [kp_C1, htL, ← hQC k, LamC]
      rw [(fpart_epart_of _ _ (polx_degree _ _)).2, polx_coeff]
  · rcases (by omega : z'.val = 0 ∨ z'.val = 1) with h | h
    · have hu : z' = 0 := Fin.ext h
      subst hu
      rw [kp_Z0, htL, ← hQZ, LamZ]
      rw [(fpart_epart_of _ _ (polx_degree _ _)).1, polx_coeff]
    · have hu : z' = 1 := Fin.ext h
      subst hu
      rw [kp_Z1, htL, ← hQZ, LamZ]
      rw [(fpart_epart_of _ _ (polx_degree _ _)).2, polx_coeff]
  · rw [kp_X, hX e j]
    simp

end
end CatalanMeasure.GenD.Uniform.W.Charts4
