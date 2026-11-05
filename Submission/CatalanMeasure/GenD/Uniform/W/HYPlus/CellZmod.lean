module
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.CellTransfer
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.CellVecs
@[expose] public section
set_option Elab.async false

/-!
# The HY+ cells at `s = 9, 10, 11` in `ZMod p` (Lemma B)

For `p ≠ 2` not dividing the explicit integer `ZHY_s` (moment-table denominators, times the gcd of
the `2 x 2` minors of `u, v`), the residues of the integer vectors `u, v, y` satisfy `HYCell`.
-/

namespace CatalanMeasure.GenD.Uniform.W.HYPlus
open Polynomial Module OAI.InternalCatalan CatalanMeasure.GenD.Uniform.Prefix
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.ZoneZ
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-! ### lcm / gcd list lemmas -/

theorem lcm_start (l : List ℕ) (a : ℕ) : a ∣ l.foldl Nat.lcm a := by
  induction l generalizing a with
  | nil => exact dvd_rfl
  | cons y l ih => exact (Nat.dvd_lcm_left a y).trans (ih _)

theorem dvd_foldl_lcm (l : List ℕ) (a x : ℕ) (hx : x ∈ l) : x ∣ l.foldl Nat.lcm a := by
  induction l generalizing a with
  | nil => simp at hx
  | cons y l ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with h | h
    · subst h; exact (Nat.dvd_lcm_right a x).trans (lcm_start l _)
    · exact ih _ h

theorem foldl_lcm_pos (l : List ℕ) (a : ℕ) (ha : 0 < a) (hl : ∀ x ∈ l, 0 < x) :
    0 < l.foldl Nat.lcm a := by
  induction l generalizing a with
  | nil => exact ha
  | cons y l ih =>
    simp only [List.foldl_cons]
    exact ih _ (Nat.lcm_pos ha (hl y (List.mem_cons_self))) (fun x hx => hl x (List.mem_cons_of_mem _ hx))

theorem dvd_foldl_gcd (q : ℕ) (l : List ℕ) (a : ℕ) (ha : q ∣ a) (hl : ∀ x ∈ l, q ∣ x) :
    q ∣ l.foldl Nat.gcd a := by
  induction l generalizing a with
  | nil => exact ha
  | cons y l ih =>
    simp only [List.foldl_cons]
    exact ih _ (Nat.dvd_gcd ha (hl y List.mem_cons_self)) (fun x hx => hl x (List.mem_cons_of_mem _ hx))

/-! ### The moment table -/

/-- Common denominator of the moments `α(u,J)`, `Z(u,J)`, `u < 15`, `J < 13`. -/
def Zmom15 : ℕ :=
  ((List.range 15).flatMap fun u => (List.range 13).flatMap fun J =>
    [(Q.alphaQ u J).den, (zetaRat u J).den]).foldl Nat.lcm 1

theorem alpha_den_dvd15 {u J : ℕ} (hu : u < 15) (hJ : J < 13) : (Q.alphaQ u J).den ∣ Zmom15 :=
  dvd_foldl_lcm _ _ _ (List.mem_flatMap.mpr ⟨u, List.mem_range.mpr hu,
    List.mem_flatMap.mpr ⟨J, List.mem_range.mpr hJ, by simp⟩⟩)

theorem zeta_den_dvd15 {u J : ℕ} (hu : u < 15) (hJ : J < 13) : (zetaRat u J).den ∣ Zmom15 :=
  dvd_foldl_lcm _ _ _ (List.mem_flatMap.mpr ⟨u, List.mem_range.mpr hu,
    List.mem_flatMap.mpr ⟨J, List.mem_range.mpr hJ, by simp⟩⟩)

theorem Zmom15_pos : 0 < Zmom15 := by
  unfold Zmom15
  refine foldl_lcm_pos _ 1 Nat.one_pos (fun x hx => ?_)
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨u, _, J, _, h⟩ := hx
  rcases h with rfl | rfl
  · exact Nat.pos_of_ne_zero (Rat.den_nz _)
  · exact Nat.pos_of_ne_zero (Rat.den_nz _)

theorem MU_of (hp2 : p ≠ 2) (hc : ¬ p ∣ Zmom15) : MU p :=
  ⟨hp2, fun _ hu _ hJ => mem_unitSub_of_dvd (alpha_den_dvd15 hu hJ) hc,
    fun _ hu _ hJ => mem_unitSub_of_dvd (zeta_den_dvd15 hu hJ) hc⟩

/-! ### Independence and non-vanishing -/

theorem linInd_zv (K : ℕ) (zU zV : ℕ → ℤ) (hg : ¬ p ∣ minorG K zU zV) :
    LinearIndependent (ZMod p) ![zv p K zU, zv p K zV] := by
  have hex : ∃ i < K, ∃ j < K, ¬ (p : ℤ) ∣ (zU i * zV j - zU j * zV i) := by
    by_contra h
    push_neg at h
    apply hg
    refine dvd_foldl_gcd p _ 0 (dvd_zero p) (fun x hx => ?_)
    simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    exact Int.natCast_dvd.mp (h i hi j hj)
  obtain ⟨i, hi, j, hj, hne⟩ := hex
  have hmin : ((zU i : ZMod p) * (zV j : ZMod p) - (zU j : ZMod p) * (zV i : ZMod p)) ≠ 0 := by
    intro h0
    apply hne
    have : (((zU i * zV j - zU j * zV i : ℤ)) : ZMod p) = 0 := by push_cast; exact h0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h1 := congrFun hab ⟨i, hi⟩
  have h2 := congrFun hab ⟨j, hj⟩
  simp only [zv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 h2
  constructor
  · have : a * ((zU i : ZMod p) * (zV j : ZMod p) - (zU j : ZMod p) * (zV i : ZMod p)) = 0 := by
      linear_combination (zV j : ZMod p) * h1 - (zV i : ZMod p) * h2
    exact (mul_eq_zero.mp this).resolve_right hmin
  · have : b * ((zU i : ZMod p) * (zV j : ZMod p) - (zU j : ZMod p) * (zV i : ZMod p)) = 0 := by
      linear_combination (zU i : ZMod p) * h2 - (zU j : ZMod p) * h1
    exact (mul_eq_zero.mp this).resolve_right hmin

theorem zv_ne_zero (K : ℕ) (zY : ℕ → ℤ) (hprim : entryG K zY = 1) : zv p K zY ≠ 0 := by
  intro h
  have hd : p ∣ entryG K zY := by
    refine dvd_foldl_gcd p _ 0 (dvd_zero p) (fun x hx => ?_)
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    have := congrFun h ⟨k, hk⟩
    simp only [zv, Pi.zero_apply] at this
    exact Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this)
  rw [hprim] at hd
  exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp hd)

/-! ### Transfer of the shift identities -/

theorem res_shift (J : ℕ) {A B C : ℚ} (hA : A ∈ unitSub p) (hB : B ∈ unitSub p)
    (h : (J : ℚ) * (A - B) = C) :
    (J : ZMod p) * (palindromicRatResidue p A - palindromicRatResidue p B) =
      palindromicRatResidue p C := by
  have hC : C ∈ unitSub p := h ▸ Subring.mul_mem _ (natCast_mem _ J) (Subring.sub_mem _ hA hB)
  have e : (J : unitSub p) * (⟨A, hA⟩ - ⟨B, hB⟩) = ⟨C, hC⟩ := Subtype.ext (by simpa using h)
  have := congrArg (resHom p) e
  simpa only [map_mul, map_natCast, map_sub, resHom_apply] using this

theorem PhiHp_mem (hm : MU p) (K : ℕ) (z : ℕ → ℤ) {J σ : ℕ} (hJ : J < 13) (hσ : σ + 3 ≤ 15) :
    PhiHp K (-1) z J σ ∈ unitSub p := PhiQ_memG hm _ _ hJ hσ

theorem PhiHm_mem (hm : MU p) (K : ℕ) (z : ℕ → ℤ) {J σ : ℕ} (hJ : J < 13) (hσ : σ + 3 ≤ 15) :
    PhiHm K (-1) z J σ ∈ unitSub p := PhiQ_memG hm _ _ hJ hσ

/-- **The HY+ cell predicate from exact rational identities.** -/
theorem hyCell_gen (hm : MU p) {K s H : ℕ} (hK : K + 1 = s) (hs : s + 1 ≤ 12) (hH : s + 4 ≤ H)
    {zU zV zY : ℕ → ℤ} (hu : HpOK K s zU) (hv : VOK K s zV) (hy : HmOK K s zY)
    (hind : LinearIndependent (ZMod p) ![zv p K zU, zv p K zV]) (hy0 : zv p K zY ≠ 0) :
    HYCell p K s (-1) H (zv p K zU) (zv p K zV) (zv p K zY) := by
  have e1 : ((s : ℤ) + 1) = ((s + 1 : ℕ) : ℤ) := by push_cast; ring
  have e2 : ((s : ℤ) - 1) = ((s - 1 : ℕ) : ℤ) := by omega
  have P0 : ∀ z J, J < 13 → (profHp p K (-1)).psi H J (s : ℤ) (zv p K z) =
      palindromicRatResidue p (PhiHp K (-1) z J s) :=
    fun z J hJ => psiHp_eq hm K (-1) z hJ (by omega) (by omega)
  have P1 : ∀ z J, J < 13 → (profHp p K (-1)).psi H J ((s : ℤ) + 1) (zv p K z) =
      palindromicRatResidue p (PhiHp K (-1) z J (s + 1)) :=
    fun z J hJ => by rw [e1]; exact psiHp_eq hm K (-1) z hJ (by omega) (by omega)
  have P2 : ∀ z J, J < 13 → (profHp p K (-1)).psi H J ((s : ℤ) - 1) (zv p K z) =
      palindromicRatResidue p (PhiHp K (-1) z J (s - 1)) :=
    fun z J hJ => by rw [e2]; exact psiHp_eq hm K (-1) z hJ (by omega) (by omega)
  have M0 : ∀ z J, J < 13 → (profHm p K (-1)).psi H J (s : ℤ) (zv p K z) =
      palindromicRatResidue p (PhiHm K (-1) z J s) :=
    fun z J hJ => psiHm_eq hm K (-1) z hJ (by omega) (by omega)
  have M1 : ∀ z J, J < 13 → (profHm p K (-1)).psi H J ((s : ℤ) + 1) (zv p K z) =
      palindromicRatResidue p (PhiHm K (-1) z J (s + 1)) :=
    fun z J hJ => by rw [e1]; exact psiHm_eq hm K (-1) z hJ (by omega) (by omega)
  have M2 : ∀ z J, J < 13 → (profHm p K (-1)).psi H J ((s : ℤ) - 1) (zv p K z) =
      palindromicRatResidue p (PhiHm K (-1) z J (s - 1)) :=
    fun z J hJ => by rw [e2]; exact psiHm_eq hm K (-1) z hJ (by omega) (by omega)
  refine ⟨palindromicRatResidue p (PhiHp K (-1) zU 1 s),
    palindromicRatResidue p (PhiHm K (-1) zY 1 s),
    palindromicRatResidue p (2 * (PhiHp K (-1) zU 2 (s + 1) - PhiHp K (-1) zU 1 s)),
    palindromicRatResidue p (2 * (PhiHm K (-1) zY 2 (s + 1) - PhiHm K (-1) zY 1 s)),
    palindromicRatResidue p (1 * (PhiHp K (-1) zU 1 s - PhiHp K (-1) zU 0 (s - 1))),
    palindromicRatResidue p (1 * (PhiHm K (-1) zY 1 s - PhiHm K (-1) zY 0 (s - 1))),
    palindromicRatResidue p (2 * (PhiHp K (-1) zV 1 (s - 1) - PhiHp K (-1) zV 1 s)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hind, hy0⟩
  · intro J h1 h2
    rw [P0 _ J (by omega), hu.1 J h1 h2]
  · intro J h1 h2
    rw [M0 _ J (by omega), hy.1 J h1 h2]
  · intro J h1 h2
    rw [P0 _ J (by omega), P1 _ J (by omega), hv.1 J h1 h2]
  · intro J h1 h2
    rw [P1 _ J (by omega)]
    exact res_shift J (PhiHp_mem hm K zU (by omega) (by omega))
      (PhiHp_mem hm K zU (by omega) (by omega)) (hu.2.1 J h1 h2)
  · intro J h1 h2
    rw [M1 _ J (by omega)]
    exact res_shift J (PhiHm_mem hm K zY (by omega) (by omega))
      (PhiHm_mem hm K zY (by omega) (by omega)) (hy.2.1 J h1 h2)
  · intro J h1
    rw [P2 _ J (by omega)]
    have := res_shift (J + 1) (PhiHp_mem hm K zU (by omega) (by omega))
      (PhiHp_mem hm K zU (by omega) (by omega)) (hu.2.2 J h1)
    push_cast at this
    exact this
  · intro J h1
    rw [M2 _ J (by omega)]
    have := res_shift (J + 1) (PhiHm_mem hm K zY (by omega) (by omega))
      (PhiHm_mem hm K zY (by omega) (by omega)) (hy.2.2 J h1)
    push_cast at this
    exact this
  · intro J h1 h2
    rw [P2 _ J (by omega), P0 _ J (by omega)]
    have := res_shift (J + 1) (PhiHp_mem hm K zV (by omega) (by omega))
      (PhiHp_mem hm K zV (by omega) (by omega)) (hv.2 J h1 h2)
    push_cast at this
    exact this

/-! ### The explicit bad-prime integers and the three cells -/

/-- Bad-prime integer of the HY+ cell at `s = 9`. -/
def ZHY9 : ℕ := Zmom15 * minorG 8 u9 v9
/-- Bad-prime integer of the HY+ cell at `s = 10`. -/
def ZHY10 : ℕ := Zmom15 * minorG 9 u10 v10
/-- Bad-prime integer of the HY+ cell at `s = 11`. -/
def ZHY11 : ℕ := Zmom15 * minorG 10 u11 v11

theorem ZHY9_pos : 0 < ZHY9 := Nat.mul_pos Zmom15_pos minor9_pos
theorem ZHY10_pos : 0 < ZHY10 := Nat.mul_pos Zmom15_pos minor10_pos
theorem ZHY11_pos : 0 < ZHY11 := Nat.mul_pos Zmom15_pos minor11_pos

theorem hyCell_9 (hp2 : p ≠ 2) (hc : ¬ p ∣ ZHY9) {H : ℕ} (hH : 13 ≤ H) :
    ∃ u v y : Fin 8 → ZMod p, HYCell p 8 9 (-1) H u v y :=
  ⟨zv p 8 u9, zv p 8 v9, zv p 8 y9,
    hyCell_gen (MU_of hp2 (fun h => hc (h.trans (Dvd.intro _ rfl)))) rfl (by norm_num) (by omega)
      hpOK9 vOK9 hmOK9 (linInd_zv 8 u9 v9 (fun h => hc (h.trans (Dvd.intro_left _ rfl))))
      (zv_ne_zero 8 y9 y9_prim)⟩

theorem hyCell_10 (hp2 : p ≠ 2) (hc : ¬ p ∣ ZHY10) {H : ℕ} (hH : 14 ≤ H) :
    ∃ u v y : Fin 9 → ZMod p, HYCell p 9 10 (-1) H u v y :=
  ⟨zv p 9 u10, zv p 9 v10, zv p 9 y10,
    hyCell_gen (MU_of hp2 (fun h => hc (h.trans (Dvd.intro _ rfl)))) rfl (by norm_num) (by omega)
      hpOK10 vOK10 hmOK10 (linInd_zv 9 u10 v10 (fun h => hc (h.trans (Dvd.intro_left _ rfl))))
      (zv_ne_zero 9 y10 y10_prim)⟩

theorem hyCell_11 (hp2 : p ≠ 2) (hc : ¬ p ∣ ZHY11) {H : ℕ} (hH : 15 ≤ H) :
    ∃ u v y : Fin 10 → ZMod p, HYCell p 10 11 (-1) H u v y :=
  ⟨zv p 10 u11, zv p 10 v11, zv p 10 y11,
    hyCell_gen (MU_of hp2 (fun h => hc (h.trans (Dvd.intro _ rfl)))) rfl (by norm_num) (by omega)
      hpOK11 vOK11 hmOK11 (linInd_zv 10 u11 v11 (fun h => hc (h.trans (Dvd.intro_left _ rfl))))
      (zv_ne_zero 10 y11 y11_prim)⟩

end
end CatalanMeasure.GenD.Uniform.W.HYPlus
