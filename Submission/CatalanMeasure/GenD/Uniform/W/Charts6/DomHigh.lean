module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.SlotsOfOrders
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts3.DomJets
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.SlotNativeCenter
@[expose] public section
set_option Elab.async false

/-!
# `hdom` from order conditions on the coordinate polynomials

Generic (label-free): if the coordinate polynomials of atoms `x` satisfy the order/degree conditions of the
paper's slot spaces (A, C, centre at `±1`, `∞`) and the two virtual-row degree bounds, then `x = Θ c`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts6
open CatalanMeasure.GenD.Uniform.W.Charts4 Module Polynomial CatalanMeasure.Parametric CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD.Uniform.W.Charts3 Finset
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

local notation "Fp" => ZMod p

theorem exists_rows_of_orders_high (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) {ex K : ℕ}
    (hK : K = bN P N p * 4 + 2 + ex) (hb : 0 < bN P N p) (x : Fin p → Fin K → Fp)
    (hX : ∀ (e : Fin p) (j : Fin ex), x e ((ckEquiv hK).symm (Sum.inr (Sum.inr j))) = 0)
    (hr0 : 0 < P.h N % p) (hrh : ¬ (P.h N % p + (p - 1) / 2 < p))
    (hFA : ∀ k : Fin (bN P N p), polx x ((ckEquiv hK).symm (Sum.inl (k, 0))) = 0)
    (hFZ : polx x ((ckEquiv hK).symm (Sum.inr (Sum.inl 0))) = 0)
    (lob lot : ℕ) (hlob : lob + p = P.h N % p + (p - gja (P.g N) p))
    (hlot : lot + p = P.h N % p + grho (P.n N) (P.g N) p)
    (hA : ∀ k : Fin (bN P N p),
      (∀ j < P.h N % p + (p - 1) / 2 - p, (taylor 1 (polx x ((ckEquiv hK).symm (Sum.inl (k, 1))))).coeff j = 0) ∧
      (∀ i, P.h N % p ≤ i → (polx x ((ckEquiv hK).symm (Sum.inl (k, 1)))).coeff i = 0))
    (hC : ∀ k : Fin (bN P N p),
      (∀ j < P.h N % p, (taylor 1 (polx x ((ckEquiv hK).symm (Sum.inl (k, 2))))).coeff j = 0) ∧
      (∀ j < (p - 1) / 2, (taylor (-1) (polx x ((ckEquiv hK).symm (Sum.inl (k, 2))) -
          2 * polx x ((ckEquiv hK).symm (Sum.inl (k, 3))))).coeff j = 0) ∧
      (∀ i, P.h N % p - 1 ≤ i → (polx x ((ckEquiv hK).symm (Sum.inl (k, 3)))).coeff i = 0))
    (hZ : (∀ j < P.h N % p + (p - 1) / 2 - p,
        (taylor 1 (polx x ((ckEquiv hK).symm (Sum.inr (Sum.inl 1))))).coeff j = 0) ∧
      (∀ i, P.h N % p ≤ i → (polx x ((ckEquiv hK).symm (Sum.inr (Sum.inl 1)))).coeff i = 0) ∧
      (∀ j < (p - 1) / 2, (taylor (-1) (polx x ((ckEquiv hK).symm (Sum.inr (Sum.inl 0))) -
          2 * polx x ((ckEquiv hK).symm (Sum.inr (Sum.inl 1))))).coeff j = 0))
    (hVb : ∀ i, lob ≤ i → (polx x ((ckEquiv hK).symm (Sum.inl (⟨0, hb⟩, 1))) -
        polx x ((ckEquiv hK).symm (Sum.inl (⟨0, hb⟩, 3))) +
        polx x ((ckEquiv hK).symm (Sum.inr (Sum.inl 1)))).coeff i = 0)
    (hVt : ∀ i, lot ≤ i → (polx x ((ckEquiv hK).symm (Sum.inl (⟨bN P N p - 1, by omega⟩, 1))) +
        polx x ((ckEquiv hK).symm (Sum.inl (⟨bN P N p - 1, by omega⟩, 3)))).coeff i = 0) :
    ∃ c : Fin (P.n N) → Fp, Theta hp2 hn hK c = x := by
  have hpr := (Fact.out : p.Prime).pos
  have hrp : P.h N % p < p := Nat.mod_lt _ hpr
  refine exists_rows_of_slots hp2 hn hK hb x hX ?_ ?_ ?_ ?_ ?_
  · intro k
    exact (native_A_jets hp2 _ hrp _ _ (polx_degree _ _)).mpr
      ⟨by rw [if_neg hrh]; exact ⟨hFA k, (hA k).1⟩, (hA k).2⟩
  · intro k
    exact (native_C_jets_positive hp2 _ hr0 hrp _ _ (polx_degree _ _)).mpr (hC k)
  · have h1 : (X - 1 : Fp[X]) = X - C 1 := by simp
    have h2 : (X + 1 : Fp[X]) = X - C (-1) := by simp
    have hc := (native_center_split hp2 (P.h N % p) hrp
      (polx x ((ckEquiv hK).symm (Sum.inr (Sum.inl 0)))) (polx x ((ckEquiv hK).symm (Sum.inr (Sum.inl 1))))
      (polx_degree _ _)).mpr ⟨⟨by rw [if_neg hrh, h1, pow_dvd_iff_taylor]; exact ⟨hFZ, hZ.1⟩,
        (degree_lt_iff_top _ _).mpr hZ.2.1⟩, by rw [h2, pow_dvd_iff_taylor]; exact hZ.2.2⟩
    obtain ⟨c, hc⟩ := hc
    refine ⟨c, ?_⟩
    show _ + _ * _ = _
    rw [hc, centerGenerator, mul_smul_comm]
  · have hF : (polx x ((ckEquiv hK).symm (Sum.inl (⟨0, hb⟩, 0))) -
        polx x ((ckEquiv hK).symm (Sum.inl (⟨0, hb⟩, 2))) +
        polx x ((ckEquiv hK).symm (Sum.inr (Sum.inl 0)))).degree < p :=
      lt_of_le_of_lt (degree_add_le _ _) (max_lt
        (lt_of_le_of_lt (degree_sub_le _ _) (max_lt (polx_degree _ _) (polx_degree _ _)))
        (polx_degree _ _))
    have := lam_degree_lt _ _ hF lob hVb
    have e : LamA (P := P) (N := N) hK x ⟨0, hb⟩ - LamC (P := P) (N := N) hK x ⟨0, hb⟩ +
        LamZ (P := P) (N := N) hK x =
        (polx x ((ckEquiv hK).symm (Sum.inl (⟨0, hb⟩, 0))) -
          polx x ((ckEquiv hK).symm (Sum.inl (⟨0, hb⟩, 2))) +
          polx x ((ckEquiv hK).symm (Sum.inr (Sum.inl 0)))) +
        (X ^ p - 1) * (polx x ((ckEquiv hK).symm (Sum.inl (⟨0, hb⟩, 1))) -
          polx x ((ckEquiv hK).symm (Sum.inl (⟨0, hb⟩, 3))) +
          polx x ((ckEquiv hK).symm (Sum.inr (Sum.inl 1)))) := by
      unfold LamA LamC LamZ; ring
    rw [e]
    have h3 : p + lob = P.h N % p + (p - gja (P.g N) p) := by omega
    rwa [h3] at this
  · have hF : (polx x ((ckEquiv hK).symm (Sum.inl (⟨bN P N p - 1, by omega⟩, 0))) +
        polx x ((ckEquiv hK).symm (Sum.inl (⟨bN P N p - 1, by omega⟩, 2)))).degree < p :=
      lt_of_le_of_lt (degree_add_le _ _) (max_lt (polx_degree _ _) (polx_degree _ _))
    have := lam_degree_lt _ _ hF lot hVt
    have e : LamA (P := P) (N := N) hK x ⟨bN P N p - 1, by omega⟩ +
        LamC (P := P) (N := N) hK x ⟨bN P N p - 1, by omega⟩ =
        (polx x ((ckEquiv hK).symm (Sum.inl (⟨bN P N p - 1, by omega⟩, 0))) +
          polx x ((ckEquiv hK).symm (Sum.inl (⟨bN P N p - 1, by omega⟩, 2)))) +
        (X ^ p - 1) * (polx x ((ckEquiv hK).symm (Sum.inl (⟨bN P N p - 1, by omega⟩, 1))) +
          polx x ((ckEquiv hK).symm (Sum.inl (⟨bN P N p - 1, by omega⟩, 3)))) := by
      unfold LamA LamC; ring
    rw [e]
    have h3 : p + lot = P.h N % p + grho (P.n N) (P.g N) p := by omega
    rwa [h3] at this

end
end CatalanMeasure.GenD.Uniform.W.Charts6
