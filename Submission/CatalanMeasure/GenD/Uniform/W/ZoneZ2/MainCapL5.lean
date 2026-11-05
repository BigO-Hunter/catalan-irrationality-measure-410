module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZMainCap
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ2.VirtL2
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ2.FlatCap5
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ2.MainCapL
@[expose] public section
set_option Elab.async false

/-!
# Theorem Z, Law_L(4), cap window (`p ≤ η < 2p`, `L ≤ 5p`): `zLcap_le_nullity` (G2h)

The Law_L engine.  Cell hypotheses: `CellHyp` (`μ_3 = 0`), `CellHyp0` (digit `0`), `CellHypCap`,
`CellHypCap1`.  Top block has no `+` members (`rt = 0`), the extra family `S - A = 0`
(`δ < d₀`) is virtual; the digit-`s` group is empty (Lemma X with `rt = 0`).
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

set_option maxHeartbeats 1600000 in
theorem zLcap5_le_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH2 : P.H N < p ^ 2)
    {hp : ℕ} (hphp : hp = (p - 1) / 2) {K : ℕ} (u u2 y1 y2 : Fin K → ZMod p)
    {μ2 μ3 ν ρ : ZMod p} {ktop k0 : Fin K}
    (hcell : CellHyp p K (P.H N) u u2 y1 y2 μ2 μ3 ν ρ ktop k0)
    (hcell0 : CellHyp0 p K (P.H N) u u2 y1 y2)
    (hcap : CellHypCap p K (P.H N) u u2 y1 y2) (hcap1 : CellHypCap1 p K (P.H N) u u2 y1 y2)
    (h3 : (3 : ZMod p) ≠ 0)
    (hind1 : ∀ (c1 c2 : ZMod p), (∀ k, c1 * u k + c2 * u2 k = 0) → c1 = 0 ∧ c2 = 0)
    (hind2 : ∀ (c1 c2 : ZMod p), (∀ k, c1 * y1 k + c2 * y2 k = 0) → c1 = 0 ∧ c2 = 0)
    (hhp : P.h N + hp ≤ p - 1) (hqh : P.q N + P.h N ≤ hp)
    (t : ℕ) (hHt : P.H N = t + 1 + 5 * p) (ht : t < p) (hη1 : P.h N + hp ≤ t + p + 1)
    (hb : P.b N < p) (g d0 : ℕ) (hg0 : g ≤ hp) (hgP : g = P.g N) (hd1 : 1 ≤ d0) (hd2 : d0 ≤ hp)
    (hvtop : ∀ d : ℕ, d ≤ hp → ¬ InRange P N ((((0 : ℤ) + (ktop : ℕ)) * p) + d) → 0 < d ∨ d = 0)
    (hvtopm : ∀ d : ℕ, d ≤ hp → ¬ InRange P N ((((0 : ℤ) + (ktop : ℕ)) * p) - d) → d < d0)
    (hv0 : ∀ d : ℕ, d ≤ hp → ¬ InRange P N ((((0 : ℤ) + (k0 : ℕ)) * p) - d) → g < d)
    (hoth : ∀ (k : Fin K) (d : ℕ), d ≤ hp → k ≠ ktop →
      InRange P N ((((0 : ℤ) + (k : ℕ)) * p) + d))
    (hoth' : ∀ (k : Fin K) (d : ℕ), d ≤ hp → k ≠ k0 → k ≠ ktop →
      InRange P N ((((0 : ℤ) + (k : ℕ)) * p) - d)) :
    (4 * hp + 2) - ((hp - 0) + (hp - g) + d0) -
        ((hp + 1 - P.h N - P.q N) + (hp + 1 - P.h N) + (P.h N + hp - (t + 1)) +
          (t + 1) + (t + 1 - P.b N) + (P.L N - 5 * p)) ≤ nullity P N p := by
  have hq0 : 0 < P.q N := Nat.mul_pos hP.2.2.1 hN
  have hodd : p = 2 * hp + 1 := by have := p_odd_half hp2; omega
  have hD : hp + 1 ≤ (p - 1) / 2 + 1 := by omega
  have hemax : P.h N + (p - 1) + (hp + 1) ≤ 2 * p := by omega
  have ht' : 0 + 1 + (hp - 0) ≤ hp + 1 := by omega
  have hg' : g + 1 + (hp - g) ≤ hp + 1 := by omega
  have hd' : d0 ≤ hp + 1 := by omega
  set e1 : ℕ := hp + 1 - P.h N - P.q N with he1
  set e2 : ℕ := hp + 1 - P.h N with he2
  set m1 : ℕ := P.h N + hp - (t + 1) with hm1
  set m5 : ℕ := t + 1 - P.b N with hm5
  set m6 : ℕ := P.L N - 5 * p with hm6
  have hHL : P.H N = P.L N + P.g N + P.h N := by simp [Parameters.H, Parameters.C]
  let V := virtL2 u u2 y1 y2 ktop k0 0 g d0 ht' hg' hd'
  let A : Submodule (ZMod p) (ZPar p hp) := LinearMap.ker V
  let Φbig : ZPar p hp →ₗ[ZMod p] (degreeLT (ZMod p) e1 × degreeLT (ZMod p) e2 ×
      (Fin m1 → ZMod p) × (Fin (t + 1) → ZMod p) × (Fin m5 → ZMod p) × (Fin m6 → ZMod p)) :=
    (valL p (hp + 1) e1 ∘ₗ LinearMap.fst _ _ _).prod
      ((valL p (hp + 1) e2 ∘ₗ ((LinearMap.fst _ _ _) ∘ₗ (LinearMap.snd _ _ _))).prod
        ((mainMo P N p hp K (t + 1) m1 u u2 y1 y2).prod
          ((zM P N p hp K (t + 1) 2 u u2 y1 y2).prod
            ((c0M P N p hp K m5 u u2 y1 y2).prod
              (c5M P N p hp K (g + P.h N) m6 u u2 y1 y2)))))
  let Φ : A →ₗ[ZMod p] (degreeLT (ZMod p) e1 × degreeLT (ZMod p) e2 ×
      (Fin m1 → ZMod p) × (Fin (t + 1) → ZMod p) × (Fin m5 → ZMod p) × (Fin m6 → ZMod p)) := Φbig.comp A.subtype
  let ξ : A →ₗ[ZMod p] (Fin ((hp + 1) + (hp + 1)) → Fin (K + K) → ZMod p) :=
    (atomLin u u2 y1 y2).comp A.subtype
  have hzc : ∀ a : A, ZCons P N p 0 (Sdata u u2 a.1.1 a.1.2.1) (Adata y1 y2 a.1.2.2.1 a.1.2.2.2) :=
    fun a => zcons_of_virt2 u u2 y1 y2 ktop k0 0 g d0 (Nat.zero_le _) hg0 hd1 hd2 ht' hg'
      (fun d hd hn => by
        rcases hvtop d hd hn with h | h
        · exact Or.inl h
        · exact Or.inr h) hvtopm hv0 hoth hoth' a.1 a.2
  have hA0 : ∀ a : A, ∀ d : Fin (hp + 1), (d : ℕ) = 0 → ∀ k,
      Adata y1 y2 a.1.2.2.1 a.1.2.2.2 d k = 0 := by
    intro a d hd k
    have : d = 0 := Fin.ext hd
    subst this
    simp [Adata, Aext]
  have hξ : ∀ a : A, ξ a ∈ (zSys P N p hp2 K (hp + 1) hD).dom := fun a =>
    mergeData_mem _ _ (hzc a) (hA0 a)
  have hξi : Function.Injective ξ :=
    (atomLin_injective u u2 y1 y2 hind1 hind2).comp Subtype.val_injective
  let sF : LinearMap.ker Φ →ₗ[ZMod p] (ZMod p → ZMod p) :=
    LinearMap.pi fun x : ZMod p => (foldL P N p hp (rOf p (P.H N) x)).comp
      (A.subtype.comp (LinearMap.ker Φ).subtype)
  have hker : ∀ u' : LinearMap.ker Φ, Φbig u'.1.1 = 0 := fun u' => by
    have := u'.2
    rw [LinearMap.mem_ker] at this
    exact this
  have hV : ∀ u' : LinearMap.ker Φ, V u'.1.1 = 0 := fun u' => u'.1.2
  have hVf : ∀ u' : LinearMap.ker Φ, virtL u u2 y1 y2 ktop k0 0 g ht' hg' u'.1.1 = 0 :=
    fun u' => congrArg Prod.fst (hV u')
  have hdv1 : ∀ u' : LinearMap.ker Φ, ((X - 1) ^ e1 : (ZMod p)[X]) ∣ tpoly u'.1.1.1 := fun u' =>
    (valL_eq_zero_iff e1 _).mp (congrArg Prod.fst (hker u'))
  have hdv2 : ∀ u' : LinearMap.ker Φ, ((X - 1) ^ e2 : (ZMod p)[X]) ∣ tpoly u'.1.1.2.1 := fun u' =>
    (valL_eq_zero_iff e2 _).mp (congrArg (fun z => z.2.1) (hker u'))
  have hpoly : ∀ u' : LinearMap.ker Φ, ∃ G : (ZMod p)[X],
      G.degree < ((p - (p - P.q N) : ℕ) : WithBot ℕ) ∧ ∀ x, sF u' x = G.eval x := by
    intro u'
    have hv := val_Pi (P := P) (N := N) u'.1.1.1 e1 (hdv1 u')
    have hex : P.h N + (p - 1) / 2 + e1 = p - P.q N := by omega
    rw [hex] at hv
    obtain ⟨G, hG, hGe⟩ := flat_value_poly (P := P) (N := N) hp2 hhp u'.1.1.1 (p - P.q N)
      (by omega) hv (P.H N)
    exact ⟨G, hG, fun x => by simp [sF, foldL_apply, hGe x]⟩
  have hresp : ∀ (u' : LinearMap.ker Φ) (j : ℕ), P.b N ≤ j → j < P.L N →
      (zSys P N p hp2 K (hp + 1) hD).resp (j / p) (j % p) (ξ u'.1) = sF u' (j : ZMod p) := by
    intro u' j hj1 hj2
    have hp0 : 0 < p := (Fact.out : p.Prime).pos
    have hJell : j / p * p + j % p = j := Nat.div_add_mod' j p
    have hl : j % p < p := Nat.mod_lt _ hp0
    have hh := hker u'
    have c3 : mainMo P N p hp K (t + 1) m1 u u2 y1 y2 u'.1.1 = 0 :=
      congrArg (fun z => z.2.2.1) hh
    have c6 : zM P N p hp K (t + 1) 2 u u2 y1 y2 u'.1.1 = 0 :=
      congrArg (fun z => z.2.2.2.1) hh
    have c8 : c0M P N p hp K m5 u u2 y1 y2 u'.1.1 = 0 :=
      congrArg (fun z => z.2.2.2.2.1) hh
    have c9 : c5M P N p hp K (g + P.h N) m6 u u2 y1 y2 u'.1.1 = 0 :=
      congrArg (fun z => z.2.2.2.2.2) hh
    have hvt := virt_top u u2 y1 y2 ktop k0 0 g ht' hg' u'.1.1 (hVf u')
    have hv0' := virt_zero u u2 y1 y2 ktop k0 0 g ht' hg' u'.1.1 (hVf u')
    have hmain : ∀ r, t + 1 ≤ r → r < P.h N + hp →
        dotc (fun c => vv p K (P.H N) u u2 y1 y2 2 c - vv p K (P.H N) u u2 y1 y2 1 c)
          (piSeq P N p u'.1.1.1) (piSeq P N p u'.1.1.2.1) (laSeq P N p (Aext u'.1.1.2.2.1))
          (laSeq P N p (Aext u'.1.1.2.2.2)) p r = 0 := by
      intro r h1 h2
      have := congrFun c3 ⟨r - (t + 1), by omega⟩
      rw [mainMo_apply] at this
      have e : t + 1 + (r - (t + 1)) = r := by omega
      simp only [e] at this
      exact this
    have hds : ∀ r, t + 1 ≤ r → g + P.h N ≤ r → r < P.h N + max g 0 → r < P.h N + hp →
        dotc (vv p K (P.H N) u u2 y1 y2 4) (piSeq P N p u'.1.1.1) (piSeq P N p u'.1.1.2.1)
          (laSeq P N p (Aext u'.1.1.2.2.1)) (laSeq P N p (Aext u'.1.1.2.2.2)) p r = 0 := by
      intro r h0 h1 h2 h3x
      have : max g 0 = g := by omega
      omega
    have hd0 : ∀ r : ℕ, t + 1 ≤ r → r < p → ((P.b N : ℤ) ≤ ((P.H N : ℤ) - 1 - 4 * p) - (r : ℤ)) →
        (fuV p K (P.H N) u 0 ((4 : ℕ) : ℤ) - 1) *
            (piSeq P N p u'.1.1.1 r + piSeq P N p u'.1.1.1 (r + p)) +
          dotc (vv p K (P.H N) u u2 y1 y2 0) (piSeq P N p u'.1.1.1) (piSeq P N p u'.1.1.2.1)
            (laSeq P N p (Aext u'.1.1.2.2.1)) (laSeq P N p (Aext u'.1.1.2.2.2)) p r = 0 := by
      intro r h1 h2 h3x
      rw [hcell0.fold0, sub_self, zero_mul, zero_add]
      by_cases hrr : P.h N + hp ≤ r
      · obtain ⟨a1, a2, a3, a4, a5⟩ := seq_zero_hi hp2 hphp hhp u'.1.1.1 u'.1.1.2.1
          u'.1.1.2.2.1 u'.1.1.2.2.2 e2 (hdv2 u') (by omega) r h2 hrr
        exact dotc_zero_of_seq _ _ _ _ _ _ _ a1 a3 a4 a5
      · exact dot_J0 hcell0 _ _ _ _ r (hmain r h1 (by omega))
    have hY : ∀ r, r ≤ t →
        dotc (zz p K (P.H N) u u2 y1 y2 2) (piSeq P N p u'.1.1.1) (piSeq P N p u'.1.1.2.1)
          (laSeq P N p (Aext u'.1.1.2.2.1)) (laSeq P N p (Aext u'.1.1.2.2.2)) 0 r = 0 := by
      intro r hr
      have := congrFun c6 ⟨r, by omega⟩
      rw [zM_apply] at this
      exact this
    have hC1 : ∀ r, r ≤ t →
        dotc (zz p K (P.H N) u u2 y1 y2 1) (piSeq P N p u'.1.1.1) (piSeq P N p u'.1.1.2.1)
          (laSeq P N p (Aext u'.1.1.2.2.1)) (laSeq P N p (Aext u'.1.1.2.2.2)) 0 r = 0 := by
      intro r hr
      rw [dotc_congr _ (fun c => 2 * zz p K (P.H N) u u2 y1 y2 2 c) _ _ _ _ _ _
        (fun c hc' => hcap1.zr1 c hc'), dotc_smul, hY r hr]; ring
    have hC0 : ∀ r, r ≤ t → P.b N + r ≤ t →
        (fuV p K (P.H N) u 0 ((4 : ℕ) : ℤ) - 1) *
            (piSeq P N p u'.1.1.1 r + piSeq P N p u'.1.1.1 (r + p)) +
          dotc (zz p K (P.H N) u u2 y1 y2 0) (piSeq P N p u'.1.1.1) (piSeq P N p u'.1.1.2.1)
            (laSeq P N p (Aext u'.1.1.2.2.1)) (laSeq P N p (Aext u'.1.1.2.2.2)) 0 r = 0 := by
      intro r hr hbr
      have := congrFun c8 ⟨r, by omega⟩
      rw [c0M_apply] at this
      exact this
    have hC5 : ∀ r, r ≤ t → P.g N + P.h N ≤ r →
        (fuV p K (P.H N) u 5 ((4 : ℕ) : ℤ) - 1) *
            (piSeq P N p u'.1.1.1 r + piSeq P N p u'.1.1.1 (r + p)) +
          dotc (zz p K (P.H N) u u2 y1 y2 5) (piSeq P N p u'.1.1.1) (piSeq P N p u'.1.1.2.1)
            (laSeq P N p (Aext u'.1.1.2.2.1)) (laSeq P N p (Aext u'.1.1.2.2.2)) 0 r = 0 := by
      intro r hr hgr
      have hi : r - (g + P.h N) < m6 := by omega
      have := congrFun c9 ⟨r - (g + P.h N), hi⟩
      rw [c5M_apply] at this
      have e : g + P.h N + (r - (g + P.h N)) = r := by omega
      simp only [e] at this
      exact this
    have hfl := flatCap5 hp2 hphp hhp u u2 y1 y2 hcell hcap h3 u'.1.1.1 u'.1.1.2.1 u'.1.1.2.2.1
      u'.1.1.2.2.2 e2 (hdv2 u') (by omega) 0 g t hvt hv0' hmain hds hd0 hY hC1 hC0 hC5
      hHt ht hb hgP hD hemax (j % p) hl (j / p) (by omega) (by omega)
    have hval : ((j : ℕ) : ZMod p).val = j % p := ZMod.val_natCast p j
    have e : rOf p (P.H N) (j : ZMod p) = (((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ)) % p).toNat := by
      unfold rOf; rw [hval]
    show (zSys P N p hp2 K (hp + 1) hD).resp (j / p) (j % p)
        (mergeData (Sdata u u2 u'.1.1.1 u'.1.1.2.1) (Adata y1 y2 u'.1.1.2.2.1 u'.1.1.2.2.2)) = _
    rw [hfl]
    have h2 : sF u' (j : ZMod p) = piSeq P N p u'.1.1.1 (rOf p (P.H N) (j : ZMod p)) +
        piSeq P N p u'.1.1.1 (rOf p (P.H N) (j : ZMod p) + p) := by
      simp only [sF, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        foldL_apply]
    rw [h2, e]
  have key := (zSys P N p hp2 K (hp + 1) hD).slot_nullity_jflat hP hN hp2 hH2 ξ hξ hξi Φ
    (p - P.q N) sF hpoly hresp
  have hA : finrank (ZMod p) (ZPar p hp) - ((hp - 0) + (hp - g) + d0) ≤ finrank (ZMod p) A := by
    have := finrank_ker_ge_codom V
    simpa [finrank_ZPar, Module.finrank_prod, Module.finrank_fin_fun] using this
  haveI : Module.Finite (ZMod p) (degreeLT (ZMod p) e1) :=
    Module.Finite.equiv (degreeLTEquiv (ZMod p) e1).symm
  haveI : Module.Finite (ZMod p) (degreeLT (ZMod p) e2) :=
    Module.Finite.equiv (degreeLTEquiv (ZMod p) e2).symm
  have hR : finrank (ZMod p) (LinearMap.range Φ) ≤
      e1 + e2 + m1 + (t + 1) + m5 + m6 := by
    have := Submodule.finrank_le (LinearMap.range Φ)
    simp only [Module.finrank_prod, finrank_degreeLT, Module.finrank_fin_fun] at this
    omega
  rw [finrank_ZPar] at hA
  omega

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
