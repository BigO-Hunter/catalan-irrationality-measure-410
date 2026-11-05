module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZMain
@[expose] public section
set_option Elab.async false

/-!
# Theorem Z, Law_H(4), no cap (`η < p`): `zH_le_nullity`
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem zH_le_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH2 : P.H N < p ^ 2)
    {hp : ℕ} (hphp : hp = (p - 1) / 2) {K : ℕ} (u u2 y1 y2 : Fin K → ZMod p)
    {μ2 μ3 ν ρ : ZMod p} {ktop k0 : Fin K}
    (hcell : CellHyp p K (P.H N) u u2 y1 y2 μ2 μ3 ν ρ ktop k0)
    (hind1 : ∀ (c1 c2 : ZMod p), (∀ k, c1 * u k + c2 * u2 k = 0) → c1 = 0 ∧ c2 = 0)
    (hind2 : ∀ (c1 c2 : ZMod p), (∀ k, c1 * y1 k + c2 * y2 k = 0) → c1 = 0 ∧ c2 = 0)
    (hhp : P.h N + hp ≤ p - 1) (hqh : P.q N + P.h N ≤ hp)
    (eta : ℕ) (hHeta : P.H N = eta + 1 + 4 * p) (hη1 : P.h N + hp ≤ eta + 1) (hη2 : eta < p)
    (hb : P.b N < p) (rt g : ℕ) (hrt : rt ≤ hp) (hg0 : g ≤ hp) (hgP : g = P.g N)
    (hvtop : ∀ d : ℕ, d ≤ hp → ¬ InRange P N ((((0 : ℤ) + (ktop : ℕ)) * p) + d) → rt < d)
    (hv0 : ∀ d : ℕ, d ≤ hp → ¬ InRange P N ((((0 : ℤ) + (k0 : ℕ)) * p) - d) → g < d)
    (hoth : ∀ (k : Fin K) (d : ℕ), d ≤ hp → k ≠ ktop →
      InRange P N ((((0 : ℤ) + (k : ℕ)) * p) + d))
    (hoth' : ∀ (k : Fin K) (d : ℕ), d ≤ hp → k ≠ k0 →
      InRange P N ((((0 : ℤ) + (k : ℕ)) * p) - d)) :
    (4 * hp + 2) - ((hp - rt) + (hp - g)) -
        ((hp + 1 - P.h N - P.q N) + (hp + 1 - P.h N) + (P.h N + hp) + (p - 1 - eta) +
          (eta + 1 - P.b N) + (min (max g rt) hp - g)) ≤ nullity P N p := by
  have hq0 : 0 < P.q N := Nat.mul_pos hP.2.2.1 hN
  have hodd : p = 2 * hp + 1 := by have := p_odd_half hp2; omega
  have hD : hp + 1 ≤ (p - 1) / 2 + 1 := by omega
  have hemax : P.h N + (p - 1) + (hp + 1) ≤ 2 * p := by omega
  have ht : rt + 1 + (hp - rt) ≤ hp + 1 := by omega
  have hg' : g + 1 + (hp - g) ≤ hp + 1 := by omega
  set e1 : ℕ := hp + 1 - P.h N - P.q N with he1
  set e2 : ℕ := hp + 1 - P.h N with he2
  set m3 : ℕ := eta + 1 - P.b N with hm3
  set m4 : ℕ := min (max g rt) hp - g with hm4
  let V := virtL u u2 y1 y2 ktop k0 rt g ht hg'
  let A : Submodule (ZMod p) (ZPar p hp) := LinearMap.ker V
  let Φbig : ZPar p hp →ₗ[ZMod p] (degreeLT (ZMod p) e1 × degreeLT (ZMod p) e2 ×
      (Fin (P.h N + hp) → ZMod p) × (Fin (p - 1 - eta) → ZMod p) × (Fin m3 → ZMod p) ×
      (Fin m4 → ZMod p)) :=
    (valL p (hp + 1) e1 ∘ₗ LinearMap.fst _ _ _).prod
      ((valL p (hp + 1) e2 ∘ₗ ((LinearMap.fst _ _ _) ∘ₗ (LinearMap.snd _ _ _))).prod
        ((mainM P N p hp K u u2 y1 y2).prod
          ((wM P N p hp eta (p - 1 - eta)).prod
            ((d0M P N p hp K m3 u u2 y1 y2).prod (dsM P N p hp K g m4 u u2 y1 y2)))))
  let Φ : A →ₗ[ZMod p] (degreeLT (ZMod p) e1 × degreeLT (ZMod p) e2 ×
      (Fin (P.h N + hp) → ZMod p) × (Fin (p - 1 - eta) → ZMod p) × (Fin m3 → ZMod p) ×
      (Fin m4 → ZMod p)) := Φbig.comp A.subtype
  -- the atom map
  let ξ : A →ₗ[ZMod p] (Fin ((hp + 1) + (hp + 1)) → Fin (K + K) → ZMod p) :=
    (atomLin u u2 y1 y2).comp A.subtype
  have hzc : ∀ a : A, ZCons P N p 0 (Sdata u u2 a.1.1 a.1.2.1) (Adata y1 y2 a.1.2.2.1 a.1.2.2.2) :=
    fun a => zcons_of_virt u u2 y1 y2 ktop k0 rt g hrt hg0 ht hg' hvtop hv0 hoth hoth' a.1 a.2
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
  -- the flat value
  let sF : LinearMap.ker Φ →ₗ[ZMod p] (ZMod p → ZMod p) :=
    LinearMap.pi fun x : ZMod p => (foldL P N p hp (rOf p (P.H N) x)).comp
      (A.subtype.comp (LinearMap.ker Φ).subtype)
  -- kernel facts
  have hker : ∀ u' : LinearMap.ker Φ, Φbig u'.1.1 = 0 := fun u' => by
    have := u'.2
    rw [LinearMap.mem_ker] at this
    exact this
  have hV : ∀ u' : LinearMap.ker Φ, V u'.1.1 = 0 := fun u' => u'.1.2
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
    have hc3 : mainM P N p hp K u u2 y1 y2 u'.1.1 = 0 := congrArg (fun z => z.2.2.1) hh
    have hc4 : wM P N p hp eta (p - 1 - eta) u'.1.1 = 0 := congrArg (fun z => z.2.2.2.1) hh
    have hc5 : d0M P N p hp K m3 u u2 y1 y2 u'.1.1 = 0 := congrArg (fun z => z.2.2.2.2.1) hh
    have hc6 : dsM P N p hp K g m4 u u2 y1 y2 u'.1.1 = 0 := congrArg (fun z => z.2.2.2.2.2) hh
    have hvt := virt_top u u2 y1 y2 ktop k0 rt g ht hg' u'.1.1 (hV u')
    have hv0' := virt_zero u u2 y1 y2 ktop k0 rt g ht hg' u'.1.1 (hV u')
    have hmain : ∀ r, 0 ≤ r → r < P.h N + hp →
        dotc (fun c => vv p K (P.H N) u u2 y1 y2 2 c - vv p K (P.H N) u u2 y1 y2 1 c)
          (piSeq P N p u'.1.1.1) (piSeq P N p u'.1.1.2.1) (laSeq P N p (Aext u'.1.1.2.2.1))
          (laSeq P N p (Aext u'.1.1.2.2.2)) p r = 0 := by
      intro r _ hr
      have := congrFun hc3 ⟨r, hr⟩
      rw [mainM_apply] at this
      exact this
    have hds : ∀ r, 0 ≤ r → g + P.h N ≤ r → r < P.h N + max g rt → r < P.h N + hp →
        dotc (vv p K (P.H N) u u2 y1 y2 4) (piSeq P N p u'.1.1.1) (piSeq P N p u'.1.1.2.1)
          (laSeq P N p (Aext u'.1.1.2.2.1)) (laSeq P N p (Aext u'.1.1.2.2.2)) p r = 0 := by
      intro r _ h1 h2 h3
      have hj : r - (g + P.h N) < m4 := by omega
      have := congrFun hc6 ⟨r - (g + P.h N), hj⟩
      rw [dsM_apply] at this
      have e : g + P.h N + (r - (g + P.h N)) = r := by omega
      simp only [e] at this
      exact this
    have hd0 : ∀ r : ℕ, 0 ≤ r → r < p → ((P.b N : ℤ) ≤ ((P.H N : ℤ) - 1 - 4 * p) - (r : ℤ)) →
        (fuV p K (P.H N) u 0 ((4 : ℕ) : ℤ) - 1) *
            (piSeq P N p u'.1.1.1 r + piSeq P N p u'.1.1.1 (r + p)) +
          dotc (vv p K (P.H N) u u2 y1 y2 0) (piSeq P N p u'.1.1.1) (piSeq P N p u'.1.1.2.1)
            (laSeq P N p (Aext u'.1.1.2.2.1)) (laSeq P N p (Aext u'.1.1.2.2.2)) p r = 0 := by
      intro r _ _ hr
      have hr' : r < m3 := by omega
      have := congrFun hc5 ⟨r, hr'⟩
      rw [d0M_apply] at this
      exact this
    have hw : ∀ r : ℕ, ((P.H N : ℤ) - 1 - 4 * p) < (r : ℤ) → r < p →
        piSeq P N p u'.1.1.1 r = 0 := by
      intro r h1 h2
      have hj : r - (eta + 1) < p - 1 - eta := by omega
      have := congrFun hc4 ⟨r - (eta + 1), hj⟩
      rw [wM_apply] at this
      have e : eta + 1 + (r - (eta + 1)) = r := by omega
      simp only [e] at this
      exact this
    have hfl := flatH hp2 hphp hhp u u2 y1 y2 hcell u'.1.1.1 u'.1.1.2.1 u'.1.1.2.2.1 u'.1.1.2.2.2
      e2 (hdv2 u') (by omega) rt g hvt hv0' hmain hds hd0 hw (by omega) (by omega) hb hgP hD hemax
      (j % p) hl (j / p) (by omega) (by omega)
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
  have hA : finrank (ZMod p) (ZPar p hp) - ((hp - rt) + (hp - g)) ≤ finrank (ZMod p) A := by
    have := finrank_ker_ge_codom V
    simpa [finrank_ZPar] using this
  haveI : Module.Finite (ZMod p) (degreeLT (ZMod p) e1) :=
    Module.Finite.equiv (degreeLTEquiv (ZMod p) e1).symm
  haveI : Module.Finite (ZMod p) (degreeLT (ZMod p) e2) :=
    Module.Finite.equiv (degreeLTEquiv (ZMod p) e2).symm
  have hR : finrank (ZMod p) (LinearMap.range Φ) ≤ e1 + e2 + (P.h N + hp) + (p - 1 - eta) + m3 + m4 := by
    have := Submodule.finrank_le (LinearMap.range Φ)
    simpa [finrank_degreeLT, Module.finrank_prod, Module.finrank_fin_fun, add_assoc] using this
  rw [finrank_ZPar] at hA
  have hmin : e1 + e2 + (P.h N + hp) + (p - 1 - eta) + m3 + m4 =
      (hp + 1 - P.h N - P.q N) + (hp + 1 - P.h N) + (P.h N + hp) + (p - 1 - eta) +
        (eta + 1 - P.b N) + (min (max g rt) hp - g) := rfl
  omega


end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
