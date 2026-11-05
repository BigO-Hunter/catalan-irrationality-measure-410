module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger3.MTGen
public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger.Instance

@[expose] public section
set_option Elab.async false

/-!
# Closed-form lower bounds for the MT (1) cells (lane G5f)

`mtBoth_ge`, `mtPlus_ge`, `mtMinus_ge`: for a digit `s`, block window `(k0, K)` with in-blocks
`[a, b)` (at most `t` out-blocks), offsets `(D1, e0)`, a digit-set bound `card <= c` and a
multiplier `m0 + c <= K + 1`, the nullity bound `mtLB3.kap N p` is at least the displayed closed
form.  All hypotheses are linear in `N`, `p`, `D1`, `e0` once the numerals are inserted.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger3
open CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.W.Thin
open CatalanMeasure.GenD.Uniform.W.SlotsT CatalanMeasure.GenD.Uniform.Bank540.Ledger
noncomputable section

theorem mtBoth_ge {N p : ℕ} [Fact p.Prime] {s K D1 e0 a b t c m0 : ℕ} {k0 : ℤ}
    (hp0 : 0 < p) (hs : s * p ≤ design.H N) (hk0 : hpKmin design N p ≤ k0)
    (hk1 : k0 ≤ hpKmax design N p) (hK : K ≤ mtKmax design N p) (hD : D1 ≤ (p - 1) / 2)
    (he : e0 ≤ D1) (hok : mtOK design N p s D1 e0)
    (hcard : (mtJJ design N p s D1 e0).card ≤ c) (hm : m0 + c ≤ K + 1) (hm0 : m0 ≤ K)
    (hL : -(design.g N : ℤ) ≤ (k0 + a) * p - D1)
    (hR : (k0 + b - 1) * p + D1 < (design.n N : ℤ) - design.g N) (ht : a + (K - b) ≤ t) :
    (D1 - e0) * m0 + (D1 + 1 - e0) * m0 - t * (2 * D1 + 1) -
        (p - design.q N - (design.h N + (p - 1) / 2 - p)) ≤ (mtLB3 design adm).kap N p := by
  have h := mtVal2_le_mtLB3 design adm N p s K D1 e0 k0 ((Nat.le_div_iff_mul_le hp0).mpr hs)
    hk0 hk1 hK hD he
  refine le_trans ?_ h
  unfold mtVal2
  rw [if_pos hok]
  have hm' : m0 ≤ min K (K + 1 - (mtJJ design N p s D1 e0).card) :=
    le_min hm0 (by omega)
  have hmix := mixMiss_le (K := K) (D1 := D1) (k0 := k0) (a := a) (b := b) (t := t) hL hR ht
  have e1 := Nat.mul_le_mul_left (D1 - e0) hm'
  have e2 := Nat.mul_le_mul_left (D1 + 1 - e0) hm'
  generalize (D1 - e0) * min K (K + 1 - (mtJJ design N p s D1 e0).card) = x1 at *
  generalize (D1 + 1 - e0) * min K (K + 1 - (mtJJ design N p s D1 e0).card) = x2 at *
  omega

theorem mtPlus_ge {N p : ℕ} [Fact p.Prime] {s K D1 e0 a b t c m0 : ℕ} {k0 : ℤ}
    (hp0 : 0 < p) (hs : s * p ≤ design.H N) (hk0 : hpKmin design N p ≤ k0)
    (hk1 : k0 ≤ hpKmax design N p) (hK : K ≤ mtKmax design N p) (hD : D1 ≤ (p - 1) / 2)
    (he : e0 ≤ D1) (hok : mtOK design N p s D1 e0)
    (hcard : (mtJJ design N p s D1 e0).card ≤ c) (hm : m0 + c ≤ K + 1) (hm0 : m0 ≤ K)
    (hL : -(design.g N : ℤ) ≤ (k0 + a) * p - D1)
    (hR : (k0 + b - 1) * p + D1 < (design.n N : ℤ) - design.g N) (ht : a + (K - b) ≤ t) :
    (D1 + 1 - e0) * m0 - (D1 + 1) * t -
        (p - design.q N - (design.h N + (p - 1) / 2 - p)) ≤ (mtLB3 design adm).kap N p := by
  have h := mtPlusVal_le_mtLB3 design adm N p s K D1 e0 k0 ((Nat.le_div_iff_mul_le hp0).mpr hs)
    hk0 hk1 hK hD he
  refine le_trans ?_ h
  unfold mtPlusVal
  rw [if_pos hok]
  have hm' : m0 ≤ min K (K + 1 - (mtJJ design N p s D1 e0).card) :=
    le_min hm0 (by omega)
  have hv := tpVirt_le (K := K) (D1 := D1) (k0 := k0) (a := a) (b := b) (t := t) hL hR ht
  have e2 := Nat.mul_le_mul_left (D1 + 1 - e0) hm'
  generalize (D1 + 1 - e0) * min K (K + 1 - (mtJJ design N p s D1 e0).card) = x2 at *
  omega

theorem mtMinus_ge {N p : ℕ} [Fact p.Prime] {s K D1 e0 a b t c m0 : ℕ} {k0 : ℤ}
    (hp0 : 0 < p) (hs : s * p ≤ design.H N) (hk0 : hpKmin design N p ≤ k0)
    (hk1 : k0 ≤ hpKmax design N p) (hK : K ≤ mtKmax design N p) (hD : D1 ≤ (p - 1) / 2)
    (he : e0 ≤ D1) (hok : mtMinusOK design N p s D1 e0)
    (hcard : (mtJJ design N p s D1 e0).card ≤ c) (hm : m0 + c ≤ K + 1) (hm0 : m0 ≤ K)
    (hL : -(design.g N : ℤ) ≤ (k0 + a) * p - D1)
    (hR : (k0 + b - 1) * p + D1 < (design.n N : ℤ) - design.g N) (ht : a + (K - b) ≤ t) :
    (D1 - e0) * m0 - D1 * t - (p - design.q N - design.h N) ≤ (mtLB3 design adm).kap N p := by
  have h := mtMinusVal_le_mtLB3 design adm N p s K D1 e0 k0 ((Nat.le_div_iff_mul_le hp0).mpr hs)
    hk0 hk1 hK hD he
  refine le_trans ?_ h
  unfold mtMinusVal
  rw [if_pos hok]
  have hm' : m0 ≤ min K (K + 1 - (mtJJ design N p s D1 e0).card) :=
    le_min hm0 (by omega)
  have hv := virtCount_le (K := K) (D1 := D1) (k0 := k0) (a := a) (b := b) (t := t) hL hR ht
  have e1 := Nat.mul_le_mul_left (D1 - e0) hm'
  generalize (D1 - e0) * min K (K + 1 - (mtJJ design N p s D1 e0).card) = x1 at *
  omega

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger3
