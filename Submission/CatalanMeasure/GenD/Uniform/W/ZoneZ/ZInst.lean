module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZCellInst2
@[expose] public section
set_option Elab.async false

/-!
# Design-level hypotheses for `K = 4` (Law_H)

For `n = 3p + rtop + 1 + g` and `d ≤ hp < p`, the only pair members that are not actual rows are
the `+` members of block 3 beyond `rtop` and the `-` members of block 0 beyond `g`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial OAI.InternalCatalan CatalanMeasure.Parametric CatalanMeasure.GenD.Uniform.Prefix
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem design_vtop {hp rt rtop : ℕ} (hphp : hp < p) (hn : P.n N = 3 * p + rtop + 1 + P.g N)
    (hrt : rt = min rtop hp) (d : ℕ) (hd : d ≤ hp)
    (h : ¬ InRange P N ((((0 : ℤ) + ((⟨3, by omega⟩ : Fin 4) : ℕ)) * p) + d)) : rt < d := by
  unfold InRange at h
  simp only [Fin.val_mk, zero_add] at h
  push_neg at h
  omega

theorem design_v0 {hp : ℕ} (hphp : hp < p) (hn : P.g N < P.n N) (d : ℕ) (hd : d ≤ hp)
    (h : ¬ InRange P N ((((0 : ℤ) + ((⟨0, by omega⟩ : Fin 4) : ℕ)) * p) - d)) : P.g N < d := by
  unfold InRange at h
  simp only [Fin.val_mk] at h
  push_neg at h
  omega

theorem design_oth {hp rtop : ℕ} (hphp : hp < p) (hn : P.n N = 3 * p + rtop + 1 + P.g N)
    (k : Fin 4) (d : ℕ) (hd : d ≤ hp) (hk : k ≠ (⟨3, by omega⟩ : Fin 4)) :
    InRange P N ((((0 : ℤ) + (k : ℕ)) * p) + d) := by
  unfold InRange
  have hk3 : (k : ℕ) < 3 := by
    have := k.isLt
    by_contra hc
    exact hk (Fin.ext (by simp; omega))
  have : (k : ℕ) * p + p ≤ 2 * p + p := by nlinarith
  have h1 : ((k : ℕ) : ℤ) * p ≤ 2 * p := by
    have : (k : ℕ) ≤ 2 := by omega
    exact_mod_cast (by nlinarith : (k : ℕ) * p ≤ 2 * p)
  simp only [zero_add]
  constructor
  · have : (0 : ℤ) ≤ ((k : ℕ) : ℤ) * p := by positivity
    omega
  · omega

theorem design_oth' {hp rtop : ℕ} (hphp : hp < p) (hn : P.n N = 3 * p + rtop + 1 + P.g N)
    (k : Fin 4) (d : ℕ) (hd : d ≤ hp) (hk : k ≠ (⟨0, by omega⟩ : Fin 4)) :
    InRange P N ((((0 : ℤ) + (k : ℕ)) * p) - d) := by
  unfold InRange
  have hk0 : 1 ≤ (k : ℕ) := by
    by_contra hc
    exact hk (Fin.ext (by simp; omega))
  have hk3 := k.isLt
  have h1 : (p : ℤ) ≤ ((k : ℕ) : ℤ) * p := by
    have : p ≤ (k : ℕ) * p := Nat.le_mul_of_pos_left p (by omega)
    exact_mod_cast this
  have h2 : ((k : ℕ) : ℤ) * p ≤ 3 * p := by
    have : (k : ℕ) ≤ 3 := by omega
    exact_mod_cast (by nlinarith : (k : ℕ) * p ≤ 3 * p)
  simp only [zero_add]
  constructor
  · omega
  · omega

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
