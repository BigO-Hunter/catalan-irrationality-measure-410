module
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Prod
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Uniform.Prefix

/-- All centers and both members of every noncentral pair. -/
abbrev RowLabels (blocks half : Nat) := Fin (blocks+1) ⊕ (Fin blocks × Fin half × Bool)
def labelBlock {b h : Nat} : RowLabels b h → Nat
  | .inl k => k.val
  | .inr (k,_,_) => k.val
def labelResidue {b h : Nat} (p : Nat) : RowLabels b h → Nat
  | .inl _ => 0
  | .inr (_,j,true) => j.val+1
  | .inr (_,j,false) => p-j.val-1
def labelPosition {b h : Nat} (p : Nat) (i : RowLabels b h) : Nat :=
  labelBlock i*p+labelResidue p i

theorem labelResidue_lt {b h p : Nat} (hp : p=2*h+1) (i : RowLabels b h) :
    labelResidue p i<p := by
  rcases i with k|⟨k,j,s⟩
  · simp [labelResidue]; omega
  · cases s <;> simp only [labelResidue] <;> have := j.is_lt <;> omega

theorem labelPosition_bounds {b h p : Nat} (hp : p=2*h+1) (i : RowLabels b h) :
    labelPosition p i<b*p+1 := by
  have hs := labelResidue_lt hp i
  rcases i with k|⟨k,j,s⟩
  · have hb : k.val≤b := by have := k.is_lt; omega
    have hm := Nat.mul_le_mul_right p hb
    dsimp [labelPosition,labelBlock,labelResidue]
    omega
  · have hb : k.val+1≤b := k.is_lt
    have hm := Nat.mul_le_mul_right p hb
    rw [Nat.add_mul,Nat.one_mul] at hm
    change k.val*p+labelResidue p (.inr (k,j,s) : RowLabels b h)<b*p+1
    omega

theorem labelPosition_mod {b h p : Nat} (hp : p=2*h+1) (i : RowLabels b h) :
    labelPosition p i%p=labelResidue p i := by
  simp [labelPosition,Nat.add_mod,Nat.mod_eq_of_lt (labelResidue_lt hp i)]
theorem labelPosition_div {b h p : Nat} (hp : p=2*h+1) (i : RowLabels b h) :
    labelPosition p i/p=labelBlock i := by
  rw [labelPosition,Nat.add_comm,Nat.add_mul_div_right _ _ (show 0<p by omega),
    Nat.div_eq_of_lt (labelResidue_lt hp i),Nat.zero_add]

theorem labelPosition_injective {b h p : Nat} (hp : p=2*h+1) :
    Function.Injective (labelPosition (b := b) (h := h) p) := by
  intro x y he
  have hr := congrArg (fun n => n%p) he
  have hb := congrArg (fun n => n/p) he
  rw [labelPosition_mod hp,labelPosition_mod hp] at hr
  rw [labelPosition_div hp,labelPosition_div hp] at hb
  rcases x with i|⟨k,j,s⟩ <;> rcases y with i'|⟨k',j',s'⟩
  · exact congrArg Sum.inl (Fin.ext hb)
  · cases s' <;> simp only [labelResidue] at hr <;> have := j'.is_lt <;> omega
  · cases s <;> simp only [labelResidue] at hr <;> have := j.is_lt <;> omega
  · have hk : k=k' := Fin.ext hb
    subst k'
    cases s <;> cases s' <;> simp only [labelResidue] at hr
    · have hj : j=j' := Fin.ext (by have := j.is_lt; have := j'.is_lt; omega)
      subst j'; rfl
    · have := j.is_lt; have := j'.is_lt; omega
    · have := j.is_lt; have := j'.is_lt; omega
    · have hj : j=j' := Fin.ext (by omega)
      subst j'; rfl

/-- Explicit bijection to EVERY enlarged physical row, including both outside
centers. No small or virtual row family is dropped. -/
noncomputable def fullRowIndexEquiv (b h p : Nat) (hp : p=2*h+1) :
    RowLabels b h ≃ Fin (b*p+1) := by
  let f : RowLabels b h → Fin (b*p+1) := fun i => ⟨labelPosition p i,labelPosition_bounds hp i⟩
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).mpr
  constructor
  · intro x y he
    exact labelPosition_injective hp (congrArg Fin.val he)
  · simp only [RowLabels,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    rw [hp]
    ring

#print axioms fullRowIndexEquiv
end CatalanMeasure.GenD.Uniform.Prefix

