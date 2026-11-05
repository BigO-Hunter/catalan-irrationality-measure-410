module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.RawResponse
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Uniform.Prefix

/-- The exact quotient/residue of the common H-1 frame, with no lost -1 offset. -/
theorem intrinsic_window_decomposition (H p ell : ℕ) (hell : ell<H) :
    (H:ℤ)-1-ell=(((H-1-ell)%p:ℕ):ℤ)+(((H-1-ell)/p:ℕ):ℤ)*p := by
  have hn : H-1-ell=(H-1-ell)%p+((H-1-ell)/p)*p := by
    simpa only [Nat.mul_comm] using (Nat.mod_add_div (H-1-ell) p).symm
  have hc : ((H-1-ell:ℕ):ℤ)=(H:ℤ)-1-ell := by omega
  rw [←hc]
  exact_mod_cast hn
 theorem intrinsic_window_bound (H p ell : ℕ) (hell : ell<H) :
    (H-1-ell)/p+1≤H := by
  have h := Nat.div_le_self (H-1-ell) p
  omega

 theorem intrinsic_window_P_index (H p ell v : ℕ) (hell : ell<H) :
    (H:ℤ)-1-ell-((v:ℤ)-1)*p=
      (((H-1-ell)%p:ℕ):ℤ)+((((H-1-ell)/p:ℕ):ℤ)+1-v)*p := by
  rw [intrinsic_window_decomposition H p ell hell]
  ring

 theorem intrinsic_window_D_index (H p ell v : ℕ) (hell : ell<H) :
    (H:ℤ)-1-ell-(v:ℤ)*p=
      (((H-1-ell)%p:ℕ):ℤ)+((((H-1-ell)/p:ℕ):ℤ)-v)*p := by
  rw [intrinsic_window_decomposition H p ell hell]
  ring

/-- The residue is exactly eta-ell in Fp, as used by the unique B prefix lift. -/
theorem intrinsic_residue_eta (H p ell : ℕ) [Fact p.Prime] (hell : ell<H) :
    (((H-1-ell)%p:ℕ):ZMod p)=(((H-1)%p:ℕ):ZMod p)-(ell:ZMod p) := by
  rw [ZMod.natCast_mod,ZMod.natCast_mod,Nat.cast_sub (show ell≤H-1 by omega)]

#print axioms intrinsic_residue_eta
end CatalanMeasure.GenD.Uniform.Prefix

