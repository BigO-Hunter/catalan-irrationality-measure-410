module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.ThetaRep
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Geom146
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts.Rows
@[expose] public section
set_option Elab.async false

/-!
# Integer coefficient tables of the real profile of the four-point frame (L0146 window)

`pd146 : ProfData` gives the `Y`-coefficients of `Gy(e_c), Ty(e_c)` for the 44 coordinates (blocks `κ = -1..8`
of `A,C` types, `F`/`E` parts, centre, two zero graph coordinates), and `monoProfile_realises` shows that the
profile of `monoData` realises it on the window.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts5
open CatalanMeasure.GenD.D58.Odd CatalanMeasure.Parametric CatalanMeasure.GenD.Uniform.W.Slots Polynomial Polynomial.Chebyshev CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts
  CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O CatalanMeasure.GenD.Uniform.W.Prof.Pilot146
noncomputable section

/-- Coefficients of the Chebyshev polynomial `U_n`. -/
def uc : ℕ → ℕ → ℤ
  | 0, i => if i = 0 then 1 else 0
  | 1, i => if i = 1 then 2 else 0
  | n + 2, i => 2 * (match i with | 0 => 0 | j + 1 => uc (n + 1) j) - uc n i

/-- Coefficients of `U_n`, `n : ℤ`. -/
def ucz : ℤ → ℕ → ℤ
  | .ofNat n, i => uc n i
  | .negSucc 0, _ => 0
  | .negSucc (m + 1), i => - uc m i

def shl (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | i + 1 => f i

/-- coefficients of `(X - 1) * f`. -/
def mY (f : ℕ → ℤ) (i : ℕ) : ℤ := shl f i - f i
/-- coefficients of `(1 + X) * f`. -/
def mO (f : ℕ → ℤ) (i : ℕ) : ℤ := f i + shl f i

def vcz (n : ℤ) (i : ℕ) : ℤ := ucz n i - ucz (n - 1) i
def wcz (n : ℤ) (i : ℕ) : ℤ := ucz n i + ucz (n - 1) i

/-- `Gy` and `Ty` coefficient functions of the block coordinate `4 k + u` (`κ = k - 1`). -/
def blockG (k u : ℕ) : ℕ → ℤ :=
  let κ : ℤ := -1 + (k : ℤ)
  let g := if u < 2 then mO (vcz κ) else mY (wcz κ)
  if u % 2 = 1 then mY g else g
def blockT (k u : ℕ) : ℕ → ℤ :=
  let κ : ℤ := -1 + (k : ℤ)
  let t := if u < 2 then wcz κ else vcz κ
  if u % 2 = 1 then mY t else t

def centG (z : ℕ) : ℕ → ℤ := if z = 0 then shl (fun i => if i = 0 then 1 else 0) else
  mY (shl (fun i => if i = 0 then 1 else 0))
def centT (z : ℕ) : ℕ → ℤ := if z = 0 then ucz (-2) else mY (ucz (-2))

def pd146 : ProfData where
  g := fun c i => if c < 40 then blockG (c / 4) (c % 4) i else if c < 42 then centG (c - 40) i else 0
  t := fun c i => if c < 40 then blockT (c / 4) (c % 4) i else if c < 42 then centT (c - 40) i else 0

/-- Polynomial `q` has coefficient function `f`. -/
def Co {R : Type*} [CommRing R] (f : ℕ → ℤ) (q : R[X]) : Prop := ∀ i, q.coeff i = (f i : R)

variable {R : Type*} [CommRing R]

theorem Co_shl {f : ℕ → ℤ} {q : R[X]} (h : Co f q) : Co (shl f) (X * q) := by
  intro i; cases i with
  | zero => simp [shl]
  | succ j => rw [coeff_X_mul]; simpa [shl] using h j

theorem Co_add {f g : ℕ → ℤ} {q r : R[X]} (hq : Co f q) (hr : Co g r) : Co (fun i => f i + g i) (q + r) := by
  intro i; rw [coeff_add, hq, hr]; push_cast; rfl
theorem Co_sub {f g : ℕ → ℤ} {q r : R[X]} (hq : Co f q) (hr : Co g r) : Co (fun i => f i - g i) (q - r) := by
  intro i; rw [coeff_sub, hq, hr]; push_cast; rfl

theorem Co_mY {f : ℕ → ℤ} {q : R[X]} (h : Co f q) : Co (mY f) ((X - 1) * q) := by
  have := Co_sub (Co_shl h) h
  intro i; have := this i; rw [sub_mul, one_mul]; simpa [mY] using this
theorem Co_mO {f : ℕ → ℤ} {q : R[X]} (h : Co f q) : Co (mO f) ((1 + X) * q) := by
  have := Co_add h (Co_shl h)
  intro i; have := this i; rw [add_mul, one_mul]; simpa [mO] using this

theorem Co_U (n : ℕ) : Co (uc n) (U R (n : ℤ)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => intro i; simp [uc, U_zero, coeff_one, eq_comm]
    | 1 =>
      intro i
      have : U R ((1 : ℕ) : ℤ) = C 2 * X := by
        rw [Nat.cast_one, U_one, map_ofNat]
      rw [this, coeff_C_mul, coeff_X]
      by_cases h : i = 1 <;> simp [uc, h, eq_comm]
    | n + 2 =>
      have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      have e : U R ((n + 2 : ℕ) : ℤ) = C 2 * (X * U R ((n + 1 : ℕ) : ℤ)) - U R (n : ℤ) := by
        have := U_add_two R (n : ℤ)
        push_cast; rw [this, map_ofNat]; ring
      intro i
      rw [e, coeff_sub, coeff_C_mul, h0 i]
      cases i with
      | zero => simp [uc]
      | succ j => rw [coeff_X_mul, h1 j]; simp [uc]

theorem Co_Uz (n : ℤ) : Co (ucz n) (U R n) := by
  match n with
  | .ofNat m => exact Co_U m
  | .negSucc 0 => intro i; have : U R (Int.negSucc 0) = 0 := by simpa using U_neg_one R
                  simp [this, ucz]
  | .negSucc (m + 1) =>
    have e : U R (Int.negSucc (m + 1)) = - U R (m : ℤ) := by
      have := U_neg_sub_two R (m : ℤ)
      rw [← this]; congr 1; omega
    intro i; rw [e, coeff_neg, (Co_U m) i]; simp [ucz]

theorem Co_Uz_sub (n : ℤ) : Co (vcz n) (U R n - U R (n - 1)) := Co_sub (Co_Uz n) (Co_Uz _)
theorem Co_Uz_add (n : ℤ) : Co (wcz n) (U R n + U R (n - 1)) := Co_add (Co_Uz n) (Co_Uz _)

/-! ### Realisation by the profile of `monoProfile` -/

section real
variable {p : ℕ} [Fact p.Prime]

/-- Decomposition of a packet coordinate into a profile coordinate kind. -/
def ckOf (k : Fin (10 * 4 + 2 + 2)) : CK 10 2 :=
  if h : k.val < 40 then Sum.inl (⟨k.val / 4, by omega⟩, ⟨k.val % 4, by omega⟩)
  else if h2 : k.val < 42 then Sum.inr (Sum.inl ⟨k.val - 40, by omega⟩)
  else Sum.inr (Sum.inr ⟨k.val - 42, by omega⟩)

theorem ckEquiv_eq : ∀ k : Fin (10 * 4 + 2 + 2),
    ckEquiv (rfl : (10 * 4 + 2 + 2 : ℕ) = 10 * 4 + 2 + 2) k = ckOf k := by
  decide +kernel

local notation "Fp" => ZMod p

theorem sumProf_single {K b ex : ℕ} (hK : K = b * 4 + 2 + ex) (G : CK b ex → Fp[X]) (k : Fin K) :
    sumProf hK G (Pi.single k 1) = G (ckEquiv hK k) := by
  rw [sumProf_apply, Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem Co_one : Co (fun i => if i = 0 then (1 : ℤ) else 0) (1 : Fp[X]) := by
  intro i; rw [coeff_one]; by_cases h : i = 0 <;> simp [h, eq_comm]

theorem Co_T : Co (shl (fun i => if i = 0 then (1 : ℤ) else 0)) (T Fp (-1)) := by
  rw [T_neg_one, ← mul_one X]; exact Co_shl Co_one

theorem Co_U2 : Co (ucz (-2)) (U Fp (-1 - 1)) := by
  have : (-1 : ℤ) - 1 = -2 := by norm_num
  rw [this]; exact Co_Uz _

theorem Co_right {f : ℕ → ℤ} {q : Fp[X]} (h : Co f q) : Co (mY f) (q * (X - 1)) := by
  rw [mul_comm]; exact Co_mY h

theorem realises_abs {b K : ℕ} (hb : b = 10) (hK : K = b * 4 + 2 + 2) :
    pd146.Realises (⟨sumProf hK (uCoefs (-1) 0), sumProf hK (tCoefs (-1) 0)⟩ : Prof p K) := by
  subst hb; subst hK
  intro k i
  simp only [sumProf_single]
  rw [show ckEquiv _ k = ckOf k from ckEquiv_eq k]
  by_cases h : k.val < 40
  · have hc : ckOf k = Sum.inl (⟨k.val / 4, by omega⟩, ⟨k.val % 4, by omega⟩) := by simp [ckOf, h]
    rw [hc]
    have hu : k.val % 4 = 0 ∨ k.val % 4 = 1 ∨ k.val % 4 = 2 ∨ k.val % 4 = 3 := by omega
    have hg : pd146.g k i = blockG (k.val / 4) (k.val % 4) i := by simp [pd146, h]
    have ht : pd146.t k i = blockT (k.val / 4) (k.val % 4) i := by simp [pd146, h]
    rw [hg, ht]
    rcases hu with hu | hu | hu | hu
    · simp only [tCoefs, uCoefs, coefC, hu, blockG, blockT]
      simp only [pow_zero, mul_one]
      exact ⟨(Co_mO (Co_Uz_sub _)) i, (Co_Uz_add _) i⟩
    · simp only [tCoefs, uCoefs, coefC, hu, blockG, blockT]
      simp only [pow_zero, mul_one]
      exact ⟨(Co_right (Co_mO (Co_Uz_sub _))) i, (Co_right (Co_Uz_add _)) i⟩
    · simp only [tCoefs, uCoefs, coefC, hu, blockG, blockT]
      simp only [pow_zero, mul_one]
      exact ⟨(Co_mY (Co_Uz_add _)) i, (Co_Uz_sub _) i⟩
    · simp only [tCoefs, uCoefs, coefC, hu, blockG, blockT]
      simp only [pow_zero, mul_one]
      exact ⟨(Co_right (Co_mY (Co_Uz_add _))) i, (Co_right (Co_Uz_sub _)) i⟩
  · by_cases h2 : k.val < 42
    · have hc : ckOf k = Sum.inr (Sum.inl ⟨k.val - 40, by omega⟩) := by simp [ckOf, h, h2]
      rw [hc]
      have hz : k.val = 40 ∨ k.val = 41 := by omega
      rcases hz with hz | hz
      · have e1 : pd146.g k i = centG 0 i := by simp [pd146, h, h2, hz]
        have e2 : pd146.t k i = centT 0 i := by simp [pd146, h, h2, hz]
        rw [e1, e2]
        simp only [tCoefs, uCoefs, coefC, hz]
        simp only [pow_zero, mul_one, centG, centT, if_true]
        exact ⟨Co_T i, Co_U2 i⟩
      · have e1 : pd146.g k i = centG 1 i := by simp [pd146, h, h2, hz]
        have e2 : pd146.t k i = centT 1 i := by simp [pd146, h, h2, hz]
        rw [e1, e2]
        simp only [tCoefs, uCoefs, coefC, hz]
        simp only [pow_zero, mul_one, centG, centT]
        exact ⟨(Co_right Co_T) i, (Co_right Co_U2) i⟩
    · have hc : ckOf k = Sum.inr (Sum.inr ⟨k.val - 42, by omega⟩) := by simp [ckOf, h, h2]
      rw [hc]
      simp [tCoefs, uCoefs, coefC, pd146, h, h2]

theorem monoProfile_realises {N : ℕ} (hW : Win N p) {K : ℕ} (hK : K = bN design N p * 4 + 2 + 2) :
    pd146.Realises (monoProfile design N p hK) := by
  have h0 := realises_abs (p := p) (geom_b hW) hK
  have e1 : k0N design N p = -1 := geom_k0 hW
  have e2 : design.h N / p = 0 := geom_hdiv hW
  unfold monoProfile
  rw [e1, e2]
  exact h0

end real

end
end CatalanMeasure.GenD.Uniform.W.Charts5
