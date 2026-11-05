module

public import Submission.CatalanMeasure.GenD.ResBase

@[expose] public section

/-!
# Row-by-row inverse certificate and the C3 assembly (generic)
-/

namespace CatalanMeasure.GenD
namespace ResInv

open OAI.InternalCatalan CatalanMeasure.Parametric ResRec ResCheck ResBase

variable {l : ℕ}

/-- One row `r` of the check `(B0 + σ B1) * B = 1`, `Bt` the transposed inverse. -/
def chkInvRow (l n σ : ℕ) (rows Bt : List (List ℕ)) (r : ℕ) : Bool :=
  allLt n fun k =>
    dotS σ (nthL rows r) (nthL rows (r + 1)) (nthL Bt k) % l == (if r == k then 1 else 0) % l

def chkInvLen (n : ℕ) (rows Bt : List (List ℕ)) : Bool :=
  allLt (n + 1) (fun r => (nthL rows r).length == n) && allLt n (fun k => (nthL Bt k).length == n)

theorem chkInv_sound {n : ℕ} (σ : ℕ) (σ' : ZMod l) (hσ : (σ : ZMod l) = σ')
    {rows Bt : List (List ℕ)} (hlen : chkInvLen n rows Bt = true)
    (h : ∀ r, r < n → chkInvRow l n σ rows Bt r = true) :
    CertMod.caseMat n l rows σ' * Matrix.of (fun j k : Fin n => CertMod.entry l Bt k j) = 1 := by
  simp only [chkInvLen, Bool.and_eq_true] at hlen
  obtain ⟨hl1, hl2⟩ := hlen
  apply CertMod.mul_eq_one_of_rows
  intro r k
  have hr := r.isLt
  have hk := k.isLt
  have hA := by simpa using allLt_spec hl1 r.val (by omega)
  have hA1 := by simpa using allLt_spec hl1 (r.val + 1) (by omega)
  have hB := by simpa using allLt_spec hl2 k.val hk
  have hc := modc (l := l) (allLt_spec (h r.val hr) k.val hk)
  rw [dotS_cast σ _ _ _ n hA hA1 hB, hσ] at hc
  simp only [CertMod.caseMat, Matrix.mul_apply, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun j => (CertMod.entry l rows r.val j + σ' * CertMod.entry l rows (r.val + 1) j) * CertMod.entry l Bt k.val j) n]
  have e1 : ∀ j, (nth (nthL rows r.val) j : ZMod l) = CertMod.entry l rows r.val j := fun j => tg_cast' rows r.val j
  have e2 : ∀ j, (nth (nthL rows (r.val + 1)) j : ZMod l) = CertMod.entry l rows (r.val + 1) j := fun j => tg_cast' rows (r.val + 1) j
  have e3 : ∀ j, (nth (nthL Bt k.val) j : ZMod l) = CertMod.entry l Bt k.val j := fun j => tg_cast' Bt k.val j
  simp only [e1, e2, e3] at hc
  rw [hc]
  by_cases hrk : r = k
  · subst hrk; simp
  · have : (r.val == k.val) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro h'; exact hrk (Fin.ext h')
    simp [hrk, this]

theorem c3_of_certificate' (P : Parameters) (ℓ : ℕ) [Fact ℓ.Prime] (rows : List (List ℕ))
    (B0 Bp Bm : Matrix (Fin P.n0) (Fin P.n0) (ZMod ℓ))
    (hE : ∀ (r k : ℕ) (hk : k < P.n0), r < P.n0 + 1 →
      baseFilteredContraction P ℓ r ⟨k, hk⟩ = CertMod.entry ℓ rows r k)
    (h0 : CertMod.caseMat P.n0 ℓ rows 0 * B0 = 1)
    (hp : CertMod.caseMat P.n0 ℓ rows 1 * Bp = 1)
    (hm : CertMod.caseMat P.n0 ℓ rows (-1) * Bm = 1) :
    (baseB0Residue P ℓ).det ≠ 0 ∧
      (baseB0Residue P ℓ + baseB1Residue P ℓ).det ≠ 0 ∧
      (baseB0Residue P ℓ - baseB1Residue P ℓ).det ≠ 0 := by
  have key : ∀ σ : ZMod ℓ,
      baseB0Residue P ℓ + σ • baseB1Residue P ℓ = CertMod.caseMat P.n0 ℓ rows σ := by
    intro σ
    ext r k
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, CertMod.caseMat, Matrix.of_apply,
      baseB0Residue, baseB1Residue]
    rw [hE r.val k.val k.isLt (by omega), hE (r.val + 1) k.val k.isLt (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · have := key 0
    rw [zero_smul, add_zero] at this
    rw [this]; exact CertMod.det_ne_zero_of_mul_eq_one h0
  · have := key 1
    rw [one_smul] at this
    rw [this]; exact CertMod.det_ne_zero_of_mul_eq_one hp
  · have := key (-1)
    rw [neg_one_smul, ← sub_eq_add_neg] at this
    rw [this]; exact CertMod.det_ne_zero_of_mul_eq_one hm

end ResInv
end CatalanMeasure.GenD
