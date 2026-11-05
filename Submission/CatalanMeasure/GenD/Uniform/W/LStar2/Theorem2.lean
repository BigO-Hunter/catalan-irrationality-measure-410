module
public import Submission.CatalanMeasure.GenD.Uniform.W.LStar2.Chain
public import Submission.CatalanMeasure.GenD.Uniform.W.LStar.Count
@[expose] public section
set_option Elab.async false

/-!
# Theorem L\* for all `h`: `lstar2Kap ≤ ν` (lane G6d)

For `h ≤ p` put `m = p - h`.  A residue `ℓ'` carries a *window* when the residues
`ℓ = ℓ' - m, …, ℓ'` have the same digit set and `(p-1)/2 ≤ e0(ℓ)`.  Then, on the common kernel of
the J-flatness maps of the residues `< ℓ'`, the `m`-th difference identity (`window_resp`) puts the
flatness map of `ℓ'` into the span of the `|NV(ℓ)|` block vectors.  For `h > p` the old bound
`lrank` is used.
-/

namespace CatalanMeasure.GenD.Uniform.W.LStar2
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Tier3
  CatalanMeasure.GenD.Uniform.W.LStar
noncomputable section
variable {P : Parameters} {N p : ℕ}

/-- Window predicate at the residue `ℓ`. -/
def wOK (P : Parameters) (N p ℓ : ℕ) : Prop :=
  P.h N ≤ p ∧ p - P.h N ≤ ℓ ∧ (p - 1) / 2 ≤ idxRes (P.H N) p (ℓ - (p - P.h N)) ∧
    ∀ s ≤ p - P.h N, jSet P N p (ℓ - (p - P.h N) + s) = jSet P N p ℓ

open Classical in
/-- The rank bound at the residue `ℓ` (windows for `h ≤ p`, `lrank` for `h > p`). -/
def lrank2 (P : Parameters) (N p ℓ : ℕ) : ℕ :=
  if wOK P N p ℓ then min (nvSet P N p (ℓ - (p - P.h N))).card ((jSet P N p ℓ).card - 1)
  else if P.h N ≤ p then (jSet P N p ℓ).card - 1 else lrank P N p ℓ

/-- **The Theorem L\* bound for all `h`.** -/
def lstar2Kap (P : Parameters) (N p : ℕ) : ℕ :=
  P.n N - ∑ ℓ ∈ Finset.range p, lrank2 P N p ℓ - (p - P.q N)

variable [Fact p.Prime]

/-- The J-flatness map at the residue `ℓ`. -/
abbrev PhiL (P : Parameters) (N p : ℕ) [Fact p.Prime] (ℓ : ZMod p) :
    (Fin (P.n N) → ZMod p) →ₗ[ZMod p] (↥(jSet P N p ℓ.val) → ZMod p) :=
  flatPhi (P := P) (N := N) (p := p) LinearMap.id (fun ℓ => jSet P N p ℓ.val)
    (fun ℓ => j0of P N p ℓ.val) ℓ

/-- Common kernel of the flatness maps of the residues `< t`. -/
def Kc (P : Parameters) (N p : ℕ) [Fact p.Prime] : ℕ → Submodule (ZMod p) (Fin (P.n N) → ZMod p)
  | 0 => ⊤
  | t + 1 => Kc P N p t ⊓ LinearMap.ker (PhiL P N p (t : ZMod p))

theorem Kc_le_ker : ∀ {s t : ℕ}, t < s → Kc P N p s ≤ LinearMap.ker (PhiL P N p (t : ZMod p))
  | s + 1, t, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h1 | h1
    · exact (inf_le_left : Kc P N p s ⊓ _ ≤ Kc P N p s).trans (Kc_le_ker h1)
    · subst h1
      exact inf_le_right

/-- The block vector of `k`. -/
def Gvec (P : Parameters) (N p ℓ0 t : ℕ) [Fact p.Prime] (k : ℤ) :
    ↥(jSet P N p (t : ZMod p).val) → ZMod p :=
  fun J => Sresp (P.H N) p ℓ0 J.1 k -
    Sresp (P.H N) p ℓ0 (j0of P N p (t : ZMod p).val) k

theorem blk_mem_nvSet (hp2 : p ≠ 2) (ℓ : ℕ) (r : Fin (P.n N))
    (hr : (blkD p (P.g N) r.val).natAbs + idxRes (P.H N) p ℓ < p + (P.h N - p)) :
    blkK p (P.g N) r.val ∈ nvSet P N p ℓ := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hrd := blk_eq hp2 (P.g N) r.val
  have hdle := blkD_natAbs_le hp2 (P.g N) r.val
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp0
  have hrn := r.isLt
  have he0 := idxRes_lt hp0 (P.H N) ℓ
  have hD : ((lD P N p ℓ : ℕ) : ℤ) = p - 1 - idxRes (P.H N) p ℓ + (P.h N - p : ℕ) := by
    unfold lD; push_cast [Nat.cast_sub (by omega : idxRes (P.H N) p ℓ ≤ p - 1)]
    rw [Nat.cast_sub (by omega : 1 ≤ p)]; push_cast; ring
  unfold nvSet
  rw [Finset.mem_Icc]
  set k := blkK p (P.g N) r.val
  set d := blkD p (P.g N) r.val
  have hdD : d.natAbs ≤ lD P N p ℓ := by unfold lD; omega
  have hdz : -(lD P N p ℓ : ℤ) ≤ d ∧ d ≤ lD P N p ℓ := by omega
  constructor
  · have h1 : -k * p ≤ (P.g N : ℤ) + lD P N p ℓ := by nlinarith
    have := Int.le_ediv_of_mul_le hpz h1
    linarith
  · have h1 : k * p ≤ (P.n N : ℤ) - P.g N - 1 + lD P N p ℓ := by nlinarith
    exact Int.le_ediv_of_mul_le hpz h1

/-- **The window step.**  On `Kc t` the flatness map of the residue `t` lies in the span of the
block vectors of `NV(t - m)`. -/
theorem step_win (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {t : ℕ} (ht : t < p) (hw : wOK P N p t) (c : Fin (P.n N) → ZMod p) (hc : c ∈ Kc P N p t) :
    PhiL P N p (t : ZMod p) c ∈ Submodule.span (ZMod p)
      ((((nvSet P N p (t - (p - P.h N))).image
        (Gvec P N p (t - (p - P.h N)) t) : Finset _) :
          Set (↥(jSet P N p (t : ZMod p).val) → ZMod p))) := by
  classical
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨hh, hmt, he, hjs⟩ := hw
  have hv : ((t : ℕ) : ZMod p).val = t := ZMod.val_cast_of_lt ht
  set m := p - P.h N with hm
  set ℓ0 := t - m with hℓ0
  have hℓ0m : ℓ0 + m = t := by omega
  have hLH : P.L N ≤ P.H N := by simp only [Parameters.H, Parameters.C]; omega
  -- the function identity
  have hfun : PhiL P N p (t : ZMod p) c = ∑ r : Fin (P.n N),
      (c r * (qOne p 0 (blkD p (P.g N) r.val)).coeff (idxRes (P.H N) p ℓ0)) •
        Gvec P N p ℓ0 t (blkK p (P.g N) r.val) := by
    funext ⟨J, hJmem⟩
    have hJt : J ∈ jSet P N p t := by rw [hv] at hJmem; exact hJmem
    have hJs : ∀ s ≤ m, J ∈ jSet P N p (ℓ0 + s) := fun s hs => by rw [hjs s hs]; exact hJt
    have hj0eq : ∀ s ≤ m, j0of P N p (ℓ0 + s) = j0of P N p t := fun s hs => by
      unfold j0of; rw [hjs s hs]
    have hJ0t : j0of P N p t ∈ jSet P N p t := j0of_mem ⟨J, hJt⟩
    have hJ0s : ∀ s ≤ m, j0of P N p t ∈ jSet P N p (ℓ0 + s) := fun s hs => by
      rw [hjs s hs]; exact hJ0t
    have hbd : ∀ {J' : ℕ} {ℓ' : ℕ}, J' ∈ jSet P N p ℓ' → J' * p + ℓ' < P.H N := fun h => by
      have := (mem_jSet hp0).mp h; omega
    have hw1 := window_resp hP hN hp2 hH (m := m) (ℓ := ℓ0) (J := J) (by omega) (by omega)
      (fun s hs => by have := hbd (hJs s hs); omega) he c
    have hw2 := window_resp hP hN hp2 hH (m := m) (ℓ := ℓ0) (J := j0of P N p t) (by omega)
      (by omega) (fun s hs => by have := hbd (hJ0s s hs); omega) he c
    -- vanishing for s < m
    have hvan : ∀ s ∈ Finset.range m, uResp P N p (J * p + (ℓ0 + s)) c =
        uResp P N p (j0of P N p t * p + (ℓ0 + s)) c := by
      intro s hs
      have hs' := Finset.mem_range.mp hs
      have hker := Kc_le_ker (P := P) (N := N) (p := p) (s := t) (t := ℓ0 + s) (by omega) hc
      have hz : ((ℓ0 + s : ℕ) : ZMod p).val = ℓ0 + s := ZMod.val_cast_of_lt (by omega)
      have hmem : J ∈ jSet P N p ((ℓ0 + s : ℕ) : ZMod p).val := by
        rw [hz]; exact hJs s (by omega)
      have h0 : uResp P N p (J * p + ((ℓ0 + s : ℕ) : ZMod p).val) c -
          uResp P N p (j0of P N p ((ℓ0 + s : ℕ) : ZMod p).val * p +
            ((ℓ0 + s : ℕ) : ZMod p).val) c = 0 := by
        have := congrFun (LinearMap.mem_ker.mp hker) ⟨J, hmem⟩
        simpa [PhiL, flatPhi] using this
      rw [hz, hj0eq s (by omega)] at h0
      exact sub_eq_zero.mp h0
    have hdiff : (∑ s ∈ Finset.range (m + 1), (wc m s : ZMod p) *
          uResp P N p (J * p + (ℓ0 + s)) c) -
        (∑ s ∈ Finset.range (m + 1), (wc m s : ZMod p) *
          uResp P N p (j0of P N p t * p + (ℓ0 + s)) c) =
        uResp P N p (J * p + t) c - uResp P N p (j0of P N p t * p + t) c := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_congr rfl fun s hs => by rw [hvan s hs]]
      rw [wc_self, hℓ0m]
      push_cast
      ring
    have hlhs : PhiL P N p (t : ZMod p) c ⟨J, hJmem⟩ =
        uResp P N p (J * p + t) c - uResp P N p (j0of P N p t * p + t) c := by
      simp only [PhiL, flatPhi, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.sub_apply,
        LinearMap.id_apply]
      rw [hv]
    rw [hlhs, ← hdiff, hw1, hw2, Finset.sum_apply]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [Pi.smul_apply, Gvec, smul_eq_mul, hv]
    ring
  rw [hfun]
  refine Submodule.sum_mem _ fun r _ => ?_
  by_cases hD : (blkD p (P.g N) r.val).natAbs + idxRes (P.H N) p ℓ0 < p + (P.h N - p)
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    rw [Finset.mem_coe, Finset.mem_image]
    exact ⟨blkK p (P.g N) r.val, blk_mem_nvSet hp2 ℓ0 r hD, rfl⟩
  · have hdle := blkD_natAbs_le hp2 (P.g N) r.val
    have he0 := idxRes_lt hp0 (P.H N) ℓ0
    rw [qOne_coeff_eq_zero (dh := 0) hp2 he0 hdle (by omega), mul_zero, zero_smul]
    exact Submodule.zero_mem _

#print axioms step_win
end
end CatalanMeasure.GenD.Uniform.W.LStar2
