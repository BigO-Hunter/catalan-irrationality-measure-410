module
public import Submission.CatalanMeasure.Parametric.PairedPrimeColumns
public import Submission.OAI.NumberTheory.Catalan.Estimates.OddPhysicalCombination
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Finset Matrix
open scoped BigOperators
noncomputable section

def lowerPairSet (P : Parameters) (N p : ℕ) : Finset ℕ :=
  Ico (max (P.b N) (P.H N-2*p)) (min (min p (P.L N-p)) (P.A N))
def lowerHighSet (P : Parameters) (N p : ℕ) : Finset ℕ :=
  (lowerPairSet P N p).image (fun ell =>p+ell)
def lowerRetainedSet (P : Parameters) (N p : ℕ) : Finset ℕ :=
  Ico (P.b N) (P.L N) \ lowerHighSet P N p
def lowerPairCount (P : Parameters) (N p : ℕ) : ℕ :=
  min (min p (P.L N-p)) (P.A N)-max (P.b N) (P.H N-2*p)
def lowerPrimeLoss (P : Parameters) (N p : ℕ) : ℕ :=
  2*P.n N-(lowerPairCount P N p-P.q N)

theorem lowerPairSet_bounds {P : Parameters} {N p ell : ℕ} (he : ell∈lowerPairSet P N p) :
    P.b N ≤ ell ∧ ell<p ∧ P.H N ≤ ell+2*p ∧ p+ell<P.L N ∧ ell<P.A N :=by
  simp only [lowerPairSet,mem_Ico,max_le_iff,lt_min_iff] at he
  omega

theorem lowerPairSet_mem_pool {P : Parameters} {N p ell : ℕ} (he : ell∈lowerPairSet P N p) :
    ell∈Ico (P.b N) (P.L N) :=by
  have hh :=lowerPairSet_bounds he
  exact mem_Ico.mpr ⟨hh.1,by omega⟩

theorem lowerHighSet_subset_pool (P : Parameters) (N p : ℕ) :
    lowerHighSet P N p ⊆ Ico (P.b N) (P.L N) :=by
  intro j hj
  obtain ⟨ell,he,rfl⟩ :=mem_image.mp hj
  have hh :=lowerPairSet_bounds he
  exact mem_Ico.mpr ⟨by omega,hh.2.2.2.1⟩

theorem lowerPairSet_mem_retained {P : Parameters} {N p ell : ℕ} (he : ell∈lowerPairSet P N p) :
    ell∈lowerRetainedSet P N p :=by
  refine mem_sdiff.mpr ⟨lowerPairSet_mem_pool he,?_⟩
  intro hj
  obtain ⟨k,hk,heq⟩ :=mem_image.mp hj
  have hh :=lowerPairSet_bounds he
  omega

theorem lowerHighSet_sub_mem_pair {P : Parameters} {N p j : ℕ} (hj : j∈lowerHighSet P N p) :
    j-p∈lowerPairSet P N p ∧ p+(j-p)=j :=by
  obtain ⟨ell,he,rfl⟩ :=mem_image.mp hj
  simpa using And.intro he (rfl : p+ell=p+ell)

theorem lowerHighSet_card (P : Parameters) (N p : ℕ) :
    (lowerHighSet P N p).card=(lowerPairSet P N p).card :=by
  apply card_image_of_injective
  intro i j hij
  change p+i=p+j at hij
  omega

theorem lowerPairSet_card (P : Parameters) (N p : ℕ) :
    (lowerPairSet P N p).card=lowerPairCount P N p :=by
  rw [lowerPairSet,Nat.card_Ico]
  rfl

theorem lowerRetainedSet_card (P : Parameters) (N p : ℕ) :
    (lowerRetainedSet P N p).card=P.n N+P.q N-lowerPairCount P N p :=by
  rw [lowerRetainedSet,card_sdiff_of_subset (lowerHighSet_subset_pool P N p),
    lowerHighSet_card,lowerPairSet_card,Nat.card_Ico]
  unfold Parameters.L
  omega

theorem lowerPairCount_le_pool (P : Parameters) (N p : ℕ) :
    lowerPairCount P N p ≤ P.n N+P.q N :=by
  have hh :=card_le_card (lowerHighSet_subset_pool P N p)
  rw [lowerHighSet_card,lowerPairSet_card,Nat.card_Ico] at hh
  unfold Parameters.L at hh
  omega

abbrev lowerRetainedSize (P : Parameters) (N p : ℕ) :=Fintype.card ↥(lowerRetainedSet P N p)
abbrev lowerPairedSize (P : Parameters) (N p : ℕ) :=Fintype.card ↥(lowerPairSet P N p)
abbrev lowerPhysicalIndex (P : Parameters) (N p : ℕ) :=
  oddPhysicalIndex (lowerRetainedSize P N p) (lowerPairedSize P N p) 0

def lowerRetainedTag {P : Parameters} {N p : ℕ} (j : ↥(lowerRetainedSet P N p)) :
    lowerPhysicalIndex P N p :=Sum.inl ((Fintype.equivFin _) j)
def lowerPairedTag {P : Parameters} {N p : ℕ} (j : ↥(lowerPairSet P N p)) :
    lowerPhysicalIndex P N p :=Sum.inr (Sum.inl ((Fintype.equivFin _) j))

def lowerRetainedVector (P : Parameters) (z : ℚ) (N p : ℕ)
    (j : Fin (lowerRetainedSize P N p)) (r : Fin (P.n N)) : ℚ :=
  (p:ℚ)^2*rawEntryRat P z N r.val (((Fintype.equivFin ↥(lowerRetainedSet P N p)).symm j).val)
def lowerPairedVector (P : Parameters) (z : ℚ) (N p : ℕ)
    (j : Fin (lowerPairedSize P N p)) (r : Fin (P.n N)) : ℚ :=
  let ell :=((Fintype.equivFin ↥(lowerPairSet P N p)).symm j).val
  (p:ℚ)*(rawEntryRat P z N r.val ell+rawEntryRat P z N r.val (p+ell))
def lowerPhysicalColumn (P : Parameters) (z : ℚ) (N p : ℕ)
    (j : lowerPhysicalIndex P N p) (r : Fin (P.n N)) : ℚ :=
  oddPhysicalColumn p (lowerRetainedVector P z N p) (lowerPairedVector P z N p)
    (fun j : Fin 0 =>Fin.elim0 j) (fun j : Fin 0 =>Fin.elim0 j) (fun j : Fin 0 =>Fin.elim0 j) j r

theorem lowerPhysicalColumn_retained {P : Parameters} {N p : ℕ} [hp : Fact p.Prime]
    (z : ℚ) (j : ↥(lowerRetainedSet P N p)) (r : Fin (P.n N)) :
    lowerPhysicalColumn P z N p (lowerRetainedTag j) r=rawEntryRat P z N r.val j.val :=by
  have hpq : (p:ℚ)≠0 :=by exact_mod_cast hp.out.ne_zero
  simp only [lowerPhysicalColumn,lowerRetainedTag,oddPhysicalColumn,lowerRetainedVector,Equiv.symm_apply_apply]
  field_simp [hpq]

theorem lowerPhysicalColumn_paired {P : Parameters} {N p : ℕ} [hp : Fact p.Prime]
    (z : ℚ) (ell : ↥(lowerPairSet P N p)) (r : Fin (P.n N)) :
    lowerPhysicalColumn P z N p (lowerPairedTag ell) r=
      rawEntryRat P z N r.val ell.val+rawEntryRat P z N r.val (p+ell.val) :=by
  have hpq : (p:ℚ)≠0 :=by exact_mod_cast hp.out.ne_zero
  simp only [lowerPhysicalColumn,lowerPairedTag,oddPhysicalColumn,lowerPairedVector,Equiv.symm_apply_apply]
  field_simp [hpq]

theorem lowerRetainedVector_den_ne_zero {P : Parameters} {N p : ℕ} [Fact p.Prime]
    (hp2 : p≠2) (hH : P.H N<p^2) (z : ℚ) (hz : (((p:ℚ)*z).den : ZMod p)≠0)
    (j : Fin (lowerRetainedSize P N p)) (r : Fin (P.n N)) :
    ((lowerRetainedVector P z N p j r).den : ZMod p)≠0 :=by
  let v :=(Fintype.equivFin ↥(lowerRetainedSet P N p)).symm j
  have hv :=(mem_Ico.mp (mem_sdiff.mp v.property).1).2
  have hvH : v.val<P.H N :=by unfold Parameters.H Parameters.C;omega
  exact (scaledRawEntry_transfer hp2 hH hvH z hz).1

theorem lowerPairedVector_den_ne_zero {P : Parameters} (hAdm : Admissible P)
    {N p : ℕ} [Fact p.Prime] (hp2 : p≠2) (hN : 0<N)
    (z : ℚ) (hz : (((p:ℚ)*z).den : ZMod p)≠0)
    (j : Fin (lowerPairedSize P N p)) (r : Fin (P.n N)) :
    ((lowerPairedVector P z N p j r).den : ZMod p)≠0 :=by
  let ell :=(Fintype.equivFin ↥(lowerPairSet P N p)).symm j
  have hb :=lowerPairSet_bounds ell.property
  have hhigh : p+ell.val<P.H N :=by have hh :=hb.2.2.2.1;unfold Parameters.H Parameters.C;omega
  exact rawEntry_pair_prime_integral hAdm hp2 hN r.isLt hb.2.1 hb.2.2.1 hhigh hb.2.2.2.2.le z hz

def lowerInverseCoeff {P : Parameters} {N p : ℕ}
    (i : lowerPhysicalIndex P N p) (j : ↥(Ico (P.b N) (P.L N))) : ℤ :=
  if hj : j.val∈lowerHighSet P N p then
    let ell : ↥(lowerPairSet P N p) :=⟨j.val-p,(lowerHighSet_sub_mem_pair hj).1⟩
    let low : ↥(lowerRetainedSet P N p) :=⟨ell.val,lowerPairSet_mem_retained ell.property⟩
    (if i=lowerPairedTag ell then 1 else 0)-(if i=lowerRetainedTag low then 1 else 0)
  else
    let keep : ↥(lowerRetainedSet P N p) :=⟨j.val,mem_sdiff.mpr ⟨j.property,hj⟩⟩
    if i=lowerRetainedTag keep then 1 else 0

theorem rawEntry_eq_lower_physical_sum {P : Parameters} {N p : ℕ} [Fact p.Prime]
    (z : ℚ) (j : ↥(Ico (P.b N) (P.L N))) (r : Fin (P.n N)) :
    rawEntryRat P z N r.val j.val=∑ i : lowerPhysicalIndex P N p,
      lowerPhysicalColumn P z N p i r*(lowerInverseCoeff i j:ℚ) :=by
  by_cases hj : j.val∈lowerHighSet P N p
  · simp only [lowerInverseCoeff,dite_eq_left hj,Int.cast_sub,Int.cast_ite,Int.cast_one,Int.cast_zero,
      mul_sub,sum_sub_distrib,mul_ite,mul_one,mul_zero,sum_ite_eq',mem_univ,ite_true]
    rw [lowerPhysicalColumn_paired,lowerPhysicalColumn_retained,(lowerHighSet_sub_mem_pair hj).2]
    ring
  · simp only [lowerInverseCoeff,dite_eq_right hj,Int.cast_ite,Int.cast_one,Int.cast_zero,
      mul_ite,mul_one,mul_zero,sum_ite_eq',mem_univ,ite_true,lowerPhysicalColumn_retained]

theorem lowerPhysical_loss_eq (P : Parameters) (N p : ℕ) :
    min (2*P.n N) (min (P.n N+lowerRetainedSize P N p)
      (2*lowerRetainedSize P N p+lowerPairedSize P N p+0))=lowerPrimeLoss P N p :=by
  have hh :=lowerPairCount_le_pool P N p
  simp only [lowerRetainedSize,lowerPairedSize,Fintype.card_coe,lowerRetainedSet_card,
    lowerPairSet_card,add_zero]
  unfold lowerPrimeLoss
  omega

theorem lowerPhysicalCombination_valuation {P : Parameters} (hAdm : Admissible P)
    {N p : ℕ} [Fact p.Prime] (hp2 : p≠2) (hN : 0<N) (hH : P.H N<p^2)
    (z : ℚ) (hz : (((p:ℚ)*z).den : ZMod p)≠0)
    (g : lowerPhysicalIndex P N p → Fin (P.n N) → ℤ) :
    -(lowerPrimeLoss P N p:ℤ) ≤ padicValRat p
      (Matrix.of fun r k : Fin (P.n N) =>∑ i,lowerPhysicalColumn P z N p i r*(g i k:ℚ)).det :=by
  have hh :=oddPhysicalCombination_valuation_lower (p :=p) (n :=P.n N)
    (lowerRetainedVector P z N p) (lowerPairedVector P z N p)
    (fun j : Fin 0 =>Fin.elim0 j) (fun j : Fin 0 =>Fin.elim0 j) (fun j : Fin 0 =>Fin.elim0 j)
    (fun i k =>(g i k:ℚ)) (lowerRetainedVector_den_ne_zero hp2 hH z hz)
    (lowerPairedVector_den_ne_zero hAdm hp2 hN z hz)
    (by intro j;exact Fin.elim0 j) (by intro j;exact Fin.elim0 j)
    (by intro j;exact Fin.elim0 j) (by intro i k;simp)
  simpa only [lowerPhysical_loss_eq,lowerPhysicalColumn] using hh

def lowerRawColumn {P : Parameters} {N : ℕ} (k : Fin (P.n N)) (v : Fin (P.q N+1)) :
    ↥(Ico (P.b N) (P.L N)) :=
  ⟨P.b N+k.val+v.val,mem_Ico.mpr ⟨rawColumn_ge_b P N k.val v.val,
    rawColumn_lt_L k.isLt (Nat.le_of_lt_succ v.isLt)⟩⟩

def lowerFilterInt (P : Parameters) (N v : ℕ) : ℤ :=(-1:ℤ)^v*(P.q N).choose v

def lowerFilteredCoeff {P : Parameters} {N p : ℕ}
    (i : lowerPhysicalIndex P N p) (k : Fin (P.n N)) : ℤ :=
  ∑ v : Fin (P.q N+1),lowerFilterInt P N v.val*lowerInverseCoeff i (lowerRawColumn k v)

theorem filteredEntry_eq_lower_physical_sum {P : Parameters} {N p : ℕ} [Fact p.Prime]
    (z : ℚ) (r k : Fin (P.n N)) :
    filteredEntryRat P z N r.val k.val=∑ i : lowerPhysicalIndex P N p,
      lowerPhysicalColumn P z N p i r*(lowerFilteredCoeff i k:ℚ) :=by
  unfold filteredEntryRat
  rw [← Fin.sum_univ_eq_sum_range (fun v =>filterCoeffRat P N v*
    rawEntryRat P z N r.val (P.b N+k.val+v))]
  have hraw (v : Fin (P.q N+1)) : rawEntryRat P z N r.val (P.b N+k.val+v.val)=
      ∑ i : lowerPhysicalIndex P N p,lowerPhysicalColumn P z N p i r*
        (lowerInverseCoeff i (lowerRawColumn k v):ℚ) :=
    rawEntry_eq_lower_physical_sum z (lowerRawColumn k v) r
  simp_rw [hraw,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  unfold lowerFilteredCoeff
  rw [Int.cast_sum,mul_sum]
  apply sum_congr rfl
  intro v hv
  have hc : filterCoeffRat P N v.val=(lowerFilterInt P N v.val:ℚ) :=by
    simp [filterCoeffRat,lowerFilterInt]
  rw [hc,Int.cast_mul]
  ring

/-- A uniform lower-pool valuation for the actual filtered determinant,
    with every arithmetic factorization hypothesis discharged. -/
theorem determinantRat_lower_prime_valuation {P : Parameters} (hAdm : Admissible P)
    {N p : ℕ} [Fact p.Prime] (hp2 : p≠2) (hN : 0<N) (hH : P.H N<p^2)
    (z : ℚ) (hz : (((p:ℚ)*z).den : ZMod p)≠0) :
    -(lowerPrimeLoss P N p:ℤ) ≤ padicValRat p (determinantRat P z N) :=by
  have hmatrix : (fun r k : Fin (P.n N) =>filteredEntryRat P z N r.val k.val)=
      (Matrix.of fun r k : Fin (P.n N) =>∑ i : lowerPhysicalIndex P N p,
        lowerPhysicalColumn P z N p i r*(lowerFilteredCoeff i k:ℚ)) :=by
    funext r k
    exact filteredEntry_eq_lower_physical_sum z r k
  unfold determinantRat
  rw [hmatrix]
  exact lowerPhysicalCombination_valuation hAdm hp2 hN hH z hz lowerFilteredCoeff

end
end CatalanMeasure.Parametric
