module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.Check.Uniq
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.Check.ProfK
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts.Rows
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# The generic psi-row identity

For a stored row `r` of the packet and `(J, S)`: on the slot coordinates `r_c Z = -r_{jet0} rowInt(J,S)(iota c)`,
on the extra coordinates `r_{extra j} = eps_j r_{jet0}`.  Then on the kernel of the row
`psi(J,S)(ins y) = sum_j eps_j y_{extra j}`.
-/
namespace CatalanMeasure.GenD.Uniform.W.Charts6.Check
open Polynomial Finset Module CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.Parametric CatalanMeasure.GenD.Uniform.W.Charts CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.ZoneZ
open CatalanMeasure.GenD.Uniform.W.Prof (Packet emb chartMap Mx)

/-- `rowInt` with the scaled moments `α(u,J), β(u,J)` taken from tables (checked once). -/
def rowIntT (pd : ProfData) (AT BT : List (List ℤ)) (J : ℕ) (S : ℤ) (k : ℕ) : ℤ :=
  ∑ u ∈ Finset.range (S.toNat + 3),
    ((AT.getD J []).getD u 0 * Q.cf (pd.g k) (S + 1 - u) + (BT.getD J []).getD u 0 * Q.cf (pd.t k) (S - u))

theorem rowIntT_eq (pd : ProfData) (AT BT : List (List ℤ)) (Z Ub J : ℕ) (S : ℤ) (k : ℕ)
    (hS : S.toNat + 3 ≤ Ub) (hA : ∀ u < Ub, (AT.getD J []).getD u 0 = qscale (Q.alphaQ u J) Z)
    (hB : ∀ u < Ub, (BT.getD J []).getD u 0 = qscale (Q.betaQ u J) Z) :
    rowIntT pd AT BT J S k = rowInt pd Z J S k := by
  unfold rowIntT rowInt
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu' : u < Ub := by have := Finset.mem_range.mp hu; omega
  rw [hA u hu', hB u hu']

def rowOKg (pk : Packet) (m : Meta) (Z : ℕ) (AT BT : List (List ℤ)) (g i J : ℕ) (S : ℤ) (eps : List ℤ) : Bool :=
  decide (1 ≤ m.ex) && decide (i < (rowsOf pk g).length) &&
  decide ((rowAt pk (g, i)).getD (extraC m 0) 0 < 0) &&
  decide ((QB ^ 40 : ℤ) % ((rowAt pk (g, i)).getD (extraC m 0) 0) = 0) &&
  (List.range m.ex).all (fun j => decide ((rowAt pk (g, i)).getD (extraC m j) 0 =
    eps.getD j 0 * (rowAt pk (g, i)).getD (extraC m 0) 0)) &&
  (List.range pk.n).all (fun c => decide (4 * m.b + 2 ≤ m.iota.getD c 0) ||
    decide ((rowAt pk (g, i)).getD c 0 * (Z : ℤ) =
      -((rowAt pk (g, i)).getD (extraC m 0) 0) * rowIntT (pdK m.k0 m.b) AT BT J S (m.iota.getD c 0))) &&
  (List.range m.ex).all (fun j => decide (rowIntT (pdK m.k0 m.b) AT BT J S (4 * m.b + 2 + j) = 0))

noncomputable section
variable {p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

/-- The extra coordinate `j` of a packet vector. -/
def yE (pk : Packet) (m : Meta) (y : Fin pk.n → Fp) (j : ℕ) : Fp :=
  if h : extraC m j < pk.n then y ⟨extraC m j, h⟩ else 0

theorem insM_eq_sum (pk : Packet) (m : Meta) (hio : iotaOK pk m = true) {K : ℕ} (hK : K = 4 * m.b + 2 + m.ex)
    (y : Fin pk.n → Fp) :
    insM m pk.n K y = ∑ c : Fin pk.n, y c • (Pi.single (⟨m.iota.getD c 0, by
      obtain ⟨hlen, hnd, hlt, hex⟩ := iotaOK_sound pk m hio
      have hcl : c.val < m.iota.length := by omega
      rw [List.getD_eq_getElem _ _ hcl]; have := hlt _ (List.getElem_mem hcl); omega⟩ : Fin K) (1 : Fp) : Fin K → Fp) := by
  obtain ⟨hlen, hnd, hlt, hex⟩ := iotaOK_sound pk m hio
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hk : k.val ∈ m.iota
  · have hidx : m.iota.idxOf k.val < m.iota.length := List.idxOf_lt_length_iff.mpr hk
    rw [Finset.sum_eq_single ⟨m.iota.idxOf k.val, by omega⟩]
    · have hget : m.iota.getD (m.iota.idxOf k.val) 0 = k.val := by
        rw [List.getD_eq_getElem _ _ hidx]; exact List.getElem_idxOf hidx
      rw [if_pos (Fin.ext hget.symm)]
      simp only [insM, LinearMap.pi_apply, pcOf, if_pos hk]
      rw [dif_pos (by omega)]
      rfl
    · intro c _ hc
      rw [if_neg]
      intro hck
      apply hc
      have hget : m.iota.getD c 0 = k.val := (congrArg Fin.val hck).symm
      have hcl : c.val < m.iota.length := by omega
      rw [List.getD_eq_getElem _ _ hcl] at hget
      apply Fin.ext
      simp only
      rw [← hget]
      exact (iota_idxOf m hnd c hcl).symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [insM, LinearMap.pi_apply, pcOf, if_neg hk]
    simp only [LinearMap.zero_apply]
    symm
    apply Finset.sum_eq_zero
    intro c _
    rw [if_neg]
    intro hck
    apply hk
    have hget : m.iota.getD c 0 = k.val := (congrArg Fin.val hck).symm
    have hcl : c.val < m.iota.length := by omega
    rw [List.getD_eq_getElem _ _ hcl] at hget
    rw [← hget]; exact List.getElem_mem hcl


theorem psi_row_g (pk : Packet) (m : Meta) (hio : iotaOK pk m = true) (hp : 59 < p) {K : ℕ}
    (hK : K = 4 * m.b + 2 + m.ex) (F : Prof p K) (hF : (pdK m.k0 m.b).Realises F)
    {Ub Jb Z : ℕ} (hZ : Z = Zmom Ub Jb) (hZd : (QB ^ 40 : ℤ) % (Z : ℤ) = 0) {AT BT : List (List ℤ)}
    {g i J : ℕ} {S : ℤ} {eps : List ℤ} {H : ℕ} (hok : rowOKg pk m Z AT BT g i J S eps = true) (hJ : J < Jb)
    (hA : ∀ u < Ub, (AT.getD J []).getD u 0 = qscale (Q.alphaQ u J) Z)
    (hB : ∀ u < Ub, (BT.getD J []).getD u 0 = qscale (Q.betaQ u J) Z)
    (hS : S.toNat + 3 ≤ Ub) (hH : S.toNat + 3 ≤ H) (y : Fin pk.n → Fp)
    (hy : ∑ c : Fin pk.n, (((rowAt pk (g, i)).getD c 0 : ℤ) : Fp) * y c = 0) :
    F.psi H J S (insM m pk.n K y) = ∑ j ∈ range m.ex, ((eps.getD j 0 : ℤ) : Fp) * yE pk m y j := by
  simp only [rowOKg, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true]
    at hok
  obtain ⟨⟨⟨⟨⟨⟨hex1, hi⟩, hneg⟩, hdvd⟩, hex⟩, hslot⟩, hzero⟩ := hok
  have hRT : ∀ k, rowIntT (pdK m.k0 m.b) AT BT J S k = rowInt (pdK m.k0 m.b) Z J S k :=
    fun k => rowIntT_eq _ AT BT Z Ub J S k hS hA hB
  simp only [hRT] at hslot hzero
  obtain ⟨hlen, hnd, hlt, hexi⟩ := iotaOK_sound pk m hio
  set r := rowAt pk (g, i) with hr
  have hZu : ((Z : ℤ) : Fp) ≠ 0 :=
    unit_of_dvdQ (Z : ℤ) (Int.dvd_of_emod_eq_zero hZd) hp
  have hZ' : (Z : Fp) ≠ 0 := by simpa using hZu
  have hZp : ¬ p ∣ Zmom Ub Jb := by
    intro h; apply hZ'; rw [hZ]; exact (ZMod.natCast_eq_zero_iff _ _).mpr h
  have hD : ((r.getD (extraC m 0) 0 : ℤ) : Fp) ≠ 0 :=
    unit_of_dvdQ _ (Int.dvd_of_emod_eq_zero hdvd) hp
  have hm : ∀ k : Fin K, ((rowInt (pdK m.k0 m.b) Z J S k : ℤ) : Fp) = (Z : Fp) * F.psi H J S (Pi.single k 1) := by
    intro k
    have := rowInt_mod (Ub := Ub) (Jb := Jb) hZp (pdK m.k0 m.b) F hF k hJ hS hH
    rw [hZ]; exact this
  have hιK : ∀ c : Fin pk.n, m.iota.getD c 0 < K := by
    intro c
    have hcl : c.val < m.iota.length := by omega
    rw [List.getD_eq_getElem _ _ hcl]; have := hlt _ (List.getElem_mem hcl); omega
  let ιF : Fin pk.n → Fin K := fun c => ⟨m.iota.getD c 0, hιK c⟩
  have hnon : ∀ c : Fin pk.n, 4 * m.b + 2 ≤ m.iota.getD c 0 → F.psi H J S (Pi.single (ιF c) 1) = 0 := by
    intro c hc
    have hcl : c.val < m.iota.length := by omega
    have hv := hlt _ (List.getElem_mem hcl)
    have hg : m.iota.getD c 0 = m.iota[c.val] := List.getD_eq_getElem _ _ hcl
    have h0 := hzero (m.iota[c.val] - (4 * m.b + 2)) (by omega)
    have e : 4 * m.b + 2 + (m.iota[c.val] - (4 * m.b + 2)) = (ιF c).val := by
      show _ = m.iota.getD c 0
      omega
    rw [e] at h0
    have := hm (ιF c)
    rw [h0] at this
    simp only [Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hZ'
  have hsl : ∀ c : Fin pk.n, m.iota.getD c 0 < 4 * m.b + 2 →
      ((r.getD c 0 : ℤ) : Fp) = -((r.getD (extraC m 0) 0 : ℤ) : Fp) * F.psi H J S (Pi.single (ιF c) 1) := by
    intro c hc
    have e := hslot c.val c.isLt
    rcases e with e | e
    · omega
    have e' := congrArg (fun z : ℤ => (z : Fp)) e
    simp only [Int.cast_mul, Int.cast_neg, Int.cast_natCast] at e'
    have hmc := hm (ιF c)
    have hmc' : ((rowInt (pdK m.k0 m.b) Z J S (m.iota.getD c 0) : ℤ) : Fp) = (Z : Fp) * F.psi H J S (Pi.single (ιF c) 1) := hmc
    rw [hmc'] at e'
    apply mul_right_cancel₀ hZ'
    linear_combination e'
  rw [insM_eq_sum pk m hio hK y, map_sum]
  simp only [map_smul, smul_eq_mul]
  change ∑ c : Fin pk.n, y c * F.psi H J S (Pi.single (ιF c) 1) = _
  let y' : Fin pk.n → Fp := fun c => if m.iota.getD c 0 < 4 * m.b + 2 then 0 else y c
  have hpt : ∀ c : Fin pk.n, ((r.getD c 0 : ℤ) : Fp) * y c =
      -((r.getD (extraC m 0) 0 : ℤ) : Fp) * (y c * F.psi H J S (Pi.single (ιF c) 1)) +
        ((r.getD c 0 : ℤ) : Fp) * y' c := by
    intro c
    by_cases hc : m.iota.getD c 0 < 4 * m.b + 2
    · simp only [y', if_pos hc, mul_zero, add_zero]
      rw [hsl c hc]; ring
    · simp only [y', if_neg hc]
      rw [hnon c (by omega)]; ring
  have hsum := Finset.sum_congr rfl (fun c (_ : c ∈ (Finset.univ : Finset (Fin pk.n))) => hpt c)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [hy] at hsum
  have hex' := extras_sum pk m hio y' r (fun c hc => by simp only [y', if_pos hc])
  rw [hex'] at hsum
  have hy2 : ∀ j ∈ range m.ex, ((r.getD (extraC m j) 0 : ℤ) : Fp) *
      (if h : extraC m j < pk.n then y' ⟨extraC m j, h⟩ else 0) =
      ((r.getD (extraC m 0) 0 : ℤ) : Fp) * (((eps.getD j 0 : ℤ) : Fp) * yE pk m y j) := by
    intro j hj
    have hjl := Finset.mem_range.mp hj
    have hrj := hex j hjl
    unfold yE
    by_cases h : extraC m j < pk.n
    · rw [dif_pos h, dif_pos h]
      have hget := extraC_get pk m hio j hjl
      have : y' ⟨extraC m j, h⟩ = y ⟨extraC m j, h⟩ := by
        simp only [y']; rw [if_neg (by show ¬ (m.iota.getD (extraC m j) 0 < 4 * m.b + 2); omega)]
      rw [this, hrj]; push_cast; ring
    · rw [dif_neg h, dif_neg h]; ring
  rw [Finset.sum_congr rfl hy2, ← Finset.mul_sum] at hsum
  apply mul_left_cancel₀ hD
  linear_combination hsum

end
end CatalanMeasure.GenD.Uniform.W.Charts6.Check
