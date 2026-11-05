module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Graph146
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Check146O
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Prof.Pilot146
  CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3 Finset
  CatalanMeasure.GenD.D58.Odd CatalanMeasure.Parametric
noncomputable section
variable {N p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

theorem poly_zero_of_orders (f : Fp[X]) (m r s : ℕ) (hdeg : f.degree < p) (hm : m + r = p) (hrs : r ≤ s)
    (hdvd : (X - 1 : Fp[X]) ^ m ∣ f) (hc : ∀ e, e < s → f.coeff e = 0) : f = 0 := by
  obtain ⟨g, rfl⟩ := hdvd
  by_contra hne
  have hg : g ≠ 0 := fun h => hne (by rw [h, mul_zero])
  have hXs : (X : Fp[X]) ^ s ∣ (X - 1) ^ m * g := (X_pow_dvd_iff).mpr hc
  have hcop : IsCoprime ((X : Fp[X]) ^ s) ((X - 1) ^ m) := by
    have : IsCoprime (X : Fp[X]) (X - 1) := ⟨1, -1, by ring⟩
    exact this.pow
  have hXg : (X : Fp[X]) ^ s ∣ g := hcop.dvd_of_dvd_mul_left hXs
  have h1 : s ≤ g.natDegree := by
    have := natDegree_le_of_dvd hXg hg
    simpa using this
  have hne' : (X - 1 : Fp[X]) ^ m * g ≠ 0 := hne
  have h2 : ((X - 1 : Fp[X]) ^ m * g).natDegree = m + g.natDegree := by
    rw [natDegree_mul (pow_ne_zero _ (by simpa using X_sub_C_ne_zero (1 : Fp))) hg]
    have : (X - 1 : Fp[X]).natDegree = 1 := by simpa using natDegree_X_sub_C (1 : Fp)
    rw [natDegree_pow, this]; ring
  have h3 : ((X - 1 : Fp[X]) ^ m * g).natDegree < p := by
    have := hdeg; rw [degree_eq_natDegree hne'] at this; exact_mod_cast this
  omega

theorem unit_of_dvd (D : ℤ) (hD : D ∣ 2310 ^ 40) (hp : 11 < p) : ((D : ℤ) : Fp) ≠ 0 := by
  intro h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have h1 : (p : ℤ) ∣ 2310 ^ 40 := h.trans hD
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have h2 : (p : ℤ) ∣ 2310 := hpp.dvd_of_dvd_pow h1
  have h3 : p ∣ 2310 := by exact_mod_cast h2
  have hpn := (Fact.out : p.Prime)
  have e : (2310 : ℕ) = 2 * 3 * 5 * 7 * 11 := by norm_num
  rw [e] at h3
  rcases (Nat.Prime.dvd_mul hpn).mp h3 with h | h
  · rcases (Nat.Prime.dvd_mul hpn).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hpn).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hpn).mp h with h | h
        · have := Nat.le_of_dvd (by norm_num) h; omega
        · have := Nat.le_of_dvd (by norm_num) h; omega
      · have := Nat.le_of_dvd (by norm_num) h; omega
    · have := Nat.le_of_dvd (by norm_num) h; omega
  · have := Nat.le_of_dvd (by norm_num) h; omega

theorem ck_X_val {b ex K : ℕ} (hK : K = b * 4 + 2 + ex) (j : Fin ex) :
    ((ckEquiv hK).symm (Sum.inr (Sum.inr j))).val = b * 4 + 2 + j.val := by
  subst hK
  simp [ckEquiv]

theorem jet0_emb (x : Fin p → Fin packetO.d → Fp) (k : ℕ) (hk : k < p) (c : Fin 44) :
    emb packetO p 44 (jet0 k x) c = emb packetO p 44 (x ⟨k, hk⟩) c := by
  rw [emb_jet0, jet0_coord]
  exact polx_coeff (X44 x) c ⟨k, hk⟩

theorem rowsum_aux (r : List ℤ) (y : Fin 44 → Fp) (hy : ∀ c : Fin 44, c.val < 42 → y c = 0) :
    ∑ c : Fin 44, ((r.getD c 0 : ℤ) : Fp) * y c =
      ((r.getD 42 0 : ℤ) : Fp) * y 42 + ((r.getD 43 0 : ℤ) : Fp) * y 43 := by
  refine Finset.sum_eq_add (42 : Fin 44) 43 (by decide) ?_ (fun h => absurd (Finset.mem_univ _) h)
    (fun h => absurd (Finset.mem_univ _) h)
  intro c _ hc
  have : c.val < 42 := by
    have h1 : c ≠ 42 := hc.1
    have h2 : c ≠ 43 := hc.2
    have := c.isLt
    have h1' : c.val ≠ 42 := fun h => h1 (Fin.ext h)
    have h2' : c.val ≠ 43 := fun h => h2 (Fin.ext h)
    omega
  rw [hy c this, mul_zero]

theorem slot_zero (hW : Win N p) (x : Fin p → Fin packetO.d → Fp)
    (hproj : ∀ e, projExtras (hKp hW) (emb packetO p 44 (x e)) = 0) (e : Fin p) (c : Fin 44)
    (hc : c.val < 42) : emb packetO p 44 (x e) c = 0 := by
  have h0 := congrFun (hproj e) c
  rw [projExtras_apply] at h0
  by_cases hx : isExtra (hKp hW) c
  · exfalso
    obtain ⟨j, hj⟩ := hx
    have h := ck_X_val (hKp hW) j
    have hc' : c = (ckEquiv (hKp hW)).symm (Sum.inr (Sum.inr j)) := by rw [← hj]; simp
    have hb : bN design N p = 10 := geom_b hW
    have hv : c.val = bN design N p * 4 + 2 + j.val := by rw [hc']; exact h
    omega
  · rw [if_neg hx] at h0; exact h0

theorem raw_vanish (x : Fin p → Fin packetO.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 11) (r : List ℤ) (hr : hasRow g r = true)
    (jt k : ℕ) (hk : k < wd N p g) (hjet : jetP N p g k = jet0 jt) (hj : jt < p)
    (hs : ∀ c : Fin 44, c.val < 42 → emb packetO p 44 (x ⟨jt, hj⟩) c = 0) :
    ((r.getD 42 0 : ℤ) : Fp) * emb packetO p 44 (x ⟨jt, hj⟩) 42 +
      ((r.getD 43 0 : ℤ) : Fp) * emb packetO p 44 (x ⟨jt, hj⟩) 43 = 0 := by
  have v := vanish_hasRow x hker g hg k hk r hr
  rw [hjet] at v
  rw [← rowsum_aux r _ hs, ← v]
  exact (Finset.sum_congr rfl fun c _ => by rw [jet0_emb x jt hj c]).symm

theorem chainJet0 (hW : Win N p) (x : Fin p → Fin packetO.d → Fp) (hker : JetKer N p x) :
    ∀ j < wd N p 3 + wd N p 4, (taylor 1 (polx (X44 x) 42)).coeff j = 0 := by
  have hj3 : ∀ k, jetP N p 3 k = Charts3.taylorJet (m := p) (d := packetO.d) 1 (0 + k) := by
    intro k; simp [jetP]
  have hj4 : ∀ k, jetP N p 4 k = Charts3.taylorJet (m := p) (d := packetO.d) 1 (wd N p 3 + k) := by
    intro k; simp [jetP]
  exact chain2 (Q := fun j => (taylor 1 (polx (X44 x) 42)).coeff j = 0)
    (fun k hk => by simpa using vtaylor_unit x hker 3 (by norm_num) 1 0 hj3 42 pt1_jet0.1 k hk)
    (vtaylor_unit x hker 4 (by norm_num) 1 (wd N p 3) hj4 42 pt1_jet0.2)

theorem chainLow (hW : Win N p) (x : Fin p → Fin packetO.d → Fp) (hker : JetKer N p x) :
    ∀ j < wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9, (polx (X44 x) 43).coeff (p - 1 - j) = 0 := by
  have hj6 : ∀ k, jetP N p 6 k = jetInf (0 + k) := by intro k; simp [jetP]
  have hj7 : ∀ k, jetP N p 7 k = jetInf (wd N p 6 + k) := by intro k; simp [jetP]
  have hj8 : ∀ k, jetP N p 8 k = jetInf (wd N p 6 + wd N p 7 + k) := by intro k; simp [jetP]
  have hj9 : ∀ k, jetP N p 9 k = jetInf (wd N p 6 + wd N p 7 + wd N p 8 + k) := by intro k; simp [jetP]
  have := wd6 hW; have := wd7 hW; have := wd8 hW; have := wd9 hW; have := hW.2.1; have := hW.2.2.1
  exact chain4 (Q := fun j => (polx (X44 x) 43).coeff (p - 1 - j) = 0)
    (fun k hk => by simpa using vinf_unit x hker 6 (by norm_num) 0 hj6 (by omega) 43 inf_low.1 k hk)
    (vinf_unit x hker 7 (by norm_num) (wd N p 6) hj7 (by omega) 43 inf_low.2.1)
    (vinf_unit x hker 8 (by norm_num) (wd N p 6 + wd N p 7) hj8 (by omega) 43 inf_low.2.2.1)
    (vinf_unit x hker 9 (by norm_num) (wd N p 6 + wd N p 7 + wd N p 8) hj9 (by omega) 43 inf_low.2.2.2)

set_option maxHeartbeats 4000000 in
theorem hinj_pilot (hW : Win N p) (hpD : ¬ (p : ℤ) ∣ packetO.D) (x : Fin p → Fin packetO.d → Fp)
    (hker : JetKer N p x) (hproj : ∀ e, projExtras (hKp hW) (emb packetO p 44 (x e)) = 0) : x = 0 := by
  have h11 : 11 < p := by have := hW.2.1; have := hW.1; omega
  have hslot := slot_zero hW x hproj
  have w1 := wd1 hW; have w2 := wd2 hW; have w6 := wd6 hW; have w7 := wd7 hW
  have w8 := wd8 hW; have w9 := wd9 hW; have hp6 := hW.2.1; have hp152 := hW.2.2.1; have hN := hW.1
  obtain ⟨r1a, r1g, r2a, r2g⟩ := raw_ok
  simp only [rawRowOK, Bool.and_eq_true, decide_eq_true_eq] at r1a r1g r2a r2g
  obtain ⟨⟨⟨hr1a, d1a⟩, n1a⟩, e1a⟩ := r1a
  obtain ⟨⟨⟨hr1g, d1g⟩, n1g⟩, e1g⟩ := r1g
  obtain ⟨⟨⟨hr2a, d2a⟩, n2a⟩, e2a⟩ := r2a
  obtain ⟨⟨⟨hr2g, d2g⟩, n2g⟩, e2g⟩ := r2g
  -- y e 42 = 0 on the prefix
  have h42 : ∀ e : Fin p, e.val < wd N p 1 + wd N p 2 → emb packetO p 44 (x e) 42 = 0 := by
    intro e he
    by_cases h1 : e.val < wd N p 1
    · have v := raw_vanish x hker 1 (by norm_num) _ hr1a e.val e.val h1 (by simp [jetP]) e.isLt (hslot ⟨e.val, e.isLt⟩)
      simp only [Fin.eta] at v
      rw [e1a] at v; simp only [zero_mul, Int.cast_zero, add_zero] at v
      have hu := unit_of_dvd _ d1a h11
      exact (mul_eq_zero.mp v).resolve_left hu
    · have v := raw_vanish x hker 2 (by norm_num) _ hr2a (e.val) (e.val - wd N p 1) (by omega)
        (by simp [jetP]; congr 1; omega) e.isLt (hslot ⟨e.val, e.isLt⟩)
      simp only [Fin.eta] at v
      rw [e2a] at v; simp only [zero_mul, Int.cast_zero, add_zero] at v
      have hu := unit_of_dvd _ d2a h11
      exact (mul_eq_zero.mp v).resolve_left hu
  have hf42 : polx (X44 x) 42 = 0 := by
    refine poly_zero_of_orders _ (p - 3 * N) (3 * N) (wd N p 1 + wd N p 2) (polx_degree _ _)
      (by omega) (by omega) ?_ ?_
    · have h1 : (X - 1 : Fp[X]) = X - C 1 := by simp
      rw [h1, pow_dvd_iff_taylor]
      intro k hk
      exact chainJet0 hW x hker k (by have := wd3 hW; have := wd4 hW; omega)
    · intro e he
      have hep : e < p := by omega
      have := polx_coeff (X44 x) 42 ⟨e, hep⟩
      simp only at this
      rw [this]
      exact h42 ⟨e, hep⟩ he
  have h42' : ∀ e : Fin p, emb packetO p 44 (x e) 42 = 0 := by
    intro e
    have := polx_coeff (X44 x) 42 e
    rw [hf42] at this
    simpa using this.symm
  have h43 : ∀ e : Fin p, emb packetO p 44 (x e) 43 = 0 := by
    intro e
    by_cases he : e.val < wd N p 1 + wd N p 2
    · by_cases h1 : e.val < wd N p 1
      · have v := raw_vanish x hker 1 (by norm_num) _ hr1g e.val e.val h1 (by simp [jetP]) e.isLt (hslot ⟨e.val, e.isLt⟩)
        simp only [Fin.eta] at v
        rw [e1g, h42' e] at v
        simp only [mul_zero, zero_add, Int.cast_mul, Int.cast_one, one_mul] at v
        have hu := unit_of_dvd _ d1g h11
        have hu' : (((((oRows 1).getD 10 []).getD 43 0 : ℤ)) : Fp) ≠ 0 := by
          rw [e1g]; simpa using hu
        exact (mul_eq_zero.mp v).resolve_left hu'
      · have v := raw_vanish x hker 2 (by norm_num) _ hr2g (e.val) (e.val - wd N p 1) (by omega)
          (by simp [jetP]; congr 1; omega) e.isLt (hslot ⟨e.val, e.isLt⟩)
        simp only [Fin.eta] at v
        rw [e2g, h42' e] at v
        simp only [mul_zero, zero_add, Int.cast_mul, Int.cast_one, one_mul] at v
        have hu := unit_of_dvd _ d2g h11
        have hu' : (((((oRows 2).getD 9 []).getD 43 0 : ℤ)) : Fp) ≠ 0 := by
          rw [e2g]; simpa using hu
        exact (mul_eq_zero.mp v).resolve_left hu'
    · have := coeff_of_inf (polx (X44 x) 43) (polx_degree _ _)
        (wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9) (8 * N - p) (by omega) (by omega)
        (fun j hj => chainLow hW x hker j hj) e.val (by omega)
      have h2 := polx_coeff (X44 x) 43 e
      rw [this] at h2
      exact h2.symm
  have hinjE : Function.Injective (emb packetO p 44) :=
    emb_injective packetO_sound rfl (not_dvd_delta hpD)
  funext e
  apply hinjE
  funext c
  simp only [Pi.zero_apply, map_zero]
  show emb packetO p 44 (x e) c = 0
  have hc := c.isLt
  by_cases h1 : c.val < 42
  · exact hslot e c h1
  · have : c = 42 ∨ c = 43 := by
      rcases (by omega : c.val = 42 ∨ c.val = 43) with h | h
      · left; exact Fin.ext h
      · right; exact Fin.ext h
    rcases this with rfl | rfl
    · exact h42' e
    · exact h43 e

end
end CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O
