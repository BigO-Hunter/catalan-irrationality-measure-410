module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Orders
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Widths
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Prof.Pilot146
  CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3 Finset
  CatalanMeasure.GenD.D58.Odd
noncomputable section
variable {N p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

theorem ck_Z_val {b ex K : ℕ} (hK : K = b * 4 + 2 + ex) (z : Fin 2) :
    ((ckEquiv hK).symm (Sum.inr (Sum.inl z))).val = b * 4 + z.val := by
  subst hK
  simp [ckEquiv]

theorem hKp (hW : Win N p) : 44 = bN design N p * 4 + 2 + 2 := by
  have : bN design N p = 10 := geom_b hW
  rw [this]

theorem polx_proj {K b ex : ℕ} (hK : K = b * 4 + 2 + ex) (X : Fin p → Fin K → Fp) (idx : Fin K)
    (h : ¬ isExtra hK idx) : polx (fun e => projExtras hK (X e)) idx = polx X idx := by
  unfold polx
  refine Finset.sum_congr rfl fun e _ => ?_
  show C (projExtras hK (X e) idx) * _ = _
  rw [projExtras_apply, if_neg h]

theorem not_extra_inl {b ex K : ℕ} (hK : K = b * 4 + 2 + ex) (k : Fin b) (u : Fin 4) :
    ¬ isExtra hK ((ckEquiv hK).symm (Sum.inl (k, u))) := by
  rintro ⟨j, hj⟩
  simp at hj

theorem not_extra_Z {b ex K : ℕ} (hK : K = b * 4 + 2 + ex) (z : Fin 2) :
    ¬ isExtra hK ((ckEquiv hK).symm (Sum.inr (Sum.inl z))) := by
  rintro ⟨j, hj⟩
  simp at hj

/-- The atoms as `44`-coordinate vectors. -/
abbrev X44 (x : Fin p → Fin packetO.d → ZMod p) : Fin p → Fin 44 → ZMod p :=
  fun e => emb packetO p 44 (x e)

section chains

theorem chainCF (hW : Win N p) (x : Fin p → Fin packetO.d → Fp) (hker : JetKer N p x) (c : Fin 44) (h3 : hasRow 3 (unitL c) = true) :
    ∀ j < 3 * N, (taylor 1 (polx (X44 x) c)).coeff j = 0 := by
  have hj3 : ∀ k, jetP N p 3 k = Charts3.taylorJet (m := p) (d := packetO.d) 1 (0 + k) := by
    intro k; simp [jetP]
  intro j hj
  have := vtaylor_unit x hker 3 (by norm_num) 1 0 hj3 c h3 j (by rw [wd3 hW]; exact hj)
  simpa using this

theorem chainAF (hW : Win N p) (x : Fin p → Fin packetO.d → Fp) (hker : JetKer N p x) (c : Fin 44) (h3 : hasRow 3 (unitL c) = true) (h4 : hasRow 4 (unitL c) = true)
    (h5 : hasRow 5 (unitL c) = true) :
    ∀ j < 3 * N + (p - 1) / 2, (taylor 1 (polx (X44 x) c)).coeff j = 0 := by
  have hj3 : ∀ k, jetP N p 3 k = Charts3.taylorJet (m := p) (d := packetO.d) 1 (0 + k) := by
    intro k; simp [jetP]
  have hj4 : ∀ k, jetP N p 4 k = Charts3.taylorJet (m := p) (d := packetO.d) 1 (wd N p 3 + k) := by
    intro k; simp [jetP]
  have hj5 : ∀ k, jetP N p 5 k =
      Charts3.taylorJet (m := p) (d := packetO.d) 1 (wd N p 3 + wd N p 4 + k) := by
    intro k; simp [jetP]
  have := chain3 (Q := fun j => (taylor 1 (polx (X44 x) c)).coeff j = 0)
    (a := wd N p 3) (b := wd N p 4) (c := wd N p 5)
    (fun k hk => by simpa using vtaylor_unit x hker 3 (by norm_num) 1 0 hj3 c h3 k hk)
    (vtaylor_unit x hker 4 (by norm_num) 1 (wd N p 3) hj4 c h4)
    (vtaylor_unit x hker 5 (by norm_num) 1 (wd N p 3 + wd N p 4) hj5 c h5)
  intro j hj
  exact this j (by have := wd3 hW; have := wd4 hW; have := wd5 hW; have := hW.2.1; omega)

theorem chainDiff (hW : Win N p) (x : Fin p → Fin packetO.d → Fp) (hker : JetKer N p x) (c d : Fin 44) (hcd : c ≠ d) (h0 : hasRow 0 (diff2L c d) = true) :
    ∀ j < (p - 1) / 2, (taylor (-1) (polx (X44 x) c - 2 * polx (X44 x) d)).coeff j = 0 := by
  have hj0 : ∀ k, jetP N p 0 k = Charts3.taylorJet (m := p) (d := packetO.d) (-1) (0 + k) := by
    intro k; simp [jetP]
  intro j hj
  have := vtaylor_diff x hker 0 (by norm_num) (-1) 0 hj0 c d hcd h0 j (by rw [wd0 hW]; exact hj)
  simpa using this

theorem chainInf2 (hW : Win N p) (x : Fin p → Fin packetO.d → Fp) (hker : JetKer N p x) (c : Fin 44) (h6 : hasRow 6 (unitL c) = true) (h7 : hasRow 7 (unitL c) = true) :
    ∀ j < wd N p 6 + wd N p 7, (polx (X44 x) c).coeff (p - 1 - j) = 0 := by
  have hj6 : ∀ k, jetP N p 6 k = jetInf (0 + k) := by intro k; simp [jetP]
  have hj7 : ∀ k, jetP N p 7 k = jetInf (wd N p 6 + k) := by intro k; simp [jetP]
  have := wd6 hW; have := wd7 hW; have := hW.2.1; have := hW.2.2.1
  exact chain2 (Q := fun j => (polx (X44 x) c).coeff (p - 1 - j) = 0)
    (fun k hk => by simpa using vinf_unit x hker 6 (by norm_num) 0 hj6 (by omega) c h6 k hk)
    (vinf_unit x hker 7 (by norm_num) (wd N p 6) hj7 (by omega) c h7)

theorem chainInf3 (hW : Win N p) (x : Fin p → Fin packetO.d → Fp) (hker : JetKer N p x) (c : Fin 44) (h6 : hasRow 6 (unitL c) = true) (h7 : hasRow 7 (unitL c) = true)
    (h8 : hasRow 8 (unitL c) = true) :
    ∀ j < wd N p 6 + wd N p 7 + wd N p 8, (polx (X44 x) c).coeff (p - 1 - j) = 0 := by
  have hj6 : ∀ k, jetP N p 6 k = jetInf (0 + k) := by intro k; simp [jetP]
  have hj7 : ∀ k, jetP N p 7 k = jetInf (wd N p 6 + k) := by intro k; simp [jetP]
  have hj8 : ∀ k, jetP N p 8 k = jetInf (wd N p 6 + wd N p 7 + k) := by intro k; simp [jetP]
  have := wd6 hW; have := wd7 hW; have := wd8 hW; have := hW.2.1; have := hW.2.2.1
  exact chain3 (Q := fun j => (polx (X44 x) c).coeff (p - 1 - j) = 0)
    (fun k hk => by simpa using vinf_unit x hker 6 (by norm_num) 0 hj6 (by omega) c h6 k hk)
    (vinf_unit x hker 7 (by norm_num) (wd N p 6) hj7 (by omega) c h7)
    (vinf_unit x hker 8 (by norm_num) (wd N p 6 + wd N p 7) hj8 (by omega) c h8)

theorem vinf_virtB (x : Fin p → Fin packetO.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 11) (o : ℕ)
    (hjet : ∀ k, jetP N p g k = jetInf (o + k)) (hb : o + wd N p g ≤ p)
    (hrow : hasRow g virtBL = true) :
    ∀ k < wd N p g, (polx (X44 x) 1 - polx (X44 x) 3 + polx (X44 x) 41).coeff (p - 1 - (o + k)) = 0 := by
  intro k hk
  have := vanish_hasRow x hker g hg k hk virtBL hrow
  rw [hjet k, sum_virtBL, emb_jetInf, jetInf_coord, jetInf_coord, jetInf_coord, if_pos (by omega),
    if_pos (by omega), if_pos (by omega)] at this
  rw [coeff_add, coeff_sub]; exact this

theorem vinf_virtT (x : Fin p → Fin packetO.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 11) (o : ℕ)
    (hjet : ∀ k, jetP N p g k = jetInf (o + k)) (hb : o + wd N p g ≤ p)
    (hrow : hasRow g virtTL = true) :
    ∀ k < wd N p g, (polx (X44 x) 37 + polx (X44 x) 39).coeff (p - 1 - (o + k)) = 0 := by
  intro k hk
  have := vanish_hasRow x hker g hg k hk virtTL hrow
  rw [hjet k, sum_virtTL, emb_jetInf, jetInf_coord, jetInf_coord, if_pos (by omega),
    if_pos (by omega)] at this
  rw [coeff_add]; exact this

theorem chainVB (hW : Win N p) (x : Fin p → Fin packetO.d → Fp) (hker : JetKer N p x) 
    : ∀ j < wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9,
      (polx (X44 x) 1 - polx (X44 x) 3 + polx (X44 x) 41).coeff (p - 1 - j) = 0 := by
  have hj6 : ∀ k, jetP N p 6 k = jetInf (0 + k) := by intro k; simp [jetP]
  have hj7 : ∀ k, jetP N p 7 k = jetInf (wd N p 6 + k) := by intro k; simp [jetP]
  have hj8 : ∀ k, jetP N p 8 k = jetInf (wd N p 6 + wd N p 7 + k) := by intro k; simp [jetP]
  have hj9 : ∀ k, jetP N p 9 k = jetInf (wd N p 6 + wd N p 7 + wd N p 8 + k) := by intro k; simp [jetP]
  have := wd6 hW; have := wd7 hW; have := wd8 hW; have := wd9 hW; have := hW.2.1; have := hW.2.2.1
  obtain ⟨r6, r7, r8, r9⟩ := inf_virtB
  exact chain4 (Q := fun j => (polx (X44 x) 1 - polx (X44 x) 3 + polx (X44 x) 41).coeff (p - 1 - j) = 0)
    (fun k hk => by simpa using vinf_virtB x hker 6 (by norm_num) 0 hj6 (by omega) r6 k hk)
    (vinf_virtB x hker 7 (by norm_num) (wd N p 6) hj7 (by omega) r7)
    (vinf_virtB x hker 8 (by norm_num) (wd N p 6 + wd N p 7) hj8 (by omega) r8)
    (vinf_virtB x hker 9 (by norm_num) (wd N p 6 + wd N p 7 + wd N p 8) hj9 (by omega) r9)

theorem chainVT (hW : Win N p) (x : Fin p → Fin packetO.d → Fp) (hker : JetKer N p x) 
    : ∀ j < wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10,
      (polx (X44 x) 37 + polx (X44 x) 39).coeff (p - 1 - j) = 0 := by
  have hj6 : ∀ k, jetP N p 6 k = jetInf (0 + k) := by intro k; simp [jetP]
  have hj7 : ∀ k, jetP N p 7 k = jetInf (wd N p 6 + k) := by intro k; simp [jetP]
  have hj8 : ∀ k, jetP N p 8 k = jetInf (wd N p 6 + wd N p 7 + k) := by intro k; simp [jetP]
  have hj9 : ∀ k, jetP N p 9 k = jetInf (wd N p 6 + wd N p 7 + wd N p 8 + k) := by intro k; simp [jetP]
  have hj10 : ∀ k, jetP N p 10 k = jetInf (wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9 + k) := by
    intro k; simp [jetP]
  have := wd6 hW; have := wd7 hW; have := wd8 hW; have := wd9 hW; have := wd10 hW
  have := hW.2.1; have := hW.2.2.1
  obtain ⟨r6, r7, r8, r9, r10⟩ := inf_virtT
  exact chain5 (Q := fun j => (polx (X44 x) 37 + polx (X44 x) 39).coeff (p - 1 - j) = 0)
    (fun k hk => by simpa using vinf_virtT x hker 6 (by norm_num) 0 hj6 (by omega) r6 k hk)
    (vinf_virtT x hker 7 (by norm_num) (wd N p 6) hj7 (by omega) r7)
    (vinf_virtT x hker 8 (by norm_num) (wd N p 6 + wd N p 7) hj8 (by omega) r8)
    (vinf_virtT x hker 9 (by norm_num) (wd N p 6 + wd N p 7 + wd N p 8) hj9 (by omega) r9)
    (vinf_virtT x hker 10 (by norm_num) (wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9) hj10 (by omega) r10)

end chains

set_option maxHeartbeats 4000000 in
theorem hdom_pilot (hW : Win N p) (hp2 : p ≠ 2) (hn : 1 ≤ design.n N)
    (x : Fin p → Fin packetO.d → Fp) (hker : JetKer N p x) :
    ∃ c : Fin (design.n N) → Fp, Theta (P := design) (N := N) hp2 hn (hKp hW) c =
      fun e => projExtras (hKp hW) (emb packetO p 44 (x e)) := by
  have hb10 : bN design N p = 10 := geom_b hW
  have hb : 0 < bN design N p := by rw [hb10]; norm_num
  have hrN : design.h N % p = 3 * N := geom_hmod hW
  have hN20 : 20 ≤ N := hW.1
  have hp6 : 6 * N < p := hW.2.1
  have hp152 : 25 * p ≤ 152 * N := hW.2.2.1
  have hodd : p % 2 = 1 := hW.2.2.2
  set x' : Fin p → Fin 44 → Fp := fun e => projExtras (hKp hW) (emb packetO p 44 (x e)) with hx'
  have hpoly_inl : ∀ (k : Fin (bN design N p)) (u : Fin 4) (hk : k.val < 10),
      polx x' ((ckEquiv (hKp hW)).symm (Sum.inl (k, u))) =
        polx (X44 x) ⟨4 * k.val + u.val, by have := u.isLt; omega⟩ := by
    intro k u hk
    rw [hx', polx_proj _ _ _ (not_extra_inl _ k u)]
    congr 1
    exact Fin.ext (ck_inl_val _ k u)
  have hpoly_Z : ∀ z : Fin 2, polx x' ((ckEquiv (hKp hW)).symm (Sum.inr (Sum.inl z))) =
      polx (X44 x) ⟨40 + z.val, by have := z.isLt; omega⟩ := by
    intro z
    rw [hx', polx_proj _ _ _ (not_extra_Z _ z)]
    congr 1
    apply Fin.ext
    rw [ck_Z_val, hb10]
  have hk10 : ∀ k : Fin (bN design N p), k.val < 10 := fun k => by have := k.isLt; omega
  have hdeg3 : ∀ (A B C : Fp[X]), A.degree < p → B.degree < p → C.degree < p →
      (A - B + C).degree < p := fun A B C hA hB hC =>
    lt_of_le_of_lt (degree_add_le _ _) (max_lt
      (lt_of_le_of_lt (degree_sub_le _ _) (max_lt hA hB)) hC)
  refine exists_rows_of_orders hp2 hn (hKp hW) hb x' ?hX ?hr0 ?hrh (8 * N - p) (56 * N - 9 * p - 1)
    ?hlob ?hlot ?hA ?hC ?hZ ?hVb ?hVt
  case hX =>
    intro e j
    rw [hx']
    show projExtras _ _ _ = 0
    rw [projExtras_apply, if_pos ⟨j, by simp⟩]
  case hr0 => rw [hrN]; omega
  case hrh => rw [hrN]; omega
  case hlob => rw [hrN, geom_ja hW]; omega
  case hlot => rw [hrN, geom_rho hW]; omega
  case hA =>
    intro k
    have hk := hk10 k
    constructor
    · intro j hj
      rw [hrN] at hj
      rw [hpoly_inl k 0 hk]
      have := pt1_AF ⟨k.val, hk⟩
      exact chainAF hW x hker ⟨4 * k.val + (0 : Fin 4).val, by omega⟩ this.1 this.2.1 this.2.2 j hj
    · intro i hi
      rw [hrN] at hi
      rw [hpoly_inl k 1 hk]
      have := inf_AE ⟨k.val, hk⟩
      have h6 := wd6 hW; have h7 := wd7 hW
      exact coeff_of_inf _ (polx_degree _ _) (wd N p 6 + wd N p 7) (3 * N) (by omega) (by omega)
        (fun j hj => chainInf2 hW x hker ⟨4 * k.val + (1 : Fin 4).val, by omega⟩ this.1 this.2 j hj) i hi
  case hC =>
    intro k
    have hk := hk10 k
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      rw [hrN] at hj
      rw [hpoly_inl k 2 hk]
      exact chainCF hW x hker ⟨4 * k.val + (2 : Fin 4).val, by omega⟩ (pt1_CF ⟨k.val, hk⟩) j hj
    · intro j hj
      rw [hpoly_inl k 2 hk, hpoly_inl k 3 hk]
      exact chainDiff hW x hker ⟨4 * k.val + (2 : Fin 4).val, by omega⟩
        ⟨4 * k.val + (3 : Fin 4).val, by omega⟩ (by intro h; have := congrArg Fin.val h; simp at this)
        (ptm1_C ⟨k.val, hk⟩) j hj
    · intro i hi
      rw [hrN] at hi
      rw [hpoly_inl k 3 hk]
      have := inf_CE ⟨k.val, hk⟩
      have h6 := wd6 hW; have h7 := wd7 hW; have h8 := wd8 hW
      exact coeff_of_inf _ (polx_degree _ _) (wd N p 6 + wd N p 7 + wd N p 8) (3 * N - 1)
        (by omega) (by omega)
        (fun j hj => chainInf3 hW x hker ⟨4 * k.val + (3 : Fin 4).val, by omega⟩ this.1 this.2.1 this.2.2 j hj) i hi
  case hZ =>
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      rw [hrN] at hj
      rw [hpoly_Z 0]
      exact chainAF hW x hker ⟨40 + (0 : Fin 2).val, by omega⟩ pt1_ZF.1 pt1_ZF.2.1 pt1_ZF.2.2 j hj
    · intro i hi
      rw [hrN] at hi
      rw [hpoly_Z 1]
      have h6 := wd6 hW; have h7 := wd7 hW
      exact coeff_of_inf _ (polx_degree _ _) (wd N p 6 + wd N p 7) (3 * N) (by omega) (by omega)
        (fun j hj => chainInf2 hW x hker ⟨40 + (1 : Fin 2).val, by omega⟩ inf_ZE.1 inf_ZE.2 j hj) i hi
    · intro j hj
      rw [hpoly_Z 0, hpoly_Z 1]
      exact chainDiff hW x hker ⟨40 + (0 : Fin 2).val, by omega⟩ ⟨40 + (1 : Fin 2).val, by omega⟩
        (by intro h; have := congrArg Fin.val h; simp at this) ptm1_Z j hj
  case hVb =>
    intro i hi
    rw [hpoly_inl ⟨0, hb⟩ 1 (by omega), hpoly_inl ⟨0, hb⟩ 3 (by omega), hpoly_Z 1]
    have h6 := wd6 hW; have h7 := wd7 hW; have h8 := wd8 hW; have h9 := wd9 hW
    exact coeff_of_inf _ (hdeg3 _ _ _ (polx_degree _ _) (polx_degree _ _) (polx_degree _ _))
      (wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9) (8 * N - p) (by omega) (by omega)
      (fun j hj => chainVB hW x hker j hj) i hi
  case hVt =>
    intro i hi
    rw [hpoly_inl ⟨bN design N p - 1, by omega⟩ 1 (by simp only; omega),
      hpoly_inl ⟨bN design N p - 1, by omega⟩ 3 (by simp only; omega)]
    have h6 := wd6 hW; have h7 := wd7 hW; have h8 := wd8 hW; have h9 := wd9 hW; have h10 := wd10 hW
    have e1 : (⟨4 * (bN design N p - 1) + (1 : Fin 4).val, by omega⟩ : Fin 44) = 37 := by
      apply Fin.ext; simp only; omega
    have e3 : (⟨4 * (bN design N p - 1) + (3 : Fin 4).val, by omega⟩ : Fin 44) = 39 := by
      apply Fin.ext; simp only; omega
    simp only [e1, e3]
    exact coeff_of_inf _ (lt_of_le_of_lt (degree_add_le _ _) (max_lt (polx_degree _ _) (polx_degree _ _)))
      (wd N p 6 + wd N p 7 + wd N p 8 + wd N p 9 + wd N p 10) (56 * N - 9 * p - 1) (by omega) (by omega)
      (fun j hj => chainVT hW x hker j hj) i hi

end
end CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O
