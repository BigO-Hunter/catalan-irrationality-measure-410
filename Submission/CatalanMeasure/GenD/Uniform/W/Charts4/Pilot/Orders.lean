module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Extract
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Geom146
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.SlotsOfOrders
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.Extras
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Prof CatalanMeasure.GenD.Uniform.W.Prof.Pilot146
  CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3 Finset
noncomputable section

theorem chain2 {Q : ℕ → Prop} {a b : ℕ} (h1 : ∀ j < a, Q j) (h2 : ∀ k < b, Q (a + k)) :
    ∀ j < a + b, Q j := by
  intro j hj
  by_cases h : j < a
  · exact h1 j h
  · have := h2 (j - a) (by omega)
    rwa [show a + (j - a) = j by omega] at this

theorem chain3 {Q : ℕ → Prop} {a b c : ℕ} (h1 : ∀ j < a, Q j) (h2 : ∀ k < b, Q (a + k))
    (h3 : ∀ k < c, Q (a + b + k)) : ∀ j < a + b + c, Q j :=
  chain2 (chain2 h1 h2) h3

theorem chain4 {Q : ℕ → Prop} {a b c d : ℕ} (h1 : ∀ j < a, Q j) (h2 : ∀ k < b, Q (a + k))
    (h3 : ∀ k < c, Q (a + b + k)) (h4 : ∀ k < d, Q (a + b + c + k)) : ∀ j < a + b + c + d, Q j :=
  chain2 (chain3 h1 h2 h3) h4

theorem chain5 {Q : ℕ → Prop} {a b c d e : ℕ} (h1 : ∀ j < a, Q j) (h2 : ∀ k < b, Q (a + k))
    (h3 : ∀ k < c, Q (a + b + k)) (h4 : ∀ k < d, Q (a + b + c + k))
    (h5 : ∀ k < e, Q (a + b + c + d + k)) : ∀ j < a + b + c + d + e, Q j :=
  chain2 (chain4 h1 h2 h3 h4) h5

variable {N p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

theorem coeff_of_inf (f : Fp[X]) (hf : f.degree < p) (W lo : ℕ) (hW : W ≤ p) (hlo : p - W ≤ lo)
    (hQ : ∀ j < W, f.coeff (p - 1 - j) = 0) : ∀ i, lo ≤ i → f.coeff i = 0 := by
  intro i hi
  by_cases hip : i < p
  · have := hQ (p - 1 - i) (by omega)
    rwa [show p - 1 - (p - 1 - i) = i by omega] at this
  · exact coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hf (by exact_mod_cast not_lt.mp hip))

theorem ck_inl_val {b ex K : ℕ} (hK : K = b * 4 + 2 + ex) (k : Fin b) (u : Fin 4) :
    ((ckEquiv hK).symm (Sum.inl (k, u))).val = 4 * k.val + u.val := by
  subst hK
  simp [ckEquiv, finProdFinEquiv]
  omega

theorem taylor_coeff_sub2 (a : Fp) (f g : Fp[X]) (j : ℕ) :
    (taylor a (f - 2 * g)).coeff j = (taylor a f).coeff j - 2 * (taylor a g).coeff j := by
  have h2 : (2 : Fp[X]) = C 2 := (map_ofNat C 2).symm
  rw [h2, map_sub, taylor_mul, taylor_C, coeff_sub, coeff_C_mul]

/-- Unit row at a Taylor jet. -/
theorem vtaylor_unit (x : Fin p → Fin packetO.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 11) (a : Fp)
    (o : ℕ) (hjet : ∀ k, jetP N p g k = Charts3.taylorJet (m := p) (d := packetO.d) a (o + k)) (c : Fin 44)
    (hrow : hasRow g (unitL c) = true) :
    ∀ k < wd N p g, (taylor a (polx (fun e => emb packetO p 44 (x e)) c)).coeff (o + k) = 0 := by
  intro k hk
  have := vanish_hasRow x hker g hg k hk (unitL c) hrow
  rw [hjet k, sum_unitL, emb_taylorJet, taylorJet_coord] at this
  exact this

/-- Difference row `e_a - 2 e_b` at a Taylor jet. -/
theorem vtaylor_diff (x : Fin p → Fin packetO.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 11) (a : Fp)
    (o : ℕ) (hjet : ∀ k, jetP N p g k = Charts3.taylorJet (m := p) (d := packetO.d) a (o + k)) (c d : Fin 44)
    (hcd : c ≠ d) (hrow : hasRow g (diff2L c d) = true) :
    ∀ k < wd N p g, (taylor a (polx (fun e => emb packetO p 44 (x e)) c -
        2 * polx (fun e => emb packetO p 44 (x e)) d)).coeff (o + k) = 0 := by
  intro k hk
  have := vanish_hasRow x hker g hg k hk (diff2L c d) hrow
  rw [hjet k, sum_diff2L c d hcd, emb_taylorJet, taylorJet_coord, taylorJet_coord] at this
  rw [taylor_coeff_sub2]; exact this

/-- Unit row at a reversed coefficient jet. -/
theorem vinf_unit (x : Fin p → Fin packetO.d → Fp) (hker : JetKer N p x) (g : ℕ) (hg : g < 11)
    (o : ℕ) (hjet : ∀ k, jetP N p g k = jetInf (o + k)) (hb : o + wd N p g ≤ p) (c : Fin 44)
    (hrow : hasRow g (unitL c) = true) :
    ∀ k < wd N p g, (polx (fun e => emb packetO p 44 (x e)) c).coeff (p - 1 - (o + k)) = 0 := by
  intro k hk
  have := vanish_hasRow x hker g hg k hk (unitL c) hrow
  rw [hjet k, sum_unitL, emb_jetInf, jetInf_coord, if_pos (by omega)] at this
  exact this

end
end CatalanMeasure.GenD.Uniform.W.Charts4.Pilot146O
