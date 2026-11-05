module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.Check.HdomSound
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts6.Check.DomGen
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# `hdomCheckG`: the generic `hdom` check for both virtual kinds at both ends, A-high and A-low
-/
namespace CatalanMeasure.GenD.Uniform.W.Charts6.Check
open Polynomial Finset Module CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W.Prof (Packet emb chartMap Mx)

/-- The check; `m.vlow` is the bottom virtual kind (`E_zero + F_degree` if true), `zt` the top one. -/
def hdomCheckG (pk : Packet) (m : Meta) (win : List Aff) (cs : Cert) (zt : Bool) : Bool :=
  let T := tOK pk m win cs
  let I := iOK pk m win cs
  (List.range m.b).all (fun k =>
    (if m.high then (pcOf m (4 * k)).isNone && T Pt.p1 [(1, 4 * k + 1)] ((rA.add hpA).sub pAff)
     else T Pt.p1 [(1, 4 * k)] (rA.add hpA)) &&
    I [(1, 4 * k + 1)] rA &&
    T Pt.p1 [(1, 4 * k + 2)] rA && T Pt.m1 [(1, 4 * k + 2), (-2, 4 * k + 3)] hpA &&
    I [(1, 4 * k + 3)] (rA.sub ⟨0, 0, 1⟩)) &&
  (if m.high then (pcOf m (4 * m.b)).isNone && T Pt.p1 [(1, 4 * m.b + 1)] ((rA.add hpA).sub pAff)
   else T Pt.p1 [(1, 4 * m.b)] (rA.add hpA)) &&
  I [(1, 4 * m.b + 1)] rA && T Pt.m1 [(1, 4 * m.b), (-2, 4 * m.b + 1)] hpA &&
  (if m.vlow then
    T Pt.z0 [(1, 1), (-1, 3), (1, 4 * m.b + 1)] pAff && I [(1, 0), (-1, 2), (1, 4 * m.b)] ((lobA m).add pAff)
   else I [(1, 1), (-1, 3), (1, 4 * m.b + 1)] (lobA m)) &&
  (if zt then
    T Pt.z0 [(1, 4 * (m.b - 1) + 1), (1, 4 * (m.b - 1) + 3)] pAff &&
      I [(1, 4 * (m.b - 1)), (1, 4 * (m.b - 1) + 2)] ((lotA m).add pAff)
   else I [(1, 4 * (m.b - 1) + 1), (1, 4 * (m.b - 1) + 3)] (lotA m)) &&
  (if m.vlow then true else holds win cs (lobA m)) && (if zt then true else holds win cs (lotA m)) &&
  (if m.high then holds win cs ((rA.add hpA).sub pAff)
   else holds win cs (pAff.sub ((rA.add hpA).add ⟨0, 0, 1⟩))) &&
  holds win cs (pAff.sub (rA.add ⟨0, 0, 1⟩)) && holds win cs (rA.sub ⟨0, 0, 1⟩) && decide (0 < m.b)

noncomputable section
variable {p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

theorem T2z_sound {pk : Packet} {m : Meta} {win : List Aff} {cs : Cert} {N : ℕ} {x : Fin p → Fin pk.d → Fp}
    (C : Ctx pk m win N x) (i1 j1 : ℕ) (req : Aff) (h : tOK pk m win cs Pt.z0 [(1, i1), (1, j1)] req = true) :
    ∀ j : ℕ, (j : ℤ) < req.eval (N : ℤ) (((p : ℤ) - 1) / 2) →
      (polAt (fun e => emb pk p pk.n (x e)) (pcOf m i1) + polAt (fun e => emb pk p pk.n (x e)) (pcOf m j1)).coeff j = 0 := by
  intro j hj
  have h1 := holds_sound win cs _ _ _ C.hwin h
  rw [Aff.eval_sub, leadAff'_eval m pk N p Pt.z0 _ C.hlen2 C.hnn] at h1
  have := order_z0 pk m x C.hker C.hlen (vecOf m pk.n [(1, i1), (1, j1)]) j (by unfold leadWd; omega)
  rwa [rowPoly_virt2] at this

theorem hdom_gen_high (pk : Packet) (m : Meta) (win : List Aff) (cs : Cert) (zt : Bool) {N : ℕ} (x : Fin p → Fin pk.d → Fp)
    (C : Ctx pk m win N x) (hp2 : p ≠ 2) (hN : 0 < N) (hn : 1 ≤ dsg.n N)
    (hb : bN dsg N p = m.b) (hrN : dsg.h N % p = 3 * N)
    (hja : ((gja (dsg.g N) p : ℕ) : ℤ) = (jaA m).eval (N : ℤ) (((p : ℤ) - 1) / 2))
    (hrho : ((grho (dsg.n N) (dsg.g N) p : ℕ) : ℤ) = (rhoA m).eval (N : ℤ) (((p : ℤ) - 1) / 2))
    (hh : m.high = true)
    (hcheck : hdomCheckG pk m win cs zt = true) :
    ∃ c : Fin (dsg.n N) → Fp, Theta (P := dsg) (N := N) hp2 hn
      (rfl : bN dsg N p * 4 + 2 + m.ex = bN dsg N p * 4 + 2 + m.ex) c =
        X' m pk (rfl : bN dsg N p * 4 + 2 + m.ex = bN dsg N p * 4 + 2 + m.ex) x := by
  have hpos := (Fact.out : p.Prime).pos
  have hgja := (gja_spec (g := dsg.g N) hpos).2
  simp only [hdomCheckG, hh, if_true, Bool.false_eq_true, if_false, Bool.and_eq_true, List.all_eq_true,
    List.mem_range, decide_eq_true_eq] at hcheck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hall, hz1⟩, hz2⟩, hz3⟩, hbot⟩, htop⟩, hlobnn⟩, hlotnn⟩, hhigh⟩, hpgt⟩, hrpos⟩, hbpos⟩ := hcheck
  have hodd := C.hodd
  have hpe : pAff.eval (N : ℤ) (((p : ℤ) - 1) / 2) = (p : ℤ) := by simp only [pAff, Aff.eval]; omega
  have hre : rA.eval (N : ℤ) (((p : ℤ) - 1) / 2) = 3 * (N : ℤ) := by simp [rA, Aff.eval]
  have hhe : hpA.eval (N : ℤ) (((p : ℤ) - 1) / 2) = ((p : ℤ) - 1) / 2 := by simp [hpA, Aff.eval]
  have hhi := holds_sound win cs _ _ _ C.hwin hhigh
  have hrp := holds_sound win cs _ _ _ C.hwin hrpos
  rw [Aff.eval_sub, Aff.eval_add, hre, hhe, hpe] at hhi
  have hlobv : (lobA m).eval (N : ℤ) (((p : ℤ) - 1) / 2) = 3 * (N : ℤ) - (jaA m).eval (N : ℤ) (((p : ℤ) - 1) / 2) := by
    simp only [lobA, Aff.eval_sub, hre]
  have hlotv : (lotA m).eval (N : ℤ) (((p : ℤ) - 1) / 2) =
      3 * (N : ℤ) + (rhoA m).eval (N : ℤ) (((p : ℤ) - 1) / 2) - p := by
    simp only [lotA, Aff.eval_sub, Aff.eval_add, hre, hpe]
  have hbpos' : 0 < bN dsg N p := by rw [hb]; exact hbpos
  have hk : ∀ k : Fin (bN dsg N p), k.val < m.b := fun k => by have := k.isLt; omega
  have blk0 : ∀ k : Fin (bN dsg N p), polx (X' m pk rfl x) ((ckEquiv (rfl : bN dsg N p * 4 + 2 + m.ex = _)).symm (Sum.inl (k, 0))) =
      polAt (fun e => emb pk p pk.n (x e)) (pcOf m (4 * k.val)) := fun k => by rw [polxX'_blk]; rfl
  have blk1 : ∀ k : Fin (bN dsg N p), polx (X' m pk rfl x) ((ckEquiv (rfl : bN dsg N p * 4 + 2 + m.ex = _)).symm (Sum.inl (k, 1))) =
      polAt (fun e => emb pk p pk.n (x e)) (pcOf m (4 * k.val + 1)) := fun k => by rw [polxX'_blk]; rfl
  have blk2 : ∀ k : Fin (bN dsg N p), polx (X' m pk rfl x) ((ckEquiv (rfl : bN dsg N p * 4 + 2 + m.ex = _)).symm (Sum.inl (k, 2))) =
      polAt (fun e => emb pk p pk.n (x e)) (pcOf m (4 * k.val + 2)) := fun k => by rw [polxX'_blk]; rfl
  have blk3 : ∀ k : Fin (bN dsg N p), polx (X' m pk rfl x) ((ckEquiv (rfl : bN dsg N p * 4 + 2 + m.ex = _)).symm (Sum.inl (k, 3))) =
      polAt (fun e => emb pk p pk.n (x e)) (pcOf m (4 * k.val + 3)) := fun k => by rw [polxX'_blk]; rfl
  have zz0 : polx (X' m pk rfl x) ((ckEquiv (rfl : bN dsg N p * 4 + 2 + m.ex = _)).symm (Sum.inr (Sum.inl 0))) =
      polAt (fun e => emb pk p pk.n (x e)) (pcOf m (4 * m.b)) := by
    rw [polxX'_Z]; show polAt _ (pcOf m (bN dsg N p * 4 + 0)) = _
    have e : bN dsg N p * 4 + 0 = 4 * m.b := by omega
    rw [e]
  have zz1 : polx (X' m pk rfl x) ((ckEquiv (rfl : bN dsg N p * 4 + 2 + m.ex = _)).symm (Sum.inr (Sum.inl 1))) =
      polAt (fun e => emb pk p pk.n (x e)) (pcOf m (4 * m.b + 1)) := by
    rw [polxX'_Z]; show polAt _ (pcOf m (bN dsg N p * 4 + 1)) = _
    have e : bN dsg N p * 4 + 1 = 4 * m.b + 1 := by omega
    rw [e]
  have hRA : ∀ j : ℕ, j < dsg.h N % p + (p - 1) / 2 - p → (j : ℤ) <
      ((rA.add hpA).sub pAff).eval (N : ℤ) (((p : ℤ) - 1) / 2) := by
    intro j hj; rw [Aff.eval_sub, Aff.eval_add, hre, hhe, hpe]; rw [hrN] at hj; omega
  refine exists_rows_high_gen hp2 hn rfl hbpos' (X' m pk rfl x) ?hX ?hr0 ?hrh ?hFA ?hFZ
    ((lobA m).eval (N : ℤ) (((p : ℤ) - 1) / 2)).toNat ((lotA m).eval (N : ℤ) (((p : ℤ) - 1) / 2)).toNat
    ?hA ?hC ?hZ ?hVb ?hVt
  case hX =>
    intro e j
    show projExtras _ _ _ = 0
    rw [projExtras_apply, if_pos ⟨j, by simp⟩]
  case hr0 => rw [hrN]; omega
  case hrh => rw [hrN]; omega
  case hFA =>
    intro k
    rw [blk0]
    have := (hall k.val (hk k)).1.1.1.1.1
    have h0 : pcOf m (4 * k.val) = none := by simpa [Option.isNone_iff_eq_none] using this
    simp [h0, polAt]
  case hFZ =>
    rw [zz0]
    have h0 : pcOf m (4 * m.b) = none := by simpa [Option.isNone_iff_eq_none] using hz1.1
    simp [h0, polAt]
  case hA =>
    intro k
    have hA5 := hall k.val (hk k)
    refine ⟨fun j hj => ?_, fun i hi => ?_⟩
    · rw [blk1]
      exact T1_sound C Pt.p1 1 (Or.inl ⟨rfl, rfl⟩) _ _ hA5.1.1.1.1.2 j (hRA j hj)
    · rw [blk1]
      refine I1_sound C _ _ hA5.1.1.1.2 i ?_
      rw [hre]; rw [hrN] at hi; omega
  case hC =>
    intro k
    have hA5 := hall k.val (hk k)
    refine ⟨fun j hj => ?_, fun j hj => ?_, fun i hi => ?_⟩
    · rw [blk2]
      refine T1_sound C Pt.p1 1 (Or.inl ⟨rfl, rfl⟩) _ _ hA5.1.1.2 j ?_
      rw [hre]; rw [hrN] at hj; omega
    · rw [blk2, blk3]
      refine Td_sound C Pt.m1 (-1) (Or.inr ⟨rfl, rfl⟩) _ _ _ hA5.1.2 j ?_
      rw [hhe]; omega
    · rw [blk3]
      refine I1_sound C _ _ hA5.2 i ?_
      rw [Aff.eval_sub, hre]; simp [Aff.eval]; rw [hrN] at hi; omega
  case hZ =>
    refine ⟨fun j hj => ?_, fun i hi => ?_, fun j hj => ?_⟩
    · rw [zz1]
      exact T1_sound C Pt.p1 1 (Or.inl ⟨rfl, rfl⟩) _ _ hz1.2 j (hRA j hj)
    · rw [zz1]
      refine I1_sound C _ _ hz2 i ?_
      rw [hre]; rw [hrN] at hi; omega
    · rw [zz0, zz1]
      refine Td_sound C Pt.m1 (-1) (Or.inr ⟨rfl, rfl⟩) _ _ _ hz3 j ?_
      rw [hhe]; omega
  case hVb =>
    rw [blk1 ⟨0, hbpos'⟩, blk3 ⟨0, hbpos'⟩, zz1, blk0 ⟨0, hbpos'⟩, blk2 ⟨0, hbpos'⟩, zz0]
    by_cases hvl : m.vlow = true
    · right
      simp only [hvl, if_true, Bool.and_eq_true] at hbot
      refine ⟨fun i => ?_, fun i hi => ?_⟩
      · by_cases hip : i < p
        · exact T3_sound C 1 3 (4 * m.b + 1) pAff hbot.1 i (by rw [hpe]; exact_mod_cast hip)
        · have hdeg3 : ∀ (A B D : Fp[X]), A.degree < p → B.degree < p → D.degree < p → (A - B + D).degree < p :=
            fun A B D hA hB hD => lt_of_le_of_lt (degree_add_le _ _) (max_lt
              (lt_of_le_of_lt (degree_sub_le _ _) (max_lt hA hB)) hD)
          exact coeff_eq_zero_of_degree_lt (lt_of_lt_of_le
            (hdeg3 _ _ _ (polAt_degree _ _) (polAt_degree _ _) (polAt_degree _ _)) (by exact_mod_cast not_lt.mp hip))
      · refine I3_sound C 0 2 (4 * m.b) ((lobA m).add pAff) hbot.2 i ?_
        rw [Aff.eval_add, hlobv, hpe]; omega
    · left
      have hvl' : m.vlow = false := by simpa using hvl
      simp only [hvl', Bool.false_eq_true, if_false] at hbot hlobnn
      have hlobe := holds_sound win cs _ _ _ C.hwin hlobnn
      rw [hlobv] at hlobe
      refine ⟨fun i hi => ?_, ?_⟩
      · refine I3_sound C 1 3 (4 * m.b + 1) (lobA m) hbot i ?_
        rw [hlobv]; omega
      · rw [hrN]; omega
  case hVt =>
    rw [blk1 ⟨bN dsg N p - 1, by omega⟩, blk3 ⟨bN dsg N p - 1, by omega⟩, blk0 ⟨bN dsg N p - 1, by omega⟩,
      blk2 ⟨bN dsg N p - 1, by omega⟩]
    have e0 : 4 * (bN dsg N p - 1) = 4 * (m.b - 1) := by omega
    have e1 : 4 * (bN dsg N p - 1) + 1 = 4 * (m.b - 1) + 1 := by omega
    have e2 : 4 * (bN dsg N p - 1) + 2 = 4 * (m.b - 1) + 2 := by omega
    have e3 : 4 * (bN dsg N p - 1) + 3 = 4 * (m.b - 1) + 3 := by omega
    simp only [Fin.val_mk, e0, e1, e2, e3]
    by_cases hzv : zt = true
    · right
      simp only [hzv, if_true, Bool.and_eq_true] at htop
      refine ⟨fun i => ?_, fun i hi => ?_⟩
      · by_cases hip : i < p
        · exact T2z_sound C (4 * (m.b - 1) + 1) (4 * (m.b - 1) + 3) pAff htop.1 i (by rw [hpe]; exact_mod_cast hip)
        · have hdeg2 : ∀ (A B : Fp[X]), A.degree < p → B.degree < p → (A + B).degree < p :=
            fun A B hA hB => lt_of_le_of_lt (degree_add_le _ _) (max_lt hA hB)
          exact coeff_eq_zero_of_degree_lt (lt_of_lt_of_le
            (hdeg2 _ _ (polAt_degree _ _) (polAt_degree _ _)) (by exact_mod_cast not_lt.mp hip))
      · refine I2_sound C (4 * (m.b - 1)) (4 * (m.b - 1) + 2) ((lotA m).add pAff) htop.2 i ?_
        rw [Aff.eval_add, hlotv, hpe]; omega
    · left
      have hzv' : zt = false := by simpa using hzv
      simp only [hzv', Bool.false_eq_true, if_false] at htop hlotnn
      have hlote := holds_sound win cs _ _ _ C.hwin hlotnn
      rw [hlotv] at hlote
      refine ⟨fun i hi => ?_, ?_⟩
      · refine I2_sound C _ _ (lotA m) htop i ?_
        rw [hlotv]; omega
      · rw [hrN]; omega

theorem hdom_gen_low (pk : Packet) (m : Meta) (win : List Aff) (cs : Cert) (zt : Bool) {N : ℕ} (x : Fin p → Fin pk.d → Fp)
    (C : Ctx pk m win N x) (hp2 : p ≠ 2) (hN : 0 < N) (hn : 1 ≤ dsg.n N)
    (hb : bN dsg N p = m.b) (hrN : dsg.h N % p = 3 * N)
    (hja : ((gja (dsg.g N) p : ℕ) : ℤ) = (jaA m).eval (N : ℤ) (((p : ℤ) - 1) / 2))
    (hrho : ((grho (dsg.n N) (dsg.g N) p : ℕ) : ℤ) = (rhoA m).eval (N : ℤ) (((p : ℤ) - 1) / 2))
    (hh : m.high = false)
    (hcheck : hdomCheckG pk m win cs zt = true) :
    ∃ c : Fin (dsg.n N) → Fp, Theta (P := dsg) (N := N) hp2 hn
      (rfl : bN dsg N p * 4 + 2 + m.ex = bN dsg N p * 4 + 2 + m.ex) c =
        X' m pk (rfl : bN dsg N p * 4 + 2 + m.ex = bN dsg N p * 4 + 2 + m.ex) x := by
  have hpos := (Fact.out : p.Prime).pos
  simp only [hdomCheckG, hh, if_true, Bool.false_eq_true, if_false, Bool.and_eq_true, List.all_eq_true,
    List.mem_range, decide_eq_true_eq] at hcheck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hall, hz1⟩, hz2⟩, hz3⟩, hbot⟩, htop⟩, hlobnn⟩, hlotnn⟩, hhigh⟩, hpgt⟩, hrpos⟩, hbpos⟩ := hcheck
  have hgja := (gja_spec (g := dsg.g N) hpos).2
  have hodd := C.hodd
  have hpe : pAff.eval (N : ℤ) (((p : ℤ) - 1) / 2) = (p : ℤ) := by simp only [pAff, Aff.eval]; omega
  have hre : rA.eval (N : ℤ) (((p : ℤ) - 1) / 2) = 3 * (N : ℤ) := by simp [rA, Aff.eval]
  have hhe : hpA.eval (N : ℤ) (((p : ℤ) - 1) / 2) = ((p : ℤ) - 1) / 2 := by simp [hpA, Aff.eval]
  have hlobv : (lobA m).eval (N : ℤ) (((p : ℤ) - 1) / 2) = 3 * (N : ℤ) - (jaA m).eval (N : ℤ) (((p : ℤ) - 1) / 2) := by
    simp only [lobA, Aff.eval_sub, hre]
  have hlotv : (lotA m).eval (N : ℤ) (((p : ℤ) - 1) / 2) =
      3 * (N : ℤ) + (rhoA m).eval (N : ℤ) (((p : ℤ) - 1) / 2) - p := by
    simp only [lotA, Aff.eval_sub, Aff.eval_add, hre, hpe]
  have hbpos' : 0 < bN dsg N p := by rw [hb]; exact hbpos
  have hk : ∀ k : Fin (bN dsg N p), k.val < m.b := fun k => by have := k.isLt; omega
  have blk0 : ∀ k : Fin (bN dsg N p), polx (X' m pk rfl x) ((ckEquiv (rfl : bN dsg N p * 4 + 2 + m.ex = _)).symm (Sum.inl (k, 0))) =
      polAt (fun e => emb pk p pk.n (x e)) (pcOf m (4 * k.val)) := fun k => by rw [polxX'_blk]; rfl
  have blk1 : ∀ k : Fin (bN dsg N p), polx (X' m pk rfl x) ((ckEquiv (rfl : bN dsg N p * 4 + 2 + m.ex = _)).symm (Sum.inl (k, 1))) =
      polAt (fun e => emb pk p pk.n (x e)) (pcOf m (4 * k.val + 1)) := fun k => by rw [polxX'_blk]; rfl
  have blk2 : ∀ k : Fin (bN dsg N p), polx (X' m pk rfl x) ((ckEquiv (rfl : bN dsg N p * 4 + 2 + m.ex = _)).symm (Sum.inl (k, 2))) =
      polAt (fun e => emb pk p pk.n (x e)) (pcOf m (4 * k.val + 2)) := fun k => by rw [polxX'_blk]; rfl
  have blk3 : ∀ k : Fin (bN dsg N p), polx (X' m pk rfl x) ((ckEquiv (rfl : bN dsg N p * 4 + 2 + m.ex = _)).symm (Sum.inl (k, 3))) =
      polAt (fun e => emb pk p pk.n (x e)) (pcOf m (4 * k.val + 3)) := fun k => by rw [polxX'_blk]; rfl
  have zz0 : polx (X' m pk rfl x) ((ckEquiv (rfl : bN dsg N p * 4 + 2 + m.ex = _)).symm (Sum.inr (Sum.inl 0))) =
      polAt (fun e => emb pk p pk.n (x e)) (pcOf m (4 * m.b)) := by
    rw [polxX'_Z]; show polAt _ (pcOf m (bN dsg N p * 4 + 0)) = _
    have e : bN dsg N p * 4 + 0 = 4 * m.b := by omega
    rw [e]
  have zz1 : polx (X' m pk rfl x) ((ckEquiv (rfl : bN dsg N p * 4 + 2 + m.ex = _)).symm (Sum.inr (Sum.inl 1))) =
      polAt (fun e => emb pk p pk.n (x e)) (pcOf m (4 * m.b + 1)) := by
    rw [polxX'_Z]; show polAt _ (pcOf m (bN dsg N p * 4 + 1)) = _
    have e : bN dsg N p * 4 + 1 = 4 * m.b + 1 := by omega
    rw [e]
  have hhi := holds_sound win cs _ _ _ C.hwin hhigh
  simp only [Aff.eval_sub, Aff.eval_add, hre, hhe, hpe] at hhi
  simp only [Aff.eval] at hhi
  have hz0 : (⟨0, 0, 0⟩ : Aff).eval (N : ℤ) (((p : ℤ) - 1) / 2) = 0 := by simp [Aff.eval]
  refine exists_rows_low_gen hp2 hn rfl hbpos' (X' m pk rfl x) ?hX ?hr0 ?hrh
    ((lobA m).eval (N : ℤ) (((p : ℤ) - 1) / 2)).toNat ((lotA m).eval (N : ℤ) (((p : ℤ) - 1) / 2)).toNat
    ?hA ?hC ?hZ ?hVb ?hVt
  case hX =>
    intro e j
    show projExtras _ _ _ = 0
    rw [projExtras_apply, if_pos ⟨j, by simp⟩]
  case hr0 => rw [hrN]; omega
  case hrh => rw [hrN]; omega
  case hA =>
    intro k
    have hA5 := hall k.val (hk k)
    refine ⟨fun j hj => ?_, fun i hi => ?_⟩
    · rw [blk0]
      refine T1_sound C Pt.p1 1 (Or.inl ⟨rfl, rfl⟩) _ _ hA5.1.1.1.1 j ?_
      rw [Aff.eval_add, hre, hhe]; rw [hrN] at hj; omega
    · rw [blk1]
      refine I1_sound C _ _ hA5.1.1.1.2 i ?_
      rw [hre]; rw [hrN] at hi; omega
  case hC =>
    intro k
    have hA5 := hall k.val (hk k)
    refine ⟨fun j hj => ?_, fun j hj => ?_, fun i hi => ?_⟩
    · rw [blk2]
      refine T1_sound C Pt.p1 1 (Or.inl ⟨rfl, rfl⟩) _ _ hA5.1.1.2 j ?_
      rw [hre]; rw [hrN] at hj; omega
    · rw [blk2, blk3]
      refine Td_sound C Pt.m1 (-1) (Or.inr ⟨rfl, rfl⟩) _ _ _ hA5.1.2 j ?_
      rw [hhe]; omega
    · rw [blk3]
      refine I1_sound C _ _ hA5.2 i ?_
      rw [Aff.eval_sub, hre]; simp [Aff.eval]; rw [hrN] at hi; omega
  case hZ =>
    refine ⟨fun j hj => ?_, fun i hi => ?_, fun j hj => ?_⟩
    · rw [zz0]
      refine T1_sound C Pt.p1 1 (Or.inl ⟨rfl, rfl⟩) _ _ hz1 j ?_
      rw [Aff.eval_add, hre, hhe]; rw [hrN] at hj; omega
    · rw [zz1]
      refine I1_sound C _ _ hz2 i ?_
      rw [hre]; rw [hrN] at hi; omega
    · rw [zz0, zz1]
      refine Td_sound C Pt.m1 (-1) (Or.inr ⟨rfl, rfl⟩) _ _ _ hz3 j ?_
      rw [hhe]; omega
  case hVb =>
    rw [blk1 ⟨0, hbpos'⟩, blk3 ⟨0, hbpos'⟩, zz1, blk0 ⟨0, hbpos'⟩, blk2 ⟨0, hbpos'⟩, zz0]
    by_cases hvl : m.vlow = true
    · right
      simp only [hvl, if_true, Bool.and_eq_true] at hbot
      refine ⟨fun i => ?_, fun i hi => ?_⟩
      · by_cases hip : i < p
        · exact T3_sound C 1 3 (4 * m.b + 1) pAff hbot.1 i (by rw [hpe]; exact_mod_cast hip)
        · have hdeg3 : ∀ (A B D : Fp[X]), A.degree < p → B.degree < p → D.degree < p → (A - B + D).degree < p :=
            fun A B D hA hB hD => lt_of_le_of_lt (degree_add_le _ _) (max_lt
              (lt_of_le_of_lt (degree_sub_le _ _) (max_lt hA hB)) hD)
          exact coeff_eq_zero_of_degree_lt (lt_of_lt_of_le
            (hdeg3 _ _ _ (polAt_degree _ _) (polAt_degree _ _) (polAt_degree _ _)) (by exact_mod_cast not_lt.mp hip))
      · refine I3_sound C 0 2 (4 * m.b) ((lobA m).add pAff) hbot.2 i ?_
        rw [Aff.eval_add, hlobv, hpe]; omega
    · left
      have hvl' : m.vlow = false := by simpa using hvl
      simp only [hvl', Bool.false_eq_true, if_false] at hbot hlobnn
      have hlobe := holds_sound win cs _ _ _ C.hwin hlobnn
      rw [hlobv] at hlobe
      refine ⟨fun i hi => ?_, ?_⟩
      · refine I3_sound C 1 3 (4 * m.b + 1) (lobA m) hbot i ?_
        rw [hlobv]; omega
      · rw [hrN]; omega
  case hVt =>
    rw [blk1 ⟨bN dsg N p - 1, by omega⟩, blk3 ⟨bN dsg N p - 1, by omega⟩, blk0 ⟨bN dsg N p - 1, by omega⟩,
      blk2 ⟨bN dsg N p - 1, by omega⟩]
    have e0 : 4 * (bN dsg N p - 1) = 4 * (m.b - 1) := by omega
    have e1 : 4 * (bN dsg N p - 1) + 1 = 4 * (m.b - 1) + 1 := by omega
    have e2 : 4 * (bN dsg N p - 1) + 2 = 4 * (m.b - 1) + 2 := by omega
    have e3 : 4 * (bN dsg N p - 1) + 3 = 4 * (m.b - 1) + 3 := by omega
    simp only [Fin.val_mk, e0, e1, e2, e3]
    by_cases hzv : zt = true
    · right
      simp only [hzv, if_true, Bool.and_eq_true] at htop
      refine ⟨fun i => ?_, fun i hi => ?_⟩
      · by_cases hip : i < p
        · exact T2z_sound C (4 * (m.b - 1) + 1) (4 * (m.b - 1) + 3) pAff htop.1 i (by rw [hpe]; exact_mod_cast hip)
        · have hdeg2 : ∀ (A B : Fp[X]), A.degree < p → B.degree < p → (A + B).degree < p :=
            fun A B hA hB => lt_of_le_of_lt (degree_add_le _ _) (max_lt hA hB)
          exact coeff_eq_zero_of_degree_lt (lt_of_lt_of_le
            (hdeg2 _ _ (polAt_degree _ _) (polAt_degree _ _)) (by exact_mod_cast not_lt.mp hip))
      · refine I2_sound C (4 * (m.b - 1)) (4 * (m.b - 1) + 2) ((lotA m).add pAff) htop.2 i ?_
        rw [Aff.eval_add, hlotv, hpe]; omega
    · left
      have hzv' : zt = false := by simpa using hzv
      simp only [hzv', Bool.false_eq_true, if_false] at htop hlotnn
      have hlote := holds_sound win cs _ _ _ C.hwin hlotnn
      rw [hlotv] at hlote
      refine ⟨fun i hi => ?_, ?_⟩
      · refine I2_sound C _ _ (lotA m) htop i ?_
        rw [hlotv]; omega
      · rw [hrN]; omega

theorem hdom_sound_gen (pk : Packet) (m : Meta) (win : List Aff) (cs : Cert) (zt : Bool) {N : ℕ}
    (x : Fin p → Fin pk.d → Fp)
    (C : Ctx pk m win N x) (hp2 : p ≠ 2) (hN : 0 < N) (hn : 1 ≤ dsg.n N)
    (hb : bN dsg N p = m.b) (hrN : dsg.h N % p = 3 * N)
    (hja : ((gja (dsg.g N) p : ℕ) : ℤ) = (jaA m).eval (N : ℤ) (((p : ℤ) - 1) / 2))
    (hrho : ((grho (dsg.n N) (dsg.g N) p : ℕ) : ℤ) = (rhoA m).eval (N : ℤ) (((p : ℤ) - 1) / 2))
    (hcheck : hdomCheckG pk m win cs zt = true) :
    ∃ c : Fin (dsg.n N) → Fp, Theta (P := dsg) (N := N) hp2 hn
      (rfl : bN dsg N p * 4 + 2 + m.ex = bN dsg N p * 4 + 2 + m.ex) c =
        X' m pk (rfl : bN dsg N p * 4 + 2 + m.ex = bN dsg N p * 4 + 2 + m.ex) x := by
  cases hh : m.high
  · exact hdom_gen_low pk m win cs zt x C hp2 hN hn hb hrN hja hrho hh hcheck
  · exact hdom_gen_high pk m win cs zt x C hp2 hN hn hb hrN hja hrho hh hcheck

end
end CatalanMeasure.GenD.Uniform.W.Charts6.Check
