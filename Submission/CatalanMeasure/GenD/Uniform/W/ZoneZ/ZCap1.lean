module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.CellsCap
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZCellInst2
@[expose] public section
set_option Elab.async false

/-!
# Window `s+1` cell facts in `ZMod p`
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial OAI.InternalCatalan CatalanMeasure.GenD.Uniform.Prefix
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- `z_J` for general cell vectors. -/
def zz (p K H : ℕ) [Fact p.Prime] (u u2 y1 y2 : Fin K → ZMod p) (J : ℕ) (c : ℕ) : ZMod p :=
  match c with
  | 0 => (profTp' p K).psi H J (5 : ℕ) u - (profTp' p K).psi H J (4 : ℕ) u
  | 1 => (profTp' p K).psi H J (5 : ℕ) u2 - (profTp' p K).psi H J (4 : ℕ) u2
  | 2 => (profTm' p K).psi H J (5 : ℕ) y1
  | 3 => (profTm' p K).psi H J (5 : ℕ) y2
  | _ => 0

/-- The cap-window cell facts. -/
structure CellHypCap (p K H : ℕ) [Fact p.Prime] (u u2 y1 y2 : Fin K → ZMod p) : Prop where
  zr3 : ∀ c < 4, 3 * zz p K H u u2 y1 y2 3 c = 2 * zz p K H u u2 y1 y2 2 c
  zr4 : ∀ c < 4, 2 * zz p K H u u2 y1 y2 4 c = zz p K H u u2 y1 y2 2 c

theorem zz_eq (hm : MomUnits p) {K H J : ℕ} (u u2 y1 y2 : ℕ → ℚ)
    (hu : ∀ k < K, u k ∈ unitSub p) (hu2 : ∀ k < K, u2 k ∈ unitSub p)
    (hy1 : ∀ k < K, y1 k ∈ unitSub p) (hy2 : ∀ k < K, y2 k ∈ unitSub p)
    (hJ : J < 7) (hH : 8 ≤ H) (c : ℕ) (hc : c < 4) :
    zz p K H (zvec p K u) (zvec p K u2) (zvec p K y1) (zvec p K y2) J c =
      palindromicRatResidue p ((Q.zq K u u2 y1 y2 J).getD c 0) := by
  have a5 := fun z hz => psiTp_zvec hm (K := K) (J := J) (H := H) z hz hJ (σ := 5) (by omega) (by omega)
  have a4 := fun z hz => psiTp_zvec hm (K := K) (J := J) (H := H) z hz hJ (σ := 4) (by omega) (by omega)
  have b5 := fun z hz => psiTm_zvec hm (K := K) (J := J) (H := H) z hz hJ (σ := 5) (by omega) (by omega)
  have mp5 := fun z (hz : ∀ k < K, z k ∈ unitSub p) => fTp_mem hm z hz (J := J) (σ := 5) hJ (by omega)
  have mp4 := fun z (hz : ∀ k < K, z k ∈ unitSub p) => fTp_mem hm z hz (J := J) (σ := 4) hJ (by omega)
  have mm5 := fun z (hz : ∀ k < K, z k ∈ unitSub p) => fTm_mem hm z hz (J := J) (σ := 5) hJ (by omega)
  interval_cases c
  · simp only [zz, Q.zq, List.getD_cons_zero]
    show (profTp p K).psi H J ((5 : ℕ) : ℤ) _ - (profTp p K).psi H J ((4 : ℕ) : ℤ) _ = _
    rw [a5 u hu, a4 u hu]
    exact (res_sub (mp5 u hu) (mp4 u hu)).2.symm
  · simp only [zz, Q.zq, List.getD_cons_succ, List.getD_cons_zero]
    show (profTp p K).psi H J ((5 : ℕ) : ℤ) _ - (profTp p K).psi H J ((4 : ℕ) : ℤ) _ = _
    rw [a5 u2 hu2, a4 u2 hu2]
    exact (res_sub (mp5 u2 hu2) (mp4 u2 hu2)).2.symm
  · simp only [zz, Q.zq, List.getD_cons_succ, List.getD_cons_zero]
    show (profTm p K).psi H J ((5 : ℕ) : ℤ) _ = _
    rw [b5 y1 hy1]
  · simp only [zz, Q.zq, List.getD_cons_succ, List.getD_cons_zero]
    show (profTm p K).psi H J ((5 : ℕ) : ℤ) _ = _
    rw [b5 y2 hy2]

theorem zz_mem (hm : MomUnits p) {K J : ℕ} (u u2 y1 y2 : ℕ → ℚ)
    (hu : ∀ k < K, u k ∈ unitSub p) (hu2 : ∀ k < K, u2 k ∈ unitSub p)
    (hy1 : ∀ k < K, y1 k ∈ unitSub p) (hy2 : ∀ k < K, y2 k ∈ unitSub p)
    (hJ : J < 7) (c : ℕ) (hc : c < 4) : (Q.zq K u u2 y1 y2 J).getD c 0 ∈ unitSub p := by
  interval_cases c
  · simpa [Q.zq] using Subring.sub_mem _ (fTp_mem hm u hu hJ (σ := 5) (by omega))
      (fTp_mem hm u hu hJ (σ := 4) (by omega))
  · simpa [Q.zq] using Subring.sub_mem _ (fTp_mem hm u2 hu2 hJ (σ := 5) (by omega))
      (fTp_mem hm u2 hu2 hJ (σ := 4) (by omega))
  · simpa [Q.zq] using fTm_mem hm y1 hy1 hJ (σ := 5) (by omega)
  · simpa [Q.zq] using fTm_mem hm y2 hy2 hJ (σ := 5) (by omega)

theorem zrank_int (hm : MomUnits p) {K H : ℕ} (hH : 8 ≤ H) (u u2 y1 y2 : ℕ → ℚ)
    (hu : ∀ k < K, u k ∈ unitSub p) (hu2 : ∀ k < K, u2 k ∈ unitSub p)
    (hy1 : ∀ k < K, y1 k ∈ unitSub p) (hy2 : ∀ k < K, y2 k ∈ unitSub p)
    (J1 J2 : ℕ) (hJ1 : J1 < 7) (hJ2 : J2 < 7) (a b : ℤ)
    (hQ : ∀ c ∈ [0, 1, 2, 3], (a : ℚ) * (Q.zq K u u2 y1 y2 J1).getD c 0 =
      (b : ℚ) * (Q.zq K u u2 y1 y2 J2).getD c 0) (c : ℕ) (hc : c < 4) :
    (a : ZMod p) * zz p K H (zvec p K u) (zvec p K u2) (zvec p K y1) (zvec p K y2) J1 c =
      (b : ZMod p) * zz p K H (zvec p K u) (zvec p K u2) (zvec p K y1) (zvec p K y2) J2 c := by
  have m1 := zz_mem hm u u2 y1 y2 hu hu2 hy1 hy2 hJ1 c hc
  have m2 := zz_mem hm u u2 y1 y2 hu hu2 hy1 hy2 hJ2 c hc
  have key := congrArg (resHom p)
    (Subtype.ext (hQ c (by interval_cases c <;> simp)) :
      (⟨(a : ℚ), intCast_mem _ _⟩ : unitSub p) * ⟨(Q.zq K u u2 y1 y2 J1).getD c 0, m1⟩ =
        ⟨(b : ℚ), intCast_mem _ _⟩ * ⟨(Q.zq K u u2 y1 y2 J2).getD c 0, m2⟩)
  simp only [map_mul, resHom_apply, palindromicRatResidue_intCast] at key
  rw [zz_eq hm u u2 y1 y2 hu hu2 hy1 hy2 hJ1 (by omega) c hc,
    zz_eq hm u u2 y1 y2 hu hu2 hy1 hy2 hJ2 (by omega) c hc]
  exact key

theorem cellHypCap_H (hp2 : p ≠ 2) (hc : ¬ p ∣ ZcH) {H : ℕ} (hH : 8 ≤ H) :
    CellHypCap p 4 H (zvec p 4 Q.uH) (zvec p 4 Q.u2H) (zvec p 4 Q.y1H) (zvec p 4 Q.y2H) := by
  have hm := momUnits_H hp2 hc
  constructor
  · intro c hc4
    have := zrank_int hm hH Q.uH Q.u2H Q.y1H Q.y2H (fun k hk => uH_mem hp2 hc hk)
      (fun k hk => u2H_mem hp2 hc hk) (fun k hk => y1H_mem hp2 hc hk) (fun k hk => y2H_mem hp2 hc hk)
      3 2 (by omega) (by omega) 3 2 (by simpa using Q.H_z3_rank) c hc4
    simpa using this
  · intro c hc4
    have := zrank_int hm hH Q.uH Q.u2H Q.y1H Q.y2H (fun k hk => uH_mem hp2 hc hk)
      (fun k hk => u2H_mem hp2 hc hk) (fun k hk => y1H_mem hp2 hc hk) (fun k hk => y2H_mem hp2 hc hk)
      4 2 (by omega) (by omega) 2 1 (by simpa using Q.H_z4_rank) c hc4
    simpa using this

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
