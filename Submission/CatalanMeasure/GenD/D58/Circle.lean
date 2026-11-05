module

public import Submission.CatalanMeasure.GenD.Analytic.GapCircleGen
public import Submission.CatalanMeasure.GenD.D58.Budget
public import Submission.CatalanMeasure.GenD.D58.OddProfile

@[expose] public section

/-!
# D58: the circle certificate `GapCircleBound` (hcirc) and the side conditions

Gap `g = 401/2500`, `a = 2g/(1+g^2) = 2005000/6410801`, radius `rc = 1001/1000`, `C = 3`,
`wc = 52788/1000` (per `N`; sup of the exponent is 52.7849, `rho - 58 secondCost = 52.7887`).
Pieces (42 of them) of `|Re z|` in `[0, rc]`, one declaration each, checked by `decide +kernel`
against the generic `CircPiece.ok`; assembled by `circCover_cons`.  Python mirror: `CIRC/gen.py`.
-/

namespace CatalanMeasure.GenD
namespace D58
open CatalanMeasure.Parametric
noncomputable section
open Analytic

def circA : ℚ := 2005000 / 6410801
def circR : ℚ := 1001 / 1000
def circE : ℚ := 7096990416075491360717939143891605301678546410
def circCsq : ℚ := 9

def cp0 : CircPiece := ⟨0, (6573 / 100000 : ℚ), (2002001 / 1000000 : ℚ), (109981571 / 100000000 : ℚ), (85952873 / 25000000 : ℚ), (672758817 / 100000000 : ℚ)⟩
theorem cp0_ok : cp0.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp1 : CircPiece := ⟨(6573 / 100000 : ℚ), (8203 / 100000 : ℚ), (199768023 / 100000000 : ℚ), (21980939 / 20000000 : ℚ), (343247359 / 100000000 : ℚ), (335802507 / 50000000 : ℚ)⟩
theorem cp1_ok : cp1.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp2 : CircPiece := ⟨(8203 / 100000 : ℚ), (73 / 800 : ℚ), (199526749 / 100000000 : ℚ), (13732727 / 12500000 : ℚ), (171466199 / 50000000 : ℚ), (167740199 / 25000000 : ℚ)⟩
theorem cp2_ok : cp2.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp3 : CircPiece := ⟨(73 / 800 : ℚ), (4871 / 50000 : ℚ), (199366541 / 100000000 : ℚ), (109833363 / 100000000 : ℚ), (171361641 / 50000000 : ℚ), (670533057 / 100000000 : ℚ)⟩
theorem cp3_ok : cp3.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp4 : CircPiece := ⟨(4871 / 50000 : ℚ), (5097 / 50000 : ℚ), (3113277 / 1562500 : ℚ), (109812627 / 100000000 : ℚ), (17128541 / 5000000 : ℚ), (670221193 / 100000000 : ℚ)⟩
theorem cp4_ok : cp4.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp5 : CircPiece := ⟨(5097 / 50000 : ℚ), (5273 / 50000 : ℚ), (199159257 / 100000000 : ℚ), (27449143 / 25000000 : ℚ), (68490549 / 20000000 : ℚ), (41873729 / 6250000 : ℚ)⟩
theorem cp5_ok : cp5.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp6 : CircPiece := ⟨(5273 / 50000 : ℚ), (677 / 6250 : ℚ), (199085931 / 100000000 : ℚ), (27445891 / 25000000 : ℚ), (6847141 / 2000000 : ℚ), (83722989 / 12500000 : ℚ)⟩
theorem cp6_ok : cp6.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp7 : CircPiece := ⟨(677 / 6250 : ℚ), (346 / 3125 : ℚ), (199024499 / 100000000 : ℚ), (109772669 / 100000000 : ℚ), (171138441 / 50000000 : ℚ), (8370249 / 1250000 : ℚ)⟩
theorem cp7_ok : cp7.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp8 : CircPiece := ⟨(346 / 3125 : ℚ), (11279 / 100000 : ℚ), (39794333 / 20000000 : ℚ), (1097633 / 1000000 : ℚ), (68441587 / 20000000 : ℚ), (669478879 / 100000000 : ℚ)⟩
theorem cp8_ok : cp8.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp9 : CircPiece := ⟨(11279 / 100000 : ℚ), (5731 / 50000 : ℚ), (99462577 / 50000000 : ℚ), (109755053 / 100000000 : ℚ), (8553681 / 2500000 : ℚ), (669354719 / 100000000 : ℚ)⟩
theorem cp9_ok : cp9.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp10 : CircPiece := ⟨(5731 / 50000 : ℚ), (11627 / 100000 : ℚ), (198883309 / 100000000 : ℚ), (21949527 / 20000000 : ℚ), (85523159 / 25000000 : ℚ), (669243017 / 100000000 : ℚ)⟩
theorem cp10_ok : cp10.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp11 : CircPiece := ⟨(11627 / 100000 : ℚ), (11777 / 100000 : ℚ), (99422497 / 50000000 : ℚ), (27435211 / 25000000 : ℚ), (342042639 / 100000000 : ℚ), (669140739 / 100000000 : ℚ)⟩
theorem cp11_ok : cp11.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp12 : CircPiece := ⟨(11777 / 100000 : ℚ), (11917 / 100000 : ℚ), (198809681 / 100000000 : ℚ), (54867293 / 50000000 : ℚ), (341996561 / 100000000 : ℚ), (334523239 / 50000000 : ℚ)⟩
theorem cp12_ok : cp12.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp13 : CircPiece := ⟨(11917 / 100000 : ℚ), (12049 / 100000 : ℚ), (49694077 / 25000000 : ℚ), (3429021 / 3125000 : ℚ), (68390603 / 20000000 : ℚ), (133791479 / 20000000 : ℚ)⟩
theorem cp13_ok : cp13.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp14 : CircPiece := ⟨(12049 / 100000 : ℚ), (487 / 4000 : ℚ), (49686119 / 25000000 : ℚ), (13715379 / 12500000 : ℚ), (8547787 / 2500000 : ℚ), (334436213 / 50000000 : ℚ)⟩
theorem cp14_ok : cp14.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp15 : CircPiece := ⟨(487 / 4000 : ℚ), (1537 / 12500 : ℚ), (99356879 / 50000000 : ℚ), (10971759 / 10000000 : ℚ), (341871399 / 100000000 : ℚ), (668790431 / 100000000 : ℚ)⟩
theorem cp15_ok : cp15.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp16 : CircPiece := ⟨(1537 / 12500 : ℚ), (6207 / 50000 : ℚ), (99341977 / 50000000 : ℚ), (10971231 / 10000000 : ℚ), (5341133 / 1562500 : ℚ), (668710879 / 100000000 : ℚ)⟩
theorem cp16_ok : cp16.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp17 : CircPiece := ⟨(6207 / 50000 : ℚ), (12531 / 100000 : ℚ), (198654601 / 100000000 : ℚ), (109707111 / 100000000 : ℚ), (170897107 / 50000000 : ℚ), (66863253 / 10000000 : ℚ)⟩
theorem cp17_ok : cp17.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp18 : CircPiece := ⟨(12531 / 100000 : ℚ), (1581 / 12500 : ℚ), (3103519 / 1562500 : ℚ), (54850953 / 50000000 : ℚ), (341755873 / 100000000 : ℚ), (334277047 / 50000000 : ℚ)⟩
theorem cp18_ok : cp18.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp19 : CircPiece := ⟨(1581 / 12500 : ℚ), (6383 / 50000 : ℚ), (3971911 / 2000000 : ℚ), (109696653 / 100000000 : ℚ), (21357323 / 6250000 : ℚ), (20889841 / 3125000 : ℚ)⟩
theorem cp19_ok : cp19.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp20 : CircPiece := ⟨(6383 / 50000 : ℚ), (6443 / 50000 : ℚ), (198565347 / 100000000 : ℚ), (13711413 / 12500000 : ℚ), (170838881 / 50000000 : ℚ), (83549287 / 12500000 : ℚ)⟩
theorem cp20_ok : cp20.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp21 : CircPiece := ⟨(6443 / 50000 : ℚ), (1301 / 10000 : ℚ), (9926717 / 5000000 : ℚ), (54842907 / 50000000 : ℚ), (85409327 / 25000000 : ℚ), (133662307 / 20000000 : ℚ)⟩
theorem cp21_ok : cp21.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp22 : CircPiece := ⟨(1301 / 10000 : ℚ), (13139 / 100000 : ℚ), (19850199 / 10000000 : ℚ), (109680087 / 100000000 : ℚ), (341595103 / 100000000 : ℚ), (83528149 / 12500000 : ℚ)⟩
theorem cp22_ok : cp22.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp23 : CircPiece := ⟨(13139 / 100000 : ℚ), (531 / 4000 : ℚ), (49617 / 25000 : ℚ), (10967407 / 10000000 : ℚ), (170775379 / 50000000 : ℚ), (668134469 / 100000000 : ℚ)⟩
theorem cp23_ok : cp23.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp24 : CircPiece := ⟨(531 / 4000 : ℚ), (671 / 5000 : ℚ), (49607949 / 25000000 : ℚ), (54833831 / 50000000 : ℚ), (170751763 / 50000000 : ℚ), (668037841 / 100000000 : ℚ)⟩
theorem cp24_ok : cp24.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp25 : CircPiece := ⟨(671 / 5000 : ℚ), (1697 / 12500 : ℚ), (198392779 / 100000000 : ℚ), (109660757 / 100000000 : ℚ), (2731621 / 800000 : ℚ), (133586741 / 20000000 : ℚ)⟩
theorem cp25_ok : cp25.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp26 : CircPiece := ⟨(1697 / 12500 : ℚ), (13747 / 100000 : ℚ), (198350319 / 100000000 : ℚ), (27413311 / 25000000 : ℚ), (170698617 / 50000000 : ℚ), (333910191 / 50000000 : ℚ)⟩
theorem cp26_ok : cp26.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp27 : CircPiece := ⟨(13747 / 100000 : ℚ), (871 / 6250 : ℚ), (198303203 / 100000000 : ℚ), (27411227 / 25000000 : ℚ), (34133577 / 10000000 : ℚ), (333847317 / 50000000 : ℚ)⟩
theorem cp27_ok : cp27.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp28 : CircPiece := ⟨(871 / 6250 : ℚ), (14149 / 100000 : ℚ), (198250427 / 100000000 : ℚ), (109635573 / 100000000 : ℚ), (13650677 / 4000000 : ℚ), (83444223 / 12500000 : ℚ)⟩
theorem cp28_ok : cp28.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp29 : CircPiece := ⟨(14149 / 100000 : ℚ), (14393 / 100000 : ℚ), (198190069 / 100000000 : ℚ), (54812449 / 50000000 : ℚ), (341188191 / 100000000 : ℚ), (6673927 / 1000000 : ℚ)⟩
theorem cp29_ok : cp29.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp30 : CircPiece := ⟨(14393 / 100000 : ℚ), (14677 / 100000 : ℚ), (99059889 / 50000000 : ℚ), (109612469 / 100000000 : ℚ), (170548251 / 50000000 : ℚ), (66720511 / 10000000 : ℚ)⟩
theorem cp30_ok : cp30.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp31 : CircPiece := ⟨(14677 / 100000 : ℚ), (1877 / 12500 : ℚ), (99018209 / 50000000 : ℚ), (54798867 / 50000000 : ℚ), (85246943 / 25000000 : ℚ), (666982651 / 100000000 : ℚ)⟩
theorem cp31_ok : cp31.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp32 : CircPiece := ⟨(1877 / 12500 : ℚ), (1543 / 10000 : ℚ), (39586947 / 20000000 : ℚ), (21915953 / 20000000 : ℚ), (340855147 / 100000000 : ℚ), (666711299 / 100000000 : ℚ)⟩
theorem cp32_ok : cp32.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp33 : CircPiece := ⟨(1543 / 10000 : ℚ), (997 / 6250 : ℚ), (49451833 / 25000000 : ℚ), (5477863 / 5000000 : ℚ), (170344493 / 50000000 : ℚ), (166592831 / 25000000 : ℚ)⟩
theorem cp33_ok : cp33.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp34 : CircPiece := ⟨(997 / 6250 : ℚ), (3327 / 20000 : ℚ), (197641633 / 100000000 : ℚ), (21905601 / 20000000 : ℚ), (68094579 / 20000000 : ℚ), (665929179 / 100000000 : ℚ)⟩
theorem cp34_ok : cp34.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp35 : CircPiece := ⟨(3327 / 20000 : ℚ), (1757 / 10000 : ℚ), (197416279 / 100000000 : ℚ), (27372061 / 25000000 : ℚ), (340179037 / 100000000 : ℚ), (665327891 / 100000000 : ℚ)⟩
theorem cp35_ok : cp35.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp36 : CircPiece := ⟨(1757 / 10000 : ℚ), (1893 / 10000 : ℚ), (197092011 / 100000000 : ℚ), (54715543 / 50000000 : ℚ), (10617383 / 3125000 : ℚ), (16611569 / 2500000 : ℚ)⟩
theorem cp36_ok : cp36.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp37 : CircPiece := ⟨(1893 / 10000 : ℚ), (527 / 2500 : ℚ), (196587641 / 100000000 : ℚ), (27335577 / 25000000 : ℚ), (339098799 / 100000000 : ℚ), (663117311 / 100000000 : ℚ)⟩
theorem cp37_ok : cp37.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp38 : CircPiece := ⟨(527 / 2500 : ℚ), (24923 / 100000 : ℚ), (97855269 / 50000000 : ℚ), (21837659 / 20000000 : ℚ), (33795589 / 10000000 : ℚ), (660778107 / 100000000 : ℚ)⟩
theorem cp38_ok : cp38.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp39 : CircPiece := ⟨(24923 / 100000 : ℚ), (8327 / 25000 : ℚ), (96947739 / 50000000 : ℚ), (54435543 / 50000000 : ℚ), (335592441 / 100000000 : ℚ), (81992447 / 12500000 : ℚ)⟩
theorem cp39_ok : cp39.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp40 : CircPiece := ⟨(8327 / 25000 : ℚ), (60407 / 100000 : ℚ), (188791919 / 100000000 : ℚ), (107990159 / 100000000 : ℚ), (328959119 / 100000000 : ℚ), (160587603 / 25000000 : ℚ)⟩
theorem cp40_ok : cp40.ok circA circR circE circCsq 53 6 = true := by decide +kernel
def cp41 : CircPiece := ⟨(60407 / 100000 : ℚ), (1001 / 1000 : ℚ), (159637269 / 100000000 : ℚ), (51643587 / 50000000 : ℚ), (291430647 / 100000000 : ℚ), (565167423 / 100000000 : ℚ)⟩
theorem cp41_ok : cp41.ok circA circR circE circCsq 53 6 = true := by decide +kernel

theorem circCover_cons {c : ℚ} {p : CircPiece} {l : List CircPiece} (hc : p.lo = c)
    (hp : p.ok circA circR circE circCsq 53 6 = true)
    (hl : circCover circA circR circE circCsq 53 6 p.hi l = true) :
    circCover circA circR circE circCsq 53 6 c (p :: l) = true := by
  simp only [circCover, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hc, hp⟩, hl⟩

theorem circCover_nil {c : ℚ} (hc : c = circR) :
    circCover circA circR circE circCsq 53 6 c [] = true := by
  simp only [circCover, decide_eq_true_eq]
  exact hc

def circPieces : List CircPiece := [cp0, cp1, cp2, cp3, cp4, cp5, cp6, cp7, cp8, cp9, cp10, cp11, cp12, cp13, cp14, cp15, cp16, cp17, cp18, cp19, cp20, cp21, cp22, cp23, cp24, cp25, cp26, cp27, cp28, cp29, cp30, cp31, cp32, cp33, cp34, cp35, cp36, cp37, cp38, cp39, cp40, cp41]

theorem circ_cover : circCover circA circR circE circCsq 53 6 0 circPieces = true := by
  unfold circPieces
  exact circCover_cons rfl cp0_ok (circCover_cons rfl cp1_ok (circCover_cons rfl cp2_ok (circCover_cons rfl cp3_ok (circCover_cons rfl cp4_ok (circCover_cons rfl cp5_ok (circCover_cons rfl cp6_ok (circCover_cons rfl cp7_ok (circCover_cons rfl cp8_ok (circCover_cons rfl cp9_ok (circCover_cons rfl cp10_ok (circCover_cons rfl cp11_ok (circCover_cons rfl cp12_ok (circCover_cons rfl cp13_ok (circCover_cons rfl cp14_ok (circCover_cons rfl cp15_ok (circCover_cons rfl cp16_ok (circCover_cons rfl cp17_ok (circCover_cons rfl cp18_ok (circCover_cons rfl cp19_ok (circCover_cons rfl cp20_ok (circCover_cons rfl cp21_ok (circCover_cons rfl cp22_ok (circCover_cons rfl cp23_ok (circCover_cons rfl cp24_ok (circCover_cons rfl cp25_ok (circCover_cons rfl cp26_ok (circCover_cons rfl cp27_ok (circCover_cons rfl cp28_ok (circCover_cons rfl cp29_ok (circCover_cons rfl cp30_ok (circCover_cons rfl cp31_ok (circCover_cons rfl cp32_ok (circCover_cons rfl cp33_ok (circCover_cons rfl cp34_ok (circCover_cons rfl cp35_ok (circCover_cons rfl cp36_ok (circCover_cons rfl cp37_ok (circCover_cons rfl cp38_ok (circCover_cons rfl cp39_ok (circCover_cons rfl cp40_ok (circCover_cons rfl cp41_ok (circCover_nil rfl))))))))))))))))))))))))))))))))))))))))))

theorem circE_le_exp : (circE : ℝ) ≤ Real.exp (2 * (52788 / 1000 : ℝ)) := by
  have h1 : (2.7182818283 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
  have h2 := Real.sum_le_exp_of_nonneg (x := (576 / 1000 : ℝ)) (by norm_num) 12
  have h3 : (2.7182818283 : ℝ) ^ 105 ≤ Real.exp 105 := by
    calc _ ≤ Real.exp 1 ^ 105 := pow_le_pow_left₀ (by norm_num) h1 105
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have h4 : (2 * (52788 / 1000 : ℝ)) = 105 + 576 / 1000 := by norm_num
  rw [h4, Real.exp_add]
  have h5 : (circE : ℝ) ≤ 2.7182818283 ^ 105 *
      ∑ i ∈ Finset.range 12, (576 / 1000 : ℝ) ^ i / (i.factorial : ℝ) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num [circE]
  calc (circE : ℝ) ≤ _ := h5
    _ ≤ Real.exp 105 * Real.exp (576 / 1000) :=
        mul_le_mul h3 h2 (Finset.sum_nonneg (fun i _ => by positivity)) (Real.exp_pos _).le

theorem circA_eq : (2 * (401 / 2500 : ℝ) / (1 + (401 / 2500 : ℝ) ^ 2)) = ((circA : ℚ) : ℝ) := by
  norm_num [circA]

theorem circ_hg0 : (0 : ℝ) < 401 / 2500 := by norm_num
theorem circ_hg1 : (401 / 2500 : ℝ) < 1 := by norm_num
theorem circ_ha4 : 1 - (2 * (401 / 2500 : ℝ) / (1 + (401 / 2500 : ℝ) ^ 2)) ^ 2 ≤
    4 * (2 * (401 / 2500 : ℝ) / (1 + (401 / 2500 : ℝ) ^ 2)) := by norm_num
theorem circ_hr1 : (1 : ℝ) < 1001 / 1000 := by norm_num
theorem circ_hr2 : (1001 / 1000 : ℝ) ≤ 2 := by norm_num

theorem circ_hcirc : GapCircleBound Odd.design (2 * (401 / 2500 : ℝ) / (1 + (401 / 2500 : ℝ) ^ 2))
    (1001 / 1000) 3 (52788 / 1000) := by
  rw [circA_eq]
  have hr : ((1001 / 1000 : ℚ) : ℝ) = (1001 / 1000 : ℝ) := by norm_num
  have := gapCircleBound_of_cover (a := circA) (r := circR) (E := circE) (Csq := circCsq)
    (pieces := circPieces) Odd.design (d := 53) (m := 6) (by norm_num [Odd.design])
    (by norm_num [Odd.design]) (by norm_num [circA]) (by norm_num [circA])
    (by norm_num [circE]) (by simp [circPieces]) circ_cover (C := 3) (wc := 52788 / 1000)
    (by norm_num) (by norm_num [circCsq]) circE_le_exp
  simpa [circR] using this

end
end D58
end CatalanMeasure.GenD
