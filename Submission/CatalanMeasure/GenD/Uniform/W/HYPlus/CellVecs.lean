module
public import Submission.CatalanMeasure.GenD.Uniform.W.HYPlus.CellQ
@[expose] public section
set_option Elab.async false

/-!
# The HY+ cell vectors at `s = 9, 10, 11` and their exact rational identities

`u = u*` (single `H+(s;1..s-1)`), `v` (raw `Pd(s;2..s-1)`), `y = y*` (single `H-(s;1..s-1)`) on
blocks `-1..s-3` as primitive integer vectors (reference: `cert.py`); every identity of the HY+
cell predicate is verified over `ℚ` by `decide +kernel`, one declaration per identity.  The
constants (`γ`, `Ψ`, `Ψ'`, `κ`) are the values of the covectors themselves at fixed arguments.
-/

namespace CatalanMeasure.GenD.Uniform.W.HYPlus

/-- Rational identities for an H+ cell `u` at window `s` (`K` profile coordinates, `k0 = -1`). -/
def HpOK (K s : ℕ) (z : ℕ → ℤ) : Prop :=
  (∀ J, 1 ≤ J → J ≤ s - 1 → PhiHp K (-1) z J s = PhiHp K (-1) z 1 s) ∧
  (∀ J, 2 ≤ J → J ≤ s → (J : ℚ) * (PhiHp K (-1) z J (s + 1) - PhiHp K (-1) z 1 s) =
      2 * (PhiHp K (-1) z 2 (s + 1) - PhiHp K (-1) z 1 s)) ∧
  (∀ J, J + 2 ≤ s → ((J + 1 : ℕ) : ℚ) * (PhiHp K (-1) z 1 s - PhiHp K (-1) z J (s - 1)) =
      1 * (PhiHp K (-1) z 1 s - PhiHp K (-1) z 0 (s - 1)))

/-- Rational identities for an H- cell `y`. -/
def HmOK (K s : ℕ) (z : ℕ → ℤ) : Prop :=
  (∀ J, 1 ≤ J → J ≤ s - 1 → PhiHm K (-1) z J s = PhiHm K (-1) z 1 s) ∧
  (∀ J, 2 ≤ J → J ≤ s → (J : ℚ) * (PhiHm K (-1) z J (s + 1) - PhiHm K (-1) z 1 s) =
      2 * (PhiHm K (-1) z 2 (s + 1) - PhiHm K (-1) z 1 s)) ∧
  (∀ J, J + 2 ≤ s → ((J + 1 : ℕ) : ℚ) * (PhiHm K (-1) z 1 s - PhiHm K (-1) z J (s - 1)) =
      1 * (PhiHm K (-1) z 1 s - PhiHm K (-1) z 0 (s - 1)))

/-- Rational identities for the period cell `v`. -/
def VOK (K s : ℕ) (z : ℕ → ℤ) : Prop :=
  (∀ J, 2 ≤ J → J ≤ s - 1 → PhiHp K (-1) z J s = PhiHp K (-1) z J (s + 1)) ∧
  (∀ J, 1 ≤ J → J + 2 ≤ s → ((J + 1 : ℕ) : ℚ) * (PhiHp K (-1) z J (s - 1) - PhiHp K (-1) z J s) =
      2 * (PhiHp K (-1) z 1 (s - 1) - PhiHp K (-1) z 1 s))

/-- gcd of all `2 x 2` minors of two integer profiles. -/
def minorG (K : ℕ) (zU zV : ℕ → ℤ) : ℕ :=
  ((List.range K).flatMap fun i => (List.range K).map fun j =>
    (zU i * zV j - zU j * zV i).natAbs).foldl Nat.gcd 0

/-- gcd of the entries of an integer profile. -/
def entryG (K : ℕ) (z : ℕ → ℤ) : ℕ := ((List.range K).map fun k => (z k).natAbs).foldl Nat.gcd 0

def u9 : ℕ → ℤ := vecI [13605691709009556332419800684862000278, (-15647655482402337341471263115496039986), (-713550938814468499152022111085972045), (-327671851773957495487144150746898825), (-96586493883826834190098298854582720), (-47287817563930438066185667717141656), (-7718055021138621324496032180693693), (-3468041793120954400271973632685345)]

def v9 : ℕ → ℤ := vecI [392960889345313945045224042985491935487, (-345431445054386220867625805562951857167), 17555924275871029968560843991346792543, 6400028688819435028012984255969857903, 2004067495194989485593220564384188203, 788042572093660701645728616173412369, 142090424033984511015045084973853475, 49753124461493636765439507642855435]

def y9 : ℕ → ℤ := vecI [(-37508299466231200233899097560365459374), (-74829167228556061549761440552157724706), (-28229778859894899825657303469540605405), (-2783020478246115557571770352762824175), (-2107649934663466031594096073314477780), (-79664296069895574252435277743491292), (-117280071050460504753503145808204773), 14102754302374530666603939079250865]

-- s = 9
theorem u9_c1 : ∀ J ∈ List.range' 1 (9-1), PhiHp 8 (-1) u9 J 9 = PhiHp 8 (-1) u9 1 9 := by decide +kernel
theorem u9_c2 : ∀ J ∈ List.range' 2 (9-1), (J:ℚ) * (PhiHp 8 (-1) u9 J (9+1) - PhiHp 8 (-1) u9 1 9) = 2 * (PhiHp 8 (-1) u9 2 (9+1) - PhiHp 8 (-1) u9 1 9) := by decide +kernel
theorem u9_c3 : ∀ J ∈ List.range (9-1), ((J+1:ℕ):ℚ) * (PhiHp 8 (-1) u9 1 9 - PhiHp 8 (-1) u9 J (9-1)) = 1 * (PhiHp 8 (-1) u9 1 9 - PhiHp 8 (-1) u9 0 (9-1)) := by decide +kernel
theorem y9_c1 : ∀ J ∈ List.range' 1 (9-1), PhiHm 8 (-1) y9 J 9 = PhiHm 8 (-1) y9 1 9 := by decide +kernel
theorem y9_c2 : ∀ J ∈ List.range' 2 (9-1), (J:ℚ) * (PhiHm 8 (-1) y9 J (9+1) - PhiHm 8 (-1) y9 1 9) = 2 * (PhiHm 8 (-1) y9 2 (9+1) - PhiHm 8 (-1) y9 1 9) := by decide +kernel
theorem y9_c3 : ∀ J ∈ List.range (9-1), ((J+1:ℕ):ℚ) * (PhiHm 8 (-1) y9 1 9 - PhiHm 8 (-1) y9 J (9-1)) = 1 * (PhiHm 8 (-1) y9 1 9 - PhiHm 8 (-1) y9 0 (9-1)) := by decide +kernel
theorem v9_d1 : ∀ J ∈ List.range' 2 (9-2), PhiHp 8 (-1) v9 J 9 = PhiHp 8 (-1) v9 J (9+1) := by decide +kernel
theorem v9_d2 : ∀ J ∈ List.range' 1 (9-2), ((J+1:ℕ):ℚ) * (PhiHp 8 (-1) v9 J (9-1) - PhiHp 8 (-1) v9 J 9) = 2 * (PhiHp 8 (-1) v9 1 (9-1) - PhiHp 8 (-1) v9 1 9) := by decide +kernel
theorem y9_prim : entryG 8 y9 = 1 := by decide +kernel
theorem minor9_pos : 0 < minorG 8 u9 v9 := by decide +kernel

theorem hpOK9 : HpOK 8 9 u9 :=
  ⟨fun J h1 h2 => u9_c1 J (List.mem_range'_1.mpr ⟨h1, by omega⟩),
   fun J h1 h2 => u9_c2 J (List.mem_range'_1.mpr ⟨h1, by omega⟩),
   fun J h1 => u9_c3 J (List.mem_range.mpr (by omega))⟩
theorem hmOK9 : HmOK 8 9 y9 :=
  ⟨fun J h1 h2 => y9_c1 J (List.mem_range'_1.mpr ⟨h1, by omega⟩),
   fun J h1 h2 => y9_c2 J (List.mem_range'_1.mpr ⟨h1, by omega⟩),
   fun J h1 => y9_c3 J (List.mem_range.mpr (by omega))⟩
theorem vOK9 : VOK 8 9 v9 :=
  ⟨fun J h1 h2 => v9_d1 J (List.mem_range'_1.mpr ⟨h1, by omega⟩),
   fun J h1 h2 => v9_d2 J (List.mem_range'_1.mpr ⟨h1, by omega⟩)⟩

def u10 : ℕ → ℤ := vecI [77799409087233358766962027190230965553027966206, (-87884942226793861392049293810640979351960262239), (-5731666785766498822858588223543340916934425615), (-1682542683987415453863094807701237172097775885), (-953270973709629473939970466698421518093567185), (-250800999054124543757831913889771581543847077), (-130782322403771178282434222536778506051386837), (-19124022710496140888848772769959059992990855), (-8994257408147522555728047473290049881603905)]

def v10 : ℕ → ℤ := vecI [5688075416973549509033307005648759071261741548979, (-5055581505959181368807041710294397114506304357726), 305478372158188275104090732250844469148213233490, 90207400413908947340569993307921966345426207310, 43364043962203689684610816701115746707909836860, 11876835247369146961573558239679990692389582082, 5150724177633556033409321728069310911295553042, 816620333706184442260640512318711141277726430, 309322543880961888513152143918139129268646605]

def y10 : ℕ → ℤ := vecI [1299707451584117393130843066199224675991685431202, (-1430136159258175704682963783658234725917504320575), (-2207134272453705167219020772276388742789658573985), (-329133716675526208082966764086154149812451615885), (-242742880595706411123786512916003720063082275615), (-39953642510562673365288330220930166542453001781), (-27500110460965904068832877253483049270458848747), (-2599046479976852588765632153048852096515972375), (-1683151906162019318473232395964242320990161535)]

-- s = 10
theorem u10_c1 : ∀ J ∈ List.range' 1 (10-1), PhiHp 9 (-1) u10 J 10 = PhiHp 9 (-1) u10 1 10 := by decide +kernel
theorem u10_c2 : ∀ J ∈ List.range' 2 (10-1), (J:ℚ) * (PhiHp 9 (-1) u10 J (10+1) - PhiHp 9 (-1) u10 1 10) = 2 * (PhiHp 9 (-1) u10 2 (10+1) - PhiHp 9 (-1) u10 1 10) := by decide +kernel
theorem u10_c3 : ∀ J ∈ List.range (10-1), ((J+1:ℕ):ℚ) * (PhiHp 9 (-1) u10 1 10 - PhiHp 9 (-1) u10 J (10-1)) = 1 * (PhiHp 9 (-1) u10 1 10 - PhiHp 9 (-1) u10 0 (10-1)) := by decide +kernel
theorem y10_c1 : ∀ J ∈ List.range' 1 (10-1), PhiHm 9 (-1) y10 J 10 = PhiHm 9 (-1) y10 1 10 := by decide +kernel
theorem y10_c2 : ∀ J ∈ List.range' 2 (10-1), (J:ℚ) * (PhiHm 9 (-1) y10 J (10+1) - PhiHm 9 (-1) y10 1 10) = 2 * (PhiHm 9 (-1) y10 2 (10+1) - PhiHm 9 (-1) y10 1 10) := by decide +kernel
theorem y10_c3 : ∀ J ∈ List.range (10-1), ((J+1:ℕ):ℚ) * (PhiHm 9 (-1) y10 1 10 - PhiHm 9 (-1) y10 J (10-1)) = 1 * (PhiHm 9 (-1) y10 1 10 - PhiHm 9 (-1) y10 0 (10-1)) := by decide +kernel
theorem v10_d1 : ∀ J ∈ List.range' 2 (10-2), PhiHp 9 (-1) v10 J 10 = PhiHp 9 (-1) v10 J (10+1) := by decide +kernel
theorem v10_d2 : ∀ J ∈ List.range' 1 (10-2), ((J+1:ℕ):ℚ) * (PhiHp 9 (-1) v10 J (10-1) - PhiHp 9 (-1) v10 J 10) = 2 * (PhiHp 9 (-1) v10 1 (10-1) - PhiHp 9 (-1) v10 1 10) := by decide +kernel
theorem y10_prim : entryG 9 y10 = 1 := by decide +kernel
theorem minor10_pos : 0 < minorG 9 u10 v10 := by decide +kernel

theorem hpOK10 : HpOK 9 10 u10 :=
  ⟨fun J h1 h2 => u10_c1 J (List.mem_range'_1.mpr ⟨h1, by omega⟩),
   fun J h1 h2 => u10_c2 J (List.mem_range'_1.mpr ⟨h1, by omega⟩),
   fun J h1 => u10_c3 J (List.mem_range.mpr (by omega))⟩
theorem hmOK10 : HmOK 9 10 y10 :=
  ⟨fun J h1 h2 => y10_c1 J (List.mem_range'_1.mpr ⟨h1, by omega⟩),
   fun J h1 h2 => y10_c2 J (List.mem_range'_1.mpr ⟨h1, by omega⟩),
   fun J h1 => y10_c3 J (List.mem_range.mpr (by omega))⟩
theorem vOK10 : VOK 9 10 v10 :=
  ⟨fun J h1 h2 => v10_d1 J (List.mem_range'_1.mpr ⟨h1, by omega⟩),
   fun J h1 h2 => v10_d2 J (List.mem_range'_1.mpr ⟨h1, by omega⟩)⟩

def u11 : ℕ → ℤ := vecI [9998320332512086496315026752418477094141229678062546599044795, (-11437701184854287567786627056431727457137233323811675801303549), (-558142660407369468992787003476878309265900171871170482144620), (-276975747350760509237476708125490311698859475881108819498300), (-101304734374655015381686716664647853323931839366227632601350), (-54273118481841058837248295172114222632665478807191928380934), (-14496287013656386232322946801004801226528329941604559755068), (-7283657903908091209201676494205022841821360403852790761580), (-1038105840085055673428967865673543224542794865774145859165), (-476458714866554304661576173094500751315887865369044942245)]

def v11 : ℕ → ℤ := vecI [1629637632997358336762556103694886004779990484899532805094474725, (-1433213763111163640646230984984030951036716963784809097536329059), 80021880926113543586156837217279790925630557115033381801638380, 32017696027608316079219854184245393422454877539990916498772540, 12272495292487637744889207996407857597700738315204302076932230, 5408326528626607342469507028268547071619527055921270468643846, 1558063640882291711818413008600809730948955757393483745935932, 632757584295528952796544754223008814035531193735547679566060, 101137691340584598663607476798962021166013028662539364721085, 36330864635328248070072562462456681296604187605016293571205]

def y11 : ℕ → ℤ := vecI [(-820898084492869571353524075619471557746984292595852610825789), (-2372746076318016672351560292418947973084849897359521800156475), (-1236216002773453846882068033153396916774394933338183032241500), (-158102873066177743788617917783488679210808653290825439924980), (-123192134934609159101841027796757063877259843180529063249990), (-13271806853923213019976713209068637044911539454290428256698), (-12431358782553220455824579977059373278545688699348649009036), 115875856502225383178666031055615058544044041616045785820, (-669011207378607730976638917104746346455067370861026466405), 116627843701968061254159804323026549590651628043154159325]

-- s = 11
theorem u11_c1 : ∀ J ∈ List.range' 1 (11-1), PhiHp 10 (-1) u11 J 11 = PhiHp 10 (-1) u11 1 11 := by decide +kernel
theorem u11_c2 : ∀ J ∈ List.range' 2 (11-1), (J:ℚ) * (PhiHp 10 (-1) u11 J (11+1) - PhiHp 10 (-1) u11 1 11) = 2 * (PhiHp 10 (-1) u11 2 (11+1) - PhiHp 10 (-1) u11 1 11) := by decide +kernel
theorem u11_c3 : ∀ J ∈ List.range (11-1), ((J+1:ℕ):ℚ) * (PhiHp 10 (-1) u11 1 11 - PhiHp 10 (-1) u11 J (11-1)) = 1 * (PhiHp 10 (-1) u11 1 11 - PhiHp 10 (-1) u11 0 (11-1)) := by decide +kernel
theorem y11_c1 : ∀ J ∈ List.range' 1 (11-1), PhiHm 10 (-1) y11 J 11 = PhiHm 10 (-1) y11 1 11 := by decide +kernel
theorem y11_c2 : ∀ J ∈ List.range' 2 (11-1), (J:ℚ) * (PhiHm 10 (-1) y11 J (11+1) - PhiHm 10 (-1) y11 1 11) = 2 * (PhiHm 10 (-1) y11 2 (11+1) - PhiHm 10 (-1) y11 1 11) := by decide +kernel
theorem y11_c3 : ∀ J ∈ List.range (11-1), ((J+1:ℕ):ℚ) * (PhiHm 10 (-1) y11 1 11 - PhiHm 10 (-1) y11 J (11-1)) = 1 * (PhiHm 10 (-1) y11 1 11 - PhiHm 10 (-1) y11 0 (11-1)) := by decide +kernel
theorem v11_d1 : ∀ J ∈ List.range' 2 (11-2), PhiHp 10 (-1) v11 J 11 = PhiHp 10 (-1) v11 J (11+1) := by decide +kernel
theorem v11_d2 : ∀ J ∈ List.range' 1 (11-2), ((J+1:ℕ):ℚ) * (PhiHp 10 (-1) v11 J (11-1) - PhiHp 10 (-1) v11 J 11) = 2 * (PhiHp 10 (-1) v11 1 (11-1) - PhiHp 10 (-1) v11 1 11) := by decide +kernel
theorem y11_prim : entryG 10 y11 = 1 := by decide +kernel
theorem minor11_pos : 0 < minorG 10 u11 v11 := by decide +kernel

theorem hpOK11 : HpOK 10 11 u11 :=
  ⟨fun J h1 h2 => u11_c1 J (List.mem_range'_1.mpr ⟨h1, by omega⟩),
   fun J h1 h2 => u11_c2 J (List.mem_range'_1.mpr ⟨h1, by omega⟩),
   fun J h1 => u11_c3 J (List.mem_range.mpr (by omega))⟩
theorem hmOK11 : HmOK 10 11 y11 :=
  ⟨fun J h1 h2 => y11_c1 J (List.mem_range'_1.mpr ⟨h1, by omega⟩),
   fun J h1 h2 => y11_c2 J (List.mem_range'_1.mpr ⟨h1, by omega⟩),
   fun J h1 => y11_c3 J (List.mem_range.mpr (by omega))⟩
theorem vOK11 : VOK 10 11 v11 :=
  ⟨fun J h1 h2 => v11_d1 J (List.mem_range'_1.mpr ⟨h1, by omega⟩),
   fun J h1 h2 => v11_d2 J (List.mem_range'_1.mpr ⟨h1, by omega⟩)⟩

end CatalanMeasure.GenD.Uniform.W.HYPlus
