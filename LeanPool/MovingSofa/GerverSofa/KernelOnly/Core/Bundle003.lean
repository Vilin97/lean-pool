/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle001
public import Mathlib.Tactic.FinCases
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.KernelOnly.PartB.Semantics.Batch001`.
* `GerverSofa.KernelOnly.PartB.Certificates.Batch004`.
* `GerverSofa.KernelOnly.PartB.Certificates.Batch003`.
* `GerverSofa.KernelOnly.PartB.Certificates.Batch002`.
* `GerverSofa.KernelOnly.PartB.Certificates.Batch001`.
* `GerverSofa.KernelOnly.PartB.Semantics.Batch002`.
-/

public section

noncomputable section

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartB.Arithmetic`.
* `KernelOnly.PartB.CellCache`.
-/

public section

noncomputable section

section

/-!
# Part B exact product-cell arithmetic

This module is deliberately independent of the noncomputable Part A root.
It contains only exact rational interval data, so all 64 diagnostic and
production rows can be kernel-reduced without rebuilding semantic layers.
-/

public section

namespace GerverSofa
namespace PartB

open RatInterval

/-- Exact target `0.171` used by the continuum theorem. -/
@[expose]
def targetQ : ℚ := 171 / 1000

/-- The 64 closed mesh cells determined by the 65 nodes `iπ/128`. -/
abbrev Cell := Fin 64

/-- Exact rational mesh coefficient. -/
@[expose]
def nodeCoeff (i : Nat) : ℚ := (i : ℚ) / 128

/-- Hull of two rational intervals. -/
@[expose]
def intervalHull (a b : RatInterval) : RatInterval :=
  ⟨min a.lo b.lo, max a.hi b.hi⟩

/-- Componentwise hull of two planar interval boxes. -/
@[expose]
def pointHull (a b : RatInterval × RatInterval) : RatInterval × RatInterval :=
  (intervalHull a.1 b.1, intervalHull a.2 b.2)

/-- Exact interval enclosure of one physical time cell. -/
@[expose]
def cellTimeInterval (i : Cell) : RatInterval :=
  intervalHull
    (ExactReplay.scale (nodeCoeff i.1) ExactReplay.piI)
    (ExactReplay.scale (nodeCoeff (i.1 + 1)) ExactReplay.piI)

/-- Exact interval evaluation of one path phase on one complete mesh cell. -/
@[expose]
def cellPieceInterval (j : Nat) (i : Cell) : RatInterval × RatInterval :=
  let t := cellTimeInterval i
  let k11 := ExactReplay.getI ExactReplay.fullInputBox 0
  let k12 := ExactReplay.getI ExactReplay.fullInputBox 1
  let k21 := ExactReplay.getI ExactReplay.fullInputBox 2
  let k22 := ExactReplay.getI ExactReplay.fullInputBox 3
  let k31 := ExactReplay.getI ExactReplay.fullInputBox 4
  let k32 := ExactReplay.getI ExactReplay.fullInputBox 5
  let k41 := ExactReplay.getI ExactReplay.fullInputBox 6
  let k42 := ExactReplay.getI ExactReplay.fullInputBox 7
  let k51 := ExactReplay.getI ExactReplay.fullInputBox 8
  let k52 := ExactReplay.getI ExactReplay.fullInputBox 9
  let a1 := ExactReplay.getI ExactReplay.fullInputBox 10
  let a2 := ExactReplay.getI ExactReplay.fullInputBox 11
  let b1 := ExactReplay.getI ExactReplay.fullInputBox 12
  let b2 := ExactReplay.getI ExactReplay.fullInputBox 13
  let c1 := ExactReplay.getI ExactReplay.fullInputBox 14
  let c2 := ExactReplay.getI ExactReplay.fullInputBox 15
  let d1 := ExactReplay.getI ExactReplay.fullInputBox 16
  let d2 := ExactReplay.getI ExactReplay.fullInputBox 17
  let e1 := ExactReplay.getI ExactReplay.fullInputBox 18
  let e2 := ExactReplay.getI ExactReplay.fullInputBox 19
  let one := ExactReplay.oneI
  let half := RatInterval.point (1 / 2)
  let quarter := RatInterval.point (1 / 4)
  let ct := ExactReplay.cosineInterval t
  let st := ExactReplay.sineInterval t
  let data : RatInterval × RatInterval × RatInterval × RatInterval :=
    if j = 1 then
      (RatInterval.sub
          (RatInterval.add (RatInterval.mul a1 ct) (RatInterval.mul a2 st)) one,
       RatInterval.sub
          (RatInterval.add (RatInterval.mul (RatInterval.neg a2) ct)
            (RatInterval.mul a1 st)) half,
       k11, k12)
    else if j = 2 then
      (RatInterval.add
          (RatInterval.add
            (RatInterval.mul (RatInterval.neg quarter) (RatInterval.mul t t))
            (RatInterval.mul b1 t)) b2,
       RatInterval.sub
          (RatInterval.sub (RatInterval.mul half t) b1) one,
       k21, k22)
    else if j = 3 then
      (RatInterval.sub c1 t, RatInterval.add c2 t, k31, k32)
    else if j = 4 then
      (RatInterval.sub
          (RatInterval.add (RatInterval.mul (RatInterval.neg half) t) d1) one,
       RatInterval.add
          (RatInterval.add
            (RatInterval.mul (RatInterval.neg quarter) (RatInterval.mul t t))
            (RatInterval.mul d1 t)) d2,
       k41, k42)
    else
      (RatInterval.sub
          (RatInterval.add (RatInterval.mul e1 ct) (RatInterval.mul e2 st)) half,
       RatInterval.sub
          (RatInterval.add (RatInterval.mul (RatInterval.neg e2) ct)
            (RatInterval.mul e1 st)) one,
       k51, k52)
  let r1 := RatInterval.sub (RatInterval.mul ct data.1)
      (RatInterval.mul st data.2.1)
  let r2 := RatInterval.add (RatInterval.mul st data.1)
      (RatInterval.mul ct data.2.1)
  (RatInterval.add r1 data.2.2.1, RatInterval.add r2 data.2.2.2)

/-- The path enclosure for a cell.  Four cells contain a switching angle and
therefore take the hull of the two adjacent analytic phases. -/
@[expose]
def cellPathInterval (i : Cell) : RatInterval × RatInterval :=
  if i.1 = 0 then cellPieceInterval 1 i
  else if i.1 = 1 then pointHull (cellPieceInterval 1 i) (cellPieceInterval 2 i)
  else if i.1 ≤ 26 then cellPieceInterval 2 i
  else if i.1 = 27 then pointHull (cellPieceInterval 2 i) (cellPieceInterval 3 i)
  else if i.1 ≤ 35 then cellPieceInterval 3 i
  else if i.1 = 36 then pointHull (cellPieceInterval 3 i) (cellPieceInterval 4 i)
  else if i.1 ≤ 61 then cellPieceInterval 4 i
  else if i.1 = 62 then pointHull (cellPieceInterval 4 i) (cellPieceInterval 5 i)
  else cellPieceInterval 5 i

/-- Exact interval image of `Gu` on one product cell. -/
@[expose]
def guCellInterval (i j : Cell) : RatInterval :=
  let xi := cellPathInterval i
  let xj := cellPathInterval j
  let c := ExactReplay.cosineInterval (cellTimeInterval i)
  let s := ExactReplay.sineInterval (cellTimeInterval i)
  let dx := RatInterval.sub xi.1 xj.1
  let dy := RatInterval.sub xi.2 xj.2
  RatInterval.add
    (RatInterval.add ExactReplay.oneI (RatInterval.mul dx c))
    (RatInterval.mul dy s)

/-- Exact interval image of `Gv` on one product cell. -/
@[expose]
def gvCellInterval (i j : Cell) : RatInterval :=
  let xi := cellPathInterval i
  let xj := cellPathInterval j
  let c := ExactReplay.cosineInterval (cellTimeInterval i)
  let s := ExactReplay.sineInterval (cellTimeInterval i)
  let dx := RatInterval.sub xi.1 xj.1
  let dy := RatInterval.sub xi.2 xj.2
  RatInterval.add
    (RatInterval.add ExactReplay.oneI
      (RatInterval.mul dx (RatInterval.neg s)))
    (RatInterval.mul dy c)

end PartB
end GerverSofa

end

end

section

/-!
# Shared exact interval evaluations for the product-cell certificates

Each table is checked against the original evaluator by the Lean kernel.
Sharing these evaluations avoids repeating the same Taylor computations in every row.
-/

public section

namespace GerverSofa.PartB

/-- Reconstruct a natural number from base-10³⁵ chunks to share decimal elaboration. -/
@[expose]
def naturalFromChunks (chunks : List ℕ) : ℕ :=
  chunks.foldl (fun value digit => value * 10 ^ 35 + digit) 0

/-- The exact cached path-coordinate pair for cell 0, sharing kernel reduction. -/
@[expose]
def cachedPath00 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      32806,
      10584377830325517359742700908850139,
      81607231342652381947323845793090454,
      96144429388381831087652413032396797,
      36868186593732552082470650873461363]) : ℤ))
      (naturalFromChunks [
      5000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      7671443713161115292750432506903126,
      43012829623794223200639225310598163,
      33075928858326908145305686159237480,
      91804944677611174042315416975718857])
      (naturalFromChunks [
      12,
      50000000000000000000000000000000000,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (-((naturalFromChunks [
      37647662,
      97447248562927873266328560474815312,
      52671058691422530540628864810962801]) : ℤ))
      (naturalFromChunks [
      500000000000,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      87326,
      79792061110285957775373564882726820,
      13026632299000909904799014917975,
      23616446106846274741656489466558196,
      56629420125081855603683656880487509])
      (naturalFromChunks [
      2500000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 1, sharing kernel reduction. -/
@[expose]
def cachedPath01 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      397036559637444138821,
      23429525818379333822931949222691947,
      56024914729271489239510386186014461,
      63013117025166082450127814194603137,
      19506445506199262500255354407394047]) : ℤ))
      (naturalFromChunks [
      25600000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      67381694628068574712,
      83394745669405697834748999450389856,
      81605402638451307158023210957921285,
      62191351641107813192015354106152141,
      69296959622689866676384082977573983])
      (naturalFromChunks [
      6553600000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      342928,
      50341465024201468247210548101732037,
      79271707896851698787958705410829626,
      75662558918120062032679167808769808,
      7365225904837141520082684788612007])
      (naturalFromChunks [
      10000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      2281520274224607845462,
      45701440614950960933322900164023200,
      89547874173976888161305214283996027,
      10849698557208910987992676093182092,
      50000036718501707078589374865104737])
      (naturalFromChunks [
      32768000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 2, sharing kernel reduction. -/
@[expose]
def cachedPath02 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      257772707128381117139,
      53978082056034263614025552654969234,
      5677716471911388018466159748398086,
      55737085031605040111489958464383129,
      43581452883468530887685734453022763]) : ℤ))
      (naturalFromChunks [
      12800000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      105594279288160461622,
      23118192145018609615577389422239556,
      10464295176902166486759014940652048,
      74082432524857500494799764093759241,
      94830813003930941592709856379344343])
      (naturalFromChunks [
      16384000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      1398712699947913978358,
      25805078325706303648518730929878394,
      20081081063356190170462867234790298,
      57907457058855645071830435777098150,
      86042787547446458393668863106067779])
      (naturalFromChunks [
      20480000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      26566583229087814189,
      33178357444382229822963276002699166,
      73942154990466666177652686009829343,
      30487308499161687512543927329346219,
      54195585922384154538050876594980787])
      (naturalFromChunks [
      256000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 3, sharing kernel reduction. -/
@[expose]
def cachedPath03 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      167431482098179646296,
      27653758568720291948081335555214563,
      13535285732814069244132527171883621,
      20204239016170134246262736347286126,
      34014896056281309646512058126667913]) : ℤ))
      (naturalFromChunks [
      6400000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      38729481078125875109,
      76637089920329856098896184724691039,
      95799959139430198336179084055884012,
      55820193666305563558980105845381763,
      76477890508403675181138314083052333])
      (naturalFromChunks [
      32768000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      651119810786289015763,
      4114142687924407599428325716088078,
      61023984528169290192365705819202379,
      79260090486694955629447642207579405,
      43485043701296945996538579373026391])
      (naturalFromChunks [
      6400000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      9005771742771812930505,
      58946786492959638175245597174788749,
      13038617100112156254240943432178320,
      21142311146930295085709411441844239,
      67644010607726716023327914535386407])
      (naturalFromChunks [
      65536000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 4, sharing kernel reduction. -/
@[expose]
def cachedPath04 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      137437287975512062338,
      70919967300170333811485565966232643,
      10638242570981596591505205507888429,
      52601132651448521777311208605664925,
      56192875748372588280815659249114093]) : ℤ))
      (naturalFromChunks [
      4096000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      22467360245297988108,
      56112342793820765380264380655133334,
      29531591438965372171000682985755594,
      45429999022724786122338458184914204,
      45847365690044714883433796662013467]) : ℤ))
      (naturalFromChunks [
      4096000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      275747586818673826219,
      50625546074936342703565113798977182,
      1146546306727773560019166956028854,
      3932337771064777894467575156849641,
      36243655997364990168367093676435219])
      (naturalFromChunks [
      2048000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      698348227654038481169,
      70667851612610394756475484262548393,
      90457228968935196947491747574871989,
      62939162869168395373032340806845914,
      87252404329967669574965606841769861])
      (naturalFromChunks [
      4096000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 5, sharing kernel reduction. -/
@[expose]
def cachedPath05 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      1082669277612280165857,
      22213585892920254341856704042520998,
      56859783556261704480209291502237127,
      44933671459361595388973986850463799,
      46427798661081607985721723295531127]) : ℤ))
      (naturalFromChunks [
      25600000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      17736738199344183985,
      44229400551172330353320805277303073,
      90697109383486804175230843143445183,
      11805592692696122400824278116777688,
      52807939621165628837900571803012337]) : ℤ))
      (naturalFromChunks [
      1310720000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      2137037759635821945951,
      15731002209590382227717230893097918,
      41621198581896007480883971564401711,
      45389410335857388480574935897589974,
      99696444501811673621546840076749761])
      (naturalFromChunks [
      12800000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      10640683123606004173,
      82310372426003510408455238278908779,
      81388355897557796731545048927062756,
      16302258963323942165116560400676029,
      18203798106858477556707665657063091])
      (naturalFromChunks [
      52428800000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 6, sharing kernel reduction. -/
@[expose]
def cachedPath06 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      2680170847027654534774,
      61684040855844559981322023906641975,
      56610652358746122042253325013736687,
      6277299733388226031141299438197790,
      40974691037601367059759116049734507]) : ℤ))
      (naturalFromChunks [
      51200000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      93930487064265178796,
      29716699436248786974627997210335582,
      63237469195814457886919109558296907,
      84856482043037459793656525431470394,
      93931613502494613889086677778825469]) : ℤ))
      (naturalFromChunks [
      4096000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      20339129419442060876594,
      1391626348646451668662347055303391,
      15465887621692242482729366937872609,
      66857945034095006437916010249540579,
      30871376576739564690425626507123041])
      (naturalFromChunks [
      102400000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      3846022310136996615290,
      27002240885343835803255878584829161,
      14458217213200498088882103192466379,
      33396394683931457590206731343397247,
      73912213202174365346865034585117389])
      (naturalFromChunks [
      16384000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 7, sharing kernel reduction. -/
@[expose]
def cachedPath07 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      20381017934146979245,
      61693320989470503371401442326964127,
      91673893309935437692126346083375172,
      67450320294182700510700928248389603,
      58833253908103808060331507300338921]) : ℤ))
      (naturalFromChunks [
      320000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      2205767220636735668142,
      35940810189556752352642392711344277,
      26762691955107816441077933703341457,
      20749704589015203587956213954524896,
      54736979393155779517911320839349317]) : ℤ))
      (naturalFromChunks [
      65536000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      367350088712004395952,
      39766286536720862570011349737953538,
      31538324792015689931670428716135632,
      68644132135603915097918340468769638,
      55268171291805020647080139170596203])
      (naturalFromChunks [
      1600000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      8709907405773836844111,
      50502012136984439007331574618703806,
      49469165334826194083182637786951896,
      72907450548893762289861020992783930,
      87470163690321514353102027409415497])
      (naturalFromChunks [
      32768000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 8, sharing kernel reduction. -/
@[expose]
def cachedPath08 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      7812229105725993755149,
      97641031873286603147948844413615301,
      75796343540237770318921365820474347,
      19977088575061253290482682834293765,
      45995749618422983633275842386474821]) : ℤ))
      (naturalFromChunks [
      102400000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      46773151077659169260,
      97287040064071377465512343272931470,
      21573777092767783318958310731734855,
      93471337492423523767974706447344462,
      75704022560099374876133741254428909]) : ℤ))
      (naturalFromChunks [
      1024000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      26604782435194208738668,
      80872704614358068781074789513746518,
      94493941070370043337611991993687952,
      40842667694072401880457855491441986,
      85621910315436639878553104013171707])
      (naturalFromChunks [
      102400000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      151598740593416817709,
      9226378357809752850127442420102858,
      55734093541596926198555674243503923,
      73808143245022699455357008191806776,
      98485060194256457186362628699029373])
      (naturalFromChunks [
      512000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 9, sharing kernel reduction. -/
@[expose]
def cachedPath09 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      23069638736666002967,
      12877861193895208738983408374202765,
      64588438122218512545763457152858773,
      22073903643433764383209779706672121,
      94801059121046692794847678062741701]) : ℤ))
      (naturalFromChunks [
      256000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      3863909614874605471117,
      40648359854104395342155670334436315,
      67926626152545763385582714167881168,
      97456953543625620753899127559258247,
      82607008735167379153577507820221821]) : ℤ))
      (naturalFromChunks [
      65536000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      296170256433636930537,
      66630312236551833493561182688790199,
      6592420113866089103834981083121999,
      69467143296029617178237254333184173,
      33713656595485136675368018626081107])
      (naturalFromChunks [
      1024000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      333363201323075817867,
      31687272918839090125789612300645001,
      1166954169132719044158493534968013,
      62890785944223099129582144205997474,
      90230433777095280334927491780464439])
      (naturalFromChunks [
      1024000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 10, sharing kernel reduction. -/
@[expose]
def cachedPath10 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      10765216446638226850857,
      59299744066641916576448686407520110,
      84702330161375927295680856336342208,
      4516745507330992498489976621197065,
      81511408194208121910810941333273883]) : ℤ))
      (naturalFromChunks [
      102400000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      6018505024411921763,
      17030749444711649401090166160001354,
      83388115444377136493465757028048465,
      72372814606718744507039061226771621,
      85261206054916356321021061778285257]) : ℤ))
      (naturalFromChunks [
      81920000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      650840451921177077031,
      93038030793606040741970645022740278,
      42989991280547562838022103397091788,
      61237015064879275543251033445908778,
      10927714242048705550957807694300573])
      (naturalFromChunks [
      2048000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      58020991744810199843,
      68507999215275411867922016848468589,
      36207505591585407971144829603117203,
      25831506287041077221720129610627196,
      15847080038091018522379721036807589])
      (naturalFromChunks [
      163840000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 11, sharing kernel reduction. -/
@[expose]
def cachedPath11 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      388141736688336868895,
      66984257106958467182590409196082226,
      95481003145049932367296596182226025,
      25677986066847416526982958324964912,
      41008523163620647626192920678433497]) : ℤ))
      (naturalFromChunks [
      3200000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      1168758992281440224547,
      16287102208851664666399704791712721,
      47676942061864743051552440361261081,
      90874044232132797985332200650670144,
      580541931498526622366134765199423]) : ℤ))
      (naturalFromChunks [
      13107200000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      221092429879427027330,
      88608008438198821562909998043439665,
      13047336253194869013295956424692359,
      53363047135120315900082011173485363,
      47675313688007582100846275507645983])
      (naturalFromChunks [
      640000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      25020942119207618609007,
      65662086365274136324062902241613617,
      20230407829829238053233158295393339,
      19732129575996048464524852170204763,
      56414247462160268260580912159592919])
      (naturalFromChunks [
      65536000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 12, sharing kernel reduction. -/
@[expose]
def cachedPath12 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      1773731627147483191230,
      36175209239618255945472513069837148,
      86686865313617304064171377235314437,
      89468174345549440081679584819172702,
      69303600230459694542080597360087611]) : ℤ))
      (naturalFromChunks [
      12800000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      434274526001465855850,
      40140375888482141794938444560415681,
      81298170686723382039329372006731002,
      36272032346813362557734848497153891,
      23649817013654428840899432451078853]) : ℤ))
      (naturalFromChunks [
      4096000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      38110474596107811052997,
      22567448013227543795816574190045428,
      6148621739332637984916400807260212,
      3105445367900174250407320778460984,
      67721687845924257486180275393586281])
      (naturalFromChunks [
      102400000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1673113596354495819892,
      99663859850762056945110856967538721,
      15315187268085034040526245941768117,
      88868877078658470159320662446010791,
      40266793041155812902529175745836119])
      (naturalFromChunks [
      4096000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 13, sharing kernel reduction. -/
@[expose]
def cachedPath13 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      2008628765280496405999,
      88041818710889025150991536031988718,
      67802598540852776870906963033442949,
      32376771739553337244108350073120327,
      8101166361721646485967471924171109]) : ℤ))
      (naturalFromChunks [
      12800000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      2031497294957303917014,
      84974101791982474935481011792204520,
      98426372616984371284109496076401980,
      65348067744465036717049064033141828,
      55012639527231088679188109392017203]) : ℤ))
      (naturalFromChunks [
      16384000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      10186092982599889011385,
      75445809284625668857234827446401256,
      9572922591564378539877611180619063,
      59863876662292155909697277164309157,
      49029987172795481332882145234705061])
      (naturalFromChunks [
      25600000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      28452052022163414126520,
      3188857407044636447299600183732073,
      64570549278856232420072930604538885,
      83164904112139175558683749277586688,
      98727427902645257279661989958565199])
      (naturalFromChunks [
      65536000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 14, sharing kernel reduction. -/
@[expose]
def cachedPath14 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      722150173434592909301,
      58851046991353602091763548730853537,
      98680631631649365122309591599360436,
      72445330859530973155614348395162504,
      30169567161732563058636612092586367]) : ℤ))
      (naturalFromChunks [
      4096000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      1171732991930521869823,
      37343757013793546654818827806379467,
      58313561677554029029079042684963043,
      1394828477275913674129295740057125,
      21868219111420349550885807779387851]) : ℤ))
      (naturalFromChunks [
      8192000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      346175364735067842297,
      48277590864265851194901038690959438,
      40969866803779673682446409520025577,
      41104078294823259265316314539343406,
      37139012554037842050137668908985367])
      (naturalFromChunks [
      819200000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      3758096417306143734854,
      49157986947996196645973836218009980,
      81801442549508901343781373774936220,
      62988791699570044998146115095030841,
      28693784905060628582225160964862971])
      (naturalFromChunks [
      8192000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 15, sharing kernel reduction. -/
@[expose]
def cachedPath15 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      1573401899376989857,
      61390673445606358559943249262846074,
      40485303902441957060259762088802928,
      29980996385309511029707993723591671,
      20430162592414247590508160529451147]) : ℤ))
      (naturalFromChunks [
      8000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      85513475642321595311,
      1611388138227603773581264109809037,
      29910490424832874624738082855515607,
      97815095887290868761373883257814986,
      83728519998198042073066687725457571]) : ℤ))
      (naturalFromChunks [
      524288000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      178471541349866931552,
      82080798306619057628694172953525409,
      51461411668440376719160952009274494,
      64011786424290545832853943329622757,
      49291117201164234567807063159973151])
      (naturalFromChunks [
      400000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1264208077804334994646,
      45984056187109252142191193421006168,
      21654621402168520232087262712011627,
      31900409802051276593209813112534137,
      86912007640780707299131977850470871])
      (naturalFromChunks [
      2621440000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 16, sharing kernel reduction. -/
@[expose]
def cachedPath16 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      2232175522607699188225,
      91190032953322708632477580711179517,
      18198603757775366862712918851175636,
      52554716962569962340204476268256643,
      48709358495140720560234482012956223]) : ℤ))
      (naturalFromChunks [
      10240000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      47144573986484561700,
      20393882355647221312919724009336554,
      18935012311525313090963907184081000,
      8639326835990205916958039686816462,
      78321641706534454926480214352213933]) : ℤ))
      (naturalFromChunks [
      256000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      47990508228491983736890,
      82777188360891801519454862611393458,
      97118251705832496709509992986480042,
      96040507250019094751055079215951112,
      85280886769706192295013734428061719])
      (naturalFromChunks [
      102400000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      25836464706022605256,
      22509887965423031993705386895346402,
      37478877332775466019282535233622298,
      15550952670072662534870817639365081,
      8902297904708943185834023894469691])
      (naturalFromChunks [
      51200000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 17, sharing kernel reduction. -/
@[expose]
def cachedPath17 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      6148896072700788812949,
      53043421946390568404884368544093008,
      78958785753223498876364649105232574,
      71290632492409024233963674357743240,
      45501385942277855477573264461473913]) : ℤ))
      (naturalFromChunks [
      25600000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      6755149746078905205046,
      28811037024431407510219365078312336,
      76658383922927573992298460543320860,
      53378925909911150600872596743289554,
      15594343672769671009892433651174151]) : ℤ))
      (naturalFromChunks [
      32768000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      313582638106586757705,
      87372461386231909729904051768169255,
      93832339306618535561602351534722481,
      17396715823787651057097928500086174,
      80862350746552740550298161258652403])
      (naturalFromChunks [
      640000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1722931461148887366510,
      46409158181583098086856385010171943,
      65411799477445493270226484209591504,
      52504702741971018918801514136857410,
      10006424262474222625926664492887733])
      (naturalFromChunks [
      3276800000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 18, sharing kernel reduction. -/
@[expose]
def cachedPath18 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      26956076469151142512381,
      49866755369027077396387222904166349,
      64686367075487352613288857348431751,
      22591177282038582248518256987764101,
      77830896854799858276659869424597243]) : ℤ))
      (naturalFromChunks [
      102400000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      3752476427667790480364,
      70645451745216788284098881576421063,
      58888219615823033835494844744798409,
      84305029134523970870708510923637953,
      18092139045718317015403128802538637]) : ℤ))
      (naturalFromChunks [
      16384000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      52232948799621723373687,
      97740482995519195309788825469980642,
      4716579278934641305838724815833601,
      15259250362978229305147952254142814,
      23930779926923549256356963352108949])
      (naturalFromChunks [
      102400000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      4470827035596881257958,
      86961292595799761390584647742694265,
      26232252001435539485088086711004455,
      89975776386155454364118256180248451,
      89268163566843973969280851164826807])
      (naturalFromChunks [
      8192000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 19, sharing kernel reduction. -/
@[expose]
def cachedPath19 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      73495325945139818809,
      8306371050718563749998178032974320,
      33501377488505376525542559208090777,
      49474525788223448235415596534377789,
      96013070524635323176719248601235113]) : ℤ))
      (naturalFromChunks [
      256000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      16564588421182096012176,
      29273864383361591221571777624871588,
      20641942462953251634759374321949101,
      23911874168868967341875742603229148,
      16128655578108919788171346684036691]) : ℤ))
      (naturalFromChunks [
      65536000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      27082979284001047506,
      79559520492811177479762935518293604,
      63949262813513831368097858266552329,
      65635176247659198607447324192713447,
      26455732627678590531196400719831429])
      (naturalFromChunks [
      51200000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      289002363685836856899,
      17527026093291510038295223648736736,
      85271027410740226881270884576939535,
      83954866806232751564042949776919242,
      97837979159043726499299779485472231])
      (naturalFromChunks [
      512000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 20, sharing kernel reduction. -/
@[expose]
def cachedPath20 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      6383300875517254031192,
      29131494420264809031195032822421161,
      82700393794748046111940805113088212,
      41845293725036682366573040277997876,
      85112712985090380754514866912717999]) : ℤ))
      (naturalFromChunks [
      20480000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      45427533799981145858,
      17953586887851602939012078609143271,
      12949960118367039099434387728043027,
      41958000804686948437166022867217953,
      29216245456445894150979303716934211]) : ℤ))
      (naturalFromChunks [
      163840000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      13992176165349168127972,
      83856438909825257690323117211977158,
      71687832787594844182089566373415837,
      5686253870847922247895428866751799,
      47367000195086438325264253866482631])
      (naturalFromChunks [
      25600000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      47666841691201280669,
      55695454142107537182683935505704275,
      18006844203933817590497298518268947,
      68498735306032288499334897180644104,
      72115191142903246332754968347275817])
      (naturalFromChunks [
      81920000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 21, sharing kernel reduction. -/
@[expose]
def cachedPath21 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      431322785493072023787,
      56599427004958405722851738981481554,
      3384495675567098461980779425235168,
      5188460070626790897620710851323643,
      18763100099683038942106162392653023]) : ℤ))
      (naturalFromChunks [
      1280000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      3965151587818684362262,
      94751912373538557491256839435816527,
      71181151810458439208200293840752877,
      36536264412921590864906946192054462,
      53257345090778891246698910753912169]) : ℤ))
      (naturalFromChunks [
      13107200000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      7204728572088139345589,
      79024545077048721515620566775608790,
      74705170721863916571618142077828695,
      48213159886109202965179325337537991,
      97490990118691632549838940501890353])
      (naturalFromChunks [
      12800000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      9797009015704454333044,
      79531328010772785133822223168203504,
      55555474198942598713408721457461837,
      12673798127526764858314469522941493,
      61383687717026893520715691959243299])
      (naturalFromChunks [
      16384000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 22, sharing kernel reduction. -/
@[expose]
def cachedPath22 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      7432116517734618500798,
      93762291373445073759496636164725261,
      48065959727405143181300388384062330,
      90025766802837099493707177047597270,
      41875785710555023943980535691796973]) : ℤ))
      (naturalFromChunks [
      20480000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      2690664215580521882457,
      8621210847716537766938969675171070,
      42829090155427542736073778285756218,
      32035517854597147101577588497096984,
      98899547702258424270356703570598241]) : ℤ))
      (naturalFromChunks [
      8192000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      59170165059194991306530,
      62513249769526416741865203352728492,
      98237134454343858181410934094382458,
      19014127533375934479135993784516078,
      11676782152962256292537976344249187])
      (naturalFromChunks [
      102400000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      401540232308970637289,
      71957584818052195563077915556536227,
      50857577687287708582644416149596137,
      98501216961056532077278540375472866,
      62043058645309070670626166162915149])
      (naturalFromChunks [
      655360000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 23, sharing kernel reduction. -/
@[expose]
def cachedPath23 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      311524683689077264076,
      81865832439147061117839984178997685,
      50586424143718922702154526372735043,
      65002669484641632410342495227830606,
      68183280954699394374852966183255519]) : ℤ))
      (naturalFromChunks [
      800000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      1454130764090289837339,
      80087964315861009545481612666624919,
      79757576261319729592487442773874219,
      88594085886580568798190957097675234,
      48573394307380205278064762344761647]) : ℤ))
      (naturalFromChunks [
      4096000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      29571653763547763974,
      37519747249989126270084668660719189,
      47928550782524185138035854584515490,
      24783589875666482940303231198041709,
      36720058144278890294853221355302129])
      (naturalFromChunks [
      50000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      41029595577706048530349,
      68340607272369226115598963398150844,
      41502464298175621172978543202541514,
      9716158378904356395067473110130294,
      46472184805117273614742091299973859])
      (naturalFromChunks [
      65536000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 24, sharing kernel reduction. -/
@[expose]
def cachedPath24 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      68230104524419658859,
      3710018708085601961211588192614519,
      84719400461408904752799797939644498,
      73402860115551976871940859828566932,
      65156912367605957567924221548286637]) : ℤ))
      (naturalFromChunks [
      163840000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      97829798387851889725,
      59693060005088178349348158273886876,
      5983367253201647876129139448652466,
      81855465756118828867565142653836040,
      73895300861281584358526124751061481]) : ℤ))
      (naturalFromChunks [
      256000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      98900495310502982360,
      29947821290084573791962464607669732,
      87953102054601526846580069211511667,
      1365590475649153559773357988948831,
      81931142070375210687381955343034307])
      (naturalFromChunks [
      163840000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      81666103229825782382,
      44915206810025307319170317505802327,
      32432750801747532264219951780762419,
      34121066514689279195213992138260298,
      16053739472581819338905830015984959])
      (naturalFromChunks [
      128000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 25, sharing kernel reduction. -/
@[expose]
def cachedPath25 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      2273035225321697952023,
      80779446263128223074618891179067779,
      75772731684221422477462013180320621,
      28702581762506875003691180955447801,
      67549939675737803575799401258684339]) : ℤ))
      (naturalFromChunks [
      5120000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      21485268119185817861,
      7629542580321023468912116859403396,
      29257650911934346579814917546276952,
      40836213232775692138446652035476381,
      30958237619418358021179764206263731]) : ℤ))
      (naturalFromChunks [
      52428800000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      7864724439432997294651,
      65660774943433334157277551864757897,
      26549610611022141140843763350181339,
      93105276316741746818811720060394398,
      30984780313361542265556932244536979])
      (naturalFromChunks [
      12800000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      68004474492341669463,
      26122830130631861841938880657614502,
      70424812979247918609585316059100120,
      22590215519708530283359232084542963,
      49173423578136672004622928618214973])
      (naturalFromChunks [
      104857600000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 26, sharing kernel reduction. -/
@[expose]
def cachedPath26 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      386559050735951328428,
      93860253269995947760667068660819041,
      55832417161228116891869017173574073,
      50866365672816566287113469711448389,
      54678889780552157407435810450991959]) : ℤ))
      (naturalFromChunks [
      819200000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      1434937896783106078200,
      59837873105880821029753500423892350,
      46883270872549022778880941131262379,
      32073849385708394435928305921846717,
      87395432974093925440676251287975507]) : ℤ))
      (naturalFromChunks [
      3276800000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      63875358401001909129984,
      53931875469103674470904999909821618,
      20280316461203537408057328231977250,
      46775415376695493454704764317128611,
      25074892422465531369740415912627057])
      (naturalFromChunks [
      102400000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      10774353128052990596664,
      86416535155033626126722231447149571,
      60117012165770299347635001926095565,
      48528175529105605724925051284711865,
      58625931480763357258191677872631807])
      (naturalFromChunks [
      16384000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 27, sharing kernel reduction. -/
@[expose]
def cachedPath27 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      100710,
      71722422228052535036734160717951499,
      42069078062123627069531182627031188,
      60431569588115081772421647447206221]) : ℤ))
      (naturalFromChunks [
      200000,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      18525,
      51271337754643255148382898432441303,
      34014299681814911264804038180437217,
      55598380712549504288585707822915881]) : ℤ))
      (naturalFromChunks [
      40000,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      4022053,
      77416366696858139556873172408424940,
      79924851481875114027458417550002170,
      34057053097440188372375809026152099])
      (naturalFromChunks [
      6400000,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      4275306,
      20792989124941816891545250537159438,
      71482972875293744656267212392707172,
      74890077329955155725363858706138837])
      (naturalFromChunks [
      6400000,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 28, sharing kernel reduction. -/
@[expose]
def cachedPath28 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      106444,
      71744953679696011782194578058509761,
      28035999862186441429009740137354524,
      55943708561620240215135912314082437]) : ℤ))
      (naturalFromChunks [
      200000,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      15740,
      8776750732905718839524000408044492,
      99632166219777093229462388845919239,
      70796128024550735631231214963854567]) : ℤ))
      (naturalFromChunks [
      32000,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      253825,
      64058481427245968592862495904428802,
      74663502867928339362798909724833356,
      11912099252696050870015849165168127])
      (naturalFromChunks [
      400000,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      539518,
      65313367049853022234902972594033713,
      8806996846566129895374134291782278,
      17196073080542759291747212267703029])
      (naturalFromChunks [
      800000,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 29, sharing kernel reduction. -/
@[expose]
def cachedPath29 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      89777,
      55072345144042668244602106782333374,
      94731070144562590808464065036350402,
      29965644846821098710715917405854081]) : ℤ))
      (naturalFromChunks [
      160000,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      666645,
      1171114820531568089470279569241904,
      54693932395102532299204730188616454,
      52407016948570446094514425857577827]) : ℤ))
      (naturalFromChunks [
      1280000,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      818124,
      19421896421628635293000871486288819,
      76388621254444552878242434497475770,
      38060824003142928695543674529583673])
      (naturalFromChunks [
      1280000,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      217341,
      31536488008256338931217996649598166,
      30981014634211552498131485054543784,
      62955665460692692088623299896984261])
      (naturalFromChunks [
      320000,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 30, sharing kernel reduction. -/
@[expose]
def cachedPath30 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      472122,
      27345801840505864683752565458625043,
      340765445130149541613146265145124,
      25488894246904112308449638971592661]) : ℤ))
      (naturalFromChunks [
      800000,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      70386,
      51776643102131349176530360857896298,
      79131142730744996451010861490057546,
      22223031733375280889558616807561627]) : ℤ))
      (naturalFromChunks [
      128000,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      256890,
      54877857413562604335920363182883048,
      56113696613416722526159793535269617,
      80194738117956331104947460921687699])
      (naturalFromChunks [
      400000,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      545912,
      38121625321411199307989203679242465,
      8310504212414468291325709056123391,
      336853041636457322733126202333951])
      (naturalFromChunks [
      800000,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 31, sharing kernel reduction. -/
@[expose]
def cachedPath31 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      1548,
      23451984757618522483743068889538775,
      2467044525233695220466329701764808,
      13030059661837812627229581950797903]) : ℤ))
      (naturalFromChunks [
      2500,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      741188,
      10428913847327982246365640472463594,
      37223266166343662856610535550156216,
      38829505429891035371828895235774909]) : ℤ))
      (naturalFromChunks [
      1280000,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      4120068,
      88587496638281270192440342247918330,
      852068397896095040199119774396422,
      79684037861133912448924813205371683])
      (naturalFromChunks [
      6400000,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      4377541,
      82957527272248733233379179755066150,
      71402981636095666726216332865018091,
      20707916364849404817370397513298871])
      (naturalFromChunks [
      6400000,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 32, sharing kernel reduction. -/
@[expose]
def cachedPath32 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      1037557,
      20381538224777594765266198263867591,
      17355344825998510312127185975386422,
      19010784226342049402859228835237643]) : ℤ))
      (naturalFromChunks [
      1600000,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      6082,
      32650921472863019893610369745587324,
      87027570329937475358145268319359999,
      67679932552720075109023094295453559]) : ℤ))
      (naturalFromChunks [
      10000,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      206003,
      44429374831914063509622015054768728,
      55276994246074772276377295948882947,
      38179827455483014586016497717007069])
      (naturalFromChunks [
      320000,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1094385,
      45739381818062183308344784394971508,
      83458021763788356837982250938260234,
      49082253023200486240710766338626717])
      (naturalFromChunks [
      1600000,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 33, sharing kernel reduction. -/
@[expose]
def cachedPath33 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      27105,
      27155241043932392696664843446877106,
      50354511670250788480004983656385382,
      56990910931227646574861427579691257]) : ℤ))
      (naturalFromChunks [
      40000,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      815838,
      22980861482340674564574493531771712,
      94800799591790395897536460124431280,
      15716935301933724021892220250268897]) : ℤ))
      (naturalFromChunks [
      1280000,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      822049,
      75609143723400333874945137498657250,
      73729894201134539091820954320725837,
      38537948222578738727711283411367437])
      (naturalFromChunks [
      1280000,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      4367299,
      4973002571289594463913502933804126,
      765491218844505831266316844074914,
      50292332714913081064053457711124621])
      (naturalFromChunks [
      6400000,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 34, sharing kernel reduction. -/
@[expose]
def cachedPath34 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      226147,
      21390757401654622492277079674082469,
      30163024462876945293415825142433941,
      64363150663990668544077633154881581]) : ℤ))
      (naturalFromChunks [
      320000,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      426506,
      73077691637404356050880871492442174,
      72191980451911471149162489950729374,
      79179700669322613733030819794165769]) : ℤ))
      (naturalFromChunks [
      640000,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      409062,
      9710948210814317646500415179265414,
      739276934016533677155708834300459,
      38717100103909717517868281743284367])
      (naturalFromChunks [
      640000,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      10867,
      6576824400412816946560899305607678,
      948756152874816408148517313783160,
      64178612778337557259232429562576461])
      (naturalFromChunks [
      16000,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 35, sharing kernel reduction. -/
@[expose]
def cachedPath35 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      18391,
      21790314748260181728078487908628352,
      13221599473533026755052808740851754,
      42819733087419604316361358437656289]) : ℤ))
      (naturalFromChunks [
      25000,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      177997,
      53513288175419116530506659247824450,
      50634414250675474978678305401995017,
      62828540394903469587928314344297931]) : ℤ))
      (naturalFromChunks [
      256000,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      2030605,
      12467851417967748742899823374996283,
      74418666746470078202535116915796006,
      79808973208004414171127008899367409])
      (naturalFromChunks [
      3200000,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      2158074,
      61253468199412088939611742940784153,
      38263522231899227350465390975518044,
      66441686576767014574220099412652673])
      (naturalFromChunks [
      3200000,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 36, sharing kernel reduction. -/
@[expose]
def cachedPath36 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      157650260878099320243,
      77877183835544861117453291204457878,
      85408826503185095076290249776113065,
      56338317715966295383843926844190705,
      54063379152704294116189504951559771]) : ℤ))
      (naturalFromChunks [
      204800000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      2944527374203468901935,
      73418658657466729713988915032841429,
      27452335493026361108700336829728293,
      2352474002776145182751284289312870,
      74349856918070432957517775957957047]) : ℤ))
      (naturalFromChunks [
      4096000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      31995384474996649030920,
      30982370731303358225852993965188042,
      57786581883320588009296983500155874,
      78279139001959409928903376240709002,
      71736359927529675093500875116198311])
      (naturalFromChunks [
      51200000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      2753291354746011280217,
      92137331557403889246327384849983287,
      87643888223871324018867139235900343,
      39952227844095517663775256005116018,
      55803892166959366738336404579319193])
      (naturalFromChunks [
      4096000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 37, sharing kernel reduction. -/
@[expose]
def cachedPath37 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      13085741654074134269776,
      1707740814580816308858624218147761,
      10586530483574567377783177782449970,
      85464263175550897348181033552398662,
      55101101011774827779589093218772079]) : ℤ))
      (naturalFromChunks [
      16384000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      9558378885962762387558,
      92529579844214364227344025520042798,
      53025129524144499922517865350529380,
      70255581650820681934789214371770310,
      25610589354628624289781311565119499]) : ℤ))
      (naturalFromChunks [
      12800000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      15796594000328278354811,
      4806842944676444889692661186813701,
      17188049668106790986154225185769722,
      51290900371701866475946425238545154,
      19537735839780775892090405221462671])
      (naturalFromChunks [
      25600000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      21776409721634122234757,
      85765475947541595980081949119086403,
      36410766429321241702119140339133286,
      18158245202580975878649676448499776,
      69968545950001021423433392167593871])
      (naturalFromChunks [
      32768000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 38, sharing kernel reduction. -/
@[expose]
def cachedPath38 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      3388245014781300975675,
      62257780396155028107572725815834243,
      79605526765556607257159114066075160,
      53458880396600943367472701738966522,
      99811072926611660865191915110308823]) : ℤ))
      (naturalFromChunks [
      4096000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      15856849343285038121097,
      21335660177827266289372394922475410,
      32353301978731273911042184450596208,
      52565989780522737971663069774584053,
      55958672018940696425292920070853233]) : ℤ))
      (naturalFromChunks [
      20480000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      62234059691033561205202,
      72041491975324071202667201957781561,
      40488269595395087680097267140261562,
      41944073624348685550025871544939687,
      51518162853490671913188410094879277])
      (naturalFromChunks [
      102400000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      2147775196323453072477,
      12080543567950122671501329245521788,
      70551249522013375517987908675331295,
      84559345963399853657792798252786655,
      52654409187657027218125608568912411])
      (naturalFromChunks [
      3276800000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 39, sharing kernel reduction. -/
@[expose]
def cachedPath39 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      7006380179505396340401,
      26591034675492979700690500474508639,
      72925296017885390679453357256060938,
      20774394996248112906989115061316339,
      71566095562074281428499310135888971]) : ℤ))
      (naturalFromChunks [
      8192000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      5128677963200454349,
      42652589724043692268324409396339717,
      67644942894425804576402185090826651,
      37901527079252080862568026861272062,
      42301357834304252210273270595382177]) : ℤ))
      (naturalFromChunks [
      6400000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      597030955646730910,
      4518838282687858670956353430855641,
      2837082848479040788814812047680624,
      80215994492834686912530087027551208,
      24034863560506258813513243395950341])
      (naturalFromChunks [
      1000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      42262001779426669296770,
      83370691679274566788010351722341093,
      25529337445357597648696356226010463,
      32948024434572673961575707866688863,
      56067163497323040407316462812425513])
      (naturalFromChunks [
      65536000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 40, sharing kernel reduction. -/
@[expose]
def cachedPath40 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      36160306118857710882,
      5637364715452318846181583026935750,
      65994035601950159937052876687844090,
      66620789810865566670384141816717892,
      42889012909875150037302349889175209]) : ℤ))
      (naturalFromChunks [
      40960000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      42392471525259002272765,
      98497625433815176813013519398764759,
      79997446803030558650552850096755195,
      40429479525172061992291781353866063,
      92414253188762505333920506346965707]) : ℤ))
      (naturalFromChunks [
      51200000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      11978893942808972830606,
      36739675436558411121279413558673518,
      92338319843915562704176182731675689,
      69886701125460575500497427411269169,
      8797979497755839010486854871716501])
      (naturalFromChunks [
      20480000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      12960543596711541739,
      68716410404648112988552785205398062,
      92144207255726863406181658992288210,
      25803750077843375985321827072164013,
      62254430007761006508875765434759847])
      (naturalFromChunks [
      20480000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 41, sharing kernel reduction. -/
@[expose]
def cachedPath41 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      59624491974566283933102,
      82547220559936315181955057616233508,
      86429527491057069340402326136849956,
      92268404683545009733566424318178944,
      72678650790114615252734176824129619]) : ℤ))
      (naturalFromChunks [
      65536000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      10932093047356330136971,
      9696759512862818178266377510251090,
      32134671497289089611679498261973339,
      30178901499109653244739872845361679,
      88390514781426934848327838990545399]) : ℤ))
      (naturalFromChunks [
      12800000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      7314016486177454451940,
      95937799647973067723765081269277736,
      26983114173056975045466954039518194,
      13748801857053647035388932557238911,
      86147570199010292928060413920106303])
      (naturalFromChunks [
      12800000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      10148070266148323980082,
      18023060885212154755876893073643680,
      45450828997018946703879364114695361,
      74817629414783409651610861273106753,
      51717065852373876182065250581819883])
      (naturalFromChunks [
      16384000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 42, sharing kernel reduction. -/
@[expose]
def cachedPath42 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      7668918286564322679689,
      9352599576170392709293563228818052,
      30179754261523247850192644312643956,
      52362071461116693780421485311512892,
      89279188531735054053690373980524333]) : ℤ))
      (naturalFromChunks [
      8192000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      90068570023718357663162,
      65524347277540766694871527812740147,
      99333196312274416093445656564252617,
      72690538562106212467477997881839128,
      51086064377181974217262512486170671]) : ℤ))
      (naturalFromChunks [
      102400000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      28495867128803959300327,
      26163041370325280163063847273374332,
      3209929424656591702633152350833764,
      68656394173078496353596419806842287,
      45868761308054199345187540466626551])
      (naturalFromChunks [
      51200000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      9904831318221862012534,
      50905794324561024451615961636933478,
      79207383237093218573890891722618781,
      38125139494542634661757462080484819,
      55303660877500939781949538329617873])
      (naturalFromChunks [
      16384000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 43, sharing kernel reduction. -/
@[expose]
def cachedPath43 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      7879178388149477673746,
      23714673916456777669685937995870527,
      10545171267936721742260093570952531,
      83095828373908876865982289055582915,
      65730978145220111651927232365375147]) : ℤ))
      (naturalFromChunks [
      8192000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      1157685667064592245728,
      49828259997210687750039367447408573,
      88604682248001454789638479975678175,
      86060921589098163162873101250266023,
      56250931209511387448426599233937467]) : ℤ))
      (naturalFromChunks [
      1280000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      216157248190062554479,
      71785053818265652223979546824576430,
      76538378090938234336923342683059768,
      14250195768537990973036583127359109,
      18479952534475768060907467061622801])
      (naturalFromChunks [
      400000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      38556703137517870211117,
      28241724684927075716250640065144502,
      57720915238635422114559816095869955,
      96042046875150346981580176867951899,
      35505717856204925869704657360521887])
      (naturalFromChunks [
      65536000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 44, sharing kernel reduction. -/
@[expose]
def cachedPath44 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      505212415317868294538,
      50211467016962255326024614023257326,
      66981110742508224011555354486321043,
      56476770122811380947738989290375097,
      77582920687818381268977858681743971]) : ℤ))
      (naturalFromChunks [
      512000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      3803605970039735401272,
      72145347326947618237545474684673909,
      56928945374755982658264895716101313,
      31803122109492817865433432527235195,
      77794107227009722635424036662968813]) : ℤ))
      (naturalFromChunks [
      4096000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      2141954827079049538394,
      27639236917832832044482705046802756,
      77253700858583690067036036199108468,
      88790303745620361460471883435053948,
      52663687011200192143889685329791313])
      (naturalFromChunks [
      4096000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      584474609222468956590,
      58905073657357212545258259266027752,
      26942537469885083847676325235661881,
      78856820038651330485557574638873692,
      46292422660751355963068226877845179])
      (naturalFromChunks [
      1024000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 45, sharing kernel reduction. -/
@[expose]
def cachedPath45 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      2649966872698085003432,
      99273626753215562186566571228357382,
      44211785454541797674607812071472944,
      64593253396544484079453272548864777,
      6138136071829232871078471374530409]) : ℤ))
      (naturalFromChunks [
      2621440000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      24372285137753689855826,
      86409123090265534706672834197570492,
      80495670025600713919364203079150146,
      46909900536807392155913195672728113,
      23013681544175995100353056511267931]) : ℤ))
      (naturalFromChunks [
      25600000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      12908236509867806135982,
      24405113202977992091996386183512872,
      7347215579436704568971982509727907,
      51917697256365602987645567880147497,
      20723926776211771775388129903317057])
      (naturalFromChunks [
      25600000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      723408550138949514911,
      51054859033676080415227491800102356,
      1853793193088089386983222768366205,
      67933245721963854464881836676503061,
      78864150468167902422453221477050403])
      (naturalFromChunks [
      1310720000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 46, sharing kernel reduction. -/
@[expose]
def cachedPath46 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      8472000394770787861028,
      2665536894607534478167324040939957,
      90085702472351983988977353805875365,
      40372119564336809430230185470490439,
      80620696047447523449649303610982639]) : ℤ))
      (naturalFromChunks [
      8192000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      99806644543929202256362,
      91556188147150478662833102530468523,
      9753752197400458595687344685903683,
      37579992291173423103390901427802553,
      69404480549133793329741677048669969]) : ℤ))
      (naturalFromChunks [
      102400000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      49592034369823818580422,
      34667425687438318739634370691310607,
      68547011140961530710105652862218337,
      44359651950619047364576791908808164,
      79006900321058864968721496978135957])
      (naturalFromChunks [
      102400000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      272273988974513452729,
      76664278446186546275125135494686871,
      85014858795928474065043429435580073,
      72931283928705849307596020749146835,
      32772759217420412222349767430958437])
      (naturalFromChunks [
      512000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 47, sharing kernel reduction. -/
@[expose]
def cachedPath47 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      17311100997464031881445,
      1512344220772055950560395149915447,
      16116332505401731781570101989325900,
      20897977391904366721180889633953509,
      70906311868029514423129786747076429]) : ℤ))
      (naturalFromChunks [
      16384000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      39858444972835500800,
      57018352083868226106314877565159042,
      16832487704410403187344799405406145,
      37596833154004124356891301865804278,
      39076000321679708747565563543634747]) : ℤ))
      (naturalFromChunks [
      40000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      37054585605281853954,
      94915339884404304339119805910159131,
      36396236373999104738310437920257421,
      12437246976726412883316301516375859,
      88718647538119505660283673844534681])
      (naturalFromChunks [
      80000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      16725317056024294295559,
      77034318343739309400978069538019864,
      95615820602912051382268769443385630,
      90296848652607106485154043933012904,
      45892241938224594282749322505985729])
      (naturalFromChunks [
      32768000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 48, sharing kernel reduction. -/
@[expose]
def cachedPath48 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      275981217681435378862,
      86619130979711065865052112704629290,
      84634547757417395005440610964719260,
      82934756496722231909479808215220524,
      12122757196464645819591082423394779]) : ℤ))
      (naturalFromChunks [
      256000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      13022146108334202659600,
      61687366393398644740428741388576365,
      87356394020849788304998433341014883,
      73243083608818824479047713621000212,
      36880174613750086299745333662297679]) : ℤ))
      (naturalFromChunks [
      12800000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      45150361306281488147735,
      94224690673439145410284198439667332,
      67694304580166197059409903448335114,
      52859201600001340710079618836587823,
      48280367670439693521216150398367587])
      (naturalFromChunks [
      102400000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      4995556961198896662,
      76610657888273821370146691095609852,
      41621384411657579053042638689649666,
      37077681604945017607115854269328256,
      77774981353087221497454858704972097])
      (naturalFromChunks [
      10240000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 49, sharing kernel reduction. -/
@[expose]
def cachedPath49 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      71993284149943212616658,
      97099490456612209913860422673534614,
      97964111359791215592675078898571154,
      28204840341701991238585237533028204,
      4665316128572012761507436991339023]) : ℤ))
      (naturalFromChunks [
      65536000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      42488220324628514009,
      35738382166792831036049248306933591,
      95681369709997401681406271575757441,
      95481092383957032676419720956763770,
      58074866801741818163395943711773391]) : ℤ))
      (naturalFromChunks [
      40960000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      4275758936002020188,
      63375988869887781459431726228500339,
      44628594077556808294419735106435159,
      81216750618248984389030957476883755,
      5627553881252710983505717429428701])
      (naturalFromChunks [
      10240000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      15208210740232113699496,
      68493925350317657180141097639558021,
      99944416878430663157971220944245843,
      76917173107151541378507664010532663,
      76154619888679762733143406056433321])
      (naturalFromChunks [
      32768000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 50, sharing kernel reduction. -/
@[expose]
def cachedPath50 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      29307081218630724415,
      80430592264357168198119289665091910,
      12034387977291587567826251842157099,
      93110922645113395920887621734524031,
      38930225913411758723380740217608283]) : ℤ))
      (naturalFromChunks [
      26214400000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      108163180183189475643827,
      25549384594879428175351783936800175,
      56466592596719639860898979988625645,
      24417204935529484086378145612724161,
      47289449639005726591578868873234177]) : ℤ))
      (naturalFromChunks [
      102400000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      20127898947040552111019,
      16213136189845430568926329312694187,
      71304509393861978260060093665311672,
      26501755357712753992712139300445255,
      15315969047664909556137812603846479])
      (naturalFromChunks [
      51200000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      5757574789943071342,
      13393811773274506708685529580597747,
      76739018115844315809213323172749689,
      19701315615203688644934297900707542,
      17454811849992515369678321983529931])
      (naturalFromChunks [
      13107200000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 51, sharing kernel reduction. -/
@[expose]
def cachedPath51 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      1861789442860452858052,
      37525670196665161410601596030472595,
      74195387808184084220935328394729863,
      58360803492354401315992514247453685,
      44044378386369864244309468289867267]) : ℤ))
      (naturalFromChunks [
      1638400000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      6875039738607663470993,
      68055020551644687732198428785777321,
      99128782006745908568032578798351692,
      82902667640438661627154410285780134,
      78933966096920581771998575869931393]) : ℤ))
      (naturalFromChunks [
      6400000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      2353086842178169546350,
      34182377096921935559552742894014476,
      39201710421975555257206922422686458,
      97562116398243036094073361828868317,
      6534469126379371925997495371079853])
      (naturalFromChunks [
      6400000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      13544348377143453411646,
      18177972451653669979422730866805892,
      72597721025586188040230125583174036,
      52766344123903491694231185064347674,
      53216195051668262858705627367822151])
      (naturalFromChunks [
      32768000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 52, sharing kernel reduction. -/
@[expose]
def cachedPath52 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      2362567135595058373067,
      79146255403379597026328502579953079,
      68421356139909629911851834511996783,
      45719972557172012366800070712023143,
      58820123729708530443484881700403439]) : ℤ))
      (naturalFromChunks [
      2048000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      13966083178290418210331,
      96126169696089460106517877766753560,
      85248533127098065360131991933703069,
      854203439712620730209737427584982,
      59179652572347895401779369488827973]) : ℤ))
      (naturalFromChunks [
      12800000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      6988583791290071667195,
      49928742147790508645321146377384150,
      75426375740615352401675989428196315,
      42601120959721244617955537273518334,
      72740970265481089186556127197612667])
      (naturalFromChunks [
      20480000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1582610411666785026245,
      95288658565463839607726946171383040,
      22896685612447778725819104221928348,
      67913818017450811474166838137633790,
      12850677809462307682975440381537859])
      (naturalFromChunks [
      4096000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 53, sharing kernel reduction. -/
@[expose]
def cachedPath53 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      19164192308501195176730,
      49730122551557770670473019875089675,
      30691583688146243136579503846280768,
      64728109512060421590601469029854805,
      15797315631581253513621188725261721]) : ℤ))
      (naturalFromChunks [
      16384000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      1416789883055958606153,
      54065828925476856714357397251893026,
      78368486010663540401489265647580244,
      17966558365555546532205866471159716,
      1317816718938404836221035893849017]) : ℤ))
      (naturalFromChunks [
      1280000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      8035271800160913109973,
      38500510846430161546365406016310841,
      44742895495566306637806878690220600,
      6640410991488991474351745313570233,
      54767044531080527081559116378247541])
      (naturalFromChunks [
      25600000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      23490058084259180072820,
      1516488527900369035709955826877710,
      23991563544490884038658282362514016,
      89288770638214613208139798889965964,
      68691802325192982237427355700859099])
      (naturalFromChunks [
      65536000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 54, sharing kernel reduction. -/
@[expose]
def cachedPath54 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      19408227985754104559635,
      8396324328521525928134306385747216,
      87139152456209524296278577264112978,
      37474120520085124558449065157410788,
      60355706230284863020459636448069033]) : ℤ))
      (naturalFromChunks [
      16384000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      35887597459077945473,
      59035212923305063461215666296455650,
      92005749006915165436833750201274608,
      57460797406582414793243334993166877,
      89172572889006383593751743229969143]) : ℤ))
      (naturalFromChunks [
      32000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      1169949385766368642493,
      15619656802541891056022752247159386,
      36991108023943947733087845255336015,
      84726614262493445545688641342819049,
      80209377524264534094747826981637327])
      (naturalFromChunks [
      4096000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      5399159943562120680457,
      47477558985996245565212371678229073,
      98596008763272863910814866964505341,
      61043410630469080719053047038055160,
      29276213552181227154041549550355293])
      (naturalFromChunks [
      16384000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 55, sharing kernel reduction. -/
@[expose]
def cachedPath55 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      3141126728033232139300,
      64433709273365123641076652943456198,
      38237652440255962047204367230007711,
      10962127756509147014114748288147563,
      6638630291687101485472293632323533]) : ℤ))
      (naturalFromChunks [
      2621440000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      907939944361995515657,
      62104033544065297279192978383106796,
      26824475805742319319759258436661448,
      84800465760849910768572062524018572,
      99150079727612104064270838751869299]) : ℤ))
      (naturalFromChunks [
      800000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      410481792508244094258,
      37437527439361368769059261307906714,
      28558060276409424485467883250747904,
      77054668705147774032497475256810071,
      65436848316672757445121948944023519])
      (naturalFromChunks [
      1600000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      392893398411529813972,
      29422772376653529920942085353092201,
      59006719482609845780199983468598448,
      36267306121028127479704529278197436,
      56827690490780014032667461219173243])
      (naturalFromChunks [
      1310720000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 56, sharing kernel reduction. -/
@[expose]
def cachedPath56 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      247938289843843481706,
      87972967728677912801209050476587008,
      73996445291204324188419887357768491,
      10675039180128071640268490241818327,
      50236178533167617809229070901382781]) : ℤ))
      (naturalFromChunks [
      204800000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      14683458153830003704904,
      69646805199971480692106625580355812,
      6523328941128642934926690503153143,
      9272242886390845438931150544463141,
      54684817919758799937296519304779131]) : ℤ))
      (naturalFromChunks [
      12800000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      11606243571831659676745,
      63916517908471891481559286566749837,
      87629564580066460276723997717623838,
      67642068872609652266539598575592867,
      54111965568185015171691497722774567])
      (naturalFromChunks [
      51200000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      137792127168248826715,
      95529132471145098400729089727287115,
      41567730914177240086907325208714506,
      33917053708245402416328235106112739,
      17773058008440909251614960282670999])
      (naturalFromChunks [
      512000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 57, sharing kernel reduction. -/
@[expose]
def cachedPath57 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      80067006011017004461286,
      1796391837515470644568159494326366,
      30955463005646480206256370460884923,
      61330182251842024652621971430645627,
      66963203290414428546674718193511439]) : ℤ))
      (naturalFromChunks [
      65536000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      7411939527323301962829,
      99810774970572544608625822283237291,
      93343113147993040686831867199618724,
      57921030378128294595617217251247964,
      74808189927179389982575801908700929]) : ℤ))
      (naturalFromChunks [
      6400000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      5019727765136790482313,
      23217892944513224113929013455933640,
      72507099784439513525018974913485235,
      85194440258981594059741435461348076,
      83936762323367696968108607654401011])
      (naturalFromChunks [
      25600000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      7789065877333308284904,
      54737189541097368458695265351802718,
      41135777746979912138288052060510952,
      27066361141533621168199516304976736,
      2847598125027115477645371663448341])
      (naturalFromChunks [
      32768000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 58, sharing kernel reduction. -/
@[expose]
def cachedPath58 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      10088299575335840431240,
      55205804665072096782588160606672331,
      11638969101672594796819427669537107,
      98050308332084005555475167798696904,
      96865471851587102571918776114254837]) : ℤ))
      (naturalFromChunks [
      8192000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      119583273905248130666943,
      13019329116091235392628306054606371,
      59964469300072616270621376592449125,
      14311517803419467558922559890197347,
      32313454234762690790445530286233781]) : ℤ))
      (naturalFromChunks [
      102400000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      2109429760060368627470,
      80006764042218937252484565613892903,
      93412665360575265295705165935041889,
      3651628705288727530696183298924961,
      70209506322442573399541021334135201])
      (naturalFromChunks [
      12800000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      841893124854572354980,
      42397658068461024358164265043485336,
      45538646147866940676041643609537972,
      53401481845321185738987124597585745,
      81786377887782996222358894912070487])
      (naturalFromChunks [
      4096000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 59, sharing kernel reduction. -/
@[expose]
def cachedPath59 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      40628261855695108521476,
      98436164360080019039896744190127201,
      47601975957783876214227478621905782,
      25576246974829156663735797899602996,
      45420038345741960605410511808728001]) : ℤ))
      (naturalFromChunks [
      32768000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      301103621620064197898,
      8299094629563441193986484979507147,
      89737269524841028484629942536317194,
      74517547697049172540089371671692020,
      88609728189593713036286665297731631]) : ℤ))
      (naturalFromChunks [
      256000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      34018762971280009037,
      16038881456561924907038935837437297,
      99960461060024166826417223242565572,
      16254863570643640444066946522242964,
      81343029253984610677309885333180499])
      (naturalFromChunks [
      256000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      11317340890168309697721,
      45410299028241762657703443089265939,
      79771779002626572528856603660265125,
      54970491515034613284867040238729879,
      5521750114139824355078337721894631])
      (naturalFromChunks [
      65536000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 60, sharing kernel reduction. -/
@[expose]
def cachedPath60 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      204289048264916622360,
      25303690206038581779430164991556215,
      2192542270261213781441669906981730,
      66383526667398392301139367816128553,
      15726067403295889577864319623494443]) : ℤ))
      (naturalFromChunks [
      163840000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      121162818757260980189505,
      73632300228112868338850596005476251,
      35119747346774774138799209858922082,
      30292570526512098617456899222946956,
      95047460575534287969219970635556017]) : ℤ))
      (naturalFromChunks [
      102400000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      1285080943834146982381,
      94076033656129489289430988656901334,
      22865595832567104132331138343971778,
      2985720029198170062456256798785702,
      33723476089459091675404318918498647])
      (naturalFromChunks [
      12800000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      2280706495280212676,
      29625833186939974161218473680947791,
      60244908883737083223098208681189621,
      77514689582140903829783894757156308,
      75484925373905506392385720664182509])
      (naturalFromChunks [
      16384000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 61, sharing kernel reduction. -/
@[expose]
def cachedPath61 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      5130128137297982199970,
      11979015270500852222911160591749029,
      25387714147347173771511135197567510,
      99264800091974613863810433868205371,
      70937418602639320365290984537430863]) : ℤ))
      (naturalFromChunks [
      4096000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      30436213158943509395870,
      14842680304673036196000346367541529,
      1194030108900438413113319737277935,
      18710598814112320770476596937507304,
      54248570701731552372197427932900391]) : ℤ))
      (naturalFromChunks [
      25600000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      1725122804722919108622,
      65996905569999348341980100555845890,
      48926926223974220807794570992152633,
      6524284593208549896091570936524320,
      74595623604981686149735450315547597])
      (naturalFromChunks [
      25600000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      6890349842948582395353,
      39086950416118534041198169122654079,
      31423384727865696078286774376217932,
      59251993932395900187461249530151928,
      16286338519958681309858881941110863])
      (naturalFromChunks [
      65536000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 62, sharing kernel reduction. -/
@[expose]
def cachedPath62 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      643393124505926708537,
      38552685670926548460089453816778488,
      38544509865162488014208150769602241,
      85686048365271887104508360608569377,
      12303532657538062832233408151059051]) : ℤ))
      (naturalFromChunks [
      512000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      7636576749161744317076,
      85235683889594245840246913456978817,
      46167670878428799642138256405623192,
      46371516784914811403710767791822485,
      31039193548587898073356345094381007]) : ℤ))
      (naturalFromChunks [
      6400000000000000000000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (naturalFromChunks [
      86818643584218515155,
      3965904627296979473505833857292664,
      31216863896850199025975956944204168,
      64713996069642754926766697377185979,
      84282986450372156536682514815769571])
      (naturalFromChunks [
      2560000000000000000000,
      0,
      0,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      288973460328803356995,
      84320300751959621006429197034719980,
      50460615055939948234575415871664412,
      61757624002882346781705050908845772,
      32582892504375119601395101704657703])
      (naturalFromChunks [
      4096000000000000000000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for cell 63, sharing kernel reduction. -/
@[expose]
def cachedPath63 : RatInterval × RatInterval :=
  (⟨(ExactReplay.q
      (-((naturalFromChunks [
      15,
      42079517288790286680036160806903126,
      43012829623794531003067991380792405,
      28809926010512734426230880545237976,
      61731630191804635017229301491936027]) : ℤ))
      (naturalFromChunks [
      12,
      50000000000000000000000000000000000,
      0,
      0,
      0])),
    (ExactReplay.q
      (-((naturalFromChunks [
      1526206,
      54711468459557349232894324772787465,
      4598192129324489394972717423811205,
      95446486344966956824293103245753667,
      87711918370437577208529341465376517]) : ℤ))
      (naturalFromChunks [
      1250000,
      0,
      0,
      0,
      0]))⟩,
    ⟨(ExactReplay.q
      (-((naturalFromChunks [
      18823831,
      48723624281463936633164280237407656,
      26335680331785015270314432345086971]) : ℤ))
      (naturalFromChunks [
      250000000000,
      0,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      87326,
      79792061110285957775373564882726820,
      13026983046313166892255834128622,
      16157419760387029253635163962055685,
      70086123399049940050711975911460799])
      (naturalFromChunks [
      2500000,
      0,
      0,
      0,
      0]))⟩)

/-- The exact cached path-coordinate pair for the selected angle cell. -/
@[expose]
def cachedPath (i : Cell) : RatInterval × RatInterval :=
  match i.val with
  | 0 => cachedPath00
  | 1 => cachedPath01
  | 2 => cachedPath02
  | 3 => cachedPath03
  | 4 => cachedPath04
  | 5 => cachedPath05
  | 6 => cachedPath06
  | 7 => cachedPath07
  | 8 => cachedPath08
  | 9 => cachedPath09
  | 10 => cachedPath10
  | 11 => cachedPath11
  | 12 => cachedPath12
  | 13 => cachedPath13
  | 14 => cachedPath14
  | 15 => cachedPath15
  | 16 => cachedPath16
  | 17 => cachedPath17
  | 18 => cachedPath18
  | 19 => cachedPath19
  | 20 => cachedPath20
  | 21 => cachedPath21
  | 22 => cachedPath22
  | 23 => cachedPath23
  | 24 => cachedPath24
  | 25 => cachedPath25
  | 26 => cachedPath26
  | 27 => cachedPath27
  | 28 => cachedPath28
  | 29 => cachedPath29
  | 30 => cachedPath30
  | 31 => cachedPath31
  | 32 => cachedPath32
  | 33 => cachedPath33
  | 34 => cachedPath34
  | 35 => cachedPath35
  | 36 => cachedPath36
  | 37 => cachedPath37
  | 38 => cachedPath38
  | 39 => cachedPath39
  | 40 => cachedPath40
  | 41 => cachedPath41
  | 42 => cachedPath42
  | 43 => cachedPath43
  | 44 => cachedPath44
  | 45 => cachedPath45
  | 46 => cachedPath46
  | 47 => cachedPath47
  | 48 => cachedPath48
  | 49 => cachedPath49
  | 50 => cachedPath50
  | 51 => cachedPath51
  | 52 => cachedPath52
  | 53 => cachedPath53
  | 54 => cachedPath54
  | 55 => cachedPath55
  | 56 => cachedPath56
  | 57 => cachedPath57
  | 58 => cachedPath58
  | 59 => cachedPath59
  | 60 => cachedPath60
  | 61 => cachedPath61
  | 62 => cachedPath62
  | _ => cachedPath63

/-- The exact cached cosine interval for cell 0, sharing kernel reduction. -/
@[expose]
def cachedCosine00 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      4998494093481021100578828,
      24833086098425030540628864810962801])
      (naturalFromChunks [
      5000000000000000000000000,
      0])),
    (ExactReplay.q
      1
      1)⟩

/-- The exact cached cosine interval for cell 1, sharing kernel reduction. -/
@[expose]
def cachedCosine01 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      9987954562051723927147716,
      4759100694443203614704611783472007])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      999698818696204220115765,
      64966617219685006108125772962576017])
      (naturalFromChunks [
      1000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 2, sharing kernel reduction. -/
@[expose]
def cachedCosine02 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      1246613070848362770169496,
      42522820977646461084895777668595067])
      (naturalFromChunks [
      1250000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      9987954562051723927147716,
      4759100694443203614704611798805657])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 3, sharing kernel reduction. -/
@[expose]
def cachedCosine03 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      9951847266721968862448369,
      53109479921575474868729857018402753])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      4986452283393451080677985,
      70091283910585844339583110691621963])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 4, sharing kernel reduction. -/
@[expose]
def cachedCosine04 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      9924795345987099981567672,
      51661117820010820654634159478691333])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      9951847266721968862448369,
      53109479921575474868729857079663467])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 5, sharing kernel reduction. -/
@[expose]
def cachedCosine05 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      9891765099647809734516737,
      38016243063983689533336907303495943])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      4962397672993549990783836,
      25830558910005410327317079787162337])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 6, sharing kernel reduction. -/
@[expose]
def cachedCosine06 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      4926388211944706223870092,
      16589273893580064577906407370938883])
      (naturalFromChunks [
      5000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      2472941274911952433629184,
      34504060765995922383334226860263941])
      (naturalFromChunks [
      2500000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 7, sharing kernel reduction. -/
@[expose]
def cachedCosine07 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      1961570560806460898252364,
      47226847807394786746178667184423201])
      (naturalFromChunks [
      2000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      9852776423889412447740184,
      33178547787160129155812814928867333])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 8, sharing kernel reduction. -/
@[expose]
def cachedCosine08 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      9757021300385285444603957,
      66419527971644012265792042946977421])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      9807852804032304491261822,
      36134239036973933730893336165978909])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 9, sharing kernel reduction. -/
@[expose]
def cachedCosine09 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      2425078132986359981509960,
      51821525062864216490562018457956381])
      (naturalFromChunks [
      2500000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      9757021300385285444603957,
      66419527971644012265792043255088541])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 10, sharing kernel reduction. -/
@[expose]
def cachedCosine10 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      9637760657954398666864643,
      55507835153663083848826632379316763])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1212539066493179990754980,
      25910762531432108245281009276435257])
      (naturalFromChunks [
      1250000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 11, sharing kernel reduction. -/
@[expose]
def cachedCosine11 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      4784701678661044324678989,
      43490134984741424602815018437715273])
      (naturalFromChunks [
      5000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1927552131590879733372928,
      71101567030732616769765326567545863])
      (naturalFromChunks [
      2000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 12, sharing kernel reduction. -/
@[expose]
def cachedCosine12 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      1186910225741295833994920,
      9273668128531528019229051300090539])
      (naturalFromChunks [
      1250000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      9569403357322088649357978,
      86980269969482849205630037419714317])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 13, sharing kernel reduction. -/
@[expose]
def cachedCosine13 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      4707720325915103892062547,
      1299751178592794897912591172543821])
      (naturalFromChunks [
      5000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      2373820451482591667989840,
      18547336257063056038458102759472587])
      (naturalFromChunks [
      2500000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 14, sharing kernel reduction. -/
@[expose]
def cachedCosine14 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      9329927988347388877116602,
      55543302498295015520512294450889103])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      4707720325915103892062547,
      1299751178592794897912591541017099])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 15, sharing kernel reduction. -/
@[expose]
def cachedCosine15 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      184775906502257351225636,
      63787935765736448332517272836157107])
      (naturalFromChunks [
      200000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1865985597669477775423320,
      51108660499659003104102459058878619])
      (naturalFromChunks [
      2000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 16, sharing kernel reduction. -/
@[expose]
def cachedCosine16 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      914209755703530654635014,
      82939357740104469111568217623822567])
      (naturalFromChunks [
      1000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      9238795325112867561281831,
      89396788286822416625863642764563933])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 17, sharing kernel reduction. -/
@[expose]
def cachedCosine17 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      9039892931234433315862002,
      97230537048710132025050607197151713])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      4571048778517653273175074,
      14696788700522345557841088657323959])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 18, sharing kernel reduction. -/
@[expose]
def cachedCosine18 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      8932243011955153203424164,
      47493397978000625588998871843311403])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      9039892931234433315862002,
      97230537048710132025050608399650477])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 19, sharing kernel reduction. -/
@[expose]
def cachedCosine19 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      8819212643483550297127568,
      63660388349508442620674726936265953])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      8932243011955153203424164,
      47493397978000625588998873178095531])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 20, sharing kernel reduction. -/
@[expose]
def cachedCosine20 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      1740173982217422837304584,
      80896769768782165557905964868101359])
      (naturalFromChunks [
      2000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      8819212643483550297127568,
      63660388349508442620674728409384211])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 21, sharing kernel reduction. -/
@[expose]
def cachedCosine21 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      428864305000136034951134,
      99214238506852124539971686638286303])
      (naturalFromChunks [
      500000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1740173982217422837304584,
      80896769768782165557905965191570209])
      (naturalFromChunks [
      2000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 22, sharing kernel reduction. -/
@[expose]
def cachedCosine22 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      1689707130499414146519142,
      41020991419543957196277821452719797])
      (naturalFromChunks [
      2000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      4288643050001360349511349,
      92142385068521245399716867266541721])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 23, sharing kernel reduction. -/
@[expose]
def cachedCosine23 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      4157348061512726185393941,
      88808952878369280405993624243212271])
      (naturalFromChunks [
      5000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      528033478281066920787232,
      319059818607486623836819324184143])
      (naturalFromChunks [
      625000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 24, sharing kernel reduction. -/
@[expose]
def cachedCosine24 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      8175848131515836965049208,
      84130633809471042517566912499545797])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      2078674030756363092696970,
      94404476439184640202996812643334609])
      (naturalFromChunks [
      2500000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 25, sharing kernel reduction. -/
@[expose]
def cachedCosine25 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      1606415062961289819613353,
      2592628384775913885434091823855011])
      (naturalFromChunks [
      2000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      4087924065757918482524604,
      42065316904735521258783457382713731])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 26, sharing kernel reduction. -/
@[expose]
def cachedCosine26 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      63067714210128500960733,
      17642877514261251945097197174484151])
      (naturalFromChunks [
      80000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1606415062961289819613353,
      2592628384775913885434092322625003])
      (naturalFromChunks [
      2000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 27, sharing kernel reduction. -/
@[expose]
def cachedCosine27 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      7730104533627369608109066,
      9758469800971041292900807641309649])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      7883464276266062620091647,
      5359689282656493137149649715782547])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 28, sharing kernel reduction. -/
@[expose]
def cachedCosine28 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      7572088465064845475754640,
      53605784473040433715731614750260323])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      7730104533627369608109066,
      9758469800971041292900811650456043])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 29, sharing kernel reduction. -/
@[expose]
def cachedCosine29 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      7409511253549590911756168,
      97495162729728955309309087808108197])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      7572088465064845475754640,
      53605784473040433715731622390746331])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 30, sharing kernel reduction. -/
@[expose]
def cachedCosine30 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      7242470829514669209410692,
      43290553167483093004800434490403453])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1852377813387397727939042,
      24373790682432238827327276982699053])
      (naturalFromChunks [
      2500000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 31, sharing kernel reduction. -/
@[expose]
def cachedCosine31 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      7071067811865475244008443,
      62104849039284835937688471452121003])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      7242470829514669209410692,
      43290553167483093004800496842348879])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 32, sharing kernel reduction. -/
@[expose]
def cachedCosine32 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      6895405447370669246167306,
      29957484702845536844279120311458241])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      7071067811865475244008443,
      62104849039284835937688672182256779])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 33, sharing kernel reduction. -/
@[expose]
def cachedCosine33 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      6715589548470184006253768,
      50427421803228750632199790827325159])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      6895405447370669246167306,
      29957484702845536844279758975438619])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 34, sharing kernel reduction. -/
@[expose]
def cachedCosine34 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      6531728429537767640842030,
      13656305415076860023714154803176483])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      6715589548470184006253768,
      50427421803228750632201768979747313])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 35, sharing kernel reduction. -/
@[expose]
def cachedCosine35 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      396495802602278436384482,
      25826593335667230443427606866067141])
      (naturalFromChunks [
      625000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      653172842953776764084203,
      1365630541507686002372009887695613])
      (naturalFromChunks [
      1000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 36, sharing kernel reduction. -/
@[expose]
def cachedCosine36 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      3076157952903134227424567,
      81706992138829715003882209350922361])
      (naturalFromChunks [
      5000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      6343932841636454982151716,
      13225493370675687094841728373967047])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 37, sharing kernel reduction. -/
@[expose]
def cachedCosine37 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      5956993044924333434670365,
      28829969889511926338437499068151809])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      3076157952903134227424567,
      81706992138829715003882215574100041])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 38, sharing kernel reduction. -/
@[expose]
def cachedCosine38 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      5758081914178453007459724,
      53815730841776008455314090690525803])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1191398608984866686934073,
      5765993977902385267687502374095949])
      (naturalFromChunks [
      2000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 39, sharing kernel reduction. -/
@[expose]
def cachedCosine39 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      86807848909312847616067,
      31467945826162108393605543717839779])
      (naturalFromChunks [
      156250000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      5758081914178453007459724,
      53815730841776008455314103848793047])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 40, sharing kernel reduction. -/
@[expose]
def cachedCosine40 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      1069995239774194421326153,
      80927403583112053138434378794486499])
      (naturalFromChunks [
      2000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      2777851165098011123714154,
      6974266437187468595377405726590153])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 41, sharing kernel reduction. -/
@[expose]
def cachedCosine41 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      2570513720966108632968469,
      19484407886304024560208105658651777])
      (naturalFromChunks [
      5000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1337494049717743026657692,
      26159254478890066423042976958330357])
      (naturalFromChunks [
      2500000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 42, sharing kernel reduction. -/
@[expose]
def cachedCosine42 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      2464490961148920184365133,
      44379404634119843653274178452139081])
      (naturalFromChunks [
      5000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      5141027441932217265936938,
      38968815772608049120416225523435447])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 43, sharing kernel reduction. -/
@[expose]
def cachedCosine43 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      294622960516248530347742,
      26619078398603591269933279609753839])
      (naturalFromChunks [
      625000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      4928981922297840368730266,
      88758809268239687306548371451045337])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 44, sharing kernel reduction. -/
@[expose]
def cachedCosine44 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      4496113296546066000462945,
      79424227075883187048377850210090887])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1178491842064994121390969,
      6476313594414365079733122159620701])
      (naturalFromChunks [
      2500000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 45, sharing kernel reduction. -/
@[expose]
def cachedCosine45 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      4275550934302820943209668,
      56888798534304578629342451401959127])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      2248056648273033000231472,
      89712113537941593524188932711408637])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 46, sharing kernel reduction. -/
@[expose]
def cachedCosine46 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      4052413140049898709084813,
      5505052466511947754105081593303987])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      133610966696963154475302,
      14277774954197018082166952091852347])
      (naturalFromChunks [
      312500000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 47, sharing kernel reduction. -/
@[expose]
def cachedCosine47 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      765366864730179543456919,
      96806079773352268912497123888020471])
      (naturalFromChunks [
      2000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      2026206570024949354542406,
      52752526233255973877052548724564719])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 48, sharing kernel reduction. -/
@[expose]
def cachedCosine48 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      3598950365349881487751045,
      72326756420202317421129018070100053])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      153073372946035908691383,
      99361215954670453782499425424319767])
      (naturalFromChunks [
      400000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 49, sharing kernel reduction. -/
@[expose]
def cachedCosine49 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      842224633480550126723133,
      3154786892619441694917803582196619])
      (naturalFromChunks [
      2500000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1799475182674940743875522,
      86163378210101158710564517271627079])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 50, sharing kernel reduction. -/
@[expose]
def cachedCosine50 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      1568408701994457383282394,
      22997050154996688754728269328643201])
      (naturalFromChunks [
      5000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1684449266961100253446266,
      6309573785238883389835615550020069])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 51, sharing kernel reduction. -/
@[expose]
def cachedCosine51 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      2902846772544623676361923,
      75817395274691476278324142814062403])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1568408701994457383282394,
      22997050154996688754728277859560449])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 52, sharing kernel reduction. -/
@[expose]
def cachedCosine52 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      533425514949796772650573,
      3023287278808423397671229548961797])
      (naturalFromChunks [
      2000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      2902846772544623676361923,
      75817395274691476278324160158605989])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 53, sharing kernel reduction. -/
@[expose]
def cachedCosine53 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      2429801799032638899482741,
      62077471118320990783283823500268651])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      2667127574748983863252865,
      15116436394042116988356165363840189])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 54, sharing kernel reduction. -/
@[expose]
def cachedCosine54 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      2191012401568697972277375,
      47497357798848360796705583324219953])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      2429801799032638899482741,
      62077471118320990783283841385219883])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 55, sharing kernel reduction. -/
@[expose]
def cachedCosine55 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      1950903220161282678482848,
      68477022240927691617751945869062889])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1095506200784348986138687,
      73748678899424180398352800733090717])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 56, sharing kernel reduction. -/
@[expose]
def cachedCosine56 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      854809443801506131818211,
      78604131765983164529572290956241377])
      (naturalFromChunks [
      5000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      975451610080641339241424,
      34238511120463845808875982129393449])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 57, sharing kernel reduction. -/
@[expose]
def cachedCosine57 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      1467304744553617516588501,
      29646717819706215316529382832580349])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      854809443801506131818211,
      78604131765983164529572300270194091])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 58, sharing kernel reduction. -/
@[expose]
def cachedCosine58 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      153013343999020248123380,
      59268868223446902951135637234185599])
      (naturalFromChunks [
      1250000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      366826186138404379147125,
      32411679454926553829132350422189393])
      (naturalFromChunks [
      2500000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 59, sharing kernel reduction. -/
@[expose]
def cachedCosine59 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      980171403295606019941955,
      63888641845861136673167491056370909])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1224106751992161984987044,
      74150945787575223609085116947700849])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 60, sharing kernel reduction. -/
@[expose]
def cachedCosine60 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      91955704499584279411832,
      2696904290226662408209734700340633])
      (naturalFromChunks [
      1250000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      98017140329560601994195,
      56388864184586113667316751033807499])
      (naturalFromChunks [
      1000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 61, sharing kernel reduction. -/
@[expose]
def cachedCosine61 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      490676743274180142549549,
      76942682658314745363025743153535963])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      735645635996674235294656,
      21575234321813299265677897081054297])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 62, sharing kernel reduction. -/
@[expose]
def cachedCosine62 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      6135307130728072007933,
      63236482073126636652980986039783221])
      (naturalFromChunks [
      250000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      122669185818545035637387,
      44235670664578686340756440704330377])
      (naturalFromChunks [
      2500000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for cell 63, sharing kernel reduction. -/
@[expose]
def cachedCosine63 : RatInterval :=
  ⟨(ExactReplay.q
      0
      1),
    (ExactReplay.q
      (naturalFromChunks [
      122706142614561440158672,
      64729641462532733059619730714551137])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached cosine interval for the selected angle cell. -/
@[expose]
def cachedCosine (i : Cell) : RatInterval :=
  match i.val with
  | 0 => cachedCosine00
  | 1 => cachedCosine01
  | 2 => cachedCosine02
  | 3 => cachedCosine03
  | 4 => cachedCosine04
  | 5 => cachedCosine05
  | 6 => cachedCosine06
  | 7 => cachedCosine07
  | 8 => cachedCosine08
  | 9 => cachedCosine09
  | 10 => cachedCosine10
  | 11 => cachedCosine11
  | 12 => cachedCosine12
  | 13 => cachedCosine13
  | 14 => cachedCosine14
  | 15 => cachedCosine15
  | 16 => cachedCosine16
  | 17 => cachedCosine17
  | 18 => cachedCosine18
  | 19 => cachedCosine19
  | 20 => cachedCosine20
  | 21 => cachedCosine21
  | 22 => cachedCosine22
  | 23 => cachedCosine23
  | 24 => cachedCosine24
  | 25 => cachedCosine25
  | 26 => cachedCosine26
  | 27 => cachedCosine27
  | 28 => cachedCosine28
  | 29 => cachedCosine29
  | 30 => cachedCosine30
  | 31 => cachedCosine31
  | 32 => cachedCosine32
  | 33 => cachedCosine33
  | 34 => cachedCosine34
  | 35 => cachedCosine35
  | 36 => cachedCosine36
  | 37 => cachedCosine37
  | 38 => cachedCosine38
  | 39 => cachedCosine39
  | 40 => cachedCosine40
  | 41 => cachedCosine41
  | 42 => cachedCosine42
  | 43 => cachedCosine43
  | 44 => cachedCosine44
  | 45 => cachedCosine45
  | 46 => cachedCosine46
  | 47 => cachedCosine47
  | 48 => cachedCosine48
  | 49 => cachedCosine49
  | 50 => cachedCosine50
  | 51 => cachedCosine51
  | 52 => cachedCosine52
  | 53 => cachedCosine53
  | 54 => cachedCosine54
  | 55 => cachedCosine55
  | 56 => cachedCosine56
  | 57 => cachedCosine57
  | 58 => cachedCosine58
  | 59 => cachedCosine59
  | 60 => cachedCosine60
  | 61 => cachedCosine61
  | 62 => cachedCosine62
  | _ => cachedCosine63

/-- The exact cached sine interval for cell 0, sharing kernel reduction. -/
@[expose]
def cachedSine00 : RatInterval :=
  ⟨(ExactReplay.q
      0
      1),
    (ExactReplay.q
      (naturalFromChunks [
      61353071307280720079336,
      32364820731266366529809862897079257])
      (naturalFromChunks [
      2500000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 1, sharing kernel reduction. -/
@[expose]
def cachedSine01 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      122706142614561440158672,
      64729641462532733059619725716057043])
      (naturalFromChunks [
      5000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      245338371637090071274774,
      88471341329157372681512876570745263])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 2, sharing kernel reduction. -/
@[expose]
def cachedSine02 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      98135348654836028509909,
      95388536531662949072605150565873389])
      (naturalFromChunks [
      2000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      11494463062448034926479,
      337113036278332801026216993369213])
      (naturalFromChunks [
      156250000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 3, sharing kernel reduction. -/
@[expose]
def cachedSine03 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      735645635996674235294656,
      21575234321813299265677887108149729])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      980171403295606019941955,
      63888641845861136673167501008218177])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 4, sharing kernel reduction. -/
@[expose]
def cachedSine04 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      490085701647803009970977,
      81944320922930568336583750193113861])
      (naturalFromChunks [
      5000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1224106751992161984987044,
      74150945787575223609085107798280139])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 5, sharing kernel reduction. -/
@[expose]
def cachedSine05 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      612053375996080992493522,
      37075472893787611804542553511452751])
      (naturalFromChunks [
      5000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      29346094891072350331770,
      2592934356394124306330587854486909])
      (naturalFromChunks [
      200000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 6, sharing kernel reduction. -/
@[expose]
def cachedSine06 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      1467304744553617516588501,
      29646717819706215316529391796992471])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1709618887603012263636423,
      57208263531966329059144591765259179])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 7, sharing kernel reduction. -/
@[expose]
def cachedSine07 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      1709618887603012263636423,
      57208263531966329059144590687611757])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      975451610080641339241424,
      34238511120463845808875977838457847])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 8, sharing kernel reduction. -/
@[expose]
def cachedSine08 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      1950903220161282678482848,
      68477022240927691617751954450934093])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1095506200784348986138687,
      73748678899424180398352796540620627])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 9, sharing kernel reduction. -/
@[expose]
def cachedSine09 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      2191012401568697972277375,
      47497357798848360796705591709160133])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      37965653109884982804417,
      83782460486223765480988809893759081])
      (naturalFromChunks [
      156250000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 10, sharing kernel reduction. -/
@[expose]
def cachedSine10 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      48596035980652777989654,
      83241549422366419815665676633698147])
      (naturalFromChunks [
      200000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      666781893687245965813216,
      28779109098510529247089039345642411])
      (naturalFromChunks [
      2500000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 11, sharing kernel reduction. -/
@[expose]
def cachedSine11 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      266712757474898386325286,
      51511643639404211698835615572607953])
      (naturalFromChunks [
      1000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      2902846772544623676361923,
      75817395274691476278324152383465761])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 12, sharing kernel reduction. -/
@[expose]
def cachedSine12 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      2902846772544623676361923,
      75817395274691476278324150589202631])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      3136817403988914766564788,
      45994100309993377509456548152568209])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 13, sharing kernel reduction. -/
@[expose]
def cachedSine13 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      3136817403988914766564788,
      45994100309993377509456546223839091])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      3368898533922200506892532,
      12619147570477766779671223744227129])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 14, sharing kernel reduction. -/
@[expose]
def cachedSine14 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      673779706784440101378506,
      42523829514095553355934244336919897])
      (naturalFromChunks [
      2000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1799475182674940743875522,
      86163378210101158710564513700014021])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 15, sharing kernel reduction. -/
@[expose]
def cachedSine15 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      3598950365349881487751045,
      72326756420202317421129025213326169])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      3826834323650897717284599,
      84030398866761344562485628678897681])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 16, sharing kernel reduction. -/
@[expose]
def cachedSine16 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      3826834323650897717284599,
      84030398866761344562485626369198849])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      810482628009979741816962,
      61101010493302389550821018147080309])
      (naturalFromChunks [
      2000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 17, sharing kernel reduction. -/
@[expose]
def cachedSine17 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      101310328501247467727120,
      32637626311662798693852627207675797])
      (naturalFromChunks [
      250000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      213777546715141047160483,
      42844439926715228931467123022092603])
      (naturalFromChunks [
      500000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 18, sharing kernel reduction. -/
@[expose]
def cachedSine18 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      4275550934302820943209668,
      56888798534304578629342457899382171])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      2248056648273033000231472,
      89712113537941593524188929571166953])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 19, sharing kernel reduction. -/
@[expose]
def cachedSine19 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      899222659309213200092589,
      15884845415176637409675571298114851])
      (naturalFromChunks [
      2000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      36827870064531066293467,
      78327384799825448908741660020119329])
      (naturalFromChunks [
      78125000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 20, sharing kernel reduction. -/
@[expose]
def cachedSine20 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      1178491842064994121390969,
      6476313594414365079733119954817529])
      (naturalFromChunks [
      2500000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      2464490961148920184365133,
      44379404634119843653274182802574183])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 21, sharing kernel reduction. -/
@[expose]
def cachedSine21 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      2464490961148920184365133,
      44379404634119843653274181375087567])
      (naturalFromChunks [
      5000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1285256860483054316484234,
      59742203943152012280104054973647861])
      (naturalFromChunks [
      2500000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 22, sharing kernel reduction. -/
@[expose]
def cachedSine22 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      5141027441932217265936938,
      38968815772608049120416216946147557])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      213999047954838884265230,
      76185480716622410627686876096839131])
      (naturalFromChunks [
      400000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 23, sharing kernel reduction. -/
@[expose]
def cachedSine23 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      167186756214717878332211,
      53269906809861258302880371855774239])
      (naturalFromChunks [
      312500000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      5555702330196022247428308,
      13948532874374937190754806256495229])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 24, sharing kernel reduction. -/
@[expose]
def cachedSine24 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      5555702330196022247428308,
      13948532874374937190754803138430933])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      719760239272306625932465,
      56726966355222001056914262358329449])
      (naturalFromChunks [
      1250000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 25, sharing kernel reduction. -/
@[expose]
def cachedSine25 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      2879040957089226503729862,
      26907865420888004227657047836341629])
      (naturalFromChunks [
      5000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      5956993044924333434670365,
      28829969889511926338437507101435027])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 26, sharing kernel reduction. -/
@[expose]
def cachedSine26 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      5956993044924333434670365,
      28829969889511926338437503837196527])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      6152315905806268454849135,
      63413984277659430007764426590572297])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 27, sharing kernel reduction. -/
@[expose]
def cachedSine27 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      6152315905806268454849135,
      63413984277659430007764423259472507])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      6343932841636454982151716,
      13225493370675687094841724025783247])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 28, sharing kernel reduction. -/
@[expose]
def cachedSine28 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      6343932841636454982151716,
      13225493370675687094841720622123773])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      6531728429537767640842030,
      13656305415076860023714163065397987])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 29, sharing kernel reduction. -/
@[expose]
def cachedSine29 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      1632932107384441910210507,
      53414076353769215005928539887217203])
      (naturalFromChunks [
      2500000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1678897387117546001563442,
      12606855450807187658049949320398029])
      (naturalFromChunks [
      2500000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 30, sharing kernel reduction. -/
@[expose]
def cachedSine30 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      3357794774235092003126884,
      25213710901614375316099896743952173])
      (naturalFromChunks [
      5000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      3447702723685334623083653,
      14978742351422768422139563431888753])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 31, sharing kernel reduction. -/
@[expose]
def cachedSine31 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      6895405447370669246167306,
      29957484702845536844279122204435661])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      3535533905932737622004221,
      81052424519642417968844240256401493])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 32, sharing kernel reduction. -/
@[expose]
def cachedSine32 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      353553390593273762200422,
      18105242451964241796884423650304123])
      (naturalFromChunks [
      500000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1448494165902933841882138,
      48658110633496618600960090516316199])
      (naturalFromChunks [
      2000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 33, sharing kernel reduction. -/
@[expose]
def cachedSine33 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      7242470829514669209410692,
      43290553167483093004800435840085161])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1157736133367123579961,
      90140233619176520149267079552312427])
      (naturalFromChunks [
      1562500000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 34, sharing kernel reduction. -/
@[expose]
def cachedSine34 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      3704755626774795455878084,
      48747581364864477654654544494722267])
      (naturalFromChunks [
      5000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1893022116266211368938660,
      13401446118260108428932937539722931])
      (naturalFromChunks [
      2500000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 35, sharing kernel reduction. -/
@[expose]
def cachedSine35 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      3786044232532422737877320,
      26802892236520216857865807875785847])
      (naturalFromChunks [
      5000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      7730104533627369608109066,
      9758469800971041292901204478665627])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 36, sharing kernel reduction. -/
@[expose]
def cachedSine36 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      309204181345094784324362,
      64390338792038841651716032162913897])
      (naturalFromChunks [
      400000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      394173213813303131004582,
      35267984464132824656857482663629509])
      (naturalFromChunks [
      500000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 37, sharing kernel reduction. -/
@[expose]
def cachedSine37 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      3941732138133031310045823,
      52679844641328246568574821626855621])
      (naturalFromChunks [
      5000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      2008018828701612274516691,
      28240785480969892356792616287522409])
      (naturalFromChunks [
      2500000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 38, sharing kernel reduction. -/
@[expose]
def cachedSine38 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      1606415062961289819613353,
      2592628384775913885434091116462087])
      (naturalFromChunks [
      2000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      2043962032878959241262302,
      21032658452367760629391729568564657])
      (naturalFromChunks [
      2500000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 39, sharing kernel reduction. -/
@[expose]
def cachedSine39 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      817584813151583696504920,
      88413063380947104251756690899071463])
      (naturalFromChunks [
      1000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1039337015378181546348485,
      47202238219592320101498406755706549])
      (naturalFromChunks [
      1250000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 40, sharing kernel reduction. -/
@[expose]
def cachedSine40 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      4157348061512726185393941,
      88808952878369280405993622507055293])
      (naturalFromChunks [
      5000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      8448535652497070732595712,
      5104957097719785981389112614274791])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 41, sharing kernel reduction. -/
@[expose]
def cachedSine41 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      4224267826248535366297856,
      2552478548859892990694551918135241])
      (naturalFromChunks [
      5000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      8577286100002720699022699,
      84284770137042490799433737906882701])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 42, sharing kernel reduction. -/
@[expose]
def cachedSine42 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      8577286100002720699022699,
      84284770137042490799433729391926801])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      4350434955543557093261462,
      2241924421955413894764914634755387])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 43, sharing kernel reduction. -/
@[expose]
def cachedSine43 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      1740173982217422837304584,
      80896769768782165557905964205769413])
      (naturalFromChunks [
      2000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1102401580435443787140946,
      7957548543688555327584341456279597])
      (naturalFromChunks [
      1250000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 44, sharing kernel reduction. -/
@[expose]
def cachedSine44 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      8819212643483550297127568,
      63660388349508442620674723695413387])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1116530376494394150428020,
      55936674747250078198624859542428149])
      (naturalFromChunks [
      1250000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 45, sharing kernel reduction. -/
@[expose]
def cachedSine45 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      8932243011955153203424164,
      47493397978000625588998868681981741])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      9039892931234433315862002,
      97230537048710132025050611472702711])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 46, sharing kernel reduction. -/
@[expose]
def cachedSine46 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      9039892931234433315862002,
      97230537048710132025050604124099479])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      4571048778517653273175074,
      14696788700522345557841090145319409])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 47, sharing kernel reduction. -/
@[expose]
def cachedSine47 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      914209755703530654635014,
      82939357740104469111568217326223477])
      (naturalFromChunks [
      1000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      2309698831278216890320457,
      97349197071705604156465911408672419])
      (naturalFromChunks [
      2500000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 48, sharing kernel reduction. -/
@[expose]
def cachedSine48 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      1154849415639108445160228,
      98674598535852802078232954867216201])
      (naturalFromChunks [
      1250000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      9329927988347388877116602,
      55543302498295015520512298049839469])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 49, sharing kernel reduction. -/
@[expose]
def cachedSine49 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      9329927988347388877116602,
      55543302498295015520512291695442729])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      9415440651830207784125094,
      2599502357185589795825185713986177])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 50, sharing kernel reduction. -/
@[expose]
def cachedSine50 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      9415440651830207784125094,
      2599502357185589795825179713135663])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      9495281805930366671959360,
      74189345028252224153832413537541717])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 51, sharing kernel reduction. -/
@[expose]
def cachedSine51 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      9495281805930366671959360,
      74189345028252224153832407901072943])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      239235083933052216233949,
      47174506749237071230140750994456933])
      (naturalFromChunks [
      250000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 52, sharing kernel reduction. -/
@[expose]
def cachedSine52 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      1196175419665261081169747,
      35872533746185356150703754314608443])
      (naturalFromChunks [
      1250000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      4818880328977199333432321,
      77753917576831541924413317523222169])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 53, sharing kernel reduction. -/
@[expose]
def cachedSine53 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      481888032897719933343232,
      17775391757683154192441331508530087])
      (naturalFromChunks [
      500000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      2425078132986359981509960,
      51821525062864216490562019065406831])
      (naturalFromChunks [
      2500000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 54, sharing kernel reduction. -/
@[expose]
def cachedSine54 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      75783691655823749422186,
      26619422658214506765330063060794377])
      (naturalFromChunks [
      78125000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      9757021300385285444603957,
      66419527971644012265792045137989823])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 55, sharing kernel reduction. -/
@[expose]
def cachedSine55 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      4878510650192642722301978,
      83209763985822006132896020532038069])
      (naturalFromChunks [
      5000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      9807852804032304491261822,
      36134239036973933730893337873019227])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 56, sharing kernel reduction. -/
@[expose]
def cachedSine56 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      1225981600504038061407727,
      79516779879621741716361666776884461])
      (naturalFromChunks [
      1250000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      1970555284777882489548036,
      86635709557432025831162563290299331])
      (naturalFromChunks [
      2000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 57, sharing kernel reduction. -/
@[expose]
def cachedSine57 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      2463194105972353111935046,
      8294636946790032288953203304812111])
      (naturalFromChunks [
      2500000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      9891765099647809734516737,
      38016243063983689533336908770800689])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 58, sharing kernel reduction. -/
@[expose]
def cachedSine58 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      9891765099647809734516737,
      38016243063983689533336905973751019])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      4962397672993549990783836,
      25830558910005410327317080351399043])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 59, sharing kernel reduction. -/
@[expose]
def cachedSine59 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      9924795345987099981567672,
      51661117820010820654634158350217921])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      4975923633360984431224184,
      76554739960787737434364928999287079])
      (naturalFromChunks [
      5000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 60, sharing kernel reduction. -/
@[expose]
def cachedSine60 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      9951847266721968862448369,
      53109479921575474868729856099492063])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      9972904566786902161355971,
      40182567821171688679166222084406173])
      (naturalFromChunks [
      10000000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 61, sharing kernel reduction. -/
@[expose]
def cachedSine61 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      9972904566786902161355971,
      40182567821171688679166220647598289])
      (naturalFromChunks [
      10000000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      624247160128232745446732,
      25297443793402700225919038267134297])
      (naturalFromChunks [
      625000000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 62, sharing kernel reduction. -/
@[expose]
def cachedSine62 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      624247160128232745446732,
      25297443793402700225919038206758057])
      (naturalFromChunks [
      625000000000000000000000,
      0])),
    (ExactReplay.q
      (naturalFromChunks [
      312405880842563818786176,
      76552067881151564408789304058354309])
      (naturalFromChunks [
      312500000000000000000000,
      0]))⟩

/-- The exact cached sine interval for cell 63, sharing kernel reduction. -/
@[expose]
def cachedSine63 : RatInterval :=
  ⟨(ExactReplay.q
      (naturalFromChunks [
      2499247046740510550289414,
      12416543049212515270314432345086971])
      (naturalFromChunks [
      2500000000000000000000000,
      0])),
    (ExactReplay.q
      1
      1)⟩

/-- The exact cached sine interval for the selected angle cell. -/
@[expose]
def cachedSine (i : Cell) : RatInterval :=
  match i.val with
  | 0 => cachedSine00
  | 1 => cachedSine01
  | 2 => cachedSine02
  | 3 => cachedSine03
  | 4 => cachedSine04
  | 5 => cachedSine05
  | 6 => cachedSine06
  | 7 => cachedSine07
  | 8 => cachedSine08
  | 9 => cachedSine09
  | 10 => cachedSine10
  | 11 => cachedSine11
  | 12 => cachedSine12
  | 13 => cachedSine13
  | 14 => cachedSine14
  | 15 => cachedSine15
  | 16 => cachedSine16
  | 17 => cachedSine17
  | 18 => cachedSine18
  | 19 => cachedSine19
  | 20 => cachedSine20
  | 21 => cachedSine21
  | 22 => cachedSine22
  | 23 => cachedSine23
  | 24 => cachedSine24
  | 25 => cachedSine25
  | 26 => cachedSine26
  | 27 => cachedSine27
  | 28 => cachedSine28
  | 29 => cachedSine29
  | 30 => cachedSine30
  | 31 => cachedSine31
  | 32 => cachedSine32
  | 33 => cachedSine33
  | 34 => cachedSine34
  | 35 => cachedSine35
  | 36 => cachedSine36
  | 37 => cachedSine37
  | 38 => cachedSine38
  | 39 => cachedSine39
  | 40 => cachedSine40
  | 41 => cachedSine41
  | 42 => cachedSine42
  | 43 => cachedSine43
  | 44 => cachedSine44
  | 45 => cachedSine45
  | 46 => cachedSine46
  | 47 => cachedSine47
  | 48 => cachedSine48
  | 49 => cachedSine49
  | 50 => cachedSine50
  | 51 => cachedSine51
  | 52 => cachedSine52
  | 53 => cachedSine53
  | 54 => cachedSine54
  | 55 => cachedSine55
  | 56 => cachedSine56
  | 57 => cachedSine57
  | 58 => cachedSine58
  | 59 => cachedSine59
  | 60 => cachedSine60
  | 61 => cachedSine61
  | 62 => cachedSine62
  | _ => cachedSine63

theorem cachedPath_eq : ∀ i : Cell, cellPathInterval i = cachedPath i := by
  decide +kernel

theorem cachedCosine_eq : ∀ i : Cell,
    ExactReplay.cosineInterval (cellTimeInterval i) = cachedCosine i := by
  decide +kernel

theorem cachedSine_eq : ∀ i : Cell,
    ExactReplay.sineInterval (cellTimeInterval i) = cachedSine i := by
  decide +kernel

end GerverSofa.PartB

end

end

end

end

end

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartB.CellRows.Row48`.
* `KernelOnly.PartB.CellRows.Row49`.
* `KernelOnly.PartB.CellRows.Row50`.
* `KernelOnly.PartB.CellRows.Row51`.
* `KernelOnly.PartB.CellRows.Row52`.
* `KernelOnly.PartB.CellRows.Row53`.
* `KernelOnly.PartB.CellRows.Row54`.
* `KernelOnly.PartB.CellRows.Row55`.
* `KernelOnly.PartB.CellRows.Row56`.
* `KernelOnly.PartB.CellRows.Row57`.
* `KernelOnly.PartB.CellRows.Row58`.
* `KernelOnly.PartB.CellRows.Row59`.
* `KernelOnly.PartB.CellRows.Row60`.
* `KernelOnly.PartB.CellRows.Row61`.
* `KernelOnly.PartB.CellRows.Row62`.
* `KernelOnly.PartB.CellRows.Row63`.
-/

public section

noncomputable section

section

/-!
Independent exact product-cell lower bounds for row 48.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_48 :
    ∀ j : Cell,
      targetQ < (guCellInterval (48 : Cell) j).lo ∧
      targetQ < (gvCellInterval (48 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 49.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_49 :
    ∀ j : Cell,
      targetQ < (guCellInterval (49 : Cell) j).lo ∧
      targetQ < (gvCellInterval (49 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 50.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_50 :
    ∀ j : Cell,
      targetQ < (guCellInterval (50 : Cell) j).lo ∧
      targetQ < (gvCellInterval (50 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 51.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_51 :
    ∀ j : Cell,
      targetQ < (guCellInterval (51 : Cell) j).lo ∧
      targetQ < (gvCellInterval (51 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 52.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_52 :
    ∀ j : Cell,
      targetQ < (guCellInterval (52 : Cell) j).lo ∧
      targetQ < (gvCellInterval (52 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 53.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_53 :
    ∀ j : Cell,
      targetQ < (guCellInterval (53 : Cell) j).lo ∧
      targetQ < (gvCellInterval (53 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 54.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_54 :
    ∀ j : Cell,
      targetQ < (guCellInterval (54 : Cell) j).lo ∧
      targetQ < (gvCellInterval (54 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 55.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_55 :
    ∀ j : Cell,
      targetQ < (guCellInterval (55 : Cell) j).lo ∧
      targetQ < (gvCellInterval (55 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 56.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_56 :
    ∀ j : Cell,
      targetQ < (guCellInterval (56 : Cell) j).lo ∧
      targetQ < (gvCellInterval (56 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 57.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_57 :
    ∀ j : Cell,
      targetQ < (guCellInterval (57 : Cell) j).lo ∧
      targetQ < (gvCellInterval (57 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 58.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_58 :
    ∀ j : Cell,
      targetQ < (guCellInterval (58 : Cell) j).lo ∧
      targetQ < (gvCellInterval (58 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 59.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_59 :
    ∀ j : Cell,
      targetQ < (guCellInterval (59 : Cell) j).lo ∧
      targetQ < (gvCellInterval (59 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 60.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_60 :
    ∀ j : Cell,
      targetQ < (guCellInterval (60 : Cell) j).lo ∧
      targetQ < (gvCellInterval (60 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 61.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_61 :
    ∀ j : Cell,
      targetQ < (guCellInterval (61 : Cell) j).lo ∧
      targetQ < (gvCellInterval (61 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 62.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_62 :
    ∀ j : Cell,
      targetQ < (guCellInterval (62 : Cell) j).lo ∧
      targetQ < (gvCellInterval (62 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 63.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_63 :
    ∀ j : Cell,
      targetQ < (guCellInterval (63 : Cell) j).lo ∧
      targetQ < (gvCellInterval (63 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

end

end

end

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartB.CellRows.Row32`.
* `KernelOnly.PartB.CellRows.Row33`.
* `KernelOnly.PartB.CellRows.Row34`.
* `KernelOnly.PartB.CellRows.Row35`.
* `KernelOnly.PartB.CellRows.Row36`.
* `KernelOnly.PartB.CellRows.Row37`.
* `KernelOnly.PartB.CellRows.Row38`.
* `KernelOnly.PartB.CellRows.Row39`.
* `KernelOnly.PartB.CellRows.Row40`.
* `KernelOnly.PartB.CellRows.Row41`.
* `KernelOnly.PartB.CellRows.Row42`.
* `KernelOnly.PartB.CellRows.Row43`.
* `KernelOnly.PartB.CellRows.Row44`.
* `KernelOnly.PartB.CellRows.Row45`.
* `KernelOnly.PartB.CellRows.Row46`.
* `KernelOnly.PartB.CellRows.Row47`.
-/

public section

noncomputable section

section

/-!
Independent exact product-cell lower bounds for row 32.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_32 :
    ∀ j : Cell,
      targetQ < (guCellInterval (32 : Cell) j).lo ∧
      targetQ < (gvCellInterval (32 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 33.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_33 :
    ∀ j : Cell,
      targetQ < (guCellInterval (33 : Cell) j).lo ∧
      targetQ < (gvCellInterval (33 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 34.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_34 :
    ∀ j : Cell,
      targetQ < (guCellInterval (34 : Cell) j).lo ∧
      targetQ < (gvCellInterval (34 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 35.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_35 :
    ∀ j : Cell,
      targetQ < (guCellInterval (35 : Cell) j).lo ∧
      targetQ < (gvCellInterval (35 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 36.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_36 :
    ∀ j : Cell,
      targetQ < (guCellInterval (36 : Cell) j).lo ∧
      targetQ < (gvCellInterval (36 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 37.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_37 :
    ∀ j : Cell,
      targetQ < (guCellInterval (37 : Cell) j).lo ∧
      targetQ < (gvCellInterval (37 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 38.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_38 :
    ∀ j : Cell,
      targetQ < (guCellInterval (38 : Cell) j).lo ∧
      targetQ < (gvCellInterval (38 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 39.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_39 :
    ∀ j : Cell,
      targetQ < (guCellInterval (39 : Cell) j).lo ∧
      targetQ < (gvCellInterval (39 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 40.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_40 :
    ∀ j : Cell,
      targetQ < (guCellInterval (40 : Cell) j).lo ∧
      targetQ < (gvCellInterval (40 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 41.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_41 :
    ∀ j : Cell,
      targetQ < (guCellInterval (41 : Cell) j).lo ∧
      targetQ < (gvCellInterval (41 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 42.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_42 :
    ∀ j : Cell,
      targetQ < (guCellInterval (42 : Cell) j).lo ∧
      targetQ < (gvCellInterval (42 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 43.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_43 :
    ∀ j : Cell,
      targetQ < (guCellInterval (43 : Cell) j).lo ∧
      targetQ < (gvCellInterval (43 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 44.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_44 :
    ∀ j : Cell,
      targetQ < (guCellInterval (44 : Cell) j).lo ∧
      targetQ < (gvCellInterval (44 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 45.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_45 :
    ∀ j : Cell,
      targetQ < (guCellInterval (45 : Cell) j).lo ∧
      targetQ < (gvCellInterval (45 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 46.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_46 :
    ∀ j : Cell,
      targetQ < (guCellInterval (46 : Cell) j).lo ∧
      targetQ < (gvCellInterval (46 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 47.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_47 :
    ∀ j : Cell,
      targetQ < (guCellInterval (47 : Cell) j).lo ∧
      targetQ < (gvCellInterval (47 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

end

end

end

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartB.CellRows.Row16`.
* `KernelOnly.PartB.CellRows.Row17`.
* `KernelOnly.PartB.CellRows.Row18`.
* `KernelOnly.PartB.CellRows.Row19`.
* `KernelOnly.PartB.CellRows.Row20`.
* `KernelOnly.PartB.CellRows.Row21`.
* `KernelOnly.PartB.CellRows.Row22`.
* `KernelOnly.PartB.CellRows.Row23`.
* `KernelOnly.PartB.CellRows.Row24`.
* `KernelOnly.PartB.CellRows.Row25`.
* `KernelOnly.PartB.CellRows.Row26`.
* `KernelOnly.PartB.CellRows.Row27`.
* `KernelOnly.PartB.CellRows.Row28`.
* `KernelOnly.PartB.CellRows.Row29`.
* `KernelOnly.PartB.CellRows.Row30`.
* `KernelOnly.PartB.CellRows.Row31`.
-/

public section

noncomputable section

section

/-!
Independent exact product-cell lower bounds for row 16.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_16 :
    ∀ j : Cell,
      targetQ < (guCellInterval (16 : Cell) j).lo ∧
      targetQ < (gvCellInterval (16 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 17.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_17 :
    ∀ j : Cell,
      targetQ < (guCellInterval (17 : Cell) j).lo ∧
      targetQ < (gvCellInterval (17 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 18.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_18 :
    ∀ j : Cell,
      targetQ < (guCellInterval (18 : Cell) j).lo ∧
      targetQ < (gvCellInterval (18 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 19.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_19 :
    ∀ j : Cell,
      targetQ < (guCellInterval (19 : Cell) j).lo ∧
      targetQ < (gvCellInterval (19 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 20.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_20 :
    ∀ j : Cell,
      targetQ < (guCellInterval (20 : Cell) j).lo ∧
      targetQ < (gvCellInterval (20 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 21.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_21 :
    ∀ j : Cell,
      targetQ < (guCellInterval (21 : Cell) j).lo ∧
      targetQ < (gvCellInterval (21 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 22.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_22 :
    ∀ j : Cell,
      targetQ < (guCellInterval (22 : Cell) j).lo ∧
      targetQ < (gvCellInterval (22 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 23.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_23 :
    ∀ j : Cell,
      targetQ < (guCellInterval (23 : Cell) j).lo ∧
      targetQ < (gvCellInterval (23 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 24.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_24 :
    ∀ j : Cell,
      targetQ < (guCellInterval (24 : Cell) j).lo ∧
      targetQ < (gvCellInterval (24 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 25.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_25 :
    ∀ j : Cell,
      targetQ < (guCellInterval (25 : Cell) j).lo ∧
      targetQ < (gvCellInterval (25 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 26.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_26 :
    ∀ j : Cell,
      targetQ < (guCellInterval (26 : Cell) j).lo ∧
      targetQ < (gvCellInterval (26 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 27.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_27 :
    ∀ j : Cell,
      targetQ < (guCellInterval (27 : Cell) j).lo ∧
      targetQ < (gvCellInterval (27 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 28.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_28 :
    ∀ j : Cell,
      targetQ < (guCellInterval (28 : Cell) j).lo ∧
      targetQ < (gvCellInterval (28 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 29.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_29 :
    ∀ j : Cell,
      targetQ < (guCellInterval (29 : Cell) j).lo ∧
      targetQ < (gvCellInterval (29 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 30.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_30 :
    ∀ j : Cell,
      targetQ < (guCellInterval (30 : Cell) j).lo ∧
      targetQ < (gvCellInterval (30 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 31.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_31 :
    ∀ j : Cell,
      targetQ < (guCellInterval (31 : Cell) j).lo ∧
      targetQ < (gvCellInterval (31 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

end

end

end

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartB.CellRows.Row00`.
* `KernelOnly.PartB.CellRows.Row01`.
* `KernelOnly.PartB.CellRows.Row02`.
* `KernelOnly.PartB.CellRows.Row03`.
* `KernelOnly.PartB.CellRows.Row04`.
* `KernelOnly.PartB.CellRows.Row05`.
* `KernelOnly.PartB.CellRows.Row06`.
* `KernelOnly.PartB.CellRows.Row07`.
* `KernelOnly.PartB.CellRows.Row08`.
* `KernelOnly.PartB.CellRows.Row09`.
* `KernelOnly.PartB.CellRows.Row10`.
* `KernelOnly.PartB.CellRows.Row11`.
* `KernelOnly.PartB.CellRows.Row12`.
* `KernelOnly.PartB.CellRows.Row13`.
* `KernelOnly.PartB.CellRows.Row14`.
* `KernelOnly.PartB.CellRows.Row15`.
-/

public section

noncomputable section

section

/-!
Independent exact product-cell lower bounds for row 00.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_00 :
    ∀ j : Cell,
      targetQ < (guCellInterval (0 : Cell) j).lo ∧
      targetQ < (gvCellInterval (0 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 01.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_01 :
    ∀ j : Cell,
      targetQ < (guCellInterval (1 : Cell) j).lo ∧
      targetQ < (gvCellInterval (1 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 02.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_02 :
    ∀ j : Cell,
      targetQ < (guCellInterval (2 : Cell) j).lo ∧
      targetQ < (gvCellInterval (2 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 03.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_03 :
    ∀ j : Cell,
      targetQ < (guCellInterval (3 : Cell) j).lo ∧
      targetQ < (gvCellInterval (3 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 04.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_04 :
    ∀ j : Cell,
      targetQ < (guCellInterval (4 : Cell) j).lo ∧
      targetQ < (gvCellInterval (4 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 05.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_05 :
    ∀ j : Cell,
      targetQ < (guCellInterval (5 : Cell) j).lo ∧
      targetQ < (gvCellInterval (5 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 06.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_06 :
    ∀ j : Cell,
      targetQ < (guCellInterval (6 : Cell) j).lo ∧
      targetQ < (gvCellInterval (6 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 07.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_07 :
    ∀ j : Cell,
      targetQ < (guCellInterval (7 : Cell) j).lo ∧
      targetQ < (gvCellInterval (7 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 08.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_08 :
    ∀ j : Cell,
      targetQ < (guCellInterval (8 : Cell) j).lo ∧
      targetQ < (gvCellInterval (8 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 09.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_09 :
    ∀ j : Cell,
      targetQ < (guCellInterval (9 : Cell) j).lo ∧
      targetQ < (gvCellInterval (9 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 10.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_10 :
    ∀ j : Cell,
      targetQ < (guCellInterval (10 : Cell) j).lo ∧
      targetQ < (gvCellInterval (10 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 11.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_11 :
    ∀ j : Cell,
      targetQ < (guCellInterval (11 : Cell) j).lo ∧
      targetQ < (gvCellInterval (11 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 12.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_12 :
    ∀ j : Cell,
      targetQ < (guCellInterval (12 : Cell) j).lo ∧
      targetQ < (gvCellInterval (12 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 13.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_13 :
    ∀ j : Cell,
      targetQ < (guCellInterval (13 : Cell) j).lo ∧
      targetQ < (gvCellInterval (13 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 14.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_14 :
    ∀ j : Cell,
      targetQ < (guCellInterval (14 : Cell) j).lo ∧
      targetQ < (gvCellInterval (14 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

section

/-!
Independent exact product-cell lower bounds for row 15.
Build all 64 row modules sequentially before the final Part B assembly.
-/

public section

namespace GerverSofa.PartB
theorem cell_row_15 :
    ∀ j : Cell,
      targetQ < (guCellInterval (15 : Cell) j).lo ∧
      targetQ < (gvCellInterval (15 : Cell) j).lo := by
  simp only [guCellInterval, gvCellInterval, cachedPath_eq, cachedCosine_eq, cachedSine_eq]
  decide +kernel

end GerverSofa.PartB

end

end

end

end

end

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartB.AllRows`.
-/

public section

noncomputable section

section

/-! Assembly of the 64 independently kernel-checked product-cell rows. -/

public section

namespace GerverSofa.PartB

theorem all_cell_lower (i j : Cell) :
    targetQ < (guCellInterval i j).lo ∧
    targetQ < (gvCellInterval i j).lo := by
  fin_cases i
  · exact cell_row_00 j
  · exact cell_row_01 j
  · exact cell_row_02 j
  · exact cell_row_03 j
  · exact cell_row_04 j
  · exact cell_row_05 j
  · exact cell_row_06 j
  · exact cell_row_07 j
  · exact cell_row_08 j
  · exact cell_row_09 j
  · exact cell_row_10 j
  · exact cell_row_11 j
  · exact cell_row_12 j
  · exact cell_row_13 j
  · exact cell_row_14 j
  · exact cell_row_15 j
  · exact cell_row_16 j
  · exact cell_row_17 j
  · exact cell_row_18 j
  · exact cell_row_19 j
  · exact cell_row_20 j
  · exact cell_row_21 j
  · exact cell_row_22 j
  · exact cell_row_23 j
  · exact cell_row_24 j
  · exact cell_row_25 j
  · exact cell_row_26 j
  · exact cell_row_27 j
  · exact cell_row_28 j
  · exact cell_row_29 j
  · exact cell_row_30 j
  · exact cell_row_31 j
  · exact cell_row_32 j
  · exact cell_row_33 j
  · exact cell_row_34 j
  · exact cell_row_35 j
  · exact cell_row_36 j
  · exact cell_row_37 j
  · exact cell_row_38 j
  · exact cell_row_39 j
  · exact cell_row_40 j
  · exact cell_row_41 j
  · exact cell_row_42 j
  · exact cell_row_43 j
  · exact cell_row_44 j
  · exact cell_row_45 j
  · exact cell_row_46 j
  · exact cell_row_47 j
  · exact cell_row_48 j
  · exact cell_row_49 j
  · exact cell_row_50 j
  · exact cell_row_51 j
  · exact cell_row_52 j
  · exact cell_row_53 j
  · exact cell_row_54 j
  · exact cell_row_55 j
  · exact cell_row_56 j
  · exact cell_row_57 j
  · exact cell_row_58 j
  · exact cell_row_59 j
  · exact cell_row_60 j
  · exact cell_row_61 j
  · exact cell_row_62 j
  · exact cell_row_63 j

end GerverSofa.PartB

end

end

end

end

end
