/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.Development.IntervalArithmetic.Foundations.Development002
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle002
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.KernelOnly.Foundation.Batch002`.
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

* `KernelOnly.LeanCertGerverData`.
* `KernelOnly.LeanCertNamedConstAD`.
* `KernelOnly.LeanCertGerverExpr`.
* `KernelOnly.LeanCertGerverCorrespondence`.
* `KernelOnly.LeanCertNoDetKrawczyk`.
* `KernelOnly.LeanCertGerverNumericsCore`.
-/

public section

noncomputable section

section

/-!
# Part A final adapter data

The original Gerver boxes are affinely normalized to `[-1,1]^n`.
If `x = m + D u`, then the preconditioner is transformed from `C` to
`D⁻¹ C`.  Consequently

`I - (D⁻¹ C) (J_F(x) D) = D⁻¹ (I - C J_F(x)) D`,

so the old weighted sup-norm contraction becomes the ordinary infinity norm
used by LeanCert.

The preconditioner literals below are exact public copies of the frozen
rational data already used by `ExactReplay`.  This avoids exposing private
helpers during simplification.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine

/-- Construct an exact rational from an integer numerator and natural denominator. -/
@[expose]
def q (n : Int) (d : Nat) : ℚ := (n : ℚ) / (d : ℚ)

/-- The rational preconditioner table for the four reduced equations. -/
@[expose]
def reducedCData : List (List ℚ) := [
  [q (-6807128249614081174405751646233895883477) 10000000000000000000000000000000000000000, q
    (-1668645298254898823756872685901589912999) 5000000000000000000000000000000000000000, q
    142655469136580991746408771201083165281 250000000000000000000000000000000000000, q
    6979196385375907434754729126542237618887 10000000000000000000000000000000000000000],
  [q (-1166509731502349263126377264338437200033) 2500000000000000000000000000000000000000, q
    12885386748281427252440540606364884831 80000000000000000000000000000000000000, q
    33867580317340694704135157308931896467 25000000000000000000000000000000000000, q
    (-669198169890925059603288141447454387733) 500000000000000000000000000000000000000],
  [q (-2734456716994644402025329684152137828373) 10000000000000000000000000000000000000000, q
    (-8773012441591382751224116906117915601) 62500000000000000000000000000000000000, q
    (-31169129168086947221083235454859786381) 156250000000000000000000000000000000000, q
    3097544571982855798592484554650267326733 10000000000000000000000000000000000000000],
  [q 5937522534788503855395693041282403727707 10000000000000000000000000000000000000000, q
    (-12894234217809317884645394772127946998229) 5000000000000000000000000000000000000000, q
    (-8661560217304957931983485334759974222533) 5000000000000000000000000000000000000000, q
    51750746732148285574274925461942534764817 10000000000000000000000000000000000000000]
]

/-- The rational preconditioner table for the twenty-two full equations. -/
@[expose]
def fullCData : List (List ℚ) := [
  [q 97524664435861749 500000000000000000000000000000000000, q 0 1, q 0 1, q 0 1, q
    101771747759019027 100000000000000000, q 1 1, q 0 1, q 63813611575753437 50000000000000000, q
    (-388441807573624079) 5000000000000000000, q 19675950003915553 31250000000000000, q
    (-298520460968330237) 500000000000000000, q (-548415754484802953) 1000000000000000000, q
    (-388441807573624079) 5000000000000000000, q 19675950003915553 31250000000000000, q
    20287597594763393 100000000000000000, q (-10119107089800079) 10000000000000000, q 0 1, q 0 1,
    q 0 1, q 0 1, q 388441807573624079 5000000000000000000, q (-19675950003915553)
    31250000000000000],
  [q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 1 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0
    1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1],
  [q (-803432388936903217) 10000000000000000000000000000000000000, q 0 1, q 0 1, q 0 1, q
    100605379900828451 50000000000000000, q 1 1, q 0 1, q 31765043860672787 12500000000000000, q
    (-4704777879791199) 4000000000000000, q 121750850637699193 100000000000000000, q
    (-122756605381830597) 100000000000000000, q (-30600542365273823) 312500000000000000, q
    (-88097234973899999) 500000000000000000, q 121750850637699193 100000000000000000, q
    396110376767452643 1000000000000000000, q (-40111351612012509) 20000000000000000, q 0 1, q 0
    1, q 0 1, q 0 1, q 88097234973899999 500000000000000000, q (-121750850637699193)
    100000000000000000],
  [q 348543935143050227 50000000000000000000000000000000000, q 0 1, q 0 1, q 0 1, q
    48663249173571721 200000000000000000, q 0 1, q 1 1, q (-229748851313700347)
    1000000000000000000, q 38538669009926041 200000000000000000, q (-148514169684624997)
    250000000000000000, q (-77095605529021527) 200000000000000000, q 899174721266506223
    100000000000000000000, q 38538669009926041 200000000000000000, q 101485830315375003
    250000000000000000, q 475834949279834579 5000000000000000000, q (-48935313448682273)
    250000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q (-38538669009926041) 200000000000000000, q
    (-101485830315375003) 250000000000000000],
  [q (-27668786810187381) 62500000000000000000000000000000000, q 0 1, q 0 1, q 0 1, q
    156689147323938593 100000000000000000, q 1 1, q 0 1, q 6806785234747033 4000000000000000, q
    (-770251148686299847) 1000000000000000000, q 839507200167063927 1000000000000000000, q
    (-32364013024529501) 40000000000000000, q (-325328497901119923) 5000000000000000000, q
    (-770251148686299847) 1000000000000000000, q 839507200167063927 1000000000000000000, q
    107433644407840839 1000000000000000000, q (-203691379660578653) 250000000000000000, q 0 1, q 0
    1, q 0 1, q 0 1, q (-229748851313700181) 1000000000000000000, q (-839507200167063927)
    1000000000000000000],
  [q 667707347369355603 100000000000000000000000000000000000, q 0 1, q 0 1, q 0 1, q
    39302260617100937 200000000000000000, q 0 1, q 1 1, q 810045947451984161 10000000000000000000,
    q 770773380198521041 1000000000000000000, q (-376226714953999619) 1000000000000000000, q
    (-67547253722371331) 125000000000000000, q (-317030024240986261) 100000000000000000000, q
    770773380198521041 1000000000000000000, q (-376226714953999619) 1000000000000000000, q
    (-50799288029152201) 50000000000000000, q (-293762044611903417) 1000000000000000000, q 0 1, q
    0 1, q 0 1, q 0 1, q (-770773380198521041) 1000000000000000000, q (-623773285046000381)
    1000000000000000000],
  [q (-27668786810187381) 62500000000000000000000000000000000, q 0 1, q 611138637517184627
    10000000000000000000, q 48547105024120657 62500000000000000, q (-142441420640562477)
    500000000000000000, q 1 1, q 0 1, q 107773638564961749 125000000000000000, q
    (-91076956856199917) 250000000000000000, q 461505893957135871 1000000000000000000, q
    (-195317298704084513) 500000000000000000, q (-32209663591571687) 1000000000000000000, q
    (-91076956856199917) 250000000000000000, q 461505893957135871 1000000000000000000, q
    (-45310771987942769) 250000000000000000, q 376036543315996397 1000000000000000000, q (-1) 1, q
    0 1, q 0 1, q 0 1, q (-635692172575200387) 1000000000000000000, q (-461505893957135871)
    1000000000000000000],
  [q 667707347369355603 100000000000000000000000000000000000, q 0 1, q (-133696152744215091)
    100000000000000000, q (-31490225467869859) 50000000000000000, q 12045884354915673
    125000000000000000, q 0 1, q 1 1, q (-229748851313700347) 1000000000000000000, q
    12043334065601893 62500000000000000, q (-594056678738499877) 1000000000000000000, q
    (-385478027645107413) 1000000000000000000, q 449587360633251377 50000000000000000000, q
    12043334065601893 62500000000000000, q (-594056678738499877) 1000000000000000000, q
    951669898559669991 10000000000000000000, q (-195741253794729203) 1000000000000000000, q 0 1, q
    (-1) 1, q 0 1, q 0 1, q (-12043334065601893) 62500000000000000, q (-405943321261500123)
    1000000000000000000],
  [q 498465919198540053 500000000000000000, q (-391372890930701059) 5000000000000000000, q
    (-8938515563507099) 6250000000000000, q (-55619746202997561) 250000000000000000, q
    354753639572627011 500000000000000000, q 1 1, q 0 1, q 106356019292922399 50000000000000000, q
    (-18512557434314989) 40000000000000000, q 52469200010441497 50000000000000000, q
    (-102115972928981447) 100000000000000000, q 26142772207772183 62500000000000000, q
    (-18512557434314989) 40000000000000000, q 52469200010441497 50000000000000000, q
    29978282170118999 2500000000000000000, q (-308810164152310551) 500000000000000000, q (-1) 1, q
    0 1, q (-1) 1, q 0 1, q (-53718606414212533) 100000000000000000, q (-52469200010441497)
    50000000000000000],
  [q (-782745781861401979) 10000000000000000000, q (-498465919198540053) 500000000000000000, q
    (-277739416158080399) 1000000000000000000, q (-295318582899254667) 500000000000000000, q
    (-18368646378566663) 125000000000000000, q 0 1, q 1 1, q (-133419044772954399)
    250000000000000000000000000000000, q 14163773178071801 250000000000000000000000000000000, q
    (-1) 1, q 79939871278032317 250000000000000000000000000000000, q (-2418968094552299)
    125000000000000000000000000000000, q 14163773178071801 250000000000000000000000000000000, q
    (-1) 1, q 470629071136429359 5000000000000000000000000000000000, q (-223711639524848453)
    5000000000000000000000000000000000, q 0 1, q (-1) 1, q 0 1, q (-1) 1, q (-14163773178071801)
    250000000000000000000000000000000, q (-21329108080229053) 625000000000000000000000000000000],
  [q (-97524664435861749) 500000000000000000000000000000000000, q 0 1, q 0 1, q 0 1, q
    (-101771747759019027) 100000000000000000, q 0 1, q 0 1, q (-63813611575753437)
    50000000000000000, q 388441807573624079 5000000000000000000, q (-19675950003915553)
    31250000000000000, q 298520460968330237 500000000000000000, q 548415754484802953
    1000000000000000000, q 388441807573624079 5000000000000000000, q (-19675950003915553)
    31250000000000000, q (-20287597594763393) 100000000000000000, q 10119107089800079
    10000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q (-388441807573624079) 5000000000000000000, q
    19675950003915553 31250000000000000],
  [q (-349465940599428639) 50000000000000000000000000000000000, q 0 1, q 0 1, q 0 1, q
    (-25253489731359111) 2500000000000000000000000000000000, q 0 1, q 0 1, q 50000000000000011
    50000000000000000, q (-353674953581839119) 5000000000000000000000000000000000, q
    94007553259298153 2000000000000000000000000000000000, q (-5928343202681263)
    25000000000000000000000000000000, q (-173331002701677877) 10000000000000000000000000000000000,
    q (-353674953581839119) 5000000000000000000000000000000000, q 94007553259298153
    2000000000000000000000000000000000, q (-288351357559389053)
    50000000000000000000000000000000000, q (-899167441101047079)
    10000000000000000000000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q 353674953581839119
    5000000000000000000000000000000000, q (-94007553259298153) 2000000000000000000000000000000000],
  [q 199958107491582403 10000000000000000000000000000000000000000000000000000, q 0 1, q 0 1, q 0
    1, q 122021605728424423 500000000000000000, q 0 1, q 0 1, q 770104303222080677
    1000000000000000000, q 193360860585517491 1000000000000000000, q 407267153261943571
    1000000000000000000, q (-383870749384345733) 1000000000000000000, q (-150698973735099509)
    5000000000000000000, q 193360860585517491 1000000000000000000, q 407267153261943571
    1000000000000000000, q 59669749873825801 625000000000000000, q (-98153004518806597)
    500000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q (-193360860585517491) 1000000000000000000, q
    (-407267153261943571) 1000000000000000000],
  [q (-466502263483670063) 1000000000000000000000000000000000000, q 0 1, q 0 1, q 0 1, q
    (-50741366468655913) 25000000000000000, q 0 1, q 0 1, q (-50425164328510137)
    20000000000000000, q 80468307190360827 500000000000000000, q (-124842964508786847)
    100000000000000000, q 6283806471937059 5000000000000000, q 493376058472616841
    5000000000000000000, q 80468307190360827 500000000000000000, q (-124842964508786847)
    100000000000000000, q (-403274191369431989) 1000000000000000000, q 10096930279303431
    5000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q (-80468307190360827) 500000000000000000, q
    124842964508786847 100000000000000000],
  [q 0 1, q 0 1, q 0 1, q 0 1, q (-74404321145684893) 50000000000000000, q 0 1, q 0 1, q
    (-30804172128883227) 20000000000000000, q (-386721721171035093) 1000000000000000000, q
    (-814534306523887031) 1000000000000000000, q 153548299753738271 200000000000000000, q
    150698973735099509 2500000000000000000, q (-386721721171035093) 1000000000000000000, q
    (-814534306523887031) 1000000000000000000, q 585810480789687893 1000000000000000000, q
    20448330548652467 20000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q 386721721171035093
    1000000000000000000, q 814534306523887031 1000000000000000000],
  [q 0 1, q 0 1, q 0 1, q 0 1, q (-488086422913697859) 1000000000000000000, q 0 1, q 0 1, q
    (-30804172128883227) 20000000000000000, q (-386721721171035093) 1000000000000000000, q
    (-814534306523887031) 1000000000000000000, q 153548299753738271 200000000000000000, q
    150698973735099509 2500000000000000000, q (-386721721171035093) 1000000000000000000, q
    (-814534306523887031) 1000000000000000000, q 585810480789687893 1000000000000000000, q
    20448330548652467 20000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q 386721721171035093
    1000000000000000000, q 814534306523887031 1000000000000000000],
  [q 0 1, q 0 1, q 1 1, q 0 1, q (-244043211456848957) 1000000000000000000, q 0 1, q 0 1, q
    (-770104303222080677) 1000000000000000000, q (-193360860585517547) 1000000000000000000, q
    (-407267153261943571) 1000000000000000000, q 191935374692172811 500000000000000000, q
    301397947470199087 10000000000000000000, q (-193360860585517547) 1000000000000000000, q
    (-407267153261943571) 1000000000000000000, q (-477357998990606547) 5000000000000000000, q
    98153004518806597 500000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q 193360860585517547
    1000000000000000000, q 407267153261943571 1000000000000000000],
  [q 0 1, q 0 1, q 0 1, q 1 1, q (-32926249572211761) 20000000000000000, q 0 1, q 0 1, q
    (-8197382535470743) 6250000000000000, q 29041696495897041 62500000000000000, q
    (-304347948359896703) 500000000000000000, q 326889265645238569 500000000000000000, q
    513317328155524291 10000000000000000000, q 29041696495897041 62500000000000000, q
    (-304347948359896703) 500000000000000000, q (-63326938273327693) 250000000000000000, q
    42775732448415943 25000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q (-29041696495897041)
    62500000000000000, q 304347948359896703 500000000000000000],
  [q 1 1, q 0 1, q 0 1, q 0 1, q (-101771747759019027) 100000000000000000, q 0 1, q 0 1, q
    (-31906805787876713) 25000000000000000, q 388441807573624287 5000000000000000000, q
    (-314815200062648959) 500000000000000000, q 597040921936660363 1000000000000000000, q
    548415754484802953 1000000000000000000, q 388441807573624287 5000000000000000000, q
    (-314815200062648959) 500000000000000000, q (-12679748496727131) 62500000000000000, q
    10119107089800079 10000000000000000, q 0 1, q 0 1, q 0 1, q 0 1, q (-388441807573624287)
    5000000000000000000, q 314815200062648959 500000000000000000],
  [q 0 1, q 1 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q (-1) 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q
    0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1, q 0 1],
  [q (-498591875083207211) 50000000000000000000000000000000000, q 0 1, q 0 1, q 0 1, q
    (-29185445604164767) 100000000000000000, q 0 1, q 0 1, q 79792970670302621 200000000000000000,
    q (-280736398130924159) 1000000000000000000, q (-546891343398928753) 1000000000000000000, q
    (-19887038235377269) 100000000000000000, q (-31228805607184943) 2000000000000000000, q
    (-280736398130924159) 1000000000000000000, q (-546891343398928753) 1000000000000000000, q
    (-62553783297256041) 500000000000000000, q 55986183994322411 250000000000000000, q 0 1, q 0 1,
    q 0 1, q 0 1, q 280736398130924159 1000000000000000000, q 546891343398928753
    1000000000000000000],
  [q 354149563585840613 100000000000000000000000000000000000, q 0 1, q 0 1, q 0 1, q
    142456721371719919 50000000000000000, q 0 1, q 0 1, q 173231204346099177 50000000000000000, q
    (-515769368712372689) 100000000000000000, q 59375225347885019 50000000000000000, q
    (-5396865719265527) 3125000000000000, q (-135595994488679511) 1000000000000000000, q
    (-515769368712372689) 100000000000000000, q 59375225347885019 50000000000000000, q
    55842855499643207 25000000000000000, q (-656462321731497211) 1000000000000000000, q 0 1, q 0
    1, q 0 1, q 0 1, q 515769368712372689 100000000000000000, q (-59375225347885019)
    50000000000000000]
]

/-- Interpret rational row lists as a square matrix, using zero for missing entries. -/
@[expose]
def listMatrix {n : Nat} (rows : List (List ℚ)) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun i j => ExactReplay.getQ (ExactReplay.getRow rows i.1) j.1

/-- The rational midpoint of a selected interval coordinate. -/
@[expose]
def boxMid (box : List RatInterval) (i : Nat) : ℚ :=
  let z := ExactReplay.getI box i
  (z.lo + z.hi) / 2

/-- Half the width of a selected rational interval coordinate. -/
@[expose]
def boxRad (box : List RatInterval) (i : Nat) : ℚ :=
  let z := ExactReplay.getI box i
  (z.hi - z.lo) / 2

/-- Map normalized coordinates to the given box using its midpoints and radii. -/
def affineFromBox {n : Nat} (box : List RatInterval)
    (u : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (boxMid box i.1 : ℝ) + (boxRad box i.1 : ℝ) * u i

/-- Subtract each box midpoint and divide by its coordinate radius. -/
def normalizeToBox {n : Nat} (box : List RatInterval)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (x i - (boxMid box i.1 : ℝ)) / (boxRad box i.1 : ℝ)

/-- The coordinate box with interval `[-1, 1]` in every dimension. -/
@[expose]
def unitBox {n : Nat} : Fin n → IntervalRat :=
  fun _ =>
    { lo := -1
      hi := 1
      le := by norm_num }

/-- The rational origin used as the normalized Newton center. -/
@[expose]
def zeroCenter {n : Nat} : Fin n → ℚ := fun _ => 0

/-- Rescale each preconditioner row by the inverse box radius. -/
@[expose]
def scaledPreconditioner {n : Nat}
    (box : List RatInterval) (rows : List (List ℚ)) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (boxRad box i.1)⁻¹ * listMatrix rows i j

/-- The preconditioner for the normalized four-dimensional system. -/
@[expose]
def reducedY : Matrix (Fin 4) (Fin 4) ℚ :=
  scaledPreconditioner ExactReplay.reducedInputBox reducedCData

/-- The preconditioner for the normalized twenty-two-dimensional system. -/
@[expose]
def fullY : Matrix (Fin 22) (Fin 22) ℚ :=
  scaledPreconditioner ExactReplay.fullInputBox fullCData

/-- Map the normalized unit box into the reduced parameter box. -/
def reducedAffine : (Fin 4 → ℝ) → Fin 4 → ℝ :=
  affineFromBox ExactReplay.reducedInputBox

/-- Map the normalized unit box into the full Romik parameter box. -/
def fullAffine : (Fin 22 → ℝ) → Fin 22 → ℝ :=
  affineFromBox ExactReplay.fullInputBox

/-- Convert reduced parameter coordinates to normalized box coordinates. -/
def reducedNormalize : (Fin 4 → ℝ) → Fin 4 → ℝ :=
  normalizeToBox ExactReplay.reducedInputBox

/-- A deliberately generous verified contraction target.
The legacy exact bounds are ~5.2e-13 (4D) and ~8.6e-11 (22D), so `1/100`
leaves many orders of magnitude of slack while keeping the normalized self-map
well inside the unit box. -/
@[expose]
def qTarget : ℚ := 1 / 100

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Minimal named-constant extension of LeanCert's AD soundness layer

LeanCert's computable total dual evaluator already evaluates
`Expr.namedConst c` as `DualInterval.ofMathConst c`, whose derivative component
is the singleton interval `{0}`.  Its public `ADSupported` predicate, however,
does not currently include `namedConst`.

The Gerver systems necessarily contain the exact constant `Real.pi`.  This file
adds exactly one missing syntactic case -- differentiable named mathematical
constants -- while reusing LeanCert's existing evaluator, interval Jacobian,
matrix norm machinery, Newton map, and contraction theorem unchanged.

No interval arithmetic is reimplemented here.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Engine.Optimization

/-- The LeanCert AD fragment plus named mathematical constants.
Every constructor here is everywhere differentiable. -/
inductive ADConstSupported : Expr → Prop where
  | const (q : ℚ) : ADConstSupported (.const q)
  | var (idx : Nat) : ADConstSupported (.var idx)
  | add {a b : Expr} :
      ADConstSupported a → ADConstSupported b → ADConstSupported (.add a b)
  | mul {a b : Expr} :
      ADConstSupported a → ADConstSupported b → ADConstSupported (.mul a b)
  | neg {a : Expr} : ADConstSupported a → ADConstSupported (.neg a)
  | exp {a : Expr} : ADConstSupported a → ADConstSupported (.exp a)
  | sin {a : Expr} : ADConstSupported a → ADConstSupported (.sin a)
  | cos {a : Expr} : ADConstSupported a → ADConstSupported (.cos a)
  | namedConst (c : MathConst) : ADConstSupported (.namedConst c)

/-- Computable recognition of the exact fragment used by the Gerver models. -/
@[expose]
def checkADConstSupported : Expr → Bool
  | .const _ | .var _ | .namedConst _ => true
  | .add a b | .mul a b => checkADConstSupported a && checkADConstSupported b
  | .neg a | .exp a | .sin a | .cos a => checkADConstSupported a
  | _ => false

theorem checkADConstSupported_correct {e : Expr}
    (h : checkADConstSupported e = true) : ADConstSupported e := by
  induction e with
  | const q => exact .const q
  | var i => exact .var i
  | add a b iha ihb =>
      simp only [checkADConstSupported, Bool.and_eq_true] at h
      exact .add (iha h.1) (ihb h.2)
  | mul a b iha ihb =>
      simp only [checkADConstSupported, Bool.and_eq_true] at h
      exact .mul (iha h.1) (ihb h.2)
  | neg a ih =>
      exact .neg (ih h)
  | exp a ih =>
      exact .exp (ih h)
  | sin a ih =>
      exact .sin (ih h)
  | cos a ih =>
      exact .cos (ih h)
  | namedConst c =>
      exact .namedConst c
  | inv _ _ | log _ _ | atan _ _ | arsinh _ _ | atanh _ _ | sinc _ _
    | erf _ _ | sinh _ _ | cosh _ _ | tanh _ _ | sqrt _ _ =>
      simp [checkADConstSupported] at h

theorem ADConstSupported.toCore {e : Expr} (h : ADConstSupported e) :
    ExprSupportedCore e := by
  induction h with
  | const q => exact .const q
  | var i => exact .var i
  | add _ _ iha ihb => exact .add iha ihb
  | mul _ _ iha ihb => exact .mul iha ihb
  | neg _ ih => exact .neg ih
  | exp _ ih => exact .exp ih
  | sin _ ih => exact .sin ih
  | cos _ ih => exact .cos ih
  | namedConst c => exact .namedConst c

/-- Dual-evaluator domain validity is likewise automatic for this fragment. -/
theorem ADConstSupported.domainValidDual {e : Expr} (h : ADConstSupported e)
    (ρ : DualEnv) (cfg : EvalConfig) : evalDomainValidDual e ρ cfg := by
  induction h with
  | const _ => trivial
  | var _ => trivial
  | add _ _ iha ihb => exact ⟨iha, ihb⟩
  | mul _ _ iha ihb => exact ⟨iha, ihb⟩
  | neg _ ih => exact ih
  | exp _ ih => exact ih
  | sin _ ih => exact ih
  | cos _ ih => exact ih
  | namedConst _ => trivial

/-! ## Calculus layer -/

theorem evalFin_differentiable_const {n : Nat} (e : Expr)
    (h : ADConstSupported e) :
    Differentiable ℝ (evalFin (n := n) e) := by
  induction h with
  | const q =>
      rw [show evalFin (n := n) (.const q) =
        (fun _ : Fin n → ℝ => (q : ℝ)) from rfl]
      exact differentiable_const _
  | var i =>
      by_cases hi : i < n
      · rw [show evalFin (n := n) (.var i) =
          (fun x : Fin n → ℝ => x ⟨i, hi⟩) by
            funext x
            simp [evalFin, finEnv, hi]]
        exact differentiable_apply _
      · rw [show evalFin (n := n) (.var i) =
          (fun _ : Fin n → ℝ => 0) by
            funext x
            simp [evalFin, finEnv, hi]]
        exact differentiable_const _
  | add _ _ iha ihb =>
      rw [show evalFin (n := n) (.add _ _) =
        evalFin (n := n) _ + evalFin (n := n) _ from rfl]
      exact iha.add ihb
  | mul _ _ iha ihb =>
      rw [show evalFin (n := n) (.mul _ _) =
        evalFin (n := n) _ * evalFin (n := n) _ from rfl]
      exact iha.mul ihb
  | neg _ ih =>
      rw [show evalFin (n := n) (.neg _) = -evalFin (n := n) _ from rfl]
      exact ih.neg
  | exp _ ih =>
      rw [show evalFin (n := n) (.exp _) =
        Real.exp ∘ evalFin (n := n) _ from rfl]
      exact Real.differentiable_exp.comp ih
  | sin _ ih =>
      rw [show evalFin (n := n) (.sin _) =
        Real.sin ∘ evalFin (n := n) _ from rfl]
      exact Real.differentiable_sin.comp ih
  | cos _ ih =>
      rw [show evalFin (n := n) (.cos _) =
        Real.cos ∘ evalFin (n := n) _ from rfl]
      exact Real.differentiable_cos.comp ih
  | namedConst c =>
      rw [show evalFin (n := n) (.namedConst c) =
        (fun _ : Fin n → ℝ => c.toReal) from rfl]
      exact differentiable_const _

theorem evalAlong_differentiable_const (e : Expr) (h : ADConstSupported e)
    (ρ : Nat → ℝ) (idx : Nat) :
    Differentiable ℝ (Expr.evalAlong e ρ idx) := by
  induction h with
  | const q =>
      simp only [Expr.evalAlong_const']
      exact differentiable_const _
  | var i =>
      by_cases hi : i = idx
      · subst i
        simp only [Expr.evalAlong_var_active]
        exact differentiable_id
      · simp only [Expr.evalAlong_var_passive _ _ _ hi]
        exact differentiable_const _
  | add _ _ iha ihb =>
      simp only [Expr.evalAlong_add]
      exact iha.add ihb
  | mul _ _ iha ihb =>
      simp only [Expr.evalAlong_mul]
      exact iha.mul ihb
  | neg _ ih =>
      simp only [Expr.evalAlong_neg]
      exact ih.neg
  | exp _ ih =>
      simp only [Expr.evalAlong_exp]
      exact Real.differentiable_exp.comp ih
  | sin _ ih =>
      simp only [Expr.evalAlong_sin]
      exact Real.differentiable_sin.comp ih
  | cos _ ih =>
      simp only [Expr.evalAlong_cos]
      exact Real.differentiable_cos.comp ih
  | namedConst c =>
      rw [show Expr.evalAlong (.namedConst c) ρ idx =
        (fun _ : ℝ => c.toReal) from rfl]
      exact differentiable_const _

/-- LeanCert's computable total AD derivative theorem, extended by the single
missing `namedConst` case. The computed interval is unchanged. -/
theorem evalDualTotalCore_der_correct_idx_const
    (e : Expr) (h : ADConstSupported e)
    (ρReal : Nat → ℝ) (ρInt : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρReal i ∈ ρInt i)
    (x : ℝ) (hx : x ∈ ρInt idx) (cfg : EvalConfig) :
    deriv (Expr.evalAlong e ρReal idx) x ∈
      (LeanCert.Internal.AD.evalTotalCore e
        (mkDualEnvCore ρInt idx) cfg).der := by
  have hmem : ∀ i, Expr.updateVar ρReal idx x i ∈
      (mkDualEnvCore ρInt idx i).val := by
    simpa only [mkDualEnvCore, mkDualEnv] using
      (updateVar_mem_mkDualEnv_val ρReal ρInt idx x hx hρ)
  induction h generalizing x with
  | const q =>
      simp only [Expr.evalAlong_const', deriv_const,
        LeanCert.Internal.AD.evalTotalCore, DualInterval.const]
      exact_mod_cast IntervalRat.mem_singleton 0
  | var i =>
      by_cases hi : i = idx
      · subst i
        simp only [Expr.evalAlong_var_active, LeanCert.Internal.AD.evalTotalCore,
          mkDualEnvCore, ↓reduceIte, DualInterval.varActive, deriv_id]
        exact_mod_cast IntervalRat.mem_singleton 1
      · simp only [Expr.evalAlong_var_passive _ _ _ hi, deriv_const,
          LeanCert.Internal.AD.evalTotalCore, mkDualEnvCore, ite_eq_right hi,
          DualInterval.varPassive]
        exact_mod_cast IntervalRat.mem_singleton 0
  | add ha hb iha ihb =>
      have hda := evalAlong_differentiable_const _ ha ρReal idx
      have hdb := evalAlong_differentiable_const _ hb ρReal idx
      simp only [Expr.evalAlong_add_pi, deriv_add (hda x) (hdb x),
        LeanCert.Internal.AD.evalTotalCore, DualInterval.add]
      exact IntervalRat.mem_add (iha x hx hmem) (ihb x hx hmem)
  | mul ha hb iha ihb =>
      have hda := evalAlong_differentiable_const _ ha ρReal idx
      have hdb := evalAlong_differentiable_const _ hb ρReal idx
      simp only [Expr.evalAlong_mul_pi, deriv_mul (hda x) (hdb x),
        LeanCert.Internal.AD.evalTotalCore, DualInterval.mul]
      have hvalA := LeanCert.Engine.evalDualTotalCore_val_correct _ ha.toCore
        (Expr.updateVar ρReal idx x) (mkDualEnvCore ρInt idx) cfg hmem
        (ha.domainValidDual (mkDualEnvCore ρInt idx) cfg)
      have hvalB := LeanCert.Engine.evalDualTotalCore_val_correct _ hb.toCore
        (Expr.updateVar ρReal idx x) (mkDualEnvCore ρInt idx) cfg hmem
        (hb.domainValidDual (mkDualEnvCore ρInt idx) cfg)
      exact IntervalRat.mem_add
        (IntervalRat.mem_mul (iha x hx hmem) hvalB)
        (IntervalRat.mem_mul hvalA (ihb x hx hmem))
  | neg ha ih =>
      have hd := evalAlong_differentiable_const _ ha ρReal idx
      simp only [Expr.evalAlong_neg_pi, deriv.neg,
        LeanCert.Internal.AD.evalTotalCore, DualInterval.neg]
      exact IntervalRat.mem_neg (ih x hx hmem)
  | @exp a ha ih =>
      have hd := evalAlong_differentiable_const a ha ρReal idx
      simp only [Expr.evalAlong_exp, deriv_exp (hd.differentiableAt),
        LeanCert.Internal.AD.evalTotalCore, DualInterval.expCore]
      have hval := LeanCert.Engine.evalDualTotalCore_val_correct a ha.toCore
        (Expr.updateVar ρReal idx x) (mkDualEnvCore ρInt idx) cfg hmem
        (ha.domainValidDual (mkDualEnvCore ρInt idx) cfg)
      exact IntervalRat.mem_mul
        (IntervalRat.mem_expComputable hval cfg.taylorDepth) (ih x hx hmem)
  | @sin a ha ih =>
      have hd := evalAlong_differentiable_const a ha ρReal idx
      simp only [Expr.evalAlong_sin, deriv_sin (hd.differentiableAt),
        LeanCert.Internal.AD.evalTotalCore, DualInterval.sinCore]
      have hval := LeanCert.Engine.evalDualTotalCore_val_correct a ha.toCore
        (Expr.updateVar ρReal idx x) (mkDualEnvCore ρInt idx) cfg hmem
        (ha.domainValidDual (mkDualEnvCore ρInt idx) cfg)
      exact IntervalRat.mem_mul
        (IntervalRat.mem_cosComputable hval cfg.taylorDepth) (ih x hx hmem)
  | @cos a ha ih =>
      have hd := evalAlong_differentiable_const a ha ρReal idx
      simp only [Expr.evalAlong_cos, deriv_cos (hd.differentiableAt),
        LeanCert.Internal.AD.evalTotalCore, DualInterval.cosCore]
      have hval := LeanCert.Engine.evalDualTotalCore_val_correct a ha.toCore
        (Expr.updateVar ρReal idx x) (mkDualEnvCore ρInt idx) cfg hmem
        (ha.domainValidDual (mkDualEnvCore ρInt idx) cfg)
      exact IntervalRat.mem_mul
        (IntervalRat.mem_neg
          (IntervalRat.mem_sinComputable hval cfg.taylorDepth))
        (ih x hx hmem)
  | namedConst c =>
      rw [show Expr.evalAlong (.namedConst c) ρReal idx =
        (fun _ : ℝ => c.toReal) from rfl]
      simpa [LeanCert.Internal.AD.evalTotalCore, DualInterval.ofMathConst] using
        (IntervalRat.mem_singleton (0 : ℚ))

/-! ## Krawczyk calculus adapters retaining LeanCert's data path -/

theorem fderiv_single_eq_deriv_evalAlong_const {n : Nat}
    (e : Expr) (h : ADConstSupported e)
    (x : Fin n → ℝ) (j : Fin n) :
    fderiv ℝ (evalFin (n := n) e) x (Pi.single j 1) =
      deriv (Expr.evalAlong e (finEnv x) j.val) (x j) := by
  have hout : HasFDerivAt (evalFin (n := n) e)
      (fderiv ℝ (evalFin (n := n) e) (Function.update x j (x j)))
      (Function.update x j (x j)) :=
    (evalFin_differentiable_const (n := n) e h).differentiableAt.hasFDerivAt
  have hcomp := hout.comp_hasDerivAt (x j) (hasDerivAt_update x j (x j))
  rw [Function.update_eq_self] at hcomp
  have heq : (evalFin (n := n) e ∘ Function.update x j) =
      Expr.evalAlong e (finEnv x) j.val := by
    funext t
    simp only [Function.comp_apply, evalFin, Expr.evalAlong_eq]
    rw [finEnv_update]
  rw [heq] at hcomp
  exact hcomp.deriv.symm

theorem systemEval_differentiable_const {n : Nat}
    (F : Fin n → Expr) (h : ∀ i, ADConstSupported (F i)) :
    Differentiable ℝ (systemEval F) := by
  rw [differentiable_pi]
  intro i
  exact evalFin_differentiable_const (F i) (h i)

theorem jacobianAt_apply_const {n : Nat}
    (F : Fin n → Expr) (h : ∀ i, ADConstSupported (F i))
    (x : Fin n → ℝ) (i j : Fin n) :
    jacobianAt F x i j =
      deriv (Expr.evalAlong (F i) (finEnv x) j.val) (x j) := by
  rw [jacobianAt, LinearMap.toMatrix'_apply]
  change fderiv ℝ (systemEval F) x (Pi.single j 1) i = _
  rw [show systemEval F = (fun x i => evalFin (F i) x) from rfl]
  have hpi := fderiv_pi (𝕜 := ℝ) (x := x)
    (φ := fun i => evalFin (F i))
    (fun i => (evalFin_differentiable_const (F i) (h i)).differentiableAt)
  rw [hpi]
  simp only [ContinuousLinearMap.coe_pi']
  exact fderiv_single_eq_deriv_evalAlong_const (F i) (h i) x j

theorem jacobianAt_mem_intervalJacobian_const {n : Nat}
    (F : Fin n → Expr) (h : ∀ i, ADConstSupported (F i))
    (X : Fin n → IntervalRat) (x : Fin n → ℝ)
    (hx : FinBoxMem x X) (cfg : EvalConfig) (i j : Fin n) :
    jacobianAt F x i j ∈ intervalJacobian F X cfg i j := by
  rw [jacobianAt_apply_const F h x i j]
  exact evalDualTotalCore_der_correct_idx_const (F i) (h i)
    (finEnv x) (finBoxEnv X) j.val (finEnv_mem_finBoxEnv hx)
    (x j) (by
      simpa only [finBoxEnv, j.isLt, dite_true] using hx j) cfg

theorem newtonMap_differentiable_const {n : Nat}
    (Y : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin n → Expr) (h : ∀ i, ADConstSupported (F i)) :
    Differentiable ℝ (newtonMap Y F) := by
  have hY : Differentiable ℝ (fun x => matrixCLM Y (systemEval F x)) :=
    (matrixCLM Y).differentiable.comp (systemEval_differentiable_const F h)
  rw [show newtonMap Y F =
      id - (fun x => matrixCLM Y (systemEval F x)) by
        funext x
        rfl]
  exact differentiable_id.sub hY

theorem newtonMap_fderiv_matrix_const {n : Nat}
    (Y : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin n → Expr) (h : ∀ i, ADConstSupported (F i))
    (x : Fin n → ℝ) :
    LinearMap.toMatrix' (fderiv ℝ (newtonMap Y F) x).toLinearMap =
      1 - Y * jacobianAt F x := by
  have hF : HasFDerivAt (systemEval F) (fderiv ℝ (systemEval F) x) x :=
    (systemEval_differentiable_const F h).differentiableAt.hasFDerivAt
  have hY := (matrixCLM Y).hasFDerivAt.comp x hF
  have hg : HasFDerivAt (newtonMap Y F)
      (ContinuousLinearMap.id ℝ _ -
        (matrixCLM Y).comp (fderiv ℝ (systemEval F) x)) x := by
    change HasFDerivAt (fun z => z - matrixCLM Y (systemEval F z)) _ x
    exact (hasFDerivAt_id x).sub hY
  rw [hg.fderiv]
  change LinearMap.toMatrix' ((ContinuousLinearMap.id ℝ _ -
    (matrixCLM Y).comp (fderiv ℝ (systemEval F) x)).toLinearMap) = _
  rw [ContinuousLinearMap.toLinearMap_sub]
  change LinearMap.toMatrix' (1 -
    (matrixCLM Y).toLinearMap.comp
      (fderiv ℝ (systemEval F) x).toLinearMap) = _
  rw [map_sub, LinearMap.toMatrix'_one, LinearMap.toMatrix'_comp]
  have hmatY : LinearMap.toMatrix' (matrixCLM Y).toLinearMap = Y := by
    change LinearMap.toMatrix' (Matrix.mulVecLin Y) = Y
    exact LinearMap.toMatrix'_toLin' Y
  rw [hmatY]
  rfl

theorem newtonMap_fderiv_norm_le_const {n : Nat}
    (Y : Matrix (Fin n) (Fin n) ℚ)
    (F : Fin n → Expr) (h : ∀ i, ADConstSupported (F i))
    (X : Fin n → IntervalRat) (x : Fin n → ℝ)
    (hx : FinBoxMem x X) (cfg : EvalConfig) :
    ‖fderiv ℝ (newtonMap (Y.map fun q => (q : ℝ)) F) x‖ ≤
      (intervalMatrixBound
        (preconditionedJacobian Y (intervalJacobian F X cfg)) : ℝ) := by
  rw [← Matrix.linfty_opNorm_toMatrix]
  rw [newtonMap_fderiv_matrix_const
    (Y.map fun q => (q : ℝ)) F h x]
  apply matrix_norm_le_intervalMatrixBound
  exact mem_preconditionedJacobian Y (jacobianAt F x)
    (intervalJacobian F X cfg)
    (jacobianAt_mem_intervalJacobian_const F h X x hx cfg)

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# LeanCert expression models for the normalized Gerver systems

These expressions use LeanCert's differentiable AD fragment plus exact
named mathematical constants.  `LeanCertNamedConstAD` supplies the one
missing soundness case for `namedConst` (derivative zero).
-/

public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine

/-- The expression syntax interpreted by the certified interval evaluator. -/
abbrev E := Expr

/-- A rational constant expression. -/
@[expose] def ec (r : ℚ) : E := .const r
/-- An indexed variable expression. -/
@[expose] def ev (i : Nat) : E := .var i
/-- Construct the sum of two expressions. -/
@[expose] def eadd (a b : E) : E := .add a b
/-- Construct the negation of an expression. -/
@[expose] def eneg (a : E) : E := .neg a
/-- Construct a difference using addition and negation. -/
@[expose] def esub (a b : E) : E := .add a (.neg b)
/-- Construct the product of two expressions. -/
@[expose] def emul (a b : E) : E := .mul a b
/-- Multiply an expression by a rational constant. -/
@[expose] def escale (r : ℚ) (a : E) : E := .mul (.const r) a
/-- Apply sine in the expression syntax. -/
@[expose] def esin (a : E) : E := .sin a
/-- Apply cosine in the expression syntax. -/
@[expose] def ecos (a : E) : E := .cos a
/-- The named π constant in the expression syntax. -/
@[expose] def epi : E := .namedConst .pi

/-- An expression for a box coordinate in terms of its normalized variable. -/
@[expose] def scaledVar (box : List RatInterval) (i : Nat) : E :=
  eadd (ec (boxMid box i)) (emul (ec (boxRad box i)) (ev i))

/-! ## Reduced 4D -/

/-- The four reduced equations encoded as evaluator expressions. -/
@[expose] def reducedExprList : List E :=
  let a := scaledVar ExactReplay.reducedInputBox 0
  let b := scaledVar ExactReplay.reducedInputBox 1
  let phi := scaledVar ExactReplay.reducedInputBox 2
  let theta := scaledVar ExactReplay.reducedInputBox 3
  let one := ec 1
  let half := ec (1 / 2)
  let quarter := ec (1 / 4)
  let cp := ecos phi
  let sp := esin phi
  let ct := ecos theta
  let st := esin theta
  let delta := esub theta phi
  -- Keep the mathematical value exactly; AST need not match the old D object.
  let f1 :=
    eadd
      (esub
        (eadd
          (esub (emul a (esub ct cp)) (emul (escale 2 b) sp))
          (emul (esub delta one) ct))
        st)
      (eadd cp sp)
  let f2 :=
    eadd
      (esub
        (eadd
          (eadd
            (esub (emul a (eadd (escale 3 st) sp))
              (emul (escale 2 b) cp))
            (emul (escale 3 (esub delta one)) st))
          (escale 3 ct))
        sp)
      cp
  let f3 :=
    esub
      (eadd
        (esub (esub (emul a cp) sp) half)
        (emul half cp))
      (emul b sp)
  let f4 :=
    eadd
      (eadd
        (esub
          (esub
            (esub
              (esub (eadd a (escale (1 / 2) epi)) phi)
              theta)
            b)
          (ec 0))
        (emul (emul half delta) (eadd one a)))
      (emul (emul quarter delta) delta)
  List.cons f1 (List.cons f2 (List.cons f3 (List.cons f4 List.nil)))

/-- Select an equation from the reduced four-dimensional expression system. -/
@[expose] def reducedExpr (i : Fin 4) : E :=
  reducedExprList.getD i.1 (ec 0)

/-! ## Direct 22D -/

/-- A full Romik parameter encoded as a normalized variable expression. -/
@[expose] def fv (i : Nat) : E := scaledVar ExactReplay.fullInputBox i

/-- The expression for the first switching angle φ. -/
@[expose] def phiE : E := fv 20
/-- The expression for the second switching angle θ. -/
@[expose] def thetaE : E := fv 21
/-- The expression for the reflected angle `π/2 - θ`. -/
@[expose] def etaE : E := esub (escale (1 / 2) epi) thetaE
/-- The expression for the reflected angle `π/2 - φ`. -/
@[expose] def tauE : E := esub (escale (1 / 2) epi) phiE

/-- Rotate a pair of coordinate expressions by an angle expression. -/
@[expose] def rotE (t z1 z2 : E) : E × E :=
  let ct := ecos t
  let st := esin t
  (esub (emul ct z1) (emul st z2),
   eadd (emul st z1) (emul ct z2))

/-- Encode a selected closed path branch as two coordinate expressions. -/
@[expose] def pathPieceE (j : Nat) (t : E) : E × E :=
  let one := ec 1
  let half := ec (1 / 2)
  let quarter := ec (1 / 4)
  let ct := ecos t
  let st := esin t
  let data : E × E × E × E :=
    if j = 1 then
      (esub (eadd (emul (fv 10) ct) (emul (fv 11) st)) one,
       esub (eadd (emul (eneg (fv 11)) ct) (emul (fv 10) st)) half,
       fv 0, fv 1)
    else if j = 2 then
      (eadd (eadd (emul (emul (eneg quarter) t) t) (emul (fv 12) t)) (fv 13),
       esub (esub (emul half t) (fv 12)) one,
       fv 2, fv 3)
    else if j = 3 then
      (esub (fv 14) t, eadd (fv 15) t, fv 4, fv 5)
    else if j = 4 then
      (esub (eadd (emul (eneg half) t) (fv 16)) one,
       eadd (eadd (emul (emul (eneg quarter) t) t) (emul (fv 16) t)) (fv 17),
       fv 6, fv 7)
    else
      (esub (eadd (emul (fv 18) ct) (emul (fv 19) st)) half,
       esub (eadd (emul (eneg (fv 19)) ct) (emul (fv 18) st)) one,
       fv 8, fv 9)
  let rr := rotE t data.1 data.2.1
  (eadd rr.1 data.2.2.1, eadd rr.2 data.2.2.2)

/-- Encode the body-frame velocity of a selected path branch. -/
@[expose] def alphaBetaE (j : Nat) (t : E) : E × E :=
  let one := ec 1
  let half := ec (1 / 2)
  let quarter := ec (1 / 4)
  let ct := ecos t
  let st := esin t
  if j = 1 then
    (eadd (eadd (emul (escale (-2) (fv 10)) st)
                 (emul (escale 2 (fv 11)) ct)) half,
     esub (eadd (emul (escale 2 (fv 10)) ct)
                 (emul (escale 2 (fv 11)) st)) one)
  else if j = 2 then
    (esub (eadd one (escale 2 (fv 12))) t,
     eadd (eadd (eadd (emul (emul (eneg quarter) t) t)
                       (emul (fv 12) t)) (fv 13)) half)
  else if j = 3 then
    (esub (esub (eneg one) (fv 15)) t,
     esub (eadd one (fv 14)) t)
  else if j = 4 then
    (esub (esub (esub (emul (emul quarter t) t)
                       (emul (fv 16) t)) (fv 17)) half,
     esub (esub (escale 2 (fv 16)) one) t)
  else
    (eadd (esub one (emul (escale 2 (fv 18)) st))
          (emul (escale 2 (fv 19)) ct),
     esub (eadd (emul (escale 2 (fv 18)) ct)
                 (emul (escale 2 (fv 19)) st)) half)

/-- Encode the world-frame derivative of a selected path branch. -/
@[expose] def pathPrimeE (j : Nat) (t : E) : E × E :=
  let ab := alphaBetaE j t
  rotE t ab.1 ab.2

/-- The twenty-two full equations encoded as evaluator expressions. -/
@[expose] def fullExprList : List E :=
  let halfPi := escale (1 / 2) epi
  let quarterPi := escale (1 / 4) epi
  let one := ec 1
  let quarter := ec (1 / 4)
  let first : List E := [
    esub (fv 18) (fv 10),
    eadd (fv 19) (fv 11),
    esub (eadd (fv 16) (fv 12)) quarterPi,
    esub (esub (fv 17) (fv 13))
      (emul quarterPi (esub (escale 2 (fv 12)) quarterPi)),
    eadd (esub (fv 15) (fv 14)) halfPi,
    eadd (esub (fv 0) one) (fv 10),
    esub (fv 1) quarter,
    eadd (fv 11) quarter
  ]
  let pairs : List ((E × E) × (E × E)) := [
    (pathPieceE 1 phiE, pathPieceE 2 phiE),
    (pathPrimeE 1 phiE, pathPrimeE 2 phiE),
    (pathPieceE 2 thetaE, pathPieceE 3 thetaE),
    (pathPrimeE 2 thetaE, pathPrimeE 3 thetaE),
    (pathPieceE 3 etaE, pathPieceE 4 etaE),
    (pathPieceE 4 tauE, pathPieceE 5 tauE)
  ]
  let matchEqs : List E := pairs.flatMap (fun lr =>
    List.cons (esub lr.1.1 lr.2.1)
      (List.cons (esub lr.1.2 lr.2.2) List.nil))
  let lhs := pathPieceE 1 phiE
  let xe := pathPieceE 3 etaE
  let ae := (alphaBetaE 3 etaE).1
  let be :=
    (esub xe.1 (emul ae (esin etaE)),
     eadd xe.2 (emul ae (ecos etaE)))
  first ++ matchEqs ++
    List.cons (esub lhs.1 be.1) (List.cons (esub lhs.2 be.2) List.nil)

/-- Select one equation from the full Romik expression system. -/
@[expose] def fullExpr (i : Fin 22) : E :=
  fullExprList.getD i.1 (ec 0)

/-- Purely syntactic support checks for the Gerver expression fragment. -/
theorem reducedExpr_supported :
    ∀ i : Fin 4, ADConstSupported (reducedExpr i) := by
  intro i
  apply checkADConstSupported_correct
  fin_cases i <;> decide

theorem fullExpr_supported :
    ∀ i : Fin 22, ADConstSupported (fullExpr i) := by
  intro i
  apply checkADConstSupported_correct
  fin_cases i <;> decide

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Lean Cert Gerver Correspondence
-/

public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine

/-- LeanCert's named π has exactly Mathlib's real value. -/
@[simp] theorem mathConst_pi_toReal :
    MathConst.pi.toReal = Real.pi := rfl

/-! Reduced semantic correspondence. -/
theorem reducedExpr_eval_0 (u : Fin 4 → ℝ) :
    evalFin (reducedExpr (0 : Fin 4)) u =
      Reduced.vectorSystem (reducedAffine u) (0 : Fin 4) := by
  have hm := congrFun (Reduced.vectorSystem_eq_models (reducedAffine u)) (0 : Fin 4)
  rw [hm]
  simp [reducedExpr, reducedExprList, reducedAffine, affineFromBox,
    scaledVar, boxMid, boxRad, eadd, esub, emul, escale, esin, ecos,
    ec, ev, epi, evalFin, finEnv, Reduced.models, ScalarModel.var,
    ScalarModel.const, ScalarModel.add, ScalarModel.neg, ScalarModel.sub,
    ScalarModel.mul, ScalarModel.scale, ScalarModel.sin, ScalarModel.cos]; ring
theorem reducedExpr_eval_1 (u : Fin 4 → ℝ) :
    evalFin (reducedExpr (1 : Fin 4)) u =
      Reduced.vectorSystem (reducedAffine u) (1 : Fin 4) := by
  have hm := congrFun (Reduced.vectorSystem_eq_models (reducedAffine u)) (1 : Fin 4)
  rw [hm]
  simp [reducedExpr, reducedExprList, reducedAffine, affineFromBox,
    scaledVar, boxMid, boxRad, eadd, esub, emul, escale, esin, ecos,
    ec, ev, epi, evalFin, finEnv, Reduced.models, ScalarModel.var,
    ScalarModel.const, ScalarModel.add, ScalarModel.neg, ScalarModel.sub,
    ScalarModel.mul, ScalarModel.scale, ScalarModel.sin, ScalarModel.cos]

theorem reducedExpr_eval_2 (u : Fin 4 → ℝ) :
    evalFin (reducedExpr (2 : Fin 4)) u =
      Reduced.vectorSystem (reducedAffine u) (2 : Fin 4) := by
  have hm := congrFun (Reduced.vectorSystem_eq_models (reducedAffine u)) (2 : Fin 4)
  rw [hm]
  simp [reducedExpr, reducedExprList, reducedAffine, affineFromBox,
    scaledVar, boxMid, boxRad, eadd, esub, emul, escale, esin, ecos,
    ec, ev, epi, evalFin, finEnv, Reduced.models, ScalarModel.var,
    ScalarModel.const, ScalarModel.add, ScalarModel.neg, ScalarModel.sub,
    ScalarModel.mul, ScalarModel.scale, ScalarModel.sin, ScalarModel.cos]

theorem reducedExpr_eval_3 (u : Fin 4 → ℝ) :
    evalFin (reducedExpr (3 : Fin 4)) u =
      Reduced.vectorSystem (reducedAffine u) (3 : Fin 4) := by
  have hm := congrFun (Reduced.vectorSystem_eq_models (reducedAffine u)) (3 : Fin 4)
  rw [hm]
  simp [reducedExpr, reducedExprList, reducedAffine, affineFromBox,
    scaledVar, boxMid, boxRad, eadd, esub, emul, escale, esin, ecos,
    ec, ev, epi, evalFin, finEnv, Reduced.models, ScalarModel.var,
    ScalarModel.const, ScalarModel.add, ScalarModel.neg, ScalarModel.sub,
    ScalarModel.mul, ScalarModel.scale, ScalarModel.sin, ScalarModel.cos]

theorem reduced_systemEval_eq (u : Fin 4 → ℝ) :
    systemEval reducedExpr u = Reduced.vectorSystem (reducedAffine u) := by
  funext i
  fin_cases i
  · exact reducedExpr_eval_0 u
  · exact reducedExpr_eval_1 u
  · exact reducedExpr_eval_2 u
  · exact reducedExpr_eval_3 u

/-! Full 22D semantic correspondence through the already proved public
`fullDualOutput_model_eq`.  This avoids unfolding the private pathPrime helper. -/
theorem fullExpr_eval_0 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (0 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (0 : Fin 22) := by
  calc
    evalFin (fullExpr (0 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 0 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]; ring
    _ = Romik.vectorSystem (fullAffine u) (0 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (0 : Fin 22)
theorem fullExpr_eval_1 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (1 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (1 : Fin 22) := by
  calc
    evalFin (fullExpr (1 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 1 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
    _ = Romik.vectorSystem (fullAffine u) (1 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (1 : Fin 22)
theorem fullExpr_eval_2 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (2 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (2 : Fin 22) := by
  calc
    evalFin (fullExpr (2 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 2 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]; ring
    _ = Romik.vectorSystem (fullAffine u) (2 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (2 : Fin 22)
theorem fullExpr_eval_3 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (3 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (3 : Fin 22) := by
  calc
    evalFin (fullExpr (3 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 3 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]; ring
    _ = Romik.vectorSystem (fullAffine u) (3 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (3 : Fin 22)
theorem fullExpr_eval_4 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (4 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (4 : Fin 22) := by
  calc
    evalFin (fullExpr (4 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 4 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]; ring
    _ = Romik.vectorSystem (fullAffine u) (4 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (4 : Fin 22)
theorem fullExpr_eval_5 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (5 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (5 : Fin 22) := by
  calc
    evalFin (fullExpr (5 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 5 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]; ring
    _ = Romik.vectorSystem (fullAffine u) (5 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (5 : Fin 22)
theorem fullExpr_eval_6 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (6 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (6 : Fin 22) := by
  calc
    evalFin (fullExpr (6 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 6 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]; ring
    _ = Romik.vectorSystem (fullAffine u) (6 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (6 : Fin 22)
theorem fullExpr_eval_7 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (7 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (7 : Fin 22) := by
  calc
    evalFin (fullExpr (7 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 7 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
    _ = Romik.vectorSystem (fullAffine u) (7 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (7 : Fin 22)
theorem fullExpr_eval_8 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (8 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (8 : Fin 22) := by
  calc
    evalFin (fullExpr (8 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 8 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]; ring
    _ = Romik.vectorSystem (fullAffine u) (8 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (8 : Fin 22)
theorem fullExpr_eval_9 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (9 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (9 : Fin 22) := by
  calc
    evalFin (fullExpr (9 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 9 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]; ring
    _ = Romik.vectorSystem (fullAffine u) (9 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (9 : Fin 22)
theorem fullExpr_eval_10 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (10 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (10 : Fin 22) := by
  calc
    evalFin (fullExpr (10 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 10 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]; ring
    _ = Romik.vectorSystem (fullAffine u) (10 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (10 : Fin 22)
theorem fullExpr_eval_11 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (11 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (11 : Fin 22) := by
  calc
    evalFin (fullExpr (11 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 11 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]; ring
    _ = Romik.vectorSystem (fullAffine u) (11 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (11 : Fin 22)
theorem fullExpr_eval_12 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (12 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (12 : Fin 22) := by
  calc
    evalFin (fullExpr (12 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 12 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]; ring
    _ = Romik.vectorSystem (fullAffine u) (12 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (12 : Fin 22)
theorem fullExpr_eval_13 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (13 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (13 : Fin 22) := by
  calc
    evalFin (fullExpr (13 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 13 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]; ring
    _ = Romik.vectorSystem (fullAffine u) (13 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (13 : Fin 22)
theorem fullExpr_eval_14 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (14 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (14 : Fin 22) := by
  calc
    evalFin (fullExpr (14 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 14 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]; ring
    _ = Romik.vectorSystem (fullAffine u) (14 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (14 : Fin 22)
theorem fullExpr_eval_15 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (15 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (15 : Fin 22) := by
  calc
    evalFin (fullExpr (15 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 15 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]; ring
    _ = Romik.vectorSystem (fullAffine u) (15 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (15 : Fin 22)
theorem fullExpr_eval_16 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (16 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (16 : Fin 22) := by
  calc
    evalFin (fullExpr (16 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 16 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]; ring_nf
    _ = Romik.vectorSystem (fullAffine u) (16 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (16 : Fin 22)
theorem fullExpr_eval_17 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (17 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (17 : Fin 22) := by
  calc
    evalFin (fullExpr (17 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 17 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]; ring_nf
    _ = Romik.vectorSystem (fullAffine u) (17 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (17 : Fin 22)
theorem fullExpr_eval_18 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (18 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (18 : Fin 22) := by
  calc
    evalFin (fullExpr (18 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 18 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]; ring_nf
    _ = Romik.vectorSystem (fullAffine u) (18 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (18 : Fin 22)
theorem fullExpr_eval_19 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (19 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (19 : Fin 22) := by
  calc
    evalFin (fullExpr (19 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 19 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]; ring_nf
    _ = Romik.vectorSystem (fullAffine u) (19 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (19 : Fin 22)
theorem fullExpr_eval_20 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (20 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (20 : Fin 22) := by
  calc
    evalFin (fullExpr (20 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 20 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]; ring_nf
    _ = Romik.vectorSystem (fullAffine u) (20 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (20 : Fin 22)
theorem fullExpr_eval_21 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (21 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (21 : Fin 22) := by
  calc
    evalFin (fullExpr (21 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 21 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]; ring_nf
    _ = Romik.vectorSystem (fullAffine u) (21 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (21 : Fin 22)

theorem full_systemEval_eq (u : Fin 22 → ℝ) :
    systemEval fullExpr u = Romik.vectorSystem (fullAffine u) := by
  funext i
  fin_cases i
  · exact fullExpr_eval_0 u
  · exact fullExpr_eval_1 u
  · exact fullExpr_eval_2 u
  · exact fullExpr_eval_3 u
  · exact fullExpr_eval_4 u
  · exact fullExpr_eval_5 u
  · exact fullExpr_eval_6 u
  · exact fullExpr_eval_7 u
  · exact fullExpr_eval_8 u
  · exact fullExpr_eval_9 u
  · exact fullExpr_eval_10 u
  · exact fullExpr_eval_11 u
  · exact fullExpr_eval_12 u
  · exact fullExpr_eval_13 u
  · exact fullExpr_eval_14 u
  · exact fullExpr_eval_15 u
  · exact fullExpr_eval_16 u
  · exact fullExpr_eval_17 u
  · exact fullExpr_eval_18 u
  · exact fullExpr_eval_19 u
  · exact fullExpr_eval_20 u
  · exact fullExpr_eval_21 u

/-! ## Box transport -/

theorem reduced_box_strict :
    ∀ i : Fin 4,
      (ExactReplay.getI ExactReplay.reducedInputBox i.1).lo <
      (ExactReplay.getI ExactReplay.reducedInputBox i.1).hi := by
  intro i
  fin_cases i <;>
    norm_num [ExactReplay.reducedInputBox, CertificateManifest.x4,
      CertificateManifest.q, ExactReplay.getI]

theorem full_box_strict :
    ∀ i : Fin 22,
      (ExactReplay.getI ExactReplay.fullInputBox i.1).lo <
      (ExactReplay.getI ExactReplay.fullInputBox i.1).hi := by
  intro i
  fin_cases i <;>
    norm_num [ExactReplay.fullInputBox, CertificateManifest.z22,
      CertificateManifest.q, ExactReplay.getI]

theorem affine_mem_interval
    (z : RatInterval) (hz : z.lo < z.hi) (u : ℝ)
    (hu : (-1 : ℝ) ≤ u ∧ u ≤ 1) :
    RatInterval.Contains z
      ((((z.lo + z.hi) / 2 : ℚ) : ℝ) +
       ((((z.hi - z.lo) / 2 : ℚ) : ℝ) * u)) := by
  have hzR : (z.lo : ℝ) < (z.hi : ℝ) := by
    exact_mod_cast hz
  have hrad : 0 ≤ ((z.hi : ℝ) - (z.lo : ℝ)) / 2 := by
    linarith
  constructor
  · push_cast
    calc
      (z.lo : ℝ) =
          ((z.lo : ℝ) + (z.hi : ℝ)) / 2 +
            (((z.hi : ℝ) - (z.lo : ℝ)) / 2) * (-1) := by ring
      _ ≤ ((z.lo : ℝ) + (z.hi : ℝ)) / 2 +
            (((z.hi : ℝ) - (z.lo : ℝ)) / 2) * u := by
        exact add_le_add_right
          (mul_le_mul_of_nonneg_left hu.1 hrad)
          (((z.lo : ℝ) + (z.hi : ℝ)) / 2)
  · push_cast
    calc
      ((z.lo : ℝ) + (z.hi : ℝ)) / 2 +
            (((z.hi : ℝ) - (z.lo : ℝ)) / 2) * u
          ≤ ((z.lo : ℝ) + (z.hi : ℝ)) / 2 +
            (((z.hi : ℝ) - (z.lo : ℝ)) / 2) * 1 := by
        exact add_le_add_right
          (mul_le_mul_of_nonneg_left hu.2 hrad)
          (((z.lo : ℝ) + (z.hi : ℝ)) / 2)
      _ = (z.hi : ℝ) := by ring

theorem normalize_mem_unit
    (z : RatInterval) (hz : z.lo < z.hi) (x : ℝ)
    (hx : RatInterval.Contains z x) :
    ((x - ((((z.lo + z.hi) / 2 : ℚ) : ℝ))) /
      ((((z.hi - z.lo) / 2 : ℚ) : ℝ))) ∈
      (unitBox (n := 1) (0 : Fin 1)) := by
  have hrQ : (0 : ℚ) < (z.hi - z.lo) / 2 := by
    linarith
  have hr : (0 : ℝ) < ((((z.hi - z.lo) / 2 : ℚ) : ℝ)) := by
    exact_mod_cast hrQ
  have hbounds :
      (-1 : ℝ) ≤
          (x - ((((z.lo + z.hi) / 2 : ℚ) : ℝ))) /
            ((((z.hi - z.lo) / 2 : ℚ) : ℝ)) ∧
        (x - ((((z.lo + z.hi) / 2 : ℚ) : ℝ))) /
            ((((z.hi - z.lo) / 2 : ℚ) : ℝ)) ≤ 1 := by
    constructor
    · rw [le_div_iff₀ hr]
      push_cast
      have hxlo := hx.1
      linarith
    · rw [div_le_iff₀ hr]
      push_cast
      have hxhi := hx.2
      linarith
  simpa [unitBox, IntervalRat.mem_def] using hbounds

theorem affine_normalize_coord
    (z : RatInterval) (hz : z.lo < z.hi) (x : ℝ) :
    ((((z.lo + z.hi) / 2 : ℚ) : ℝ) +
      ((((z.hi - z.lo) / 2 : ℚ) : ℝ) *
        ((x - ((((z.lo + z.hi) / 2 : ℚ) : ℝ))) /
          ((((z.hi - z.lo) / 2 : ℚ) : ℝ))))) = x := by
  have hrQ : ((z.hi - z.lo) / 2 : ℚ) ≠ 0 := by
    have : (0 : ℚ) < (z.hi - z.lo) / 2 := by linarith
    exact ne_of_gt this
  have hr : ((((z.hi - z.lo) / 2 : ℚ) : ℝ)) ≠ 0 := by
    exact_mod_cast hrQ
  field_simp
  ring

theorem reducedAffine_mem {u : Fin 4 → ℝ}
    (hu : FinBoxMem u (unitBox (n := 4))) :
    reducedAffine u ∈ Reduced.vectorBox := by
  apply (Reduced.inputBox_exact _).2
  refine ⟨by norm_num [ExactReplay.reducedInputBox, CertificateManifest.x4], ?_⟩
  intro i
  simpa [reducedAffine, affineFromBox, boxMid, boxRad,
    ExactReplay.getI, ExactReplay.zeroI, RatInterval.point] using
    affine_mem_interval
      (ExactReplay.getI ExactReplay.reducedInputBox i.1)
      (reduced_box_strict i) (u i) (by
        simpa [unitBox, IntervalRat.mem_def] using hu i)

theorem fullAffine_mem {u : Fin 22 → ℝ}
    (hu : FinBoxMem u (unitBox (n := 22))) :
    fullAffine u ∈ Romik.vectorBox := by
  apply (Romik.inputBox_exact _).2
  refine ⟨by norm_num [ExactReplay.fullInputBox, CertificateManifest.z22], ?_⟩
  intro i
  simpa [fullAffine, affineFromBox, boxMid, boxRad,
    ExactReplay.getI, ExactReplay.zeroI, RatInterval.point] using
    affine_mem_interval
      (ExactReplay.getI ExactReplay.fullInputBox i.1)
      (full_box_strict i) (u i) (by
        simpa [unitBox, IntervalRat.mem_def] using hu i)

theorem reducedNormalize_mem {x : Fin 4 → ℝ}
    (hx : x ∈ Reduced.vectorBox) :
    FinBoxMem (reducedNormalize x) (unitBox (n := 4)) := by
  have henc := (Reduced.inputBox_exact x).1 hx
  intro i
  have hi := henc.2 i
  have h := normalize_mem_unit
    (ExactReplay.getI ExactReplay.reducedInputBox i.1)
    (reduced_box_strict i) (x i) hi
  simpa [reducedNormalize, normalizeToBox, boxMid, boxRad, unitBox,
    IntervalRat.mem_def] using h

theorem reducedAffine_normalize (x : Fin 4 → ℝ) :
    reducedAffine (reducedNormalize x) = x := by
  funext i
  simpa [reducedAffine, reducedNormalize, affineFromBox, normalizeToBox,
    boxMid, boxRad] using
      affine_normalize_coord
        (ExactReplay.getI ExactReplay.reducedInputBox i.1)
        (reduced_box_strict i) (x i)

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# Determinant-free checked Krawczyk endgame

For a square system, the usual explicit determinant test on the preconditioner
is redundant once `‖I - YJ‖ < 1` is known: at any point in the box,
`YJ = 1 - T` with `‖T‖ < 1`, hence `YJ` is a unit by the Neumann-series
theorem.  Therefore `Y` is surjective, hence injective in finite dimension.

This matters computationally in dimension 22 because Mathlib's generic
Leibniz determinant is the wrong algorithm for a huge exact rational matrix.
-/

/-!
## Kernel-reducible finite interval sums

LeanCert's public `intervalRatMatVec` uses `Finset.sum` with a local
proof-transported `AddCommMonoid IntervalRat`.  That is semantically sound, but
closed `decide +kernel` computations can get stuck reducing the transported
typeclass instance.

We keep LeanCert's interval operations and mathematical semantics, but package
this one finite sum by structural recursion on `Fin n`.  Mathlib's existing
`Fin.sum_univ_succ` is the semantic bridge to the ordinary real finite sum.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine

/-- A finite interval sum that reduces by structural recursion, with no
`AddCommMonoid IntervalRat` instance involved in computation. -/
@[expose]
def kernelIntervalFinSum : {n : Nat} → (Fin n → IntervalRat) → IntervalRat
  | 0, _ => IntervalRat.singleton 0
  | n + 1, f =>
      IntervalRat.add (f 0)
        (kernelIntervalFinSum (fun j : Fin n => f j.succ))

/-- Semantic soundness of the kernel-reducible finite interval sum. -/
theorem mem_kernelIntervalFinSum :
    ∀ (n : Nat) (x : Fin n → ℝ) (I : Fin n → IntervalRat),
      (∀ i, x i ∈ I i) →
      (∑ i, x i) ∈ kernelIntervalFinSum I := by
  intro n
  induction n with
  | zero =>
      intro x I h
      simp [kernelIntervalFinSum, IntervalRat.mem_def, IntervalRat.singleton]
  | succ n ih =>
      intro x I h
      rw [Fin.sum_univ_succ]
      exact IntervalRat.mem_add (h 0)
        (ih (fun j : Fin n => x j.succ)
          (fun j : Fin n => I j.succ)
          (fun j => h j.succ))

/-- Kernel-reducible exact interval matrix-vector product. -/
@[expose]
def kernelIntervalRatMatVec {n : Nat}
    (Y : Matrix (Fin n) (Fin n) ℚ)
    (v : Fin n → IntervalRat) : Fin n → IntervalRat :=
  fun i =>
    kernelIntervalFinSum
      (fun j => IntervalRat.scale (Y i j) (v j))

/-!
## Kernel-reducible point values at the Newton center

LeanCert's ordinary rational evaluator uses `sinComputableReduced` and
`cosComputableReduced`.  Those are mathematically excellent general-purpose
routines, but their period-reduction step computes a rational floor.  On the
closed Gerver certificates that floor can prevent `decide +kernel` from
normalizing an otherwise entirely rational proposition.

For the exact Gerver expression fragment (`ADConstSupported`) we therefore use
a tiny point evaluator that is identical on algebraic operations and named
constants, but calls the already-proved *unreduced* Taylor enclosures
`sinComputable` and `cosComputable`.  These enclosures are globally sound for
arbitrary real arguments; argument reduction is an optimization, not a
soundness requirement.  This keeps the Newton-center calculation purely in
kernel-reducible rational arithmetic without changing the mathematical map.
-/

/-- A kernel-reducible interval for π, using the exact project interval
whose semantic soundness is already proved in `TranscendentalSoundness`.

The generic LeanCert `MathConst.interval` route is mathematically sound, but
its named-constant machinery does not always normalize far enough for closed
`decide +kernel` comparisons.  Reusing the project's already-certified exact
rational π endpoints removes only that reduction bottleneck; it does not
change the represented real constant or weaken any enclosure. -/
@[expose]
def kernelPiInterval : IntervalRat :=
  { lo := ExactReplay.piI.lo
    hi := ExactReplay.piI.hi
    le := by
      norm_num [ExactReplay.piI, ExactReplay.q] }

/-- The true real π lies in the kernel-reducible π interval. -/
theorem real_pi_mem_kernelPiInterval : Real.pi ∈ kernelPiInterval := by
  simpa [kernelPiInterval, IntervalRat.mem_def, RatInterval.Contains] using
    ExactReplay.piI_contains_pi

/-- Named constants for the point evaluator.  π takes the specialized
kernel-reducible path; every other LeanCert named constant keeps LeanCert's
public certified interval unchanged. -/
@[expose]
def kernelNamedConstInterval (c : MathConst) : IntervalRat :=
  if c = .pi then kernelPiInterval else c.interval

/-- Point evaluator for the everywhere-defined Gerver expression fragment.
Unsupported constructors are deliberately mapped to `{0}`; the soundness
lemma below is only stated for `ADConstSupported`, whose constructors are all
handled explicitly. -/
@[expose]
def kernelPointEvalCore (e : Expr) (ρ : IntervalEnv)
    (depth : Nat) : IntervalRat :=
  match e with
  | .const q => IntervalRat.singleton q
  | .var idx => ρ idx
  | .add a b => IntervalRat.add
      (kernelPointEvalCore a ρ depth) (kernelPointEvalCore b ρ depth)
  | .mul a b => IntervalRat.mul
      (kernelPointEvalCore a ρ depth) (kernelPointEvalCore b ρ depth)
  | .neg a => IntervalRat.neg (kernelPointEvalCore a ρ depth)
  | .exp a => IntervalRat.expComputable
      (kernelPointEvalCore a ρ depth) depth
  | .sin a => IntervalRat.sinComputable
      (kernelPointEvalCore a ρ depth) depth
  | .cos a => IntervalRat.cosComputable
      (kernelPointEvalCore a ρ depth) depth
  | .namedConst c => kernelNamedConstInterval c
  | _ => IntervalRat.singleton 0

/-- Soundness of the kernel-reducible point evaluator on exactly the Gerver
fragment.  In the sine/cosine cases this uses LeanCert's global Taylor
correctness theorems directly, so no period-reduction hypothesis is needed. -/
theorem eval_mem_kernelPointEvalCore {e : Expr}
    (h : ADConstSupported e)
    (ρReal : Nat → ℝ) (ρInt : IntervalEnv)
    (hmem : envMem ρReal ρInt) (depth : Nat) :
    Expr.eval ρReal e ∈ kernelPointEvalCore e ρInt depth := by
  induction h with
  | const q =>
      simp only [Expr.eval_const, kernelPointEvalCore]
      exact IntervalRat.mem_singleton q
  | var idx =>
      simp only [Expr.eval_var, kernelPointEvalCore]
      exact hmem idx
  | add _ _ iha ihb =>
      simp only [Expr.eval_add, kernelPointEvalCore]
      exact IntervalRat.mem_add iha ihb
  | mul _ _ iha ihb =>
      simp only [Expr.eval_mul, kernelPointEvalCore]
      exact IntervalRat.mem_mul iha ihb
  | neg _ ih =>
      simp only [Expr.eval_neg, kernelPointEvalCore]
      exact IntervalRat.mem_neg ih
  | exp _ ih =>
      simp only [Expr.eval_exp, kernelPointEvalCore]
      exact IntervalRat.mem_expComputable ih depth
  | sin _ ih =>
      simp only [Expr.eval_sin, kernelPointEvalCore]
      exact IntervalRat.mem_sinComputable ih depth
  | cos _ ih =>
      simp only [Expr.eval_cos, kernelPointEvalCore]
      exact IntervalRat.mem_cosComputable ih depth
  | namedConst c =>
      simp only [Expr.eval_namedConst, kernelPointEvalCore]
      by_cases hc : c = .pi
      · subst c
        simp only [kernelNamedConstInterval]
        simpa using real_pi_mem_kernelPiInterval
      · simp only [kernelNamedConstInterval, ite_eq_right hc]
        exact c.mem_interval

/-- Taylor depth used only for the Newton-center point values.
The reduced system has coordinates at scale about `10^-15`; the 22D system
contains substantially thinner coordinates.  Depth 26 is the smallest retained value after an
exact-rational replay of all
22 normalized Newton-center images that still leaves the direct self-map
strictly inside the unit box.  It materially reduces kernel rational size
compared with depth 27/34 while leaving the Jacobian evaluator and its
already-passing certificates untouched. -/
@[expose]
def kernelCenterTaylorDepth (n : Nat) : Nat :=
  if n ≤ 4 then 20 else 26

/-- Point-value enclosures for a square system at a rational center. -/
@[expose]
def pointEvalIntervalsKernel {n : Nat}
    (F : Fin n → Expr) (m : Fin n → ℚ)
    (_cfg : EvalConfig := {}) : Fin n → IntervalRat :=
  fun i => kernelPointEvalCore (F i) (pointIntervalEnv m)
    (kernelCenterTaylorDepth n)

/-- Every real system coordinate at the rational center lies in the
kernel-reducible point enclosure. -/
theorem systemEval_mem_pointEvalIntervalsKernel_const {n : Nat}
    (F : Fin n → Expr) (h : ∀ i, ADConstSupported (F i))
    (m : Fin n → ℚ) (cfg : EvalConfig) (i : Fin n) :
    systemEval F (fun j => (m j : ℝ)) i ∈
      pointEvalIntervalsKernel F m cfg i := by
  change Expr.eval (finEnv (fun j => (m j : ℝ))) (F i) ∈
    kernelPointEvalCore (F i) (pointIntervalEnv m)
      (kernelCenterTaylorDepth n)
  exact eval_mem_kernelPointEvalCore (h i)
    (finEnv (fun j => (m j : ℝ))) (pointIntervalEnv m)
    (finEnv_ratCast_mem_pointIntervalEnv m) (kernelCenterTaylorDepth n)

/-- Kernel-reducible version of LeanCert's Newton-center enclosure. -/
@[expose]
def kernelNewtonCenterInterval {n : Nat}
    (F : Fin n → Expr) (m : Fin n → ℚ)
    (Y : Matrix (Fin n) (Fin n) ℚ)
    (cfg : EvalConfig := {}) : Fin n → IntervalRat :=
  fun i =>
    IntervalRat.sub (IntervalRat.singleton (m i))
      (kernelIntervalRatMatVec Y (pointEvalIntervalsKernel F m cfg) i)

/-- The real Newton center lies in the kernel-reducible enclosure. -/
theorem newtonMap_center_mem_kernel_const {n : Nat}
    (F : Fin n → Expr) (h : ∀ i, ADConstSupported (F i))
    (m : Fin n → ℚ) (Y : Matrix (Fin n) (Fin n) ℚ)
    (cfg : EvalConfig) (i : Fin n) :
    newtonMap (Y.map fun q => (q : ℝ)) F
        (fun j => (m j : ℝ)) i ∈
      kernelNewtonCenterInterval F m Y cfg i := by
  apply IntervalRat.mem_sub
  · exact IntervalRat.mem_singleton (m i)
  · simp only [Matrix.mulVec, dotProduct, kernelIntervalRatMatVec]
    exact mem_kernelIntervalFinSum n
      (fun j => (Y i j : ℝ) * systemEval F (fun k => (m k : ℝ)) j)
      (fun j => IntervalRat.scale (Y i j) (pointEvalIntervalsKernel F m cfg j))
      (fun j =>
        IntervalRat.mem_scale (Y i j)
          (systemEval_mem_pointEvalIntervalsKernel_const F h m cfg j))

/-- Same checked self-map enclosure as before, now with a kernel-reducible
finite interval sum at the Newton center. -/
@[expose]
def imageEnclosureWithQ {n : Nat}
    (F : Fin n → Expr) (X : Fin n → IntervalRat)
    (m : Fin n → ℚ) (Y : Matrix (Fin n) (Fin n) ℚ)
    (cfg : EvalConfig) (q : ℚ) : Fin n → IntervalRat :=
  fun i => IntervalRat.add (kernelNewtonCenterInterval F m Y cfg i)
    (symmetricInterval (q * boxRadius X m))

theorem mapsTo_of_bound_and_enclosure {n : Nat}
    (F : Fin n → Expr) (hsupp : ∀ i, ADConstSupported (F i))
    (X : Fin n → IntervalRat) (m : Fin n → ℚ)
    (hm : FinBoxMem (fun i => (m i : ℝ)) X)
    (Y : Matrix (Fin n) (Fin n) ℚ) (cfg : EvalConfig)
    (q : ℚ) (hq0 : 0 ≤ q)
    (hbound :
      intervalMatrixBound
        (preconditionedJacobian Y (intervalJacobian F X cfg)) ≤ q)
    (hencl : ∀ i,
      intervalStrictInside (imageEnclosureWithQ F X m Y cfg q i) (X i) = true) :
    Set.MapsTo (newtonMap (Y.map fun r => (r : ℝ)) F)
      (finBoxSet X) (finBoxSet X) := by
  intro x hx i
  let mr : Fin n → ℝ := fun i => (m i : ℝ)
  have hdiff :
      ‖newtonMap (Y.map fun r => (r : ℝ)) F x -
          newtonMap (Y.map fun r => (r : ℝ)) F mr‖
        ≤ (q : ℝ) * ‖x - mr‖ := by
    apply (finBoxSet_convex X).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    · intro z hz
      exact (newtonMap_differentiable_const (Y.map fun r => (r : ℝ)) F hsupp).differentiableAt
    · intro z hz
      calc
        ‖fderiv ℝ (newtonMap (Y.map fun r => (r : ℝ)) F) z‖
            ≤ (intervalMatrixBound
                (preconditionedJacobian Y (intervalJacobian F X cfg)) : ℝ) :=
          newtonMap_fderiv_norm_le_const Y F hsupp X z hz cfg
        _ ≤ (q : ℝ) := by exact_mod_cast hbound
    · exact hm
    · exact hx
  have hr0 : 0 ≤ boxRadius X m := boxRadius_nonneg X m
  have hnorm :
      ‖newtonMap (Y.map fun r => (r : ℝ)) F x -
          newtonMap (Y.map fun r => (r : ℝ)) F mr‖
        ≤ ((q * boxRadius X m : ℚ) : ℝ) := by
    calc
      _ ≤ (q : ℝ) * ‖x - mr‖ := hdiff
      _ ≤ (q : ℝ) * (boxRadius X m : ℝ) :=
        mul_le_mul_of_nonneg_left (norm_sub_center_le_boxRadius hx)
          (by exact_mod_cast hq0)
      _ = _ := by push_cast; rfl
  have hcoord :
      |(newtonMap (Y.map fun r => (r : ℝ)) F x -
          newtonMap (Y.map fun r => (r : ℝ)) F mr) i|
        ≤ ((q * boxRadius X m : ℚ) : ℝ) :=
    (norm_le_pi_norm _ i).trans hnorm
  have herr :
      (newtonMap (Y.map fun r => (r : ℝ)) F x -
          newtonMap (Y.map fun r => (r : ℝ)) F mr) i ∈
        symmetricInterval (q * boxRadius X m) := by
    rw [abs_le] at hcoord
    simpa [symmetricInterval, IntervalRat.mem_def,
      abs_of_nonneg (mul_nonneg hq0 hr0)] using hcoord
  have hcenter := newtonMap_center_mem_kernel_const F hsupp m Y cfg i
  have himage :
      newtonMap (Y.map fun r => (r : ℝ)) F x i ∈
        imageEnclosureWithQ F X m Y cfg q i := by
    have hadd := IntervalRat.mem_add hcenter herr
    simpa [imageEnclosureWithQ, mr, Pi.sub_apply] using hadd
  exact intervalStrictInside_sound (hencl i) _ himage

theorem preconditioner_injective_of_bound_lt_one {n : Nat}
    (F : Fin n → Expr) (hsupp : ∀ i, ADConstSupported (F i))
    (X : Fin n → IntervalRat) (m : Fin n → ℚ)
    (hm : FinBoxMem (fun i => (m i : ℝ)) X)
    (Y : Matrix (Fin n) (Fin n) ℚ) (cfg : EvalConfig)
    (hq :
      intervalMatrixBound
        (preconditionedJacobian Y (intervalJacobian F X cfg)) < 1) :
    Function.Injective
      (fun v : Fin n → ℝ => (Y.map fun r => (r : ℝ)).mulVec v) := by
  let Yr : Matrix (Fin n) (Fin n) ℝ := Y.map fun r => (r : ℝ)
  let mr : Fin n → ℝ := fun i => (m i : ℝ)
  let J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    fderiv ℝ (systemEval F) mr
  let A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := matrixCLM Yr
  let T : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    fderiv ℝ (newtonMap Yr F) mr
  have hTle :
      ‖T‖ ≤
        (intervalMatrixBound
          (preconditionedJacobian Y (intervalJacobian F X cfg)) : ℝ) := by
    exact newtonMap_fderiv_norm_le_const Y F hsupp X mr hm cfg
  have hTlt : ‖T‖ < 1 := lt_of_le_of_lt hTle (by exact_mod_cast hq)
  let S : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := 1 - T
  have hunitS : IsUnit S := by
    dsimp [S]
    exact isUnit_one_sub_of_norm_lt_one hTlt
  have hbijS : Function.Bijective ⇑S :=
    (ContinuousLinearMap.isUnit_iff_bijective).mp hunitS
  have hF : HasFDerivAt (systemEval F) J mr :=
    (systemEval_differentiable_const F hsupp).differentiableAt.hasFDerivAt
  have hAJ : HasFDerivAt (fun x => A (systemEval F x)) (A.comp J) mr :=
    A.hasFDerivAt.comp mr hF
  have hg : HasFDerivAt (newtonMap Yr F)
      (ContinuousLinearMap.id ℝ _ - A.comp J) mr := by
    change HasFDerivAt (fun z => z - A (systemEval F z)) _ mr
    exact (hasFDerivAt_id mr).sub hAJ
  have hT :
      T = ContinuousLinearMap.id ℝ _ - A.comp J := hg.fderiv
  have hS : S = A.comp J := by
    dsimp [S]
    rw [hT, ContinuousLinearMap.one_def]
    abel
  have hsurjComp : Function.Surjective ⇑(A.comp J) := by
    rw [← hS]
    exact hbijS.2
  have hsurjA : Function.Surjective ⇑A := by
    intro y
    obtain ⟨x, hx⟩ := hsurjComp y
    refine ⟨J x, ?_⟩
    simpa only [ContinuousLinearMap.comp_apply] using hx
  have hsurjLin : Function.Surjective ⇑A.toLinearMap := hsurjA
  have hinjLin : Function.Injective ⇑A.toLinearMap :=
    (LinearMap.injective_iff_surjective (f := A.toLinearMap)).2 hsurjLin
  intro x y hxy
  apply hinjLin
  change (Y.map fun r => (r : ℝ)).mulVec x =
    (Y.map fun r => (r : ℝ)).mulVec y
  exact hxy

theorem fixedPoint_iff_systemZero_of_injective {n : Nat}
    (F : Fin n → Expr) (Y : Matrix (Fin n) (Fin n) ℚ)
    (hinj : Function.Injective
      (fun v : Fin n → ℝ => (Y.map fun r => (r : ℝ)).mulVec v))
    (x : Fin n → ℝ) :
    newtonMap (Y.map fun r => (r : ℝ)) F x = x ↔ SystemZero F x := by
  let Yr : Matrix (Fin n) (Fin n) ℝ := Y.map fun r => (r : ℝ)
  constructor
  · intro hfix
    have hmul : Yr.mulVec (systemEval F x) = 0 := by
      funext i
      have hi := congrFun hfix i
      change x i - Yr.mulVec (systemEval F x) i = x i at hi
      exact sub_eq_self.mp hi
    have hz : systemEval F x = 0 := hinj (by simpa [Yr] using hmul)
    intro i
    exact congrFun hz i
  · intro hz
    have hs : systemEval F x = 0 := by
      funext i
      exact hz i
    funext i
    simp [newtonMap, hs]

theorem uniqueSystemZero_of_certified_contraction {n : Nat}
    (F : Fin n → Expr) (hsupp : ∀ i, ADConstSupported (F i))
    (X : Fin n → IntervalRat) (m : Fin n → ℚ)
    (hm : FinBoxMem (fun i => (m i : ℝ)) X)
    (Y : Matrix (Fin n) (Fin n) ℚ) (cfg : EvalConfig)
    (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbound :
      intervalMatrixBound
        (preconditionedJacobian Y (intervalJacobian F X cfg)) ≤ q)
    (hencl : ∀ i,
      intervalStrictInside (imageEnclosureWithQ F X m Y cfg q i) (X i) = true) :
    ∃! x, FinBoxMem x X ∧ SystemZero F x := by
  have hmap := mapsTo_of_bound_and_enclosure
    F hsupp X m hm Y cfg q hq0 hbound hencl
  have hactualLt :
      intervalMatrixBound
        (preconditionedJacobian Y (intervalJacobian F X cfg)) < 1 :=
    lt_of_le_of_lt hbound hq1
  have hinj := preconditioner_injective_of_bound_lt_one
    F hsupp X m hm Y cfg hactualLt
  have hfixed := contraction_unique_fixedPoint_in_finBox X
    (fun i => (m i : ℝ)) hm
    (newtonMap (Y.map fun r => (r : ℝ)) F)
    hmap (q : ℝ) (by exact_mod_cast hq0) (by exact_mod_cast hq1)
    (fun x _ =>
      (newtonMap_differentiable_const (Y.map fun r => (r : ℝ)) F hsupp).differentiableAt)
    (fun x hx => by
      calc
        ‖fderiv ℝ (newtonMap (Y.map fun r => (r : ℝ)) F) x‖
            ≤ (intervalMatrixBound
                (preconditionedJacobian Y (intervalJacobian F X cfg)) : ℝ) :=
          newtonMap_fderiv_norm_le_const Y F hsupp X x hx cfg
        _ ≤ (q : ℝ) := by exact_mod_cast hbound)
  refine ⟨hfixed.choose, ⟨hfixed.choose_spec.1.1,
    (fixedPoint_iff_systemZero_of_injective F Y hinj hfixed.choose).mp
      hfixed.choose_spec.1.2⟩, ?_⟩
  intro y hy
  exact hfixed.unique ⟨hy.1,
    (fixedPoint_iff_systemZero_of_injective F Y hinj y).mpr hy.2⟩
    hfixed.choose_spec.1

/-!
## Cached Newton-center values for large closed systems

For the direct 22D Gerver certificate, recomputing all 22 transcendental
point values inside every image-row proposition creates a very large kernel
reduction.  The following variant accepts independently checked point-value
enclosures.  It changes no mathematics: each cached interval is accompanied
by a kernel proof that the corresponding real system value lies in it.
-/

/-- Endpoint inclusion between two rational intervals. -/
@[expose]
def intervalContained (I J : IntervalRat) : Prop :=
  J.lo ≤ I.lo ∧ I.hi ≤ J.hi

theorem mem_of_intervalContained {x : ℝ} {I J : IntervalRat}
    (hx : x ∈ I) (hIJ : intervalContained I J) : x ∈ J := by
  change J.lo ≤ I.lo ∧ I.hi ≤ J.hi at hIJ
  rw [IntervalRat.mem_def] at hx ⊢
  have hlo : (J.lo : ℝ) ≤ (I.lo : ℝ) := by
    exact_mod_cast hIJ.1
  have hhi : (I.hi : ℝ) ≤ (J.hi : ℝ) := by
    exact_mod_cast hIJ.2
  exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩

/-- Newton-center enclosure from externally supplied, proof-carrying point
value intervals. -/
@[expose]
def kernelNewtonCenterIntervalWithValues {n : Nat}
    (m : Fin n → ℚ) (Y : Matrix (Fin n) (Fin n) ℚ)
    (V : Fin n → IntervalRat) : Fin n → IntervalRat :=
  fun i =>
    IntervalRat.sub (IntervalRat.singleton (m i))
      (kernelIntervalRatMatVec Y V i)

theorem newtonMap_center_mem_kernel_values {n : Nat}
    (F : Fin n → Expr) (m : Fin n → ℚ)
    (Y : Matrix (Fin n) (Fin n) ℚ)
    (V : Fin n → IntervalRat)
    (hV : ∀ j, systemEval F (fun k => (m k : ℝ)) j ∈ V j)
    (i : Fin n) :
    newtonMap (Y.map fun q => (q : ℝ)) F
        (fun j => (m j : ℝ)) i ∈
      kernelNewtonCenterIntervalWithValues m Y V i := by
  apply IntervalRat.mem_sub
  · exact IntervalRat.mem_singleton (m i)
  · simp only [Matrix.mulVec, dotProduct, kernelIntervalRatMatVec]
    exact mem_kernelIntervalFinSum n
      (fun j => (Y i j : ℝ) * systemEval F (fun k => (m k : ℝ)) j)
      (fun j => IntervalRat.scale (Y i j) (V j))
      (fun j => IntervalRat.mem_scale (Y i j) (hV j))

/-- Self-map enclosure built from independently certified center values. -/
@[expose]
def imageEnclosureWithValuesQ {n : Nat}
    (X : Fin n → IntervalRat) (m : Fin n → ℚ)
    (Y : Matrix (Fin n) (Fin n) ℚ) (V : Fin n → IntervalRat)
    (q : ℚ) : Fin n → IntervalRat :=
  fun i => IntervalRat.add (kernelNewtonCenterIntervalWithValues m Y V i)
    (symmetricInterval (q * boxRadius X m))

theorem mapsTo_of_bound_and_values_enclosure {n : Nat}
    (F : Fin n → Expr) (hsupp : ∀ i, ADConstSupported (F i))
    (X : Fin n → IntervalRat) (m : Fin n → ℚ)
    (hm : FinBoxMem (fun i => (m i : ℝ)) X)
    (Y : Matrix (Fin n) (Fin n) ℚ) (cfg : EvalConfig)
    (q : ℚ) (hq0 : 0 ≤ q)
    (hbound :
      intervalMatrixBound
        (preconditionedJacobian Y (intervalJacobian F X cfg)) ≤ q)
    (V : Fin n → IntervalRat)
    (hV : ∀ j, systemEval F (fun k => (m k : ℝ)) j ∈ V j)
    (hencl : ∀ i,
      intervalStrictInside (imageEnclosureWithValuesQ X m Y V q i) (X i) = true) :
    Set.MapsTo (newtonMap (Y.map fun r => (r : ℝ)) F)
      (finBoxSet X) (finBoxSet X) := by
  intro x hx i
  let mr : Fin n → ℝ := fun i => (m i : ℝ)
  have hdiff :
      ‖newtonMap (Y.map fun r => (r : ℝ)) F x -
          newtonMap (Y.map fun r => (r : ℝ)) F mr‖
        ≤ (q : ℝ) * ‖x - mr‖ := by
    apply (finBoxSet_convex X).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    · intro z hz
      exact (newtonMap_differentiable_const (Y.map fun r => (r : ℝ)) F hsupp).differentiableAt
    · intro z hz
      calc
        ‖fderiv ℝ (newtonMap (Y.map fun r => (r : ℝ)) F) z‖
            ≤ (intervalMatrixBound
                (preconditionedJacobian Y (intervalJacobian F X cfg)) : ℝ) :=
          newtonMap_fderiv_norm_le_const Y F hsupp X z hz cfg
        _ ≤ (q : ℝ) := by exact_mod_cast hbound
    · exact hm
    · exact hx
  have hr0 : 0 ≤ boxRadius X m := boxRadius_nonneg X m
  have hnorm :
      ‖newtonMap (Y.map fun r => (r : ℝ)) F x -
          newtonMap (Y.map fun r => (r : ℝ)) F mr‖
        ≤ ((q * boxRadius X m : ℚ) : ℝ) := by
    calc
      _ ≤ (q : ℝ) * ‖x - mr‖ := hdiff
      _ ≤ (q : ℝ) * (boxRadius X m : ℝ) :=
        mul_le_mul_of_nonneg_left (norm_sub_center_le_boxRadius hx)
          (by exact_mod_cast hq0)
      _ = _ := by push_cast; rfl
  have hcoord :
      |(newtonMap (Y.map fun r => (r : ℝ)) F x -
          newtonMap (Y.map fun r => (r : ℝ)) F mr) i|
        ≤ ((q * boxRadius X m : ℚ) : ℝ) :=
    (norm_le_pi_norm _ i).trans hnorm
  have herr :
      (newtonMap (Y.map fun r => (r : ℝ)) F x -
          newtonMap (Y.map fun r => (r : ℝ)) F mr) i ∈
        symmetricInterval (q * boxRadius X m) := by
    rw [abs_le] at hcoord
    simpa [symmetricInterval, IntervalRat.mem_def,
      abs_of_nonneg (mul_nonneg hq0 hr0)] using hcoord
  have hcenter := newtonMap_center_mem_kernel_values F m Y V hV i
  have himage :
      newtonMap (Y.map fun r => (r : ℝ)) F x i ∈
        imageEnclosureWithValuesQ X m Y V q i := by
    have hadd := IntervalRat.mem_add hcenter herr
    simpa [imageEnclosureWithValuesQ, mr, Pi.sub_apply] using hadd
  exact intervalStrictInside_sound (hencl i) _ himage

theorem uniqueSystemZero_of_certified_contraction_values {n : Nat}
    (F : Fin n → Expr) (hsupp : ∀ i, ADConstSupported (F i))
    (X : Fin n → IntervalRat) (m : Fin n → ℚ)
    (hm : FinBoxMem (fun i => (m i : ℝ)) X)
    (Y : Matrix (Fin n) (Fin n) ℚ) (cfg : EvalConfig)
    (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbound :
      intervalMatrixBound
        (preconditionedJacobian Y (intervalJacobian F X cfg)) ≤ q)
    (V : Fin n → IntervalRat)
    (hV : ∀ j, systemEval F (fun k => (m k : ℝ)) j ∈ V j)
    (hencl : ∀ i,
      intervalStrictInside (imageEnclosureWithValuesQ X m Y V q i) (X i) = true) :
    ∃! x, FinBoxMem x X ∧ SystemZero F x := by
  have hmap := mapsTo_of_bound_and_values_enclosure
    F hsupp X m hm Y cfg q hq0 hbound V hV hencl
  have hactualLt :
      intervalMatrixBound
        (preconditionedJacobian Y (intervalJacobian F X cfg)) < 1 :=
    lt_of_le_of_lt hbound hq1
  have hinj := preconditioner_injective_of_bound_lt_one
    F hsupp X m hm Y cfg hactualLt
  have hfixed := contraction_unique_fixedPoint_in_finBox X
    (fun i => (m i : ℝ)) hm
    (newtonMap (Y.map fun r => (r : ℝ)) F)
    hmap (q : ℝ) (by exact_mod_cast hq0) (by exact_mod_cast hq1)
    (fun x _ =>
      (newtonMap_differentiable_const (Y.map fun r => (r : ℝ)) F hsupp).differentiableAt)
    (fun x hx => by
      calc
        ‖fderiv ℝ (newtonMap (Y.map fun r => (r : ℝ)) F) x‖
            ≤ (intervalMatrixBound
                (preconditionedJacobian Y (intervalJacobian F X cfg)) : ℝ) :=
          newtonMap_fderiv_norm_le_const Y F hsupp X x hx cfg
        _ ≤ (q : ℝ) := by exact_mod_cast hbound)
  refine ⟨hfixed.choose, ⟨hfixed.choose_spec.1.1,
    (fixedPoint_iff_systemZero_of_injective F Y hinj hfixed.choose).mp
      hfixed.choose_spec.1.2⟩, ?_⟩
  intro y hy
  exact hfixed.unique ⟨hy.1,
    (fixedPoint_iff_systemZero_of_injective F Y hinj y).mpr hy.2⟩
    hfixed.choose_spec.1

end PartALeanCert
end GerverSofa

end

end

end

section

/-!
# LeanCert Gerver numerical core

Only shared definitions and lightweight list lemmas live here.
The expensive 22D kernel checks are split into one Lake module per row.
-/

public section

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine

/-- The default evaluation configuration used for the numerical certificates. -/
@[expose]
def cfg : EvalConfig := {}

/-- The interval enclosure of the normalized reduced Newton-map derivative. -/
@[expose]
def reducedPJ : Matrix (Fin 4) (Fin 4) IntervalRat :=
  preconditionedJacobian reducedY
    (intervalJacobian reducedExpr (unitBox (n := 4)) cfg)

/-- The interval enclosure of the normalized full Newton-map derivative. -/
@[expose]
def fullPJ : Matrix (Fin 22) (Fin 22) IntervalRat :=
  preconditionedJacobian fullY
    (intervalJacobian fullExpr (unitBox (n := 22)) cfg)

theorem qTarget_pos : (0 : ℚ) < qTarget := by norm_num [qTarget]
theorem qTarget_nonneg : (0 : ℚ) ≤ qTarget := qTarget_pos.le
theorem qTarget_lt_one : qTarget < (1 : ℚ) := by norm_num [qTarget]

/-- Assemble a bound from independently kernel-checked rows without re-running AD. -/
theorem foldl_max_lt {xs : List ℚ} {a q : ℚ}
    (ha : a < q) (hxs : ∀ x ∈ xs, x < q) :
    xs.foldl max a < q := by
  induction xs generalizing a with
  | nil => simpa using ha
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact max_lt ha (hxs x (by simp))
      · intro y hy
        exact hxs y (by simp [hy])

theorem matrixBound_lt_of_rows {n : Nat}
    (A : Matrix (Fin n) (Fin n) IntervalRat) (q : ℚ)
    (hq0 : 0 < q)
    (hrows : ∀ i : Fin n, intervalMatrixRowBound A i < q) :
    intervalMatrixBound A < q := by
  unfold intervalMatrixBound
  apply foldl_max_lt hq0
  intro x hx
  rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
  exact hrows i

/-! ## Proof-carrying cache for the 22 Newton-center residuals

These deliberately simple rational intervals are much wider than the actual
point residuals, but still narrow enough after the scaled preconditioner to
leave a large self-map margin.  Each coordinate is checked independently in a
separate module before it is used by the final contraction theorem.
-/
/-- Cached interval evaluations of the full system at the normalized center. -/
@[expose]
def fullPointCacheList : List IntervalRat := [
  ⟨q (-1) 100000000000000000000000000000, q 1 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 100000000000000000000000000000, q 1 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q 0 1, q 3 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 50000000000000000000000000000, q 1 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 100000000000000000000000000000, q 1 50000000000000000000000000000, by norm_num [q]⟩,
  ⟨q 0 1, q 1 50000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 100000000000000000000000000000, q 1 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 100000000000000000000000000000, q 1 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 100000000000000000000000000000, q 1 50000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 100000000000000000000000000000, q 1 50000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 50000000000000000000000000000, q 1 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q 1 100000000000000000000000000000, q 1 25000000000000000000000000000, by norm_num [q]⟩,
  ⟨q 0 1, q 3 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 50000000000000000000000000000, q 1 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 100000000000000000000000000000, q 1 50000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 100000000000000000000000000000, q 1 50000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 50000000000000000000000000000, q 1 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 50000000000000000000000000000, q 1 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 25000000000000000000000, q 1 20000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 20000000000000000000000, q 1 25000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 100000000000000000000000000000, q 3 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-3) 100000000000000000000000000000, q 1 100000000000000000000000000000, by norm_num [q]⟩
]

/-- Select a cached center evaluation of a full-system equation. -/
@[expose]
def fullPointCache (i : Fin 22) : IntervalRat :=
  fullPointCacheList.getD i.1 (IntervalRat.singleton 0)

/-- The full Newton image enclosure computed with cached center evaluations. -/
@[expose]
def fullImageCachedQ (i : Fin 22) : IntervalRat :=
  imageEnclosureWithValuesQ (unitBox (n := 22)) (zeroCenter (n := 22))
    fullY fullPointCache qTarget i

/-- The reduced Newton image enclosure on the normalized unit box. -/
@[expose]
def reducedImageQ (i : Fin 4) : IntervalRat :=
  imageEnclosureWithQ reducedExpr (unitBox (n := 4))
    (zeroCenter (n := 4)) reducedY cfg qTarget i

theorem reduced_center_mem :
    FinBoxMem (fun i : Fin 4 => ((zeroCenter (n := 4) i : ℚ) : ℝ))
      (unitBox (n := 4)) := by
  intro i
  simp [zeroCenter, unitBox, IntervalRat.mem_def]

theorem full_center_mem :
    FinBoxMem (fun i : Fin 22 => ((zeroCenter (n := 22) i : ℚ) : ℝ))
      (unitBox (n := 22)) := by
  intro i
  simp [zeroCenter, unitBox, IntervalRat.mem_def]

end PartALeanCert
end GerverSofa

end

end

end

end

end

end
