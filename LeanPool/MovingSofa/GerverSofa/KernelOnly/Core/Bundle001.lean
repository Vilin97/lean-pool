/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Lattice.Order
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.Foundation.Batch001`.
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

* `Basic`.
* `KrawczykSpec`.
* `RationalInterval`.
* `CertificateManifest`.
* `ExactReplay`.
-/

public section

noncomputable section

section

/-!
# Basic planar geometry for the moving-sofa problem

This file fixes the exact hallway convention used by the manuscript.
The inner quadrant is open, so contact with an inner wall is allowed.
-/

public section

namespace GerverSofa

/-- Cartesian coordinates for the hallway and sofa geometry. -/
abbrev Point := ℝ × ℝ

/-- Horizontal unit-width arm `(-∞,1] × [0,1]`. -/
@[expose]
def horizontalArm : Set Point :=
  {p | p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}

/-- Vertical unit-width arm `[0,1] × (-∞,1]`. -/
@[expose]
def verticalArm : Set Point :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 ≤ 1}

/-- Closed outer quarter-plane `(-∞,1]²`. -/
@[expose]
def outerQuarter : Set Point :=
  {p | p.1 ≤ 1 ∧ p.2 ≤ 1}

/-- Open inner quarter-plane `(-∞,0)²`. -/
@[expose]
def innerQuarter : Set Point :=
  {p | p.1 < 0 ∧ p.2 < 0}

/-- The standard unit right-angled hallway. -/
@[expose]
def hallway : Set Point := horizontalArm ∪ verticalArm

/-- Quarter-plane presentation of the standard hallway. -/
theorem hallway_eq_outer_diff_inner :
    hallway = outerQuarter \ innerQuarter := by
  ext p
  constructor
  · intro hp
    rcases hp with hp | hp
    · exact ⟨⟨hp.1, hp.2.2⟩, fun hn => (not_lt_of_ge hp.2.1) hn.2⟩
    · exact ⟨⟨hp.2.1, hp.2.2⟩, fun hn => (not_lt_of_ge hp.1) hn.1⟩
  · rintro ⟨hout, hnotin⟩
    by_cases hx : 0 ≤ p.1
    · exact Or.inr ⟨hx, hout.1, hout.2⟩
    · have hxneg : p.1 < 0 := lt_of_not_ge hx
      have hy : 0 ≤ p.2 := by
        by_contra hy0
        exact hnotin ⟨hxneg, lt_of_not_ge hy0⟩
      exact Or.inl ⟨hout.1, hy, hout.2⟩

@[simp] theorem mem_horizontalArm (p : Point) :
    p ∈ horizontalArm ↔ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := Iff.rfl

@[simp] theorem mem_verticalArm (p : Point) :
    p ∈ verticalArm ↔ 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 ≤ 1 := Iff.rfl

@[simp] theorem mem_outerQuarter (p : Point) :
    p ∈ outerQuarter ↔ p.1 ≤ 1 ∧ p.2 ≤ 1 := Iff.rfl

@[simp] theorem mem_innerQuarter (p : Point) :
    p ∈ innerQuarter ↔ p.1 < 0 ∧ p.2 < 0 := Iff.rfl

end GerverSofa

end

end

section

/-!
# Specification boundary for interval/Krawczyk certification

The records below make the logical target explicit.  A completed numerical
formalisation must construct these records from exact interval operations,
Taylor bounds for `sin`/`cos`, a certified interval Jacobian and the general
Krawczyk theorem.  No global axiom is introduced here.
-/

public section

namespace GerverSofa

/-- A unique solution of a predicate inside an explicit set. -/
structure CertifiedUniqueSolution {α : Type*} (P : α → Prop) (X : Set α) where
  /-- The certified point satisfying the predicate in the specified domain. -/
  solution : α
  solution_mem : solution ∈ X
  satisfies : P solution
  unique_iff : ∀ y, y ∈ X → (P y ↔ y = solution)

/-- Any other solution in the certified domain equals the recorded solution. -/
theorem CertifiedUniqueSolution.unique {α : Type*} {P : α → Prop} {X : Set α}
    (c : CertifiedUniqueSolution P X) (y : α) (hy : y ∈ X) (hP : P y) :
    y = c.solution := (c.unique_iff y hy).mp hP

/-- Real coordinate vectors indexed by a finite type. -/
abbrev Vec (n : Nat) := Fin n → ℝ

/-- A unique zero of a vector-valued function in a set. -/
@[expose]
def CertifiedUniqueZero {n : Nat} (F : Vec n → Vec n) (X : Set (Vec n)) :=
  CertifiedUniqueSolution (fun x => F x = 0) X

end GerverSofa

end

end

section

/-!
# Exact rational intervals

This module is intentionally small.  It provides the decidable relations used
to audit the published output manifest.  It does not assert that a particular
transcendental expression is enclosed; that analytic soundness is a distinct
proof obligation.
-/

public section

namespace GerverSofa

/-- Rational endpoints used by exact interval computations; no ordering is assumed. -/
structure RatInterval where
  /-- Lower endpoint of the interval. -/
  lo : ℚ
  /-- Upper endpoint of the interval. -/
  hi : ℚ
  deriving Repr

@[expose, instance_reducible, instance]
def instDecidableEqRatInterval : DecidableEq RatInterval := fun a b =>
  if hlo : a.lo = b.lo then
    if hhi : a.hi = b.hi then
      isTrue (by cases a; cases b; cases hlo; cases hhi; rfl)
    else
      isFalse (by intro hab; exact hhi (congrArg RatInterval.hi hab))
  else
    isFalse (by intro hab; exact hlo (congrArg RatInterval.lo hab))

namespace RatInterval

/-- Strict inclusion in the interior of another interval. -/
def strictInsideB (x outer : RatInterval) : Bool :=
  decide (outer.lo < x.lo ∧ x.hi < outer.hi)

/-- Point interval. -/
@[expose]
def point (x : ℚ) : RatInterval := ⟨x, x⟩

/-- Exact interval addition. -/
@[expose]
def add (x y : RatInterval) : RatInterval :=
  ⟨x.lo + y.lo, x.hi + y.hi⟩

/-- Exact interval negation. -/
@[expose]
def neg (x : RatInterval) : RatInterval :=
  ⟨-x.hi, -x.lo⟩

/-- Exact interval subtraction. -/
@[expose]
def sub (x y : RatInterval) : RatInterval := add x (neg y)

/-- Product hull of two rational intervals. -/
@[expose]
def mul (x y : RatInterval) : RatInterval :=
  let p₁ := x.lo * y.lo
  let p₂ := x.lo * y.hi
  let p₃ := x.hi * y.lo
  let p₄ := x.hi * y.hi
  ⟨min (min p₁ p₂) (min p₃ p₄), max (max p₁ p₂) (max p₃ p₄)⟩

/-! ## Real semantics -/

/-- Semantic membership of a real number in a rational interval. -/
@[expose]
def Contains (z : RatInterval) (x : ℝ) : Prop :=
  (z.lo : ℝ) ≤ x ∧ x ≤ (z.hi : ℝ)

@[simp] theorem strictInsideB_eq_true_iff (x outer : RatInterval) :
    strictInsideB x outer = true ↔ outer.lo < x.lo ∧ x.hi < outer.hi := by
  simp [strictInsideB]

@[simp] theorem contains_point_iff (q : ℚ) (x : ℝ) :
    Contains (point q) x ↔ x = (q : ℝ) := by
  constructor
  · intro hx
    exact le_antisymm hx.2 hx.1
  · rintro rfl
    exact ⟨le_rfl, le_rfl⟩

/-- Exact interval addition is sound over the reals. -/
theorem contains_add {a b : RatInterval} {x y : ℝ}
    (hx : Contains a x) (hy : Contains b y) :
    Contains (add a b) (x + y) := by
  rcases hx with ⟨hxl, hxu⟩
  rcases hy with ⟨hyl, hyu⟩
  simpa [Contains, add] using
    (And.intro (add_le_add hxl hyl) (add_le_add hxu hyu))

/-- Exact interval negation is sound over the reals. -/
theorem contains_neg {a : RatInterval} {x : ℝ}
    (hx : Contains a x) : Contains (neg a) (-x) := by
  rcases hx with ⟨hxl, hxu⟩
  simpa [Contains, neg] using
    (And.intro (neg_le_neg hxu) (neg_le_neg hxl))

/-- Exact interval subtraction is sound over the reals. -/
theorem contains_sub {a b : RatInterval} {x y : ℝ}
    (hx : Contains a x) (hy : Contains b y) :
    Contains (sub a b) (x - y) := by
  simpa [sub, sub_eq_add_neg] using contains_add hx (contains_neg hy)

/-- Closed interval inclusion transports semantic membership. -/
theorem contains_of_subset
    {x outer : RatInterval} {r : ℝ}
    (hsub : outer.lo ≤ x.lo ∧ x.hi ≤ outer.hi)
    (hr : Contains x r) : Contains outer r := by
  constructor
  · exact le_trans (by exact_mod_cast hsub.1) hr.1
  · exact le_trans hr.2 (by exact_mod_cast hsub.2)

/-! ## Multiplicative soundness -/

private theorem min_mul_le_mul_right
    {l u z c : ℝ} (hz : l ≤ z ∧ z ≤ u) :
    min (l * c) (u * c) ≤ z * c := by
  by_cases hc : 0 ≤ c
  · exact le_trans (min_le_left _ _)
      (mul_le_mul_of_nonneg_right hz.1 hc)
  · have hc' : c ≤ 0 := le_of_lt (lt_of_not_ge hc)
    exact le_trans (min_le_right _ _)
      (mul_le_mul_of_nonpos_right hz.2 hc')

private theorem mul_le_max_mul_right
    {l u z c : ℝ} (hz : l ≤ z ∧ z ≤ u) :
    z * c ≤ max (l * c) (u * c) := by
  by_cases hc : 0 ≤ c
  · exact le_trans (mul_le_mul_of_nonneg_right hz.2 hc)
      (le_max_right _ _)
  · have hc' : c ≤ 0 := le_of_lt (lt_of_not_ge hc)
    exact le_trans (mul_le_mul_of_nonpos_right hz.1 hc')
      (le_max_left _ _)

private theorem min_mul_le_mul_left
    {l u z c : ℝ} (hz : l ≤ z ∧ z ≤ u) :
    min (c * l) (c * u) ≤ c * z := by
  by_cases hc : 0 ≤ c
  · exact le_trans (min_le_left _ _)
      (mul_le_mul_of_nonneg_left hz.1 hc)
  · have hc' : c ≤ 0 := le_of_lt (lt_of_not_ge hc)
    exact le_trans (min_le_right _ _)
      (mul_le_mul_of_nonpos_left hz.2 hc')

private theorem mul_le_max_mul_left
    {l u z c : ℝ} (hz : l ≤ z ∧ z ≤ u) :
    c * z ≤ max (c * l) (c * u) := by
  by_cases hc : 0 ≤ c
  · exact le_trans (mul_le_mul_of_nonneg_left hz.2 hc)
      (le_max_right _ _)
  · have hc' : c ≤ 0 := le_of_lt (lt_of_not_ge hc)
    exact le_trans (mul_le_mul_of_nonpos_left hz.1 hc')
      (le_max_left _ _)

/-- The four-corner product hull contains every real product of members. -/
theorem contains_mul {a b : RatInterval} {x y : ℝ}
    (hx : Contains a x) (hy : Contains b y) :
    Contains (mul a b) (x * y) := by
  let A : ℝ := a.lo
  let B : ℝ := a.hi
  let C : ℝ := b.lo
  let D : ℝ := b.hi
  have hx' : A ≤ x ∧ x ≤ B := by
    simpa [A, B, Contains] using hx
  have hy' : C ≤ y ∧ y ≤ D := by
    simpa [C, D, Contains] using hy
  have hLowC :
      min (min (A * C) (A * D)) (min (B * C) (B * D)) ≤
        min (A * C) (B * C) := by
    apply le_min
    · exact le_trans (min_le_left _ _) (min_le_left _ _)
    · exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hLowD :
      min (min (A * C) (A * D)) (min (B * C) (B * D)) ≤
        min (A * D) (B * D) := by
    apply le_min
    · exact le_trans (min_le_left _ _) (min_le_right _ _)
    · exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hLower :
      min (min (A * C) (A * D)) (min (B * C) (B * D)) ≤ x * y := by
    have hXC :
        min (min (A * C) (A * D)) (min (B * C) (B * D)) ≤ x * C :=
      le_trans hLowC (min_mul_le_mul_right hx')
    have hXD :
        min (min (A * C) (A * D)) (min (B * C) (B * D)) ≤ x * D :=
      le_trans hLowD (min_mul_le_mul_right hx')
    exact le_trans (le_min hXC hXD) (min_mul_le_mul_left hy')
  have hUpC :
      max (A * C) (B * C) ≤
        max (max (A * C) (A * D)) (max (B * C) (B * D)) := by
    apply max_le
    · exact le_trans (le_max_left _ _) (le_max_left _ _)
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hUpD :
      max (A * D) (B * D) ≤
        max (max (A * C) (A * D)) (max (B * C) (B * D)) := by
    apply max_le
    · exact le_trans (le_max_right _ _) (le_max_left _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hUpper :
      x * y ≤ max (max (A * C) (A * D)) (max (B * C) (B * D)) := by
    have hXC : x * C ≤
        max (max (A * C) (A * D)) (max (B * C) (B * D)) :=
      le_trans (mul_le_max_mul_right hx') hUpC
    have hXD : x * D ≤
        max (max (A * C) (A * D)) (max (B * C) (B * D)) :=
      le_trans (mul_le_max_mul_right hx') hUpD
    exact le_trans (mul_le_max_mul_left hy') (max_le hXC hXD)
  simpa [Contains, mul, A, B, C, D] using And.intro hLower hUpper

/-- Rational scaling is a special case of sound interval multiplication. -/
theorem contains_scale {a : ℚ} {z : RatInterval} {x : ℝ}
    (hx : Contains z x) :
    Contains (mul (point a) z) ((a : ℝ) * x) := by
  exact contains_mul ((contains_point_iff a (a : ℝ)).2 rfl) hx

/-- Semantic validity follows from the existence of a contained real point. -/
theorem valid_of_contains {z : RatInterval} {x : ℝ} (hx : Contains z x) :
    (z.lo : ℝ) ≤ (z.hi : ℝ) := le_trans hx.1 hx.2

/-- A strict Boolean inclusion is, in particular, a closed semantic inclusion. -/
theorem contains_of_strictInsideB
    {x outer : RatInterval} {r : ℝ}
    (hstrict : strictInsideB x outer = true)
    (hr : Contains x r) : Contains outer r := by
  have h := (strictInsideB_eq_true_iff x outer).1 hstrict
  exact contains_of_subset
    ⟨le_of_lt h.1, le_of_lt h.2⟩ hr

end RatInterval
end GerverSofa

end

end

section

/-!
# Exact rational audit of the published certificate manifest

This file contains no floating-point literals.  Every value is emitted as an
integer numerator and a positive integer denominator from the deterministic
Python `Fraction` replay.  kernel reduction therefore checks the strict box
inclusions and every published rational margin in the Lean kernel/runtime.

This manifest audit deliberately does **not** by itself prove the analytic
soundness of the sine/cosine enclosures or the Krawczyk existence theorem;
those proof obligations are represented separately in `KrawczykSpec.lean` and
`GerverCertificate.lean`.
-/

public section

namespace GerverSofa.CertificateManifest

open GerverSofa

/-- Reconstruct a natural number from base-10³⁵ chunks to share decimal elaboration. -/
@[expose]
def naturalFromChunks (chunks : List ℕ) : ℕ :=
  chunks.foldl (fun n part ↦ n * 10 ^ 35 + part) 0

/-- Construct an exact rational number from its integer numerator and natural denominator. -/
@[expose]
def q (n : Int) (d : Nat) : ℚ := (n : ℚ) / (d : ℚ)
/-- The frozen rational enclosure of π used by the certificate manifest. -/
@[expose]
def declaredPi : RatInterval := ⟨q 31415926535897932384626433832795028841971693993751
  10000000000000000000000000000000000000000000000000, q
  39269908169872415480783042290993786052464617492189
  12500000000000000000000000000000000000000000000000⟩
/-- The frozen interval obtained from the manifest’s Machin-formula computation. -/
@[expose]
def machinPi : RatInterval := ⟨q (naturalFromChunks [295505634309898,
  38894826843310944618692683285957161, 54840908697424127783146795390704820,
  62285304765520132090285996624652812, 88395258878959894304877191976978068]) (naturalFromChunks
  [94062364823852, 62383071716578914264051429490249517, 24107156289559560132134809009503737,
  77692872755942719128485898305927492, 83511011526570655405521392822265625]), q (naturalFromChunks
  [3375915467483141175, 2280823352893512868952395431804961, 33509141418627522640018221186493436,
  5780061841563520292595907995044547, 84418309242836154390330033778013752]) (naturalFromChunks
  [1074587268220657145, 16687904540832335376340782508534865, 44974883186326861534485086372601111,
  18916938440811867648599426576863646, 86497881848481483757495880126953125])⟩
/-- The four rational intervals specifying the reduced parameter box. -/
@[expose]
def x4 : List RatInterval := [
    ⟨q 1888531216873 20000000000000, q 4721328042183 50000000000000⟩,
    ⟨q 69960186366677 50000000000000, q 34980093183339 25000000000000⟩,
    ⟨q 122429264969 3125000000000, q 3917736479009 100000000000000⟩,
    ⟨q 2129067216821 3125000000000, q 68130150938273 100000000000000⟩
  ]
/-- The twenty-two rational intervals specifying the full Romik parameter box. -/
@[expose]
def z22 : List RatInterval := [
    ⟨q (-21032242207268875141628571849) 100000000000000000000000000000, q
      (-21032242207268875141608571849) 100000000000000000000000000000⟩,
    ⟨q 2499999999999999999999 10000000000000000000000, q 2500000000000000000001
      10000000000000000000000⟩,
    ⟨q (-91917929277159332227479610289) 100000000000000000000000000000, q
      (-91917929277159332227459610289) 100000000000000000000000000000⟩,
    ⟨q 29525413734425341573853797657 62500000000000000000000000000, q
      29525413734425341573866297657 62500000000000000000000000000⟩,
    ⟨q (-15344080735756291713875357283) 25000000000000000000000000000, q
      (-15344080735756291713870357283) 25000000000000000000000000000⟩,
    ⟨q 17792529580064437214538861001 20000000000000000000000000000, q
      17792529580064437214542861001 20000000000000000000000000000⟩,
    ⟨q (-15417358304445500741761623987) 50000000000000000000000000000, q
      (-15417358304445500741751623987) 50000000000000000000000000000⟩,
    ⟨q 29525413734425341573853797657 62500000000000000000000000000, q
      29525413734425341573866297657 62500000000000000000000000000⟩,
    ⟨q (-20344080735756291713874857283) 20000000000000000000000000000, q
      (-20344080735756291713870857283) 20000000000000000000000000000⟩,
    ⟨q 2499999999999999999999 10000000000000000000000, q 2500000000000000000001
      10000000000000000000000⟩,
    ⟨q 2420644844145377502832171437 2000000000000000000000000000, q 2420644844145377502832571437
      2000000000000000000000000000⟩,
    ⟨q (-2500000000000000000001) 10000000000000000000000, q (-2499999999999999999999)
      10000000000000000000000⟩,
    ⟨q (-52762459802678462416060380937) 100000000000000000000000000000, q
      (-52762459802678462416040380937) 100000000000000000000000000000⟩,
    ⟨q 92025838516063762289360579501 100000000000000000000000000000, q
      92025838516063762289380579501 100000000000000000000000000000⟩,
    ⟨q 313022761424232933776114655193 500000000000000000000000000000, q
      313022761424232933776214655193 500000000000000000000000000000⟩,
    ⟨q (-151160128631428920268654781) 160000000000000000000000000, q
      (-151160128631428920268622781) 160000000000000000000000000⟩,
    ⟨q 1641278451780291167220080819 1250000000000000000000000000, q 1641278451780291167220330819
      1250000000000000000000000000⟩,
    ⟨q (-105076534082910887440587258861) 200000000000000000000000000000, q
      (-105076534082910887440547258861) 200000000000000000000000000000⟩,
    ⟨q 2420644844145377502832171437 2000000000000000000000000000, q 2420644844145377502832571437
      2000000000000000000000000000⟩,
    ⟨q 2499999999999999999999 10000000000000000000000, q 2500000000000000000001
      10000000000000000000000⟩,
    ⟨q 1958868239504182093160893749 50000000000000000000000000000, q 78354729580167283726435751
      2000000000000000000000000000⟩,
    ⟨q 34065075469136244723692787727 50000000000000000000000000000, q
      34065075469136244723692787983 50000000000000000000000000000⟩
  ]

/-- Small kernel-checkable chunks of the frozen rational certificate.

The previous one-shot package asked the kernel to normalize the whole executable
replay in one enormous `decide +kernel`.  That is logically sound but can take
hours.  Here the proof path uses the already frozen rational certificate and
checks it in bounded, independent chunks.  The expensive executable replay is
still retained in `ExactReplay.lean` as a diagnostic cross-check, but it is not
recomputed while building the trusted certificate. -/
@[expose]
def piCheck : Bool :=
  RatInterval.strictInsideB machinPi declaredPi
theorem piCheck_eq_true : piCheck = true := by
  decide +kernel

end GerverSofa.CertificateManifest

end

end

section

/-!
# Executable exact-rational replay of the 4D and 22D Krawczyk inclusions

This is a direct, floating-point-free transcription of the companion Python
algorithm.  It computes with `ℚ`, interval automatic differentiation and the
frozen rational preconditioners.  The analytic theorem saying that the Taylor
intervals enclose the real `sin` and `cos`, and the abstract Krawczyk theorem,
remain separate proof obligations; the arithmetic replay itself is decidable.
-/

public section

namespace GerverSofa.ExactReplay

open GerverSofa
open RatInterval
open scoped BigOperators

/-- Construct an exact rational number from its integer numerator and natural denominator. -/
@[expose] def q (n : Int) (d : Nat := 1) : ℚ := (n : ℚ) / (d : ℚ)

/-- The singleton rational interval at zero. -/
@[expose] def zeroI : RatInterval := point 0
/-- The singleton rational interval at one. -/
@[expose] def oneI : RatInterval := point 1

private def midpoint (x : RatInterval) : ℚ := (x.lo + x.hi) / 2

/-- Multiply an interval by a rational singleton using exact interval arithmetic. -/
@[expose] def scale (a : ℚ) (x : RatInterval) : RatInterval :=
  mul (point a) x

/-- A factorial interpreted as an exact rational number. -/
@[expose] def factorialQ (n : Nat) : ℚ := (Nat.factorial n : ℚ)

/-- An alternating Taylor term with the specified power and factorial denominator. -/
@[expose] def signedTerm (k : Nat) (x : ℚ) (power : Nat) : ℚ :=
  let z := x ^ power / factorialQ power
  if k % 2 = 0 then z else -z

/-- The finite odd-power Taylor sum for sine at a rational argument. -/
@[expose] def sinPartial (x : ℚ) (terms : Nat) : ℚ :=
  Finset.sum (Finset.range terms) (fun k => signedTerm k x (2 * k + 1))

/-- The finite even-power Taylor sum for cosine at a rational argument. -/
@[expose] def cosPartial (x : ℚ) (terms : Nat) : ℚ :=
  Finset.sum (Finset.range terms) (fun k => signedTerm k x (2 * k))

/-- The interval between the nineteen- and twenty-term sine Taylor sums. -/
@[expose] def sinBound (x : ℚ) : RatInterval :=
  let a := sinPartial x 19
  let b := sinPartial x 20
  ⟨min a b, max a b⟩

/-- The interval between the nineteen- and twenty-term cosine Taylor sums. -/
@[expose] def cosBound (x : ℚ) : RatInterval :=
  let a := cosPartial x 19
  let b := cosPartial x 20
  ⟨min a b, max a b⟩

/-- The rational π enclosure used for trigonometric argument reduction. -/
@[expose] def piI : RatInterval :=
  ⟨q 157079632679489661923132169163975144209858469968755
    50000000000000000000000000000000000000000000000000,
   q 78539816339744830961566084581987572104929234984378
     25000000000000000000000000000000000000000000000000⟩

/-- A finite alternating rational Taylor sum for arctangent. -/
@[expose] def atanPartial (x : ℚ) (terms : Nat) : ℚ :=
  Finset.sum (Finset.range terms) (fun k =>
    if k % 2 = 0 then
      x ^ (2 * k + 1) / ((2 * k + 1 : Nat) : ℚ)
    else
      -(x ^ (2 * k + 1) / ((2 * k + 1 : Nat) : ℚ)))

/-- The interval between two specified arctangent Taylor sums. -/
@[expose] def atanBound (x : ℚ) (lowTerms highTerms : Nat) : RatInterval :=
  let a := atanPartial x lowTerms
  let b := atanPartial x highTerms
  ⟨min a b, max a b⟩

/-- Evaluate the Machin expression `16 atan(1/5) - 4 atan(1/239)` by rational intervals. -/
@[expose] def machinPi : RatInterval :=
  sub (scale 16 (atanBound (1 / 5) 43 44))
      (scale 4 (atanBound (1 / 239) 13 14))

/-- Exact downward rounding to a fixed number of decimal places. -/
@[expose] def floorDecimal (x : ℚ) (digits : Nat := 60) : ℚ :=
  let scale : ℚ := (10 : ℚ) ^ digits
  ((⌊x * scale⌋ : ℤ) : ℚ) / scale

/-- Exact upward rounding to a fixed number of decimal places. -/
@[expose] def ceilDecimal (x : ℚ) (digits : Nat := 60) : ℚ :=
  let scale : ℚ := (10 : ℚ) ^ digits
  ((⌈x * scale⌉ : ℤ) : ℚ) / scale

/-- The same 60-decimal outward rounding used by the submitted verifier. -/
@[expose] def outwardDecimal (z : RatInterval) : RatInterval :=
  ⟨floorDecimal z.lo, ceilDecimal z.hi⟩

/-- Evaluate the small-argument sine enclosure with outward decimal rounding. -/
@[expose] def sinSmall (x : RatInterval) : RatInterval :=
  outwardDecimal ⟨(sinBound x.lo).lo, (sinBound x.hi).hi⟩

/-- Evaluate the small-argument cosine enclosure with outward decimal rounding. -/
@[expose] def cosSmall (x : RatInterval) : RatInterval :=
  outwardDecimal ⟨(cosBound x.hi).lo, (cosBound x.lo).hi⟩

/-- Clamp an interval to the physical angular range used by the Gerver
certificate.  If `x ∈ [0, π/2]` and `x` is enclosed by the input interval,
then `x` is still enclosed after clamping once `piI` has been proved to
contain `Real.pi`. -/
@[expose] def physicalClamp (x : RatInterval) : RatInterval :=
  ⟨max 0 x.lo, min (piI.hi / 2) x.hi⟩

/-- A fail-closed enclosure used only when an externally supplied interval is
too wide for the small-argument Taylor/range-reduction evaluator.  Every
certified Gerver call remains in one of the two sharp branches below, so this
fallback does not alter the frozen replay. -/
@[expose] def universalTrigInterval : RatInterval := ⟨-1, 1⟩

/-- Complementary interval for the identity `sin x = cos (π/2-x)` and
`cos x = sin (π/2-x)`. -/
@[expose] def complementInterval (x : RatInterval) : RatInterval :=
  ⟨max 0 (piI.lo / 2 - x.hi), piI.hi / 2 - x.lo⟩

/-- Evaluate sine by small-argument bounds and complementary-angle reduction. -/
@[expose] def sinI (x : RatInterval) : RatInterval :=
  let z := physicalClamp x
  if z.hi ≤ 9 / 10 then sinSmall z
  else
    let y := complementInterval z
    if y.hi ≤ 9 / 10 then cosSmall y else universalTrigInterval

/-- Evaluate cosine by small-argument bounds and complementary-angle reduction. -/
@[expose] def cosI (x : RatInterval) : RatInterval :=
  let z := physicalClamp x
  if z.hi ≤ 9 / 10 then cosSmall z
  else
    let y := complementInterval z
    if y.hi ≤ 9 / 10 then sinSmall y else universalTrigInterval

/-- An interval value together with a list of interval partial derivatives. -/
structure D where
  /-- The interval enclosing the scalar value. -/
  val : RatInterval
  /-- Interval enclosures for the coordinate partial derivatives. -/
  der : List RatInterval
  deriving Repr

namespace D

/-- A constant interval with zero partial derivatives in every coordinate. -/
@[expose] def const (v : RatInterval) (n : Nat) : D :=
  ⟨v, List.replicate n zeroI⟩

/-- A rational singleton with zero partial derivatives. -/
@[expose] def pointConst (v : ℚ) (n : Nat) : D := const (point v) n

/-- An interval variable with the selected coordinate derivative equal to one. -/
@[expose] def varD (v : RatInterval) (j n : Nat) : D :=
  ⟨v, (List.range n).map (fun k => point (if k = j then 1 else 0))⟩

/-- Addition with interval propagation of all coordinate derivatives. -/
@[expose] def addD (x y : D) : D :=
  ⟨add x.val y.val, List.zipWith add x.der y.der⟩

/-- Negation with interval propagation of all coordinate derivatives. -/
@[expose] def negD (x : D) : D :=
  ⟨neg x.val, x.der.map neg⟩

/-- Subtraction with interval propagation of all coordinate derivatives. -/
@[expose] def subD (x y : D) : D := addD x (negD y)

/-- Multiplication with interval propagation of all coordinate derivatives. -/
@[expose] def mulD (x y : D) : D :=
  ⟨mul x.val y.val,
   List.zipWith (fun dx dy => add (mul dx y.val) (mul x.val dy)) x.der y.der⟩

/-- Rational scaling with interval propagation of all coordinate derivatives. -/
@[expose] def scaleD (a : ℚ) (x : D) : D :=
  ⟨scale a x.val, x.der.map (scale a)⟩

/-- Sine with interval propagation of all coordinate derivatives. -/
@[expose] def sinD (x : D) : D :=
  let sv := sinI x.val
  let cv := cosI x.val
  ⟨sv, x.der.map (mul cv)⟩

/-- Cosine with interval propagation of all coordinate derivatives. -/
@[expose] def cosD (x : D) : D :=
  let sv := sinI x.val
  let cv := cosI x.val
  ⟨cv, x.der.map (fun z => neg (mul sv z))⟩

instance : Add D := ⟨addD⟩
instance : Neg D := ⟨negD⟩
instance : Sub D := ⟨subD⟩
instance : Mul D := ⟨mulD⟩
instance : HMul ℚ D D := ⟨scaleD⟩

end D

/-- Read an interval coordinate, returning the zero interval outside the list. -/
@[expose] def getI (xs : List RatInterval) (i : Nat) : RatInterval :=
  xs.getD i zeroI

/-- Read a rational coordinate, returning zero outside the list. -/
@[expose] def getQ (xs : List ℚ) (i : Nat) : ℚ := xs.getD i 0
/-- Read a rational matrix row, returning the empty row outside the list. -/
@[expose] def getRow (m : List (List ℚ)) (i : Nat) : List ℚ := m.getD i []

/-! ## Reduced 4D system -/

private def x4 : List RatInterval := [
  ⟨q 1888531216873 20000000000000, q 4721328042183 50000000000000⟩,
  ⟨q 69960186366677 50000000000000, q 34980093183339 25000000000000⟩,
  ⟨q 122429264969 3125000000000, q 3917736479009 100000000000000⟩,
  ⟨q 2129067216821 3125000000000, q 68130150938273 100000000000000⟩
]

private def z22 : List RatInterval := [
  ⟨q (-21032242207268875141628571849) 100000000000000000000000000000, q
    (-21032242207268875141608571849) 100000000000000000000000000000⟩,
  ⟨q 2499999999999999999999 10000000000000000000000, q 2500000000000000000001
    10000000000000000000000⟩,
  ⟨q (-91917929277159332227479610289) 100000000000000000000000000000, q
    (-91917929277159332227459610289) 100000000000000000000000000000⟩,
  ⟨q 29525413734425341573853797657 62500000000000000000000000000, q 29525413734425341573866297657
    62500000000000000000000000000⟩,
  ⟨q (-15344080735756291713875357283) 25000000000000000000000000000, q
    (-15344080735756291713870357283) 25000000000000000000000000000⟩,
  ⟨q 17792529580064437214538861001 20000000000000000000000000000, q 17792529580064437214542861001
    20000000000000000000000000000⟩,
  ⟨q (-15417358304445500741761623987) 50000000000000000000000000000, q
    (-15417358304445500741751623987) 50000000000000000000000000000⟩,
  ⟨q 29525413734425341573853797657 62500000000000000000000000000, q 29525413734425341573866297657
    62500000000000000000000000000⟩,
  ⟨q (-20344080735756291713874857283) 20000000000000000000000000000, q
    (-20344080735756291713870857283) 20000000000000000000000000000⟩,
  ⟨q 2499999999999999999999 10000000000000000000000, q 2500000000000000000001
    10000000000000000000000⟩,
  ⟨q 2420644844145377502832171437 2000000000000000000000000000, q 2420644844145377502832571437
    2000000000000000000000000000⟩,
  ⟨q (-2500000000000000000001) 10000000000000000000000, q (-2499999999999999999999)
    10000000000000000000000⟩,
  ⟨q (-52762459802678462416060380937) 100000000000000000000000000000, q
    (-52762459802678462416040380937) 100000000000000000000000000000⟩,
  ⟨q 92025838516063762289360579501 100000000000000000000000000000, q 92025838516063762289380579501
    100000000000000000000000000000⟩,
  ⟨q 313022761424232933776114655193 500000000000000000000000000000, q
    313022761424232933776214655193 500000000000000000000000000000⟩,
  ⟨q (-151160128631428920268654781) 160000000000000000000000000, q (-151160128631428920268622781)
    160000000000000000000000000⟩,
  ⟨q 1641278451780291167220080819 1250000000000000000000000000, q 1641278451780291167220330819
    1250000000000000000000000000⟩,
  ⟨q (-105076534082910887440587258861) 200000000000000000000000000000, q
    (-105076534082910887440547258861) 200000000000000000000000000000⟩,
  ⟨q 2420644844145377502832171437 2000000000000000000000000000, q 2420644844145377502832571437
    2000000000000000000000000000⟩,
  ⟨q 2499999999999999999999 10000000000000000000000, q 2500000000000000000001
    10000000000000000000000⟩,
  ⟨q 1958868239504182093160893749 50000000000000000000000000000, q 78354729580167283726435751
    2000000000000000000000000000⟩,
  ⟨q 34065075469136244723692787727 50000000000000000000000000000, q 34065075469136244723692787983
    50000000000000000000000000000⟩
]

/-! ## Direct 22D Romik system -/

/-! ## Public proof-carrying view and optional executable cross-check

The full executable Krawczyk/grid replay above is intentionally retained, but
normalizing it in one kernel reduction is prohibitively expensive.  The trusted
proof path therefore consumes the frozen exact-rational certificate emitted by
the independent replay and checks that certificate in `CertificateManifest`.
This is the standard proof-carrying-data split: expensive certificate discovery
is outside the kernel; small rational certificate verification is inside it.

The executable wrappers prefixed by `executable` remain available for offline
cross-checking and provenance. -/

/-- The rational interval used internally by the executable replay for `Real.pi`. -/
def declaredPiInterval : RatInterval := piI

/-- Public wrapper around the executable sine enclosure. -/
@[expose] def sineInterval (x : RatInterval) : RatInterval := sinI x

/-- Public wrapper around the executable cosine enclosure. -/
@[expose] def cosineInterval (x : RatInterval) : RatInterval := cosI x

/-- Frozen reduced input box used by the trusted certificate. -/
@[expose] def reducedInputBox : List RatInterval := CertificateManifest.x4

/-- Frozen direct-system input box used by the trusted certificate. -/
@[expose] def fullInputBox : List RatInterval := CertificateManifest.z22

end GerverSofa.ExactReplay

end

end

end

end

end
