/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.LinearAlgebra.Dimension.Localization
public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionRiemannRoch

/-!
# The canonical divisor `-2∞` on the rational function field

This module constructs an actual infinity place of the identity extension
`K(X) / K(X)`, proves that its residue degree is one, and identifies the
divisor supported there with coefficient `-2` as canonical.  The proof uses
the in-repository Riemann--Roch theorem and the proved genus-zero theorem for
`RatFunc K`; it does not assume a base canonical divisor.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped Polynomial

noncomputable section

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]

local instance ratFuncIdentityInfinityClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K (RatFunc K)) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K)
    (RatFunc K) (RatFuncInfinityIntegralClosure K (RatFunc K))

local instance ratFuncIdentityInfinityClosureIsIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K (RatFunc K)) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) (RatFunc K)

local instance ratFuncIdentityInfinityClosureIsTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K (RatFunc K)) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) (RatFunc K)

local instance ratFuncIdentityInfinityClosureNoZeroSMulDivisors :
    NoZeroSMulDivisors (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K (RatFunc K)) where
  eq_zero_or_eq_zero_of_smul_eq_zero h := smul_eq_zero.mp h

local instance ratFuncIdentityInfinityClosureIsDedekind :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K (RatFunc K)) :=
  IsIntegralClosure.isDedekindDomain (RatFuncInfinityIntegers K)
    (RatFunc K) (RatFunc K)
    (RatFuncInfinityIntegralClosure K (RatFunc K))

local instance ratFuncIdentityInfinityClosureIsFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K (RatFunc K)) (RatFunc K) :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) (RatFunc K)
    (RatFuncInfinityIntegralClosure K (RatFunc K))

/-- A place above infinity in the identity extension `K(X) / K(X)`. -/
noncomputable def ratFuncIdentityInfinityPlace :
    FiniteExtensionInfinityPlace K (RatFunc K) :=
  Classical.choice inferInstance

private theorem inertiaDegree_le_fractionField_finrank
    (R S K L : Type*) [CommRing R] [IsDomain R] [CommRing S]
    [Field K] [Field L] [Algebra R S] [Module.Finite R S] [Module.Flat R S]
    [Algebra R K] [Algebra S L] [Algebra R L] [Algebra K L]
    [IsScalarTower R K L] [IsScalarTower R S L]
    [IsFractionRing R K] [IsFractionRing S L]
    (p : Ideal R) [p.IsPrime] [Finite (p.primesOver S)]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    q.inertiaDeg R ≤ Module.finrank K L := by
  let : Fintype (p.primesOver S) := Fintype.ofFinite _
  let Q : p.primesOver S := ⟨q, inferInstance, inferInstance⟩
  calc
    q.inertiaDeg R ≤ q.ramificationIdx R * q.inertiaDeg R :=
      Nat.le_mul_of_pos_left _ (Ideal.ramificationIdx_pos q R)
    _ ≤ ∑ Q : p.primesOver S, Q.1.ramificationIdx R * Q.1.inertiaDeg R :=
      Finset.single_le_sum
        (f := fun Q : p.primesOver S => Q.1.ramificationIdx R * Q.1.inertiaDeg R)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ Q)
    _ = Module.finrank R S := Ideal.sum_ramification_inertia_eq_finrank p S
    _ = Module.finrank K L := (IsFractionRing.finrank_eq R K S L).symm

omit [Fintype K] in
/-- The chosen identity-extension infinity place has residue degree one. -/
theorem ratFuncIdentityInfinityPlace_degree_eq_one :
    finiteExtensionPlaceDegree K (RatFunc K)
        (.inr (ratFuncIdentityInfinityPlace K)) = 1 := by
  let P := ratFuncIdentityInfinityPlace K
  change P.1.inertiaDeg (RatFuncInfinityIntegers K) = 1
  have hpos : 0 < P.1.inertiaDeg (RatFuncInfinityIntegers K) :=
    Ideal.inertiaDeg_pos P.1 (RatFuncInfinityIntegers K)
  let : P.1.IsPrime := P.2.1
  let : P.1.LiesOver (ratFuncInfinityPlace K).asIdeal := P.2.2
  let : Fintype (FiniteExtensionInfinityPlace K (RatFunc K)) :=
    Set.Finite.fintype (IsDedekindDomain.primesOver_finite
      (ratFuncInfinityPlace K).asIdeal (RatFuncInfinityIntegralClosure K (RatFunc K)))
  have hle := inertiaDegree_le_fractionField_finrank
    (RatFuncInfinityIntegers K) (RatFuncInfinityIntegralClosure K (RatFunc K))
    (RatFunc K) (RatFunc K) (ratFuncInfinityPlace K).asIdeal P.1
  rw [Module.finrank_self] at hle
  omega

/-- The chosen infinity place in the Riemann--Roch two-chart place model. -/
noncomputable def ratFuncInfinityChartPlace :
    FunctionField.Chart.PlaceA K (RatFunc K) :=
  finiteExtensionPlaceEquivChart K (RatFunc K)
    (.inr (ratFuncIdentityInfinityPlace K))

/-- The explicit divisor `-2∞` on `K(X)`. -/
noncomputable def ratFuncCanonicalInfinityDivisor :
    FunctionField.Chart.DivisorA K (RatFunc K) :=
  Finsupp.single (ratFuncInfinityChartPlace K) (-2)

omit [Fintype K] [DecidableEq K] in
/-- The explicit divisor `-2∞` has degree `-2`. -/
theorem ratFuncCanonicalInfinityDivisor_degree :
    FunctionField.Chart.deg K (RatFunc K)
        (ratFuncCanonicalInfinityDivisor K) = -2 := by
  classical
  rw [ratFuncCanonicalInfinityDivisor, FunctionField.Chart.deg_single]
  have hdegree := finiteExtensionPlaceDegree_eq_chart K (RatFunc K)
    (.inr (ratFuncIdentityInfinityPlace K))
  rw [ratFuncIdentityInfinityPlace_degree_eq_one K] at hdegree
  change (1 : ℕ) = FunctionField.Chart.placeDegree K (RatFunc K)
    (ratFuncInfinityChartPlace K) at hdegree
  rw [← hdegree]
  norm_num

omit [Fintype K] [DecidableEq K] in
/-- The explicit divisor `-2∞` is canonical on `K(X)`. -/
theorem ratFuncCanonicalInfinityDivisor_isCanonical :
    FunctionField.Chart.IsCanonical K (RatFunc K)
      (ratFuncCanonicalInfinityDivisor K) := by
  classical
  rw [FunctionField.chart_isCanonical_iff_degree_ell]
  constructor
  · rw [ratFuncCanonicalInfinityDivisor_degree,
      FunctionField.Chart.genus_ratFunc]
    norm_num
  · have hnegative : FunctionField.Chart.deg K (RatFunc K)
        (ratFuncCanonicalInfinityDivisor K) < 0 := by
      rw [ratFuncCanonicalInfinityDivisor_degree]
      norm_num
    rw [FunctionField.Chart.RRspace_neg_deg_ell K (RatFunc K) hnegative,
      FunctionField.Chart.genus_ratFunc]

end

end BGS.HasseWeil
