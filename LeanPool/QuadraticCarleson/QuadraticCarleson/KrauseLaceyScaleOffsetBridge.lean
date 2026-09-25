/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceySparseDilation
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyFiniteRadiusSmoothSparse
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceySparseReflection
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyFullDyadicSparseTransfer

/-!
# The scale-offset bridge

The native KL estimate is indexed by integer dyadic suffixes. The dilation
adapter, however, asks for the finite family with radii `a * 2^k`, where `a`
is an arbitrary positive real. These are not identified here by a dyadic
invariance assertion.

The missing analytic input is isolated as an annular comparison premise. It
says that the arbitrary-offset smooth maximum is controlled, at the pairing
level, by the adjacent integer-dyadic maximum plus one comparison operator.
The latter is required to have a sparse bound. This is precisely the place
where the smooth annular difference should be dominated by the
Hardy--Littlewood maximal operator in the analytic proof. No such sparse
bound for that comparison family is currently present in the project, so the
premise is intentionally exposed rather than silently assuming the desired
conclusion.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal NNReal Topology ComplexConjugate

namespace QuadraticCarleson.KrauseLaceyScaleOffsetBridge

open QuadraticHilbertMaximalMeasurable
open KrauseLaceySparseDilation
open KrauseLaceyFiniteRadiusSmoothSparse
open KrauseLaceyCompactPairingStabilization
open KrauseLaceySparseReflection
open KrauseLaceyFullDyadicSparseTransfer


noncomputable
section

/-- The native positive dyadic-suffix input, with its constant made explicit. -/
def HasNativePositiveDyadicSuffixSparseBound (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (lam : ℝ) (j : ℤ) (p : ℝ), 1 < p → p < 2 → ∀ N : ℕ,
    HasSparseOnePBound (C * holderConjugate p) p
      (finitePositiveDyadicSuffixMaxOperator lam j N)

/-- A comparison family for one offset and one finite radius family. In the
intended application this is the finite sum of smooth annular differences
between `a * 2^k` and the adjacent integer dyadic cutoffs. -/
abbrev ComparisonFamily :=
  (a : ℝ) → (ha : 0 < a) → (s : Finset densePositiveRadii) → TestOperator

/-- Smallest faithful premise for the missing annular step: sparse control of
the comparison family itself. It does not mention the target smooth maximum.
-/
def HasComparisonFamilySparseBound (D : ℝ) (V : ComparisonFamily) : Prop :=
  0 ≤ D ∧ ∀ (a : ℝ) (ha : 0 < a) (s : Finset densePositiveRadii) (p : ℝ),
    1 < p → p < 2 → HasSparseOnePBound (D * holderConjugate p) p (V a ha s)

/- The second missing ingredient is the actual smooth-annular estimate. It is
stated at the pairing level so that no unproved pointwise or dyadic-invariance
claim is hidden in the bridge. -/
/-- Pairing domination of scaled finite-radius maxima by dyadic high-pass maxima and a
comparison family. -/
def HasScaleOffsetAnnularComparison (V : ComparisonFamily) : Prop :=
  ∀ (a : ℝ) (ha : 0 < a) (s : Finset densePositiveRadii)
    (p : ℝ) (_hp : 1 < p) (_hp2 : p < 2),
    ∀ (f g : L0Infinity),
      ‖operatorPairing (finiteSmoothMaxOperator 1
        (scaleRadii a ha (roundedRadii s))) f g‖ ≤
        ‖operatorPairing (dyadicSmoothHighPassMaxOperator 1
          (finiteRadiusLowerIndex s)) f g‖ +
        ‖operatorPairing (V a ha s) f g‖

/- The source proof is expected to instantiate `V` with the annular
comparison maximal operator and prove its sparse bound from the
Hardy--Littlewood bound. -/
theorem hasSparseOnePBound_scaleOffset_of_native_and_comparison
    {C D : ℝ} {V : ComparisonFamily}
    (hC : HasNativePositiveDyadicSuffixSparseBound C)
    (hD : HasComparisonFamilySparseBound D V)
    (hcompare : HasScaleOffsetAnnularComparison V)
    (a : ℝ) (ha : 0 < a) (s : Finset densePositiveRadii) (p : ℝ)
    (hp : 1 < p) (hp2 : p < 2) :
    HasSparseOnePBound ((2 * C + D) * holderConjugate p) p
      (finiteSmoothMaxOperator 1 (scaleRadii a ha (roundedRadii s))) := by
  have hdyadic : HasSparseOnePBound (2 * C * holderConjugate p) p
      (dyadicSmoothHighPassMaxOperator 1 (finiteRadiusLowerIndex s)) := by
    have hh := hasSparseOnePBound_dyadicSmoothHighPassMax_of_uniform_positive_finiteSuffixMax
      1 (finiteRadiusLowerIndex s) (p := p)
      (mul_nonneg hC.1 (holderConjugate_spec hp).symm.pos.le)
      (fun N ↦ hC.2 1 (finiteRadiusLowerIndex s) p hp hp2 N)
    simpa [mul_assoc] using hh
  have hpos : 0 < holderConjugate p := (holderConjugate_spec hp).symm.pos
  have hsum := hasSparseOnePBound_of_pairing_le_add
    (mul_nonneg (mul_nonneg (by norm_num) hC.1) hpos.le)
      (mul_nonneg hD.1 hpos.le) hdyadic
    (hD.2 a ha s p hp hp2)
    (U := finiteSmoothMaxOperator 1 (scaleRadii a ha (roundedRadii s)))
    (T := dyadicSmoothHighPassMaxOperator 1 (finiteRadiusLowerIndex s))
    (V := V a ha s)
    (fun f g ↦ hcompare a ha s p hp hp2 f g)
  convert hsum using 1; ring

/- The bridge to the dilation adapter is immediate once the annular premise is
proved. The constant is preserved by dilation and the comparison costs `D`.
-/
theorem hasUnitScaleOffsetSmoothSparseBound_of_native_and_comparison
    {C D : ℝ} {V : ComparisonFamily}
    (hC : HasNativePositiveDyadicSuffixSparseBound C)
    (hD : HasComparisonFamilySparseBound D V)
    (hcompare : HasScaleOffsetAnnularComparison V) :
    HasUnitScaleOffsetSmoothSparseBound (2 * C + D) := by
  refine ⟨add_nonneg (mul_nonneg (by norm_num) hC.1) hD.1, ?_⟩
  intro a ha s p hp hp2
  exact hasSparseOnePBound_scaleOffset_of_native_and_comparison
    hC hD hcompare a ha s p hp hp2


end
end QuadraticCarleson.KrauseLaceyScaleOffsetBridge
