/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Expectation.YoungRHS

/-! # JUpper Bound Weak Norms -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53

/-!
# Upper bound for `J` by weak norms

Top-level module for the first manuscript lemma in Section 5.3.  The proof is
split under `Section53/JUpperBoundWeakNorms/`; this file is the stable import
surface for the lemma.
-/

open MeasureTheory

open scoped ENNReal BigOperators

noncomputable section

/-- First manuscript lemma of Section 5.3, in its note-facing form up to the
finite-RHS inputs supplied by the scalar maximizer weak-norm lemma.  The two
integrability hypotheses say exactly that the scaled gradient and flux weak-norm
square expectations appearing on the right-hand side are finite. -/
theorem JUpperBoundWeakNorms_homogenizationScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℤ} (hk_nonneg : 0 ≤ k) (hkm : k ≤ m)
    {s t : ℝ} (hs : 0 < s) (hs_lt_one : s < 1) (ht : 0 < t)
    (hst : s + t ≤ 1)
    (p q p0 q0 : Vec d)
    (hGradSq :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.canonicalScalarResponseGradientWeakNormCubeSet
            (originCube d m) s p q p0 a.toFun) ^ 2) P)
    (hFluxSq :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
            (originCube d m) t p q q0 a.toFun) ^ 2) P) :
    let Q : TriadicCube d := originCube d m
    let j : ℕ := Int.toNat (m - k)
    Ch04.expectedResponseJCubeSet P Q p q -
        (1 / 2 : ℝ) * vecDot p0 q0 ≤
      JUpperBoundWeakNorms.jUpperWeakNormManuscriptExpectedRHSAtScale P m k s t
        (1 + JUpperBoundWeakNorms.section53CutoffBound Q)
        (JUpperBoundWeakNorms.section53CutoffOscillationConstant Q)
        (JUpperBoundWeakNorms.section53CutoffScaleSep Q j)
        (JUpperBoundWeakNorms.section53CutoffDualBound Q s)
        (JUpperBoundWeakNorms.section53CutoffDualBound Q t)
        (JUpperBoundWeakNorms.section53CutoffProductCoeff Q s t)
        p q p0 q0 := by
  exact
    JUpperBoundWeakNorms.expectedResponseJCubeSet_sub_half_dot_le_jUpperWeakNormManuscriptExpectedRHSAtScale_of_normalizedCutoff_of_P4
      hP hstat hStruct hP4 hk_nonneg hkm hs hs_lt_one ht hst p q p0 q0
      hGradSq hFluxSq

/-- First Section 5.3 lemma with the additivity term treated by Young rather
than by Cauchy in probability.  This is the surface used by the flatness-rules
route: the RHS contains `eta * E[J_k] + eta^{-1} * tau_{m,k}` instead of
`sqrt(tau_{m,k}) * sqrt(E[J_k])`. -/
theorem JUpperBoundWeakNorms_young_homogenizationScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hstat : Ch04.RestrictionStationaryLaw P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℤ} (hk_nonneg : 0 ≤ k) (hkm : k ≤ m)
    {s t : ℝ} (hs : 0 < s) (hs_lt_one : s < 1) (ht : 0 < t)
    (hst : s + t ≤ 1)
    (p q p0 q0 : Vec d) {η : ℝ} (hη : 0 < η)
    (hGradSq :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.canonicalScalarResponseGradientWeakNormCubeSet
            (originCube d m) s p q p0 a.toFun) ^ 2) P)
    (hFluxSq :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.canonicalScalarResponseFluxWeakNormCubeSet
            (originCube d m) t p q q0 a.toFun) ^ 2) P) :
    let Q : TriadicCube d := originCube d m
    let j : ℕ := Int.toNat (m - k)
    Ch04.expectedResponseJCubeSet P Q p q -
        (1 / 2 : ℝ) * vecDot p0 q0 ≤
      JUpperBoundWeakNorms.jUpperWeakNormYoungManuscriptExpectedRHSAtScale P m k s t
        (1 + JUpperBoundWeakNorms.section53CutoffBound Q)
        (JUpperBoundWeakNorms.section53CutoffOscillationConstant Q)
        (JUpperBoundWeakNorms.section53CutoffScaleSep Q j)
        (JUpperBoundWeakNorms.section53CutoffDualBound Q s)
        (JUpperBoundWeakNorms.section53CutoffDualBound Q t)
        (JUpperBoundWeakNorms.section53CutoffProductCoeff Q s t)
        η p q p0 q0 := by
  exact
    JUpperBoundWeakNorms.expectedResponseJCubeSet_sub_half_dot_le_jUpperWeakNormYoungManuscriptExpectedRHSAtScale_of_normalizedCutoff_of_P4
      hP hstat hStruct hP4 hk_nonneg hkm hs hs_lt_one ht hst p q p0 q0 hη
      hGradSq hFluxSq

end

end Section53
end Ch05
end Book
end Homogenization
