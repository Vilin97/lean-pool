/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Definitions
import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.ExactOverlapEuclideanRegularity
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CenteredCubeCalderonZygmundQTwo
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.FullNormEquivalence

/-!
# Exact Chapter 1 classical inputs

This additive public surface exposes the repaired centered-cube
Calderón--Zygmund endpoint only at the formalized `q = 2` exponent, together
with the literal continuous `K`-functional kernel and its approved additive
full-norm equivalence with the exact fractional Sobolev carrier.  It does not
replace the older discrete/legacy Chapter 1 facade.
-/

namespace Homogenization
namespace Book
namespace Ch01

open scoped ENNReal

noncomputable section

/-- The exact centered-cube classical `q = 2` Calderón--Zygmund statement.
One constant is shared by the normalized-Frobenius Dirichlet branch and the
internally centered Neumann branch.  In both branches a weak-Hessian witness
is a supplied `W^{2,2}` hypothesis, and the conclusion estimates that same
witness. -/
abbrev CenteredCubeCalderonZygmundQTwo (d : ℕ) (C : ℝ) : Prop :=
  Homogenization.CenteredCubeCalderonZygmundQTwo d C

/-- The explicit common dimension-only constant for the exact centered-cube
classical `q = 2` branches. -/
noncomputable abbrev centeredCubeCalderonZygmundQTwoConstant
    (d : ℕ) [NeZero d] : ℝ :=
  Homogenization.centeredCubeCalderonZygmundQTwoConstant d

theorem centeredCubeCalderonZygmundQTwoConstant_nonneg
    (d : ℕ) [NeZero d] :
    0 ≤ centeredCubeCalderonZygmundQTwoConstant d :=
  Homogenization.centeredCubeCalderonZygmundQTwoConstant_nonneg d

/-- The exact common centered-cube `q = 2` Calderón--Zygmund theorem.  The
common constant precedes every scale, forcing, solution, and weak-Hessian
binder in the underlying predicate. -/
theorem centeredCubeCalderonZygmundQTwo_exact
    (d : ℕ) [NeZero d] :
    CenteredCubeCalderonZygmundQTwo d (centeredCubeCalderonZygmundQTwoConstant d) :=
  Homogenization.centeredCubeCalderonZygmundQTwo_exact d

/-- Existential form of the exact common centered-cube `q = 2`
Calderón--Zygmund theorem. -/
theorem exists_centeredCubeCalderonZygmundQTwo
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, CenteredCubeCalderonZygmundQTwo d C :=
  Homogenization.exists_centeredCubeCalderonZygmundQTwo d

/-- Exact Euclidean `L²` datum carrier for the continuous Chapter 1
`K`-functional on the unit centered cube. -/
abbrev UnitCubeEuclideanL2Field (d : ℕ) : Type :=
  Homogenization.UnitCubeEuclideanL2Field d

/-- The exact source fractional-order carrier `0 < s < 1`, shared by the
continuous `K` and Euclidean fractional `H^s` kernels. -/
abbrev FractionalOrder : Type := Homogenization.FractionalOrder

/-- Exact source scale carrier `0 < t ≤ 1` for the continuous Chapter 1
`K`-functional. -/
abbrev ContinuousKScale : Type := Homogenization.ContinuousKScale

/-- Exact coordinatewise-weak-`H¹` competitor carrier for the continuous
Chapter 1 `K`-functional. -/
abbrev ContinuousKCompetitor (d : ℕ) : Type :=
  Homogenization.ContinuousKCompetitor d

/-- The literal continuous real-interpolation `K(t,F)` functional on the
unit centered cube.  This is deliberately distinct from the legacy discrete
cube `K`-functional API. -/
noncomputable abbrev continuousKFunctional {d : ℕ}
    (t : ContinuousKScale) (F : UnitCubeEuclideanL2Field d) : ℝ :=
  Homogenization.continuousKFunctional t F

/-- The exact ENNReal-valued continuous interpolation seminorm built from
`t^(-2s) K(t,F)^2 dt / t`. -/
noncomputable abbrev continuousKSeminorm {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) : ℝ≥0∞ :=
  Homogenization.continuousKSeminorm s F

/-- The public continuous `K`-functional keeps its literal infimum-over-
weak-`H¹`-competitors characterization. -/
theorem continuousKFunctional_eq_sInf {d : ℕ}
    (t : ContinuousKScale) (F : UnitCubeEuclideanL2Field d) :
    continuousKFunctional t F =
      sInf (Set.range fun G : ContinuousKCompetitor d =>
        Homogenization.continuousKFunctionalCompetitorValue t F G) :=
  Homogenization.continuousKFunctional_eq_sInf t F

/-- The public continuous `K` seminorm keeps its exact continuum-lintegral
characterization. -/
theorem continuousKSeminorm_eq_lintegral {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    continuousKSeminorm s F =
      (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        Homogenization.continuousKSeminormIntegrand s.1 F t) ^ (1 / 2 : ℝ) :=
  Homogenization.continuousKSeminorm_eq_lintegral s F

/-- Membership in the exact Euclidean fractional `H^s` carrier on the unit
centered cube. -/
abbrev MemEuclideanHs {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) : Prop :=
  Homogenization.MemEuclideanHs s F

/-- The exact extended Euclidean fractional `H^s` seminorm on the unit
centered cube.  It uses the source's normalized-first-variable double
integral. -/
noncomputable abbrev euclideanHsESeminorm {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) : ℝ≥0∞ :=
  Homogenization.euclideanHsESeminorm s F

/-- Literal double-lintegral characterization of the exact Euclidean
fractional `H^s` seminorm. -/
theorem euclideanHsESeminorm_eq_lintegral {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    euclideanHsESeminorm s F =
      (∫⁻ z, ENNReal.ofReal
        (‖HilbertVec.ofVec (F z.1 - F z.2)‖ ^ 2 /
          Real.rpow (euclideanDist z.1 z.2) ((d : ℝ) + 2 * s.1))
        ∂Homogenization.euclideanHsProductMeasure d) ^ ((2 : ℝ)⁻¹) :=
  Homogenization.euclideanHsESeminorm_eq_lintegral s F

/-- The approved source-facing full norm: normalized Euclidean `L²` plus the
literal continuous interpolation seminorm. -/
noncomputable abbrev continuousKFullENorm {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) : ℝ≥0∞ :=
  Homogenization.continuousKFullENorm s F

/-- The approved source-facing full norm: normalized Euclidean `L²` plus the
exact Euclidean fractional `H^s` seminorm. -/
noncomputable abbrev euclideanHsFullENorm {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) : ℝ≥0∞ :=
  Homogenization.euclideanHsFullENorm s F

/-- Evaluation formula for the approved continuous interpolation full norm. -/
theorem continuousKFullENorm_eq {d : ℕ} (s : FractionalOrder)
    (F : UnitCubeEuclideanL2Field d) :
    continuousKFullENorm s F =
      (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F +
        continuousKSeminorm s F :=
  Homogenization.continuousKFullENorm_eq s F

/-- Evaluation formula for the approved exact Euclidean fractional full norm. -/
theorem euclideanHsFullENorm_eq {d : ℕ} (s : FractionalOrder)
    (F : UnitCubeEuclideanL2Field d) :
    euclideanHsFullENorm s F =
      (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F +
        euclideanHsESeminorm s F :=
  Homogenization.euclideanHsFullENorm_eq s F

/-- The explicit finite common constant for both approved full-norm
comparisons. -/
noncomputable abbrev continuousKEuclideanHsFullENormConstant
    (s : FractionalOrder) (d : ℕ) : ℝ≥0∞ :=
  Homogenization.continuousKEuclideanHsFullENormConstant s d

/-- The explicit common full-norm comparison constant is finite. -/
theorem continuousKEuclideanHsFullENormConstant_lt_top
    (s : FractionalOrder) (d : ℕ) :
    continuousKEuclideanHsFullENormConstant s d < ∞ :=
  Homogenization.continuousKEuclideanHsFullENormConstant_lt_top s d

/-- The approved continuous interpolation full norm controls the exact
Euclidean fractional full norm with the common finite constant. -/
theorem euclideanHsFullENorm_le_mul_continuousKFullENorm {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    euclideanHsFullENorm s F ≤
      continuousKEuclideanHsFullENormConstant s d * continuousKFullENorm s F :=
  Homogenization.euclideanHsFullENorm_le_mul_continuousKFullENorm s F

/-- The exact Euclidean fractional full norm controls the approved continuous
interpolation full norm with the same common finite constant. -/
theorem continuousKFullENorm_le_mul_euclideanHsFullENorm {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    continuousKFullENorm s F ≤
      continuousKEuclideanHsFullENormConstant s d * euclideanHsFullENorm s F :=
  Homogenization.continuousKFullENorm_le_mul_euclideanHsFullENorm s F

/-- Exact membership characterization by finiteness of the literal continuous
interpolation seminorm. -/
theorem memEuclideanHs_iff_continuousKSeminorm_lt_top {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    MemEuclideanHs s F ↔ continuousKSeminorm s F < ∞ :=
  Homogenization.memEuclideanHs_iff_continuousKSeminorm_lt_top s F

/-- Exact Chapter 1 root theorem for the approved additive full-norm
equivalence. -/
theorem exists_continuousKFullENorm_euclideanHsFullENorm_equivalence
    (d : ℕ) (s : FractionalOrder) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ F : UnitCubeEuclideanL2Field d,
      (MemEuclideanHs s F ↔ continuousKSeminorm s F < ∞) ∧
        euclideanHsFullENorm s F ≤ C * continuousKFullENorm s F ∧
          continuousKFullENorm s F ≤ C * euclideanHsFullENorm s F :=
  Homogenization.exists_continuousKFullENorm_euclideanHsFullENorm_equivalence d s

/-! ## Exact centered-cube Dirichlet overlap regularity -/

/-- Exact Euclidean `L²` datum carrier on the centered triadic cube at scale
`m`. -/
abbrev CenteredCubeEuclideanL2Field (d : ℕ) (m : ℤ) : Type :=
  Homogenization.CenteredCubeEuclideanL2Field d m

/-- Membership in the literal physical centered-cube Euclidean fractional
`H^s` carrier. -/
abbrev MemCenteredCubeEuclideanHs {d : ℕ} {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m) : Prop :=
  Homogenization.MemCenteredCubeEuclideanHs s F

/-- The literal squared Euclidean fractional energy on a centered cube. -/
noncomputable abbrev centeredCubeEuclideanHsEnergy {d : ℕ} {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m) : ℝ≥0∞ :=
  Homogenization.centeredCubeEuclideanHsEnergy s F

/-- Literal double-lintegral characterization of the centered-cube Euclidean
fractional energy. -/
theorem centeredCubeEuclideanHsEnergy_eq_lintegral {d : ℕ} {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m) :
    centeredCubeEuclideanHsEnergy s F =
      (∫⁻ z, ENNReal.ofReal
        (‖HilbertVec.ofVec (F z.1 - F z.2)‖ ^ 2 /
          Real.rpow (euclideanDist z.1 z.2) ((d : ℝ) + 2 * s.1))
        ∂Homogenization.centeredCubeEuclideanHsProductMeasure d m) :=
  Homogenization.centeredCubeEuclideanHsEnergy_eq_lintegral s F

/-- Centered-cube Euclidean fractional membership is exactly finiteness of
the literal physical energy. -/
theorem memCenteredCubeEuclideanHs_iff_energy_lt_top {d : ℕ} {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m) :
    MemCenteredCubeEuclideanHs s F ↔ centeredCubeEuclideanHsEnergy s F < ∞ :=
  Homogenization.memCenteredCubeEuclideanHs_iff_energy_lt_top s F

/-- Coordinatewise integrability certificates for the exact Euclidean
overlap norm on a triadic cube. -/
abbrev ExactOverlapEuclideanIntegrable {d : ℕ} (Q : Cube d)
    (F : Vec d → Vec d) : Prop :=
  Homogenization.ExactOverlapEuclideanIntegrable Q F

/-- The canonical exact-overlap integrability certificate carried by a
centered-cube Euclidean `L²` field. -/
theorem centeredCubeEuclideanL2Field_exactOverlapEuclideanIntegrable
    {d : ℕ} {m : ℤ} (F : CenteredCubeEuclideanL2Field d m) :
    ExactOverlapEuclideanIntegrable (originCube d m) F :=
  Homogenization.CenteredCubeEuclideanL2Field.exactOverlapEuclideanIntegrable F

/-- Euclidean magnitude of the exact-overlap coordinate root means. -/
noncomputable abbrev exactOverlapEuclideanRootMeanENorm {d : ℕ} (Q : Cube d)
    (F : Vec d → Vec d) (hF : ExactOverlapEuclideanIntegrable Q F) : ℝ≥0∞ :=
  Homogenization.exactOverlapEuclideanRootMeanENorm Q F hF

/-- Exact Euclidean `p = q = 2` overlap seminorm on a triadic cube. -/
noncomputable abbrev exactOverlapEuclideanSeminormTwo {d : ℕ}
    (s : FractionalOrder) (Q : Cube d) (F : Vec d → Vec d)
    (hF : ExactOverlapEuclideanIntegrable Q F) : ℝ≥0∞ :=
  Homogenization.exactOverlapEuclideanSeminormTwo s Q F hF

/-- Exact source-facing Euclidean overlap full norm at `p = q = 2`. -/
noncomputable abbrev exactOverlapEuclideanNormTwo {d : ℕ}
    (s : FractionalOrder) (Q : Cube d) (F : Vec d → Vec d)
    (hF : ExactOverlapEuclideanIntegrable Q F) : ℝ≥0∞ :=
  Homogenization.exactOverlapEuclideanNormTwo s Q F hF

/-- Evaluation formula for the Euclidean magnitude of exact-overlap root
means. -/
theorem exactOverlapEuclideanRootMeanENorm_eq {d : ℕ} (Q : Cube d)
    (F : Vec d → Vec d) (hF : ExactOverlapEuclideanIntegrable Q F) :
    exactOverlapEuclideanRootMeanENorm Q F hF =
      (∑ i : Fin d,
        (ENNReal.ofReal |Homogenization.exactOverlapRootMean Q (fun x => F x i)
          (hF.coordinate i).root|) ^ 2) ^ ((2 : ℝ)⁻¹) :=
  Homogenization.exactOverlapEuclideanRootMeanENorm_eq Q F hF

/-- Evaluation formula for the exact Euclidean overlap seminorm. -/
theorem exactOverlapEuclideanSeminormTwo_eq {d : ℕ}
    (s : FractionalOrder) (Q : Cube d) (F : Vec d → Vec d)
    (hF : ExactOverlapEuclideanIntegrable Q F) :
    exactOverlapEuclideanSeminormTwo s Q F hF =
      (∑ i : Fin d,
        (Homogenization.exactOverlapFiniteSeminorm
          (Homogenization.exactOverlapTwoParameters s) Q
          (fun x => F x i) (hF.coordinate i)) ^ 2) ^ ((2 : ℝ)⁻¹) :=
  Homogenization.exactOverlapEuclideanSeminormTwo_eq s Q F hF

/-- Evaluation formula for the exact source-facing Euclidean overlap full
norm. -/
theorem exactOverlapEuclideanNormTwo_eq {d : ℕ}
    (s : FractionalOrder) (Q : Cube d) (F : Vec d → Vec d)
    (hF : ExactOverlapEuclideanIntegrable Q F) :
    exactOverlapEuclideanNormTwo s Q F hF =
      exactOverlapEuclideanSeminormTwo s Q F hF +
        Homogenization.exactOverlapRootWeight Q s.1 *
          exactOverlapEuclideanRootMeanENorm Q F hF :=
  Homogenization.exactOverlapEuclideanNormTwo_eq s Q F hF

/-- The gradient of a centered-cube zero-trace function, packaged as an exact
Euclidean `L²` field. -/
noncomputable abbrev centeredCubeGradientEuclideanL2Field {d : ℕ} {m : ℤ}
    (w : H10Function (openCubeSet (originCube d m))) :
    CenteredCubeEuclideanL2Field d m :=
  Homogenization.centeredCubeGradientEuclideanL2Field w

/-- Pointwise evaluation of the centered-cube gradient field. -/
theorem centeredCubeGradientEuclideanL2Field_apply {d : ℕ} {m : ℤ}
    (w : H10Function (openCubeSet (originCube d m))) (x : Vec d) :
    centeredCubeGradientEuclideanL2Field w x = w.toH1Function.grad x :=
  Homogenization.centeredCubeGradientEuclideanL2Field_apply w x

/-- Weak zero-trace formulation of the centered-cube Dirichlet divergence
problem. -/
abbrev CubeDirichletDivergenceProblem {d : ℕ} (Q : Cube d)
    (w : H10Function (openCubeSet Q)) (h : Vec d → Vec d) : Prop :=
  Homogenization.CubeDirichletDivergenceProblem Q w h

/-- Literal weak-form characterization of the centered-cube Dirichlet
divergence problem. -/
theorem cubeDirichletDivergenceProblem_iff {d : ℕ} (Q : Cube d)
    (w : H10Function (openCubeSet Q)) (h : Vec d → Vec d) :
    CubeDirichletDivergenceProblem Q w h ↔
      ∀ φ : H10Function (openCubeSet Q),
        ∫ x in openCubeSet Q,
            vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x)
              ∂MeasureTheory.volume =
          -∫ x in openCubeSet Q,
            vecDot (h x) (φ.toH1Function.grad x) ∂MeasureTheory.volume :=
  Iff.rfl

/-- Exact centered-cube Dirichlet regularity in the source-facing Euclidean
overlap norm.  One finite constant is chosen before the scale, datum, and
solution. -/
theorem exists_centeredCubeDirichletExactOverlapEuclideanNormTwoRegularity
    (d : ℕ) [NeZero d] (s : FractionalOrder) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m : ℤ) (h : CenteredCubeEuclideanL2Field d m)
        (w : H10Function (openCubeSet (originCube d m))),
        MemCenteredCubeEuclideanHs s h →
          CubeDirichletDivergenceProblem (originCube d m) w h →
            exactOverlapEuclideanNormTwo s (originCube d m)
                (centeredCubeGradientEuclideanL2Field w)
                (centeredCubeGradientEuclideanL2Field w).exactOverlapEuclideanIntegrable ≤
              C * exactOverlapEuclideanNormTwo s (originCube d m) h
                h.exactOverlapEuclideanIntegrable :=
  Homogenization.exists_centeredCubeDirichletExactOverlapEuclideanNormTwoRegularity d s

end

end Ch01
end Book
end Homogenization
