/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite.Definitions

/-! # Definitions -/


open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate Topology

noncomputable section

namespace Hermite1DimdLEAN

/-- `CSpace`: C Space. -/
abbrev CSpace (d : ℕ) := Fin d → ℂ
/-- `MultiIndex`: Multi Index. -/
abbrev MultiIndex (d : ℕ) := Fin d → ℕ
/-- `T`: T. -/
abbrev T : ℝ := HermiteLEAN.T

lemma T_pos : 0 < T := HermiteLEAN.T_pos

instance : Fact (0 < T) := ⟨T_pos⟩

/-- `Circle`: Circle. -/
abbrev Circle := AddCircle T

/-- `gaussianDensity`: gaussian Density. -/
def gaussianDensity (d : ℕ) (z : CSpace d) : ℝ :=
  (1 / Real.pi ^ d) * Real.exp (-(∑ q : Fin d, ‖z q‖ ^ 2))

/-- `gaussianMeasure`: gaussian Measure. -/
def gaussianMeasure (d : ℕ) : Measure (CSpace d) :=
  volume.withDensity fun z => ENNReal.ofReal (gaussianDensity d z)

/-- `oneDimPhi`: one Dim Phi. -/
noncomputable def oneDimPhi (k n : ℕ) : ℂ → ℂ := fun z =>
  ((1 / Real.sqrt ((Nat.factorial k : ℝ) * (Nat.factorial n : ℝ))) : ℂ) *
    Finset.sum (Finset.range (min k n + 1)) (fun j =>
      ((-1 : ℂ) ^ j) * (Nat.choose k j : ℂ) *
        ((Nat.factorial n : ℂ) / (Nat.factorial (n - j) : ℂ)) *
        z ^ (n - j) * (star z) ^ (k - j))

/-- `PhiKappaAlpha`: Phi Kappa Alpha. -/
def PhiKappaAlpha {d : ℕ} (κ α : MultiIndex d) : CSpace d → ℂ :=
  fun z => ∏ q : Fin d, oneDimPhi (κ q) (α q) (z q)

/-- `nuKappa`: nu Kappa. -/
def nuKappa {d : ℕ} (κ : MultiIndex d) : CSpace d → ℂ :=
  PhiKappaAlpha κ 0

/-- `rho`: rho. -/
def rho (a u : ℂ) : ℝ := |‖a + u‖ - ‖a‖|

/-- `gaussianL2NormSq`: gaussian L2 Norm Sq. -/
def gaussianL2NormSq {d : ℕ} {α : Type*} [Norm α] (F : CSpace d → α) : ℝ :=
  ∫ z, ‖F z‖ ^ 2 ∂ gaussianMeasure d

/-- `gaussianL2Norm`: gaussian L2 Norm. -/
def gaussianL2Norm {d : ℕ} {α : Type*} [Norm α] (F : CSpace d → α) : ℝ :=
  Real.sqrt (gaussianL2NormSq F)

/-- `gaussianInner`: gaussian Inner. -/
def gaussianInner {d : ℕ} (F G : CSpace d → ℂ) : ℂ :=
  ∫ z, F z * conj (G z) ∂ gaussianMeasure d

/-- `circleL2NormSq`: circle L2 Norm Sq. -/
def circleL2NormSq {α : Type*} [Norm α] (F : Circle → α) : ℝ :=
  ∫ t, ‖F t‖ ^ 2 ∂ AddCircle.haarAddCircle

/-- `circleL2Norm`: circle L2 Norm. -/
def circleL2Norm {α : Type*} [Norm α] (F : Circle → α) : ℝ :=
  Real.sqrt (circleL2NormSq F)

/-- `FiniteHermiteSum`: Finite Hermite Sum. -/
structure FiniteHermiteSum (d : ℕ) where
  /-- `coeff`: coeff. -/
  coeff : MultiIndex d →₀ ℂ

namespace FiniteHermiteSum

/-- `support`: support. -/
def support {d : ℕ} (G : FiniteHermiteSum d) : Finset (MultiIndex d) :=
  G.coeff.support

end FiniteHermiteSum

/-- `evalHermiteSum`: eval Hermite Sum. -/
def evalHermiteSum {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) : CSpace d → ℂ :=
  fun z => Finset.sum G.support fun α => G.coeff α * PhiKappaAlpha κ α z

/-- `hermiteInner`: hermite Inner. -/
def hermiteInner {d : ℕ} (κ : MultiIndex d) (G H : FiniteHermiteSum d) : ℂ :=
  gaussianInner (evalHermiteSum κ G) (evalHermiteSum κ H)

/-- `hermiteInnerNu`: hermite Inner Nu. -/
def hermiteInnerNu {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) : ℂ :=
  gaussianInner (evalHermiteSum κ G) (nuKappa κ)

/-- `hermiteNormSq`: hermite Norm Sq. -/
def hermiteNormSq {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) : ℝ :=
  gaussianL2NormSq (evalHermiteSum κ G)

/-- `hermiteNorm`: hermite Norm. -/
def hermiteNorm {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) : ℝ :=
  gaussianL2Norm (evalHermiteSum κ G)

/-- `defectFunction`: defect Function. -/
def defectFunction {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) : CSpace d → ℝ :=
  fun z => rho (nuKappa κ z) (evalHermiteSum κ G z)

/-- `defectNormSq`: defect Norm Sq. -/
def defectNormSq {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) : ℝ :=
  gaussianL2NormSq (defectFunction κ G)

/-- `defectNorm`: defect Norm. -/
def defectNorm {d : ℕ} (κ : MultiIndex d) (G : FiniteHermiteSum d) : ℝ :=
  gaussianL2Norm (defectFunction κ G)

/-- `totalDegree`: total Degree. -/
def totalDegree {d : ℕ} (α : MultiIndex d) : ℕ :=
  ∑ q : Fin d, α q

/-- `blockIndexMulti`: block Index Multi. -/
def blockIndexMulti {d : ℕ} (α : MultiIndex d) : MultiIndex d :=
  fun q => HermiteLEAN.blockIndex (α q)

/-- `totalDegreePiece`: total Degree Piece. -/
def totalDegreePiece {d : ℕ} (n : ℕ) (G : FiniteHermiteSum d) : FiniteHermiteSum d := by
  classical
  refine ⟨Finsupp.onFinset (G.support.filter fun α => totalDegree α = n)
    (fun α => if totalDegree α = n then G.coeff α else 0) ?_⟩
  intro α hα
  have hdeg : totalDegree α = n := by
    by_contra hne
    simp [hne] at hα
  have hsupp : α ∈ G.support := Finsupp.mem_support_iff.mpr (by simpa [hdeg] using hα)
  exact Finset.mem_filter.mpr ⟨hsupp, hdeg⟩

/-- `productAnnulus`: product Annulus. -/
def productAnnulus {d : ℕ} (j : MultiIndex d) : Set (CSpace d) :=
  { z | ∀ q, (j q : ℝ) ≤ ‖z q‖ ∧ ‖z q‖ < (j q : ℝ) + 1 }

/-- `indicatorMul`: the indicator of `s` times `f`, valued in `ℂ`. -/
def indicatorMul {α : Type*} (s : Set α) (f : α → ℂ) : α → ℂ :=
  by
    classical
    exact fun x => if x ∈ s then f x else 0

/-- `annulusInner`: annulus Inner. -/
def annulusInner {d : ℕ} (j : MultiIndex d) (F G : CSpace d → ℂ) : ℂ :=
  by
    classical
    exact ∫ z, if z ∈ productAnnulus j then F z * conj (G z) else 0 ∂ gaussianMeasure d

/-- `annulusMass`: annulus Mass. -/
def annulusMass {d : ℕ} (j : MultiIndex d) (F : CSpace d → ℂ) : ℝ :=
  by
    classical
    exact ∫ z, if z ∈ productAnnulus j then ‖F z‖ ^ 2 else 0 ∂ gaussianMeasure d

/-- `defectAnnulusMass`: defect Annulus Mass. -/
def defectAnnulusMass {d : ℕ} (κ : MultiIndex d) (j : MultiIndex d)
    (F : CSpace d → ℂ) : ℝ :=
  by
    classical
    exact
      ∫ z, if z ∈ productAnnulus j then rho (nuKappa κ z) (F z) ^ 2 else 0
        ∂ gaussianMeasure d

/-- `squareBlock`: square Block. -/
def squareBlock {d : ℕ} (ℓ : MultiIndex d) : Set (MultiIndex d) :=
  { α | ∀ q, α q ∈ HermiteLEAN.squareBlock (ℓ q) }

/-- `blockDistance`: block Distance. -/
def blockDistance {d : ℕ} (j ℓ : MultiIndex d) : ℕ :=
  (Finset.univ : Finset (Fin d)).sup fun q => Nat.dist (j q) (ℓ q)

/-- `blockPart`: block Part. -/
def blockPart {d : ℕ} (ℓ : MultiIndex d) (G : FiniteHermiteSum d) : FiniteHermiteSum d := by
  classical
  refine ⟨Finsupp.onFinset (G.support.filter fun α => α ∈ squareBlock ℓ)
    (fun α => if α ∈ squareBlock ℓ then G.coeff α else 0) ?_⟩
  intro α hα
  have hblock : α ∈ squareBlock ℓ := by
    by_contra hne
    simp [hne] at hα
  have hsupp : α ∈ G.support := Finsupp.mem_support_iff.mpr (by simpa [hblock] using hα)
  exact Finset.mem_filter.mpr ⟨hsupp, hblock⟩

/-- `localCoeffSet`: local Coeff Set. -/
def localCoeffSet {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    Finset (MultiIndex d) :=
  G.support.filter fun α => blockDistance j (blockIndexMulti α) ≤ M

/-- `farCoeffSet`: far Coeff Set. -/
def farCoeffSet {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    Finset (MultiIndex d) :=
  G.support.filter fun α => M < blockDistance j (blockIndexMulti α)

/-- `localPart`: local Part. -/
def localPart {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    FiniteHermiteSum d := by
  classical
  refine ⟨Finsupp.onFinset (localCoeffSet j M G)
    (fun α => if blockDistance j (blockIndexMulti α) ≤ M then G.coeff α else 0) ?_⟩
  intro α hα
  have hlocal : blockDistance j (blockIndexMulti α) ≤ M := by
    by_contra hne
    simp [hne] at hα
  have hsupp : α ∈ G.support := Finsupp.mem_support_iff.mpr (by simpa [hlocal] using hα)
  exact Finset.mem_filter.mpr ⟨hsupp, hlocal⟩

/-- `remainderPart`: remainder Part. -/
def remainderPart {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) :
    FiniteHermiteSum d := by
  classical
  refine ⟨Finsupp.onFinset (farCoeffSet j M G)
    (fun α => if M < blockDistance j (blockIndexMulti α) then G.coeff α else 0) ?_⟩
  intro α hα
  have hfar : M < blockDistance j (blockIndexMulti α) := by
    by_contra hne
    simp [hne] at hα
  have hsupp : α ∈ G.support := Finsupp.mem_support_iff.mpr (by simpa [hfar] using hα)
  exact Finset.mem_filter.mpr ⟨hsupp, hfar⟩

/-- `localDegreeSet`: local Degree Set. -/
def localDegreeSet {d : ℕ} (j : MultiIndex d) (M : ℕ) (G : FiniteHermiteSum d) : Finset ℕ :=
  (localCoeffSet j M G).image totalDegree

/-- `localDegreePiece`: local Degree Piece. -/
def localDegreePiece {d : ℕ} (j : MultiIndex d) (M n : ℕ) (G : FiniteHermiteSum d) :
    FiniteHermiteSum d :=
  totalDegreePiece n (localPart j M G)

/-- `degreeIntervalLower`: degree Interval Lower. -/
def degreeIntervalLower {d : ℕ} (j : MultiIndex d) (M : ℕ) : ℕ :=
  ∑ q, (max (j q) M - M) ^ 2

/-- `degreeIntervalUpper`: degree Interval Upper. -/
def degreeIntervalUpper {d : ℕ} (j : MultiIndex d) (M : ℕ) : ℕ :=
  ∑ q, ((j q + M + 1) ^ 2 - 1)

/-- `degreeWidth`: degree Width. -/
def degreeWidth {d : ℕ} (j : MultiIndex d) (M : ℕ) : ℕ :=
  degreeIntervalUpper j M - degreeIntervalLower j M + 1

/-- `annulusRadius`: annulus Radius. -/
def annulusRadius {d : ℕ} (j : MultiIndex d) : ℕ :=
  (Finset.univ : Finset (Fin d)).sup fun q => j q

/-- `degreeThreshold`: degree Threshold. -/
def degreeThreshold (d M : ℕ) : ℕ := M + 120 * d * (2 * M + 1)

/-- `productAnnulusConstant`: product Annulus Constant. -/
def productAnnulusConstant (d M : ℕ) : ℝ :=
  12 * Real.sqrt d * ((degreeThreshold d M + M : ℕ) : ℝ)

/-- `productAnnulusConstantSq`: product Annulus Constant Sq. -/
def productAnnulusConstantSq (d M : ℕ) : ℝ :=
  144 * d * ((degreeThreshold d M + M : ℕ) : ℝ) ^ 2

/-- `prodLocalizationConstant`: prod Localization Constant. -/
def prodLocalizationConstant {d : ℕ} (κ : MultiIndex d) : ℝ :=
  ∏ q : Fin d, ((κ q + 1 : ℕ) : ℝ)

/-- `prodLocalizationDecay`: prod Localization Decay. -/
def prodLocalizationDecay {d : ℕ} (κ : MultiIndex d) : ℝ :=
  (∏ q : Fin d, ((κ q + 1 : ℕ) : ℝ))⁻¹

/-- `prodLocalizationShift`: prod Localization Shift. -/
def prodLocalizationShift {d : ℕ} (κ : MultiIndex d) : ℝ :=
  ∑ q : Fin d, ((κ q + 4 : ℕ) : ℝ)

/-- `shellCardinality`: shell Cardinality. -/
def shellCardinality (d r : ℕ) : ℕ :=
  (2 * r + 1) ^ d - (2 * r - 1) ^ d

/-- `localizationLeakageCoefficient`: localization Leakage Coefficient. -/
def localizationLeakageCoefficient (C c B : ℝ) (d M : ℕ) : ℝ :=
  C *
    ∑' r : ℕ,
      if M + 1 ≤ r then
        (shellCardinality d r : ℝ) *
          Real.exp
            (-(c) *
              max ((r : ℝ) - B) 0 ^ 2)
      else 0

/-- `leakageCoefficient`: leakage Coefficient. -/
def leakageCoefficient {d : ℕ} (κ : MultiIndex d) (M : ℕ) : ℝ :=
  prodLocalizationConstant κ *
    ∑' r : ℕ,
      if M + 1 ≤ r then
        (shellCardinality d r : ℝ) *
          Real.exp
            (-(prodLocalizationDecay κ) *
              max ((r : ℝ) - prodLocalizationShift κ) 0 ^ 2)
      else 0

/-- `absorptionPredicate`: absorption Predicate. -/
def absorptionPredicate {d : ℕ} (κ : MultiIndex d) (M : ℕ) : Prop :=
  (4 * productAnnulusConstantSq d M + 2) * leakageCoefficient κ M < 1 / 2

/-- `coercivityConstant`: coercivity Constant. -/
def coercivityConstant {d : ℕ} (κ : MultiIndex d) (M : ℕ) : ℝ :=
  2 * productAnnulusConstant d M /
    Real.sqrt (1 - (4 * productAnnulusConstantSq d M + 2) * leakageCoefficient κ M)

/-- `reductionDelta`: reduction Delta. -/
def reductionDelta (M : ℝ) : ℝ := 1 / (M + 1)
/-- `reductionMtilde`: reduction Mtilde. -/
def reductionMtilde (M : ℝ) : ℝ := 5 * M + 3

/-- `phaseAdjustedDifference`: phase Adjusted Difference. -/
def phaseAdjustedDifference {d : ℕ} (κ : MultiIndex d) (w : ℂ) (G : FiniteHermiteSum d) :
    CSpace d → ℂ :=
  fun z => w * (nuKappa κ z + evalHermiteSum κ G z) - nuKappa κ z

/-- `phaseAdjustedNormSq`: phase Adjusted Norm Sq. -/
def phaseAdjustedNormSq {d : ℕ} (κ : MultiIndex d) (w : ℂ) (G : FiniteHermiteSum d) : ℝ :=
  gaussianL2NormSq (phaseAdjustedDifference κ w G)

/-- `phaseAdjustedNorm`: phase Adjusted Norm. -/
def phaseAdjustedNorm {d : ℕ} (κ : MultiIndex d) (w : ℂ) (G : FiniteHermiteSum d) : ℝ :=
  gaussianL2Norm (phaseAdjustedDifference κ w G)

/-- `positiveFrequencyPolynomial`: positive Frequency Polynomial. -/
def positiveFrequencyPolynomial (E : Finset ℕ) (b : ℕ → ℂ) : Circle → ℂ :=
  fun t => Finset.sum E fun n => b n * fourier (n : ℤ) t

/-- `bandLimitedPolynomial`: band Limited Polynomial. -/
def bandLimitedPolynomial (N L : ℕ) (c : Fin L → ℂ) : Circle → ℂ :=
  fun t => ∑ m : Fin L, c m * fourier ((N + m.1 : ℕ) : ℤ) t

/-- `HasPositiveFrequencySupport`: Has Positive Frequency Support. -/
def HasPositiveFrequencySupport (P : Circle → ℂ) (E : Finset ℕ) : Prop :=
  ∃ b : ℕ → ℂ, P = positiveFrequencyPolynomial E b

/-- `HasBandlimitedSupport`: Has Bandlimited Support. -/
def HasBandlimitedSupport (P : Circle → ℂ) (N L : ℕ) : Prop :=
  ∃ c : Fin L → ℂ, P = bandLimitedPolynomial N L c

end Hermite1DimdLEAN
