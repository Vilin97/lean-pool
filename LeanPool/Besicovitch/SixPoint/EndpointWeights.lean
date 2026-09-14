/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Certificates.EndpointBridge
public import LeanPool.Besicovitch.Certificates.RadicalInterval
public import LeanPool.Besicovitch.SixPoint.WeightedReduction

/-!
# Exact endpoint weights

This file defines the geometric quantities and Cramer weights in the weighted endpoint argument.
Small exact radical certificates prove the numerical inequalities; the stationarity identities are
proved symbolically from Cramer's rule.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

/-- The outer radius `b` in the endpoint configuration. -/
def endpointOuterRadius (c B : ℝ) : ℝ :=
  (2 * B - 3 * c ^ 2 + 2 * c - 1) / (c + 1)

/-- The distance `D` in the endpoint configuration. -/
def endpointSecondDistance (c B : ℝ) : ℝ :=
  4 * c ^ 2 - 2 * c - B

/-- The first auxiliary distance `A` in the endpoint configuration. -/
def endpointFirstAuxiliaryDistance (B : ℝ) : ℝ :=
  Real.sqrt ((B ^ 2 - 1) / 2)

/-- The mixed auxiliary distance `C` in the endpoint configuration. -/
def endpointMixedAuxiliaryDistance (c B : ℝ) : ℝ :=
  Real.sqrt ((B ^ 2 + endpointSecondDistance c B ^ 2) / 2 - c ^ 2)

/-- The unit-circle abscissa `x` in the endpoint configuration. -/
def endpointUnitAbscissa (B : ℝ) : ℝ :=
  (5 - B ^ 2) / 4

/-- The outer-circle abscissa `z` in the endpoint configuration. -/
def endpointOuterAbscissa (c B : ℝ) : ℝ :=
  (1 + 4 * endpointOuterRadius c B ^ 2 - endpointSecondDistance c B ^ 2) / 4

/-- The positive unit-circle ordinate `y` in the endpoint configuration. -/
def endpointUnitOrdinate (B : ℝ) : ℝ :=
  Real.sqrt (1 - endpointUnitAbscissa B ^ 2)

/-- The negative outer-circle ordinate `w` in the endpoint configuration. -/
def endpointOuterOrdinate (c B : ℝ) : ℝ :=
  -Real.sqrt (endpointOuterRadius c B ^ 2 - endpointOuterAbscissa c B ^ 2)

/-- The chord abscissa `k` for the radial endpoint deformation. -/
def endpointChordAbscissa (c B : ℝ) : ℝ :=
  (1 + endpointOuterRadius c B ^ 2 - c ^ 2) / 2

/-- The positive chord ordinate `r` for the radial endpoint deformation. -/
def endpointChordOrdinate (c B : ℝ) : ℝ :=
  Real.sqrt (endpointOuterRadius c B ^ 2 - endpointChordAbscissa c B ^ 2)

/-- The angular rate `rho` that keeps the endpoint chord length fixed. -/
def endpointAngularRate (c B : ℝ) : ℝ :=
  endpointOuterRadius c B * (1 - endpointChordAbscissa c B) /
    endpointChordOrdinate c B

/-- The derivative `z_b` of the outer abscissa along the radial deformation. -/
def endpointOuterAbscissaDerivative (c B : ℝ) : ℝ :=
  endpointOuterRadius c B * endpointUnitAbscissa B -
    endpointAngularRate c B * endpointUnitOrdinate B

/-- The derivative `D_b` of the second distance along the radial deformation. -/
def endpointSecondDistanceDerivative (c B : ℝ) : ℝ :=
  (4 * endpointOuterRadius c B - 2 * endpointOuterAbscissaDerivative c B) /
    endpointSecondDistance c B

/-- The derivative `C_b` of the mixed distance along the radial deformation. -/
def endpointMixedDistanceDerivative (c B : ℝ) : ℝ :=
  (2 * endpointOuterRadius c B - endpointOuterAbscissaDerivative c B) /
    endpointMixedAuxiliaryDistance c B

/-- The constant coefficient in the angular stationarity equation. -/
def endpointBaseAngularCoefficient (c B : ℝ) : ℝ :=
  2 * endpointUnitOrdinate B / B +
    2 * endpointOuterOrdinate c B / endpointSecondDistance c B

/-- The coefficient of `lambda` in the angular stationarity equation. -/
def endpointLambdaAngularCoefficient (B : ℝ) : ℝ :=
  2 * endpointUnitOrdinate B / B

/-- The coefficient of `mu` in the angular stationarity equation. -/
def endpointMuAngularCoefficient (c B : ℝ) : ℝ :=
  endpointUnitOrdinate B / endpointFirstAuxiliaryDistance B +
    (endpointUnitOrdinate B + endpointOuterOrdinate c B) /
      endpointMixedAuxiliaryDistance c B

/-- The coefficient of `lambda` in the radial stationarity equation. -/
def endpointLambdaRadialCoefficient (c : ℝ) : ℝ :=
  -(c + 1) / 2

/-- The coefficient of `mu` in the radial stationarity equation. -/
def endpointMuRadialCoefficient (c B : ℝ) : ℝ :=
  endpointMixedDistanceDerivative c B - 3 * c

/-- The determinant of the two endpoint stationarity equations. -/
def endpointStationarityDeterminant (c B : ℝ) : ℝ :=
  endpointLambdaAngularCoefficient B * endpointMuRadialCoefficient c B -
    endpointMuAngularCoefficient c B * endpointLambdaRadialCoefficient c

/-- Cramer's first weight for the two endpoint stationarity equations. -/
def endpointCramerLambda (c B : ℝ) : ℝ :=
  (-endpointBaseAngularCoefficient c B * endpointMuRadialCoefficient c B +
      endpointMuAngularCoefficient c B * endpointSecondDistanceDerivative c B) /
    endpointStationarityDeterminant c B

/-- Cramer's second weight for the two endpoint stationarity equations. -/
def endpointCramerMu (c B : ℝ) : ℝ :=
  (-endpointLambdaAngularCoefficient B * endpointSecondDistanceDerivative c B +
      endpointBaseAngularCoefficient c B * endpointLambdaRadialCoefficient c) /
    endpointStationarityDeterminant c B

/-- The exact positive multiplier of the second failure slack. -/
def endpointLambda : ℝ :=
  endpointCramerLambda cStar certifiedEndpointPair.2

/-- The exact positive multiplier of the third failure slack. -/
def endpointMu : ℝ :=
  endpointCramerMu cStar certifiedEndpointPair.2

private def endpointInput : Fin 2 → ℝ
  | 0 => cStar
  | 1 => certifiedEndpointPair.2

private def endpointInputBox : Fin 2 → RationalInterval
  | 0 => ⟨13866128436518096 / 10 ^ 16, 13866128436518100 / 10 ^ 16, by norm_num⟩
  | 1 => ⟨2873744161801659 / 10 ^ 15, 2873744161801662 / 10 ^ 15, by norm_num⟩

private theorem endpointInput_mem_box :
    ∀ i, (endpointInputBox i).Contains (endpointInput i) := by
  intro i
  fin_cases i
  · simpa [endpointInputBox, endpointInput, RationalInterval.Contains] using
      ⟨cStar_mem_isolation_box.1.le, cStar_mem_isolation_box.2.le⟩
  · simpa [endpointInputBox, endpointInput, RationalInterval.Contains] using
      ⟨certifiedEndpointPair_second_mem_isolation_box.1.le,
        certifiedEndpointPair_second_mem_isolation_box.2.le⟩

section


private theorem endpointOuterRadius_mem_interval :
    (734358 : ℝ) / 1000000 ≤ endpointOuterRadius cStar certifiedEndpointPair.2 ∧
      endpointOuterRadius cStar certifiedEndpointPair.2 ≤ 734359 / 1000000 := by
  let f : RadicalExpression 2 :=
    .mul
      (.add
        (.add
          (.add (.mul (.constant 2) (.var 1))
            (.neg (.mul (.constant 3) (.mul (.var 0) (.var 0)))))
          (.mul (.constant 2) (.var 0)))
        (.neg (.constant 1)))
      (.inv (.add (.var 0) (.constant 1)))
  let target : RationalInterval := ⟨734358 / 1000000, 734359 / 1000000, by norm_num⟩
  have hf : f.certifiesWithin endpointInputBox target = true := by
    norm_num [f, endpointInputBox, target, RadicalExpression.certifiesWithin,
      RadicalExpression.enclosure, RationalInterval.singleton, RationalInterval.add,
      RationalInterval.neg, RationalInterval.mul, RationalInterval.inv]
  have h := RadicalExpression.certifiesWithin_sound endpointInput_mem_box hf
  simpa [f, endpointInput, target, endpointOuterRadius, RationalInterval.Contains,
    RadicalExpression.eval, div_eq_mul_inv, pow_two, sub_eq_add_neg, add_assoc] using h

private theorem endpointSecondDistance_mem_interval :
    (2043810 : ℝ) / 1000000 ≤ endpointSecondDistance cStar certifiedEndpointPair.2 ∧
      endpointSecondDistance cStar certifiedEndpointPair.2 ≤ 2043811 / 1000000 := by
  let f : RadicalExpression 2 :=
    .add
      (.add (.mul (.constant 4) (.mul (.var 0) (.var 0)))
        (.neg (.mul (.constant 2) (.var 0))))
      (.neg (.var 1))
  let target : RationalInterval := ⟨2043810 / 1000000, 2043811 / 1000000, by norm_num⟩
  have hf : f.certifiesWithin endpointInputBox target = true := by
    norm_num [f, endpointInputBox, target, RadicalExpression.certifiesWithin,
      RadicalExpression.enclosure, RationalInterval.singleton, RationalInterval.add,
      RationalInterval.neg, RationalInterval.mul]
  have h := RadicalExpression.certifiesWithin_sound endpointInput_mem_box hf
  simpa [f, endpointInput, target, endpointSecondDistance, RationalInterval.Contains,
    RadicalExpression.eval, pow_two, sub_eq_add_neg, add_assoc] using h

private theorem endpointFirstAuxiliaryRadicand_mem_interval :
    (3629202 : ℝ) / 1000000 ≤ (certifiedEndpointPair.2 ^ 2 - 1) / 2 ∧
      (certifiedEndpointPair.2 ^ 2 - 1) / 2 ≤ 3629203 / 1000000 := by
  let f : RadicalExpression 1 :=
    .mul (.add (.mul (.var 0) (.var 0)) (.neg (.constant 1))) (.inv (.constant 2))
  let X : Fin 1 → RationalInterval
    | 0 => endpointInputBox 1
  let target : RationalInterval := ⟨3629202 / 1000000, 3629203 / 1000000, by norm_num⟩
  have hX : ∀ i, (X i).Contains (![certifiedEndpointPair.2] i) := by
    intro i
    fin_cases i
    exact endpointInput_mem_box 1
  have hf : f.certifiesWithin X target = true := by
    norm_num [f, X, endpointInputBox, target, RadicalExpression.certifiesWithin,
      RadicalExpression.enclosure, RationalInterval.singleton, RationalInterval.add,
      RationalInterval.neg, RationalInterval.mul, RationalInterval.inv]
  have h := RadicalExpression.certifiesWithin_sound hX hf
  simpa [f, target, RationalInterval.Contains, RadicalExpression.eval, div_eq_mul_inv,
    pow_two, sub_eq_add_neg] using h

private theorem endpointFirstAuxiliaryDistance_mem_interval :
    (1905046 : ℝ) / 1000000 ≤ endpointFirstAuxiliaryDistance certifiedEndpointPair.2 ∧
      endpointFirstAuxiliaryDistance certifiedEndpointPair.2 ≤ 1905047 / 1000000 := by
  rw [endpointFirstAuxiliaryDistance]
  constructor
  · apply Real.le_sqrt_of_sq_le
    nlinarith [endpointFirstAuxiliaryRadicand_mem_interval.1]
  · apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · nlinarith [endpointFirstAuxiliaryRadicand_mem_interval.2]

private theorem endpointMixedAuxiliaryRadicand_mem_interval :
    (4295087 : ℝ) / 1000000 ≤
        (certifiedEndpointPair.2 ^ 2 +
            endpointSecondDistance cStar certifiedEndpointPair.2 ^ 2) / 2 - cStar ^ 2 ∧
      (certifiedEndpointPair.2 ^ 2 +
            endpointSecondDistance cStar certifiedEndpointPair.2 ^ 2) / 2 - cStar ^ 2 ≤
        4295090 / 1000000 := by
  let f : RadicalExpression 3 :=
    .add
      (.mul (.add (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2)))
        (.inv (.constant 2)))
      (.neg (.mul (.var 0) (.var 0)))
  let X : Fin 3 → RationalInterval
    | 0 => endpointInputBox 0
    | 1 => endpointInputBox 1
    | 2 => ⟨2043810 / 1000000, 2043811 / 1000000, by norm_num⟩
  let value : Fin 3 → ℝ :=
    ![cStar, certifiedEndpointPair.2, endpointSecondDistance cStar certifiedEndpointPair.2]
  let target : RationalInterval := ⟨4295087 / 1000000, 4295090 / 1000000, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · exact endpointInput_mem_box 0
    · exact endpointInput_mem_box 1
    · simpa [X, value, RationalInterval.Contains] using endpointSecondDistance_mem_interval
  have hf : f.certifiesWithin X target = true := by
    norm_num [f, X, endpointInputBox, target, RadicalExpression.certifiesWithin,
      RadicalExpression.enclosure, RationalInterval.singleton, RationalInterval.add,
      RationalInterval.neg, RationalInterval.mul, RationalInterval.inv]
  have h := RadicalExpression.certifiesWithin_sound hX hf
  simpa [f, value, target, RationalInterval.Contains, RadicalExpression.eval,
    div_eq_mul_inv, pow_two, sub_eq_add_neg] using h

private theorem endpointMixedAuxiliaryDistance_mem_interval :
    (2072459 : ℝ) / 1000000 ≤
        endpointMixedAuxiliaryDistance cStar certifiedEndpointPair.2 ∧
      endpointMixedAuxiliaryDistance cStar certifiedEndpointPair.2 ≤ 2072460 / 1000000 := by
  rw [endpointMixedAuxiliaryDistance]
  constructor
  · apply Real.le_sqrt_of_sq_le
    nlinarith [endpointMixedAuxiliaryRadicand_mem_interval.1]
  · apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · nlinarith [endpointMixedAuxiliaryRadicand_mem_interval.2]

private theorem endpointUnitAbscissa_mem_interval :
    (-814602 : ℝ) / 1000000 ≤ endpointUnitAbscissa certifiedEndpointPair.2 ∧
      endpointUnitAbscissa certifiedEndpointPair.2 ≤ -814601 / 1000000 := by
  let f : RadicalExpression 1 :=
    .mul (.add (.constant 5) (.neg (.mul (.var 0) (.var 0)))) (.inv (.constant 4))
  let X : Fin 1 → RationalInterval
    | 0 => endpointInputBox 1
  let target : RationalInterval := ⟨-814602 / 1000000, -814601 / 1000000, by norm_num⟩
  have hX : ∀ i, (X i).Contains (![certifiedEndpointPair.2] i) := by
    intro i
    fin_cases i
    exact endpointInput_mem_box 1
  have hf : f.certifiesWithin X target = true := by
    norm_num [f, X, endpointInputBox, target, RadicalExpression.certifiesWithin,
      RadicalExpression.enclosure, RationalInterval.singleton, RationalInterval.add,
      RationalInterval.neg, RationalInterval.mul, RationalInterval.inv]
  have h := RadicalExpression.certifiesWithin_sound hX hf
  simpa [f, target, endpointUnitAbscissa, RationalInterval.Contains, RadicalExpression.eval,
    div_eq_mul_inv, pow_two, sub_eq_add_neg] using h

private theorem endpointOuterAbscissa_mem_interval :
    (-255010 : ℝ) / 1000000 ≤ endpointOuterAbscissa cStar certifiedEndpointPair.2 ∧
      endpointOuterAbscissa cStar certifiedEndpointPair.2 ≤ -255006 / 1000000 := by
  let f : RadicalExpression 2 :=
    .mul
      (.add
        (.add (.constant 1) (.mul (.constant 4) (.mul (.var 0) (.var 0))))
        (.neg (.mul (.var 1) (.var 1))))
      (.inv (.constant 4))
  let X : Fin 2 → RationalInterval
    | 0 => ⟨734358 / 1000000, 734359 / 1000000, by norm_num⟩
    | 1 => ⟨2043810 / 1000000, 2043811 / 1000000, by norm_num⟩
  let value : Fin 2 → ℝ :=
    ![endpointOuterRadius cStar certifiedEndpointPair.2,
      endpointSecondDistance cStar certifiedEndpointPair.2]
  let target : RationalInterval := ⟨-255010 / 1000000, -255006 / 1000000, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using endpointOuterRadius_mem_interval
    · simpa [X, value, RationalInterval.Contains] using endpointSecondDistance_mem_interval
  have hf : f.certifiesWithin X target = true := by
    norm_num [f, X, target, RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.neg,
      RationalInterval.mul, RationalInterval.inv]
  have h := RadicalExpression.certifiesWithin_sound hX hf
  simpa [f, value, target, endpointOuterAbscissa, RationalInterval.Contains,
    RadicalExpression.eval, div_eq_mul_inv, pow_two, sub_eq_add_neg] using h

private theorem endpointUnitOrdinateRadicand_mem_interval :
    (3364233 : ℝ) / 10000000 ≤ 1 - endpointUnitAbscissa certifiedEndpointPair.2 ^ 2 ∧
      1 - endpointUnitAbscissa certifiedEndpointPair.2 ^ 2 ≤ 3364253 / 10000000 := by
  let f : RadicalExpression 1 :=
    .add (.constant 1) (.neg (.mul (.var 0) (.var 0)))
  let X : Fin 1 → RationalInterval
    | 0 => ⟨-814602 / 1000000, -814601 / 1000000, by norm_num⟩
  let target : RationalInterval := ⟨3364233 / 10000000, 3364253 / 10000000, by norm_num⟩
  have hX : ∀ i, (X i).Contains (![endpointUnitAbscissa certifiedEndpointPair.2] i) := by
    intro i
    fin_cases i
    simpa [X, RationalInterval.Contains] using endpointUnitAbscissa_mem_interval
  have hf : f.certifiesWithin X target = true := by
    norm_num [f, X, target, RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.neg,
      RationalInterval.mul]
  have h := RadicalExpression.certifiesWithin_sound hX hf
  simpa [f, target, RationalInterval.Contains, RadicalExpression.eval, pow_two,
    sub_eq_add_neg] using h

private theorem endpointUnitOrdinate_mem_interval :
    (580020 : ℝ) / 1000000 ≤ endpointUnitOrdinate certifiedEndpointPair.2 ∧
      endpointUnitOrdinate certifiedEndpointPair.2 ≤ 580023 / 1000000 := by
  rw [endpointUnitOrdinate]
  constructor
  · apply Real.le_sqrt_of_sq_le
    nlinarith [endpointUnitOrdinateRadicand_mem_interval.1]
  · apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · nlinarith [endpointUnitOrdinateRadicand_mem_interval.2]

private theorem endpointOuterOrdinateRadicand_mem_interval :
    (4742515 : ℝ) / 10000000 ≤
        endpointOuterRadius cStar certifiedEndpointPair.2 ^ 2 -
          endpointOuterAbscissa cStar certifiedEndpointPair.2 ^ 2 ∧
      endpointOuterRadius cStar certifiedEndpointPair.2 ^ 2 -
          endpointOuterAbscissa cStar certifiedEndpointPair.2 ^ 2 ≤ 4742552 / 10000000 := by
  let f : RadicalExpression 2 :=
    .add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 1) (.var 1)))
  let X : Fin 2 → RationalInterval
    | 0 => ⟨734358 / 1000000, 734359 / 1000000, by norm_num⟩
    | 1 => ⟨-255010 / 1000000, -255006 / 1000000, by norm_num⟩
  let value : Fin 2 → ℝ :=
    ![endpointOuterRadius cStar certifiedEndpointPair.2,
      endpointOuterAbscissa cStar certifiedEndpointPair.2]
  let target : RationalInterval := ⟨4742515 / 10000000, 4742552 / 10000000, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using endpointOuterRadius_mem_interval
    · simpa [X, value, RationalInterval.Contains] using endpointOuterAbscissa_mem_interval
  have hf : f.certifiesWithin X target = true := by
    norm_num [f, X, target, RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.neg,
      RationalInterval.mul]
  have h := RadicalExpression.certifiesWithin_sound hX hf
  simpa [f, value, target, RationalInterval.Contains, RadicalExpression.eval, pow_two,
    sub_eq_add_neg] using h

private theorem endpointOuterOrdinate_mem_interval :
    (-688662 : ℝ) / 1000000 ≤ endpointOuterOrdinate cStar certifiedEndpointPair.2 ∧
      endpointOuterOrdinate cStar certifiedEndpointPair.2 ≤ -688657 / 1000000 := by
  rw [endpointOuterOrdinate]
  constructor
  · have hupper : Real.sqrt
        (endpointOuterRadius cStar certifiedEndpointPair.2 ^ 2 -
          endpointOuterAbscissa cStar certifiedEndpointPair.2 ^ 2) ≤
        (688662 : ℝ) / 1000000 := by
      apply (Real.sqrt_le_iff).2
      constructor
      · norm_num
      · nlinarith [endpointOuterOrdinateRadicand_mem_interval.2]
    linarith
  · have hlower : (688657 : ℝ) / 1000000 ≤ Real.sqrt
        (endpointOuterRadius cStar certifiedEndpointPair.2 ^ 2 -
          endpointOuterAbscissa cStar certifiedEndpointPair.2 ^ 2) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [endpointOuterOrdinateRadicand_mem_interval.1]
    linarith

private theorem endpointChordAbscissa_mem_interval :
    (-191708 : ℝ) / 1000000 ≤ endpointChordAbscissa cStar certifiedEndpointPair.2 ∧
      endpointChordAbscissa cStar certifiedEndpointPair.2 ≤ -191705 / 1000000 := by
  let f : RadicalExpression 2 :=
    .mul
      (.add (.add (.constant 1) (.mul (.var 1) (.var 1)))
        (.neg (.mul (.var 0) (.var 0))))
      (.inv (.constant 2))
  let X : Fin 2 → RationalInterval
    | 0 => endpointInputBox 0
    | 1 => ⟨734358 / 1000000, 734359 / 1000000, by norm_num⟩
  let value : Fin 2 → ℝ := ![cStar, endpointOuterRadius cStar certifiedEndpointPair.2]
  let target : RationalInterval := ⟨-191708 / 1000000, -191705 / 1000000, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · exact endpointInput_mem_box 0
    · simpa [X, value, RationalInterval.Contains] using endpointOuterRadius_mem_interval
  have hf : f.certifiesWithin X target = true := by
    norm_num [f, X, endpointInputBox, target, RadicalExpression.certifiesWithin,
      RadicalExpression.enclosure, RationalInterval.singleton, RationalInterval.add,
      RationalInterval.neg, RationalInterval.mul, RationalInterval.inv]
  have h := RadicalExpression.certifiesWithin_sound hX hf
  simpa [f, value, target, endpointChordAbscissa, RationalInterval.Contains,
    RadicalExpression.eval, div_eq_mul_inv, pow_two, sub_eq_add_neg] using h

private theorem endpointChordOrdinateRadicand_mem_interval :
    (5025295 : ℝ) / 10000000 ≤
        endpointOuterRadius cStar certifiedEndpointPair.2 ^ 2 -
          endpointChordAbscissa cStar certifiedEndpointPair.2 ^ 2 ∧
      endpointOuterRadius cStar certifiedEndpointPair.2 ^ 2 -
          endpointChordAbscissa cStar certifiedEndpointPair.2 ^ 2 ≤ 5025325 / 10000000 := by
  let f : RadicalExpression 2 :=
    .add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 1) (.var 1)))
  let X : Fin 2 → RationalInterval
    | 0 => ⟨734358 / 1000000, 734359 / 1000000, by norm_num⟩
    | 1 => ⟨-191708 / 1000000, -191705 / 1000000, by norm_num⟩
  let value : Fin 2 → ℝ :=
    ![endpointOuterRadius cStar certifiedEndpointPair.2,
      endpointChordAbscissa cStar certifiedEndpointPair.2]
  let target : RationalInterval := ⟨5025295 / 10000000, 5025325 / 10000000, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using endpointOuterRadius_mem_interval
    · simpa [X, value, RationalInterval.Contains] using endpointChordAbscissa_mem_interval
  have hf : f.certifiesWithin X target = true := by
    norm_num [f, X, target, RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.neg,
      RationalInterval.mul]
  have h := RadicalExpression.certifiesWithin_sound hX hf
  simpa [f, value, target, RationalInterval.Contains, RadicalExpression.eval, pow_two,
    sub_eq_add_neg] using h

private theorem endpointChordOrdinate_mem_interval :
    (708893 : ℝ) / 1000000 ≤ endpointChordOrdinate cStar certifiedEndpointPair.2 ∧
      endpointChordOrdinate cStar certifiedEndpointPair.2 ≤ 708896 / 1000000 := by
  rw [endpointChordOrdinate]
  constructor
  · apply Real.le_sqrt_of_sq_le
    nlinarith [endpointChordOrdinateRadicand_mem_interval.1]
  · apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · nlinarith [endpointChordOrdinateRadicand_mem_interval.2]

private theorem endpointAngularRate_mem_interval :
    (1234508 : ℝ) / 1000000 ≤ endpointAngularRate cStar certifiedEndpointPair.2 ∧
      endpointAngularRate cStar certifiedEndpointPair.2 ≤ 1234521 / 1000000 := by
  let f : RadicalExpression 3 :=
    .mul (.mul (.var 0) (.add (.constant 1) (.neg (.var 1)))) (.inv (.var 2))
  let X : Fin 3 → RationalInterval
    | 0 => ⟨734358 / 1000000, 734359 / 1000000, by norm_num⟩
    | 1 => ⟨-191708 / 1000000, -191705 / 1000000, by norm_num⟩
    | 2 => ⟨708893 / 1000000, 708896 / 1000000, by norm_num⟩
  let value : Fin 3 → ℝ :=
    ![endpointOuterRadius cStar certifiedEndpointPair.2,
      endpointChordAbscissa cStar certifiedEndpointPair.2,
      endpointChordOrdinate cStar certifiedEndpointPair.2]
  let target : RationalInterval := ⟨1234508 / 1000000, 1234521 / 1000000, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using endpointOuterRadius_mem_interval
    · simpa [X, value, RationalInterval.Contains] using endpointChordAbscissa_mem_interval
    · simpa [X, value, RationalInterval.Contains] using endpointChordOrdinate_mem_interval
  have hf : f.certifiesWithin X target = true := by
    norm_num [f, X, target, RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.neg,
      RationalInterval.mul, RationalInterval.inv]
  have h := RadicalExpression.certifiesWithin_sound hX hf
  simpa [f, value, target, endpointAngularRate, RationalInterval.Contains,
    RadicalExpression.eval, div_eq_mul_inv, sub_eq_add_neg] using h

private theorem endpointOuterAbscissaDerivative_mem_interval :
    (-1314265 : ℝ) / 1000000 ≤
        endpointOuterAbscissaDerivative cStar certifiedEndpointPair.2 ∧
      endpointOuterAbscissaDerivative cStar certifiedEndpointPair.2 ≤ -1314242 / 1000000 := by
  let f : RadicalExpression 4 :=
    .add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3)))
  let X : Fin 4 → RationalInterval
    | 0 => ⟨734358 / 1000000, 734359 / 1000000, by norm_num⟩
    | 1 => ⟨-814602 / 1000000, -814601 / 1000000, by norm_num⟩
    | 2 => ⟨1234508 / 1000000, 1234521 / 1000000, by norm_num⟩
    | 3 => ⟨580020 / 1000000, 580023 / 1000000, by norm_num⟩
  let value : Fin 4 → ℝ :=
    ![endpointOuterRadius cStar certifiedEndpointPair.2,
      endpointUnitAbscissa certifiedEndpointPair.2,
      endpointAngularRate cStar certifiedEndpointPair.2,
      endpointUnitOrdinate certifiedEndpointPair.2]
  let target : RationalInterval :=
    ⟨-1314265 / 1000000, -1314242 / 1000000, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using endpointOuterRadius_mem_interval
    · simpa [X, value, RationalInterval.Contains] using endpointUnitAbscissa_mem_interval
    · simpa [X, value, RationalInterval.Contains] using endpointAngularRate_mem_interval
    · simpa [X, value, RationalInterval.Contains] using endpointUnitOrdinate_mem_interval
  have hf : f.certifiesWithin X target = true := by
    norm_num [f, X, target, RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.neg,
      RationalInterval.mul]
  have h := RadicalExpression.certifiesWithin_sound hX hf
  simpa [f, value, target, endpointOuterAbscissaDerivative, RationalInterval.Contains,
    RadicalExpression.eval, sub_eq_add_neg] using h

private theorem endpointSecondDistanceDerivative_mem_interval :
    (2723294 : ℝ) / 1000000 ≤
        endpointSecondDistanceDerivative cStar certifiedEndpointPair.2 ∧
      endpointSecondDistanceDerivative cStar certifiedEndpointPair.2 ≤ 2723337 / 1000000 := by
  let f : RadicalExpression 3 :=
    .mul
      (.add (.mul (.constant 4) (.var 0)) (.neg (.mul (.constant 2) (.var 1))))
      (.inv (.var 2))
  let X : Fin 3 → RationalInterval
    | 0 => ⟨734358 / 1000000, 734359 / 1000000, by norm_num⟩
    | 1 => ⟨-1314265 / 1000000, -1314242 / 1000000, by norm_num⟩
    | 2 => ⟨2043810 / 1000000, 2043811 / 1000000, by norm_num⟩
  let value : Fin 3 → ℝ :=
    ![endpointOuterRadius cStar certifiedEndpointPair.2,
      endpointOuterAbscissaDerivative cStar certifiedEndpointPair.2,
      endpointSecondDistance cStar certifiedEndpointPair.2]
  let target : RationalInterval := ⟨2723294 / 1000000, 2723337 / 1000000, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using endpointOuterRadius_mem_interval
    · simpa [X, value, RationalInterval.Contains] using
        endpointOuterAbscissaDerivative_mem_interval
    · simpa [X, value, RationalInterval.Contains] using endpointSecondDistance_mem_interval
  have hf : f.certifiesWithin X target = true := by
    norm_num [f, X, target, RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.neg,
      RationalInterval.mul, RationalInterval.inv]
  have h := RadicalExpression.certifiesWithin_sound hX hf
  simpa [f, value, target, endpointSecondDistanceDerivative, RationalInterval.Contains,
    RadicalExpression.eval, div_eq_mul_inv, sub_eq_add_neg] using h

private theorem endpointMixedDistanceDerivative_mem_interval :
    (1342822 : ℝ) / 1000000 ≤
        endpointMixedDistanceDerivative cStar certifiedEndpointPair.2 ∧
      endpointMixedDistanceDerivative cStar certifiedEndpointPair.2 ≤ 1342847 / 1000000 := by
  let f : RadicalExpression 3 :=
    .mul (.add (.mul (.constant 2) (.var 0)) (.neg (.var 1))) (.inv (.var 2))
  let X : Fin 3 → RationalInterval
    | 0 => ⟨734358 / 1000000, 734359 / 1000000, by norm_num⟩
    | 1 => ⟨-1314265 / 1000000, -1314242 / 1000000, by norm_num⟩
    | 2 => ⟨2072459 / 1000000, 2072460 / 1000000, by norm_num⟩
  let value : Fin 3 → ℝ :=
    ![endpointOuterRadius cStar certifiedEndpointPair.2,
      endpointOuterAbscissaDerivative cStar certifiedEndpointPair.2,
      endpointMixedAuxiliaryDistance cStar certifiedEndpointPair.2]
  let target : RationalInterval := ⟨1342822 / 1000000, 1342847 / 1000000, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using endpointOuterRadius_mem_interval
    · simpa [X, value, RationalInterval.Contains] using
        endpointOuterAbscissaDerivative_mem_interval
    · simpa [X, value, RationalInterval.Contains] using
        endpointMixedAuxiliaryDistance_mem_interval
  have hf : f.certifiesWithin X target = true := by
    norm_num [f, X, target, RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.neg,
      RationalInterval.mul, RationalInterval.inv]
  have h := RadicalExpression.certifiesWithin_sound hX hf
  simpa [f, value, target, endpointMixedDistanceDerivative, RationalInterval.Contains,
    RadicalExpression.eval, div_eq_mul_inv, sub_eq_add_neg] using h

private theorem endpointBaseAngularCoefficient_mem_interval :
    (-270235 : ℝ) / 1000000 ≤
        endpointBaseAngularCoefficient cStar certifiedEndpointPair.2 ∧
      endpointBaseAngularCoefficient cStar certifiedEndpointPair.2 ≤ -270221 / 1000000 := by
  let f : RadicalExpression 4 :=
    .add (.mul (.mul (.constant 2) (.var 0)) (.inv (.var 1)))
      (.mul (.mul (.constant 2) (.var 2)) (.inv (.var 3)))
  let X : Fin 4 → RationalInterval
    | 0 => ⟨580020 / 1000000, 580023 / 1000000, by norm_num⟩
    | 1 => endpointInputBox 1
    | 2 => ⟨-688662 / 1000000, -688657 / 1000000, by norm_num⟩
    | 3 => ⟨2043810 / 1000000, 2043811 / 1000000, by norm_num⟩
  let value : Fin 4 → ℝ :=
    ![endpointUnitOrdinate certifiedEndpointPair.2, certifiedEndpointPair.2,
      endpointOuterOrdinate cStar certifiedEndpointPair.2,
      endpointSecondDistance cStar certifiedEndpointPair.2]
  let target : RationalInterval := ⟨-270235 / 1000000, -270221 / 1000000, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using endpointUnitOrdinate_mem_interval
    · exact endpointInput_mem_box 1
    · simpa [X, value, RationalInterval.Contains] using endpointOuterOrdinate_mem_interval
    · simpa [X, value, RationalInterval.Contains] using endpointSecondDistance_mem_interval
  have hf : f.certifiesWithin X target = true := by
    norm_num [f, X, endpointInputBox, target, RadicalExpression.certifiesWithin,
      RadicalExpression.enclosure, RationalInterval.singleton, RationalInterval.add,
      RationalInterval.mul, RationalInterval.inv]
  have h := RadicalExpression.certifiesWithin_sound hX hf
  simpa [f, value, target, endpointBaseAngularCoefficient, RationalInterval.Contains,
    RadicalExpression.eval, div_eq_mul_inv] using h

private theorem endpointLambdaAngularCoefficient_mem_interval :
    (403668 : ℝ) / 1000000 ≤ endpointLambdaAngularCoefficient certifiedEndpointPair.2 ∧
      endpointLambdaAngularCoefficient certifiedEndpointPair.2 ≤ 403672 / 1000000 := by
  let f : RadicalExpression 2 :=
    .mul (.mul (.constant 2) (.var 0)) (.inv (.var 1))
  let X : Fin 2 → RationalInterval
    | 0 => ⟨580020 / 1000000, 580023 / 1000000, by norm_num⟩
    | 1 => endpointInputBox 1
  let value : Fin 2 → ℝ :=
    ![endpointUnitOrdinate certifiedEndpointPair.2, certifiedEndpointPair.2]
  let target : RationalInterval := ⟨403668 / 1000000, 403672 / 1000000, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using endpointUnitOrdinate_mem_interval
    · exact endpointInput_mem_box 1
  have hf : f.certifiesWithin X target = true := by
    norm_num [f, X, endpointInputBox, target, RadicalExpression.certifiesWithin,
      RadicalExpression.enclosure, RationalInterval.singleton, RationalInterval.mul,
      RationalInterval.inv]
  have h := RadicalExpression.certifiesWithin_sound hX hf
  simpa [f, value, target, endpointLambdaAngularCoefficient, RationalInterval.Contains,
    RadicalExpression.eval, div_eq_mul_inv] using h

private theorem endpointMuAngularCoefficient_mem_interval :
    (252041 : ℝ) / 1000000 ≤ endpointMuAngularCoefficient cStar certifiedEndpointPair.2 ∧
      endpointMuAngularCoefficient cStar certifiedEndpointPair.2 ≤ 252051 / 1000000 := by
  let f : RadicalExpression 4 :=
    .add (.mul (.var 0) (.inv (.var 1)))
      (.mul (.add (.var 0) (.var 2)) (.inv (.var 3)))
  let X : Fin 4 → RationalInterval
    | 0 => ⟨580020 / 1000000, 580023 / 1000000, by norm_num⟩
    | 1 => ⟨1905046 / 1000000, 1905047 / 1000000, by norm_num⟩
    | 2 => ⟨-688662 / 1000000, -688657 / 1000000, by norm_num⟩
    | 3 => ⟨2072459 / 1000000, 2072460 / 1000000, by norm_num⟩
  let value : Fin 4 → ℝ :=
    ![endpointUnitOrdinate certifiedEndpointPair.2,
      endpointFirstAuxiliaryDistance certifiedEndpointPair.2,
      endpointOuterOrdinate cStar certifiedEndpointPair.2,
      endpointMixedAuxiliaryDistance cStar certifiedEndpointPair.2]
  let target : RationalInterval := ⟨252041 / 1000000, 252051 / 1000000, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using endpointUnitOrdinate_mem_interval
    · simpa [X, value, RationalInterval.Contains] using
        endpointFirstAuxiliaryDistance_mem_interval
    · simpa [X, value, RationalInterval.Contains] using endpointOuterOrdinate_mem_interval
    · simpa [X, value, RationalInterval.Contains] using
        endpointMixedAuxiliaryDistance_mem_interval
  have hf : f.certifiesWithin X target = true := by
    norm_num [f, X, target, RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.mul,
      RationalInterval.inv]
  have h := RadicalExpression.certifiesWithin_sound hX hf
  simpa [f, value, target, endpointMuAngularCoefficient, RationalInterval.Contains,
    RadicalExpression.eval, div_eq_mul_inv] using h

private theorem endpointLambdaRadialCoefficient_mem_interval :
    (-1193307 : ℝ) / 1000000 ≤ endpointLambdaRadialCoefficient cStar ∧
      endpointLambdaRadialCoefficient cStar ≤ -1193306 / 1000000 := by
  rw [endpointLambdaRadialCoefficient]
  constructor <;> linarith [cStar_mem_isolation_box.1, cStar_mem_isolation_box.2]

private theorem endpointMuRadialCoefficient_mem_interval :
    (-2817020 : ℝ) / 1000000 ≤ endpointMuRadialCoefficient cStar certifiedEndpointPair.2 ∧
      endpointMuRadialCoefficient cStar certifiedEndpointPair.2 ≤ -2816989 / 1000000 := by
  let f : RadicalExpression 2 :=
    .add (.var 0) (.neg (.mul (.constant 3) (.var 1)))
  let X : Fin 2 → RationalInterval
    | 0 => ⟨1342822 / 1000000, 1342847 / 1000000, by norm_num⟩
    | 1 => endpointInputBox 0
  let value : Fin 2 → ℝ :=
    ![endpointMixedDistanceDerivative cStar certifiedEndpointPair.2, cStar]
  let target : RationalInterval := ⟨-2817020 / 1000000, -2816989 / 1000000, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using
        endpointMixedDistanceDerivative_mem_interval
    · exact endpointInput_mem_box 0
  have hf : f.certifiesWithin X target = true := by
    norm_num [f, X, endpointInputBox, target, RadicalExpression.certifiesWithin,
      RadicalExpression.enclosure, RationalInterval.singleton, RationalInterval.add,
      RationalInterval.neg, RationalInterval.mul]
  have h := RadicalExpression.certifiesWithin_sound hX hf
  simpa [f, value, target, endpointMuRadialCoefficient, RationalInterval.Contains,
    RadicalExpression.eval, sub_eq_add_neg] using h

private theorem endpointStationarityDeterminant_mem_interval :
    (-836399 : ℝ) / 1000000 ≤
        endpointStationarityDeterminant cStar certifiedEndpointPair.2 ∧
      endpointStationarityDeterminant cStar certifiedEndpointPair.2 ≤ -836342 / 1000000 := by
  let f : RadicalExpression 4 :=
    .add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3)))
  let X : Fin 4 → RationalInterval
    | 0 => ⟨403668 / 1000000, 403672 / 1000000, by norm_num⟩
    | 1 => ⟨-2817020 / 1000000, -2816989 / 1000000, by norm_num⟩
    | 2 => ⟨252041 / 1000000, 252051 / 1000000, by norm_num⟩
    | 3 => ⟨-1193307 / 1000000, -1193306 / 1000000, by norm_num⟩
  let value : Fin 4 → ℝ :=
    ![endpointLambdaAngularCoefficient certifiedEndpointPair.2,
      endpointMuRadialCoefficient cStar certifiedEndpointPair.2,
      endpointMuAngularCoefficient cStar certifiedEndpointPair.2,
      endpointLambdaRadialCoefficient cStar]
  let target : RationalInterval := ⟨-836399 / 1000000, -836342 / 1000000, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using
        endpointLambdaAngularCoefficient_mem_interval
    · simpa [X, value, RationalInterval.Contains] using
        endpointMuRadialCoefficient_mem_interval
    · simpa [X, value, RationalInterval.Contains] using
        endpointMuAngularCoefficient_mem_interval
    · simpa [X, value, RationalInterval.Contains] using
        endpointLambdaRadialCoefficient_mem_interval
  have hf : f.certifiesWithin X target = true := by
    norm_num [f, X, target, RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.neg,
      RationalInterval.mul]
  have h := RadicalExpression.certifiesWithin_sound hX hf
  simpa [f, value, target, endpointStationarityDeterminant, RationalInterval.Contains,
    RadicalExpression.eval, sub_eq_add_neg] using h

private theorem endpointLambda_mem_interval_aux :
    (8 : ℝ) / 100 ≤ endpointLambda ∧ endpointLambda ≤ 10 / 100 := by
  let f : RadicalExpression 5 :=
    .mul
      (.add (.neg (.mul (.var 0) (.var 1))) (.mul (.var 2) (.var 3)))
      (.inv (.var 4))
  let X : Fin 5 → RationalInterval
    | 0 => ⟨-270235 / 1000000, -270221 / 1000000, by norm_num⟩
    | 1 => ⟨-2817020 / 1000000, -2816989 / 1000000, by norm_num⟩
    | 2 => ⟨252041 / 1000000, 252051 / 1000000, by norm_num⟩
    | 3 => ⟨2723294 / 1000000, 2723337 / 1000000, by norm_num⟩
    | 4 => ⟨-836399 / 1000000, -836342 / 1000000, by norm_num⟩
  let value : Fin 5 → ℝ :=
    ![endpointBaseAngularCoefficient cStar certifiedEndpointPair.2,
      endpointMuRadialCoefficient cStar certifiedEndpointPair.2,
      endpointMuAngularCoefficient cStar certifiedEndpointPair.2,
      endpointSecondDistanceDerivative cStar certifiedEndpointPair.2,
      endpointStationarityDeterminant cStar certifiedEndpointPair.2]
  let target : RationalInterval := ⟨8 / 100, 10 / 100, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using
        endpointBaseAngularCoefficient_mem_interval
    · simpa [X, value, RationalInterval.Contains] using
        endpointMuRadialCoefficient_mem_interval
    · simpa [X, value, RationalInterval.Contains] using
        endpointMuAngularCoefficient_mem_interval
    · simpa [X, value, RationalInterval.Contains] using
        endpointSecondDistanceDerivative_mem_interval
    · simpa [X, value, RationalInterval.Contains] using
        endpointStationarityDeterminant_mem_interval
  have hf : f.certifiesWithin X target = true := by
    norm_num [f, X, target, RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.neg,
      RationalInterval.mul, RationalInterval.inv]
  have h := RadicalExpression.certifiesWithin_sound hX hf
  simpa [f, value, target, endpointLambda, endpointCramerLambda,
    RationalInterval.Contains, RadicalExpression.eval, div_eq_mul_inv, sub_eq_add_neg] using h

private theorem endpointMu_mem_interval_aux :
    (92 : ℝ) / 100 ≤ endpointMu ∧ endpointMu ≤ 94 / 100 := by
  let f : RadicalExpression 5 :=
    .mul
      (.add (.neg (.mul (.var 0) (.var 1))) (.mul (.var 2) (.var 3)))
      (.inv (.var 4))
  let X : Fin 5 → RationalInterval
    | 0 => ⟨403668 / 1000000, 403672 / 1000000, by norm_num⟩
    | 1 => ⟨2723294 / 1000000, 2723337 / 1000000, by norm_num⟩
    | 2 => ⟨-270235 / 1000000, -270221 / 1000000, by norm_num⟩
    | 3 => ⟨-1193307 / 1000000, -1193306 / 1000000, by norm_num⟩
    | 4 => ⟨-836399 / 1000000, -836342 / 1000000, by norm_num⟩
  let value : Fin 5 → ℝ :=
    ![endpointLambdaAngularCoefficient certifiedEndpointPair.2,
      endpointSecondDistanceDerivative cStar certifiedEndpointPair.2,
      endpointBaseAngularCoefficient cStar certifiedEndpointPair.2,
      endpointLambdaRadialCoefficient cStar,
      endpointStationarityDeterminant cStar certifiedEndpointPair.2]
  let target : RationalInterval := ⟨92 / 100, 94 / 100, by norm_num⟩
  have hX : ∀ i, (X i).Contains (value i) := by
    intro i
    fin_cases i
    · simpa [X, value, RationalInterval.Contains] using
        endpointLambdaAngularCoefficient_mem_interval
    · simpa [X, value, RationalInterval.Contains] using
        endpointSecondDistanceDerivative_mem_interval
    · simpa [X, value, RationalInterval.Contains] using
        endpointBaseAngularCoefficient_mem_interval
    · simpa [X, value, RationalInterval.Contains] using
        endpointLambdaRadialCoefficient_mem_interval
    · simpa [X, value, RationalInterval.Contains] using
        endpointStationarityDeterminant_mem_interval
  have hf : f.certifiesWithin X target = true := by
    norm_num [f, X, target, RadicalExpression.certifiesWithin, RadicalExpression.enclosure,
      RationalInterval.singleton, RationalInterval.add, RationalInterval.neg,
      RationalInterval.mul, RationalInterval.inv]
  have h := RadicalExpression.certifiesWithin_sound hX hf
  simpa [f, value, target, endpointMu, endpointCramerMu, RationalInterval.Contains,
    RadicalExpression.eval, div_eq_mul_inv, sub_eq_add_neg] using h

end

/-- The first endpoint weight lies between `0.08` and `0.1`. -/
theorem endpointLambda_mem_interval :
    (2 : ℝ) / 25 ≤ endpointLambda ∧ endpointLambda ≤ 1 / 10 := by
  convert endpointLambda_mem_interval_aux using 1 <;> norm_num

/-- The second endpoint weight lies between `0.92` and `0.94`. -/
theorem endpointMu_mem_interval :
    (23 : ℝ) / 25 ≤ endpointMu ∧ endpointMu ≤ 47 / 50 := by
  convert endpointMu_mem_interval_aux using 1 <;> norm_num

/-- The first endpoint weight is positive. -/
theorem endpointLambda_pos : 0 < endpointLambda := by
  linarith [endpointLambda_mem_interval.1]

/-- The second endpoint weight is positive. -/
theorem endpointMu_pos : 0 < endpointMu := by
  linarith [endpointMu_mem_interval.1]

/-- The endpoint stationarity system has nonzero determinant. -/
theorem endpointStationarityDeterminant_ne_zero :
    endpointStationarityDeterminant cStar certifiedEndpointPair.2 ≠ 0 := by
  linarith [endpointStationarityDeterminant_mem_interval.2]

/-- Cramer's endpoint weights satisfy angular stationarity exactly. -/
theorem endpoint_angular_stationarity :
    endpointBaseAngularCoefficient cStar certifiedEndpointPair.2 +
        endpointLambda * endpointLambdaAngularCoefficient certifiedEndpointPair.2 +
      endpointMu * endpointMuAngularCoefficient cStar certifiedEndpointPair.2 = 0 := by
  rw [endpointLambda, endpointMu, endpointCramerLambda, endpointCramerMu]
  field_simp [endpointStationarityDeterminant_ne_zero]
  rw [endpointStationarityDeterminant]
  ring

/-- Cramer's endpoint weights satisfy radial stationarity exactly. -/
theorem endpoint_radial_stationarity :
    endpointSecondDistanceDerivative cStar certifiedEndpointPair.2 +
        endpointLambda * endpointLambdaRadialCoefficient cStar +
      endpointMu * endpointMuRadialCoefficient cStar certifiedEndpointPair.2 = 0 := by
  rw [endpointLambda, endpointMu, endpointCramerLambda, endpointCramerMu]
  field_simp [endpointStationarityDeterminant_ne_zero]
  rw [endpointStationarityDeterminant]
  ring

/-- Radial shrinkage gains more than one unit beyond both Lipschitz losses. -/
theorem one_lt_endpoint_weight_penalty_margin :
    1 < weightedSecondPenalty cStar endpointLambda endpointMu - (2 + endpointMu) := by
  have hc := cStar_mem_isolation_box.1
  have hlambda := endpointLambda_mem_interval.1
  have hmu := endpointMu_mem_interval.1
  rw [weightedSecondPenalty]
  nlinarith

/-- The endpoint weights meet the non-strict hypothesis of radial chord reduction. -/
theorem endpoint_weight_reduction_margin :
    2 + endpointMu ≤ weightedSecondPenalty cStar endpointLambda endpointMu := by
  linarith [one_lt_endpoint_weight_penalty_margin]

end LeanPool.Besicovitch
