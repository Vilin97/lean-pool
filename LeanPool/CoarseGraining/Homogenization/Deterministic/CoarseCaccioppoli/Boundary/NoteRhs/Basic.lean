/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.RadiusIteration

/-! # Basic -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped BigOperators

/-- Boundary recursion prefactor with the public `uL2Sq` factor removed. -/
def coarseCaccioppoliBoundaryRecursionCoeff {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C : ℝ) : ℝ :=
  C *
    Real.rpow
      (C / (s * (1 - s)) * Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ))
      (coarseCaccioppoliPower s t) *
    LambdaSq Q s (.finite 1) a

/-- Split recursion prefactor with the public `uL2Sq` factor removed. -/
def coarseCaccioppoliBoundaryRecursionCoeffSplit {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t Calpha Ccross : ℝ) : ℝ :=
  Ccross *
    Real.rpow
      (Calpha / (s * (1 - s)) * Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ))
      (coarseCaccioppoliPower s t) *
    LambdaSq Q s (.finite 1) a

theorem coarseCaccioppoliBoundaryRecursionCoeffSplit_self {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ) :
    coarseCaccioppoliBoundaryRecursionCoeffSplit Q a s t C C =
      coarseCaccioppoliBoundaryRecursionCoeff Q a s t C := by
  rfl

/-- Explicit-height recursion prefactor with the public `uL2Sq` factor removed. -/
def coarseCaccioppoliBoundaryExplicitHeightRecursionCoeff {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ) : ℝ :=
  (6561 : ℝ) * 6561 * C ^ (2 : ℕ) * LambdaSq Q s (.finite 1) a +
    ((9 : ℝ) * Real.rpow (4 : ℝ) (coarseCaccioppoliPower s t) *
      Real.rpow (81 : ℝ) (coarseCaccioppoliPower s t)) *
      C * coarseCaccioppoliBoundaryRecursionCoeff Q a s t C

/-- Split explicit-height recursion prefactor with the public `uL2Sq` factor
removed.  The left branch depends only on `Ccross`; the logarithmic branch
depends on `Calpha` through the height and on `Ccross` through the cross term. -/
def coarseCaccioppoliBoundaryExplicitHeightRecursionCoeffSplit {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t Calpha Ccross : ℝ) : ℝ :=
  (6561 : ℝ) * 6561 * Ccross ^ (2 : ℕ) * LambdaSq Q s (.finite 1) a +
    ((9 : ℝ) * Real.rpow (4 : ℝ) (coarseCaccioppoliPower s t) *
      Real.rpow (81 : ℝ) (coarseCaccioppoliPower s t)) *
      Ccross *
        coarseCaccioppoliBoundaryRecursionCoeffSplit Q a s t Calpha Ccross

theorem coarseCaccioppoliBoundaryExplicitHeightRecursionCoeffSplit_self {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ) :
    coarseCaccioppoliBoundaryExplicitHeightRecursionCoeffSplit Q a s t C C =
      coarseCaccioppoliBoundaryExplicitHeightRecursionCoeff Q a s t C := by
  rfl

/-- Explicit-height radius-iteration prefactor with `uL2Sq` removed. -/
def coarseCaccioppoliBoundaryExplicitHeightCoeff {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C : ℝ) : ℝ :=
  coarseCaccioppoliRadiusIterationConst (coarseCaccioppoliBeta s t) *
    coarseCaccioppoliBoundaryExplicitHeightRecursionCoeff Q a s t C

/-- Split explicit-height prefactor using the standard beta-dependent radius
iteration.  This is the coefficient surface for the note-facing route, carrying
the standard `(C beta)^beta` iteration loss. -/
def coarseCaccioppoliBoundaryStandardExplicitHeightCoeffSplit {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t Calpha Ccross : ℝ) : ℝ :=
  coarseCaccioppoliStandardRadiusIterationConst (coarseCaccioppoliBeta s t) *
    coarseCaccioppoliBoundaryExplicitHeightRecursionCoeffSplit Q a s t Calpha Ccross

/-- Standard-radius split explicit-height bound, before conversion to the
public note RHS. -/
def coarseCaccioppoliBoundaryStandardExplicitHeightBoundSplit {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross uL2Sq : ℝ) : ℝ :=
  coarseCaccioppoliStandardRadiusIterationConst (coarseCaccioppoliBeta s t) *
    coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit
      Q a s t Calpha Ccross uL2Sq

/-- Literal note RHS prefactor with the public `uL2Sq` factor removed. -/
def coarseCaccioppoliBoundaryNoteCoeff {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C : ℝ) : ℝ :=
  Real.rpow (C / coarseCaccioppoliSigma s t)
      (2 + 4 * s / coarseCaccioppoliSigma s t) *
    Real.rpow s (-2 * s / coarseCaccioppoliSigma s t) *
    Real.rpow (ThetaRatio Q s t a) (s / coarseCaccioppoliSigma s t) *
    LambdaSq Q s (.finite 1) a

theorem coarseCaccioppoliBoundaryRecursionRhs_eq_coeff_mul_uL2Sq {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ) :
    coarseCaccioppoliBoundaryRecursionRhs Q a s t C uL2Sq =
      coarseCaccioppoliBoundaryRecursionCoeff Q a s t C * uL2Sq := by
  unfold coarseCaccioppoliBoundaryRecursionRhs
    coarseCaccioppoliBoundaryRecursionCoeff
  ring

theorem coarseCaccioppoliBoundaryRecursionRhsSplit_eq_coeff_mul_uL2Sq {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross uL2Sq : ℝ) :
    coarseCaccioppoliBoundaryRecursionRhsSplit Q a s t Calpha Ccross uL2Sq =
      coarseCaccioppoliBoundaryRecursionCoeffSplit Q a s t Calpha Ccross *
        uL2Sq := by
  unfold coarseCaccioppoliBoundaryRecursionRhsSplit
    coarseCaccioppoliBoundaryRecursionCoeffSplit
  ring

theorem
    coarseCaccioppoliBoundaryExplicitHeightRecursionRhs_eq_coeff_mul_uL2Sq
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ) :
    coarseCaccioppoliBoundaryExplicitHeightRecursionRhs Q a s t C uL2Sq =
      coarseCaccioppoliBoundaryExplicitHeightRecursionCoeff Q a s t C * uL2Sq := by
  unfold coarseCaccioppoliBoundaryExplicitHeightRecursionRhs
    coarseCaccioppoliBoundaryExplicitHeightRecursionCoeff
    coarseCaccioppoliBoundaryRecursionRhs
    coarseCaccioppoliBoundaryRecursionCoeff
  ring

theorem
    coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit_eq_coeff_mul_uL2Sq
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross uL2Sq : ℝ) :
    coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit
        Q a s t Calpha Ccross uL2Sq =
      coarseCaccioppoliBoundaryExplicitHeightRecursionCoeffSplit
          Q a s t Calpha Ccross * uL2Sq := by
  unfold coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit
    coarseCaccioppoliBoundaryExplicitHeightRecursionCoeffSplit
    coarseCaccioppoliBoundaryRecursionRhsSplit
    coarseCaccioppoliBoundaryRecursionCoeffSplit
  ring

theorem coarseCaccioppoliBoundaryExplicitHeightBound_eq_coeff_mul_uL2Sq
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ) :
    coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq =
      coarseCaccioppoliBoundaryExplicitHeightCoeff Q a s t C * uL2Sq := by
  unfold coarseCaccioppoliBoundaryExplicitHeightBound
    coarseCaccioppoliBoundaryExplicitHeightCoeff
    coarseCaccioppoliBoundaryExplicitHeightRecursionRhs
    coarseCaccioppoliBoundaryExplicitHeightRecursionCoeff
    coarseCaccioppoliBoundaryRecursionRhs
    coarseCaccioppoliBoundaryRecursionCoeff
  ring

theorem
    coarseCaccioppoliBoundaryStandardExplicitHeightBoundSplit_eq_coeff_mul_uL2Sq
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross uL2Sq : ℝ) :
    coarseCaccioppoliBoundaryStandardExplicitHeightBoundSplit
        Q a s t Calpha Ccross uL2Sq =
      coarseCaccioppoliBoundaryStandardExplicitHeightCoeffSplit
          Q a s t Calpha Ccross *
        uL2Sq := by
  unfold coarseCaccioppoliBoundaryStandardExplicitHeightBoundSplit
    coarseCaccioppoliBoundaryStandardExplicitHeightCoeffSplit
    coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit
    coarseCaccioppoliBoundaryExplicitHeightRecursionCoeffSplit
    coarseCaccioppoliBoundaryRecursionRhsSplit
    coarseCaccioppoliBoundaryRecursionCoeffSplit
  ring

theorem coarseCaccioppoliBoundaryNoteRhs_eq_coeff_mul_uL2Sq {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ) :
    coarseCaccioppoliBoundaryNoteRhs Q a s t C uL2Sq =
      coarseCaccioppoliBoundaryNoteCoeff Q a s t C * uL2Sq := by
  unfold coarseCaccioppoliBoundaryNoteRhs coarseCaccioppoliBoundaryNoteCoeff
  ring

theorem coarseCaccioppoliBoundaryRecursionRhs_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq) :
    0 ≤ coarseCaccioppoliBoundaryRecursionRhs Q a s t C uL2Sq := by
  have hs1 : s < 1 := by linarith
  have hden_nonneg : 0 ≤ s * (1 - s) := by
    nlinarith
  have htheta_nonneg : 0 ≤ ThetaRatio Q s t a :=
    thetaRatio_nonneg Q s t a hs.le ht.le
  have hpow_nonneg :
      0 ≤
        Real.rpow
          (C / (s * (1 - s)) * Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ))
          (coarseCaccioppoliPower s t) := by
    refine Real.rpow_nonneg ?_ _
    refine mul_nonneg ?_ ?_
    · exact div_nonneg hC hden_nonneg
    · exact Real.rpow_nonneg htheta_nonneg _
  have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le
  unfold coarseCaccioppoliBoundaryRecursionRhs
  positivity

theorem coarseCaccioppoliBoundaryRecursionRhsSplit_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross uL2Sq : ℝ)
    (hCalpha : 0 ≤ Calpha) (hCcross : 0 ≤ Ccross)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq) :
    0 ≤ coarseCaccioppoliBoundaryRecursionRhsSplit
      Q a s t Calpha Ccross uL2Sq := by
  have hs1 : s < 1 := by
    linarith
  have hden_nonneg : 0 ≤ s * (1 - s) := by
    nlinarith
  have htheta_nonneg : 0 ≤ ThetaRatio Q s t a :=
    thetaRatio_nonneg Q s t a hs.le ht.le
  have hpow_nonneg :
      0 ≤
        Real.rpow
          (Calpha / (s * (1 - s)) *
            Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ))
          (coarseCaccioppoliPower s t) := by
    refine Real.rpow_nonneg ?_ _
    refine mul_nonneg ?_ ?_
    · exact div_nonneg hCalpha hden_nonneg
    · exact Real.rpow_nonneg htheta_nonneg _
  have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le
  unfold coarseCaccioppoliBoundaryRecursionRhsSplit
  positivity

theorem coarseCaccioppoliBoundaryExplicitHeightRecursionRhs_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq) :
    0 ≤ coarseCaccioppoliBoundaryExplicitHeightRecursionRhs Q a s t C uL2Sq := by
  have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le
  have hrec_nonneg :
      0 ≤ coarseCaccioppoliBoundaryRecursionRhs Q a s t C uL2Sq :=
    coarseCaccioppoliBoundaryRecursionRhs_nonneg Q a s t C uL2Sq hC hs ht hst hu
  unfold coarseCaccioppoliBoundaryExplicitHeightRecursionRhs
  refine add_nonneg ?_ ?_
  · exact mul_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg C)) hLambda_nonneg)
      hu
  · refine mul_nonneg ?_ hrec_nonneg
    refine mul_nonneg ?_ hC
    exact mul_nonneg
      (mul_nonneg (by norm_num : 0 ≤ (9 : ℝ))
        (Real.rpow_nonneg (by norm_num : 0 ≤ (4 : ℝ)) _))
      (Real.rpow_nonneg (by norm_num : 0 ≤ (81 : ℝ)) _)

theorem coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross uL2Sq : ℝ)
    (hCalpha : 0 ≤ Calpha) (hCcross : 0 ≤ Ccross)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq) :
    0 ≤ coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit
      Q a s t Calpha Ccross uL2Sq := by
  have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le
  have hrec_nonneg :
      0 ≤ coarseCaccioppoliBoundaryRecursionRhsSplit
        Q a s t Calpha Ccross uL2Sq :=
    coarseCaccioppoliBoundaryRecursionRhsSplit_nonneg
      Q a s t Calpha Ccross uL2Sq hCalpha hCcross hs ht hst hu
  unfold coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit
  refine add_nonneg ?_ ?_
  · exact mul_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg Ccross)) hLambda_nonneg)
      hu
  · refine mul_nonneg ?_ hrec_nonneg
    refine mul_nonneg ?_ hCcross
    exact mul_nonneg
      (mul_nonneg (by norm_num : 0 ≤ (9 : ℝ))
        (Real.rpow_nonneg (by norm_num : 0 ≤ (4 : ℝ)) _))
      (Real.rpow_nonneg (by norm_num : 0 ≤ (81 : ℝ)) _)

theorem coarseCaccioppoliBoundaryBound_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq) :
    0 ≤ coarseCaccioppoliBoundaryBound Q a s t C uL2Sq := by
  unfold coarseCaccioppoliBoundaryBound
  exact mul_nonneg
    (coarseCaccioppoliRadiusIterationConst_nonneg (coarseCaccioppoliBeta s t))
    (coarseCaccioppoliBoundaryRecursionRhs_nonneg Q a s t C uL2Sq hC hs ht hst hu)

theorem coarseCaccioppoliBoundaryExplicitHeightBound_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq) :
    0 ≤ coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq := by
  unfold coarseCaccioppoliBoundaryExplicitHeightBound
  exact mul_nonneg
    (coarseCaccioppoliRadiusIterationConst_nonneg (coarseCaccioppoliBeta s t))
    (coarseCaccioppoliBoundaryExplicitHeightRecursionRhs_nonneg
      Q a s t C uL2Sq hC hs ht hst hu)

theorem coarseCaccioppoliBoundaryRecursionCoeff_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    0 ≤ coarseCaccioppoliBoundaryRecursionCoeff Q a s t C := by
  have h :=
    coarseCaccioppoliBoundaryRecursionRhs_nonneg Q a s t C (1 : ℝ)
      hC hs ht hst (by norm_num)
  simpa [coarseCaccioppoliBoundaryRecursionRhs_eq_coeff_mul_uL2Sq] using h

theorem coarseCaccioppoliBoundaryRecursionCoeffSplit_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t Calpha Ccross : ℝ)
    (hCalpha : 0 ≤ Calpha) (hCcross : 0 ≤ Ccross)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    0 ≤ coarseCaccioppoliBoundaryRecursionCoeffSplit
      Q a s t Calpha Ccross := by
  have h :=
    coarseCaccioppoliBoundaryRecursionRhsSplit_nonneg
      Q a s t Calpha Ccross (1 : ℝ)
      hCalpha hCcross hs ht hst (by norm_num)
  simpa [coarseCaccioppoliBoundaryRecursionRhsSplit_eq_coeff_mul_uL2Sq] using h

theorem coarseCaccioppoliBoundaryExplicitHeightRecursionCoeff_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    0 ≤ coarseCaccioppoliBoundaryExplicitHeightRecursionCoeff Q a s t C := by
  have h :=
    coarseCaccioppoliBoundaryExplicitHeightRecursionRhs_nonneg Q a s t C (1 : ℝ)
      hC hs ht hst (by norm_num)
  simpa [coarseCaccioppoliBoundaryExplicitHeightRecursionRhs_eq_coeff_mul_uL2Sq] using h

theorem coarseCaccioppoliBoundaryExplicitHeightRecursionCoeffSplit_nonneg
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross : ℝ)
    (hCalpha : 0 ≤ Calpha) (hCcross : 0 ≤ Ccross)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    0 ≤ coarseCaccioppoliBoundaryExplicitHeightRecursionCoeffSplit
      Q a s t Calpha Ccross := by
  have h :=
    coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit_nonneg
      Q a s t Calpha Ccross (1 : ℝ)
      hCalpha hCcross hs ht hst (by norm_num)
  simpa [coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit_eq_coeff_mul_uL2Sq]
    using h

theorem coarseCaccioppoliBoundaryExplicitHeightCoeff_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    0 ≤ coarseCaccioppoliBoundaryExplicitHeightCoeff Q a s t C := by
  have h :=
    coarseCaccioppoliBoundaryExplicitHeightBound_nonneg Q a s t C (1 : ℝ)
      hC hs ht hst (by norm_num)
  simpa [coarseCaccioppoliBoundaryExplicitHeightBound_eq_coeff_mul_uL2Sq] using h

theorem coarseCaccioppoliBoundaryNoteRhs_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq) :
    0 ≤ coarseCaccioppoliBoundaryNoteRhs Q a s t C uL2Sq := by
  have hσ_pos : 0 < coarseCaccioppoliSigma s t :=
    coarseCaccioppoli_sigma_pos hst
  have htheta_nonneg : 0 ≤ ThetaRatio Q s t a :=
    thetaRatio_nonneg Q s t a hs.le ht.le
  have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le
  unfold coarseCaccioppoliBoundaryNoteRhs
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (div_nonneg hC hσ_pos.le) _)
          (Real.rpow_nonneg hs.le _))
        (Real.rpow_nonneg htheta_nonneg _))
      hLambda_nonneg)
    hu

theorem coarseCaccioppoliBoundaryNoteCoeff_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    0 ≤ coarseCaccioppoliBoundaryNoteCoeff Q a s t C := by
  have h :=
    coarseCaccioppoliBoundaryNoteRhs_nonneg Q a s t C (1 : ℝ)
      hC hs ht hst (by norm_num)
  simpa [coarseCaccioppoliBoundaryNoteRhs_eq_coeff_mul_uL2Sq] using h

theorem coarseCaccioppoliBoundaryNoteCoeff_mono_C {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C₁ C₂ : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₁C₂ : C₁ ≤ C₂)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    coarseCaccioppoliBoundaryNoteCoeff Q a s t C₁ ≤
      coarseCaccioppoliBoundaryNoteCoeff Q a s t C₂ := by
  have hσ_pos : 0 < coarseCaccioppoliSigma s t :=
    coarseCaccioppoli_sigma_pos hst
  have hexp_nonneg :
      0 ≤ 2 + 4 * s / coarseCaccioppoliSigma s t := by
    have hnum_nonneg : 0 ≤ 4 * s := by positivity
    have hdiv_nonneg : 0 ≤ 4 * s / coarseCaccioppoliSigma s t :=
      div_nonneg hnum_nonneg hσ_pos.le
    linarith
  have hbase_nonneg : 0 ≤ C₁ / coarseCaccioppoliSigma s t :=
    div_nonneg hC₁ hσ_pos.le
  have hbase_le :
      C₁ / coarseCaccioppoliSigma s t ≤
        C₂ / coarseCaccioppoliSigma s t :=
    div_le_div_of_nonneg_right hC₁C₂ hσ_pos.le
  have hpow_le :
      Real.rpow (C₁ / coarseCaccioppoliSigma s t)
          (2 + 4 * s / coarseCaccioppoliSigma s t) ≤
        Real.rpow (C₂ / coarseCaccioppoliSigma s t)
          (2 + 4 * s / coarseCaccioppoliSigma s t) :=
    Real.rpow_le_rpow hbase_nonneg hbase_le hexp_nonneg
  have hs_factor_nonneg :
      0 ≤ Real.rpow s (-2 * s / coarseCaccioppoliSigma s t) :=
    Real.rpow_nonneg hs.le _
  have htheta_nonneg : 0 ≤ ThetaRatio Q s t a :=
    thetaRatio_nonneg Q s t a hs.le ht.le
  have htheta_factor_nonneg :
      0 ≤
        Real.rpow (ThetaRatio Q s t a)
          (s / coarseCaccioppoliSigma s t) :=
    Real.rpow_nonneg htheta_nonneg _
  have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le
  unfold coarseCaccioppoliBoundaryNoteCoeff
  exact
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpow_le hs_factor_nonneg)
        htheta_factor_nonneg)
      hLambda_nonneg

theorem coarseCaccioppoliBoundaryNoteRhs_mono_C {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C₁ C₂ uL2Sq : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₁C₂ : C₁ ≤ C₂)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq) :
    coarseCaccioppoliBoundaryNoteRhs Q a s t C₁ uL2Sq ≤
      coarseCaccioppoliBoundaryNoteRhs Q a s t C₂ uL2Sq := by
  rw [coarseCaccioppoliBoundaryNoteRhs_eq_coeff_mul_uL2Sq,
    coarseCaccioppoliBoundaryNoteRhs_eq_coeff_mul_uL2Sq]
  exact mul_le_mul_of_nonneg_right
    (coarseCaccioppoliBoundaryNoteCoeff_mono_C
      Q a s t C₁ C₂ hC₁ hC₁C₂ hs ht hst)
    hu

private theorem const_mul_rpow_le_rpow_of_mul_le {M x y p : ℝ}
    (hM : 1 ≤ M) (hx : 0 ≤ x) (hMxy : M * x ≤ y) (hp : 1 ≤ p) :
    M * Real.rpow x p ≤ Real.rpow y p := by
  have hM_nonneg : 0 ≤ M := le_trans (by norm_num) hM
  have hMx_nonneg : 0 ≤ M * x := mul_nonneg hM_nonneg hx
  have hM_le_Mp : M ≤ Real.rpow M p := by
    simpa using Real.self_le_rpow_of_one_le hM hp
  have hxpow_nonneg : 0 ≤ Real.rpow x p := Real.rpow_nonneg hx p
  have hleft : M * Real.rpow x p ≤ Real.rpow M p * Real.rpow x p :=
    mul_le_mul_of_nonneg_right hM_le_Mp hxpow_nonneg
  have hmul_rpow : Real.rpow M p * Real.rpow x p = Real.rpow (M * x) p :=
    (Real.mul_rpow hM_nonneg hx).symm
  calc
    M * Real.rpow x p ≤ Real.rpow M p * Real.rpow x p := hleft
    _ = Real.rpow (M * x) p := hmul_rpow
    _ ≤ Real.rpow y p :=
      Real.rpow_le_rpow hMx_nonneg hMxy (by linarith)

theorem coarseCaccioppoliBoundaryNoteCoeff_mul_const_le_of_mul_constant_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t M C₁ C₂ : ℝ)
    (hM : 1 ≤ M) (hC₁ : 0 ≤ C₁) (hMC₁C₂ : M * C₁ ≤ C₂)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    M * coarseCaccioppoliBoundaryNoteCoeff Q a s t C₁ ≤
      coarseCaccioppoliBoundaryNoteCoeff Q a s t C₂ := by
  let σ : ℝ := coarseCaccioppoliSigma s t
  let p : ℝ := 2 + 4 * s / σ
  let F : ℝ :=
    Real.rpow s (-2 * s / σ) *
      Real.rpow (ThetaRatio Q s t a) (s / σ) *
        LambdaSq Q s (.finite 1) a
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    exact coarseCaccioppoli_sigma_pos hst
  have hp_ge_one : 1 ≤ p := by
    have hdiv_nonneg : 0 ≤ 4 * s / σ := by positivity
    dsimp [p]
    linarith
  have hbase_nonneg : 0 ≤ C₁ / σ := div_nonneg hC₁ hσ_pos.le
  have hbase_le : M * (C₁ / σ) ≤ C₂ / σ := by
    calc
      M * (C₁ / σ) = (M * C₁) / σ := by ring
      _ ≤ C₂ / σ := div_le_div_of_nonneg_right hMC₁C₂ hσ_pos.le
  have hpow :
      M * Real.rpow (C₁ / σ) p ≤ Real.rpow (C₂ / σ) p :=
    const_mul_rpow_le_rpow_of_mul_le hM hbase_nonneg hbase_le hp_ge_one
  have htheta_nonneg : 0 ≤ ThetaRatio Q s t a :=
    thetaRatio_nonneg Q s t a hs.le ht.le
  have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le
  have hF_nonneg : 0 ≤ F := by
    dsimp [F]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hs.le _)
        (Real.rpow_nonneg htheta_nonneg _))
      hLambda_nonneg
  calc
    M * coarseCaccioppoliBoundaryNoteCoeff Q a s t C₁ =
        (M * Real.rpow (C₁ / σ) p) * F := by
      dsimp [F, p, σ]
      unfold coarseCaccioppoliBoundaryNoteCoeff
      ring_nf
      simp [LambdaSq]
    _ ≤ Real.rpow (C₂ / σ) p * F :=
      mul_le_mul_of_nonneg_right hpow hF_nonneg
    _ = coarseCaccioppoliBoundaryNoteCoeff Q a s t C₂ := by
      dsimp [F, p, σ]
      unfold coarseCaccioppoliBoundaryNoteCoeff
      ring_nf
      simp [LambdaSq]

theorem coarseCaccioppoliBoundaryNoteRhs_mul_const_le_of_mul_constant_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t M C₁ C₂ uL2Sq : ℝ)
    (hM : 1 ≤ M) (hC₁ : 0 ≤ C₁) (hMC₁C₂ : M * C₁ ≤ C₂)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq) :
    M * coarseCaccioppoliBoundaryNoteRhs Q a s t C₁ uL2Sq ≤
      coarseCaccioppoliBoundaryNoteRhs Q a s t C₂ uL2Sq := by
  rw [coarseCaccioppoliBoundaryNoteRhs_eq_coeff_mul_uL2Sq,
    coarseCaccioppoliBoundaryNoteRhs_eq_coeff_mul_uL2Sq]
  calc
    M * (coarseCaccioppoliBoundaryNoteCoeff Q a s t C₁ * uL2Sq) =
        (M * coarseCaccioppoliBoundaryNoteCoeff Q a s t C₁) * uL2Sq := by
      ring
    _ ≤ coarseCaccioppoliBoundaryNoteCoeff Q a s t C₂ * uL2Sq :=
      mul_le_mul_of_nonneg_right
        (coarseCaccioppoliBoundaryNoteCoeff_mul_const_le_of_mul_constant_le
          Q a s t M C₁ C₂ hM hC₁ hMC₁C₂ hs ht hst)
        hu

end

end Homogenization
