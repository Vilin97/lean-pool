/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicResidual

/-!
# Grouping the actual residual with an independent axisymmetric alias

The alias removed from the good residual may contain an arbitrary function
of the non-angular variables in addition to the finite harmonic label sums.
Subtracting that function changes the angular mean by the same amount and
leaves the nonconstant residual unchanged.  The needed angular integrability
is derived from the represented finite harmonic fields, with no regularity
or support assumption on the independent alias.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.AxisymmetricResidualGrouping

open Set Function Filter MeasureTheory CorrectionState
open scoped Topology ContDiff BigOperators

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Lift an arbitrary mean vector to a field constant in the angular variable. -/
noncomputable def axisymmetricLift (a : MeanVector D) : Oscillation D :=
  fun n x => a n x.1

/-- Add an independent alias without changing any velocity or pressure field. -/
noncomputable def addAxisymmetricAlias (s : State D) (a : MeanVector D) : State D :=
  { s with errors := { s.errors with aliasError := s.errors.aliasError + axisymmetricLift a } }

/-- Remove precisely the specified independent alias from the stored errors. -/
noncomputable def eraseAxisymmetricAlias (s : State D) (a : MeanVector D) : State D :=
  { s with errors := { s.errors with aliasError := s.errors.aliasError - axisymmetricLift a } }

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
@[simp] theorem add_eraseAxisymmetricAlias (s : State D) (a : MeanVector D) :
    addAxisymmetricAlias (eraseAxisymmetricAlias s a) a = s := by
  simp [addAxisymmetricAlias, eraseAxisymmetricAlias]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
@[simp] theorem erase_addAxisymmetricAlias (s : State D) (a : MeanVector D) :
    eraseAxisymmetricAlias (addAxisymmetricAlias s a) a = s := by
  simp [addAxisymmetricAlias, eraseAxisymmetricAlias]

@[simp] theorem stateFullResidual_addAxisymmetricAlias (c : Context D) (s : State D)
    (a : MeanVector D) :
    HarmonicResidual.stateFullResidual c (addAxisymmetricAlias s a) =
      HarmonicResidual.stateFullResidual c s := rfl

@[simp] theorem stateFullResidual_eraseAxisymmetricAlias (c : Context D) (s : State D)
    (a : MeanVector D) :
    HarmonicResidual.stateFullResidual c (eraseAxisymmetricAlias s a) =
      HarmonicResidual.stateFullResidual c s := rfl

theorem stateGoodResidual_addAxisymmetricAlias (c : Context D) (s : State D)
    (a : MeanVector D) (n : ℕ) (x : D × ℝ) (i : Fin 3) :
    HarmonicResidual.stateGoodResidual c (addAxisymmetricAlias s a) n x i =
      HarmonicResidual.stateGoodResidual c s n x i - a n x.1 i := by
  simp only [HarmonicResidual.stateGoodResidual, Pi.sub_apply]
  rw [stateFullResidual_addAxisymmetricAlias]
  simp only [ExcludedErrors.total,
    addAxisymmetricAlias, axisymmetricLift, Pi.add_apply]
  ring

theorem stateGoodResidual_eraseAxisymmetricAlias (c : Context D) (s : State D)
    (a : MeanVector D) (n : ℕ) (x : D × ℝ) (i : Fin 3) :
    HarmonicResidual.stateGoodResidual c (eraseAxisymmetricAlias s a) n x i =
      HarmonicResidual.stateGoodResidual c s n x i + a n x.1 i := by
  simp only [HarmonicResidual.stateGoodResidual, Pi.sub_apply]
  rw [stateFullResidual_eraseAxisymmetricAlias]
  simp only [ExcludedErrors.total,
    eraseAxisymmetricAlias, axisymmetricLift, Pi.add_apply, Pi.sub_apply]
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- Angular integration needs integrability only on this one fiber. -/
theorem angularAverage_sub_axisymmetric (f : OscillatoryScalar D) (a : ScalarField D)
    (n : ℕ) (x : D)
    (hf : IntervalIntegrable (fun θ => f n (x, θ)) volume 0 (2 * Real.pi)) :
    angularAverage (fun m y => f m y - a m y.1) n x =
      angularAverage f n x - a n x := by
  simp only [angularAverage]
  rw [intervalIntegral.integral_sub hf intervalIntegrable_const,
    intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul, sub_div]
  field_simp [Real.pi_ne_zero]

/-- Adding an arbitrary axisymmetric alias leaves the nonconstant residual
unchanged on every angular fiber on which the original residual is integrable. -/
theorem stateGoodWaveResidual_addAxisymmetricAlias (c : Context D) (s : State D)
    (a : MeanVector D) (n : ℕ) (x : D × ℝ) (i : Fin 3)
    (hf : IntervalIntegrable
      (fun θ => HarmonicResidual.stateGoodResidual c s n (x.1, θ) i)
      volume 0 (2 * Real.pi)) :
    HarmonicResidual.stateGoodWaveResidual c (addAxisymmetricAlias s a) n x i =
      HarmonicResidual.stateGoodWaveResidual c s n x i := by
  simp only [HarmonicResidual.stateGoodWaveResidual]
  simp_rw [stateGoodResidual_addAxisymmetricAlias]
  rw [angularAverage_sub_axisymmetric
    (fun m y => HarmonicResidual.stateGoodResidual c s m y i)
    (fun m y => a m y i) n x.1 hf]
  ring

/-- The finite label representation keeps the independent zero mode explicit. -/
structure Representation {ι : Type*} (labels : ℕ → Finset ι)
    (blocks : ι → HarmonicBlock D)
    (gaussianCoeffs aliasCoeffs : ι → HarmonicResidual.BlockCoefficients D)
    (s : State D) (axis : MeanVector D) : Prop where
  velocity : ∀ n x i, s.oscillation n x i = ∑ l ∈ labels n, (blocks l).oscillation n x i
  pressure : ∀ n x, s.oscillatoryPressure n x =
    ∑ l ∈ labels n, (blocks l).oscillatoryPressure n x
  gaussian : ∀ n x i, s.errors.gaussian n x i =
    ∑ l ∈ labels n,
      ((HarmonicResidual.ofBlock (blocks l) (gaussianCoeffs l) (aliasCoeffs l) n).gaussianField x
          i).re
  aliasError : ∀ n x i, s.errors.aliasError n x i =
    (∑ l ∈ labels n,
      ((HarmonicResidual.ofBlock (blocks l) (gaussianCoeffs l) (aliasCoeffs l) n).aliasField x
          i).re) +
      axis n x.1 i

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem Representation.erase {ι : Type*} {labels : ℕ → Finset ι}
    {blocks : ι → HarmonicBlock D}
    {gaussian aliasCoeffs : ι → HarmonicResidual.BlockCoefficients D}
    {s : State D} {axis : MeanVector D}
    (h : Representation labels blocks gaussian aliasCoeffs s axis) :
    HarmonicResidual.BlockRepresentation labels blocks gaussian aliasCoeffs
      (eraseAxisymmetricAlias s axis) where
  velocity := h.velocity
  pressure := h.pressure
  gaussian := h.gaussian
  aliasError := by
    intro n x i
    change s.errors.aliasError n x i - axis n x.1 i = _
    rw [h.aliasError]
    exact add_sub_cancel_right _ _

theorem extractionRegular_erase {ι : Type*} {U : Set D} {c : Context D} {s : State D}
    {labels : ℕ → Finset ι} {blocks : ι → HarmonicBlock D}
    {gaussian aliasCoeffs : ι → HarmonicResidual.BlockCoefficients D} {n : ℕ}
    (h : HarmonicResidual.ExtractionRegular U c s labels blocks gaussian aliasCoeffs n)
    (axis : MeanVector D) :
    HarmonicResidual.ExtractionRegular U c (eraseAxisymmetricAlias s axis)
      labels blocks gaussian aliasCoeffs n :=
  ⟨h.frame, h.base, h.mean, h.pressure, h.blocks, h.gaussian, h.aliasError,
    h.disjoint, h.angular_nonzero⟩

@[simp] theorem residualBlock_erase (c : Context D) (s : State D) (axis : MeanVector D)
    (b : HarmonicBlock D) (gaussian aliasCoeffs : HarmonicResidual.BlockCoefficients D) :
    HarmonicResidual.residualBlock c (eraseAxisymmetricAlias s axis) b gaussian aliasCoeffs =
      HarmonicResidual.residualBlock c s b gaussian aliasCoeffs := rfl

@[simp] theorem stateMeanCoefficientValue_erase {ι : Type*} (labels : ℕ → Finset ι)
    (blocks : ι → HarmonicBlock D)
    (gaussian aliasCoeffs : ι → HarmonicResidual.BlockCoefficients D)
    (c : Context D) (s : State D) (axis : MeanVector D) :
    HarmonicResidual.stateMeanCoefficientValue labels blocks gaussian aliasCoeffs c
      (eraseAxisymmetricAlias s axis) =
      HarmonicResidual.stateMeanCoefficientValue labels blocks gaussian aliasCoeffs c s := rfl

/-- The existing finite harmonic representation implies continuity in the
angular variable even when the independent base error is not regular. -/
theorem represented_goodResidual_angular_continuous {ι : Type*} {U : Set D}
    (hU : IsOpen U) {c : Context D} {s : State D} {labels : ℕ → Finset ι}
    {blocks : ι → HarmonicBlock D}
    {gaussian aliasCoeffs : ι → HarmonicResidual.BlockCoefficients D}
    (hrep : HarmonicResidual.BlockRepresentation labels blocks gaussian aliasCoeffs s) {n : ℕ}
    (h : HarmonicResidual.ExtractionRegular U c s labels blocks gaussian aliasCoeffs n)
    {x : D} (hx : x ∈ U) (i : Fin 3) :
    Continuous (fun θ => HarmonicResidual.stateGoodResidual c s n (x, θ) i) := by
  let data := fun l => HarmonicResidual.ofBlock (blocks l) (gaussian l) (aliasCoeffs l) n
  have he : (fun θ => HarmonicResidual.stateGoodResidual c s n (x, θ) i) =
      fun θ => (HarmonicResidual.meanCoefficients (HarmonicResidual.contextFrame c n)
        (HarmonicResidual.contextBase c n) (HarmonicResidual.stateMean s n)
        (fun y => (s.pressure n y : ℂ)) i 0 x).re +
        HarmonicResidual.contextVirtual c n x i +
        ∑ l ∈ labels n, (HarmonicFields.field
          ((data l).residualCoefficients (HarmonicResidual.contextFrame c n)
            (HarmonicResidual.contextBase c n) (HarmonicResidual.stateMean s n) i)
          (data l).frequency (data l).phase (data l).angularFrequency (x, θ)).re := by
    funext θ
    rw [hrep.goodResidual_eq c n (x, θ) i]
    exact HarmonicResidual.goodResidual_grouped (labels n) data hU h.frame _ _ _ _
      h.base h.mean (Complex.ofRealCLM.contDiff.comp_contDiffOn h.pressure)
      h.blocks h.dataDisjoint ⟨hx, mem_univ θ⟩ i
  rw [he]
  exact continuous_const.add (continuous_finsetSum (labels n) (fun l _ =>
    Complex.continuous_re.comp (HarmonicFields.field_angular_continuous _ _ _ _ _)))

/-- An arbitrary independent alias does not disturb angular continuity. -/
theorem Representation.goodResidual_angular_continuous {ι : Type*} {U : Set D}
    (hU : IsOpen U) {c : Context D} {s : State D} {labels : ℕ → Finset ι}
    {blocks : ι → HarmonicBlock D}
    {gaussian aliasCoeffs : ι → HarmonicResidual.BlockCoefficients D}
    {axis : MeanVector D}
    (hrep : Representation labels blocks gaussian aliasCoeffs s axis) {n : ℕ}
    (h : HarmonicResidual.ExtractionRegular U c s labels blocks gaussian aliasCoeffs n)
    {x : D} (hx : x ∈ U) (i : Fin 3) :
    Continuous (fun θ => HarmonicResidual.stateGoodResidual c s n (x, θ) i) := by
  have hc := represented_goodResidual_angular_continuous hU hrep.erase
    (extractionRegular_erase h axis) hx i
  have he : (fun θ => HarmonicResidual.stateGoodResidual c s n (x, θ) i) =
      fun θ => HarmonicResidual.stateGoodResidual c (eraseAxisymmetricAlias s axis)
        n (x, θ) i - axis n x i := by
    funext θ
    rw [stateGoodResidual_eraseAxisymmetricAlias]
    exact (add_sub_cancel_right _ _).symm
  rw [he]
  exact hc.sub continuous_const

/-- Actual nonconstant residual grouping, with no smoothness or support
assumption on the independent axisymmetric alias. -/
theorem stateGoodWaveResidual_grouped {ι : Type*} {U : Set D} (hU : IsOpen U)
    {c : Context D} {s : State D} {labels : ℕ → Finset ι}
    {blocks : ι → HarmonicBlock D}
    {gaussian aliasCoeffs : ι → HarmonicResidual.BlockCoefficients D}
    {axis : MeanVector D}
    (hrep : Representation labels blocks gaussian aliasCoeffs s axis) {n : ℕ}
    (h : HarmonicResidual.ExtractionRegular U c s labels blocks gaussian aliasCoeffs n)
    {x : D × ℝ} (hx : x ∈ HarmonicResidual.liftDomain U) (i : Fin 3) :
    HarmonicResidual.stateGoodWaveResidual c s n x i =
      ∑ l ∈ labels n,
        (HarmonicResidual.residualBlock c s (blocks l) (gaussian l) (aliasCoeffs l)).oscillation n
            x i := by
  have hr := extractionRegular_erase h axis
  have hc := represented_goodResidual_angular_continuous hU hrep.erase hr hx.1 i
  have he := stateGoodWaveResidual_addAxisymmetricAlias c (eraseAxisymmetricAlias s axis)
    axis n x i (hc.intervalIntegrable _ _)
  rw [add_eraseAxisymmetricAlias] at he
  rw [he, HarmonicResidual.stateGoodWaveResidual_grouped hU hrep.erase hr hx i]
  rfl

/-- The independent alias changes the actual zero mode by its negative. -/
theorem stateGoodResidual_angularAverage {ι : Type*} {U : Set D} (hU : IsOpen U)
    {c : Context D} {s : State D} {labels : ℕ → Finset ι}
    {blocks : ι → HarmonicBlock D}
    {gaussian aliasCoeffs : ι → HarmonicResidual.BlockCoefficients D}
    {axis : MeanVector D}
    (hrep : Representation labels blocks gaussian aliasCoeffs s axis) {n : ℕ}
    (h : HarmonicResidual.ExtractionRegular U c s labels blocks gaussian aliasCoeffs n)
    {x : D} (hx : x ∈ U) (i : Fin 3) :
    angularAverage (fun m y => HarmonicResidual.stateGoodResidual c s m y i) n x =
      HarmonicResidual.stateMeanCoefficientValue labels blocks gaussian aliasCoeffs
        c s n x i - axis n x i := by
  have hr := extractionRegular_erase h axis
  have hc := represented_goodResidual_angular_continuous hU hrep.erase hr hx i
  have he := angularAverage_sub_axisymmetric
    (fun m y => HarmonicResidual.stateGoodResidual c (eraseAxisymmetricAlias s axis) m y i)
    (fun m y => axis m y i) n x (hc.intervalIntegrable _ _)
  have hb : (fun m y => HarmonicResidual.stateGoodResidual c
      (eraseAxisymmetricAlias s axis) m y i - axis m y.1 i) =
      (fun m y => HarmonicResidual.stateGoodResidual c s m y i) := by
    funext m y
    rw [stateGoodResidual_eraseAxisymmetricAlias]
    exact add_sub_cancel_right _ _
  rw [hb, ← HarmonicResidual.stateMeanCoefficientValue_eq_average hU hrep.erase hr hx i,
    stateMeanCoefficientValue_erase] at he
  exact he

/-- The complete residual retains the actual excluded errors and the corrected
mean mode. In particular the independent alias is never silently discarded. -/
theorem stateFullResidual_reconstructed {ι : Type*} {U : Set D} (hU : IsOpen U)
    {c : Context D} {s : State D} {labels : ℕ → Finset ι}
    {blocks : ι → HarmonicBlock D}
    {gaussian aliasCoeffs : ι → HarmonicResidual.BlockCoefficients D}
    {axis : MeanVector D}
    (hrep : Representation labels blocks gaussian aliasCoeffs s axis) {n : ℕ}
    (h : HarmonicResidual.ExtractionRegular U c s labels blocks gaussian aliasCoeffs n)
    {x : D × ℝ} (hx : x ∈ HarmonicResidual.liftDomain U) (i : Fin 3) :
    HarmonicResidual.stateFullResidual c s n x i =
      (∑ l ∈ labels n,
        (HarmonicResidual.residualBlock c s (blocks l) (gaussian l) (aliasCoeffs l)).oscillation n
            x i) +
      (HarmonicResidual.stateMeanCoefficientValue labels blocks gaussian aliasCoeffs
        c s n x.1 i - axis n x.1 i) + s.errors.total n x i := by
  have he := stateGoodWaveResidual_grouped hU hrep h hx i
  simp only [HarmonicResidual.stateGoodWaveResidual] at he
  rw [stateGoodResidual_angularAverage hU hrep h hx.1 i] at he
  simp only [HarmonicResidual.stateGoodResidual, Pi.sub_apply] at he
  linarith

end NavierStokes.AxisymmetricResidualGrouping
