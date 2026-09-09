/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ParticularWaveBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.LiftedMeanResidual

@[expose] public section

/-!
# Isometric reindexing of the actual correction state

Pullback along `e : D ≃ₗᵢ[ℝ] E` sends fields on `E` to fields on `D`.
Vector directions are transported by `e.symm`.  The final specialization is
the existing associator from `PressureStream.Lift S` to `((ℝ × S) × Plane)`.
-/

noncomputable section

namespace NavierStokes.StateReindex

open Set Filter Function HarmonicCalculus
open scoped Topology ContDiff BigOperators ComplexConjugate

variable {D E F : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def cylinder (e : D ≃ₗᵢ[ℝ] E) : (D × ℝ) ≃ₗᵢ[ℝ] (E × ℝ) where
  toLinearEquiv := e.toLinearEquiv.prodCongr (LinearEquiv.refl ℝ ℝ)
  norm_map' x := by
    change max ‖e x.1‖ ‖x.2‖ = max ‖x.1‖ ‖x.2‖
    rw [e.norm_map]

@[simp] theorem cylinder_apply (e : D ≃ₗᵢ[ℝ] E) (x : D × ℝ) :
    cylinder e x = (e x.1, x.2) := rfl

@[simp] theorem cylinder_symm_apply (e : D ≃ₗᵢ[ℝ] E) (x : E × ℝ) :
    (cylinder e).symm x = (e.symm x.1, x.2) := rfl

noncomputable def vector (e : D ≃ₗᵢ[ℝ] E) (V : E → E) : D → D :=
  ParticularWaveBounds.reindexVector e V

theorem fderiv_pull (e : D ≃ₗᵢ[ℝ] E) (f : E → F) (x v : D) :
    fderiv ℝ (fun y => f (e y)) x v = fderiv ℝ f (e x) (e v) := by
  change fderiv ℝ (f ∘ e.toContinuousLinearEquiv) x v = _
  rw [e.toContinuousLinearEquiv.comp_right_fderiv]
  rfl

theorem along_pull (e : D ≃ₗᵢ[ℝ] E) (V : E → E) (f : E → F) :
    along (vector e V) (fun x => f (e x)) = fun x => along V f (e x) := by
  funext x
  unfold along vector ParticularWaveBounds.reindexVector
  rw [fderiv_pull, e.apply_symm_apply]

theorem along_pull_component {ι : Type*} (e : D ≃ₗᵢ[ℝ] E) (V : E → E)
    (f : E → ι → F) (i : ι) :
    along (vector e V) (fun x => f (e x) i) =
      fun x => along V (fun y => f y i) (e x) := along_pull e V (fun y => f y i)

theorem iteratedFDeriv_pull (e : D ≃ₗᵢ[ℝ] E) (f : E → F) (m : ℕ) (x : D) :
    iteratedFDeriv ℝ m (fun y => f (e y)) x =
      (iteratedFDeriv ℝ m f (e x)).compContinuousLinearMap
        (fun _ => e.toContinuousLinearEquiv.toContinuousLinearMap) := by
  have h := e.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f
    uniqueDiffOn_univ (mem_univ (e x)) m
  simp only [iteratedFDerivWithin_univ, preimage_univ, Function.comp_def] at h
  exact h

theorem norm_iteratedFDeriv_pull (e : D ≃ₗᵢ[ℝ] E) (f : E → F) (m : ℕ) (x : D) :
    ‖iteratedFDeriv ℝ m (fun y => f (e y)) x‖ = ‖iteratedFDeriv ℝ m f (e x)‖ :=
  e.norm_iteratedFDeriv_comp_right f x m

noncomputable def field (e : D ≃ₗᵢ[ℝ] E) (f : MeanIncrementBounds.Field E) :
    MeanIncrementBounds.Field D := fun n x => f n (e x)

noncomputable def triple (e : D ≃ₗᵢ[ℝ] E) (b : MeanIncrementBounds.Triple E) :
    MeanIncrementBounds.Triple D := ⟨field e b.radial, field e b.angular, field e b.axial⟩

noncomputable def operators (e : D ≃ₗᵢ[ℝ] E) (o : MeanIncrementBounds.Operators E) :
    MeanIncrementBounds.Operators D where
  epsilon := o.epsilon
  radialFrequency := o.radialFrequency
  fastCoefficient := o.fastCoefficient
  radius := fun x => o.radius (e x)
  radialProfile := fun x => o.radialProfile (e x)
  eR := e.symm o.eR
  eZ := e.symm o.eZ
  eT := e.symm o.eT
  vR := e.symm o.vR
  vT := e.symm o.vT

noncomputable def context (e : D ≃ₗᵢ[ℝ] E) (c : CorrectionState.Context E) :
    CorrectionState.Context D where
  operators := operators e c.operators
  base := triple e c.base
  virtualTheta := field e c.virtualTheta
  virtualAxial := field e c.virtualAxial

noncomputable def oscillation (e : D ≃ₗᵢ[ℝ] E) (u : CorrectionState.Oscillation E) :
    CorrectionState.Oscillation D := fun n x => u n (cylinder e x)

noncomputable def errors (e : D ≃ₗᵢ[ℝ] E) (a : CorrectionState.ExcludedErrors E) :
    CorrectionState.ExcludedErrors D :=
  ⟨oscillation e a.base, oscillation e a.gaussian, oscillation e a.aliasError⟩

noncomputable def state (e : D ≃ₗᵢ[ℝ] E) (u : CorrectionState.State E) : CorrectionState.State D
  where
  mean := triple e u.mean
  pressure := field e u.pressure
  oscillation := oscillation e u.oscillation
  oscillatoryPressure := fun n x => u.oscillatoryPressure n (cylinder e x)
  errors := errors e u.errors

theorem fderiv_field (e : D ≃ₗᵢ[ℝ] E) (f : MeanIncrementBounds.Field E)
    (n : ℕ) (x : D) (v : E) :
    fderiv ℝ (field e f n) x (e.symm v) = fderiv ℝ (f n) (e x) v := by
  change fderiv ℝ (fun y => f n (e y)) x (e.symm v) = _
  rw [fderiv_pull, e.apply_symm_apply]

theorem dr_pull (e : D ≃ₗᵢ[ℝ] E) (o : MeanIncrementBounds.Operators E)
    (f : MeanIncrementBounds.Field E) : (operators e o).dr (field e f) = field e (o.dr f) := by
  funext n x
  simp only [MeanIncrementBounds.Operators.dr, WeightedClasses.graphDerivative,
    operators, fderiv_field, field]

theorem dz_pull (e : D ≃ₗᵢ[ℝ] E) (o : MeanIncrementBounds.Operators E)
    (f : MeanIncrementBounds.Field E) : (operators e o).dz (field e f) = field e (o.dz f) := by
  funext n x
  simp only [MeanIncrementBounds.Operators.dz, operators, fderiv_field, field]

theorem time_pull (e : D ≃ₗᵢ[ℝ] E) (o : MeanIncrementBounds.Operators E)
    (f : MeanIncrementBounds.Field E) : (operators e o).time (field e f) = field e (o.time f) := by
  funext n x
  simp only [MeanIncrementBounds.Operators.time, MeanIncrementBounds.Operators.slowTime,
    MeanIncrementBounds.Operators.fastTime, operators, fderiv_field, field, Pi.add_apply]

theorem radialDiv_pull (e : D ≃ₗᵢ[ℝ] E) (o : MeanIncrementBounds.Operators E)
    (k : ℝ) (f : MeanIncrementBounds.Field E) :
    (operators e o).radialDiv k (field e f) = field e (o.radialDiv k f) := by
  unfold MeanIncrementBounds.Operators.radialDiv
  rw [dr_pull]
  rfl

theorem viscosity_pull (e : D ≃ₗᵢ[ℝ] E) (o : MeanIncrementBounds.Operators E)
    (k : ℝ) (f : MeanIncrementBounds.Field E) :
    (operators e o).viscosity k (field e f) = field e (o.viscosity k f) := by
  unfold MeanIncrementBounds.Operators.viscosity
  rw [dr_pull, dr_pull, dz_pull, dz_pull]
  rfl

theorem angularAverage_pull (e : D ≃ₗᵢ[ℝ] E) (f : CorrectionState.OscillatoryScalar E) :
    CorrectionState.angularAverage (fun n x => f n (cylinder e x)) =
      field e (CorrectionState.angularAverage f) := rfl

theorem covariance_pull (e : D ≃ₗᵢ[ℝ] E) (u : CorrectionState.State E) (i j : Fin 3) :
    (state e u).covariance i j = field e (u.covariance i j) := rfl

theorem totalErrors_pull (e : D ≃ₗᵢ[ℝ] E) (a : CorrectionState.ExcludedErrors E) :
    (errors e a).total = oscillation e a.total := rfl

theorem totalVelocity_pull (e : D ≃ₗᵢ[ℝ] E)
    (c : CorrectionState.Context E) (u : CorrectionState.State E) :
    (state e u).totalVelocity (context e c) = oscillation e (u.totalVelocity c) := rfl

theorem totalPressure_pull (e : D ≃ₗᵢ[ℝ] E) (u : CorrectionState.State E) :
    (state e u).totalPressureIncrement =
      fun n x => u.totalPressureIncrement n (cylinder e x) := rfl

/-! ## Finite harmonic coefficients -/

noncomputable def coefficients (e : D ≃ₗᵢ[ℝ] E) (a : HarmonicFields.Coefficients E) :
    HarmonicFields.Coefficients D :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapRange (fun f : E → ℂ => fun x => f (e x)) rfl a.coeff)

@[simp] theorem coefficients_apply (e : D ≃ₗᵢ[ℝ] E) (a : HarmonicFields.Coefficients E)
    (j : ℤ) (x : D) : coefficients e a j x = a j (e x) := rfl

theorem coefficients_fun (e : D ≃ₗᵢ[ℝ] E) (a : HarmonicFields.Coefficients E) (j : ℤ) :
    coefficients e a j = fun x => a j (e x) := rfl

theorem coefficients_support (e : D ≃ₗᵢ[ℝ] E) (a : HarmonicFields.Coefficients E) :
    (coefficients e a).support = a.support := by
  ext j
  simp only [Finsupp.mem_support_iff]
  apply not_congr
  constructor
  · intro h
    funext y
    obtain ⟨x, rfl⟩ := e.surjective y
    exact congrFun h x
  · intro h
    funext x
    exact congrFun h (e x)

@[simp] theorem coefficients_zero (e : D ≃ₗᵢ[ℝ] E) : coefficients e 0 = 0 := by
  ext j x
  rfl

theorem coefficients_add (e : D ≃ₗᵢ[ℝ] E) (a b : HarmonicFields.Coefficients E) :
    coefficients e (a + b) = coefficients e a + coefficients e b := by
  ext j x
  rfl

theorem coefficients_sub (e : D ≃ₗᵢ[ℝ] E) (a b : HarmonicFields.Coefficients E) :
    coefficients e (a - b) = coefficients e a - coefficients e b := by
  ext j x
  rfl

theorem coefficients_neg (e : D ≃ₗᵢ[ℝ] E) (a : HarmonicFields.Coefficients E) :
    coefficients e (-a) = -coefficients e a := by
  ext j x
  rfl

theorem coefficients_mul (e : D ≃ₗᵢ[ℝ] E) (a b : HarmonicFields.Coefficients E) :
    coefficients e (a * b) = coefficients e a * coefficients e b := by
  ext j x
  simp only [coefficients_apply, HarmonicFields.convolution_apply, coefficients_support]

theorem coefficients_constant (e : D ≃ₗᵢ[ℝ] E) (a : E → ℂ) :
    coefficients e (HarmonicFields.constantCoefficient a) =
      HarmonicFields.constantCoefficient (fun x => a (e x)) := by
  ext j x
  by_cases hj : j = 0
  · subst j
    simp [coefficients_apply, HarmonicFields.constantCoefficient]
  · simp [coefficients_apply, HarmonicFields.constantCoefficient, hj]

theorem evaluate_pull (e : D ≃ₗᵢ[ℝ] E) (a : HarmonicFields.Coefficients E)
    (x : D) (theta : ℝ) :
    HarmonicFields.evaluate (coefficients e a) x theta = HarmonicFields.evaluate a (e x) theta := by
  simp only [HarmonicFields.evaluate, Finsupp.sum, coefficients_support, coefficients_apply]

theorem harmonicField_pull (e : D ≃ₗᵢ[ℝ] E) (a : HarmonicFields.Coefficients E)
    (k : ℝ) (Phi : E → ℝ) (kp : ℤ) (x : D × ℝ) :
    HarmonicFields.field (coefficients e a) k (fun y => Phi (e y)) kp x =
      HarmonicFields.field a k Phi kp (cylinder e x) := by
  exact evaluate_pull e a x.1 _

theorem coefficientMass_pull (e : D ≃ₗᵢ[ℝ] E) (a : HarmonicFields.Coefficients E) (x : D) :
    HarmonicFields.coefficientMass (coefficients e a) x = HarmonicFields.coefficientMass a (e x) :=
      by
  simp only [HarmonicFields.coefficientMass, coefficients_support, coefficients_apply]

theorem bandLimited_pull (e : D ≃ₗᵢ[ℝ] E) {a : HarmonicFields.Coefficients E} {N : ℕ}
    (ha : HarmonicFields.BandLimited a N) : HarmonicFields.BandLimited (coefficients e a) N := by
  simpa only [HarmonicFields.BandLimited, coefficients_support] using ha

theorem differentiate_pull (e : D ≃ₗᵢ[ℝ] E) (V : E → E) (k : ℝ)
    (Phi : E → ℝ) (a : HarmonicFields.Coefficients E) :
    HarmonicFields.differentiate (vector e V) k (fun x => Phi (e x)) (coefficients e a) =
      coefficients e (HarmonicFields.differentiate V k Phi a) := by
  ext j x
  simp only [HarmonicFields.differentiate_apply, coefficients_apply, coefficients_fun,
    HarmonicFields.derivativeCoefficient, along_pull]

theorem angularDifferentiate_pull (e : D ≃ₗᵢ[ℝ] E) (kp : ℤ)
    (a : HarmonicFields.Coefficients E) :
    HarmonicFields.angularDifferentiate kp (coefficients e a) =
      coefficients e (HarmonicFields.angularDifferentiate kp a) := by
  ext j x
  rfl

theorem realCoefficients_pull (e : D ≃ₗᵢ[ℝ] E) (a : HarmonicFields.Coefficients E) :
    HarmonicResidual.realCoefficients (coefficients e a) =
      coefficients e (HarmonicResidual.realCoefficients a) := by
  ext j x
  simp only [HarmonicResidual.realCoefficients_apply, coefficients_apply]

theorem nonconstant_pull (e : D ≃ₗᵢ[ℝ] E) (a : HarmonicFields.Coefficients E) :
    HarmonicResidual.nonconstant (coefficients e a) =
      coefficients e (HarmonicResidual.nonconstant a) := by
  ext j x
  by_cases hj : j = 0
  · subst j
    simp [HarmonicResidual.nonconstant, coefficients_apply]
  · simp [HarmonicResidual.nonconstant, coefficients_apply, hj]

noncomputable def block (e : D ≃ₗᵢ[ℝ] E) (b : CorrectionState.HarmonicBlock E) :
    CorrectionState.HarmonicBlock D where
  velocity n i := coefficients e (b.velocity n i)
  pressure n := coefficients e (b.pressure n)
  frequency := b.frequency
  phase n x := b.phase n (e x)
  angularFrequency := b.angularFrequency

noncomputable def blockCoefficients (e : D ≃ₗᵢ[ℝ] E) (a : HarmonicResidual.BlockCoefficients E) :
    HarmonicResidual.BlockCoefficients D := fun n i => coefficients e (a n i)

theorem block_oscillation (e : D ≃ₗᵢ[ℝ] E) (b : CorrectionState.HarmonicBlock E) :
    (block e b).oscillation = oscillation e b.oscillation := by
  funext n x i
  exact congrArg Complex.re (harmonicField_pull e (b.velocity n i) (b.frequency n)
    (b.phase n) (b.angularFrequency n) x)

theorem block_pressure (e : D ≃ₗᵢ[ℝ] E) (b : CorrectionState.HarmonicBlock E) :
    (block e b).oscillatoryPressure = fun n x => b.oscillatoryPressure n (cylinder e x) := by
  funext n x
  exact congrArg Complex.re (harmonicField_pull e (b.pressure n) (b.frequency n)
    (b.phase n) (b.angularFrequency n) x)

/-! ## The actual coefficient residual -/

noncomputable def frame (e : D ≃ₗᵢ[ℝ] E) (g : HarmonicResidual.Frame E) : HarmonicResidual.Frame D
  where
  radius := fun x => g.radius (e x)
  radial := vector e g.radial
  axial := vector e g.axial
  time := vector e g.time
  viscosity := g.viscosity

theorem rotate_pull (e : D ≃ₗᵢ[ℝ] E) (a : HarmonicResidual.VectorCoefficients E) :
    HarmonicResidual.rotate (fun i => coefficients e (a i)) =
      fun i => coefficients e (HarmonicResidual.rotate a i) := by
  funext i
  fin_cases i <;> simp [HarmonicResidual.rotate, coefficients_neg]

theorem scalarLaplacian_pull (e : D ≃ₗᵢ[ℝ] E) (g : HarmonicResidual.Frame E)
    (k : ℝ) (Phi : E → ℝ) (kp : ℤ) (a : HarmonicFields.Coefficients E) :
    HarmonicResidual.scalarLaplacian (frame e g) k (fun x => Phi (e x)) kp (coefficients e a) =
      coefficients e (HarmonicResidual.scalarLaplacian g k Phi kp a) := by
  simp only [HarmonicResidual.scalarLaplacian, frame, coefficients_add, coefficients_mul,
    coefficients_constant, differentiate_pull, angularDifferentiate_pull]

theorem vectorLaplacian_pull (e : D ≃ₗᵢ[ℝ] E) (g : HarmonicResidual.Frame E)
    (k : ℝ) (Phi : E → ℝ) (kp : ℤ) (a : HarmonicResidual.VectorCoefficients E) :
    HarmonicResidual.vectorLaplacian (frame e g) k (fun x => Phi (e x)) kp
      (fun i => coefficients e (a i)) =
      fun i => coefficients e (HarmonicResidual.vectorLaplacian g k Phi kp a i) := by
  funext i
  simp only [HarmonicResidual.vectorLaplacian, scalarLaplacian_pull, angularDifferentiate_pull,
    rotate_pull]
  simp only [frame, coefficients_add,
    coefficients_mul, coefficients_constant]

theorem transportCoefficients_pull (e : D ≃ₗᵢ[ℝ] E) (g : HarmonicResidual.Frame E)
    (k : ℝ) (Phi : E → ℝ) (kp : ℤ) (a b : HarmonicResidual.VectorCoefficients E) :
    HarmonicResidual.transport (frame e g) k (fun x => Phi (e x)) kp
      (fun i => coefficients e (a i)) (fun i => coefficients e (b i)) =
      fun i => coefficients e (HarmonicResidual.transport g k Phi kp a b i) := by
  funext i
  simp only [HarmonicResidual.transport, frame, differentiate_pull, angularDifferentiate_pull,
    rotate_pull, coefficients_add, coefficients_mul, coefficients_constant]

theorem gradientCoefficients_pull (e : D ≃ₗᵢ[ℝ] E) (g : HarmonicResidual.Frame E)
    (k : ℝ) (Phi : E → ℝ) (kp : ℤ) (a : HarmonicFields.Coefficients E) :
    HarmonicResidual.gradient (frame e g) k (fun x => Phi (e x)) kp (coefficients e a) =
      fun i => coefficients e (HarmonicResidual.gradient g k Phi kp a i) := by
  funext i
  fin_cases i <;> simp [HarmonicResidual.gradient, frame, differentiate_pull,
    angularDifferentiate_pull, coefficients_mul, coefficients_constant]

theorem linearCoefficients_pull (e : D ≃ₗᵢ[ℝ] E) (g : HarmonicResidual.Frame E)
    (k : ℝ) (Phi : E → ℝ) (kp : ℤ) (B a : HarmonicResidual.VectorCoefficients E)
    (p : HarmonicFields.Coefficients E) :
    HarmonicResidual.linearResidual (frame e g) k (fun x => Phi (e x)) kp
      (fun i => coefficients e (B i)) (fun i => coefficients e (a i)) (coefficients e p) =
      fun i => coefficients e (HarmonicResidual.linearResidual g k Phi kp B a p i) := by
  funext i
  simp only [HarmonicResidual.linearResidual, transportCoefficients_pull, vectorLaplacian_pull,
    gradientCoefficients_pull]
  simp only [frame, differentiate_pull, coefficients_add,
    coefficients_sub, coefficients_mul, coefficients_constant]

theorem nonlinearCoefficients_pull (e : D ≃ₗᵢ[ℝ] E) (g : HarmonicResidual.Frame E)
    (k : ℝ) (Phi : E → ℝ) (kp : ℤ) (B a : HarmonicResidual.VectorCoefficients E)
    (p : HarmonicFields.Coefficients E) :
    HarmonicResidual.nonlinearResidual (frame e g) k (fun x => Phi (e x)) kp
      (fun i => coefficients e (B i)) (fun i => coefficients e (a i)) (coefficients e p) =
      fun i => coefficients e (HarmonicResidual.nonlinearResidual g k Phi kp B a p i) := by
  funext i
  simp only [HarmonicResidual.nonlinearResidual, linearCoefficients_pull,
    transportCoefficients_pull, coefficients_add]

theorem constantVector_pull (e : D ≃ₗᵢ[ℝ] E) (B : E → ComplexVector) :
    HarmonicResidual.constantVector (fun x => B (e x)) =
      fun i => coefficients e (HarmonicResidual.constantVector B i) := by
  funext i
  exact (coefficients_constant e (fun x => B x i)).symm

noncomputable def label (e : D ≃ₗᵢ[ℝ] E) (d : HarmonicResidual.LabelData E) :
    HarmonicResidual.LabelData D where
  frequency := d.frequency
  phase := fun x => d.phase (e x)
  angularFrequency := d.angularFrequency
  velocity := fun i => coefficients e (d.velocity i)
  pressure := coefficients e d.pressure
  gaussian := fun i => coefficients e (d.gaussian i)
  aliasError := fun i => coefficients e (d.aliasError i)

theorem labelResidual_pull (e : D ≃ₗᵢ[ℝ] E) (d : HarmonicResidual.LabelData E)
    (g : HarmonicResidual.Frame E) (B M : E → ComplexVector) :
    (label e d).residualCoefficients (frame e g) (fun x => B (e x)) (fun x => M (e x)) =
      fun i => coefficients e (d.residualCoefficients g B M i) := by
  have hbase : HarmonicResidual.constantVector ((fun x => B (e x)) + (fun x => M (e x))) =
      fun i => coefficients e (HarmonicResidual.constantVector (B + M) i) :=
    constantVector_pull e (B + M)
  funext i
  unfold HarmonicResidual.LabelData.residualCoefficients
  simp only [label]
  rw [← realCoefficients_pull, coefficients_sub, coefficients_sub, hbase,
    nonlinearCoefficients_pull]

theorem labelWaveResidual_pull (e : D ≃ₗᵢ[ℝ] E) (d : HarmonicResidual.LabelData E)
    (g : HarmonicResidual.Frame E) (B M : E → ComplexVector) :
    (label e d).waveResidualCoefficients (frame e g) (fun x => B (e x)) (fun x => M (e x)) =
      fun i => coefficients e (d.waveResidualCoefficients g B M i) := by
  funext i
  simp only [HarmonicResidual.LabelData.waveResidualCoefficients, labelResidual_pull,
    nonconstant_pull]

theorem contextFrame_pull (e : D ≃ₗᵢ[ℝ] E) (c : CorrectionState.Context E) (n : ℕ) :
    HarmonicResidual.contextFrame (context e c) n = frame e (HarmonicResidual.contextFrame c n) :=
      by
  unfold HarmonicResidual.contextFrame context operators frame
  congr 1 <;> funext x <;>
    simp only [vector, ParticularWaveBounds.reindexVector, map_add, map_smul, map_sub]

theorem contextBase_pull (e : D ≃ₗᵢ[ℝ] E) (c : CorrectionState.Context E) (n : ℕ) :
    HarmonicResidual.contextBase (context e c) n = fun x => HarmonicResidual.contextBase c n (e x)
      := rfl

theorem stateMean_pull (e : D ≃ₗᵢ[ℝ] E) (u : CorrectionState.State E) (n : ℕ) :
    HarmonicResidual.stateMean (state e u) n = fun x => HarmonicResidual.stateMean u n (e x) := rfl

theorem ofBlock_pull (e : D ≃ₗᵢ[ℝ] E) (b : CorrectionState.HarmonicBlock E)
    (G A : HarmonicResidual.BlockCoefficients E) (n : ℕ) :
    HarmonicResidual.ofBlock (block e b) (blockCoefficients e G) (blockCoefficients e A) n =
      label e (HarmonicResidual.ofBlock b G A n) := by
  simp only [HarmonicResidual.ofBlock, block, label, realCoefficients_pull]
  rfl

/-- Exact reindexing of the stripped nonzero coefficients of the actual
current-state residual, including Gaussian and alias subtraction. -/
theorem residualBlock_pull (e : D ≃ₗᵢ[ℝ] E)
    (c : CorrectionState.Context E) (u : CorrectionState.State E)
    (b : CorrectionState.HarmonicBlock E) (G A : HarmonicResidual.BlockCoefficients E) :
    HarmonicResidual.residualBlock (context e c) (state e u) (block e b)
      (blockCoefficients e G) (blockCoefficients e A) =
      block e (HarmonicResidual.residualBlock c u b G A) := by
  change CorrectionState.HarmonicBlock.mk _ _ _ _ _ = CorrectionState.HarmonicBlock.mk _ _ _ _ _
  congr 1
  · funext n
    rw [ofBlock_pull, contextFrame_pull, contextBase_pull, stateMean_pull, labelWaveResidual_pull]
    rfl

/-! ## The full differential residual -/

theorem scalarLaplacian_field_pull (e : D ≃ₗᵢ[ℝ] E) (R : E → ℝ)
    (Vr Vt Vz : E → E) (f : E → F) (x : D) :
    HarmonicCalculus.cylindricalLaplacian (fun y => R (e y))
      (vector e Vr) (vector e Vt) (vector e Vz) (fun y => f (e y)) x =
      HarmonicCalculus.cylindricalLaplacian R Vr Vt Vz f (e x) := by
  simp only [HarmonicCalculus.cylindricalLaplacian, along_pull]

theorem scalarLaplacian_component_pull {ι : Type*} (e : D ≃ₗᵢ[ℝ] E) (R : E → ℝ)
    (Vr Vt Vz : E → E) (f : E → ι → F) (i : ι) (x : D) :
    HarmonicCalculus.cylindricalLaplacian (fun y => R (e y))
      (vector e Vr) (vector e Vt) (vector e Vz) (fun y => f (e y) i) x =
      HarmonicCalculus.cylindricalLaplacian R Vr Vt Vz (fun y => f y i) (e x) :=
  scalarLaplacian_field_pull e R Vr Vt Vz (fun y => f y i) x

theorem transport_field_pull (e : D ≃ₗᵢ[ℝ] E) (R : E → ℝ)
    (Vr Vt Vz : E → E) (u v : E → ComplexVector) (x : D) :
    LinearWaveResidual.transport (fun y => R (e y)) (vector e Vr) (vector e Vt) (vector e Vz)
      (fun y => u (e y)) (fun y => v (e y)) x =
      LinearWaveResidual.transport R Vr Vt Vz u v (e x) := by
  funext i
  simp only [LinearWaveResidual.transport, along_pull_component]

theorem vectorLaplacian_field_pull (e : D ≃ₗᵢ[ℝ] E) (R : E → ℝ)
    (Vr Vt Vz : E → E) (a : E → ComplexVector) (x : D) :
    HarmonicCalculus.cylindricalVectorLaplacian (fun y => R (e y))
      (vector e Vr) (vector e Vt) (vector e Vz) (fun y => a (e y)) x =
      HarmonicCalculus.cylindricalVectorLaplacian R Vr Vt Vz a (e x) := by
  funext i
  simp only [HarmonicCalculus.cylindricalVectorLaplacian, scalarLaplacian_component_pull,
    along_pull_component]

theorem linearResidual_field_pull (e : D ≃ₗᵢ[ℝ] E) (epsilon : ℝ) (R : E → ℝ)
    (Vr Vt Vz Vtime : E → E) (B a : E → ComplexVector) (p : E → ℂ) (x : D) :
    LinearWaveResidual.linearResidual epsilon (fun y => R (e y))
      (vector e Vr) (vector e Vt) (vector e Vz) (vector e Vtime)
      (fun y => B (e y)) (fun y => a (e y)) (fun y => p (e y)) x =
      LinearWaveResidual.linearResidual epsilon R Vr Vt Vz Vtime B a p (e x) := by
  funext i
  simp only [LinearWaveResidual.linearResidual, LinearWaveResidual.gradient,
    transport_field_pull, vectorLaplacian_field_pull, along_pull, along_pull_component]

theorem radialDirection_pull (e : D ≃ₗᵢ[ℝ] E) (c : CorrectionState.Context E) (n : ℕ) :
    LiftedMeanResidual.radialDirection (context e c) n =
      vector (cylinder e) (LiftedMeanResidual.radialDirection c n) := by
  funext x
  simp only [LiftedMeanResidual.radialDirection, LiftedMeanResidual.liftDirection,
    LiftedMeanResidual.radialVector, context, operators, vector, ParticularWaveBounds.reindexVector,
    cylinder_apply, cylinder_symm_apply, map_add, map_smul]

theorem axialDirection_pull (e : D ≃ₗᵢ[ℝ] E) (c : CorrectionState.Context E) (n : ℕ) :
    LiftedMeanResidual.axialDirection (context e c) n =
      vector (cylinder e) (LiftedMeanResidual.axialDirection c n) := by
  funext x
  simp only [LiftedMeanResidual.axialDirection, LiftedMeanResidual.liftDirection,
    LiftedMeanResidual.axialVector, context, operators, vector, ParticularWaveBounds.reindexVector,
      cylinder_symm_apply, map_smul]

theorem timeDirection_pull (e : D ≃ₗᵢ[ℝ] E) (c : CorrectionState.Context E) (n : ℕ) :
    LiftedMeanResidual.timeDirection (context e c) n =
      vector (cylinder e) (LiftedMeanResidual.timeDirection c n) := by
  funext x
  simp only [LiftedMeanResidual.timeDirection, LiftedMeanResidual.liftDirection,
    LiftedMeanResidual.temporalVector, context, operators, vector,
      ParticularWaveBounds.reindexVector, cylinder_symm_apply, map_sub, map_smul]

theorem angularDirection_pull (e : D ≃ₗᵢ[ℝ] E) :
    vector (cylinder e) (LiftedMeanResidual.angularDirection (D := E)) =
      LiftedMeanResidual.angularDirection := by
  funext x
  change (e.symm 0, 1) = (0, 1)
  rw [map_zero]

theorem complexBase_pull (e : D ≃ₗᵢ[ℝ] E) (c : CorrectionState.Context E) (n : ℕ) :
    LiftedMeanResidual.complexBase (context e c) n =
      fun x => LiftedMeanResidual.complexBase c n (cylinder e x) := rfl

theorem complexPerturbation_pull (e : D ≃ₗᵢ[ℝ] E) (u : CorrectionState.State E) (n : ℕ) :
    LiftedMeanResidual.complexPerturbation (state e u) n =
      fun x => LiftedMeanResidual.complexPerturbation u n (cylinder e x) := rfl

theorem complexPressure_pull (e : D ≃ₗᵢ[ℝ] E) (u : CorrectionState.State E) (n : ℕ) :
    LiftedMeanResidual.complexPressure (state e u) n =
      fun x => LiftedMeanResidual.complexPressure u n (cylinder e x) := rfl

theorem virtualDivergence_pull (e : D ≃ₗᵢ[ℝ] E) (c : CorrectionState.Context E)
    (n : ℕ) (x : D × ℝ) :
    LiftedMeanResidual.virtualDivergence (context e c) n x =
      LiftedMeanResidual.virtualDivergence c n (cylinder e x) := by
  change ![0, -((operators e c.operators).radialDiv 2 (field e c.virtualTheta) n x.1),
    -((operators e c.operators).radialDiv 1 (field e c.virtualAxial) n x.1)] = _
  rw [radialDiv_pull, radialDiv_pull]
  rfl

theorem fullResidual_pull (e : D ≃ₗᵢ[ℝ] E) (c : CorrectionState.Context E)
    (u : CorrectionState.State E) (n : ℕ) (x : D × ℝ) (i : Fin 3) :
    LiftedMeanResidual.fullResidual (context e c) (state e u) n x i =
      LiftedMeanResidual.fullResidual c u n (cylinder e x) i := by
  have hl := linearResidual_field_pull (cylinder e) (c.operators.epsilon n)
    (fun y : E × ℝ => c.operators.radius y.1)
    (LiftedMeanResidual.radialDirection c n) LiftedMeanResidual.angularDirection
    (LiftedMeanResidual.axialDirection c n) (LiftedMeanResidual.timeDirection c n)
    (LiftedMeanResidual.complexBase c n) (LiftedMeanResidual.complexPerturbation u n)
    (LiftedMeanResidual.complexPressure u n) x
  have hq := transport_field_pull (cylinder e) (fun y : E × ℝ => c.operators.radius y.1)
    (LiftedMeanResidual.radialDirection c n) LiftedMeanResidual.angularDirection
    (LiftedMeanResidual.axialDirection c n)
    (LiftedMeanResidual.complexPerturbation u n) (LiftedMeanResidual.complexPerturbation u n) x
  rw [angularDirection_pull] at hl hq
  unfold LiftedMeanResidual.fullResidual LiftedMeanResidual.nonlinearResidual
  rw [radialDirection_pull, axialDirection_pull, timeDirection_pull,
    complexBase_pull, complexPerturbation_pull, complexPressure_pull]
  rw [show (fun y : D × ℝ => (context e c).operators.radius y.1) =
    (fun y : D × ℝ => c.operators.radius (cylinder e y).1) from rfl]
  change ((LinearWaveResidual.linearResidual (c.operators.epsilon n)
    (fun y : D × ℝ => c.operators.radius (cylinder e y).1)
    (vector (cylinder e) (LiftedMeanResidual.radialDirection c n))
      LiftedMeanResidual.angularDirection
    (vector (cylinder e) (LiftedMeanResidual.axialDirection c n))
    (vector (cylinder e) (LiftedMeanResidual.timeDirection c n))
    _ _ _ x + LinearWaveResidual.transport _ _ _ _ _ _ x) i).re + _ + _ = _
  rw [hl, hq, virtualDivergence_pull]
  rfl

theorem fullGoodResidual_pull (e : D ≃ₗᵢ[ℝ] E) (c : CorrectionState.Context E)
    (u : CorrectionState.State E) (n : ℕ) (x : D × ℝ) (i : Fin 3) :
    LiftedMeanResidual.fullGoodResidual (context e c) (state e u) n x i =
      LiftedMeanResidual.fullGoodResidual c u n (cylinder e x) i := by
  change LiftedMeanResidual.fullResidual (context e c) (state e u) n x i - _ = _
  rw [fullResidual_pull]
  rfl

/-! ## Exact return from the alternate layout -/

theorem coefficients_roundtrip (e : D ≃ₗᵢ[ℝ] E) (a : HarmonicFields.Coefficients D) :
    coefficients e (coefficients e.symm a) = a := by
  ext j x
  simp only [coefficients_apply, e.symm_apply_apply]

theorem block_roundtrip (e : D ≃ₗᵢ[ℝ] E) (b : CorrectionState.HarmonicBlock D) :
    block e (block e.symm b) = b := by
  cases b
  simp only [block, coefficients_roundtrip, e.symm_apply_apply]

theorem field_roundtrip (e : D ≃ₗᵢ[ℝ] E) (f : MeanIncrementBounds.Field D) :
    field e (field e.symm f) = f := by
  funext n x
  exact congrArg (f n) (e.symm_apply_apply x)

theorem oscillation_roundtrip (e : D ≃ₗᵢ[ℝ] E) (f : CorrectionState.Oscillation D) :
    oscillation e (oscillation e.symm f) = f := by
  funext n x
  change f n (e.symm (e x.1), x.2) = f n x
  rw [e.symm_apply_apply]

theorem state_roundtrip (e : D ≃ₗᵢ[ℝ] E) (u : CorrectionState.State D) :
    state e (state e.symm u) = u := by
  cases u with
  | mk m p a q r =>
    cases m
    cases r
    simp only [state, triple, errors, cylinder_apply, e.symm_apply_apply,
      field_roundtrip, oscillation_roundtrip]

theorem context_roundtrip (e : D ≃ₗᵢ[ℝ] E) (c : CorrectionState.Context D) :
    context e (context e.symm c) = c := by
  cases c with
  | mk o b t z =>
    cases o
    cases b
    simp only [context, operators, triple, LinearIsometryEquiv.symm_symm,
      e.symm_apply_apply, field_roundtrip]

/-! ## The same weighted classes, without loss of exponents -/

noncomputable def strip (e : D ≃ₗᵢ[ℝ] E) (s : WeightedClasses.StripData E) :
    WeightedClasses.StripData D := ParticularWaveBounds.reindexStrip e s

theorem memClass_pull (e : D ≃ₗᵢ[ℝ] E) {s : WeightedClasses.StripData E}
    {w : ℕ → E → ℝ} {alpha : ℝ} {f : ℕ → E → F}
    (hf : WeightedClasses.MemClass s w alpha f) :
    WeightedClasses.MemClass (strip e s) (fun n x => w n (e x)) alpha (fun n x => f n (e x)) :=
  ParticularWaveBounds.memClass_reindex e hf

theorem block_waveBounds (e : D ≃ₗᵢ[ℝ] E) {s : WeightedClasses.StripData E}
    {w : ℕ → E → ℝ} {alpha : ℝ} {b : CorrectionState.HarmonicBlock E}
    (hb : b.WaveBounds s w alpha) :
    (block e b).WaveBounds (strip e s) (fun n x => w n (e x)) alpha := by
  intro i j hj
  exact ParticularWaveBounds.waveClass_reindex e (hb i j hj)

theorem block_pressureBounds (e : D ≃ₗᵢ[ℝ] E) {s : WeightedClasses.StripData E}
    {w : ℕ → E → ℝ} {alpha : ℝ} {b : CorrectionState.HarmonicBlock E}
    (hb : b.PressureBounds s w alpha) :
    (block e b).PressureBounds (strip e s) (fun n x => w n (e x)) alpha := by
  intro j hj
  exact ParticularWaveBounds.waveClass_reindex e (hb j hj)

/-! ## Real linearization and the mean equations -/

theorem realTransport_pull (e : D ≃ₗᵢ[ℝ] E) (R : E → ℝ)
    (Vr Vt Vz : E → E) (u v : E → Fin 3 → ℝ) (x : D) :
    LinearWaveResidual.realTransport (fun y => R (e y)) (vector e Vr) (vector e Vt) (vector e Vz)
      (fun y => u (e y)) (fun y => v (e y)) x =
      LinearWaveResidual.realTransport R Vr Vt Vz u v (e x) := by
  funext i
  simp only [LinearWaveResidual.realTransport, along_pull_component]

theorem realFrameLaplacian_pull (e : D ≃ₗᵢ[ℝ] E) (R : E → ℝ)
    (Vr Vt Vz : E → E) (a : E → Fin 3 → ℝ) (x : D) :
    LinearWaveResidual.realFrameLaplacian (fun y => R (e y))
      (vector e Vr) (vector e Vt) (vector e Vz) (fun y => a (e y)) x =
      LinearWaveResidual.realFrameLaplacian R Vr Vt Vz a (e x) := by
  funext i
  simp only [LinearWaveResidual.realFrameLaplacian, scalarLaplacian_component_pull,
    along_pull_component]

theorem realComponentLinearResidual_pull (e : D ≃ₗᵢ[ℝ] E) (epsilon : ℝ) (R : E → ℝ)
    (Vr Vt Vz Vtime : E → E) (B a : E → Fin 3 → ℝ) (p : E → ℝ) (x : D) :
    LinearWaveResidual.realComponentLinearResidual epsilon (fun y => R (e y))
      (vector e Vr) (vector e Vt) (vector e Vz) (vector e Vtime)
      (fun y => B (e y)) (fun y => a (e y)) (fun y => p (e y)) x =
      LinearWaveResidual.realComponentLinearResidual epsilon R Vr Vt Vz Vtime B a p (e x) := by
  funext i
  simp only [LinearWaveResidual.realComponentLinearResidual, realTransport_pull,
    realFrameLaplacian_pull, along_pull, along_pull_component]

theorem thetaResidual_pull (e : D ≃ₗᵢ[ℝ] E) (c : CorrectionState.Context E)
    (u : CorrectionState.State E) :
    (state e u).thetaResidual (context e c) = field e (u.thetaResidual c) := by
  change (operators e c.operators).time (field e u.mean.angular) +
    (operators e c.operators).radialDiv 2
      (field e (MeanIncrementBounds.thetaRadial c.base u.mean + u.covariance 0 1)) +
    (operators e c.operators).dz
      (field e (MeanIncrementBounds.thetaAxial c.base u.mean + u.covariance 2 1)) -
    (operators e c.operators).viscosity 1 (field e u.mean.angular) -
    (operators e c.operators).radialDiv 2 (field e c.virtualTheta) = _
  rw [time_pull, radialDiv_pull, dz_pull, viscosity_pull, radialDiv_pull]
  rfl

theorem axialResidual_pull (e : D ≃ₗᵢ[ℝ] E) (c : CorrectionState.Context E)
    (u : CorrectionState.State E) :
    (state e u).axialResidual (context e c) = field e (u.axialResidual c) := by
  change (operators e c.operators).time (field e u.mean.axial) +
    (operators e c.operators).radialDiv 1
      (field e (MeanIncrementBounds.axialRadial c.base u.mean + u.covariance 0 2)) +
    (operators e c.operators).dz
      (field e (MeanIncrementBounds.axialAxial c.base u.mean + u.covariance 2 2 + u.pressure)) -
    (operators e c.operators).viscosity 0 (field e u.mean.axial) -
    (operators e c.operators).radialDiv 1 (field e c.virtualAxial) = _
  rw [time_pull, radialDiv_pull, dz_pull, viscosity_pull, radialDiv_pull]
  rfl

theorem gr_pull (e : D ≃ₗᵢ[ℝ] E) (c : CorrectionState.Context E)
    (u : CorrectionState.State E) :
    (state e u).gr (context e c) = field e (u.gr c) := by
  change -((operators e c.operators).time (field e u.mean.radial) +
    (operators e c.operators).radialDiv 1
      (field e (MeanIncrementBounds.radialRadial c.base u.mean + u.covariance 0 0)) +
    (operators e c.operators).dz
      (field e (MeanIncrementBounds.axialRadial c.base u.mean + u.covariance 2 0)) -
    (operators e c.operators).invRadius *
      field e (MeanIncrementBounds.radialAngular c.base u.mean + u.covariance 1 1) -
    (operators e c.operators).viscosity 1 (field e u.mean.radial)) = _
  rw [time_pull, radialDiv_pull, dz_pull, viscosity_pull]
  rfl

theorem radialResidual_pull (e : D ≃ₗᵢ[ℝ] E) (c : CorrectionState.Context E)
    (u : CorrectionState.State E) :
    (state e u).radialResidual (context e c) = field e (u.radialResidual c) := by
  unfold CorrectionState.State.radialResidual
  rw [gr_pull]
  change (operators e c.operators).dr (field e u.pressure) - field e (u.gr c) = _
  rw [dr_pull]
  rfl

theorem reducedMeanResidual_pull (e : D ≃ₗᵢ[ℝ] E) (c : CorrectionState.Context E)
    (u : CorrectionState.State E) (n : ℕ) (x : D) :
    (state e u).reducedMeanResidual (context e c) n x = u.reducedMeanResidual c n (e x) := by
  unfold CorrectionState.State.reducedMeanResidual
  rw [radialResidual_pull, thetaResidual_pull, axialResidual_pull]
  rfl

theorem meanResidual_pull (e : D ≃ₗᵢ[ℝ] E) (c : CorrectionState.Context E)
    (u : CorrectionState.State E) (n : ℕ) (x : D) (i : Fin 3) :
    (state e u).meanResidual (context e c) n x i = u.meanResidual c n (e x) i := by
  change (state e u).reducedMeanResidual (context e c) n x i + _ = _
  rw [reducedMeanResidual_pull]
  rfl

theorem meanGoodResidual_pull (e : D ≃ₗᵢ[ℝ] E) (c : CorrectionState.Context E)
    (u : CorrectionState.State E) (n : ℕ) (x : D) (i : Fin 3) :
    (state e u).meanGoodResidual (context e c) n x i = u.meanGoodResidual c n (e x) i := by
  change (state e u).meanResidual (context e c) n x i - _ = _
  rw [meanResidual_pull]
  rfl

theorem block_bandLimited (e : D ≃ₗᵢ[ℝ] E) {b : CorrectionState.HarmonicBlock E} {N : ℕ}
    (hb : b.BandLimited N) : (block e b).BandLimited N :=
  ⟨fun n i => bandLimited_pull e (hb.1 n i), fun n => bandLimited_pull e (hb.2 n)⟩

/-! ## The actual association used by the wave assembly -/

section Association

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

abbrev Associated (S : Type) := (ℝ × S) × TorusInverse.Plane

/-- The actual auxiliary torus integral in the associated layout. -/
noncomputable def associatedTorusAverage (f : Associated S → ℝ) (p : ℝ × S) : ℝ :=
  ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (p, (x, y))

/-- The actual radial integral of that torus average. -/
noncomputable def associatedMass (f : Associated S → ℝ) (s : S) : ℝ :=
  ∫ r, associatedTorusAverage f (r, s)

theorem torusAverage_liftAssoc (f : Associated S → ℝ) (p : ℝ × S) :
    PressureStream.torusAverage (fun x => f (ParticularWaveBounds.liftAssoc S x)) p =
      associatedTorusAverage f p := rfl

theorem pressureMass_liftAssoc (f : Associated S → ℝ) (s : S) :
    PressureStream.pressureMass (fun x => f (ParticularWaveBounds.liftAssoc S x)) s =
      associatedMass f s := rfl

theorem radialMoment_liftAssoc (k : ℕ) (f : MeanIncrementBounds.Field (Associated S))
    (n : ℕ) (s : S) :
    CorrectionState.radialMoment k (field (ParticularWaveBounds.liftAssoc S) f) n s =
      associatedMass (fun x => x.1.1 ^ k * f n x) s := rfl

theorem covarianceMass_liftAssoc (k : ℕ) (u : CorrectionState.State (Associated S))
    (i j : Fin 3) (n : ℕ) (s : S) :
    CorrectionState.radialMoment k ((state (ParticularWaveBounds.liftAssoc S) u).covariance i j) n
      s =
      associatedMass (fun x => x.1.1 ^ k * u.covariance i j n x) s := rfl

/-- A current state sent into the assembly and returned has exactly its
original stripped residual block, including the actual error coefficients. -/
theorem residualBlock_liftAssoc_return
    (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S))
    (b : CorrectionState.HarmonicBlock (PressureStream.Lift S))
    (G A : HarmonicResidual.BlockCoefficients (PressureStream.Lift S)) :
    block (ParticularWaveBounds.liftAssoc S)
      (HarmonicResidual.residualBlock
        (context (ParticularWaveBounds.liftAssoc S).symm c)
        (state (ParticularWaveBounds.liftAssoc S).symm u)
        (block (ParticularWaveBounds.liftAssoc S).symm b)
        (blockCoefficients (ParticularWaveBounds.liftAssoc S).symm G)
        (blockCoefficients (ParticularWaveBounds.liftAssoc S).symm A)) =
      HarmonicResidual.residualBlock c u b G A := by
  rw [residualBlock_pull, block_roundtrip]

theorem fullResidual_liftAssoc_return
    (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S)) (n : ℕ)
    (x : PressureStream.Lift S × ℝ) (i : Fin 3) :
    LiftedMeanResidual.fullResidual
      (context (ParticularWaveBounds.liftAssoc S).symm c)
      (state (ParticularWaveBounds.liftAssoc S).symm u) n
      (cylinder (ParticularWaveBounds.liftAssoc S) x) i =
      LiftedMeanResidual.fullResidual c u n x i := by
  rw [fullResidual_pull]
  rfl

end Association

end NavierStokes.StateReindex
