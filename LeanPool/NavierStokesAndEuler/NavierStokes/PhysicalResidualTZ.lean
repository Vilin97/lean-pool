/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalResidualBridge

/-!
# Physical residuals in the slow-coordinate order `(T,Z)`

`PhysicalResidualBridge` uses slow coordinates `(Z,T)`.  The correction-state
pipeline uses `(T,Z)`.  The map below swaps those two input coordinates and
leaves radius, fast variables, angle, and vector components unchanged.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.PhysicalResidualTZ

open Set Filter Function HarmonicCalculus
open scoped Topology ContDiff

/-- Plane: an abbreviation for `PhysicalResidualBridge.Plane`. -/
abbrev Plane := PhysicalResidualBridge.Plane
/-- Lift: an abbreviation for `PhysicalResidualBridge.Lift`. -/
abbrev Lift := PhysicalResidualBridge.Lift
/-- Cylinder: an abbreviation for `PhysicalResidualBridge.Cylinder`. -/
abbrev Cylinder := PhysicalResidualBridge.Cylinder

/-- The fixed isometric involution `(R,(Z,T),Y) ↔ (R,(T,Z),Y)`. -/
noncomputable def swapSlow : Lift ≃ₗᵢ[ℝ] Lift where
  toFun x := (x.1, ((x.2.1.2, x.2.1.1), x.2.2))
  invFun x := (x.1, ((x.2.1.2, x.2.1.1), x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' x := by
    change ‖(x.1, ((x.2.1.2, x.2.1.1), x.2.2))‖ = ‖x‖
    simp only [Prod.norm_def]
    rw [max_comm ‖x.2.1.2‖ ‖x.2.1.1‖]

@[simp] theorem swapSlow_apply (x : Lift) :
    swapSlow x = (x.1, ((x.2.1.2, x.2.1.1), x.2.2)) := rfl

@[simp] theorem swapSlow_symm_apply (x : Lift) : swapSlow.symm x = swapSlow x := rfl

theorem swapSlow_swapSlow (x : Lift) : swapSlow (swapSlow x) = x := rfl

/-- Extension to the actual angular cylinder; the angle is not permuted. -/
noncomputable def swapCylinder : Cylinder ≃ₗᵢ[ℝ] Cylinder where
  toLinearEquiv := swapSlow.toLinearEquiv.prodCongr (LinearEquiv.refl ℝ ℝ)
  norm_map' x := by
    change max ‖swapSlow x.1‖ ‖x.2‖ = max ‖x.1‖ ‖x.2‖
    rw [swapSlow.norm_map]

@[simp] theorem swapCylinder_apply (x : Cylinder) :
    swapCylinder x = (swapSlow x.1, x.2) := rfl

@[simp] theorem swapCylinder_symm_apply (x : Cylinder) :
    swapCylinder.symm x = swapCylinder x := rfl

theorem swapCylinder_swapCylinder (x : Cylinder) :
    swapCylinder (swapCylinder x) = x := rfl

/-- This is exactly the continuous linear map used for `swapSlow` in the
variable-gauge module, expressed using only frozen dependencies. -/
theorem swapSlow_toContinuousLinearMap :
    swapSlow.toContinuousLinearEquiv.toContinuousLinearMap =
      (ContinuousLinearMap.id ℝ ℝ).prodMap
        ((ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearMap.prodMap
          (ContinuousLinearMap.id ℝ Plane)) := by
  rfl

section Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pullback of a vector field under a fixed linear change of coordinates. -/
noncomputable def reindexVector (e : E ≃L[ℝ] E) (V : E → E) (x : E) : E :=
  e.symm (V (e x))

/-- The chain rule is valid even for the total derivative convention at a
nondifferentiable point, because the coordinate change is an equivalence. -/
theorem fderiv_reindex (e : E ≃L[ℝ] E) (f : E → F) (x v : E) :
    fderiv ℝ (fun y => f (e y)) x v = fderiv ℝ f (e x) (e v) := by
  change fderiv ℝ (f ∘ e) x v = _
  rw [e.comp_right_fderiv]
  rfl

theorem along_reindex (e : E ≃L[ℝ] E) (V : E → E) (f : E → F) :
    along (reindexVector e V) (fun x => f (e x)) = fun x => along V f (e x) := by
  funext x
  unfold along reindexVector
  rw [fderiv_reindex, e.apply_symm_apply]

theorem along_reindex_component {ι : Type*} (e : E ≃L[ℝ] E) (V : E → E)
    (f : E → ι → F) (i : ι) :
    along (reindexVector e V) (fun x => f (e x) i) =
      fun x => along V (fun y => f y i) (e x) :=
  along_reindex e V (fun y => f y i)

theorem cylindricalLaplacian_reindex (e : E ≃L[ℝ] E) (R : E → ℝ)
    (Vr Vθ Vz : E → E) (f : E → F) (x : E) :
    cylindricalLaplacian (fun y => R (e y)) (reindexVector e Vr)
      (reindexVector e Vθ) (reindexVector e Vz) (fun y => f (e y)) x =
      cylindricalLaplacian R Vr Vθ Vz f (e x) := by
  simp only [cylindricalLaplacian, along_reindex]

theorem cylindricalLaplacian_reindex_component {ι : Type*}
    (e : E ≃L[ℝ] E) (R : E → ℝ) (Vr Vθ Vz : E → E)
    (f : E → ι → F) (i : ι) (x : E) :
    cylindricalLaplacian (fun y => R (e y)) (reindexVector e Vr)
      (reindexVector e Vθ) (reindexVector e Vz) (fun y => f (e y) i) x =
      cylindricalLaplacian R Vr Vθ Vz (fun y => f y i) (e x) :=
  cylindricalLaplacian_reindex e R Vr Vθ Vz (fun y => f y i) x

theorem transport_reindex (e : E ≃L[ℝ] E) (R : E → ℝ)
    (Vr Vθ Vz : E → E) (u v : E → ComplexVector) (x : E) :
    LinearWaveResidual.transport (fun y => R (e y)) (reindexVector e Vr)
      (reindexVector e Vθ) (reindexVector e Vz)
      (fun y => u (e y)) (fun y => v (e y)) x =
      LinearWaveResidual.transport R Vr Vθ Vz u v (e x) := by
  funext i
  simp only [LinearWaveResidual.transport, along_reindex_component]

theorem cylindricalVectorLaplacian_reindex (e : E ≃L[ℝ] E) (R : E → ℝ)
    (Vr Vθ Vz : E → E) (a : E → ComplexVector) (x : E) :
    cylindricalVectorLaplacian (fun y => R (e y)) (reindexVector e Vr)
      (reindexVector e Vθ) (reindexVector e Vz) (fun y => a (e y)) x =
      cylindricalVectorLaplacian R Vr Vθ Vz a (e x) := by
  funext i
  simp only [cylindricalVectorLaplacian, cylindricalLaplacian_reindex_component,
      along_reindex_component]

theorem linearResidual_reindex (e : E ≃L[ℝ] E) (epsilon : ℝ) (R : E → ℝ)
    (Vr Vθ Vz Vt : E → E) (B a : E → ComplexVector) (p : E → ℂ) (x : E) :
    LinearWaveResidual.linearResidual epsilon (fun y => R (e y))
      (reindexVector e Vr) (reindexVector e Vθ) (reindexVector e Vz) (reindexVector e Vt)
      (fun y => B (e y)) (fun y => a (e y)) (fun y => p (e y)) x =
      LinearWaveResidual.linearResidual epsilon R Vr Vθ Vz Vt B a p (e x) := by
  funext i
  simp only [LinearWaveResidual.linearResidual, LinearWaveResidual.gradient,
    transport_reindex, cylindricalVectorLaplacian_reindex, along_reindex, along_reindex_component]

theorem realTransport_reindex (e : E ≃L[ℝ] E) (R : E → ℝ)
    (Vr Vθ Vz : E → E) (u v : E → Fin 3 → ℝ) (x : E) :
    LinearWaveResidual.realTransport (fun y => R (e y)) (reindexVector e Vr)
      (reindexVector e Vθ) (reindexVector e Vz)
      (fun y => u (e y)) (fun y => v (e y)) x =
      LinearWaveResidual.realTransport R Vr Vθ Vz u v (e x) := by
  funext i
  simp only [LinearWaveResidual.realTransport, along_reindex_component]

theorem realFrameLaplacian_reindex (e : E ≃L[ℝ] E) (R : E → ℝ)
    (Vr Vθ Vz : E → E) (a : E → Fin 3 → ℝ) (x : E) :
    LinearWaveResidual.realFrameLaplacian (fun y => R (e y)) (reindexVector e Vr)
      (reindexVector e Vθ) (reindexVector e Vz) (fun y => a (e y)) x =
      LinearWaveResidual.realFrameLaplacian R Vr Vθ Vz a (e x) := by
  funext i
  simp only [LinearWaveResidual.realFrameLaplacian, cylindricalLaplacian_reindex_component,
    along_reindex_component]

theorem graphResidual_reindex (e : E ≃L[ℝ] E) (epsilon : ℝ) (R : E → ℝ)
    (Vr Vθ Vz Vt : E → E) (a : E → Fin 3 → ℝ) (p : E → ℝ) (x : E) :
    PhysicalResidualBridge.graphResidual epsilon (fun y => R (e y))
      (reindexVector e Vr) (reindexVector e Vθ) (reindexVector e Vz) (reindexVector e Vt)
      (fun y => a (e y)) (fun y => p (e y)) x =
      PhysicalResidualBridge.graphResidual epsilon R Vr Vθ Vz Vt a p (e x) := by
  funext i
  simp only [PhysicalResidualBridge.graphResidual, realTransport_reindex,
    realFrameLaplacian_reindex, along_reindex, along_reindex_component]

end Calculus

/-- Swap field, defined pointwise by `f n (swapSlow x)`. -/
noncomputable def swapField (f : MeanIncrementBounds.Field Lift) : MeanIncrementBounds.Field Lift :=
  fun n x => f n (swapSlow x)

/-- Swap triple, given by `⟨swapField m.radial, swapField m.angular, swapField m.axial⟩`. -/
noncomputable def swapTriple (m : MeanIncrementBounds.Triple Lift) : MeanIncrementBounds.Triple
    Lift :=
  ⟨swapField m.radial, swapField m.angular, swapField m.axial⟩

/-- Swap operators, bundling `epsilon`, `radialFrequency`, `fastCoefficient`, `radius` and the
required compatibility proofs. -/
noncomputable def swapOperators (o : MeanIncrementBounds.Operators Lift) :
    MeanIncrementBounds.Operators Lift where
  epsilon := o.epsilon
  radialFrequency := o.radialFrequency
  fastCoefficient := o.fastCoefficient
  radius := fun x => o.radius (swapSlow x)
  radialProfile := fun x => o.radialProfile (swapSlow x)
  eR := swapSlow o.eR
  eZ := swapSlow o.eZ
  eT := swapSlow o.eT
  vR := swapSlow o.vR
  vT := swapSlow o.vT

/-- Swap context, bundling `operators`, `base`, `virtualTheta`, `virtualAxial`. -/
noncomputable def swapContext (c : CorrectionState.Context Lift) : CorrectionState.Context Lift
    where
  operators := swapOperators c.operators
  base := swapTriple c.base
  virtualTheta := swapField c.virtualTheta
  virtualAxial := swapField c.virtualAxial

/-- Swap oscillation, defined pointwise by `f n (swapCylinder x)`. -/
noncomputable def swapOscillation (f : CorrectionState.Oscillation Lift) :
    CorrectionState.Oscillation Lift := fun n x => f n (swapCylinder x)

/-- Swap errors, bundling `base`, `gaussian`, `aliasError`. -/
noncomputable def swapErrors (e : CorrectionState.ExcludedErrors Lift) :
    CorrectionState.ExcludedErrors Lift where
  base := swapOscillation e.base
  gaussian := swapOscillation e.gaussian
  aliasError := swapOscillation e.aliasError

/-- Swap state, bundling `mean`, `pressure`, `oscillation`, `oscillatoryPressure` and the
required compatibility proofs. -/
noncomputable def swapState (s : CorrectionState.State Lift) : CorrectionState.State Lift where
  mean := swapTriple s.mean
  pressure := swapField s.pressure
  oscillation := swapOscillation s.oscillation
  oscillatoryPressure := fun n x => s.oscillatoryPressure n (swapCylinder x)
  errors := swapErrors s.errors

theorem fderiv_swapField (f : MeanIncrementBounds.Field Lift) (n : ℕ) (x v : Lift) :
    fderiv ℝ (swapField f n) x (swapSlow v) = fderiv ℝ (f n) (swapSlow x) v := by
  change fderiv ℝ (fun y => f n (swapSlow.toContinuousLinearEquiv y)) x (swapSlow v) = _
  rw [fderiv_reindex]
  rfl

theorem dr_swap (o : MeanIncrementBounds.Operators Lift) (f : MeanIncrementBounds.Field Lift) :
    (swapOperators o).dr (swapField f) = swapField (o.dr f) := by
  funext n x
  simp only [MeanIncrementBounds.Operators.dr, WeightedClasses.graphDerivative,
    swapOperators, fderiv_swapField, swapField]

theorem dz_swap (o : MeanIncrementBounds.Operators Lift) (f : MeanIncrementBounds.Field Lift) :
    (swapOperators o).dz (swapField f) = swapField (o.dz f) := by
  funext n x
  simp only [MeanIncrementBounds.Operators.dz, swapOperators, fderiv_swapField, swapField]

theorem time_swap (o : MeanIncrementBounds.Operators Lift) (f : MeanIncrementBounds.Field Lift) :
    (swapOperators o).time (swapField f) = swapField (o.time f) := by
  funext n x
  simp only [MeanIncrementBounds.Operators.time, MeanIncrementBounds.Operators.slowTime,
    MeanIncrementBounds.Operators.fastTime, swapOperators, fderiv_swapField, swapField,
    Pi.add_apply]

theorem radialDiv_swap (o : MeanIncrementBounds.Operators Lift)
    (k : ℝ) (f : MeanIncrementBounds.Field Lift) :
    (swapOperators o).radialDiv k (swapField f) = swapField (o.radialDiv k f) := by
  unfold MeanIncrementBounds.Operators.radialDiv
  rw [dr_swap]
  rfl

theorem radialDirection_swap (c : CorrectionState.Context Lift) (n : ℕ) :
    LiftedMeanResidual.radialDirection (swapContext c) n =
      reindexVector swapCylinder.toContinuousLinearEquiv
        (LiftedMeanResidual.radialDirection c n) := by
  rfl

theorem axialDirection_swap (c : CorrectionState.Context Lift) (n : ℕ) :
    LiftedMeanResidual.axialDirection (swapContext c) n =
      reindexVector swapCylinder.toContinuousLinearEquiv
        (LiftedMeanResidual.axialDirection c n) := by
  rfl

theorem timeDirection_swap (c : CorrectionState.Context Lift) (n : ℕ) :
    LiftedMeanResidual.timeDirection (swapContext c) n =
      reindexVector swapCylinder.toContinuousLinearEquiv
        (LiftedMeanResidual.timeDirection c n) := by
  rfl

theorem angularDirection_swap :
    reindexVector swapCylinder.toContinuousLinearEquiv
      (LiftedMeanResidual.angularDirection (D := Lift)) = LiftedMeanResidual.angularDirection := rfl

theorem complexBase_swap (c : CorrectionState.Context Lift) (n : ℕ) :
    LiftedMeanResidual.complexBase (swapContext c) n =
      fun x => LiftedMeanResidual.complexBase c n (swapCylinder x) := rfl

theorem complexPerturbation_swap (s : CorrectionState.State Lift) (n : ℕ) :
    LiftedMeanResidual.complexPerturbation (swapState s) n =
      fun x => LiftedMeanResidual.complexPerturbation s n (swapCylinder x) := rfl

theorem complexPressure_swap (s : CorrectionState.State Lift) (n : ℕ) :
    LiftedMeanResidual.complexPressure (swapState s) n =
      fun x => LiftedMeanResidual.complexPressure s n (swapCylinder x) := rfl

theorem virtualDivergence_swap (c : CorrectionState.Context Lift) (n : ℕ) (x : Cylinder) :
    LiftedMeanResidual.virtualDivergence (swapContext c) n x =
      LiftedMeanResidual.virtualDivergence c n (swapCylinder x) := by
  change ![0, -((swapOperators c.operators).radialDiv 2 (swapField c.virtualTheta) n x.1),
      -((swapOperators c.operators).radialDiv 1 (swapField c.virtualAxial) n x.1)] = _
  rw [radialDiv_swap, radialDiv_swap]
  rfl

/-- Exact covariance of the full nonlinear correction residual.  It includes
the fixed base error once, exactly as in the original state definition. -/
theorem fullResidual_swap (c : CorrectionState.Context Lift) (s : CorrectionState.State Lift)
    (n : ℕ) (x : Cylinder) (i : Fin 3) :
    LiftedMeanResidual.fullResidual (swapContext c) (swapState s) n x i =
      LiftedMeanResidual.fullResidual c s n (swapCylinder x) i := by
  have hlin := linearResidual_reindex swapCylinder.toContinuousLinearEquiv
    (c.operators.epsilon n) (fun y : Cylinder => c.operators.radius y.1)
    (LiftedMeanResidual.radialDirection c n) LiftedMeanResidual.angularDirection
    (LiftedMeanResidual.axialDirection c n) (LiftedMeanResidual.timeDirection c n)
    (LiftedMeanResidual.complexBase c n) (LiftedMeanResidual.complexPerturbation s n)
    (LiftedMeanResidual.complexPressure s n) x
  have hquad := transport_reindex swapCylinder.toContinuousLinearEquiv
    (fun y : Cylinder => c.operators.radius y.1)
    (LiftedMeanResidual.radialDirection c n) LiftedMeanResidual.angularDirection
    (LiftedMeanResidual.axialDirection c n)
    (LiftedMeanResidual.complexPerturbation s n) (LiftedMeanResidual.complexPerturbation s n) x
  rw [angularDirection_swap] at hlin hquad
  unfold LiftedMeanResidual.fullResidual LiftedMeanResidual.nonlinearResidual
  rw [radialDirection_swap, axialDirection_swap, timeDirection_swap,
    complexBase_swap, complexPerturbation_swap, complexPressure_swap]
  rw [show (swapContext c).operators.epsilon = c.operators.epsilon from rfl,
    show (fun y : Cylinder => (swapContext c).operators.radius y.1) =
      (fun y : Cylinder => c.operators.radius (swapCylinder.toContinuousLinearEquiv y).1) from rfl]
  have hcoe : (swapCylinder.toContinuousLinearEquiv : Cylinder → Cylinder) = swapCylinder := rfl
  simp only [hcoe] at hlin hquad ⊢
  rw [hlin, hquad, virtualDivergence_swap]
  rfl

theorem fullGoodResidual_swap (c : CorrectionState.Context Lift) (s : CorrectionState.State Lift)
    (n : ℕ) (x : Cylinder) (i : Fin 3) :
    LiftedMeanResidual.fullGoodResidual (swapContext c) (swapState s) n x i =
      LiftedMeanResidual.fullGoodResidual c s n (swapCylinder x) i := by
  change LiftedMeanResidual.fullResidual (swapContext c) (swapState s) n x i - _ = _
  rw [fullResidual_swap]
  rfl

/-- Literal operator data in the order `(T,Z)`.  No derivative identity is
assumed: all derivative transport is supplied by the preceding theorems. -/
structure MatchesAtTZ (o : MeanIncrementBounds.Operators Lift)
    (G : PhysicalResidualBridge.ScaledGraph) (n : ℕ) : Prop where
  epsilon : o.epsilon n = G.epsilon
  frequency : o.radialFrequency n = G.frequency
  fast : o.fastCoefficient n = G.fastCoefficient
  radius : o.radius = Prod.fst
  profile : o.radialProfile = fun x => GraphCalculus.radialSpeed G.exponent x.1
  eR : o.eR = (1, (0, 0))
  eZ : o.eZ = (0, ((0, 1), 0))
  eT : o.eT = (0, ((1, 0), 0))
  vR : o.vR = (0, (0, G.radialVector))
  vT : o.vT = (0, (0, G.temporalVector))

theorem MatchesAtTZ.toMatchesAt {o : MeanIncrementBounds.Operators Lift}
    {G : PhysicalResidualBridge.ScaledGraph} {n : ℕ} (H : MatchesAtTZ o G n) :
    PhysicalResidualBridge.MatchesAt (swapOperators o) G n := by
  constructor
  · exact H.epsilon
  · exact H.frequency
  · exact H.fast
  · change (fun x => o.radius (swapSlow x)) = Prod.fst
    rw [H.radius]
    rfl
  · change (fun x => o.radialProfile (swapSlow x)) = _
    rw [H.profile]
    rfl
  · change swapSlow o.eR = _
    rw [H.eR]
    rfl
  · change swapSlow o.eZ = _
    rw [H.eZ]
    rfl
  · change swapSlow o.eT = _
    rw [H.eT]
    rfl
  · change swapSlow o.vR = _
    rw [H.vR]
    rfl
  · change swapSlow o.vT = _
    rw [H.vT]
    rfl

theorem matchesAtTZ_graphOperators (r : CorrectionState.ReconstructionData)
    (epsilon fast : ℕ → ℝ) (G : PhysicalResidualBridge.ScaledGraph) (n : ℕ)
    (hε : epsilon n = G.epsilon) (hM : r.frequency n = G.frequency)
    (hc : fast n = G.fastCoefficient) (hd : r.exponent = G.exponent)
    (hv : r.radialDirection = G.radialVector) :
    MatchesAtTZ (CorrectionState.graphOperators r epsilon fast
      (((0, 1) : Plane), (0 : Plane)) (((1, 0) : Plane), (0 : Plane)) G.temporalVector) G n := by
  constructor
  · exact hε
  · exact hM
  · exact hc
  · rfl
  · simp only [CorrectionState.graphOperators, hd, RadialPullback.radialJacobian,
      GraphCalculus.radialSpeed]
  · rfl
  · rfl
  · rfl
  · simp only [CorrectionState.graphOperators, hv]
  · rfl

/-- The actual scaled physical graph, with the slow coordinates in `(T,Z)` order. -/
noncomputable def graphMapTZ (G : PhysicalResidualBridge.ScaledGraph)
    (p : ProblemStatement.SpaceTime) : Cylinder := swapCylinder (G.map p)

/-- Graph source TZ, given by `{p | 0 < p.2 0 ∧ graphMapTZ G p ∈ U}`. -/
noncomputable def graphSourceTZ (G : PhysicalResidualBridge.ScaledGraph) (U : Set Cylinder) :
    Set ProblemStatement.SpaceTime := {p | 0 < p.2 0 ∧ graphMapTZ G p ∈ U}

/-- Graph radial TZ, given by `reindexVector swapCylinder.toContinuousLinearEquiv G.radial`. -/
noncomputable def graphRadialTZ (G : PhysicalResidualBridge.ScaledGraph) : Cylinder → Cylinder :=
  reindexVector swapCylinder.toContinuousLinearEquiv G.radial

/-- Graph angular TZ, given by `reindexVector swapCylinder.toContinuousLinearEquiv
PhysicalResidualBridge.ScaledGraph.angular`. -/
noncomputable def graphAngularTZ : Cylinder → Cylinder :=
  reindexVector swapCylinder.toContinuousLinearEquiv PhysicalResidualBridge.ScaledGraph.angular

/-- Graph axial TZ, given by `reindexVector swapCylinder.toContinuousLinearEquiv G.axial`. -/
noncomputable def graphAxialTZ (G : PhysicalResidualBridge.ScaledGraph) : Cylinder → Cylinder :=
  reindexVector swapCylinder.toContinuousLinearEquiv G.axial

/-- Graph temporal TZ, given by `reindexVector swapCylinder.toContinuousLinearEquiv G.temporal`. -/
noncomputable def graphTemporalTZ (G : PhysicalResidualBridge.ScaledGraph) : Cylinder → Cylinder :=
  reindexVector swapCylinder.toContinuousLinearEquiv G.temporal

theorem graphAxialTZ_apply (G : PhysicalResidualBridge.ScaledGraph) (x : Cylinder) :
    graphAxialTZ G x = ((0, ((0, G.epsilon), 0)), 0) := rfl

theorem graphTemporalTZ_apply (G : PhysicalResidualBridge.ScaledGraph) (x : Cylinder) :
    graphTemporalTZ G x = ((0, ((-G.epsilon, 0), G.fastCoefficient • G.temporalVector)), 0) := rfl

theorem graphRadialTZ_eq (G : PhysicalResidualBridge.ScaledGraph) : graphRadialTZ G = G.radial :=
    rfl

theorem graphAngularTZ_eq : graphAngularTZ = PhysicalResidualBridge.ScaledGraph.angular := rfl

/-- Velocity TZ, given by `G.velocity (fun x => a (swapCylinder x))`. -/
noncomputable def velocityTZ (G : PhysicalResidualBridge.ScaledGraph)
    (a : Cylinder → Fin 3 → ℝ) : ProblemStatement.VelocityField :=
  G.velocity (fun x => a (swapCylinder x))

/-- Pressure TZ, given by `G.pressure (fun x => p (swapCylinder x))`. -/
noncomputable def pressureTZ (G : PhysicalResidualBridge.ScaledGraph)
    (p : Cylinder → ℝ) : ProblemStatement.PressureField :=
  G.pressure (fun x => p (swapCylinder x))

/-- Exact covariance of the complete real graph equation in the two layouts. -/
theorem graphResidual_swap (G : PhysicalResidualBridge.ScaledGraph)
    (a : Cylinder → Fin 3 → ℝ) (p : Cylinder → ℝ) (x : Cylinder) :
    PhysicalResidualBridge.graphResidual G.epsilon PhysicalResidualBridge.ScaledGraph.radius
      G.radial PhysicalResidualBridge.ScaledGraph.angular G.axial G.temporal
      (fun y => a (swapCylinder y)) (fun y => p (swapCylinder y)) x =
    PhysicalResidualBridge.graphResidual G.epsilon PhysicalResidualBridge.ScaledGraph.radius
      (graphRadialTZ G) graphAngularTZ (graphAxialTZ G) (graphTemporalTZ G)
      a p (swapCylinder x) := by
  exact (graphResidual_reindex swapCylinder.toContinuousLinearEquiv G.epsilon
    PhysicalResidualBridge.ScaledGraph.radius G.radial PhysicalResidualBridge.ScaledGraph.angular
    G.axial G.temporal (fun y => a (swapCylinder y)) (fun y => p (swapCylinder y))
    (swapCylinder x)).symm

/-- The same fixed linear chart map used by the variable-gauge mean, in `(T,Z)` order. -/
noncomputable def physicalToChartTZ (h : ℝ) (n k : ℕ) : Lift →L[ℝ] Lift :=
  swapSlow.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((MeanChartCompatibility.physicalToChart h n k).comp
      swapSlow.toContinuousLinearEquiv.toContinuousLinearMap)

theorem physicalToChartTZ_swap (h : ℝ) (n k : ℕ) (x : Lift) :
    physicalToChartTZ h n k (swapSlow x) =
      swapSlow (MeanChartCompatibility.physicalToChart h n k x) := rfl

theorem physicalToChartTZ_eq_formula (h : ℝ) (n k : ℕ) :
    physicalToChartTZ h n k =
      MeanChartCompatibility.chartLinear (MeanChartCompatibility.chartScale n)
        (((ChartScales.Q n ^ (-1 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
          (ChartScales.Q n ^ (-CoordinateAlgebra.D h) • ContinuousLinearMap.snd ℝ ℝ ℝ)).prodMap
            (TemporalMeanUpdate.coverMap k)) := rfl

/-- Absolute lift TZ, given by `swapSlow (PhysicalResidualBridge.absoluteLift h p)`. -/
noncomputable def absoluteLiftTZ (h : ℝ) (p : ProblemStatement.SpaceTime) : Lift :=
  swapSlow (PhysicalResidualBridge.absoluteLift h p)

theorem commonGraph_eq_physicalToChartTZ (h : ℝ) (n k : ℕ) {p : ProblemStatement.SpaceTime}
    (hr : 0 < p.2 0) :
    graphMapTZ (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h k) p =
      (physicalToChartTZ h n k (absoluteLiftTZ h p), p.2 1) := by
  unfold graphMapTZ
  rw [PhysicalResidualBridge.commonGraph_eq_physicalToChart h n k hr]
  rfl

/-- The full correction-state residual in `(T,Z)` coordinates is the actual
scaled Cartesian Navier--Stokes residual. The fixed base-pressure equation
and the neighborhood representation of the actual physical fields remain explicit. -/
theorem context_fullResidual_physicalTZ {Q : ℝ} (hQ : 0 < Q) (h : ℝ) (k n : ℕ)
    (c : CorrectionState.Context Lift) (s : CorrectionState.State Lift)
    (H : MatchesAtTZ c.operators (PhysicalResidualBridge.commonGraph Q h k) n)
    {U : Set Cylinder} (hU : IsOpen U) (hR : ∀ x ∈ U, x.1.1 ≠ 0)
    {p₀ : Cylinder → ℝ}
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun x => PhysicalResidualBridge.baseComponents c n x i) U)
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun x => PhysicalResidualBridge.incrementComponents s n x i) U)
    (hp₀ : ContDiffOn ℝ ∞ p₀ U) (hp : ContDiffOn ℝ ∞ (s.totalPressureIncrement n) U)
    {t : ℝ} {q : ProblemStatement.Space}
    (hz : (t, q) ∈ graphSourceTZ (PhysicalResidualBridge.commonGraph Q h k) U)
    (hbase : ∀ i, PhysicalResidualBridge.graphResidual (Q ^ h)
      PhysicalResidualBridge.ScaledGraph.radius
      (graphRadialTZ (PhysicalResidualBridge.commonGraph Q h k)) graphAngularTZ
      (graphAxialTZ (PhysicalResidualBridge.commonGraph Q h k))
      (graphTemporalTZ (PhysicalResidualBridge.commonGraph Q h k))
      (PhysicalResidualBridge.baseComponents c n) p₀
      (graphMapTZ (PhysicalResidualBridge.commonGraph Q h k) (t, q)) i =
        LiftedMeanResidual.virtualDivergence c n
          (graphMapTZ (PhysicalResidualBridge.commonGraph Q h k) (t, q)) i +
        s.errors.base n (graphMapTZ (PhysicalResidualBridge.commonGraph Q h k) (t, q)) i)
    {u : ProblemStatement.VelocityField} {P : ProblemStatement.PressureField}
    (hu : ContDiffAt ℝ 2 u (t, CylindricalResidual.chart q))
    (hP : DifferentiableAt ℝ P (t, CylindricalResidual.chart q))
    (hrep : (fun z : ProblemStatement.SpaceTime => u (z.1, CylindricalResidual.chart z.2)) =ᶠ[𝓝 (t,
        q)]
      (fun z => CylindricalResidual.frame (z.2 1)
        (velocityTZ (PhysicalResidualBridge.commonGraph Q h k)
          (fun y j => PhysicalResidualBridge.baseComponents c n y j +
            PhysicalResidualBridge.incrementComponents s n y j) z)))
    (hpRep : CylindricalResidual.pressurePullback P =ᶠ[𝓝 (t, q)]
      pressureTZ (PhysicalResidualBridge.commonGraph Q h k)
        (fun y => p₀ y + s.totalPressureIncrement n y)) (i : Fin 3) :
    LiftedMeanResidual.fullResidual c s n
      (graphMapTZ (PhysicalResidualBridge.commonGraph Q h k) (t, q)) i =
      Q ^ (2 * CoordinateAlgebra.A h + 1 / 2) *
        CylindricalResidual.frame (-(q 1))
          (ProblemStatement.navierStokesResidual u P t (CylindricalResidual.chart q)) i := by
  let V : Set Cylinder := swapCylinder ⁻¹' U
  have hV : IsOpen V := hU.preimage swapCylinder.continuous
  have hRV : ∀ x ∈ V, x.1.1 ≠ 0 := fun x hx => hR (swapCylinder x) hx
  have hBV (j : Fin 3) : ContDiffOn ℝ ∞
      (fun x => PhysicalResidualBridge.baseComponents (swapContext c) n x j) V :=
    (hB j).comp swapCylinder.contDiff.contDiffOn (fun _ hx => hx)
  have haV (j : Fin 3) : ContDiffOn ℝ ∞
      (fun x => PhysicalResidualBridge.incrementComponents (swapState s) n x j) V :=
    (ha j).comp swapCylinder.contDiff.contDiffOn (fun _ hx => hx)
  have hpV : ContDiffOn ℝ ∞ ((swapState s).totalPressureIncrement n) V :=
    hp.comp swapCylinder.contDiff.contDiffOn (fun _ hx => hx)
  have hp₀V : ContDiffOn ℝ ∞ (fun x => p₀ (swapCylinder x)) V :=
    hp₀.comp swapCylinder.contDiff.contDiffOn (fun _ hx => hx)
  have hbaseV : ∀ j, PhysicalResidualBridge.graphResidual (Q ^ h)
      PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph Q h k).radial PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph Q h k).axial (PhysicalResidualBridge.commonGraph Q h
          k).temporal
      (PhysicalResidualBridge.baseComponents (swapContext c) n)
      (fun x => p₀ (swapCylinder x)) ((PhysicalResidualBridge.commonGraph Q h k).map (t, q)) j =
        LiftedMeanResidual.virtualDivergence (swapContext c) n
          ((PhysicalResidualBridge.commonGraph Q h k).map (t, q)) j +
        (swapState s).errors.base n ((PhysicalResidualBridge.commonGraph Q h k).map (t, q)) j := by
    intro j
    change PhysicalResidualBridge.graphResidual (PhysicalResidualBridge.commonGraph Q h k).epsilon
      PhysicalResidualBridge.ScaledGraph.radius
      (PhysicalResidualBridge.commonGraph Q h k).radial PhysicalResidualBridge.ScaledGraph.angular
      (PhysicalResidualBridge.commonGraph Q h k).axial (PhysicalResidualBridge.commonGraph Q h
          k).temporal
      (fun x => PhysicalResidualBridge.baseComponents c n (swapCylinder x))
      (fun x => p₀ (swapCylinder x)) ((PhysicalResidualBridge.commonGraph Q h k).map (t, q)) j = _
    rw [graphResidual_swap, virtualDivergence_swap]
    exact hbase j
  have he := PhysicalResidualBridge.context_fullResidual_physical hQ h k n
    (swapContext c) (swapState s) H.toMatchesAt hV hRV hBV haV hp₀V hpV hz hbaseV hu hP hrep hpRep i
  rw [fullResidual_swap] at he
  exact he

end NavierStokes.PhysicalResidualTZ
