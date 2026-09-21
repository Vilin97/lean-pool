/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

import LeanPool.PoincareGeometry.BonnetMyers.LocalEnergy
import LeanPool.PoincareGeometry.BonnetMyers.Transport

/-!
# Manifold-valued local geodesics

The coordinate ODE in `Geodesic.lean` is useful for the analytic existence
argument, but a later geometric argument should not have to carry a model
coordinate curve around.  This file packages the local solution with its
actual manifold curve and its actual tangent-fibre velocity.

The preferred extended chart at the initial point and `Module.finBasis` are
canonical Mathlib choices.  Thus the public object has no user-selected chart
or basis parameter; the coordinate certificate is kept as an implementation
detail of the construction.  The global continuation and chart-transition
theorems are intentionally not claimed here.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

namespace IntrinsicGeodesic

variable [RiemannianBundle (TangentSpace I : M → Type _)]

/-- The canonical finite basis used by the local coordinate construction. -/
noncomputable def canonicalBasis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
  Module.finBasis ℝ E

/-- A manifold-valued local geodesic certificate with initial point `x₀` and
initial tangent `v₀`.  Its coordinate certificate uses only the canonical
preferred chart and basis; clients consume `curve` and `velocity` below. -/
structure LocalGeodesic
    (cov : CovariantDerivative I E (TangentSpace I : M → Type u))
    (x₀ : M) (v₀ : TangentSpace I x₀) where
  solution : LocalChartSecondOrderSolution (I := I) (E := E) (H := H) (M := M)
      (LocalGeodesicData.coordinateAcceleration (I := I) (M := M) (E := E)
        cov x₀ (canonicalBasis (E := E)))
      x₀ (LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E) x₀ v₀)
  isGeodesic : LocalGeodesicData.IsCoordinateGeodesic
      (cov := cov) (x₀ := x₀) (b := canonicalBasis (E := E)) solution

namespace LocalGeodesic

variable {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
  {x₀ : M} {v₀ : TangentSpace I x₀}
include cov x₀ v₀

/-- The actual curve in `M`, obtained from the local chart solution. -/
def curve (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀) : ℝ → M :=
  LocalChartSecondOrderSolution.curve (I := I) (M := M) (E := E) (H := H) γ.solution

/-- The actual tangent vector along the curve.  The inverse extended-chart
derivative converts the model-space velocity into the tangent fibre. -/
def velocity (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀) (t : ℝ) :
    TangentSpace I (curve γ t) :=
  LocalGeodesicData.tangentField (I := I) (M := M) (E := E) (H := H)
    cov x₀ (canonicalBasis (E := E)) γ.solution
    γ.solution.velocity t

lemma curve_initial (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀) : curve γ 0 = x₀ := by
  exact LocalChartSecondOrderSolution.curve_initial (I := I) (M := M) (E := E)
    (H := H) γ.solution

lemma velocity_initial (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀) : velocity γ 0 = v₀ := by
  have h := LocalGeodesicData.tangentField_initial_coordinateVelocity
    (I := I) (M := M) (E := E) cov x₀ (canonicalBasis (E := E)) γ.solution v₀ rfl
  simpa [curve, velocity, LocalGeodesicData.tangentField,
    γ.solution.velocity_initial] using h

lemma hasMFDerivAt_curve (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {t : ℝ} (ht : t ∈ Ioo (-γ.solution.radius) γ.solution.radius) :
    HasMFDerivAt (𝓘(ℝ, ℝ)) I (curve γ) t
      (ContinuousLinearMap.toSpanSingleton ℝ (velocity γ t)) := by
  change HasMFDerivAt (𝓘(ℝ, ℝ)) I
    (LocalChartSecondOrderSolution.curve γ.solution) t
    (ContinuousLinearMap.toSpanSingleton ℝ
      (LocalGeodesicData.tangentField cov x₀ (canonicalBasis (E := E))
        γ.solution γ.solution.velocity t))
  rw [LocalGeodesicData.tangentField_eq_coordinateFrameCombination
    (I := I) (M := M) (E := E) (H := H) cov x₀
    (canonicalBasis (E := E)) γ.solution γ.solution.velocity ht]
  exact LocalGeodesicData.curve_derivative_velocity
    (I := I) (M := M) (E := E) (H := H) cov x₀
    (canonicalBasis (E := E)) γ.solution ht

lemma isCoordinateGeodesic (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀) :
    LocalGeodesicData.IsCoordinateGeodesic
      (cov := cov) (x₀ := x₀) (b := canonicalBasis (E := E)) γ.solution :=
  γ.isGeodesic

end LocalGeodesic

/-- Local existence of a manifold-valued geodesic for every tangent vector. -/
theorem exists_localGeodesic
    (cov : CovariantDerivative I E (TangentSpace I : M → Type u))
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (x₀ : M) (v₀ : TangentSpace I x₀) :
    Nonempty (LocalGeodesic (I := I) (M := M) cov x₀ v₀) := by
  obtain ⟨sol, hsol⟩ :=
    LocalGeodesicData.exists_local_coordinateGeodesic_for_velocity
      (I := I) (M := M) (E := E) (H := H) cov x₀
      (canonicalBasis (E := E)) v₀
  exact ⟨⟨sol, hsol⟩⟩

def LocalChartSecondOrderSolution.castInitialVelocity
    {F : E → E → E} {c : M} {u v : E}
    (h : u = v) (sol : LocalChartSecondOrderSolution I F c v) :
    LocalChartSecondOrderSolution I F c u :=
  Eq.mpr (congrArg (fun w ↦ LocalChartSecondOrderSolution I F c w) h) sol

@[simp] theorem LocalChartSecondOrderSolution.coordinate_castInitialVelocity
    {F : E → E → E} {c : M} {u v : E}
    (h : u = v) (sol : LocalChartSecondOrderSolution I F c v) :
    (LocalChartSecondOrderSolution.castInitialVelocity h sol).coordinate = sol.coordinate := by
  cases h
  rfl

@[simp] theorem LocalChartSecondOrderSolution.velocity_castInitialVelocity
    {F : E → E → E} {c : M} {u v : E}
    (h : u = v) (sol : LocalChartSecondOrderSolution I F c v) :
    (LocalChartSecondOrderSolution.castInitialVelocity h sol).velocity = sol.velocity := by
  cases h
  rfl

@[simp] theorem LocalChartSecondOrderSolution.radius_castInitialVelocity
    {F : E → E → E} {c : M} {u v : E}
    (h : u = v) (sol : LocalChartSecondOrderSolution I F c v) :
    (LocalChartSecondOrderSolution.castInitialVelocity h sol).radius = sol.radius := by
  cases h
  rfl

namespace LocalGeodesic

variable {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
  {x₀ : M} {v₀ : TangentSpace I x₀}
include cov x₀ v₀

/-- Reverse a local geodesic in time.  Both the coordinate geodesic equation
and the tangent-frame reconstruction respect this reversal. -/
noncomputable def reverse
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀) :
    LocalGeodesic (I := I) (M := M) cov x₀ (-v₀) := by
  let solRev := LocalGeodesicData.LocalChartSecondOrderSolution.reverse
    (fun z u ↦ LocalGeodesicData.coordinateAcceleration_neg cov x₀
      (canonicalBasis (E := E)) z u) γ.solution
  have hcoord : LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E) x₀ (-v₀) =
      -LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E) x₀ v₀ := by
    simp [LocalGeodesicData.coordinateVelocity]
  let sol' : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration cov x₀
        (canonicalBasis (E := E))) x₀
      (LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E) x₀ (-v₀)) :=
    LocalChartSecondOrderSolution.castInitialVelocity hcoord solRev
  exact ⟨sol', LocalGeodesicData.local_solution_isCoordinateGeodesic
    (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀)
      (b := canonicalBasis (E := E)) sol'⟩

@[simp] lemma reverse_coordinate
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t : ℝ) :
    (reverse γ).solution.coordinate t = γ.solution.coordinate (-t) := by
  simp [reverse, LocalGeodesicData.LocalChartSecondOrderSolution.reverse]

@[simp] lemma reverse_velocity
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t : ℝ) :
    (reverse γ).solution.velocity t = -γ.solution.velocity (-t) := by
  simp [reverse, LocalGeodesicData.LocalChartSecondOrderSolution.reverse]

@[simp] lemma reverse_radius
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀) :
    (reverse γ).solution.radius = γ.solution.radius := by
  simp [reverse, LocalGeodesicData.LocalChartSecondOrderSolution.reverse]

lemma reverse_curve
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t : ℝ) :
    curve (reverse γ) t = curve γ (-t) := by
  simp [curve, LocalChartSecondOrderSolution.curve, Function.comp_apply]

lemma reverse_actual_velocity
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {t : ℝ} (ht : t ∈ Ioo (-γ.solution.radius) γ.solution.radius) :
    velocity (reverse γ) t = -velocity γ (-t) := by
  have htrev : t ∈ Ioo (-(reverse γ).solution.radius)
      (reverse γ).solution.radius := by
    simpa using ht
  have htneg : -t ∈ Ioo (-γ.solution.radius) γ.solution.radius := by
    constructor <;> linarith [ht.1, ht.2]
  have hrev := LocalGeodesicData.tangentField_eq_coordinateFrameCombination
    (I := I) (M := M) (E := E) cov x₀
      (canonicalBasis (E := E)) (reverse γ).solution
      (reverse γ).solution.velocity htrev
  have horig := LocalGeodesicData.tangentField_eq_coordinateFrameCombination
    (I := I) (M := M) (E := E) cov x₀
      (canonicalBasis (E := E)) γ.solution γ.solution.velocity htneg
  have hcurve : (reverse γ).solution.curve t = γ.solution.curve (-t) := by
    simpa [curve] using reverse_curve γ t
  rw [velocity, hrev, velocity, horig, reverse_velocity, hcurve,
    LocalGeodesicData.coordinateFrameCombination_neg]
  rfl

/-- Positively rescale an intrinsic local geodesic.  This is the manifold
counterpart of the quadratic coordinate-spray rescaling: the new curve is
the original curve evaluated at `a * t` and starts at `a • v₀`. -/
noncomputable def rescale
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    (a : ℝ) (ha : 0 < a) :
    LocalGeodesic (I := I) (M := M) cov x₀ (a • v₀) := by
  let solRescale := LocalGeodesicData.LocalChartSecondOrderSolution.rescale
    (cov := cov) (x₀ := x₀) (b := canonicalBasis (E := E)) γ.solution a ha
  have hcoord : LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E)
      x₀ (a • v₀) = a • LocalGeodesicData.coordinateVelocity
        (I := I) (M := M) (E := E) x₀ v₀ := by
    simp [LocalGeodesicData.coordinateVelocity]
  let sol' : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration cov x₀
        (canonicalBasis (E := E))) x₀
      (LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E)
        x₀ (a • v₀)) :=
    LocalChartSecondOrderSolution.castInitialVelocity hcoord solRescale
  exact ⟨sol', LocalGeodesicData.local_solution_isCoordinateGeodesic
    (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀)
      (b := canonicalBasis (E := E)) sol'⟩

@[simp] lemma rescale_coordinate
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    (a : ℝ) (ha : 0 < a) (t : ℝ) :
    (rescale γ a ha).solution.coordinate t = γ.solution.coordinate (a * t) := by
  simp [rescale, LocalGeodesicData.LocalChartSecondOrderSolution.rescale]

@[simp] lemma rescale_velocity
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    (a : ℝ) (ha : 0 < a) (t : ℝ) :
    (rescale γ a ha).solution.velocity t = a • γ.solution.velocity (a * t) := by
  simp [rescale, LocalGeodesicData.LocalChartSecondOrderSolution.rescale]

@[simp] lemma rescale_radius
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    (a : ℝ) (ha : 0 < a) :
    (rescale γ a ha).solution.radius = γ.solution.radius / a := by
  simp [rescale, LocalGeodesicData.LocalChartSecondOrderSolution.rescale]

lemma rescale_curve
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    (a : ℝ) (ha : 0 < a) (t : ℝ) :
    curve (rescale γ a ha) t = curve γ (a * t) := by
  simp [curve, LocalChartSecondOrderSolution.curve, Function.comp_apply]

lemma rescale_actual_velocity
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    (a : ℝ) (ha : 0 < a) {t : ℝ}
    (ht : a * t ∈ Ioo (-γ.solution.radius) γ.solution.radius) :
    velocity (rescale γ a ha) t = a • velocity γ (a * t) := by
  have htRescale : t ∈ Ioo (-(rescale γ a ha).solution.radius)
      (rescale γ a ha).solution.radius := by
    rw [rescale_radius]
    constructor
    · have hneg : -γ.solution.radius / a < t :=
        (div_lt_iff₀ ha).2 (by simpa only [mul_comm] using ht.1)
      simpa only [neg_div] using hneg
    · exact (lt_div_iff₀ ha).2 (by simpa only [mul_comm] using ht.2)
  have hscaled := LocalGeodesicData.tangentField_eq_coordinateFrameCombination
    (I := I) (M := M) (E := E) cov x₀ (canonicalBasis (E := E))
      (rescale γ a ha).solution (rescale γ a ha).solution.velocity htRescale
  have horig := LocalGeodesicData.tangentField_eq_coordinateFrameCombination
    (I := I) (M := M) (E := E) cov x₀ (canonicalBasis (E := E))
      γ.solution γ.solution.velocity ht
  have hcurve : (rescale γ a ha).solution.curve t =
      γ.solution.curve (a * t) := by
    simpa only [curve] using rescale_curve γ a ha t
  rw [velocity, hscaled, velocity, horig, rescale_velocity, hcurve,
    LocalGeodesicData.coordinateFrameCombination_smul]
  rfl

end LocalGeodesic

/-- Package a chart-coordinate geodesic solution as an intrinsic local
geodesic.  The initial model-space velocity is read back through the tangent
bundle trivialization, so the resulting object carries its actual initial
tangent vector rather than a coordinate surrogate. -/
noncomputable def LocalGeodesic.of_coordinateSolution
    {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {c : M} {u : E}
    (sol : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration cov c
        (canonicalBasis (E := E))) c u) :
    LocalGeodesic (I := I) (M := M) cov c
      ((trivializationAt E (TangentSpace I : M → Type _) c).symmL ℝ c u) := by
  let v : TangentSpace I c :=
    (trivializationAt E (TangentSpace I : M → Type _) c).symmL ℝ c u
  have hv : LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E) c v = u := by
    dsimp [v, LocalGeodesicData.coordinateVelocity]
    exact (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt_symmL
      (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) c) u
  let sol' : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration cov c
        (canonicalBasis (E := E))) c
      (LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E) c v) :=
    LocalChartSecondOrderSolution.castInitialVelocity hv sol
  exact ⟨sol', LocalGeodesicData.local_solution_isCoordinateGeodesic
    (I := I) (M := M) (E := E) (cov := cov) (x₀ := c)
      (b := canonicalBasis (E := E)) sol'⟩

@[simp] theorem LocalGeodesic.of_coordinateSolution_coordinate
    {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {c : M} {u : E}
    (sol : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration cov c
        (canonicalBasis (E := E))) c u) :
    (LocalGeodesic.of_coordinateSolution (I := I) (M := M) sol).solution.coordinate =
      sol.coordinate := by
  simp [LocalGeodesic.of_coordinateSolution]

@[simp] theorem LocalGeodesic.of_coordinateSolution_velocity
    {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {c : M} {u : E}
    (sol : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration cov c
        (canonicalBasis (E := E))) c u) :
    (LocalGeodesic.of_coordinateSolution (I := I) (M := M) sol).solution.velocity =
      sol.velocity := by
  simp [LocalGeodesic.of_coordinateSolution]

@[simp] theorem LocalGeodesic.of_coordinateSolution_radius
    {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {c : M} {u : E}
    (sol : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration cov c
        (canonicalBasis (E := E))) c u) :
    (LocalGeodesic.of_coordinateSolution (I := I) (M := M) sol).solution.radius =
      sol.radius := by
  simp [LocalGeodesic.of_coordinateSolution]

@[simp] theorem LocalGeodesic.of_coordinateSolution_curve
    {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {c : M} {u : E}
    (sol : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration cov c
        (canonicalBasis (E := E))) c u) :
    LocalGeodesic.curve
      (LocalGeodesic.of_coordinateSolution (I := I) (M := M) sol) =
        LocalChartSecondOrderSolution.curve sol := by
  funext t
  simp [LocalGeodesic.curve, LocalChartSecondOrderSolution.curve,
    Function.comp_apply]

/-! ### Local chart-independent uniqueness

The ODE uniqueness theorem gives equality of the coordinate and model-space
velocity components.  The following statement transports that equality back
through the fixed chart.  `HEq` is intentional: tangent vectors at the two
curves initially live in fibres over points that have not yet been identified
by a definitional equality.
-/

theorem eventuallyEq_curve_velocity_of_same_initial
    (cov : CovariantDerivative I E (TangentSpace I : M → Type u))
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (x₀ : M) (v₀ : TangentSpace I x₀)
    (γ₁ γ₂ : LocalGeodesic (I := I) (M := M) cov x₀ v₀) :
    (LocalGeodesic.curve γ₁ =ᶠ[𝓝 (0 : ℝ)] LocalGeodesic.curve γ₂) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), HEq (LocalGeodesic.velocity γ₁ t)
        (LocalGeodesic.velocity γ₂ t)) := by
  have hcoord := LocalGeodesicData.coordinateGeodesic_eventuallyEq_of_same_initial
    (I := I) (M := M) (E := E) (H := H) cov x₀
      (canonicalBasis (E := E)) γ₁.solution γ₂.solution
  have hI₁ : Ioo (-γ₁.solution.radius) γ₁.solution.radius ∈ 𝓝 (0 : ℝ) := by
    exact Ioo_mem_nhds (by linarith [γ₁.solution.radius_pos])
      (by linarith [γ₁.solution.radius_pos])
  have hI₂ : Ioo (-γ₂.solution.radius) γ₂.solution.radius ∈ 𝓝 (0 : ℝ) := by
    exact Ioo_mem_nhds (by linarith [γ₂.solution.radius_pos])
      (by linarith [γ₂.solution.radius_pos])
  constructor
  · filter_upwards [hcoord, hI₁, hI₂] with t hpair ht₁ ht₂
    have hcoordinate : γ₁.solution.coordinate t = γ₂.solution.coordinate t :=
      congrArg Prod.fst hpair
    simpa [LocalGeodesic.curve, LocalChartSecondOrderSolution.curve,
      Function.comp_apply] using
      congrArg (extChartAt I x₀).symm hcoordinate
  · filter_upwards [hcoord, hI₁, hI₂] with t hpair ht₁ ht₂
    have hcoordinate : γ₁.solution.coordinate t = γ₂.solution.coordinate t :=
      congrArg Prod.fst hpair
    have hvelocity : γ₁.solution.velocity t = γ₂.solution.velocity t :=
      congrArg Prod.snd hpair
    have hcurve : γ₁.solution.curve t = γ₂.solution.curve t := by
      simpa [LocalChartSecondOrderSolution.curve, Function.comp_apply] using
        congrArg (extChartAt I x₀).symm hcoordinate
    have hfield₁ := LocalGeodesicData.tangentField_eq_coordinateFrameCombination
      (I := I) (M := M) (E := E) (H := H) cov x₀
        (canonicalBasis (E := E)) γ₁.solution γ₁.solution.velocity ht₁
    have hfield₂ := LocalGeodesicData.tangentField_eq_coordinateFrameCombination
      (I := I) (M := M) (E := E) (H := H) cov x₀
        (canonicalBasis (E := E)) γ₂.solution γ₂.solution.velocity ht₂
    rw [LocalGeodesic.velocity, hfield₁, LocalGeodesic.velocity, hfield₂]
    rw [hcurve, hvelocity]
    rfl

/-- Two intrinsic local geodesics with the same initial tangent state agree as
manifold-valued curves throughout the common interval of their coordinate
certificates.  Unlike germ uniqueness, this can identify a prescribed nearby
endpoint of either solution. -/
theorem LocalGeodesic.curve_eqOn_common_interval_of_same_initial
    (cov : CovariantDerivative I E (TangentSpace I : M → Type u))
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (x₀ : M) (v₀ : TangentSpace I x₀)
    (γ₁ γ₂ : LocalGeodesic (I := I) (M := M) cov x₀ v₀) :
    Set.EqOn (LocalGeodesic.curve γ₁) (LocalGeodesic.curve γ₂)
      (Ioo (-(min γ₁.solution.radius γ₂.solution.radius))
        (min γ₁.solution.radius γ₂.solution.radius)) := by
  have hpair := LocalChartSecondOrderSolution.pair_eqOn_common_interval_of_same_initial
    γ₁.solution γ₂.solution (by
      intro t ht
      exact LocalGeodesicData.coordinateAcceleration_system_contDiffAt_of_mem_target
        (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀)
        (b := canonicalBasis (E := E))
        (γ₁.solution.coordinate_mem_target t (by
          have hle : min γ₁.solution.radius γ₂.solution.radius ≤
              γ₁.solution.radius := min_le_left _ _
          constructor <;> linarith [ht.1, ht.2]))
        (γ₁.solution.velocity t))
  intro t ht
  have hcoord : γ₁.solution.coordinate t = γ₂.solution.coordinate t :=
    congrArg Prod.fst (hpair ht)
  exact congrArg (extChartAt I x₀).symm hcoord

/-! ### Recovering tangent state from a curve germ

The next two lemmas are the coherence input for a maximal-extension
construction.  A curve germ already determines its tangent velocity germ:
after a time translation, two local geodesics which agree as manifold-valued
curves also agree as tangent-bundle-valued states.  This is proved through
uniqueness of the manifold derivative, rather than by choosing coordinates. -/

open LocalGeodesic

variable {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}

/-- Equality of shifted local-geodesic curve germs determines equality of
their tangent-velocity germs. -/
theorem eventuallyEq_velocity_of_eventuallyEq_curve_shift
    {y₀ : M} {w₀ : TangentSpace I y₀}
    (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    (δ : LocalGeodesic (I := I) (M := M) cov y₀ w₀)
    {τ : ℝ} (hτ : τ ∈ Ioo (-γ.solution.radius) γ.solution.radius)
    (hcurve : (fun s ↦ curve γ (τ + s)) =ᶠ[𝓝 (0 : ℝ)] curve δ) :
    ∀ᶠ s in 𝓝 (0 : ℝ), HEq (velocity γ (τ + s)) (velocity δ s) := by
  obtain ⟨U, hUsub, hUopen, hUzero⟩ := mem_nhds_iff.mp hcurve
  have hU : U ∈ 𝓝 (0 : ℝ) := hUopen.mem_nhds hUzero
  have hγinterval' : Ioo (-γ.solution.radius - τ)
      (γ.solution.radius - τ) ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith [hτ.1]) (by linarith [hτ.2])
  have hδinterval : Ioo (-δ.solution.radius) δ.solution.radius ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith [δ.solution.radius_pos])
      (by linarith [δ.solution.radius_pos])
  filter_upwards [hU, hγinterval', hδinterval] with s hsU hsγ hsδ
  have hsγ' : τ + s ∈ Ioo (-γ.solution.radius) γ.solution.radius := by
    constructor <;> linarith [hsγ.1, hsγ.2]
  have heq : (fun r ↦ curve γ (τ + r)) =ᶠ[𝓝 s] curve δ := by
    apply Filter.mem_of_superset (hUopen.mem_nhds hsU)
    exact hUsub
  have hadd : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ))
      (fun r : ℝ ↦ τ + r) s (ContinuousLinearMap.id ℝ _) := by
    have hconst : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ))
        (fun _ : ℝ ↦ τ) s 0 := hasMFDerivAt_const τ s
    have hid : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ))
        (fun r : ℝ ↦ r) s (ContinuousLinearMap.id ℝ _) := hasMFDerivAt_id s
    have hfun : (fun r : ℝ ↦ τ + r) = (fun _ : ℝ ↦ τ) + (fun r : ℝ ↦ r) := by
      funext r
      rfl
    rw [hfun]
    exact (hconst.add hid).congr_mfderiv (zero_add _)
  have hleft : HasMFDerivAt (𝓘(ℝ, ℝ)) I
      (fun r ↦ curve γ (τ + r)) s
      (ContinuousLinearMap.toSpanSingleton ℝ (velocity γ (τ + s))) := by
    have h := (hasMFDerivAt_curve γ hsγ').comp s hadd
    apply h.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro r
    rfl
  have hright := hasMFDerivAt_curve δ hsδ
  have hleft' := hleft.congr_of_eventuallyEq heq.symm
  have hmaps := hasMFDerivAt_unique hleft' hright
  have hvalue : (ContinuousLinearMap.toSpanSingleton ℝ (velocity γ (τ + s))) 1 =
      (ContinuousLinearMap.toSpanSingleton ℝ (velocity δ s)) 1 :=
    congrArg (fun f ↦ f 1) hmaps
  have hvalue' := hvalue
  simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at hvalue'
  exact heq_of_eq hvalue'

/-- The preceding velocity coherence upgrades curve-germ equality to equality
of the complete tangent-bundle state germ. -/
theorem eventuallyEq_state_of_eventuallyEq_curve_shift
    {y₀ : M} {w₀ : TangentSpace I y₀}
    (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    (δ : LocalGeodesic (I := I) (M := M) cov y₀ w₀)
    {τ : ℝ} (hτ : τ ∈ Ioo (-γ.solution.radius) γ.solution.radius)
    (hcurve : (fun s ↦ curve γ (τ + s)) =ᶠ[𝓝 (0 : ℝ)] curve δ) :
    (fun s ↦ (⟨curve γ (τ + s), velocity γ (τ + s)⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _))) =ᶠ[𝓝 (0 : ℝ)]
      fun s ↦ ⟨curve δ s, velocity δ s⟩ := by
  have hvelocity := eventuallyEq_velocity_of_eventuallyEq_curve_shift
    (I := I) (M := M) γ δ hτ hcurve
  filter_upwards [hcurve, hvelocity] with s hcurve hvelocity
  exact Bundle.TotalSpace.ext hcurve hvelocity

end IntrinsicGeodesic

end BonnetMyersEntry
