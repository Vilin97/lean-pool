/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurck
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacianLocalFrame

/-!
# The standard DeTurck vector field

This file records the geometric DeTurck vector used in the Ricci--DeTurck
equation.  It is the metric contraction of *both* input slots of the
difference between the metric Levi-Civita connection and a background
connection:

`W = tr_g (∇ᵍ - ∇̄)`.

The older `intrinsicDeTurckVectorField` remains available for its existing
uses, but it traces only one varying input slot and is therefore a different
construction.  In particular, no theorem in this file identifies the two.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff Topology

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

section ChosenLeviCivita

variable [SigmaCompactSpace M]

/-- The two-input tensor `∇ᵍ - ∇̄` whose metric contraction is the standard
DeTurck vector field.  The first input is the covariant-derivative direction
and the second is the differentiated vector. -/
def standardDeTurckDifferenceBilinear
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) :
    TM x →L[ℝ] TM x →L[ℝ] TM x :=
  ContinuousLinearMap.flipₗᵢ ℝ (TM x) (TM x) (TM x)
    (CovariantDerivative.difference
      ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x)

@[simp] theorem standardDeTurckDifferenceBilinear_apply
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    standardDeTurckDifferenceBilinear (I := I) (M := M) g background t x u v =
      (CovariantDerivative.difference
        ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x v) u := rfl

/-- The standard DeTurck vector `W = tr_g(∇ᵍ - ∇̄)`.  Unlike the legacy
trace-one-form construction, this contracts both lower connection indices and
leaves the connection output as a tangent vector. -/
noncomputable def standardDeTurckVectorField
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) : TM x := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let B := standardDeTurckDifferenceBilinear (I := I) (M := M) g background t x
  let L : TM x →ₗ[ℝ] TM x →ₗ[ℝ] TM x :=
    { toFun := fun u => (B u).toLinearMap
      map_add' := by
        intro u v
        ext w
        exact congrArg (fun q : TM x →L[ℝ] TM x => q w) (B.map_add u v)
      map_smul' := by
        intro c u
        ext w
        exact congrArg (fun q : TM x →L[ℝ] TM x => q w) (B.map_smul c u) }
  exact TensorProduct.lift L
    (InnerProductSpace.canonicalCovariantTensor (TM x))

/-- In an arbitrary local frame, the standard DeTurck vector contracts the
two connection inputs with the inverse metric Gram matrix.  This is the
coordinate-free local formula whose components are
`g^{ab} (Γ(g)^k_ab - Γ(background)^k_ab)`. -/
theorem standardDeTurckVectorField_eq_sum_localFrame_inverseGram
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet) :
    standardDeTurckVectorField (I := I) (M := M) g background t x =
      (letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
       ∑ i : ι, ∑ j : ι,
         CovariantDerivative.localFrameInverseGramMatrix (I := I) e b x i j •
           (CovariantDerivative.difference
             ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t) x
             (e.localFrame b j x)) (e.localFrame b i x)) := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  rw [standardDeTurckVectorField,
    CovariantDerivative.canonicalCovariantTensor_eq_sum_localFrame_inverseGram
      (I := I) (E := E) e b hx, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [TensorProduct.lift.tmul, LinearMapClass.map_smul]
  rfl

end ChosenLeviCivita

end RicciFlow
