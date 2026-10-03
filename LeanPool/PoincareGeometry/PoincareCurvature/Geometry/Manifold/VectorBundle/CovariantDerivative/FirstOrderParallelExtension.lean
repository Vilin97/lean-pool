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

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacianCoordinate
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor

/-!
# First-order parallel extensions

This module constructs a genuine local first jet for a vector-bundle section.
Centered manifold coordinates provide scalar coordinate functions with a
prescribed differential.  Multiplying those functions by smooth bundle
extensions realizes an arbitrary covariant derivative at the center.

Subtracting the first jet of an initial smooth extension therefore produces a
section with any prescribed value and vanishing covariant derivative at the
center.  This is the intrinsic contact-vector extension needed in tensor
maximum-principle arguments.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The actual tangent fibre at the center, in its centered model coordinates. -/
def centeredTangentCoordinate (x : M) : TM x ≃L[ℝ] E :=
  let hx : x ∈ (trivializationAt E TM x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  (trivializationAt E TM x).continuousLinearEquivAt ℝ x hx

/-- Convert centered model coordinates back to the actual tangent fibre. -/
def tangentOfCenteredCoordinate (x : M) : E ≃L[ℝ] TM x :=
  (centeredTangentCoordinate (I := I) x).symm

theorem centeredTangentCoordinate_eq_mfderiv_extChartAt
    (x : M) :
    (centeredTangentCoordinate (I := I) x : TM x →L[ℝ] E) =
      mfderiv I 𝓘(ℝ, E) (extChartAt I x) x := by
  rw [centeredTangentCoordinate]
  rw [Bundle.Trivialization.coe_continuousLinearEquivAt_eq']
  rw [TangentBundle.continuousLinearMapAt_trivializationAt]
  simp

@[simp] theorem tangentOfCenteredCoordinate_centeredTangentCoordinate
    (x : M) (u : TM x) :
    tangentOfCenteredCoordinate (I := I) x
      (centeredTangentCoordinate (I := I) x u) = u := by
  exact (centeredTangentCoordinate (I := I) x).symm_apply_apply u

@[simp] theorem centeredTangentCoordinate_tangentOfCenteredCoordinate
    (x : M) (u : E) :
    centeredTangentCoordinate (I := I) x
      (tangentOfCenteredCoordinate (I := I) x u) = u := by
  exact (centeredTangentCoordinate (I := I) x).apply_symm_apply u

/-- A tangent-basis coordinate of displacement from a chart center. -/
def tangentBasisChartDisplacementCoordinate
    {ι : Type*} [Fintype ι] (x : M)
    (b : Module.Basis ι ℝ (TM x)) (i : ι) (y : M) : ℝ :=
  b.coord i (tangentOfCenteredCoordinate (I := I) x
    ((extChartAt I x) y - (extChartAt I x) x))

theorem hasMFDerivAt_tangentBasisChartDisplacementCoordinate
    {ι : Type*} [Fintype ι] (x : M)
    (b : Module.Basis ι ℝ (TM x)) (i : ι) :
    HasMFDerivAt I 𝓘(ℝ)
      (tangentBasisChartDisplacementCoordinate (I := I) x b i)
      x (LinearMap.toContinuousLinearMap (b.coord i)) := by
  change HasMFDerivAt I 𝓘(ℝ)
    (tangentBasisChartDisplacementCoordinate (I := I) x b i) x
      ((NormedSpace.fromTangentSpace
        (tangentBasisChartDisplacementCoordinate (I := I) x b i x)).symm.toContinuousLinearMap.comp
          (LinearMap.toContinuousLinearMap (b.coord i)))
  let D : TM x →L[ℝ] E := mfderiv I 𝓘(ℝ, E) (extChartAt I x) x
  let T : E →L[ℝ] TM x := tangentOfCenteredCoordinate (I := I) x
  let L : TM x →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.coord i)
  let B : E →L[ℝ] ℝ := L.comp T
  have hchart : HasMFDerivAt I 𝓘(ℝ, E) (extChartAt I x) x D :=
    ((contMDiffAt_extChartAt (I := I) (n := (1 : WithTop ℕ∞))
      (x := x)).mdifferentiableAt one_ne_zero).hasMFDerivAt
  have hconst : HasMFDerivAt I 𝓘(ℝ, E)
      (fun _ : M => (extChartAt I x) x) x 0 :=
    hasMFDerivAt_const _ _
  have hsub := hchart.sub hconst
  have hB : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ) B
      ((extChartAt I x) x - (extChartAt I x) x) B :=
    B.hasFDerivAt.hasMFDerivAt
  have hsub' : HasMFDerivAt I 𝓘(ℝ, E)
      (fun y ↦ (extChartAt I x) y - (extChartAt I x) x) x D := by
    unfold HasMFDerivAt at hsub ⊢
    refine ⟨hsub.1, ?_⟩
    convert! hsub.2 using 1
    ext u
    change D _ = D _ - 0
    simp only [sub_zero]
    rfl
  have hcomp := hB.comp x hsub'
  have hderiv : B.comp D = L := by
    ext u
    simp only [ContinuousLinearMap.comp_apply]
    change L (tangentOfCenteredCoordinate (I := I) x (D u)) = L u
    change L (tangentOfCenteredCoordinate (I := I) x
      ((mfderiv I 𝓘(ℝ, E) (extChartAt I x) x) u)) = L u
    rw [← centeredTangentCoordinate_eq_mfderiv_extChartAt (I := I) x]
    exact congrArg L
      ((centeredTangentCoordinate (I := I) x).symm_apply_apply u)
  have hfun : tangentBasisChartDisplacementCoordinate (I := I) x b i =
      B ∘ (fun y ↦ (extChartAt I x) y - (extChartAt I x) x) := rfl
  rw [hfun]
  unfold HasMFDerivAt at hcomp ⊢
  refine ⟨hcomp.1, ?_⟩
  convert! hcomp.2 using 1
  ext u
  change L _ = (B.comp D) _
  rw [hderiv]


variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ y, AddCommGroup (V y)] [∀ y, Module ℝ (V y)]
  [∀ y, TopologicalSpace (V y)] [∀ y, IsTopologicalAddGroup (V y)]
  [∀ y, ContinuousSMul ℝ (V y)] [FiberBundle F V]
  [VectorBundle ℝ F V] [FiniteDimensional ℝ F] [CompleteSpace F]
  [ContMDiffVectorBundle 2 F V I]

/-- A global smooth-at-the-center section realizing a prescribed zero value
and prescribed first covariant derivative. -/
def affineFirstJetSection
    {ι : Type*} [Fintype ι]
    (x : M) (b : Module.Basis ι ℝ (TM x))
    (A : TM x →ₗ[ℝ] V x) : ∀ y : M, V y :=
  by
    classical
    exact ∑ i : ι,
      (tangentBasisChartDisplacementCoordinate (I := I) x b i) •
        smoothExtend (I := I) (F := F) (V := V) x (A (b i))

@[simp] theorem affineFirstJetSection_apply_center
    {ι : Type*} [Fintype ι]
    (x : M) (b : Module.Basis ι ℝ (TM x))
    (A : TM x →ₗ[ℝ] V x) :
    affineFirstJetSection (I := I) (F := F) (V := V) x b A x = 0 := by
  classical
  simp [affineFirstJetSection, tangentBasisChartDisplacementCoordinate,
    smoothExtend_apply]

theorem affineFirstJetSection_mdifferentiableAt
    {ι : Type*} [Fintype ι]
    (x : M) (b : Module.Basis ι ℝ (TM x))
    (A : TM x →ₗ[ℝ] V x) :
    MDiffAt (T% (affineFirstJetSection
      (I := I) (F := F) (V := V) x b A)) x := by
  classical
  simpa [affineFirstJetSection] using
    (MDifferentiableAt.sum_section (s := (Finset.univ : Finset ι))
      (fun i _ =>
        (hasMFDerivAt_tangentBasisChartDisplacementCoordinate
          (I := I) x b i).mdifferentiableAt.smul_section
          ((smoothExtend_contMDiff_one (I := I) (F := F) (V := V)
            x (A (b i))).mdifferentiableAt one_ne_zero)))

/-- Finite Leibniz expansion used by the first-jet construction. -/
private theorem covariantDerivative_sum_smul_apply_firstJet
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I F V)
    (c : ι → M → ℝ) (σ : ι → ∀ y : M, V y) {x : M}
    (hc : ∀ i, MDiffAt (c i) x) (hσ : ∀ i, MDiffAt (T% (σ i)) x)
    (u : TM x) :
    cov (∑ i : ι, c i • σ i) x u =
      ∑ i : ι, ((c i x) • cov (σ i) x u +
        mvfderiv (I := I) (c i) x u • σ i x) := by
  classical
  have hfinite (s : Finset ι) :
      cov (∑ i ∈ s, c i • σ i) x u =
        ∑ i ∈ s, ((c i x) • cov (σ i) x u +
          mvfderiv (I := I) (c i) x u • σ i x) := by
    induction s using Finset.induction_on with
    | empty =>
        have hz := cov.isCovariantDerivativeOn.zero (x := x)
        have hzu := congrArg (fun L : TM x →L[ℝ] V x => L u) hz
        simpa using hzu
    | @insert i s hi ih =>
        have hterm : MDiffAt (T% (c i • σ i)) x :=
          (hc i).smul_section (hσ i)
        have hrest : MDiffAt (T% (∑ j ∈ s, c j • σ j)) x := by
          have hr := MDifferentiableAt.sum_section (s := s)
            (fun j _ => (hc j).smul_section (hσ j))
          convert hr using 1 <;> ext y <;> simp
        have hadd := cov.isCovariantDerivativeOn.add hterm hrest (x := x)
        have hleibniz := cov.isCovariantDerivativeOn.leibniz
          (hσ i) (hc i) (x := x)
        have hadd_u := congrArg (fun L : TM x →L[ℝ] V x => L u) hadd
        have hleibniz_u :=
          congrArg (fun L : TM x →L[ℝ] V x => L u) hleibniz
        simp only [Finset.sum_insert hi]
        simp only [add_apply, smul_apply,
          ContinuousLinearMap.smulRight_apply] at hadd_u hleibniz_u
        rw [hadd_u, hleibniz_u, ih]
  simpa using hfinite Finset.univ

/-- The affine first-jet section realizes exactly the prescribed covariant
derivative at its center. -/
theorem covariantDerivative_affineFirstJetSection
    {ι : Type*} [Fintype ι]
    (cov : CovariantDerivative I F V)
    (x : M) (b : Module.Basis ι ℝ (TM x))
    (A : TM x →ₗ[ℝ] V x) (u : TM x) :
    cov (affineFirstJetSection
      (I := I) (F := F) (V := V) x b A) x u = A u := by
  classical
  have h := covariantDerivative_sum_smul_apply_firstJet
    (I := I) cov
    (fun i => tangentBasisChartDisplacementCoordinate (I := I) x b i)
    (fun i => smoothExtend (I := I) (F := F) (V := V) x (A (b i)))
    (fun i => (hasMFDerivAt_tangentBasisChartDisplacementCoordinate
      (I := I) x b i).mdifferentiableAt)
    (fun i => (smoothExtend_contMDiff_one (I := I) (F := F) (V := V)
      x (A (b i))).mdifferentiableAt one_ne_zero) u
  rw [show affineFirstJetSection (I := I) (F := F) (V := V) x b A =
      ∑ i : ι,
        (tangentBasisChartDisplacementCoordinate (I := I) x b i) •
          smoothExtend (I := I) (F := F) (V := V) x (A (b i)) by rfl]
  rw [h]
  simp only [tangentBasisChartDisplacementCoordinate, sub_self,
    map_zero, zero_smul, zero_add,
    smoothExtend_apply]
  simp_rw [mvfderiv,
    (hasMFDerivAt_tangentBasisChartDisplacementCoordinate
      (I := I) x b _).mfderiv]
  change (∑ i : ι, (b.coord i u) • A (b i)) = A u
  calc
    (∑ i : ι, (b.coord i u) • A (b i)) =
        ∑ i : ι, A ((b.coord i u) • b i) := by simp
    _ = A (∑ i : ι, (b.coord i u) • b i) := by rw [map_sum]
    _ = A u := by rw [show (∑ i : ι, (b.coord i u) • b i) = u by
      exact b.sum_repr u]

/-- A canonical finite basis of the actual tangent fibre. -/
def tangentFiberBasis (x : M) :
    Module.Basis (Module.Basis.ofVectorSpaceIndex ℝ (TM x)) ℝ (TM x) :=
  Module.Basis.ofVectorSpace ℝ (TM x)

/-- A smooth-at-the-center extension whose prescribed value has vanishing
first covariant derivative at the center. -/
def firstOrderParallelSmoothExtend
    (cov : CovariantDerivative I F V) (x : M) (v : V x) : ∀ y : M, V y :=
  let σ := smoothExtend (I := I) (F := F) (V := V) x v
  let A : TM x →ₗ[ℝ] V x := -(cov σ x).toLinearMap
  σ + affineFirstJetSection (I := I) (F := F) (V := V)
    x (tangentFiberBasis (I := I) x) A

@[simp] theorem firstOrderParallelSmoothExtend_apply_center
    (cov : CovariantDerivative I F V) (x : M) (v : V x) :
    firstOrderParallelSmoothExtend
      (I := I) (F := F) (V := V) cov x v x = v := by
  simp [firstOrderParallelSmoothExtend, smoothExtend_apply]

theorem firstOrderParallelSmoothExtend_mdifferentiableAt
    (cov : CovariantDerivative I F V) (x : M) (v : V x) :
    MDiffAt (T% (firstOrderParallelSmoothExtend
      (I := I) (F := F) (V := V) cov x v)) x := by
  apply mdifferentiableAt_add_section
  · exact (smoothExtend_contMDiff_one (I := I) (F := F) (V := V)
      x v).mdifferentiableAt one_ne_zero
  · exact affineFirstJetSection_mdifferentiableAt
      (I := I) (F := F) (V := V) x (tangentFiberBasis (I := I) x)
        (-(cov (smoothExtend (I := I) (F := F) (V := V) x v) x).toLinearMap)

/-- The canonical first-order parallel extension has zero covariant
derivative at its center, with no parallel-field hypothesis. -/
theorem covariantDerivative_firstOrderParallelSmoothExtend_eq_zero
    (cov : CovariantDerivative I F V) (x : M) (v : V x) :
    cov (firstOrderParallelSmoothExtend
      (I := I) (F := F) (V := V) cov x v) x = 0 := by
  let σ := smoothExtend (I := I) (F := F) (V := V) x v
  let b := tangentFiberBasis (I := I) x
  let A : TM x →ₗ[ℝ] V x := -(cov σ x).toLinearMap
  have hσ : MDiffAt (T% σ) x :=
    (smoothExtend_contMDiff_one (I := I) (F := F) (V := V)
      x v).mdifferentiableAt one_ne_zero
  have hA : MDiffAt (T% (affineFirstJetSection
      (I := I) (F := F) (V := V) x b A)) x :=
    affineFirstJetSection_mdifferentiableAt
      (I := I) (F := F) (V := V) x b A
  have hadd := cov.isCovariantDerivativeOn.add hσ hA (x := x)
  change cov (σ + affineFirstJetSection
      (I := I) (F := F) (V := V) x b A) x = 0
  rw [hadd]
  have hcor := covariantDerivative_affineFirstJetSection
    (I := I) cov x b A
  ext u
  rw [add_apply, hcor]
  simp [A]

end CovariantDerivative
