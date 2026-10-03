/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatClosedExistence
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.SpatialInitialExtension

/-!
# Concrete spatial initial data for the closed tensor heat theorem

This file replaces an arbitrary space-time higher extension by bounded
spatial `C^{2,α}` data in every member of the finite atlas.  The canonical
extension is constant in normalized time, has exactly the supplied initial
trace, and is bounded by an explicit finite-atlas spatial norm.
-/

@[expose] public section

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology

namespace RicciFlow
namespace AnalyticPDE

variable {X V : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

@[reducible] local instance atlasSpatialDataFirstNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance atlasSpatialDataFirstNormedSpace :
    NormedSpace ℝ (X →L[ℝ] V) := ContinuousLinearMap.toNormedSpace
@[reducible] local instance atlasSpatialDataSecondNormedAddCommGroup :
    NormedAddCommGroup (X →L[ℝ] X →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance atlasSpatialDataSecondNormedSpace :
    NormedSpace ℝ (X →L[ℝ] X →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace

namespace BoundedSpatialC2AlphaData

/-- An explicit norm radius for bounded spatial `C^{2,α}` data. -/
def normRadius {α : ℝ} (D : BoundedSpatialC2AlphaData X V α) : ℝ :=
  max (‖D.value‖ + D.holderConstant)
    (max (‖D.spaceDeriv‖ + D.holderConstant)
      (‖D.spaceSecondDeriv‖ + D.holderConstant))

theorem normRadius_nonneg {α : ℝ}
    (D : BoundedSpatialC2AlphaData X V α) : 0 ≤ D.normRadius := by
  unfold normRadius
  exact (add_nonneg (norm_nonneg D.value) D.holderConstant_nonneg).trans
    (le_max_left _ _)

private theorem parabolicC0AlphaNormLe_snd
    {F : Type*} [NormedAddCommGroup F]
    (f : BoundedContinuousFunction X F) {α H : ℝ}
    (hα : 0 ≤ α) (hH : 0 ≤ H)
    (hholder : ∀ x y, ‖f x - f y‖ ≤ H * dist x y ^ α)
    (s : Set (ℝ × X)) :
    ParabolicC0AlphaNormLe (‖f‖ + H) α (fun z : ℝ × X => f z.2) s := by
  refine ⟨‖f‖, norm_nonneg _, H, hH, le_rfl, ?_⟩
  constructor
  · intro z _hz
    exact f.norm_coe_le_norm z.2
  · intro p _hp q _hq
    calc
      ‖f p.2 - f q.2‖ ≤ H * dist p.2 q.2 ^ α := hholder p.2 q.2
      _ ≤ H * parabolicDistance p q ^ α := by
        apply mul_le_mul_of_nonneg_left _ hH
        exact Real.rpow_le_rpow dist_nonneg
          (parabolicDistance.space_dist_le p q) hα

/-- The constant-in-time higher extension is controlled by the explicit
spatial `C^{2,α}` radius. -/
theorem norm_timeIndependentExtension_le
    {α t₀ T : ℝ} (D : BoundedSpatialC2AlphaData X V α)
    (hα : 0 < α) :
    ‖D.timeIndependentExtension (t₀ := t₀) (T := T) hα‖ ≤
      D.normRadius := by
  let Nv := ‖D.value‖ + D.holderConstant
  let N₁ := ‖D.spaceDeriv‖ + D.holderConstant
  let N₂ := ‖D.spaceSecondDeriv‖ + D.holderConstant
  have hv : ParabolicC0AlphaNormLe Nv α
      (fun z : ℝ × X => D.value z.2)
      (parabolicFiniteCylinder X t₀ T) :=
    parabolicC0AlphaNormLe_snd D.value hα.le D.holderConstant_nonneg
      D.value_holder _
  have h₁ : ParabolicC0AlphaNormLe N₁ α
      (fun z : ℝ × X => D.spaceDeriv z.2)
      (parabolicFiniteCylinder X t₀ T) :=
    parabolicC0AlphaNormLe_snd D.spaceDeriv hα.le
      D.holderConstant_nonneg D.spaceDeriv_holder _
  have h₂ : ParabolicC0AlphaNormLe N₂ α
      (fun z : ℝ × X => D.spaceSecondDeriv z.2)
      (parabolicFiniteCylinder X t₀ T) :=
    parabolicC0AlphaNormLe_snd D.spaceSecondDeriv hα.le
      D.holderConstant_nonneg D.spaceSecondDeriv_holder _
  have hNv : Nv ≤ D.normRadius := by
    unfold normRadius Nv
    exact le_max_left _ _
  have hN₁ : N₁ ≤ D.normRadius := by
    unfold normRadius N₁
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hN₂ : N₂ ≤ D.normRadius := by
    unfold normRadius N₂
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hz : ParabolicC0AlphaNormLe D.normRadius α
      (fun _z : ℝ × X => (0 : V))
      (parabolicFiniteCylinder X t₀ T) := by
    exact (ParabolicC0AlphaNormLe.zero (X := X) (E := V)
      (α := α) (s := parabolicFiniteCylinder X t₀ T)).mono_const
        D.normRadius_nonneg
  unfold timeIndependentExtension
  apply FiniteParabolicC2AlphaBanach.norm_ofSecondJet_le
  · exact hv.mono_const hNv
  · exact h₁.mono_const hN₁
  · exact h₂.mono_const hN₂
  · simpa [timeIndependentSecondJet] using hz

end BoundedSpatialC2AlphaData

namespace FiniteTensorHeatParametrixAtlas

open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [CompactSpace M] [SigmaCompactSpace M] [I.Boundaryless] [Nonempty M]

variable {d : ℕ} {t₀ T α : ℝ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)
local notation "W₂" => (Fin d × Fin d → ℝ)

@[reducible] local instance atlasSpatialThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedAddCommGroup
@[reducible] local instance atlasSpatialThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedSpace
@[reducible] local instance atlasSpatialThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedAddCommGroup x
@[reducible] local instance atlasSpatialThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedSpace x
local instance atlasSpatialThreeTotalSpaceTopology :
    TopologicalSpace (TotalSpace
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance atlasSpatialThreeFiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance atlasSpatialThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂

/-- Intrinsic initial data represented by a finite family of bounded spatial
`C^{2,α}` matrix fields in the normalized tensor-heat charts. -/
abbrev AtlasSpatialInitialData
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α) :=
  A.cover.Index → BoundedSpatialC2AlphaData E W₂ α

/-- Canonical time-independent initial extension: keep every normalized spatial
datum constant in time. -/
def spatialInitialExtension
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (D : AtlasSpatialInitialData cov A) : HigherCoefficientSpace cov A :=
  fun i => (D i).timeIndependentExtension A.alpha_pos

/-- A concrete global atlas `C^{2,α}` size for spatial initial data. -/
def spatialInitialSize
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (D : AtlasSpatialInitialData cov A) : ℝ :=
  ∑ i : A.cover.Index, (D i).normRadius

theorem spatialInitialSize_nonneg
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (D : AtlasSpatialInitialData cov A) :
    0 ≤ spatialInitialSize cov A D := by
  exact Finset.sum_nonneg fun i _hi => (D i).normRadius_nonneg

/-- The canonical initial extension costs no more than the explicit spatial
atlas size. -/
theorem norm_spatialInitialExtension_le
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (D : AtlasSpatialInitialData cov A) :
    ‖spatialInitialExtension cov A D‖ ≤ spatialInitialSize cov A D := by
  apply (pi_norm_le_iff_of_nonneg
    (A.spatialInitialSize_nonneg cov D)).2
  intro i
  exact ((D i).norm_timeIndependentExtension_le A.alpha_pos).trans
    (Finset.single_le_sum
      (fun j _hj => (D j).normRadius_nonneg) (Finset.mem_univ i))

/-- The genuine global initial tensor synthesized from normalized spatial
chart data. -/
def spatialInitialTensor
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (D : AtlasSpatialInitialData cov A) : ∀ x : M, T₂ x :=
  fun x => ∑ i : A.cover.Index,
    cutoffLocalTensorOfMatrix (I := I)
      (trivializationAt E TM (i : M)) b (A.cover.partition i)
      (fun y => tensorCoordinateReconstructionEquiv d
        ((D i).value (normalizedTensorHeatCoordinate (I := I)
          (i : M) (A.radius (i : M)) y))) x

/-- The trace of the canonical extension is exactly the concrete spatial
tensor synthesized from `D`. -/
theorem atlasInitialTrace_spatialInitialExtension
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (D : AtlasSpatialInitialData cov A) :
    atlasInitialTrace cov A (spatialInitialExtension cov A D) =
      spatialInitialTensor cov A D := by
  funext x
  unfold atlasInitialTrace spatialInitialTensor localInitialTrace
    spatialInitialExtension
  apply Finset.sum_congr rfl
  intro i _hi
  rw [(D i).initialTraceL_timeIndependentExtension
    A.time_lt A.alpha_pos]

/-- An explicit constant converting the parametrix/Neumann estimate to the
standard data-norm form. -/
def strongAtlasSchauderConstant
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (Hlift : StrongCommutatorLift cov A) : ℝ :=
  1 + ‖localSolutionFamilyL cov A‖ *
    (1 - ‖Hlift.sourceLift.toContinuousLinearMap‖)⁻¹ *
      (1 + ‖localCoordinateCauchyFamilyL cov A‖ + ‖Hlift.higherMap‖)

/-- The unique strong solution satisfies the standard global Schauder shape:
one fixed geometric constant times the sum of the spatial `C^{2,α}` initial
size and the parabolic `C^{α,α/2}` source norm. -/
theorem norm_le_strongAtlasSchauderConstant_mul_data
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (hunique : HasLocalZeroTraceUniqueness cov A)
    (Hlift : StrongCommutatorLift cov A)
    (D : AtlasSpatialInitialData cov A) (f : SourceSpace cov A)
    (u : HigherCoefficientSpace cov A)
    (hu : StrongAtlasClassicalSolution cov Hlift
      (spatialInitialExtension cov A D) f u) :
    ‖u‖ ≤ strongAtlasSchauderConstant cov Hlift *
      (spatialInitialSize cov A D + ‖f‖) := by
  let h : HigherCoefficientSpace cov A := spatialInitialExtension cov A D
  let L : ℝ := ‖localSolutionFamilyL cov A‖
  let R : ℝ := (1 - ‖Hlift.sourceLift.toContinuousLinearMap‖)⁻¹
  let C₀ : ℝ := ‖localCoordinateCauchyFamilyL cov A‖
  let H₀ : ℝ := ‖Hlift.higherMap‖
  let N₀ : ℝ := spatialInitialSize cov A D
  have hL : 0 ≤ L := by
    dsimp [L]
    exact norm_nonneg (localSolutionFamilyL cov A)
  have hR : 0 ≤ R := by
    dsimp [R]
    exact inv_nonneg.mpr (sub_nonneg.mpr
      (le_of_lt Hlift.sourceLift.norm_lt_one))
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    exact norm_nonneg (localCoordinateCauchyFamilyL cov A)
  have hH₀ : 0 ≤ H₀ := by
    dsimp [H₀]
    exact norm_nonneg Hlift.higherMap
  have hN₀ : 0 ≤ N₀ := by
    dsimp [N₀]
    exact A.spatialInitialSize_nonneg cov D
  have hh : ‖h‖ ≤ N₀ := by
    simpa [h, N₀] using A.norm_spatialInitialExtension_le cov D
  have hres :
      ‖f - localCoordinateCauchyFamilyL cov A h + Hlift.higherMap h‖ ≤
        ‖f‖ + (C₀ + H₀) * ‖h‖ := by
    calc
      ‖f - localCoordinateCauchyFamilyL cov A h + Hlift.higherMap h‖ ≤
          ‖f - localCoordinateCauchyFamilyL cov A h‖ +
            ‖Hlift.higherMap h‖ := norm_add_le _ _
      _ ≤ (‖f‖ + ‖localCoordinateCauchyFamilyL cov A h‖) +
            ‖Hlift.higherMap h‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (‖f‖ + C₀ * ‖h‖) + H₀ * ‖h‖ := by
        simpa [C₀, H₀] using
          (add_le_add
            (add_le_add le_rfl
              ((localCoordinateCauchyFamilyL cov A).le_opNorm h))
            (Hlift.higherMap.le_opNorm h))
      _ = ‖f‖ + (C₀ + H₀) * ‖h‖ := by ring
  have hueq : u = strongSolutionFamily cov Hlift h f :=
    strongAtlasSolutionEquation_unique cov hunique Hlift h f
      hu.1 (strongSolutionFamily_solves cov Hlift h f)
  have hbase := norm_strongSolutionFamily_le cov Hlift h f
  rw [hueq]
  change ‖strongSolutionFamily cov Hlift h f‖ ≤ _
  calc
    ‖strongSolutionFamily cov Hlift h f‖ ≤
        ‖h‖ + L * R *
          ‖f - localCoordinateCauchyFamilyL cov A h +
            Hlift.higherMap h‖ := by simpa [L, R] using hbase
    _ ≤ ‖h‖ + L * R * (‖f‖ + (C₀ + H₀) * ‖h‖) := by
      gcongr
    _ ≤ N₀ + L * R * (‖f‖ + (C₀ + H₀) * N₀) := by
      gcongr
    _ ≤ (1 + L * R * (1 + C₀ + H₀)) * (N₀ + ‖f‖) := by
      have hLR : 0 ≤ L * R := mul_nonneg hL hR
      have hCH : 0 ≤ C₀ + H₀ := add_nonneg hC₀ hH₀
      nlinarith [norm_nonneg f, mul_nonneg hLR hCH,
        mul_nonneg hLR hN₀, mul_nonneg hCH hN₀,
        mul_nonneg hCH (norm_nonneg f)]
    _ = strongAtlasSchauderConstant cov Hlift *
        (spatialInitialSize cov A D + ‖f‖) := by
      rfl

/-- The concrete classical solution predicate for spatial initial data. It
mentions the genuine synthesized initial tensor and intrinsic source equation
directly. -/
def AtlasSpatialClassicalSolution
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (Hlift : StrongCommutatorLift cov A)
    (D : AtlasSpatialInitialData cov A) (f : SourceSpace cov A)
    (u : HigherCoefficientSpace cov A) : Prop :=
  StrongAtlasSolutionEquation cov Hlift
      (spatialInitialExtension cov A D) f u ∧
    FiniteClassicalTensorHeatField.HasInitialTrace cov
      (atlasFieldOfHigher cov A u) (spatialInitialTensor cov A D) ∧
    ∀ (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime) (x : M),
      (atlasFieldOfHigher cov A u).tensorHeatOperator cov t ht x =
        A.physicalAtlasSourceSlice cov f t x

/-- The concrete spatial-data predicate is equivalent to the strong
atlas-classical predicate for the canonical time-independent extension. -/
theorem atlasSpatialClassicalSolution_iff_strong
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (Hlift : StrongCommutatorLift cov A)
    (D : AtlasSpatialInitialData cov A) (f : SourceSpace cov A)
    (u : HigherCoefficientSpace cov A) :
    AtlasSpatialClassicalSolution cov Hlift D f u ↔
      StrongAtlasClassicalSolution cov Hlift
        (spatialInitialExtension cov A D) f u := by
  unfold AtlasSpatialClassicalSolution StrongAtlasClassicalSolution
  rw [A.atlasInitialTrace_spatialInitialExtension cov D]

/-- Existence and uniqueness for concrete bounded spatial initial data. -/
theorem existsUnique_atlasSpatialClassicalSolution
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (hunique : HasLocalZeroTraceUniqueness cov A)
    (Hlift : StrongCommutatorLift cov A)
    (D : AtlasSpatialInitialData cov A) (f : SourceSpace cov A) :
    ∃! u : HigherCoefficientSpace cov A,
      AtlasSpatialClassicalSolution cov Hlift D f u := by
  obtain ⟨u, hu, huniq⟩ := existsUnique_strongAtlasClassicalSolution
    cov hunique Hlift (spatialInitialExtension cov A D) f
  refine ⟨u, (atlasSpatialClassicalSolution_iff_strong
    cov Hlift D f u).2 hu, ?_⟩
  intro v hv
  exact huniq v ((atlasSpatialClassicalSolution_iff_strong
    cov Hlift D f v).1 hv)

/-- **Closed-manifold tensor-heat well-posedness for concrete spatial
`C^{2,α}` data, with the standard global Schauder estimate.**

No atlas, local inverse, or contraction is assumed: all are constructed from
the closed Riemannian background. -/
theorem exists_short_spatial_tensorHeat_wellPosed
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (b : Module.Basis (Fin d) ℝ E)
    (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ (S : ℝ) (_hS : t₀ < S) (_hST : S ≤ T)
      (A : FiniteTensorHeatParametrixAtlas
        (E := E) (I := I) (M := M) cov b t₀ S α)
      (Hlift : StrongCommutatorLift cov A),
      HasLocalZeroTraceUniqueness cov A ∧
        ∀ (D : AtlasSpatialInitialData cov A) (f : SourceSpace cov A),
          (∃! u : HigherCoefficientSpace cov A,
            AtlasSpatialClassicalSolution cov Hlift D f u) ∧
          ∀ u : HigherCoefficientSpace cov A,
            AtlasSpatialClassicalSolution cov Hlift D f u →
              ‖u‖ ≤ strongAtlasSchauderConstant cov Hlift *
                (spatialInitialSize cov A D + ‖f‖) := by
  obtain ⟨S, hS, hST, A, Hlift, hunique, _hwell⟩ :=
    exists_short_tensorHeat_wellPosed cov b hT hα hα1
  refine ⟨S, hS, hST, A, Hlift, hunique, ?_⟩
  intro D f
  refine ⟨existsUnique_atlasSpatialClassicalSolution
    cov hunique Hlift D f, ?_⟩
  intro u hu
  exact norm_le_strongAtlasSchauderConstant_mul_data
    cov hunique Hlift D f u
      ((atlasSpatialClassicalSolution_iff_strong cov Hlift D f u).1 hu)

end FiniteTensorHeatParametrixAtlas

end AnalyticPDE
end RicciFlow
