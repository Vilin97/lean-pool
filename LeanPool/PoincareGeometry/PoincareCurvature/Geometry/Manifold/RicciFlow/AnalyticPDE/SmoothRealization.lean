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

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE
/-!
# Smooth Ricci-DeTurck realizations of Banach chart solutions

This module names the remaining PDE closure data needed to turn a Banach
Ricci-DeTurck chart solution into a smooth intrinsic Ricci-DeTurck solution:
smooth metric realization, boundary time derivatives, identification of the
Banach vector field with the geometric Ricci-DeTurck right-hand side, and use of
the chosen Levi-Civita background. The constructions then produce the
self-encoding candidate used by the local-existence theorem packages.
-/

@[expose] public noncomputable section

open Set
open scoped Bundle Manifold ContDiff NNReal Topology

namespace RicciFlow
namespace AnalyticPDE
namespace MetricLocusEvolution

open PoincareCurvature.Bundle.Trivialization
open PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace

variable {M : Type*} [TopologicalSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {W : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F W)]
  [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [FiberBundle F W] [VectorBundle ℝ F W]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)
/-- Derivatives of curves valued in a normed submodule are equivalent to derivatives of their
ambient inclusions. This is the basic subtype bridge used when re-encoding ambient Banach curves in
closed carriers such as the symmetric-section submodule. -/
theorem Submodule.hasDerivWithinAt_subtype_iff
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Submodule ℝ X) {g : ℝ → S} {g' : S} {s : Set ℝ} {t : ℝ} :
    HasDerivWithinAt g g' s t ↔
      HasDerivWithinAt (fun τ : ℝ => (g τ : X)) (g' : X) s t := by
  constructor
  · intro hg
    simpa using (S.subtypeL.hasFDerivAt.comp_hasDerivWithinAt t hg)
  · intro hg
    refine (hasDerivWithinAt_iff_tendsto (𝕜 := ℝ) (f := g) (f' := g') (s := s) (x := t)).2 ?_
    simpa using
      ((hasDerivWithinAt_iff_tendsto
        (𝕜 := ℝ) (f := fun τ : ℝ => (g τ : X)) (f' := (g' : X)) (s := s) (x := t)).1 hg)

/-- Derivatives of curves valued in a normed submodule are equivalent to derivatives of their
ambient inclusions. This is the unrestricted companion to
`Submodule.hasDerivWithinAt_subtype_iff`. -/
theorem Submodule.hasDerivAt_subtype_iff
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Submodule ℝ X) {g : ℝ → S} {g' : S} {t : ℝ} :
    HasDerivAt g g' t ↔ HasDerivAt (fun τ : ℝ => (g τ : X)) (g' : X) t := by
  constructor
  · intro hg
    have hw : HasDerivWithinAt (fun τ : ℝ => (g τ : X)) (g' : X) Set.univ t :=
      (Submodule.hasDerivWithinAt_subtype_iff (S := S) (s := Set.univ)).1
        hg.hasDerivWithinAt
    exact hw.hasDerivAt (by simp)
  · intro hg
    have hw : HasDerivWithinAt g g' Set.univ t :=
      (Submodule.hasDerivWithinAt_subtype_iff (S := S) (s := Set.univ)).2
        hg.hasDerivWithinAt
    exact hw.hasDerivAt (by simp)

/-- A time-dependent finite-cover section curve whose time slices are spatially `C^2` and lie in
the symmetric positive-definite locus. This isolates the spatial regularity needed to turn a Banach
metric-section curve into a genuine time-dependent smooth Riemannian metric. -/
structure SmoothMetricSectionCurveData
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    (sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)) where
  /-- A global-in-time section extension of the Banach solution curve. -/
  sectionCurve : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
    (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
    et Kc hKc Ko hKo hKoEq hcover
  /-- On the local solution interval the global section extension is the Banach solution curve. -/
  section_eq_curve : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
    sectionCurve t = sol.curve t
  /-- Every time slice is symmetric and positive-definite. -/
  mem_spd : ∀ t : ℝ, sectionCurve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F)
    (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover
  /-- Every time slice is spatially `C^2` as a bilinear-form-bundle section. -/
  contMDiff : ∀ t : ℝ,
    ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
      (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (sectionCurve t x))

namespace SmoothMetricSectionCurveData

/-- Reify a spatially `C^2`, symmetric positive-definite section curve as a time-dependent smooth
Riemannian metric family. -/
def metric
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (D : SmoothMetricSectionCurveData
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover sol) :
    MetricFamily (I := I) (M := M) :=
  fun t ↦ _root_.Bundle.ContMDiffRiemannianMetric.ofContinuousSectionSpace
    (M := M) (F := F) (W := (TangentSpace I : M → Type _)) (I₀ := I)
    (n := (2 : WithTop ℕ∞)) et Kc hKc Ko hKo hKoEq hcover
    (D.sectionCurve t) (D.mem_spd t) (D.contMDiff t)

@[simp] theorem metricTensor_metric
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (D : SmoothMetricSectionCurveData
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover sol)
    (t : ℝ) (x : M) (u v : TangentSpace I x) :
    metricTensor (I := I) (M := M) D.metric t x u v = D.sectionCurve t x u v := by
  simp [metric, metricTensor]

/-- The reified metric realizes the original Banach solution on the local solution interval. -/
theorem metric_eq_curve
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (D : SmoothMetricSectionCurveData
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover sol)
    {t : ℝ} (ht : t ∈ Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TangentSpace I x) :
    metricTensor (I := I) (M := M) D.metric t x u v = sol.curve t x u v := by
  rw [metricTensor_metric]
  simpa using
    congrArg
      (fun s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover ↦ s x u v)
      (D.section_eq_curve ht)

/-- Scalar time derivatives of the spatial section curve give the corresponding time derivative of
the reified metric family. -/
theorem hasTimeDerivativeAt_of_sectionCurve_hasDerivAt
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (D : SmoothMetricSectionCurveData
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover sol)
    {gdot : MetricTensorFamily (I := I) (M := M)} {t : ℝ}
    (hderiv : ∀ (x : M) (u v : TangentSpace I x),
      HasDerivAt (fun τ : ℝ ↦ D.sectionCurve τ x u v) (gdot t x u v) t) :
    HasTimeDerivativeAt (I := I) (M := M) D.metric gdot t := by
  intro x u v
  simpa [metricTensor_metric] using hderiv x u v

/-- A smooth metric family whose tensor coefficients agree with a Banach section curve supplies the
corresponding smooth section-curve data. This is the converse bridge to `metric`: existing smooth
geometric candidates can be encoded back into the finite-cover section model with their spatial
`C^2` regularity and positivity exposed. -/
def of_metricFamily
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (metric : MetricFamily (I := I) (M := M))
    (metric_eq_curve : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
      ∀ (x : M) (u v : TangentSpace I x),
        metricTensor (I := I) (M := M) metric t x u v = sol.curve t x u v) :
    SmoothMetricSectionCurveData
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover sol where
  sectionCurve t := ⟨(metric t).toSection, (metric t).continuous_toSection⟩
  section_eq_curve := by
    intro t ht
    ext x u v
    exact metric_eq_curve ht x u v
  mem_spd := by
    intro t
    simpa [_root_.Bundle.ContMDiffRiemannianMetric.toSection,
      _root_.Bundle.ContinuousRiemannianMetric.toSection] using
      mem_symmetricPositiveDefiniteLocus_of_continuousRiemannianMetric
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover
        ((metric t).toContinuousRiemannianMetric)
  contMDiff := by
    intro t
    simpa [_root_.Bundle.ContMDiffRiemannianMetric.toSection] using
      (_root_.Bundle.ContMDiffRiemannianMetric.contMDiff_toSection
        (IB := I) (n := (2 : WithTop ℕ∞)) (F := F)
        (V := (TangentSpace I : M → Type _)) (metric t))

/-- Any existing smooth intrinsic DeTurck realization canonically exposes the same spatial
finite-cover section-curve data. This lets later reductions work with the proof-bearing
section-curve interface without assuming a second, independent smooth realization. -/
def of_smoothIntrinsicDeTurckRealization
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [T2Space M] [FiniteDimensional ℝ F] [CompleteSpace F]
    [IsManifold I ∞ M] [SigmaCompactSpace M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    {κ : Type*} [Finite κ]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover)}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A stateSet ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol) :
    SmoothMetricSectionCurveData
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover sol :=
  SmoothMetricSectionCurveData.of_metricFamily
    (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover
    realization.metric realization.metric_eq_curve

end SmoothMetricSectionCurveData

/-- A solution-specific-free identification of a finite-cover Banach vector field with the
chosen-background intrinsic Ricci-DeTurck operator.  Unlike the existential `geometric` field on a
chart, this says that whenever a smooth metric family realizes the current Banach section at the
current time, the chart vector field is the Ricci-DeTurck RHS for that same realized metric. -/
structure SmoothSectionRHSIdentification
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) where
  eq_intrinsic : ∀ ⦃t : ℝ⦄
    {s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover},
    s ∈ positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover →
    ∀ metric : MetricFamily (I := I) (M := M),
      (∀ (x : M) (u v : TangentSpace I x),
        metricTensor (I := I) (M := M) metric t x u v = s x u v) →
      ∀ (x : M) (u v : TangentSpace I x),
        A t s x u v =
          intrinsicRicciDeTurckRHS (I := I) (M := M)
            metric (chosenLeviCivitaFamily (I := I) (M := M) metric) t x u v

namespace SmoothSectionRHSIdentification

/-- A chart-level specific RHS identification gives the RHS equality for the canonical smooth metric
reified from a smooth section-curve realization of a Banach solution. -/
theorem chartRHS_eq_intrinsic
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {sol : BanachEvolutionLocalSolutionIn A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover A)
    (spatial : SmoothMetricSectionCurveData
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover sol)
    {t : ℝ} (ht : t ∈ Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TangentSpace I x) :
    A t (sol.curve t) x u v =
      intrinsicRicciDeTurckRHS (I := I) (M := M)
        spatial.metric
        (chosenLeviCivitaFamily (I := I) (M := M) spatial.metric) t x u v :=
  rhs.eq_intrinsic (sol.mem_state ht) spatial.metric
    (fun x u v ↦ spatial.metric_eq_curve (t := t) ht x u v) x u v

/-- A chart-level specific Ricci-DeTurck RHS identification proves symmetry of the chart vector
field on every smooth symmetric positive-definite section.  This is the non-existential tangency
statement needed when the analytic vector field is constructed directly from the reified metric. -/
theorem A_mem_symmetricLocus_of_smooth_spd
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover A)
    {s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover}
    (hs : s ∈ symmetricPositiveDefiniteLocus
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover)
    (hsmooth : ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
      (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (s x)))
    (t : ℝ) :
    A t s ∈ symmetricLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover := by
  let metric : MetricFamily (I := I) (M := M) :=
    fun _ ↦ _root_.Bundle.ContMDiffRiemannianMetric.ofContinuousSectionSpace
      (M := M) (F := F) (W := (TangentSpace I : M → Type _)) (I₀ := I)
      (n := (2 : WithTop ℕ∞)) et Kc hKc Ko hKo hKoEq hcover s hs hsmooth
  intro x u v
  have hreal : ∀ (y : M) (w z : TangentSpace I y),
      metricTensor (I := I) (M := M) metric t y w z = s y w z := by
    intro y w z
    simp [metric, metricTensor]
  calc
    A t s x u v =
        intrinsicRicciDeTurckRHS (I := I) (M := M) metric
          (chosenLeviCivitaFamily (I := I) (M := M) metric) t x u v :=
      rhs.eq_intrinsic hs.2 metric hreal x u v
    _ = intrinsicRicciDeTurckRHS (I := I) (M := M) metric
          (chosenLeviCivitaFamily (I := I) (M := M) metric) t x v u :=
      intrinsicRicciDeTurckRHS_symm (I := I) (M := M) metric
        (chosenLeviCivitaFamily (I := I) (M := M) metric) t x u v
    _ = A t s x v u :=
      (rhs.eq_intrinsic hs.2 metric hreal x v u).symm

/-- Coordinatewise antisymmetric-defect form of
`A_mem_symmetricLocus_of_smooth_spd`.  This is the equation consumed by the symmetric-carrier
submodule route, with symmetry now obtained from the specific reified Ricci-DeTurck RHS. -/
theorem A_coordwiseSymmetryDefect_eq_zero_of_smooth_spd
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover A)
    {s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover}
    (hs : s ∈ symmetricPositiveDefiniteLocus
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover)
    (hsmooth : ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
      (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (s x)))
    (t : ℝ) :
    _root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap
        (F := F) (V := _root_.Bundle.BilinearFormBundle
          (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover (A t s) = 0 := by
  exact (_root_.PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace.coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      x0 et het Kc hKc Ko hKo hKoEq hcover (A t s)).2
    (rhs.A_mem_symmetricLocus_of_smooth_spd
      (M := M) (F := F) (I := I) hs hsmooth t)

/-- Submodule membership form of `A_mem_symmetricLocus_of_smooth_spd`.  This packages the
specific-RHS symmetry proof as the exact target condition for defining a symmetric-carrier vector
field. -/
theorem A_mem_symmetricSectionSubmodule_of_smooth_spd
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover A)
    {s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover}
    (hs : s ∈ symmetricPositiveDefiniteLocus
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover)
    (hsmooth : ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
      (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (s x)))
    (t : ℝ) :
    A t s ∈ symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover := by
  rw [mem_symmetricSectionSubmodule_iff
    (M := M) (F := F) (W := (TangentSpace I : M → Type _))
    x0 et het Kc hKc Ko hKo hKoEq hcover]
  exact rhs.A_mem_symmetricLocus_of_smooth_spd
    (M := M) (F := F) (I := I) hs hsmooth t

/-- Metric closure criterion for the smooth symmetric positive-definite slices in the finite-cover
section space.  This packages the remaining density theorem in the standard approximation form:
for every positive error, produce a smooth SPD section within that error. -/
theorem mem_closure_smooth_spd_of_forall_dist_lt
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover}
    (happrox : ∀ ε > 0,
      ∃ u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover,
        u ∈ symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover ∧
        ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
          (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x)) ∧
        dist s u < ε) :
    s ∈ closure
      ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover |
          u ∈ symmetricPositiveDefiniteLocus
            (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover ∧
          ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
            (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}) := by
  refine Metric.mem_closure_iff.2 ?_
  intro ε hε
  rcases happrox ε hε with ⟨u, hspd, hsmooth, hdist⟩
  exact ⟨u, ⟨hspd, hsmooth⟩, hdist⟩

/-- Smooth symmetric approximants are enough for the smooth SPD closure criterion near an SPD
section: positivity of the approximants is obtained by shrinking the approximation radius inside the
open positive-definite locus.  This isolates the density theorem still needed for point 4 to the
linear symmetric submodule rather than the nonlinear positivity constraint. -/
theorem mem_closure_smooth_spd_of_forall_dist_lt_symmetric
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover}
    (hs : s ∈ symmetricPositiveDefiniteLocus
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover)
    (happrox : ∀ ε > 0,
      ∃ u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover,
        u ∈ symmetricLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover ∧
        ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
          (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x)) ∧
        dist s u < ε) :
    s ∈ closure
      ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover |
          u ∈ symmetricPositiveDefiniteLocus
            (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover ∧
          ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
            (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}) := by
  obtain ⟨δ, hδpos, hδsubset⟩ :=
    exists_dist_lt_subset_positiveDefiniteLocus
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      x0 et het Kc hKc Ko hKo hKoEq hcover hs.2
  refine mem_closure_smooth_spd_of_forall_dist_lt
    (M := M) (F := F) (I := I)
    (et := et) (Kc := Kc) (hKc := hKc)
    (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq)
    (hcover := hcover) ?_
  intro ε hεpos
  let η : ℝ := min ε δ
  have hηpos : 0 < η := lt_min hεpos hδpos
  rcases happrox η hηpos with ⟨u, hu_symm, hu_smooth, hudist⟩
  have hudistε : dist s u < ε := lt_of_lt_of_le hudist (min_le_left ε δ)
  have hudistδ : dist u s < δ := by
    rw [dist_comm]
    exact lt_of_lt_of_le hudist (min_le_right ε δ)
  exact ⟨u, ⟨hu_symm, hδsubset u hudistδ⟩, hu_smooth, hudistε⟩

/-- Arbitrary smooth approximants are enough for the smooth SPD closure criterion near an SPD
section.  The approximants are fiberwise symmetrized; the tangent fiber is the model vector space,
so fiberwise symmetrization preserves spatial smoothness and is nonexpansive toward a symmetric
target.  Positivity is then recovered by the openness argument in
`mem_closure_smooth_spd_of_forall_dist_lt_symmetric`. -/
theorem mem_closure_smooth_spd_of_forall_dist_lt_unsymmetric
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover}
    (hs : s ∈ symmetricPositiveDefiniteLocus
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover)
    (happrox : ∀ ε > 0,
      ∃ u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover,
        ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
          (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x)) ∧
        dist s u < ε) :
    s ∈ closure
      ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover |
          u ∈ symmetricPositiveDefiniteLocus
            (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover ∧
          ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
            (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}) := by
  refine mem_closure_smooth_spd_of_forall_dist_lt_symmetric
    (M := M) (F := F) (I := I) (x0 := x0) (het := het) hs ?_
  intro ε hε
  rcases happrox ε hε with ⟨u, hu_smooth, hudist⟩
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (n := (∞ : WithTop ℕ∞)) (by simp)
  letI : TopologicalSpace
      (_root_.Bundle.TotalSpace F (TangentSpace I : M → Type _)) :=
    (instTopologicalSpaceTangentBundle (I := I) (M := M) :
      TopologicalSpace (TangentBundle I M))
  letI : FiberBundle F (TangentSpace I : M → Type _) :=
    TangentSpace.fiberBundle (I := I) (M := M)
  letI : VectorBundle ℝ F (TangentSpace I : M → Type _) :=
    TangentSpace.vectorBundle (𝕜 := ℝ) (I := I) (M := M)
  letI : TopologicalSpace (_root_.Bundle.TotalSpace BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))) :=
    inferInstance
  have hu_symm_smooth : ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
      (fun x ↦ _root_.Bundle.TotalSpace.mk'
        (E := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        BilF x (_root_.Bundle.symmetrizeBilinearSection
          (W := (TangentSpace I : M → Type _)) (fun y ↦ u y) x)) :=
    @_root_.Bundle.contMDiff_symmetrizeBilinearSection
      M inferInstance F inferInstance inferInstance
      (TangentSpace I : M → Type _)
      (instTopologicalSpaceTangentBundle (I := I) (M := M) :
        TopologicalSpace (TangentBundle I M))
      (fun x ↦ PoincareCurvature.instNormedAddCommGroupTangentSpace I x)
      (fun x ↦ PoincareCurvature.instNormedSpaceTangentSpace I x)
      (TangentSpace.fiberBundle (I := I) (M := M))
      (TangentSpace.vectorBundle (𝕜 := ℝ) (I := I) (M := M))
      F inferInstance inferInstance H inferInstance
      I (2 : WithTop ℕ∞) inferInstance
      (fun y ↦ u y) hu_smooth
  let v : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover :=
    ⟨fun x ↦ _root_.Bundle.symmetrizeBilinearSection
        (W := (TangentSpace I : M → Type _)) (fun y ↦ u y) x,
      by
        change Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk'
          (E := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          BilF x (_root_.Bundle.symmetrizeBilinearSection
            (W := (TangentSpace I : M → Type _)) (fun y ↦ u y) x))
        exact hu_symm_smooth.continuous⟩
  have hv_symm : v ∈ symmetricLocus
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover := by
    intro x p q
    exact _root_.Bundle.symmetrizeBilinearSection_forall_symmetric
      (W := (TangentSpace I : M → Type _)) (fun y ↦ u y) x p q
  have hv_smooth : ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
      (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (v x)) := by
    simpa [v] using hu_symm_smooth
  have hdist_le : dist s v ≤ dist s u :=
    dist_symmetrizeBilinearSection_le_of_symmetric
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      x0 et het Kc hKc Ko hKo hKoEq hcover s u v hs.1 (by
        intro x p q
        change (_root_.Bundle.symmetrizeBilinearSection
            (W := (TangentSpace I : M → Type _)) (fun y ↦ u y) x) p q =
          ((u x) p q + (u x) q p) / 2
        exact _root_.Bundle.symmetrizeBilinearSection_apply_apply
          (W := (TangentSpace I : M → Type _)) (fun y ↦ u y) x p q)
  exact ⟨v, hv_symm, hv_smooth, lt_of_le_of_lt hdist_le hudist⟩

/-- Convert a metric-locus smooth symmetric approximation theorem into the closure hypothesis used
by the density-based carrier.  This is the point-4 density target in its current linearized form:
approximate every positive symmetric continuous metric section by smooth symmetric sections; the
previous theorem then supplies positivity of the approximants by openness. -/
theorem closure_smooth_spd_of_metric_locus_and_forall_dist_lt_symmetric
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (happrox : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover →
      ∀ ε > 0,
        ∃ u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover,
          u ∈ symmetricLocus
            (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover ∧
          ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
            (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x)) ∧
          dist (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) u < ε) :
    ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover →
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) ∈ closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover |
              u ∈ symmetricPositiveDefiniteLocus
                (M := M) (F := F) (W := (TangentSpace I : M → Type _))
                et Kc hKc Ko hKo hKoEq hcover ∧
              ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
                (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}) := by
  intro s hs
  have hspd :
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) ∈
        symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover :=
    (mem_riemannianMetricLocusSubmodule_iff
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      x0 et het Kc hKc Ko hKo hKoEq hcover s).1 hs
  exact mem_closure_smooth_spd_of_forall_dist_lt_symmetric
    (M := M) (F := F) (I := I) (x0 := x0) (het := het) hspd (happrox s hs)

/-- Convert arbitrary smooth approximation of metric-locus states into closure by smooth symmetric
positive-definite slices.  The arbitrary approximants are first symmetrized fiberwise, so the
residual density input no longer has to build symmetric approximants by hand. -/
theorem closure_smooth_spd_of_metric_locus_and_forall_dist_lt_unsymmetric
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (happrox : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover →
      ∀ ε > 0,
        ∃ u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover,
          ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
            (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x)) ∧
          dist (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) u < ε) :
    ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover →
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) ∈ closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover |
              u ∈ symmetricPositiveDefiniteLocus
                (M := M) (F := F) (W := (TangentSpace I : M → Type _))
                et Kc hKc Ko hKo hKoEq hcover ∧
              ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
                (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}) := by
  intro s hs
  have hspd :
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) ∈
        symmetricPositiveDefiniteLocus
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover :=
    (mem_riemannianMetricLocusSubmodule_iff
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      x0 et het Kc hKc Ko hKo hKoEq hcover s).1 hs
  exact mem_closure_smooth_spd_of_forall_dist_lt_unsymmetric
    (M := M) (F := F) (I := I) (x0 := x0) (het := het) hspd (happrox s hs)

/-- A dense-smooth-slice extension of the specific-RHS tangency theorem.  If a positive
continuous section lies in the closure of the smooth symmetric positive-definite slices, and the
ambient Ricci-DeTurck vector field is continuous there (here via a Lipschitz estimate), then the
specific-RHS symmetry proof extends from smooth slices to that section.  This is the analytic
bridge needed to replace the false assumption that every Banach metric-locus state is spatially
smooth. -/
theorem A_mem_symmetricSectionSubmodule_of_closure_smooth_spd
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover A)
    {Kstate : ℝ≥0}
    {s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover}
    (hpos : s ∈ positiveDefiniteLocus
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      et Kc hKc Ko hKo hKoEq hcover)
    (hclosure : s ∈ closure
      ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover |
          u ∈ symmetricPositiveDefiniteLocus
            (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            et Kc hKc Ko hKo hKoEq hcover ∧
          ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
            (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}))
    (t : ℝ)
    (hLip : LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover)) :
    A t s ∈ symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover := by
  let smoothSPD : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
      et Kc hKc Ko hKo hKoEq hcover) :=
    {u | u ∈ symmetricPositiveDefiniteLocus
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover ∧
      ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
        (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}
  have hsmooth_subset_pos : smoothSPD ⊆
      positiveDefiniteLocus
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover := by
    intro u hu
    exact hu.1.2
  have hmaps : MapsTo (A t) smoothSPD
      (symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover :
        Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle
            (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover)) := by
    intro u hu
    exact rhs.A_mem_symmetricSectionSubmodule_of_smooth_spd
      (M := M) (F := F) (I := I) (x0 := x0) (het := het)
      hu.1 hu.2 t
  have hcont : ContinuousWithinAt (A t) smoothSPD s :=
    ((hLip.continuousOn) s hpos).mono hsmooth_subset_pos
  have hcl : A t s ∈ closure
      (symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover :
        Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle
            (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover)) :=
    hcont.mem_closure (by simpa [smoothSPD] using hclosure) hmaps
  have hclosed : IsClosed
      (symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover :
        Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle
            (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover)) := by
    change IsClosed
      (((coordwiseSymmetryDefectContinuousLinearMap (F := F)
          (V := _root_.Bundle.BilinearFormBundle
            (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover).ker) :
        Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle
            (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover))
    exact ContinuousLinearMap.isClosed_ker _
  simpa [hclosed.closure_eq] using hcl

/-- Generic restriction of an ambient finite-cover vector field to the symmetric metric carrier,
from a direct tangency proof on the Riemannian metric locus.  The specific-RHS and density-based
carriers below are instances of this proof surface. -/
noncomputable def restrictedSymmetricAOfMem
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    (hmem : ∀ t (s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover),
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      A t (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) ∈
        symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
    ℝ →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover :=
  fun t s => by
    classical
    by_cases hs : s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover
    · exact ⟨A t (s :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover), hmem t s hs⟩
    · exact 0

/-- Density-based specific-RHS carrier.  On the metric locus, tangency is obtained by extending
the smooth-slice Ricci-DeTurck symmetry proof across the closure of smooth SPD slices using
Lipschitz continuity. -/
noncomputable def restrictedSymmetricA_of_closure_smooth_spd
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover A)
    (hclosure : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) ∈ closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover |
              u ∈ symmetricPositiveDefiniteLocus
                (M := M) (F := F) (W := (TangentSpace I : M → Type _))
                et Kc hKc Ko hKo hKoEq hcover ∧
              ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
                (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}))
    (hLip : ∀ t, ∃ Kstate : ℝ≥0, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover)) :
    ℝ →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover :=
  restrictedSymmetricAOfMem
    (M := M) (F := F) (I := I)
    x0 et het Kc hKc Ko hKo hKoEq hcover
    (A := A)
    (fun t s hs => by
      obtain ⟨Kstate, hLip_t⟩ := hLip t
      exact rhs.A_mem_symmetricSectionSubmodule_of_closure_smooth_spd
        (M := M) (F := F) (I := I) (x0 := x0) (het := het)
        (((mem_riemannianMetricLocusSubmodule_iff
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          x0 et het Kc hKc Ko hKo hKoEq hcover s).1 hs).2)
        (hclosure s hs) t hLip_t)
/-- On the Riemannian metric locus, the density-based specific-RHS carrier is exactly the ambient
finite-cover vector field. -/
theorem restrictedSymmetricA_of_closure_smooth_spd_coe_of_mem
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover A)
    (hclosure : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) ∈ closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover |
              u ∈ symmetricPositiveDefiniteLocus
                (M := M) (F := F) (W := (TangentSpace I : M → Type _))
                et Kc hKc Ko hKo hKoEq hcover ∧
              ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
                (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}))
    (hLip : ∀ t, ∃ Kstate : ℝ≥0, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover)) :
    ∀ t x,
      x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
        ((restrictedSymmetricA_of_closure_smooth_spd
          (M := M) (F := F) (I := I)
          x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hLip) t x :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) =
          A t (x :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) := by
  intro t x hx
  simp [restrictedSymmetricA_of_closure_smooth_spd, restrictedSymmetricAOfMem, hx]
/-- Interval-scoped density-based specific-RHS carrier.  On the Picard interval, tangency to the
symmetric carrier is obtained by extending the smooth-slice Ricci-DeTurck symmetry proof across the
closure of smooth SPD slices using the interval Lipschitz estimate.  Outside the interval the carrier
is set to zero, so no artificial global-in-time Lipschitz witness is needed. -/
noncomputable def restrictedSymmetricA_of_closure_smooth_spd_on_Icc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover A)
    (hclosure : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) ∈ closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover |
              u ∈ symmetricPositiveDefiniteLocus
                (M := M) (F := F) (W := (TangentSpace I : M → Type _))
                et Kc hKc Ko hKo hKoEq hcover ∧
              ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
                (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}))
    {t₀ T : ℝ} {Kstate : ℝ≥0}
    (hLip : ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover)) :
    ℝ →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover :=
  fun t s => by
    classical
    by_cases ht : t ∈ Icc t₀ T
    · by_cases hs : s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover
      · exact ⟨A t (s :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover),
          rhs.A_mem_symmetricSectionSubmodule_of_closure_smooth_spd
            (M := M) (F := F) (I := I) (x0 := x0) (het := het)
            (((mem_riemannianMetricLocusSubmodule_iff
              (M := M) (F := F) (W := (TangentSpace I : M → Type _))
              x0 et het Kc hKc Ko hKo hKoEq hcover s).1 hs).2)
            (hclosure s hs) t (hLip t ht)⟩
      · exact 0
    · exact 0
/-- On the Riemannian metric locus and inside the Picard interval, the interval-scoped
density-based specific-RHS carrier is exactly the ambient finite-cover vector field. -/
theorem restrictedSymmetricA_of_closure_smooth_spd_on_Icc_coe_of_mem
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover A)
    (hclosure : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) ∈ closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover |
              u ∈ symmetricPositiveDefiniteLocus
                (M := M) (F := F) (W := (TangentSpace I : M → Type _))
                et Kc hKc Ko hKo hKoEq hcover ∧
              ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
                (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}))
    {t₀ T : ℝ} {Kstate : ℝ≥0}
    (hLip : ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover)) :
    ∀ t, t ∈ Icc t₀ T → ∀ x,
      x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
        ((restrictedSymmetricA_of_closure_smooth_spd_on_Icc
          (M := M) (F := F) (I := I)
          x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hLip) t x :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) =
          A t (x :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) := by
  intro t ht x hx
  simp [restrictedSymmetricA_of_closure_smooth_spd_on_Icc, ht, hx]
/-- Ambient interval Lipschitz control descends to the interval-scoped density-based specific-RHS
carrier without requiring any global-in-time Lipschitz witness. -/
theorem restrictedSymmetricA_of_closure_smooth_spd_on_Icc_lipschitzOn_Icc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover A)
    (hclosure : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) ∈ closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover |
              u ∈ symmetricPositiveDefiniteLocus
                (M := M) (F := F) (W := (TangentSpace I : M → Type _))
                et Kc hKc Ko hKo hKoEq hcover ∧
              ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
                (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}))
    {t₀ T : ℝ} {Kstate : ℝ≥0}
    (hLip : ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover)) :
    ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate
      ((restrictedSymmetricA_of_closure_smooth_spd_on_Icc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hLip) t)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) := by
  intro t ht x hx y hy
  have hxy := hLip t ht hx hy
  simpa [restrictedSymmetricA_of_closure_smooth_spd_on_Icc, ht, hx, hy] using hxy
/-- Ambient Picard-Lindelöf hypotheses transfer to the interval-scoped density-based specific-RHS
symmetric carrier once the Picard ball is contained in the metric cone.  This version only consumes
the interval Lipschitz estimate needed on the Picard interval. -/
theorem restrictedSymmetricA_of_closure_smooth_spd_on_Icc_picard_of_closedBall_subset_riemannianMetricLocus
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover A)
    (hclosure : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) ∈ closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover |
              u ∈ symmetricPositiveDefiniteLocus
                (M := M) (F := F) (W := (TangentSpace I : M → Type _))
                et Kc hKc Ko hKo hKoEq hcover ∧
              ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
                (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}))
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (hT : ivp.initialTime < T)
    (picard : IsPicardLindelof A (tmin := ivp.initialTime) (tmax := T)
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT⟩⟩
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)
      a 0 L Kpic)
    (hLip : ∀ t ∈ Icc ivp.initialTime T, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover))
    (hball : Metric.closedBall
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a ⊆
      riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) :
    IsPicardLindelof
      (restrictedSymmetricA_of_closure_smooth_spd_on_Icc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hLip)
      (tmin := ivp.initialTime) (tmax := T)
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT⟩⟩
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a 0 L Kpic where
  lipschitzOnWith t ht := by
    intro x hx y hy
    have hxLocus : x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover :=
      hball hx
    have hyLocus : y ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover :=
      hball hy
    have hxAmb :
        (x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) ∈
        Metric.closedBall
          ((InitialValueProblem.toSymmetricSectionSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) a := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hyAmb :
        (y : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) ∈
        Metric.closedBall
          ((InitialValueProblem.toSymmetricSectionSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) a := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    have hxy := picard.lipschitzOnWith t ht
      (x := (x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)) hxAmb
      (y := (y : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)) hyAmb
    simpa [Subtype.edist_eq, restrictedSymmetricA_of_closure_smooth_spd_on_Icc,
      ht, hxLocus, hyLocus] using hxy
  continuousOn x hx := by
    have hxLocus : x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover :=
      hball hx
    have hxAmb :
        (x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) ∈
        Metric.closedBall
          ((InitialValueProblem.toSymmetricSectionSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) a := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hcontAmb := picard.continuousOn
      ((x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)) hxAmb
    have hcontCoe : ContinuousOn
        (fun t => ((restrictedSymmetricA_of_closure_smooth_spd_on_Icc
          (M := M) (F := F) (I := I)
          x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hLip) t x :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover))
        (Icc ivp.initialTime T) := by
      refine hcontAmb.congr ?_
      intro t ht
      exact restrictedSymmetricA_of_closure_smooth_spd_on_Icc_coe_of_mem
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hLip t ht x hxLocus
    rw [continuousOn_iff_continuous_restrict] at hcontCoe ⊢
    simpa using Continuous.subtype_mk hcontCoe
      (fun t => ((restrictedSymmetricA_of_closure_smooth_spd_on_Icc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hLip) t.1 x).2)
  norm_le t ht x hx := by
    have hxLocus : x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover :=
      hball hx
    have hxAmb :
        (x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) ∈
        Metric.closedBall
          ((InitialValueProblem.toSymmetricSectionSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) a := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hnorm := picard.norm_le t ht
      ((x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)) hxAmb
    simpa [restrictedSymmetricA_of_closure_smooth_spd_on_Icc, ht, hxLocus] using hnorm
  mul_max_le := picard.mul_max_le
/-- Ambient interval Lipschitz control descends to the density-based specific-RHS carrier. -/
theorem restrictedSymmetricA_of_closure_smooth_spd_lipschitzOn_Icc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover A)
    (hclosure : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) ∈ closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover |
              u ∈ symmetricPositiveDefiniteLocus
                (M := M) (F := F) (W := (TangentSpace I : M → Type _))
                et Kc hKc Ko hKo hKoEq hcover ∧
              ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
                (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}))
    (hGlobalLip : ∀ t, ∃ Kglobal : ℝ≥0, LipschitzOnWith Kglobal (A t)
      (positiveDefiniteLocus
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover))
    {t₀ T : ℝ} {Kstate : ℝ≥0}
    (hLip : ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover)) :
    ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate
      ((restrictedSymmetricA_of_closure_smooth_spd
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hGlobalLip) t)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) := by
  intro t ht x hx y hy
  have hxy := hLip t ht hx hy
  simpa [restrictedSymmetricA_of_closure_smooth_spd, restrictedSymmetricAOfMem, hx, hy] using hxy
/-- Ambient Picard-Lindelöf hypotheses transfer to the density-based specific-RHS symmetric carrier
once the Picard ball is contained in the metric cone.  Tangency is supplied by density of smooth SPD
slices plus Lipschitz extension, not by assuming all Banach states are spatially smooth. -/
theorem restrictedSymmetricA_of_closure_smooth_spd_picard_of_closedBall_subset_riemannianMetricLocus
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover A)
    (hclosure : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) ∈ closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover |
              u ∈ symmetricPositiveDefiniteLocus
                (M := M) (F := F) (W := (TangentSpace I : M → Type _))
                et Kc hKc Ko hKo hKoEq hcover ∧
              ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
                (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}))
    (hGlobalLip : ∀ t, ∃ Kglobal : ℝ≥0, LipschitzOnWith Kglobal (A t)
      (positiveDefiniteLocus
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover))
    {T : ℝ} {a L Kpic : ℝ≥0}
    (hT : ivp.initialTime < T)
    (picard : IsPicardLindelof A (tmin := ivp.initialTime) (tmax := T)
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT⟩⟩
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)
      a 0 L Kpic)
    (hball : Metric.closedBall
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a ⊆
      riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) :
    IsPicardLindelof
      (restrictedSymmetricA_of_closure_smooth_spd
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hGlobalLip)
      (tmin := ivp.initialTime) (tmax := T)
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT⟩⟩
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a 0 L Kpic where
  lipschitzOnWith t ht := by
    intro x hx y hy
    have hxLocus : x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover :=
      hball hx
    have hyLocus : y ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover :=
      hball hy
    have hxAmb :
        (x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) ∈
        Metric.closedBall
          ((InitialValueProblem.toSymmetricSectionSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) a := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hyAmb :
        (y : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) ∈
        Metric.closedBall
          ((InitialValueProblem.toSymmetricSectionSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) a := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    have hxy := picard.lipschitzOnWith t ht
      (x := (x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)) hxAmb
      (y := (y : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)) hyAmb
    simpa [Subtype.edist_eq, restrictedSymmetricA_of_closure_smooth_spd,
      restrictedSymmetricAOfMem, hxLocus, hyLocus] using hxy
  continuousOn x hx := by
    have hxLocus : x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover :=
      hball hx
    have hxAmb :
        (x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) ∈
        Metric.closedBall
          ((InitialValueProblem.toSymmetricSectionSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) a := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hcontAmb := picard.continuousOn
      ((x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)) hxAmb
    have hcontCoe : ContinuousOn
        (fun t => ((restrictedSymmetricA_of_closure_smooth_spd
          (M := M) (F := F) (I := I)
          x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hGlobalLip) t x :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover))
        (Icc ivp.initialTime T) := by
      refine hcontAmb.congr ?_
      intro t ht
      exact restrictedSymmetricA_of_closure_smooth_spd_coe_of_mem
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hGlobalLip t x hxLocus
    rw [continuousOn_iff_continuous_restrict] at hcontCoe ⊢
    simpa using Continuous.subtype_mk hcontCoe
      (fun t => ((restrictedSymmetricA_of_closure_smooth_spd
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hGlobalLip) t.1 x).2)
  norm_le t ht x hx := by
    have hxLocus : x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover :=
      hball hx
    have hxAmb :
        (x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) ∈
        Metric.closedBall
          ((InitialValueProblem.toSymmetricSectionSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) a := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hnorm := picard.norm_le t ht
      ((x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)) hxAmb
    simpa [restrictedSymmetricA_of_closure_smooth_spd, restrictedSymmetricAOfMem, hxLocus]
      using hnorm
  mul_max_le := picard.mul_max_le

/-- Ambient Picard-Lindelöf hypotheses transfer to the density-based specific-RHS symmetric carrier
directly from arbitrary smooth approximation of metric-locus states.  The closure by smooth SPD
slices is produced internally by fiberwise symmetrizing approximants. -/
theorem restrictedSymmetricA_of_forall_dist_lt_unsymmetric_picard_of_closedBall_subset_riemannianMetricLocus
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover A)
    (happrox : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      ∀ ε > 0,
        ∃ u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover,
          ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
            (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x)) ∧
          dist (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) u < ε)
    (hGlobalLip : ∀ t, ∃ Kglobal : ℝ≥0, LipschitzOnWith Kglobal (A t)
      (positiveDefiniteLocus
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover))
    {T : ℝ} {a L Kpic : ℝ≥0}
    (hT : ivp.initialTime < T)
    (picard : IsPicardLindelof A (tmin := ivp.initialTime) (tmax := T)
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT⟩⟩
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)
      a 0 L Kpic)
    (hball : Metric.closedBall
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a ⊆
      riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) :
    IsPicardLindelof
      (restrictedSymmetricA_of_closure_smooth_spd
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs
        (closure_smooth_spd_of_metric_locus_and_forall_dist_lt_unsymmetric
          x0 et het Kc hKc Ko hKo hKoEq hcover happrox)
        hGlobalLip)
      (tmin := ivp.initialTime) (tmax := T)
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT⟩⟩
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a 0 L Kpic :=
  restrictedSymmetricA_of_closure_smooth_spd_picard_of_closedBall_subset_riemannianMetricLocus
    (M := M) (F := F) (I := I)
    x0 et het Kc hKc Ko hKo hKoEq hcover rhs
    (closure_smooth_spd_of_metric_locus_and_forall_dist_lt_unsymmetric
      x0 et het Kc hKc Ko hKo hKoEq hcover happrox)
    hGlobalLip hT picard hball

/-- Restrict a specific-RHS vector field to the genuine symmetric metric carrier.  On the
Riemannian metric locus this is the ambient vector field, with target membership proved from the
specific reified Ricci-DeTurck RHS rather than the chart's existential geometric field; outside the
metric locus it is extended by zero so the map is total on the closed symmetric submodule. -/
noncomputable def restrictedSymmetricA
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover A)
    (hspatial : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
        (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x
          ((s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) x))) :
    ℝ →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover :=
  fun t s => by
    classical
    by_cases hs : s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover
    · exact ⟨A t (s :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover), by
        exact rhs.A_mem_symmetricSectionSubmodule_of_smooth_spd
          (M := M) (F := F) (I := I) (x0 := x0) (het := het)
          ((mem_riemannianMetricLocusSubmodule_iff
            (M := M) (F := F) (W := (TangentSpace I : M → Type _))
            x0 et het Kc hKc Ko hKo hKoEq hcover s).1 hs)
          (hspatial s hs) t⟩
    · exact 0

/-- On the Riemannian metric locus, the specific-RHS restricted carrier is exactly the ambient
finite-cover vector field. -/
theorem restrictedSymmetricA_coe_of_mem
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover A)
    (hspatial : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
        (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x
          ((s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) x))) :
    ∀ t x,
      x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
        ((restrictedSymmetricA
          (M := M) (F := F) (I := I)
          x0 et het Kc hKc Ko hKo hKoEq hcover rhs hspatial) t x :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) =
          A t (x :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) := by
  intro t x hx
  simp [restrictedSymmetricA, hx]

/-- Ambient Lipschitz control on the positive cone descends to the specific-RHS restricted
symmetric carrier. -/
theorem restrictedSymmetricA_lipschitzOn_Icc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover A)
    (hspatial : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
        (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x
          ((s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) x)))
    {t₀ T : ℝ} {Kstate : ℝ≥0}
    (hLip : ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover)) :
    ∀ t ∈ Icc t₀ T, LipschitzOnWith Kstate
      ((restrictedSymmetricA
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hspatial) t)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) := by
  intro t ht x hx y hy
  have hxy := hLip t ht hx hy
  simpa [restrictedSymmetricA, hx, hy] using hxy
/-- If the Picard closed ball in the symmetric submodule stays inside the Riemannian metric locus,
then ambient Picard-Lindelöf hypotheses for a specific-RHS vector field transfer to the directly
restricted symmetric carrier.  This removes the old dependence on the chart-level existential
geometric RHS field; the only tangency input is the concrete RHS identification on smooth metric
slices. -/
theorem restrictedSymmetricA_picard_of_closedBall_subset_riemannianMetricLocus
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover A)
    (hspatial : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
        (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x
          ((s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) x)))
    {T : ℝ} {a L Kpic : ℝ≥0}
    (hT : ivp.initialTime < T)
    (picard : IsPicardLindelof A (tmin := ivp.initialTime) (tmax := T)
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT⟩⟩
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)
      a 0 L Kpic)
    (hball : Metric.closedBall
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a ⊆
      riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) :
    IsPicardLindelof
      (restrictedSymmetricA
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hspatial)
      (tmin := ivp.initialTime) (tmax := T)
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT⟩⟩
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a 0 L Kpic where
  lipschitzOnWith t ht := by
    intro x hx y hy
    have hxLocus : x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover :=
      hball hx
    have hyLocus : y ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover :=
      hball hy
    have hxAmb :
        (x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) ∈
        Metric.closedBall
          ((InitialValueProblem.toSymmetricSectionSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) a := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hyAmb :
        (y : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) ∈
        Metric.closedBall
          ((InitialValueProblem.toSymmetricSectionSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) a := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    have hxy := picard.lipschitzOnWith t ht
      (x := (x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)) hxAmb
      (y := (y : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)) hyAmb
    simpa [Subtype.edist_eq, restrictedSymmetricA, hxLocus, hyLocus] using hxy
  continuousOn x hx := by
    have hxLocus : x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover :=
      hball hx
    have hxAmb :
        (x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) ∈
        Metric.closedBall
          ((InitialValueProblem.toSymmetricSectionSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) a := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hcontAmb := picard.continuousOn
      ((x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)) hxAmb
    have hcontCoe : ContinuousOn
        (fun t => ((restrictedSymmetricA
          (M := M) (F := F) (I := I)
          x0 et het Kc hKc Ko hKo hKoEq hcover rhs hspatial) t x :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover))
        (Icc ivp.initialTime T) := by
      refine hcontAmb.congr ?_
      intro t ht
      exact restrictedSymmetricA_coe_of_mem
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hspatial t x hxLocus
    rw [continuousOn_iff_continuous_restrict] at hcontCoe ⊢
    simpa using Continuous.subtype_mk hcontCoe
      (fun t => ((restrictedSymmetricA
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hspatial) t.1 x).2)
  norm_le t ht x hx := by
    have hxLocus : x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover :=
      hball hx
    have hxAmb :
        (x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) ∈
        Metric.closedBall
          ((InitialValueProblem.toSymmetricSectionSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) a := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hnorm := picard.norm_le t ht
      ((x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)) hxAmb
    simpa [restrictedSymmetricA, hxLocus] using hnorm
  mul_max_le := picard.mul_max_le

end SmoothSectionRHSIdentification

/-- PDE closure data realizing one global Ricci-DeTurck Banach-chart solution
as a smooth chosen-background intrinsic DeTurck solution. -/
structure RicciDeTurckSmoothRealizationData
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)) where
  /-- Smooth metric family realizing the Banach curve. -/
  metric : MetricFamily (I := I) (M := M)
  /-- Background connection used for the DeTurck equation. -/
  background : ConnectionFamily (I := I) (M := M)
  /-- The smooth metric realizes the Banach section curve on the solution interval. -/
  metric_eq_curve : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
    ∀ (x : M) (u v : TangentSpace I x),
      metricTensor (I := I) (M := M) metric t x u v = sol.curve t x u v
  /-- Boundary time-derivative obligations not supplied by the interior Banach ODE. -/
  boundary_hasTimeDerivative : ∀ ⦃t : ℝ⦄,
    t ∈ Icc ivp.initialTime sol.terminalTime →
    t ∉ Ioo ivp.initialTime sol.terminalTime →
    HasTimeDerivativeAt (I := I) (M := M) metric
      (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) t
  /-- Identification of the Banach vector field with the geometric Ricci-DeTurck RHS. -/
  chartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
    ∀ (x : M) (u v : TangentSpace I x),
      chart.A t (sol.curve t) x u v =
        intrinsicRicciDeTurckRHS (I := I) (M := M) metric background t x u v
  /-- The realization uses the chosen Levi-Civita background. -/
  hbackground : background = chosenLeviCivitaFamily (I := I) (M := M) metric

/-- Build global smooth-realization closure data when the background is the chosen Levi-Civita
connection and the only supplied boundary time-derivative data are the two endpoint derivatives. -/
def RicciDeTurckSmoothRealizationData.of_chosenBackground_endpointTimeDerivative_chartRHS
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (metric : MetricFamily (I := I) (M := M))
    (metric_eq_curve : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
      ∀ (x : M) (u v : TangentSpace I x),
        metricTensor (I := I) (M := M) metric t x u v = sol.curve t x u v)
    (initial_hasTimeDerivative :
      HasTimeDerivativeAt (I := I) (M := M) metric
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) ivp.initialTime)
    (terminal_hasTimeDerivative :
      HasTimeDerivativeAt (I := I) (M := M) metric
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) sol.terminalTime)
    (chartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
      ∀ (x : M) (u v : TangentSpace I x),
        chart.A t (sol.curve t) x u v =
          intrinsicRicciDeTurckRHS (I := I) (M := M)
            metric (chosenLeviCivitaFamily (I := I) (M := M) metric) t x u v) :
    RicciDeTurckSmoothRealizationData x0 et het Kc hKc Ko hKo hKoEq hcover chart sol where
  metric := metric
  background := chosenLeviCivitaFamily (I := I) (M := M) metric
  metric_eq_curve := metric_eq_curve
  boundary_hasTimeDerivative := by
    intro t ht hboundary
    rcases eq_left_or_eq_right_of_mem_Icc_not_mem_Ioo ht hboundary with rfl | rfl
    · exact initial_hasTimeDerivative
    · exact terminal_hasTimeDerivative
  chartRHS_eq_intrinsic := chartRHS_eq_intrinsic
  hbackground := rfl

/-- Build global smooth-realization closure data from a spatially `C^2` symmetric
positive-definite section-curve realization of the Banach solution. This is the global-chart
counterpart of the interval constructor below. -/
def RicciDeTurckSmoothRealizationData.of_smoothMetricSectionCurve_endpointTimeDerivative_chartRHS
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (spatial : SmoothMetricSectionCurveData
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover sol)
    (initial_hasTimeDerivative :
      HasTimeDerivativeAt (I := I) (M := M) spatial.metric
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) ivp.initialTime)
    (terminal_hasTimeDerivative :
      HasTimeDerivativeAt (I := I) (M := M) spatial.metric
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) sol.terminalTime)
    (chartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
      ∀ (x : M) (u v : TangentSpace I x),
        chart.A t (sol.curve t) x u v =
          intrinsicRicciDeTurckRHS (I := I) (M := M)
            spatial.metric
            (chosenLeviCivitaFamily (I := I) (M := M) spatial.metric) t x u v) :
    RicciDeTurckSmoothRealizationData x0 et het Kc hKc Ko hKo hKoEq hcover chart sol :=
  RicciDeTurckSmoothRealizationData.of_chosenBackground_endpointTimeDerivative_chartRHS
    (M := M) (F := F) (I := I) spatial.metric
    (fun {t} ht x u v ↦ spatial.metric_eq_curve (t := t) ht x u v)
    initial_hasTimeDerivative terminal_hasTimeDerivative chartRHS_eq_intrinsic

/-- Build global smooth-realization closure data when the endpoint time derivatives are supplied
directly as scalar derivatives of the spatial section-curve realization. This is the global-chart
analogue of the interval constructor and removes bundled endpoint derivative data from the closure
primitive. -/
def RicciDeTurckSmoothRealizationData.of_smoothMetricSectionCurve_endpointSectionDerivatives_chartRHS
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (spatial : SmoothMetricSectionCurveData
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover sol)
    (initial_hasDerivAt : ∀ (x : M) (u v : TangentSpace I x),
      HasDerivAt (fun τ : ℝ ↦ spatial.sectionCurve τ x u v)
        (chart.A ivp.initialTime (sol.curve ivp.initialTime) x u v) ivp.initialTime)
    (terminal_hasDerivAt : ∀ (x : M) (u v : TangentSpace I x),
      HasDerivAt (fun τ : ℝ ↦ spatial.sectionCurve τ x u v)
        (chart.A sol.terminalTime (sol.curve sol.terminalTime) x u v) sol.terminalTime)
    (chartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
      ∀ (x : M) (u v : TangentSpace I x),
        chart.A t (sol.curve t) x u v =
          intrinsicRicciDeTurckRHS (I := I) (M := M)
            spatial.metric
            (chosenLeviCivitaFamily (I := I) (M := M) spatial.metric) t x u v) :
    RicciDeTurckSmoothRealizationData x0 et het Kc hKc Ko hKo hKoEq hcover chart sol :=
  RicciDeTurckSmoothRealizationData.of_smoothMetricSectionCurve_endpointTimeDerivative_chartRHS
    (M := M) (F := F) (I := I) spatial
    (SmoothMetricSectionCurveData.hasTimeDerivativeAt_of_sectionCurve_hasDerivAt
      (M := M) (F := F) (I := I) spatial
      (gdot := fun τ x u v ↦ chart.A τ (sol.curve τ) x u v)
      (t := ivp.initialTime) initial_hasDerivAt)
    (SmoothMetricSectionCurveData.hasTimeDerivativeAt_of_sectionCurve_hasDerivAt
      (M := M) (F := F) (I := I) spatial
      (gdot := fun τ x u v ↦ chart.A τ (sol.curve τ) x u v)
      (t := sol.terminalTime) terminal_hasDerivAt)
    chartRHS_eq_intrinsic

/-- Build global smooth-realization closure data from scalar endpoint derivatives and a chart-level
specific Ricci-DeTurck RHS identification. This removes the per-solution RHS-equality argument once
the Banach vector field has been proved local with respect to the reified smooth metric. -/
def RicciDeTurckSmoothRealizationData.of_smoothMetricSectionCurve_endpointSectionDerivatives_specificRHS
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover chart.A)
    (spatial : SmoothMetricSectionCurveData
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover sol)
    (initial_hasDerivAt : ∀ (x : M) (u v : TangentSpace I x),
      HasDerivAt (fun τ : ℝ ↦ spatial.sectionCurve τ x u v)
        (chart.A ivp.initialTime (sol.curve ivp.initialTime) x u v) ivp.initialTime)
    (terminal_hasDerivAt : ∀ (x : M) (u v : TangentSpace I x),
      HasDerivAt (fun τ : ℝ ↦ spatial.sectionCurve τ x u v)
        (chart.A sol.terminalTime (sol.curve sol.terminalTime) x u v) sol.terminalTime) :
    RicciDeTurckSmoothRealizationData x0 et het Kc hKc Ko hKo hKoEq hcover chart sol :=
  RicciDeTurckSmoothRealizationData.of_smoothMetricSectionCurve_endpointSectionDerivatives_chartRHS
    (M := M) (F := F) (I := I) (x0 := x0) (et := et) (het := het)
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover) (chart := chart)
    spatial initial_hasDerivAt terminal_hasDerivAt
    (fun {t} ht x u v ↦
      SmoothSectionRHSIdentification.chartRHS_eq_intrinsic
        (M := M) (F := F) (I := I) (rhs := rhs) spatial ht x u v)

/-- Convert global smooth-realization closure data into the core smooth intrinsic
DeTurck realization object. -/
def RicciDeTurckSmoothRealizationData.toSmoothIntrinsicDeTurckRealization
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (D : RicciDeTurckSmoothRealizationData x0 et het Kc hKc Ko hKo hKoEq hcover chart sol) :
    BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol :=
  BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.of_boundaryTimeDerivative_chartRHS
    (M := M) (F := F) (I := I)
    et Kc hKc Ko hKo hKoEq hcover x0 het
    D.metric D.background D.metric_eq_curve
    D.boundary_hasTimeDerivative D.chartRHS_eq_intrinsic

/-- Global closure data exposes the realized smooth metric as finite-cover section-curve data. This
is the proof-bearing reverse direction to the section-curve constructors above. -/
def RicciDeTurckSmoothRealizationData.toSmoothMetricSectionCurveData
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (D : RicciDeTurckSmoothRealizationData x0 et het Kc hKc Ko hKo hKoEq hcover chart sol) :
    SmoothMetricSectionCurveData
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover sol :=
  SmoothMetricSectionCurveData.of_smoothIntrinsicDeTurckRealization
    (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover
    D.toSmoothIntrinsicDeTurckRealization

/-- The smooth realization produced from global closure data uses the chosen background. -/
theorem RicciDeTurckSmoothRealizationData.usesChosenBackground
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (D : RicciDeTurckSmoothRealizationData x0 et het Kc hKc Ko hKo hKoEq hcover chart sol) :
    UsesChosenBackground (I := I) (M := M)
      (D.toSmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution) := by
  dsimp [UsesChosenBackground,
    BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution,
    RicciDeTurckSmoothRealizationData.toSmoothIntrinsicDeTurckRealization]
  exact D.hbackground

/-- The chosen-background DeTurck solution produced by global closure data. -/
def RicciDeTurckSmoothRealizationData.toChosenIntrinsicDeTurckLocalSolution
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (D : RicciDeTurckSmoothRealizationData x0 et het Kc hKc Ko hKo hKoEq hcover chart sol) :
    ChosenIntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp :=
  ⟨D.toSmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution,
    D.usesChosenBackground⟩

/-- Global closure data self-encodes its produced chosen-background candidate in
the same Ricci-DeTurck Banach chart. -/
def RicciDeTurckSmoothRealizationData.toCandidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (D : RicciDeTurckSmoothRealizationData x0 et het Kc hKc Ko hKo hKoEq hcover chart sol) :
    TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
      (M := M) (F := F) (I := I) chart
      (D.toChosenIntrinsicDeTurckLocalSolution.1) :=
  TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding.of_chosenSmoothRealization
    (M := M) (F := F) (I := I)
    D.toSmoothIntrinsicDeTurckRealization D.usesChosenBackground

/-- PDE closure data realizing one interval-scoped Ricci-DeTurck Banach-chart
solution as a smooth chosen-background intrinsic DeTurck solution. -/
structure RicciDeTurckSmoothRealizationDataOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)) where
  /-- The encoded solution interval stays within the interval chart's Picard interval. -/
  terminal_le_chart : sol.terminalTime ≤ T
  /-- Smooth metric family realizing the Banach curve. -/
  metric : MetricFamily (I := I) (M := M)
  /-- Background connection used for the DeTurck equation. -/
  background : ConnectionFamily (I := I) (M := M)
  /-- The smooth metric realizes the Banach section curve on the solution interval. -/
  metric_eq_curve : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
    ∀ (x : M) (u v : TangentSpace I x),
      metricTensor (I := I) (M := M) metric t x u v = sol.curve t x u v
  /-- Boundary time-derivative obligations not supplied by the interior Banach ODE. -/
  boundary_hasTimeDerivative : ∀ ⦃t : ℝ⦄,
    t ∈ Icc ivp.initialTime sol.terminalTime →
    t ∉ Ioo ivp.initialTime sol.terminalTime →
    HasTimeDerivativeAt (I := I) (M := M) metric
      (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) t
  /-- Identification of the Banach vector field with the geometric Ricci-DeTurck RHS. -/
  chartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
    ∀ (x : M) (u v : TangentSpace I x),
      chart.A t (sol.curve t) x u v =
        intrinsicRicciDeTurckRHS (I := I) (M := M) metric background t x u v
  /-- The realization uses the chosen Levi-Civita background. -/
  hbackground : background = chosenLeviCivitaFamily (I := I) (M := M) metric

/-- Build interval smooth-realization closure data when the background is the chosen Levi-Civita
connection and the only supplied boundary time-derivative data are the two endpoint derivatives. -/
def RicciDeTurckSmoothRealizationDataOnIcc.of_chosenBackground_endpointTimeDerivative_chartRHS
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (terminal_le_chart : sol.terminalTime ≤ T)
    (metric : MetricFamily (I := I) (M := M))
    (metric_eq_curve : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
      ∀ (x : M) (u v : TangentSpace I x),
        metricTensor (I := I) (M := M) metric t x u v = sol.curve t x u v)
    (initial_hasTimeDerivative :
      HasTimeDerivativeAt (I := I) (M := M) metric
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) ivp.initialTime)
    (terminal_hasTimeDerivative :
      HasTimeDerivativeAt (I := I) (M := M) metric
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) sol.terminalTime)
    (chartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
      ∀ (x : M) (u v : TangentSpace I x),
        chart.A t (sol.curve t) x u v =
          intrinsicRicciDeTurckRHS (I := I) (M := M)
            metric (chosenLeviCivitaFamily (I := I) (M := M) metric) t x u v) :
    RicciDeTurckSmoothRealizationDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart sol where
  terminal_le_chart := terminal_le_chart
  metric := metric
  background := chosenLeviCivitaFamily (I := I) (M := M) metric
  metric_eq_curve := metric_eq_curve
  boundary_hasTimeDerivative := by
    intro t ht hboundary
    rcases eq_left_or_eq_right_of_mem_Icc_not_mem_Ioo ht hboundary with rfl | rfl
    · exact initial_hasTimeDerivative
    · exact terminal_hasTimeDerivative
  chartRHS_eq_intrinsic := chartRHS_eq_intrinsic
  hbackground := rfl

/-- Build interval smooth-realization closure data from a spatially `C^2` symmetric
positive-definite section-curve realization of the Banach solution. This removes the smooth metric
family from the primitive data: the metric is reified from section-space regularity and positivity. -/
def RicciDeTurckSmoothRealizationDataOnIcc.of_smoothMetricSectionCurve_endpointTimeDerivative_chartRHS
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (terminal_le_chart : sol.terminalTime ≤ T)
    (spatial : SmoothMetricSectionCurveData
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover sol)
    (initial_hasTimeDerivative :
      HasTimeDerivativeAt (I := I) (M := M) spatial.metric
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) ivp.initialTime)
    (terminal_hasTimeDerivative :
      HasTimeDerivativeAt (I := I) (M := M) spatial.metric
        (fun τ x u v ↦ chart.A τ (sol.curve τ) x u v) sol.terminalTime)
    (chartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
      ∀ (x : M) (u v : TangentSpace I x),
        chart.A t (sol.curve t) x u v =
          intrinsicRicciDeTurckRHS (I := I) (M := M)
            spatial.metric
            (chosenLeviCivitaFamily (I := I) (M := M) spatial.metric) t x u v) :
    RicciDeTurckSmoothRealizationDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart sol :=
  RicciDeTurckSmoothRealizationDataOnIcc.of_chosenBackground_endpointTimeDerivative_chartRHS
    (M := M) (F := F) (I := I) terminal_le_chart spatial.metric
    (fun {t} ht x u v ↦ spatial.metric_eq_curve (t := t) ht x u v)
    initial_hasTimeDerivative terminal_hasTimeDerivative chartRHS_eq_intrinsic

/-- Build interval smooth-realization closure data when the endpoint time derivatives are supplied
directly as scalar derivatives of the spatial section-curve realization. -/
def RicciDeTurckSmoothRealizationDataOnIcc.of_smoothMetricSectionCurve_endpointSectionDerivatives_chartRHS
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (terminal_le_chart : sol.terminalTime ≤ T)
    (spatial : SmoothMetricSectionCurveData
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover sol)
    (initial_hasDerivAt : ∀ (x : M) (u v : TangentSpace I x),
      HasDerivAt (fun τ : ℝ ↦ spatial.sectionCurve τ x u v)
        (chart.A ivp.initialTime (sol.curve ivp.initialTime) x u v) ivp.initialTime)
    (terminal_hasDerivAt : ∀ (x : M) (u v : TangentSpace I x),
      HasDerivAt (fun τ : ℝ ↦ spatial.sectionCurve τ x u v)
        (chart.A sol.terminalTime (sol.curve sol.terminalTime) x u v) sol.terminalTime)
    (chartRHS_eq_intrinsic : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
      ∀ (x : M) (u v : TangentSpace I x),
        chart.A t (sol.curve t) x u v =
          intrinsicRicciDeTurckRHS (I := I) (M := M)
            spatial.metric
            (chosenLeviCivitaFamily (I := I) (M := M) spatial.metric) t x u v) :
    RicciDeTurckSmoothRealizationDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart sol :=
  RicciDeTurckSmoothRealizationDataOnIcc.of_smoothMetricSectionCurve_endpointTimeDerivative_chartRHS
    (M := M) (F := F) (I := I) terminal_le_chart spatial
    (SmoothMetricSectionCurveData.hasTimeDerivativeAt_of_sectionCurve_hasDerivAt
      (M := M) (F := F) (I := I) spatial
      (gdot := fun τ x u v ↦ chart.A τ (sol.curve τ) x u v)
      (t := ivp.initialTime) initial_hasDerivAt)
    (SmoothMetricSectionCurveData.hasTimeDerivativeAt_of_sectionCurve_hasDerivAt
      (M := M) (F := F) (I := I) spatial
      (gdot := fun τ x u v ↦ chart.A τ (sol.curve τ) x u v)
      (t := sol.terminalTime) terminal_hasDerivAt)
    chartRHS_eq_intrinsic

/-- Build interval smooth-realization closure data from scalar endpoint derivatives and a chart-level
specific Ricci-DeTurck RHS identification. -/
def RicciDeTurckSmoothRealizationDataOnIcc.of_smoothMetricSectionCurve_endpointSectionDerivatives_specificRHS
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover chart.A)
    (terminal_le_chart : sol.terminalTime ≤ T)
    (spatial : SmoothMetricSectionCurveData
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover sol)
    (initial_hasDerivAt : ∀ (x : M) (u v : TangentSpace I x),
      HasDerivAt (fun τ : ℝ ↦ spatial.sectionCurve τ x u v)
        (chart.A ivp.initialTime (sol.curve ivp.initialTime) x u v) ivp.initialTime)
    (terminal_hasDerivAt : ∀ (x : M) (u v : TangentSpace I x),
      HasDerivAt (fun τ : ℝ ↦ spatial.sectionCurve τ x u v)
        (chart.A sol.terminalTime (sol.curve sol.terminalTime) x u v) sol.terminalTime) :
    RicciDeTurckSmoothRealizationDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart sol :=
  RicciDeTurckSmoothRealizationDataOnIcc.of_smoothMetricSectionCurve_endpointSectionDerivatives_chartRHS
    (M := M) (F := F) (I := I) (x0 := x0) (et := et) (het := het)
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover) (chart := chart)
    terminal_le_chart spatial initial_hasDerivAt terminal_hasDerivAt
    (fun {t} ht x u v ↦
      SmoothSectionRHSIdentification.chartRHS_eq_intrinsic
        (M := M) (F := F) (I := I) (rhs := rhs) spatial ht x u v)

/-- Convert interval smooth-realization closure data into the core smooth
intrinsic DeTurck realization object. -/
def RicciDeTurckSmoothRealizationDataOnIcc.toSmoothIntrinsicDeTurckRealization
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (D : RicciDeTurckSmoothRealizationDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart sol) :
    BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp sol :=
  BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.of_boundaryTimeDerivative_chartRHS
    (M := M) (F := F) (I := I)
    et Kc hKc Ko hKo hKoEq hcover x0 het
    D.metric D.background D.metric_eq_curve
    D.boundary_hasTimeDerivative D.chartRHS_eq_intrinsic

/-- Interval closure data exposes the realized smooth metric as finite-cover section-curve data. -/
def RicciDeTurckSmoothRealizationDataOnIcc.toSmoothMetricSectionCurveData
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (D : RicciDeTurckSmoothRealizationDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart sol) :
    SmoothMetricSectionCurveData
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover sol :=
  SmoothMetricSectionCurveData.of_smoothIntrinsicDeTurckRealization
    (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover
    D.toSmoothIntrinsicDeTurckRealization

/-- The smooth realization produced from interval closure data uses the chosen
background. -/
theorem RicciDeTurckSmoothRealizationDataOnIcc.usesChosenBackground
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (D : RicciDeTurckSmoothRealizationDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart sol) :
    UsesChosenBackground (I := I) (M := M)
      (D.toSmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution) := by
  dsimp [UsesChosenBackground,
    BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution,
    RicciDeTurckSmoothRealizationDataOnIcc.toSmoothIntrinsicDeTurckRealization]
  exact D.hbackground

/-- The chosen-background DeTurck solution produced by interval closure data. -/
def RicciDeTurckSmoothRealizationDataOnIcc.toChosenIntrinsicDeTurckLocalSolution
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (D : RicciDeTurckSmoothRealizationDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart sol) :
    ChosenIntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp :=
  ⟨D.toSmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution,
    D.usesChosenBackground⟩

/-- Interval closure data self-encodes its produced chosen-background candidate
in the same bounded Ricci-DeTurck Banach chart. -/
def RicciDeTurckSmoothRealizationDataOnIcc.toCandidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)}
    (D : RicciDeTurckSmoothRealizationDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart sol) :
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
      (M := M) (F := F) (I := I) chart
      (D.toChosenIntrinsicDeTurckLocalSolution.1) :=
  TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding.of_chosenSmoothRealization
    (M := M) (F := F) (I := I)
    D.terminal_le_chart D.toSmoothIntrinsicDeTurckRealization D.usesChosenBackground

/-- Global Ricci-DeTurck Banach-chart closure data: every Banach solution has a
smooth chosen-background realization, and every chosen-background candidate can
be encoded back into the same chart. -/
structure RicciDeTurckChartClosureData
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate) where
  realization : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
    RicciDeTurckSmoothRealizationData x0 et het Kc hKc Ko hKo hKoEq hcover chart sol
  encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp,
    TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
      (M := M) (F := F) (I := I) chart candidate.1

/-- Global chart closure data gives a proof-level smooth realization witness for
every Banach solution in the positive-definite locus. -/
theorem RicciDeTurckChartClosureData.nonempty_realization
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)) :
    Nonempty (RicciDeTurckSmoothRealizationData
      x0 et het Kc hKc Ko hKo hKoEq hcover chart sol) :=
  ⟨D.realization sol⟩

/-- Global chart closure data self-encodes the chosen-background candidate
produced by realizing any Banach solution. -/
def RicciDeTurckChartClosureData.realizationCandidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)) :
    TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
      (M := M) (F := F) (I := I) chart
      ((D.realization sol).toChosenIntrinsicDeTurckLocalSolution.1) :=
  (D.realization sol).toCandidateEncoding

/-- Global chart closure data gives a proof-level Banach encoding witness for
every chosen-background intrinsic DeTurck candidate. -/
theorem RicciDeTurckChartClosureData.nonempty_candidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (candidate : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp) :
    Nonempty (TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
      (M := M) (F := F) (I := I) chart candidate.1) :=
  ⟨D.encode candidate⟩

/-- Build global chart closure data directly from smooth section-curve realizations, endpoint scalar
derivatives, and the solution-specific geometric RHS identification. -/
def RicciDeTurckChartClosureData.of_smoothMetricSectionCurve_endpointSectionDerivatives_chartRHS
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (spatial :
      ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        SmoothMetricSectionCurveData
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover sol)
    (initial_hasDerivAt :
      ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        ∀ (x : M) (u v : TangentSpace I x),
          HasDerivAt (fun τ : ℝ ↦ (spatial sol).sectionCurve τ x u v)
            (chart.A ivp.initialTime (sol.curve ivp.initialTime) x u v) ivp.initialTime)
    (terminal_hasDerivAt :
      ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        ∀ (x : M) (u v : TangentSpace I x),
          HasDerivAt (fun τ : ℝ ↦ (spatial sol).sectionCurve τ x u v)
            (chart.A sol.terminalTime (sol.curve sol.terminalTime) x u v) sol.terminalTime)
    (chartRHS_eq_intrinsic :
      ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            chart.A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (spatial sol).metric
                (chosenLeviCivitaFamily (I := I) (M := M) (spatial sol).metric) t x u v)
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1) :
    RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart where
  realization sol :=
    RicciDeTurckSmoothRealizationData.of_smoothMetricSectionCurve_endpointSectionDerivatives_chartRHS
      (M := M) (F := F) (I := I) (x0 := x0) (et := et) (het := het)
      (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
      (hKoEq := hKoEq) (hcover := hcover) (chart := chart)
      (spatial sol) (initial_hasDerivAt sol) (terminal_hasDerivAt sol)
      (chartRHS_eq_intrinsic sol)
  encode := encode

/-- Build global chart closure data from smooth section-curve realizations, endpoint scalar
derivatives, and a chart-level specific Ricci-DeTurck RHS identification. -/
def RicciDeTurckChartClosureData.of_smoothMetricSectionCurve_endpointSectionDerivatives_specificRHS
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover chart.A)
    (spatial :
      ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        SmoothMetricSectionCurveData
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover sol)
    (initial_hasDerivAt :
      ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        ∀ (x : M) (u v : TangentSpace I x),
          HasDerivAt (fun τ : ℝ ↦ (spatial sol).sectionCurve τ x u v)
            (chart.A ivp.initialTime (sol.curve ivp.initialTime) x u v) ivp.initialTime)
    (terminal_hasDerivAt :
      ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        ∀ (x : M) (u v : TangentSpace I x),
          HasDerivAt (fun τ : ℝ ↦ (spatial sol).sectionCurve τ x u v)
            (chart.A sol.terminalTime (sol.curve sol.terminalTime) x u v) sol.terminalTime)
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChart.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1) :
    RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart :=
  RicciDeTurckChartClosureData.of_smoothMetricSectionCurve_endpointSectionDerivatives_chartRHS
    (M := M) (F := F) (I := I) (x0 := x0) (et := et) (het := het)
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover) (chart := chart)
    spatial initial_hasDerivAt terminal_hasDerivAt
    (fun sol {t} ht x u v ↦
      SmoothSectionRHSIdentification.chartRHS_eq_intrinsic
        (M := M) (F := F) (I := I) (rhs := rhs) (spatial sol) ht x u v)
    encode

/-- Global chart closure data yields the chosen-background DeTurck theorem
package. -/
theorem RicciDeTurckChartClosureData.toChosenIntrinsicDeTurckLocalExistenceUniqueness
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  TimeDependentGeometricRicciDeTurckBanachChart.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncoding
    (M := M) (F := F) (I := I) chart
    (fun sol ↦ (D.realization sol).toSmoothIntrinsicDeTurckRealization)
    (fun sol ↦ by
      simpa using (D.realization sol).usesChosenBackground)
    D.encode

/-- Proof-level chosen-background DeTurck theorem package from global chart closure data. -/
theorem RicciDeTurckChartClosureData.nonempty_chosenIntrinsicDeTurckLocalExistenceUniqueness
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := F) (H := H) (I := I) (M := M) ivp) :=
  ⟨D.toChosenIntrinsicDeTurckLocalExistenceUniqueness⟩

/-- Global chart closure data yields the intrinsic compact point-4 theorem package via the
chosen-background identity `C³` gauge. -/
noncomputable def RicciDeTurckChartClosureData.toIntrinsicLocalExistenceUniqueness
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  D.toChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaIdentityDiffeomorph3Gauge

/-- Global chart closure data yields the ordinary compact point-4 theorem package via the
chosen-background identity `C³` gauge. -/
noncomputable def RicciDeTurckChartClosureData.toLocalExistenceUniqueness
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    LocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  D.toChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaIdentityDiffeomorph3Gauge

/-- Interval Ricci-DeTurck Banach-chart closure data: every Banach solution has a
smooth chosen-background realization, and every chosen-background candidate can
be encoded back into the same bounded chart. -/
structure RicciDeTurckChartClosureDataOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate) where
  realization : ∀ sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
    RicciDeTurckSmoothRealizationDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart sol
  encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp,
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
      (M := M) (F := F) (I := I) chart candidate.1

/-- Interval chart closure data gives a proof-level smooth realization witness
for every Banach solution in the positive-definite locus. -/
theorem RicciDeTurckChartClosureDataOnIcc.nonempty_realization
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)) :
    Nonempty (RicciDeTurckSmoothRealizationDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart sol) :=
  ⟨D.realization sol⟩

/-- Interval chart closure data self-encodes the chosen-background candidate
produced by realizing any Banach solution. -/
def RicciDeTurckChartClosureDataOnIcc.realizationCandidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (sol : BanachEvolutionLocalSolutionIn chart.A
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)) :
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
      (M := M) (F := F) (I := I) chart
      ((D.realization sol).toChosenIntrinsicDeTurckLocalSolution.1) :=
  (D.realization sol).toCandidateEncoding

/-- Interval chart closure data gives a proof-level Banach encoding witness for
every chosen-background intrinsic DeTurck candidate. -/
theorem RicciDeTurckChartClosureDataOnIcc.nonempty_candidateEncoding
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (candidate : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp) :
    Nonempty (TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
      (M := M) (F := F) (I := I) chart candidate.1) :=
  ⟨D.encode candidate⟩

/-- Build interval chart closure data directly from smooth section-curve realizations, endpoint
scalar derivatives, and the solution-specific geometric RHS identification. -/
def RicciDeTurckChartClosureDataOnIcc.of_smoothMetricSectionCurve_endpointSectionDerivatives_chartRHS
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (terminal_le_chart :
      ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        sol.terminalTime ≤ T)
    (spatial :
      ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        SmoothMetricSectionCurveData
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover sol)
    (initial_hasDerivAt :
      ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        ∀ (x : M) (u v : TangentSpace I x),
          HasDerivAt (fun τ : ℝ ↦ (spatial sol).sectionCurve τ x u v)
            (chart.A ivp.initialTime (sol.curve ivp.initialTime) x u v) ivp.initialTime)
    (terminal_hasDerivAt :
      ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        ∀ (x : M) (u v : TangentSpace I x),
          HasDerivAt (fun τ : ℝ ↦ (spatial sol).sectionCurve τ x u v)
            (chart.A sol.terminalTime (sol.curve sol.terminalTime) x u v) sol.terminalTime)
    (chartRHS_eq_intrinsic :
      ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime sol.terminalTime →
          ∀ (x : M) (u v : TangentSpace I x),
            chart.A t (sol.curve t) x u v =
              intrinsicRicciDeTurckRHS (I := I) (M := M)
                (spatial sol).metric
                (chosenLeviCivitaFamily (I := I) (M := M) (spatial sol).metric) t x u v)
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1) :
    RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart where
  realization sol :=
    RicciDeTurckSmoothRealizationDataOnIcc.of_smoothMetricSectionCurve_endpointSectionDerivatives_chartRHS
      (M := M) (F := F) (I := I) (x0 := x0) (et := et) (het := het)
      (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
      (hKoEq := hKoEq) (hcover := hcover) (chart := chart)
      (terminal_le_chart sol) (spatial sol)
      (initial_hasDerivAt sol) (terminal_hasDerivAt sol) (chartRHS_eq_intrinsic sol)
  encode := encode

/-- Build interval chart closure data from smooth section-curve realizations, endpoint scalar
derivatives, and a chart-level specific Ricci-DeTurck RHS identification. -/
def RicciDeTurckChartClosureDataOnIcc.of_smoothMetricSectionCurve_endpointSectionDerivatives_specificRHS
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover chart.A)
    (terminal_le_chart :
      ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        sol.terminalTime ≤ T)
    (spatial :
      ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        SmoothMetricSectionCurveData
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover sol)
    (initial_hasDerivAt :
      ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        ∀ (x : M) (u v : TangentSpace I x),
          HasDerivAt (fun τ : ℝ ↦ (spatial sol).sectionCurve τ x u v)
            (chart.A ivp.initialTime (sol.curve ivp.initialTime) x u v) ivp.initialTime)
    (terminal_hasDerivAt :
      ∀ sol : BanachEvolutionLocalSolutionIn chart.A
        (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          et Kc hKc Ko hKo hKoEq hcover) ivp.initialTime
        (InitialValueProblem.toContinuousSectionSpace
          (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp),
        ∀ (x : M) (u v : TangentSpace I x),
          HasDerivAt (fun τ : ℝ ↦ (spatial sol).sectionCurve τ x u v)
            (chart.A sol.terminalTime (sol.curve sol.terminalTime) x u v) sol.terminalTime)
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
        (M := M) (F := F) (I := I) chart candidate.1) :
    RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart :=
  RicciDeTurckChartClosureDataOnIcc.of_smoothMetricSectionCurve_endpointSectionDerivatives_chartRHS
    (M := M) (F := F) (I := I) (x0 := x0) (et := et) (het := het)
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover) (chart := chart)
    terminal_le_chart spatial initial_hasDerivAt terminal_hasDerivAt
    (fun sol {t} ht x u v ↦
      SmoothSectionRHSIdentification.chartRHS_eq_intrinsic
        (M := M) (F := F) (I := I) (rhs := rhs) (spatial sol) ht x u v)
    encode

/-- Interval chart closure data yields the chosen-background DeTurck theorem
package. -/
theorem RicciDeTurckChartClosureDataOnIcc.toChosenIntrinsicDeTurckLocalExistenceUniqueness
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  TimeDependentGeometricRicciDeTurckBanachChartOnIcc.chosenIntrinsicDeTurckLocalExistenceUniqueness_of_smoothRealization_and_chosenCandidateEncoding
    (M := M) (F := F) (I := I) chart
    (fun sol ↦ (D.realization sol).toSmoothIntrinsicDeTurckRealization)
    (fun sol ↦ by
      simpa using (D.realization sol).usesChosenBackground)
    D.encode

/-- Proof-level chosen-background DeTurck theorem package from interval chart closure data. -/
theorem RicciDeTurckChartClosureDataOnIcc.nonempty_chosenIntrinsicDeTurckLocalExistenceUniqueness
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    Nonempty (ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := F) (H := H) (I := I) (M := M) ivp) :=
  ⟨D.toChosenIntrinsicDeTurckLocalExistenceUniqueness⟩

/-- Interval chart closure data yields the intrinsic compact point-4 theorem package via the
chosen-background identity `C³` gauge. -/
noncomputable def RicciDeTurckChartClosureDataOnIcc.toIntrinsicLocalExistenceUniqueness
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  D.toChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaIdentityDiffeomorph3Gauge

/-- Interval chart closure data yields the ordinary compact point-4 theorem package via the
chosen-background identity `C³` gauge. -/
noncomputable def RicciDeTurckChartClosureDataOnIcc.toLocalExistenceUniqueness
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    LocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  D.toChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaIdentityDiffeomorph3Gauge

/-- The interval Ricci-DeTurck chart vector field restricted to the genuine symmetric metric
carrier. Outside the Riemannian-metric locus we use `0`, so the map is total on the closed
symmetric submodule; on the metric locus it is exactly the chart's ambient vector field. -/
noncomputable def TimeDependentGeometricRicciDeTurckBanachChartOnIcc.restrictedSymmetricA
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate) :
    ℝ →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover :=
  fun τ s => by
    classical
    by_cases hs : s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover
    · exact ⟨chart.A τ (s :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover), by
        rw [mem_symmetricSectionSubmodule_iff
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          x0 et het Kc hKc Ko hKo hKoEq hcover]
        exact chart.A_mem_symmetricLocus τ hs⟩
    · exact 0

/-- On the Riemannian-metric locus, the restricted symmetric vector field is exactly the ambient
Ricci-DeTurck chart vector field. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.restrictedSymmetricA_coe_of_mem
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate) :
    ∀ t x,
      x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
        ((chart.restrictedSymmetricA
          (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) t x :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) =
          chart.A t (x :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) := by
  intro t x hx
  simp [TimeDependentGeometricRicciDeTurckBanachChartOnIcc.restrictedSymmetricA, hx]

/-- Ambient interval Lipschitz control descends to the chart-derived vector field on the genuine
symmetric Riemannian-metric carrier. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.restrictedSymmetricA_lipschitzOn_Icc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate) :
    ∀ t ∈ Icc ivp.initialTime T, LipschitzOnWith Kstate
      ((chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) t)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) := by
  intro t ht x hx y hy
  have hxy := chart.lipschitzOn_Icc t ht hx hy
  simpa [TimeDependentGeometricRicciDeTurckBanachChartOnIcc.restrictedSymmetricA, hx, hy] using hxy

/-- Restrict an interval Ricci-DeTurck chart to a shorter forward interval and a smaller Picard
radius.  The Banach representative and geometric RHS identification are unchanged; only the
Picard-Lindelöf data and interval-scoped Lipschitz proof are shrunk. -/
def TimeDependentGeometricRicciDeTurckBanachChartOnIcc.shrink
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    {T' : ℝ} (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
    {a' : ℝ≥0} (ha' : a' ≤ a)
    (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
      a' - (0 : ℝ≥0)) :
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate where
  A := chart.A
  hT := hT'
  picard := chart.picard.shrink
    (⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT'⟩⟩ : Icc ivp.initialTime T')
    le_rfl hT'le ha' (by simpa using htime)
  lipschitzOn_Icc := fun t ht =>
    chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩
  geometric := chart.geometric
/-- If the Picard closed ball in the symmetric submodule is contained in the Riemannian-metric
locus, the ambient interval Picard-Lindelöf estimates transfer to the chart-derived symmetric
carrier.  This is the proof bridge needed after shrinking the analytic radius to remain inside
the open cone of metrics. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.restrictedSymmetricA_picard_of_closedBall_subset_riemannianMetricLocus
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (hball : Metric.closedBall
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a ⊆
      riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) :
    IsPicardLindelof
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (tmin := ivp.initialTime) (tmax := T)
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt chart.hT⟩⟩
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a 0 L Kpic where
  lipschitzOnWith t ht := by
    intro x hx y hy
    have hxLocus : x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover :=
      hball hx
    have hyLocus : y ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover :=
      hball hy
    have hxAmb :
        (x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) ∈
        Metric.closedBall
          ((InitialValueProblem.toSymmetricSectionSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) a := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hyAmb :
        (y : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) ∈
        Metric.closedBall
          ((InitialValueProblem.toSymmetricSectionSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) a := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    have hxy := chart.picard.lipschitzOnWith t ht
      (x := (x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)) hxAmb
      (y := (y : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)) hyAmb
    simpa [Subtype.edist_eq,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.restrictedSymmetricA, hxLocus, hyLocus]
      using hxy
  continuousOn x hx := by
    have hxLocus : x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover :=
      hball hx
    have hxAmb :
        (x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) ∈
        Metric.closedBall
          ((InitialValueProblem.toSymmetricSectionSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) a := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hcontAmb := chart.picard.continuousOn
      ((x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)) hxAmb
    have hcontCoe : ContinuousOn
        (fun t => ((chart.restrictedSymmetricA
          (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) t x :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover))
        (Icc ivp.initialTime T) := by
      refine hcontAmb.congr ?_
      intro t ht
      exact chart.restrictedSymmetricA_coe_of_mem
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover t x hxLocus
    rw [continuousOn_iff_continuous_restrict] at hcontCoe ⊢
    simpa using Continuous.subtype_mk hcontCoe
      (fun t => ((chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) t.1 x).2)
  norm_le t ht x hx := by
    have hxLocus : x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover :=
      hball hx
    have hxAmb :
        (x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) ∈
        Metric.closedBall
          ((InitialValueProblem.toSymmetricSectionSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) a := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hnorm := chart.picard.norm_le t ht
      ((x : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)) hxAmb
    simpa [TimeDependentGeometricRicciDeTurckBanachChartOnIcc.restrictedSymmetricA, hxLocus]
      using hnorm
  mul_max_le := chart.picard.mul_max_le

/-- After shrinking an interval chart to a closed ball contained in the metric cone, the symmetric
carrier Picard-Lindelöf hypotheses are obtained automatically from the ambient chart Picard data. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.shrink_restrictedSymmetricA_picard_of_closedBall_subset_riemannianMetricLocus
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    {T' : ℝ} (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
    {a' : ℝ≥0} (ha' : a' ≤ a)
    (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
      a' - (0 : ℝ≥0))
    (hball : Metric.closedBall
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
      riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) :
    let chart' := chart.shrink (M := M) (F := F) (I := I)
      hT' hT'le ha' htime
    IsPicardLindelof
      (chart'.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (tmin := ivp.initialTime) (tmax := T')
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt chart'.hT⟩⟩
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a' 0 L Kpic := by
  let chart' := chart.shrink (M := M) (F := F) (I := I)
    hT' hT'le ha' htime
  exact chart'.restrictedSymmetricA_picard_of_closedBall_subset_riemannianMetricLocus
    (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover hball

/-- An interval reverse candidate encoding into the ambient Ricci-DeTurck chart is automatically
valued in the symmetric positive-definite locus on the encoded interval.  The positivity is the
state invariant of the encoded Banach solution; symmetry comes from the smooth Riemannian metric
realizing that Banach curve. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding.curve_mem_symmetricPositiveDefiniteLocus
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {candidate : IntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp}
    (enc : TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
      (M := M) (F := F) (I := I) chart candidate)
    {t : ℝ} (ht : t ∈ Icc ivp.initialTime candidate.terminalTime) :
    enc.sol.curve t ∈ symmetricPositiveDefiniteLocus (M := M) (F := F)
      (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover := by
  have htSol : t ∈ Icc ivp.initialTime enc.sol.terminalTime := by
    simpa [enc.terminal_eq] using ht
  refine ⟨?_, enc.sol.mem_state htSol⟩
  intro x u v
  calc
    enc.sol.curve t x u v =
        metricTensor (I := I) (M := M) enc.realization.metric t x u v :=
      (enc.realization.metric_eq_curve htSol x u v).symm
    _ = metricTensor (I := I) (M := M)
        candidate.toIntrinsicDeTurckSolution.metric t x u v :=
      (enc.metric_eq ht x u v).symm
    _ = metricTensor (I := I) (M := M)
        candidate.toIntrinsicDeTurckSolution.metric t x v u := by
      simpa [metricTensor] using
        (candidate.toIntrinsicDeTurckSolution.metric t).symm x u v
    _ = metricTensor (I := I) (M := M) enc.realization.metric t x v u :=
      enc.metric_eq ht x v u
    _ = enc.sol.curve t x v u :=
      enc.realization.metric_eq_curve htSol x v u

/-- The ambient reverse encoding curve canonically determines a point of the symmetric-carrier
Riemannian metric locus on the encoded interval. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding.curve_toSymmetricSectionSubmodule_mem_riemannianMetricLocusSubmodule
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {candidate : IntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp}
    (enc : TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
      (M := M) (F := F) (I := I) chart candidate)
    {t : ℝ} (ht : t ∈ Icc ivp.initialTime candidate.terminalTime) :
    (⟨enc.sol.curve t, by
      rw [mem_symmetricSectionSubmodule_iff
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        x0 et het Kc hKc Ko hKo hKoEq hcover]
      exact (enc.curve_mem_symmetricPositiveDefiniteLocus
        (M := M) (F := F) (I := I) ht).1⟩ :
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) ∈
      riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover := by
  rw [mem_riemannianMetricLocusSubmodule_iff
    (M := M) (F := F) (W := (TangentSpace I : M → Type _))
    x0 et het Kc hKc Ko hKo hKoEq hcover]
  exact enc.curve_mem_symmetricPositiveDefiniteLocus
    (M := M) (F := F) (I := I) ht

/-- Total symmetric-submodule curve associated to an ambient candidate encoding. It agrees with the
ambient encoded curve on the solution interval and uses the initial metric outside that interval so
that it is a total curve into the closed symmetric carrier. -/
noncomputable def TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding.toSymmetricSectionSubmoduleCurve
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {candidate : IntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp}
    (enc : TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
      (M := M) (F := F) (I := I) chart candidate) :
    ℝ → symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover :=
  fun t => by
    classical
    by_cases ht : t ∈ Icc ivp.initialTime enc.sol.terminalTime
    · exact ⟨enc.sol.curve t, by
        rw [mem_symmetricSectionSubmodule_iff
          (M := M) (F := F) (W := (TangentSpace I : M → Type _))
          x0 et het Kc hKc Ko hKo hKoEq hcover]
        exact (enc.curve_mem_symmetricPositiveDefiniteLocus
          (M := M) (F := F) (I := I) (by simpa [enc.terminal_eq] using ht)).1⟩
    · exact InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp

theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding.coe_toSymmetricSectionSubmoduleCurve_of_mem
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {candidate : IntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp}
    (enc : TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
      (M := M) (F := F) (I := I) chart candidate)
    {t : ℝ} (ht : t ∈ Icc ivp.initialTime enc.sol.terminalTime) :
    ((enc.toSymmetricSectionSubmoduleCurve
      (M := M) (F := F) (I := I) (x0 := x0) (het := het) t) :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) =
      enc.sol.curve t := by
  simp [TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding.toSymmetricSectionSubmoduleCurve,
    ht]

theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding.toSymmetricSectionSubmoduleCurve_initial_eq
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {candidate : IntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp}
    (enc : TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
      (M := M) (F := F) (I := I) chart candidate) :
    enc.toSymmetricSectionSubmoduleCurve
      (M := M) (F := F) (I := I) (x0 := x0) (het := het) ivp.initialTime =
      InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp := by
  apply Subtype.ext
  have ht : ivp.initialTime ∈ Icc ivp.initialTime enc.sol.terminalTime :=
    ⟨le_rfl, le_of_lt enc.sol.initial_lt_terminal⟩
  simp [TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding.coe_toSymmetricSectionSubmoduleCurve_of_mem,
    ht, enc.sol.initial_eq]

theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding.toSymmetricSectionSubmoduleCurve_mem_state
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {candidate : IntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp}
    (enc : TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
      (M := M) (F := F) (I := I) chart candidate)
    {t : ℝ} (ht : t ∈ Icc ivp.initialTime enc.sol.terminalTime) :
    enc.toSymmetricSectionSubmoduleCurve
      (M := M) (F := F) (I := I) (x0 := x0) (het := het) t ∈
      riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover := by
  rw [mem_riemannianMetricLocusSubmodule_iff
    (M := M) (F := F) (W := (TangentSpace I : M → Type _))
    x0 et het Kc hKc Ko hKo hKoEq hcover]
  have htCand : t ∈ Icc ivp.initialTime candidate.terminalTime := by
    simpa [enc.terminal_eq] using ht
  have hspd := enc.curve_mem_symmetricPositiveDefiniteLocus
    (M := M) (F := F) (I := I) htCand
  simpa [TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding.coe_toSymmetricSectionSubmoduleCurve_of_mem,
    ht] using hspd

/-- The total symmetric-submodule curve associated to an ambient candidate encoding satisfies the
symmetric-carrier ODE on the encoded interval, provided the symmetric vector field agrees with the
ambient chart vector field on the Riemannian metric locus. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding.toSymmetricSectionSubmoduleCurve_equation
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {candidate : IntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp}
    (enc : TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
      (M := M) (F := F) (I := I) chart candidate)
    (Asub : ℝ →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (hcomm : ∀ t x,
      x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
        (Asub t x :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) =
          chart.A t (x :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover))
    {t : ℝ} (ht : t ∈ Icc ivp.initialTime enc.sol.terminalTime) :
    HasDerivWithinAt
      (enc.toSymmetricSectionSubmoduleCurve
        (M := M) (F := F) (I := I) (x0 := x0) (het := het))
      (Asub t (enc.toSymmetricSectionSubmoduleCurve
        (M := M) (F := F) (I := I) (x0 := x0) (het := het) t))
      (Icc ivp.initialTime enc.sol.terminalTime) t := by
  let γ := enc.toSymmetricSectionSubmoduleCurve
    (M := M) (F := F) (I := I) (x0 := x0) (het := het)
  have hγcoe : ∀ τ ∈ Icc ivp.initialTime enc.sol.terminalTime,
      ((γ τ : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) =
        enc.sol.curve τ := by
    intro τ hτ
    exact enc.coe_toSymmetricSectionSubmoduleCurve_of_mem
      (M := M) (F := F) (I := I) (x0 := x0) (het := het) hτ
  have hγmem : γ t ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
      (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover :=
    enc.toSymmetricSectionSubmoduleCurve_mem_state
      (M := M) (F := F) (I := I) (x0 := x0) (het := het) ht
  have htarget :
      chart.A t (enc.sol.curve t) =
        (Asub t (γ t) :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) := by
    calc
      chart.A t (enc.sol.curve t) =
          chart.A t ((γ t : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) := by
        rw [hγcoe t ht]
      _ = (Asub t (γ t) :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) := (hcomm t (γ t) hγmem).symm
  have hamb :
      HasDerivWithinAt
        (fun τ : ℝ => ((γ τ : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover))
        ((Asub t (γ t) : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover)
        (Icc ivp.initialTime enc.sol.terminalTime) t :=
    ((enc.sol.equation ht).congr hγcoe (hγcoe t ht)).congr_deriv htarget
  exact (Submodule.hasDerivWithinAt_subtype_iff
    (symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (g := γ)
    (g' := Asub t (γ t))
    (s := Icc ivp.initialTime enc.sol.terminalTime)
    (t := t)).2 hamb

/-- Interior unrestricted version of `toSymmetricSectionSubmoduleCurve_equation`.  Away from the
closed interval boundary, the ambient Banach ODE gives an ordinary derivative, and the derivative
descends through the symmetric submodule. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding.toSymmetricSectionSubmoduleCurve_hasDerivAt_of_mem_Ioo
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {candidate : IntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp}
    (enc : TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
      (M := M) (F := F) (I := I) chart candidate)
    (Asub : ℝ →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (hcomm : ∀ t x,
      x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
        (Asub t x :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) =
          chart.A t (x :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover))
    {t : ℝ} (ht : t ∈ Ioo ivp.initialTime enc.sol.terminalTime) :
    HasDerivAt
      (enc.toSymmetricSectionSubmoduleCurve
        (M := M) (F := F) (I := I) (x0 := x0) (het := het))
      (Asub t (enc.toSymmetricSectionSubmoduleCurve
        (M := M) (F := F) (I := I) (x0 := x0) (het := het) t)) t := by
  let γ := enc.toSymmetricSectionSubmoduleCurve
    (M := M) (F := F) (I := I) (x0 := x0) (het := het)
  have hγcoe : ∀ τ ∈ Icc ivp.initialTime enc.sol.terminalTime,
      ((γ τ : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) =
        enc.sol.curve τ := by
    intro τ hτ
    exact enc.coe_toSymmetricSectionSubmoduleCurve_of_mem
      (M := M) (F := F) (I := I) (x0 := x0) (het := het) hτ
  have hγmem : γ t ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
      (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover :=
    enc.toSymmetricSectionSubmoduleCurve_mem_state
      (M := M) (F := F) (I := I) (x0 := x0) (het := het) (Ioo_subset_Icc_self ht)
  have htarget :
      chart.A t (enc.sol.curve t) =
        (Asub t (γ t) :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) := by
    calc
      chart.A t (enc.sol.curve t) =
          chart.A t ((γ t : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) := by
        rw [hγcoe t (Ioo_subset_Icc_self ht)]
      _ = (Asub t (γ t) :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) := (hcomm t (γ t) hγmem).symm
  have hEq :
      (fun τ : ℝ =>
        ((γ τ : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover)) =ᶠ[𝓝 t] enc.sol.curve := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
    exact hγcoe τ hτ
  have hamb :
      HasDerivAt
        (fun τ : ℝ =>
          ((γ τ : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover))
        ((Asub t (γ t) : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) t := by
    exact
      ((enc.sol.toBanachEvolutionLocalSolution.equation_hasDerivAt_of_mem_Ioo ht).congr_of_eventuallyEq
        hEq).congr_deriv htarget
  exact (Submodule.hasDerivAt_subtype_iff
    (symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (g := γ)
    (g' := Asub t (γ t))
    (t := t)).2 hamb

/-- Candidate encoding for the genuine symmetric Banach carrier.  The encoded
solution lives in the closed submodule of symmetric section-space bilinear
forms, not in the larger ambient nonsymmetric carrier. -/
structure SymmetricSubmoduleCandidateEncodingOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ}
    (Asub : ℝ →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)
    (hcomm : ∀ t x,
      x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
        (Asub t x :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) =
          A t (x :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover))
    (candidate : IntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp) where
  /-- The symmetric-carrier Banach solution representing the candidate. -/
  sol : BanachEvolutionLocalSolutionIn Asub
    (riemannianMetricLocusSubmodule (M := M) (F := F)
      (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
    ivp.initialTime
    (InitialValueProblem.toSymmetricSectionSubmodule
      (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)
  /-- The encoded interval stays inside the Picard interval used for the symmetric carrier. -/
  terminal_le_chart : sol.terminalTime ≤ T
  /-- The smooth realization of the ambient image of the symmetric-carrier solution. -/
  realization : BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
    (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp
    (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
      (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp hcomm sol)
  /-- The symmetric-carrier and candidate intervals have the same terminal time. -/
  terminal_eq : sol.terminalTime = candidate.terminalTime
  /-- The candidate metric is the smooth realization of the encoded symmetric-carrier solution. -/
  metric_eq : ∀ ⦃t : ℝ⦄, t ∈ Icc ivp.initialTime candidate.terminalTime →
    ∀ (x : M) (u v : TangentSpace I x),
      metricTensor (I := I) (M := M) candidate.toIntrinsicDeTurckSolution.metric t x u v =
        metricTensor (I := I) (M := M) realization.metric t x u v

/-- Restrict a genuine symmetric-carrier candidate encoding to a shorter candidate terminal time.
The symmetric Banach solution is restricted in the symmetric carrier, while the ambient smooth
realization reuses the same metric, velocity, and background data on the shorter interval. -/
def SymmetricSubmoduleCandidateEncodingOnIcc.restrictTerminal
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ}
    {Asub : ℝ →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover}
    {A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover}
    {hcomm : ∀ t x,
      x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
        (Asub t x :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) =
          A t (x :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)}
    {candidate : IntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp}
    (enc : SymmetricSubmoduleCandidateEncodingOnIcc
      (T := T) x0 et het Kc hKc Ko hKo hKoEq hcover Asub A hcomm candidate)
    {T' : ℝ} (hT'₀ : ivp.initialTime < T') (hT' : T' ≤ candidate.terminalTime) :
    SymmetricSubmoduleCandidateEncodingOnIcc
      (T := T) x0 et het Kc hKc Ko hKo hKoEq hcover Asub A hcomm
      (candidate.restrictTerminal hT'₀ hT') := by
  let sol' := enc.sol.restrictTerminal hT'₀ (by simpa [enc.terminal_eq] using hT')
  let ambSol' :=
    BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
      (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp hcomm sol'
  let ambSol :=
    BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
      (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp hcomm enc.sol
  have hT'sol : T' ≤ enc.sol.terminalTime := by
    simpa [enc.terminal_eq] using hT'
  have hAmbSubset :
      Icc ivp.initialTime ambSol'.terminalTime ⊆ Icc ivp.initialTime ambSol.terminalTime := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    have htSol' : t ≤ T' := by
      simpa [ambSol',
        BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule,
        BanachEvolutionLocalSolutionIn.mapContinuousLinearMapBetween, sol'] using ht.2
    simpa [ambSol,
      BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule,
      BanachEvolutionLocalSolutionIn.mapContinuousLinearMapBetween] using
      le_trans htSol' hT'sol
  refine
    { sol := sol'
      terminal_le_chart := ?_
      realization := ?_
      terminal_eq := ?_
      metric_eq := ?_ }
  · exact le_trans hT'sol enc.terminal_le_chart
  · exact
      { metric := enc.realization.metric
        metricVelocity := enc.realization.metricVelocity
        background := enc.realization.background
        metric_eq_curve := by
          intro t ht x u v
          simpa [ambSol',
            ambSol,
            BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule,
            BanachEvolutionLocalSolutionIn.mapContinuousLinearMapBetween, sol',
            BanachEvolutionLocalSolutionIn.restrictTerminal] using
            enc.realization.metric_eq_curve (hAmbSubset ht) x u v
        hasTimeDerivative := by
          exact enc.realization.hasTimeDerivative.mono hAmbSubset
        equation := by
          intro t ht
          exact enc.realization.equation (hAmbSubset ht) }
  · rfl
  · intro t ht x u v
    have htCandidate : t ∈ Icc ivp.initialTime candidate.terminalTime :=
      ⟨ht.1, le_trans (by simpa [IntrinsicDeTurckLocalSolution.restrictTerminal] using ht.2) hT'⟩
    simpa [IntrinsicDeTurckLocalSolution.restrictTerminal] using
      enc.metric_eq htCandidate x u v

/-- Localized symmetric-carrier uniqueness for chosen-background DeTurck candidates.  It only asks
for reverse encodings of the candidates after both have been restricted to the same shorter
terminal time `S` inside the chart interval, and concludes metric equality on `[t₀, S]`. -/
theorem chosenIntrinsicDeTurckLocalSolution_metric_eq_on_restricted_interval_of_symmetricSubmoduleCandidateEncodingOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
    {T : ℝ} {Kstate : ℝ≥0}
    (Asub : ℝ →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)
    (hcomm : ∀ t x,
      x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
        (Asub t x :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) =
          A t (x :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover))
    (lipschitzOn_Icc : ∀ t ∈ Icc ivp.initialTime T, LipschitzOnWith Kstate (Asub t)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover))
    (encode :
      ∀ (candidate : ChosenIntrinsicDeTurckLocalSolution
          (E := F) (H := H) (I := I) (M := M) ivp)
        {S : ℝ} (hS₀ : ivp.initialTime < S) (hScandidate : S ≤ candidate.1.terminalTime)
        (_hSchart : S ≤ T),
        SymmetricSubmoduleCandidateEncodingOnIcc
          (T := T) x0 et het Kc hKc Ko hKo hKoEq hcover
          Asub A hcomm (candidate.1.restrictTerminal hS₀ hScandidate))
    (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp)
    {S : ℝ} (hS₀ : ivp.initialTime < S)
    (hS₁ : S ≤ sol₁.1.terminalTime) (hS₂ : S ≤ sol₂.1.terminalTime) (hST : S ≤ T)
    {t : ℝ} (ht : t ∈ Icc ivp.initialTime S)
    (x : M) (u v : TangentSpace I x) :
    metricTensor (I := I) (M := M) sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.1.toIntrinsicDeTurckSolution.metric t x u v := by
  let enc₁ := encode sol₁ hS₀ hS₁ hST
  let enc₂ := encode sol₂ hS₀ hS₂ hST
  have htCandidate₁ :
      t ∈ Icc ivp.initialTime (sol₁.1.restrictTerminal hS₀ hS₁).terminalTime := by
    simpa [IntrinsicDeTurckLocalSolution.restrictTerminal] using ht
  have htCandidate₂ :
      t ∈ Icc ivp.initialTime (sol₂.1.restrictTerminal hS₀ hS₂).terminalTime := by
    simpa [IntrinsicDeTurckLocalSolution.restrictTerminal] using ht
  have hS_enc₁ : S ≤ enc₁.sol.terminalTime := by
    rw [enc₁.terminal_eq]
    simp [IntrinsicDeTurckLocalSolution.restrictTerminal]
  have hS_enc₂ : S ≤ enc₂.sol.terminalTime := by
    rw [enc₂.terminal_eq]
    simp [IntrinsicDeTurckLocalSolution.restrictTerminal]
  have hEq := BanachEvolutionLocalSolutionIn.eqOn_Icc_of_lipschitzOn_Icc_of_le_terminal
    (F := Asub)
    (stateSet := riemannianMetricLocusSubmodule (M := M) (F := F)
      (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
    (t₀ := ivp.initialTime)
    (u₀ := InitialValueProblem.toSymmetricSectionSubmodule
      (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)
    (K := Kstate) enc₁.sol enc₂.sol hS₀ hS_enc₁ hS_enc₂
    (fun τ hτ ↦ lipschitzOn_Icc τ ⟨hτ.1, le_trans hτ.2 hST⟩)
  have htEnc₁ : t ∈ Icc ivp.initialTime enc₁.sol.terminalTime :=
    ⟨ht.1, le_trans ht.2 hS_enc₁⟩
  have htEnc₂ : t ∈ Icc ivp.initialTime enc₂.sol.terminalTime :=
    ⟨ht.1, le_trans ht.2 hS_enc₂⟩
  have htAmb₁ :
      t ∈ Icc ivp.initialTime
        (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp hcomm enc₁.sol).terminalTime := by
    simpa [BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule,
      BanachEvolutionLocalSolutionIn.mapContinuousLinearMapBetween] using htEnc₁
  have htAmb₂ :
      t ∈ Icc ivp.initialTime
        (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp hcomm enc₂.sol).terminalTime := by
    simpa [BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule,
      BanachEvolutionLocalSolutionIn.mapContinuousLinearMapBetween] using htEnc₂
  have hreal₁ :
      metricTensor (I := I) (M := M) enc₁.realization.metric t x u v =
        ((enc₁.sol.curve t :
          symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) x u v := by
    simpa [BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule,
      BanachEvolutionLocalSolutionIn.mapContinuousLinearMapBetween] using
      enc₁.realization.metric_eq_curve htAmb₁ x u v
  have hreal₂ :
      metricTensor (I := I) (M := M) enc₂.realization.metric t x u v =
        ((enc₂.sol.curve t :
          symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) x u v := by
    simpa [BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule,
      BanachEvolutionLocalSolutionIn.mapContinuousLinearMapBetween] using
      enc₂.realization.metric_eq_curve htAmb₂ x u v
  have hcurve :
      ((enc₁.sol.curve t :
        symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) x u v =
      ((enc₂.sol.curve t :
        symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) x u v := by
    exact congrArg
      (fun s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover =>
        ((s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover) x u v)) (hEq ht)
  calc
    metricTensor (I := I) (M := M) sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
        metricTensor (I := I) (M := M) enc₁.realization.metric t x u v := by
      simpa [IntrinsicDeTurckLocalSolution.restrictTerminal] using
        enc₁.metric_eq htCandidate₁ x u v
    _ =
        ((enc₁.sol.curve t :
          symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) x u v := hreal₁
    _ =
        ((enc₂.sol.curve t :
          symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) x u v := hcurve
    _ = metricTensor (I := I) (M := M) enc₂.realization.metric t x u v := hreal₂.symm
    _ = metricTensor (I := I) (M := M) sol₂.1.toIntrinsicDeTurckSolution.metric t x u v := by
      simpa [IntrinsicDeTurckLocalSolution.restrictTerminal] using
        (enc₂.metric_eq htCandidate₂ x u v).symm

/-- If chosen-background DeTurck metric uniqueness is available on every
prescribed shorter common terminal, then it is available on the open common
candidate overlap.  This is the order-theoretic continuation bridge from
restricted-terminal readouts to open-overlap readouts. -/
theorem chosenIntrinsicDeTurckLocalSolution_metric_eq_on_common_Ico_of_restricted_interval
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F] [T2Space M]
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp)
    (hmetric : ∀ {S : ℝ},
      ivp.initialTime < S → S ≤ sol₁.1.terminalTime → S ≤ sol₂.1.terminalTime →
      ∀ {t : ℝ}, t ∈ Icc ivp.initialTime S → ∀ (x : M) (u v : TangentSpace I x),
        metricTensor (I := I) (M := M)
          sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
            metricTensor (I := I) (M := M)
              sol₂.1.toIntrinsicDeTurckSolution.metric t x u v)
    {t : ℝ} (ht : t ∈ Ico ivp.initialTime
      (min sol₁.1.terminalTime sol₂.1.terminalTime))
    (x : M) (u v : TangentSpace I x) :
    metricTensor (I := I) (M := M) sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.1.toIntrinsicDeTurckSolution.metric t x u v := by
  rcases exists_between ht.2 with ⟨S, htS, hScommon⟩
  have hS₀ : ivp.initialTime < S := lt_of_le_of_lt ht.1 htS
  have hS₁ : S ≤ sol₁.1.terminalTime :=
    le_trans (le_of_lt hScommon) (min_le_left _ _)
  have hS₂ : S ≤ sol₂.1.terminalTime :=
    le_trans (le_of_lt hScommon) (min_le_right _ _)
  have htScc : t ∈ Icc ivp.initialTime S := ⟨ht.1, le_of_lt htS⟩
  exact hmetric (S := S) hS₀ hS₁ hS₂ (t := t) htScc x u v

/-- Connection-level open-overlap bridge from prescribed shorter-terminal
canonical-connection uniqueness. -/
theorem chosenIntrinsicDeTurckLocalSolution_connection_eq_on_common_Ico_of_restricted_interval
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F] [T2Space M]
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp)
    (hconnection : ∀ {S : ℝ},
      ivp.initialTime < S → S ≤ sol₁.1.terminalTime → S ≤ sol₂.1.terminalTime →
      ∀ {t : ℝ}, t ∈ Icc ivp.initialTime S →
      ∀ {x : M} {σ : Π y : M, TangentSpace I y},
        MDiffAt (T% σ) x →
        sol₁.1.canonicalConnection
          (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
          sol₂.1.canonicalConnection
            (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2) t σ x)
    {t : ℝ} (ht : t ∈ Ico ivp.initialTime
      (min sol₁.1.terminalTime sol₂.1.terminalTime))
    {x : M} {σ : Π y : M, TangentSpace I y} (hσ : MDiffAt (T% σ) x) :
    sol₁.1.canonicalConnection
      (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
      sol₂.1.canonicalConnection
        (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2) t σ x := by
  rcases exists_between ht.2 with ⟨S, htS, hScommon⟩
  have hS₀ : ivp.initialTime < S := lt_of_le_of_lt ht.1 htS
  have hS₁ : S ≤ sol₁.1.terminalTime :=
    le_trans (le_of_lt hScommon) (min_le_left _ _)
  have hS₂ : S ≤ sol₂.1.terminalTime :=
    le_trans (le_of_lt hScommon) (min_le_right _ _)
  have htScc : t ∈ Icc ivp.initialTime S := ⟨ht.1, le_of_lt htS⟩
  exact hconnection (S := S) hS₀ hS₁ hS₂ (t := t) htScc hσ

/-- Restrict an ambient candidate encoding to a shrunk interval chart when the encoded candidate
interval is known to fit inside the smaller chart interval. -/
def TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding.shrink
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {candidate : IntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp}
    (enc : TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
      (M := M) (F := F) (I := I) chart candidate)
    {T' : ℝ} (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
    {a' : ℝ≥0} (ha' : a' ≤ a)
    (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
      a' - (0 : ℝ≥0))
    (hterminal : enc.sol.terminalTime ≤ T') :
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
      (M := M) (F := F) (I := I)
      (chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha' htime)
      candidate where
  sol := by
    simpa [TimeDependentGeometricRicciDeTurckBanachChartOnIcc.shrink] using enc.sol
  terminal_le_chart := hterminal
  realization := by
    simpa [TimeDependentGeometricRicciDeTurckBanachChartOnIcc.shrink] using enc.realization
  terminal_eq := enc.terminal_eq
  metric_eq := enc.metric_eq

/-- An ambient interval candidate encoding canonically descends to the genuine symmetric-carrier
candidate encoding whenever the symmetric vector field agrees with the ambient chart vector field on
the Riemannian metric locus. -/
noncomputable def TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding.toSymmetricSubmoduleCandidateEncodingOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    {candidate : IntrinsicDeTurckLocalSolution (E := F) (H := H) (I := I) (M := M) ivp}
    (enc : TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding
      (M := M) (F := F) (I := I) chart candidate)
    (Asub : ℝ →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (hcomm : ∀ t x,
      x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
        (Asub t x :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) =
          chart.A t (x :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover)) :
    SymmetricSubmoduleCandidateEncodingOnIcc
      (T := T)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      Asub chart.A hcomm candidate := by
  let γ := enc.toSymmetricSectionSubmoduleCurve
    (M := M) (F := F) (I := I) (x0 := x0) (het := het)
  let solSub : BanachEvolutionLocalSolutionIn Asub
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) :=
    { terminalTime := enc.sol.terminalTime
      initial_lt_terminal := enc.sol.initial_lt_terminal
      curve := γ
      initial_eq := by
        simpa [γ] using
          enc.toSymmetricSectionSubmoduleCurve_initial_eq
            (M := M) (F := F) (I := I) (x0 := x0) (het := het)
      equation := by
        intro t ht
        simpa [γ] using
          enc.toSymmetricSectionSubmoduleCurve_equation
            (M := M) (F := F) (I := I) (x0 := x0) (het := het) Asub hcomm ht
      mem_state := by
        intro t ht
        simpa [γ] using
          enc.toSymmetricSectionSubmoduleCurve_mem_state
            (M := M) (F := F) (I := I) (x0 := x0) (het := het) ht }
  let ambSol :=
    BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
      (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp hcomm solSub
  refine
    { sol := solSub
      terminal_le_chart := ?_
      realization := ?_
      terminal_eq := ?_
      metric_eq := ?_ }
  · simpa [solSub] using enc.terminal_le_chart
  · exact
      { metric := enc.realization.metric
        metricVelocity := enc.realization.metricVelocity
        background := enc.realization.background
        metric_eq_curve := by
          intro t ht x u v
          have htEnc : t ∈ Icc ivp.initialTime enc.sol.terminalTime := by
            simpa [ambSol,
              BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule,
              BanachEvolutionLocalSolutionIn.mapContinuousLinearMapBetween, solSub] using ht
          have hcurve :
              ((solSub.curve t :
                symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
                ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
                  (V := _root_.Bundle.BilinearFormBundle
                    (V := (TangentSpace I : M → Type _)))
                  et Kc hKc Ko hKo hKoEq hcover) =
                enc.sol.curve t := by
            simpa [solSub, γ] using
              enc.coe_toSymmetricSectionSubmoduleCurve_of_mem
                (M := M) (F := F) (I := I) (x0 := x0) (het := het) htEnc
          calc
            metricTensor (I := I) (M := M) enc.realization.metric t x u v =
                enc.sol.curve t x u v :=
              enc.realization.metric_eq_curve htEnc x u v
            _ =
                ((solSub.curve t :
                  symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
                  ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
                    (V := _root_.Bundle.BilinearFormBundle
                      (V := (TangentSpace I : M → Type _)))
                    et Kc hKc Ko hKo hKoEq hcover) x u v := by
              rw [hcurve]
            _ = ambSol.curve t x u v := by
              rfl
        hasTimeDerivative := by
          simpa [ambSol,
            BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule,
            BanachEvolutionLocalSolutionIn.mapContinuousLinearMapBetween, solSub] using
            enc.realization.hasTimeDerivative
        equation := by
          intro t ht
          have htEnc : t ∈ Icc ivp.initialTime enc.sol.terminalTime := by
            simpa [ambSol,
              BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule,
              BanachEvolutionLocalSolutionIn.mapContinuousLinearMapBetween, solSub] using ht
          exact enc.realization.equation htEnc }
  · simpa [solSub] using enc.terminal_eq
  · intro t ht x u v
    simpa using enc.metric_eq ht x u v

/-- The initial smooth Riemannian metric has a positive closed ball contained in the genuine
symmetric-carrier metric locus. This is the local-radius input used to shrink Banach/Picard
arguments to the actual Riemannian-metric carrier rather than the whole symmetric submodule. -/
theorem InitialValueProblem.exists_closedBall_toSymmetricSectionSubmodule_subset_riemannianMetricLocusSubmodule
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)) :
    ∃ ε : ℝ, 0 < ε ∧
      Metric.closedBall
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) ε ⊆
        riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover := by
  let g₀ := InitialValueProblem.toSymmetricSectionSubmodule
    (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp
  have hopen : IsOpen (riemannianMetricLocusSubmodule (M := M) (F := F)
      (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) :=
    isOpen_riemannianMetricLocusSubmodule
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      x0 et het Kc hKc Ko hKo hKoEq hcover
  have hg₀ : g₀ ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
      (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover := by
    exact InitialValueProblem.toSymmetricSectionSubmodule_mem_riemannianMetricLocusSubmodule
      (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp
  rcases (Metric.isOpen_iff.1 hopen) g₀ hg₀ with ⟨ε, hεpos, hball⟩
  refine ⟨ε / 2, by positivity, ?_⟩
  exact (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε)).trans hball

/-- NNReal-radius version of the local metric-cone radius: any positive analytic Picard radius can
be shrunk to a positive radius whose closed ball lies in the Riemannian-metric submodule locus. -/
theorem InitialValueProblem.exists_pos_nnreal_le_closedBall_toSymmetricSectionSubmodule_subset_riemannianMetricLocusSubmodule
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
    {a : ℝ≥0} (ha : 0 < a) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ a ∧
      Metric.closedBall
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (ρ : ℝ) ⊆
        riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover := by
  rcases InitialValueProblem.exists_closedBall_toSymmetricSectionSubmodule_subset_riemannianMetricLocusSubmodule
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover ivp with
    ⟨ε, hεpos, hεball⟩
  let εnn : ℝ≥0 := ⟨ε / 2, le_of_lt (half_pos hεpos)⟩
  let ρ : ℝ≥0 := min (a / 2) εnn
  have hρpos : 0 < ρ := by
    dsimp [ρ, εnn]
    exact lt_min (by positivity) (by exact_mod_cast half_pos hεpos)
  have hρle_a : ρ ≤ a := by
    have hhalf : a / 2 ≤ a := by
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_right' (by norm_num : ((2 : ℝ≥0)⁻¹ ≤ 1))
    exact le_trans (min_le_left _ _) hhalf
  have hρle_ε : (ρ : ℝ) ≤ ε := by
    have hρle_εnn : ρ ≤ εnn := min_le_right _ _
    have hρle_half : (ρ : ℝ) ≤ ε / 2 := by
      exact_mod_cast hρle_εnn
    linarith
  refine ⟨ρ, hρpos, hρle_a, ?_⟩
  exact (Metric.closedBall_subset_closedBall hρle_ε).trans hεball

/-- Positive shrinking parameters for the symmetric-carrier route. Starting from any interval
Ricci-DeTurck chart with positive Picard radius, one can shrink to a positive terminal time and a
positive radius whose Picard closed ball is contained in the Riemannian metric cone and whose time
length satisfies the Picard-Lindelöf radius constraint. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrink_parameters
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0),
      ∃ hT' : ivp.initialTime < T',
        T' ≤ T ∧ 0 < a' ∧ a' ≤ a ∧
          L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
            a' - (0 : ℝ≥0) ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F)
              (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover := by
  rcases InitialValueProblem.exists_pos_nnreal_le_closedBall_toSymmetricSectionSubmodule_subset_riemannianMetricLocusSubmodule
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover ivp ha with
    ⟨ρ, hρpos, hρle, hρball⟩
  let δ : ℝ := min ((T - ivp.initialTime) / 2)
    ((ρ : ℝ) / (2 * ((L : ℝ) + 1)))
  have hTgap : 0 < T - ivp.initialTime := sub_pos.mpr chart.hT
  have hρrealpos : 0 < (ρ : ℝ) := by exact_mod_cast hρpos
  have hdenpos : 0 < 2 * ((L : ℝ) + 1) := by positivity
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min (half_pos hTgap) (div_pos hρrealpos hdenpos)
  have hδle_time : δ ≤ (T - ivp.initialTime) / 2 := by
    dsimp [δ]
    exact min_le_left _ _
  have hδle_radius : δ ≤ (ρ : ℝ) / (2 * ((L : ℝ) + 1)) := by
    dsimp [δ]
    exact min_le_right _ _
  refine ⟨ivp.initialTime + δ, ρ, by linarith, ?_, hρpos, hρle, ?_, hρball⟩
  · linarith
  · have hLnonneg : 0 ≤ (L : ℝ) := by positivity
    have hρnonneg : 0 ≤ (ρ : ℝ) := le_of_lt hρrealpos
    have hcoef : (L : ℝ) / (2 * ((L : ℝ) + 1)) ≤ 1 := by
      rw [div_le_iff₀ hdenpos]
      nlinarith [hLnonneg]
    have hmul_radius : (L : ℝ) * δ ≤ (ρ : ℝ) := by
      calc
        (L : ℝ) * δ ≤ (L : ℝ) * ((ρ : ℝ) / (2 * ((L : ℝ) + 1))) := by
          gcongr
        _ = (ρ : ℝ) * ((L : ℝ) / (2 * ((L : ℝ) + 1))) := by ring
        _ ≤ (ρ : ℝ) * 1 := by
          gcongr
        _ = (ρ : ℝ) := by ring
    have hmax :
        max (ivp.initialTime + δ - ivp.initialTime)
            (ivp.initialTime - ivp.initialTime) = δ := by
      rw [sub_self, max_eq_left]
      · ring
      · linarith
    have hmaxδ : max δ 0 = δ := max_eq_left (le_of_lt hδpos)
    simpa [hmax, hmaxδ] using hmul_radius

/-- A positive-radius interval Ricci-DeTurck chart can be shrunk to an actual chart whose
chart-derived symmetric vector field satisfies Picard-Lindelöf on a closed ball lying in the
Riemannian-metric cone.  Thus the symmetric-carrier Picard obligation is derivable after the
standard local cone/time-radius shrink. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_restrictedSymmetricA_picard
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (hT' : ivp.initialTime < T'),
      ∃ chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        T' ≤ T ∧ 0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F)
              (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover ∧
          IsPicardLindelof
            (chart'.restrictedSymmetricA
              (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
            (tmin := ivp.initialTime) (tmax := T')
            ⟨ivp.initialTime, ⟨le_rfl, le_of_lt chart'.hT⟩⟩
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a' 0 L Kpic := by
  rcases chart.exists_metricCone_shrink_parameters
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover ha with
    ⟨T', a', hT', hT'le, ha'pos, ha'le, htime, hball⟩
  let chart' := chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha'le htime
  have hpicard := chart.shrink_restrictedSymmetricA_picard_of_closedBall_subset_riemannianMetricLocus
    (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover
    hT' hT'le ha'le htime hball
  refine ⟨T', a', hT', chart', hT'le, ha'pos, ha'le, hball, ?_⟩
  simpa [chart'] using hpicard

/-- A positive-radius interval Ricci-DeTurck chart can be shrunk so that the direct
specific-RHS symmetric carrier satisfies Picard-Lindelöf on a closed ball in the metric cone.  This
is the shrink step for the non-existential RHS route: tangency is supplied by
`SmoothSectionRHSIdentification` on smooth metric slices, not by the chart-level `geometric` field. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_restrictedSymmetricA_picard
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover chart.A)
    (hspatial : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
        (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x
          ((s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) x)))
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (hT' : ivp.initialTime < T'),
      ∃ chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        T' ≤ T ∧ 0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F)
              (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover ∧
          IsPicardLindelof
            (SmoothSectionRHSIdentification.restrictedSymmetricA
              (M := M) (F := F) (I := I)
              x0 et het Kc hKc Ko hKo hKoEq hcover rhs hspatial)
            (tmin := ivp.initialTime) (tmax := T')
            ⟨ivp.initialTime, ⟨le_rfl, le_of_lt chart'.hT⟩⟩
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a' 0 L Kpic := by
  rcases chart.exists_metricCone_shrink_parameters
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover ha with
    ⟨T', a', hT', hT'le, ha'pos, ha'le, htime, hball⟩
  let chart' := chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha'le htime
  have hpicardAmb : IsPicardLindelof chart.A
      (tmin := ivp.initialTime) (tmax := T')
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT'⟩⟩
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)
      a' 0 L Kpic := by
    simpa [chart', TimeDependentGeometricRicciDeTurckBanachChartOnIcc.shrink] using
      chart'.picard
  have hpicard :=
    SmoothSectionRHSIdentification.restrictedSymmetricA_picard_of_closedBall_subset_riemannianMetricLocus
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover rhs hspatial hT' hpicardAmb hball
  refine ⟨T', a', hT', chart', hT'le, ha'pos, ha'le, hball, ?_⟩
  simpa [chart'] using hpicard

/-- A positive-radius interval Ricci-DeTurck chart can be shrunk so that the density-based direct
specific-RHS symmetric carrier satisfies Picard-Lindelöf on a closed ball in the metric cone.  This
is the shrink step that replaces the over-strong assumption that all metric-locus states are
spatially smooth by density of smooth SPD slices. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_closure_restrictedSymmetricA_picard
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover chart.A)
    (hclosure : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) ∈ closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover |
              u ∈ symmetricPositiveDefiniteLocus
                (M := M) (F := F) (W := (TangentSpace I : M → Type _))
                et Kc hKc Ko hKo hKoEq hcover ∧
              ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
                (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}))
    (hGlobalLip : ∀ t, ∃ Kglobal : ℝ≥0, LipschitzOnWith Kglobal (chart.A t)
      (positiveDefiniteLocus
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover))
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (hT' : ivp.initialTime < T'),
      ∃ chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        T' ≤ T ∧ 0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F)
              (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover ∧
          IsPicardLindelof
            (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd
              (M := M) (F := F) (I := I)
              x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hGlobalLip)
            (tmin := ivp.initialTime) (tmax := T')
            ⟨ivp.initialTime, ⟨le_rfl, le_of_lt chart'.hT⟩⟩
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a' 0 L Kpic := by
  rcases chart.exists_metricCone_shrink_parameters
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover ha with
    ⟨T', a', hT', hT'le, ha'pos, ha'le, htime, hball⟩
  let chart' := chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha'le htime
  have hpicardAmb : IsPicardLindelof chart.A
      (tmin := ivp.initialTime) (tmax := T')
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT'⟩⟩
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)
      a' 0 L Kpic := by
    simpa [chart', TimeDependentGeometricRicciDeTurckBanachChartOnIcc.shrink] using
      chart'.picard
  have hpicard :=
    SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_picard_of_closedBall_subset_riemannianMetricLocus
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hGlobalLip hT' hpicardAmb hball
  refine ⟨T', a', hT', chart', hT'le, ha'pos, ha'le, hball, ?_⟩
  simpa [chart'] using hpicard

/-- A positive-radius interval Ricci-DeTurck chart can be shrunk so that the density-based direct
specific-RHS symmetric carrier satisfies Picard-Lindelöf, with the metric-locus closure produced
from arbitrary smooth approximants.  Fiberwise symmetrization is used internally, so the density
input no longer needs to preselect symmetric approximating sections. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_unsymmetricApprox_restrictedSymmetricA_picard
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover chart.A)
    (happrox : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      ∀ ε > 0,
        ∃ u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover,
          ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
            (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x)) ∧
          dist (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) u < ε)
    (hGlobalLip : ∀ t, ∃ Kglobal : ℝ≥0, LipschitzOnWith Kglobal (chart.A t)
      (positiveDefiniteLocus
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover))
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (hT' : ivp.initialTime < T'),
      ∃ chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        T' ≤ T ∧ 0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F)
              (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover ∧
          IsPicardLindelof
            (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd
              (M := M) (F := F) (I := I)
              x0 et het Kc hKc Ko hKo hKoEq hcover rhs
              (SmoothSectionRHSIdentification.closure_smooth_spd_of_metric_locus_and_forall_dist_lt_unsymmetric
                x0 et het Kc hKc Ko hKo hKoEq hcover happrox)
              hGlobalLip)
            (tmin := ivp.initialTime) (tmax := T')
            ⟨ivp.initialTime, ⟨le_rfl, le_of_lt chart'.hT⟩⟩
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a' 0 L Kpic := by
  exact chart.exists_metricCone_shrunk_specificRHS_closure_restrictedSymmetricA_picard
    (M := M) (F := F) (I := I)
    x0 et het Kc hKc Ko hKo hKoEq hcover rhs
    (SmoothSectionRHSIdentification.closure_smooth_spd_of_metric_locus_and_forall_dist_lt_unsymmetric
      x0 et het Kc hKc Ko hKo hKoEq hcover happrox)
    hGlobalLip ha
/-- A positive-radius interval Ricci-DeTurck chart can be shrunk so that the interval-scoped
density-based direct specific-RHS symmetric carrier satisfies Picard-Lindelöf on a closed ball in the
metric cone.  Unlike the global carrier, this route consumes only the chart's interval Lipschitz
estimate. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_closure_restrictedSymmetricA_on_Icc_picard
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover chart.A)
    (hclosure : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) ∈ closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover |
              u ∈ symmetricPositiveDefiniteLocus
                (M := M) (F := F) (W := (TangentSpace I : M → Type _))
                et Kc hKc Ko hKo hKoEq hcover ∧
              ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
                (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}))
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (hT' : ivp.initialTime < T') (hT'le : T' ≤ T),
      ∃ _chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F)
              (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover ∧
          IsPicardLindelof
            (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc
              (M := M) (F := F) (I := I)
              x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
              (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩))
            (tmin := ivp.initialTime) (tmax := T')
            ⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT'⟩⟩
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a' 0 L Kpic := by
  rcases chart.exists_metricCone_shrink_parameters
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover ha with
    ⟨T', a', hT', hT'le, ha'pos, ha'le, htime, hball⟩
  let chart' := chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha'le htime
  have hpicardAmb : IsPicardLindelof chart.A
      (tmin := ivp.initialTime) (tmax := T')
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT'⟩⟩
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)
      a' 0 L Kpic := by
    simpa [chart', TimeDependentGeometricRicciDeTurckBanachChartOnIcc.shrink] using
      chart'.picard
  have hpicard :=
    SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc_picard_of_closedBall_subset_riemannianMetricLocus
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hT'
      hpicardAmb (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩) hball
  refine ⟨T', a', hT', hT'le, chart', ha'pos, ha'le, hball, ?_⟩
  simpa [chart'] using hpicard
/-- A positive-radius interval Ricci-DeTurck chart can be shrunk so that the interval-scoped
density-based direct specific-RHS symmetric carrier satisfies Picard-Lindelöf, with the metric-locus
closure produced from arbitrary smooth approximants.  This is the interval-local analogue of the
unsymmetric smooth-approximation route and does not require any global-in-time Lipschitz witness. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_unsymmetricApprox_restrictedSymmetricA_on_Icc_picard
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover chart.A)
    (happrox : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      ∀ ε > 0,
        ∃ u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
          (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
          et Kc hKc Ko hKo hKoEq hcover,
          ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
            (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x)) ∧
          dist (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) u < ε)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (hT' : ivp.initialTime < T') (hT'le : T' ≤ T),
      ∃ _chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F)
              (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover ∧
          IsPicardLindelof
            (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc
              (M := M) (F := F) (I := I)
              x0 et het Kc hKc Ko hKo hKoEq hcover rhs
              (SmoothSectionRHSIdentification.closure_smooth_spd_of_metric_locus_and_forall_dist_lt_unsymmetric
                x0 et het Kc hKc Ko hKo hKoEq hcover happrox)
              (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩))
            (tmin := ivp.initialTime) (tmax := T')
            ⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT'⟩⟩
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a' 0 L Kpic := by
  exact chart.exists_metricCone_shrunk_specificRHS_closure_restrictedSymmetricA_on_Icc_picard
    (M := M) (F := F) (I := I)
    x0 et het Kc hKc Ko hKo hKoEq hcover rhs
    (SmoothSectionRHSIdentification.closure_smooth_spd_of_metric_locus_and_forall_dist_lt_unsymmetric
      x0 et het Kc hKc Ko hKo hKoEq hcover happrox)
    ha

/-- Chosen-background point-4 package from a Ricci-DeTurck chart whose Picard theorem and uniqueness
are proved on the genuine symmetric Riemannian-metric Banach carrier.  This route avoids requiring a
Picard theorem on the larger ambient nonsymmetric section space; the ambient chart only appears after
the symmetric solution is mapped through the submodule inclusion for smooth realization. -/
theorem chosenIntrinsicDeTurckLocalExistenceUniqueness_of_symmetricSubmodulePicard_smoothRealization_and_candidateEncodingOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (Asub : ℝ →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)
    (hcomm : ∀ t x,
      x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
        (Asub t x :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) =
          A t (x :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover))
    (hT : ivp.initialTime < T)
    (picard : IsPicardLindelof Asub (tmin := ivp.initialTime) (tmax := T)
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT⟩⟩
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a 0 L Kpic)
    (lipschitzOn_Icc : ∀ t ∈ Icc ivp.initialTime T, LipschitzOnWith Kstate (Asub t)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover))
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn Asub
        (riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp
        (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp hcomm sol))
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn Asub
        (riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol)))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      SymmetricSubmoduleCandidateEncodingOnIcc
        (T := T)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        Asub A hcomm candidate.1) :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := F) (H := H) (I := I) (M := M) ivp := by
  refine ⟨?_, ?_⟩
  · rcases exists_unique_in_riemannianMetricLocusSubmodule_of_isPicardLindelof_lipschitzOn_Icc_terminal_le
      (M := M) (F := F) (W := (TangentSpace I : M → Type _))
      x0 et het Kc hKc Ko hKo hKoEq hcover inferInstance hT picard
      (InitialValueProblem.toSymmetricSectionSubmodule_mem_riemannianMetricLocusSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)
      lipschitzOn_Icc with ⟨sol, _hsolT, _huniq⟩
    exact ⟨⟨
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
        (M := M) (F := F) (I := I) (realize sol),
      hchosen sol⟩⟩
  · intro sol₁ sol₂ t ht x u v
    let enc₁ := encode sol₁
    let enc₂ := encode sol₂
    have ht₁ : t ∈ Icc ivp.initialTime sol₁.1.terminalTime :=
      ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
    have ht₂ : t ∈ Icc ivp.initialTime sol₂.1.terminalTime :=
      ⟨ht.1, le_trans ht.2 (min_le_right _ _)⟩
    have htSub : t ∈ Icc ivp.initialTime (min enc₁.sol.terminalTime enc₂.sol.terminalTime) := by
      refine ⟨ht.1, ?_⟩
      simpa [enc₁.terminal_eq, enc₂.terminal_eq] using ht.2
    have hLipCommon :
        ∀ τ ∈ Icc ivp.initialTime (min enc₁.sol.terminalTime enc₂.sol.terminalTime),
          LipschitzOnWith Kstate (Asub τ)
            (riemannianMetricLocusSubmodule (M := M) (F := F)
              (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover) := by
      intro τ hτ
      exact lipschitzOn_Icc τ
        ⟨hτ.1, le_trans hτ.2 (le_trans (min_le_left _ _) enc₁.terminal_le_chart)⟩
    have hEq := BanachEvolutionLocalSolutionIn.eqOn_Icc_of_lipschitzOn_Icc
      (F := Asub)
      (stateSet := riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
      (t₀ := ivp.initialTime)
      (u₀ := InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)
      (K := Kstate) enc₁.sol enc₂.sol hLipCommon
    have htSub₁ : t ∈ Icc ivp.initialTime enc₁.sol.terminalTime :=
      ⟨htSub.1, le_trans htSub.2 (min_le_left _ _)⟩
    have htSub₂ : t ∈ Icc ivp.initialTime enc₂.sol.terminalTime :=
      ⟨htSub.1, le_trans htSub.2 (min_le_right _ _)⟩
    have htAmb₁ :
        t ∈ Icc ivp.initialTime
          (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp hcomm enc₁.sol).terminalTime := by
      simpa [BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule,
        BanachEvolutionLocalSolutionIn.mapContinuousLinearMapBetween] using htSub₁
    have htAmb₂ :
        t ∈ Icc ivp.initialTime
          (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp hcomm enc₂.sol).terminalTime := by
      simpa [BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule,
        BanachEvolutionLocalSolutionIn.mapContinuousLinearMapBetween] using htSub₂
    have hreal₁ :
        metricTensor (I := I) (M := M) enc₁.realization.metric t x u v =
          ((enc₁.sol.curve t :
            symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) x u v := by
      simpa [BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule,
        BanachEvolutionLocalSolutionIn.mapContinuousLinearMapBetween] using
          (enc₁.realization.metric_eq_curve htAmb₁ x u v)
    have hreal₂ :
        metricTensor (I := I) (M := M) enc₂.realization.metric t x u v =
          ((enc₂.sol.curve t :
            symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) x u v := by
      simpa [BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule,
        BanachEvolutionLocalSolutionIn.mapContinuousLinearMapBetween] using
          (enc₂.realization.metric_eq_curve htAmb₂ x u v)
    have hcurve :
        ((enc₁.sol.curve t :
          symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) x u v =
        ((enc₂.sol.curve t :
          symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) x u v := by
      exact congrArg
        (fun s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover =>
          ((s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) x u v)) (hEq htSub)
    calc
      metricTensor (I := I) (M := M) sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
          metricTensor (I := I) (M := M) enc₁.realization.metric t x u v :=
        enc₁.metric_eq ht₁ x u v
      _ =
          ((enc₁.sol.curve t :
            symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) x u v := hreal₁
      _ =
          ((enc₂.sol.curve t :
            symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover) :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover) x u v := hcurve
      _ = metricTensor (I := I) (M := M) enc₂.realization.metric t x u v := hreal₂.symm
      _ = metricTensor (I := I) (M := M) sol₂.1.toIntrinsicDeTurckSolution.metric t x u v :=
        (enc₂.metric_eq ht₂ x u v).symm

/-- Intrinsic Ricci-flow point-4 package from the symmetric-carrier Ricci-DeTurck route and the
chosen-background identity `C^3` gauge. -/
noncomputable def intrinsicLocalExistenceUniqueness_of_symmetricSubmodulePicard_smoothRealization_and_candidateEncodingOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (Asub : ℝ →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover →
      symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover)
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)
    (hcomm : ∀ t x,
      x ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
        (Asub t x :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) =
          A t (x :
            ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
              (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
              et Kc hKc Ko hKo hKoEq hcover))
    (hT : ivp.initialTime < T)
    (picard : IsPicardLindelof Asub (tmin := ivp.initialTime) (tmax := T)
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT⟩⟩
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a 0 L Kpic)
    (lipschitzOn_Icc : ∀ t ∈ Icc ivp.initialTime T, LipschitzOnWith Kstate (Asub t)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover))
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn Asub
        (riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp
        (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp hcomm sol))
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn Asub
        (riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol)))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      SymmetricSubmoduleCandidateEncodingOnIcc
        (T := T)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        Asub A hcomm candidate.1) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  (chosenIntrinsicDeTurckLocalExistenceUniqueness_of_symmetricSubmodulePicard_smoothRealization_and_candidateEncodingOnIcc
    (M := M) (F := F) (I := I)
    x0 et het Kc hKc Ko hKo hKoEq hcover ivp Asub A hcomm hT picard
    lipschitzOn_Icc realize hchosen encode).toIntrinsic_viaIdentityDiffeomorph3Gauge

/-- Intrinsic Ricci-flow point-4 package from the concrete specific-RHS symmetric-carrier route.
The symmetric carrier, its Picard-Lindelöf data, and its Lipschitz control are all derived from the
ambient finite-cover vector field using `SmoothSectionRHSIdentification`; the remaining inputs are
the genuinely analytic smooth-realization and reverse-encoding results for that carrier. -/
noncomputable def intrinsicLocalExistenceUniqueness_of_specificRHS_symmetricSubmodulePicard_smoothRealization_and_candidateEncodingOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover A)
    (hspatial : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
        (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x
          ((s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) x)))
    (hT : ivp.initialTime < T)
    (picard : IsPicardLindelof A (tmin := ivp.initialTime) (tmax := T)
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT⟩⟩
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)
      a 0 L Kpic)
    (lipschitzOn_Icc : ∀ t ∈ Icc ivp.initialTime T, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover))
    (hball : Metric.closedBall
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a ⊆
      riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn
        (SmoothSectionRHSIdentification.restrictedSymmetricA
          (M := M) (F := F) (I := I)
          x0 et het Kc hKc Ko hKo hKoEq hcover rhs hspatial)
        (riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp
        (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp
          (SmoothSectionRHSIdentification.restrictedSymmetricA_coe_of_mem
            (M := M) (F := F) (I := I)
            x0 et het Kc hKc Ko hKo hKoEq hcover rhs hspatial) sol))
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn
        (SmoothSectionRHSIdentification.restrictedSymmetricA
          (M := M) (F := F) (I := I)
          x0 et het Kc hKc Ko hKo hKoEq hcover rhs hspatial)
        (riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol)))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      SymmetricSubmoduleCandidateEncodingOnIcc
        (T := T)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        (SmoothSectionRHSIdentification.restrictedSymmetricA
          (M := M) (F := F) (I := I)
          x0 et het Kc hKc Ko hKo hKoEq hcover rhs hspatial)
        A
        (SmoothSectionRHSIdentification.restrictedSymmetricA_coe_of_mem
          (M := M) (F := F) (I := I)
          x0 et het Kc hKc Ko hKo hKoEq hcover rhs hspatial)
        candidate.1) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  exact intrinsicLocalExistenceUniqueness_of_symmetricSubmodulePicard_smoothRealization_and_candidateEncodingOnIcc
    (M := M) (F := F) (I := I)
    x0 et het Kc hKc Ko hKo hKoEq hcover ivp
    (SmoothSectionRHSIdentification.restrictedSymmetricA
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover rhs hspatial)
    A
    (SmoothSectionRHSIdentification.restrictedSymmetricA_coe_of_mem
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover rhs hspatial)
    hT
    (SmoothSectionRHSIdentification.restrictedSymmetricA_picard_of_closedBall_subset_riemannianMetricLocus
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover rhs hspatial hT picard hball)
    (SmoothSectionRHSIdentification.restrictedSymmetricA_lipschitzOn_Icc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover rhs hspatial lipschitzOn_Icc)
    realize hchosen encode

/-- Intrinsic Ricci-flow point-4 package from the density-based concrete specific-RHS symmetric
carrier route.  This is the version of the direct specific-RHS theorem whose tangency hypothesis is
density of smooth symmetric positive-definite slices plus Lipschitz extension, rather than spatial
smoothness of every Banach metric-locus state. -/
noncomputable def intrinsicLocalExistenceUniqueness_of_specificRHS_closure_symmetricSubmodulePicard_smoothRealization_and_candidateEncodingOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M))
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover A)
    (hclosure : ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover →
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover) ∈ closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover |
              u ∈ symmetricPositiveDefiniteLocus
                (M := M) (F := F) (W := (TangentSpace I : M → Type _))
                et Kc hKc Ko hKo hKoEq hcover ∧
              ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
                (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}))
    (hGlobalLip : ∀ t, ∃ Kglobal : ℝ≥0, LipschitzOnWith Kglobal (A t)
      (positiveDefiniteLocus
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover))
    (hT : ivp.initialTime < T)
    (picard : IsPicardLindelof A (tmin := ivp.initialTime) (tmax := T)
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT⟩⟩
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)
      a 0 L Kpic)
    (lipschitzOn_Icc : ∀ t ∈ Icc ivp.initialTime T, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover))
    (hball : Metric.closedBall
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a ⊆
      riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
    (realize : ∀ sol : BanachEvolutionLocalSolutionIn
        (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd
          (M := M) (F := F) (I := I)
          x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hGlobalLip)
        (riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
      BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp
        (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp
          (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_coe_of_mem
            (M := M) (F := F) (I := I)
            x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hGlobalLip) sol))
    (hchosen : ∀ sol : BanachEvolutionLocalSolutionIn
        (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd
          (M := M) (F := F) (I := I)
          x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hGlobalLip)
        (riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
      UsesChosenBackground (I := I) (M := M)
        (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
          (M := M) (F := F) (I := I) (realize sol)))
    (encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      SymmetricSubmoduleCandidateEncodingOnIcc
        (T := T)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd
          (M := M) (F := F) (I := I)
          x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hGlobalLip)
        A
        (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_coe_of_mem
          (M := M) (F := F) (I := I)
          x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hGlobalLip)
        candidate.1) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp := by
  exact intrinsicLocalExistenceUniqueness_of_symmetricSubmodulePicard_smoothRealization_and_candidateEncodingOnIcc
    (M := M) (F := F) (I := I)
    x0 et het Kc hKc Ko hKo hKoEq hcover ivp
    (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hGlobalLip)
    A
    (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_coe_of_mem
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hGlobalLip)
    hT
    (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_picard_of_closedBall_subset_riemannianMetricLocus
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hGlobalLip hT picard hball)
    (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_lipschitzOn_Icc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hGlobalLip lipschitzOn_Icc)
    realize hchosen encode

/-- Interval chart closure data for the genuine symmetric carrier, with the symmetric vector field
derived from the ambient Ricci-DeTurck chart.  This packages the remaining proof obligations after
the geometric RHS has shown that the chart vector field is tangent to symmetric bilinear forms. -/
structure SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate) where
  /-- Picard-Lindelof data for the chart-derived symmetric-carrier vector field. -/
  picard : IsPicardLindelof
    (chart.restrictedSymmetricA
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
    (tmin := ivp.initialTime) (tmax := T)
    ⟨ivp.initialTime, ⟨le_rfl, le_of_lt chart.hT⟩⟩
    (InitialValueProblem.toSymmetricSectionSubmodule
      (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a 0 L Kpic
  /-- Smooth realization of every symmetric-carrier solution after including it into the ambient
  section-space chart. -/
  realization : ∀ sol : BanachEvolutionLocalSolutionIn
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
    BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp
      (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp
        (chart.restrictedSymmetricA_coe_of_mem
          (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) sol)
  /-- The realized solutions use the chosen Levi-Civita background. -/
  usesChosenBackground : ∀ sol : BanachEvolutionLocalSolutionIn
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
    UsesChosenBackground (I := I) (M := M)
      (BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.toIntrinsicDeTurckLocalSolution
        (M := M) (F := F) (I := I) (realization sol))
  /-- Reverse encoding for arbitrary chosen-background candidates, now into the chart-derived
  symmetric carrier. -/
  encode : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp,
    SymmetricSubmoduleCandidateEncodingOnIcc
      (T := T)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      chart.A
      (chart.restrictedSymmetricA_coe_of_mem
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      candidate.1

/-- Build chart-derived symmetric-carrier closure data from existing ambient interval closure data.
The ambient closure already realizes the included symmetric solution smoothly; the extra remaining
datum is Picard-Lindelof on the restricted carrier; reverse encoding is derived from the ambient
candidate encoding by descending to the symmetric metric submodule. -/
def SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.ofRicciDeTurckChartClosureDataOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (picard : IsPicardLindelof
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (tmin := ivp.initialTime) (tmax := T)
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt chart.hT⟩⟩
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a 0 L Kpic) :
    SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart where
  picard := picard
  realization := fun sol =>
    (D.realization
      (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp
        (chart.restrictedSymmetricA_coe_of_mem
          (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) sol)).toSmoothIntrinsicDeTurckRealization
  usesChosenBackground := fun sol => by
    simpa using
      (D.realization
        (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp
          (chart.restrictedSymmetricA_coe_of_mem
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) sol)).usesChosenBackground
  encode := fun candidate =>
    (D.encode candidate).toSymmetricSubmoduleCandidateEncodingOnIcc
      (M := M) (F := F) (I := I) (x0 := x0) (het := het)
      (chart.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (chart.restrictedSymmetricA_coe_of_mem
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)

/-- Shrunk-chart variant of
`SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.ofRicciDeTurckChartClosureDataOnIcc`.
The ambient closure data still supplies smooth realization after inclusion, the symmetric carrier
Picard-Lindelöf proof is derived from the shrunk ambient chart and the closed-ball containment in the
Riemannian metric cone, and reverse encoding is derived from the ambient encoding once the candidate
interval is known to fit inside the shrunken chart. -/
def SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.ofShrunkRicciDeTurckChartClosureDataOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    {T' : ℝ} (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
    {a' : ℝ≥0} (ha' : a' ≤ a)
    (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
      a' - (0 : ℝ≥0))
    (hball : Metric.closedBall
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
      riemannianMetricLocusSubmodule (M := M) (F := F)
        (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover)
    (hencode_terminal : ∀ candidate : ChosenIntrinsicDeTurckLocalSolution
        (E := F) (H := H) (I := I) (M := M) ivp,
      (D.encode candidate).sol.terminalTime ≤ T') :
    let chart' := chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha' htime
    SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart' := by
  let chart' := chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha' htime
  refine
    { picard := ?_
      realization := ?_
      usesChosenBackground := ?_
      encode := ?_ }
  · simpa [chart'] using
      chart.shrink_restrictedSymmetricA_picard_of_closedBall_subset_riemannianMetricLocus
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover
        hT' hT'le ha' htime hball
  · intro sol
    exact
      (D.realization
        (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp
          (chart'.restrictedSymmetricA_coe_of_mem
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) sol)).toSmoothIntrinsicDeTurckRealization
  · intro sol
    simpa [chart'] using
      (D.realization
        (BanachEvolutionLocalSolutionIn.toAmbientContinuousSectionSpace_of_riemannianMetricLocusSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp
          (chart'.restrictedSymmetricA_coe_of_mem
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) sol)).usesChosenBackground
  · intro candidate
    let enc' := (D.encode candidate).shrink
      (M := M) (F := F) (I := I) (x0 := x0) (het := het)
      hT' hT'le ha' htime (hencode_terminal candidate)
    simpa [chart', enc'] using
      enc'.toSymmetricSubmoduleCandidateEncodingOnIcc
        (M := M) (F := F) (I := I) (x0 := x0) (het := het)
        (chart'.restrictedSymmetricA
          (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
        (chart'.restrictedSymmetricA_coe_of_mem
          (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)

/-- Local uniqueness readout from shrunk ambient closure data without requiring the full candidate
intervals to fit in the shrink.  For any common shorter terminal time `S ≤ T'`, the ambient closure
encodes the two restricted chosen-background candidates, shrinks those encodings, descends them to
the symmetric carrier, and applies the localized symmetric-carrier uniqueness theorem on
`[t₀, S]`. -/
theorem RicciDeTurckChartClosureDataOnIcc.metric_eq_on_restricted_interval_of_shrunk_symmetricCarrier
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    {T' : ℝ} (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
    {a' : ℝ≥0} (ha' : a' ≤ a)
    (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
      a' - (0 : ℝ≥0))
    (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp)
    {S : ℝ} (hS₀ : ivp.initialTime < S)
    (hS₁ : S ≤ sol₁.1.terminalTime) (hS₂ : S ≤ sol₂.1.terminalTime) (hST' : S ≤ T')
    {t : ℝ} (ht : t ∈ Icc ivp.initialTime S)
    (x : M) (u v : TangentSpace I x) :
    metricTensor (I := I) (M := M) sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.1.toIntrinsicDeTurckSolution.metric t x u v := by
  let chart' := chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha' htime
  refine
    chosenIntrinsicDeTurckLocalSolution_metric_eq_on_restricted_interval_of_symmetricSubmoduleCandidateEncodingOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover ivp
      (chart'.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      chart'.A
      (chart'.restrictedSymmetricA_coe_of_mem
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (chart'.restrictedSymmetricA_lipschitzOn_Icc
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      ?_ sol₁ sol₂ hS₀ hS₁ hS₂ hST' ht x u v
  intro candidate S hS₀ hScandidate hSchart
  let candidateS := candidate.restrictTerminal hS₀ hScandidate
  let enc := D.encode candidateS
  have hterminal : enc.sol.terminalTime ≤ T' := by
    simpa [candidateS, ChosenIntrinsicDeTurckLocalSolution.restrictTerminal,
      IntrinsicDeTurckLocalSolution.restrictTerminal, enc.terminal_eq] using hSchart
  let enc' := enc.shrink
    (M := M) (F := F) (I := I) (x0 := x0) (het := het)
    hT' hT'le ha' htime hterminal
  simpa [chart', candidateS, enc'] using
    enc'.toSymmetricSubmoduleCandidateEncodingOnIcc
      (M := M) (F := F) (I := I) (x0 := x0) (het := het)
      (chart'.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (chart'.restrictedSymmetricA_coe_of_mem
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)

/-- Local metric uniqueness on the open common candidate overlap, derived from
the prescribed shorter-terminal readout.  The selected shrink is only used to
show that each intermediate shorter terminal remains visible in the shrunk
chart. -/
theorem RicciDeTurckChartClosureDataOnIcc.metric_eq_on_common_Ico_of_common_terminal_le_shrink_of_shrunk_symmetricCarrier
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    {T' : ℝ} (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
    {a' : ℝ≥0} (ha' : a' ≤ a)
    (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
      a' - (0 : ℝ≥0))
    (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp)
    (hcommonT : min sol₁.1.terminalTime sol₂.1.terminalTime ≤ T')
    {t : ℝ}
    (ht : t ∈ Ico ivp.initialTime (min sol₁.1.terminalTime sol₂.1.terminalTime))
    (x : M) (u v : TangentSpace I x) :
    metricTensor (I := I) (M := M) sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.1.toIntrinsicDeTurckSolution.metric t x u v := by
  exact
    chosenIntrinsicDeTurckLocalSolution_metric_eq_on_common_Ico_of_restricted_interval
      (M := M) (F := F) (I := I) sol₁ sol₂
      (fun {S} hS₀ hS₁ hS₂ {t} htS x u v ↦ by
        have hST' : S ≤ T' := le_trans (le_min hS₁ hS₂) hcommonT
        exact
          RicciDeTurckChartClosureDataOnIcc.metric_eq_on_restricted_interval_of_shrunk_symmetricCarrier
            (M := M) (F := F) (I := I) (D := D)
            hT' hT'le ha' htime sol₁ sol₂ hS₀ hS₁ hS₂ hST' (t := t) htS x u v)
      ht x u v

/-- Local uniqueness from shrunk ambient closure data on the whole common interval visible inside
the shrink.  This is the packaged form of
`RicciDeTurckChartClosureDataOnIcc.metric_eq_on_restricted_interval_of_shrunk_symmetricCarrier`
with the shorter terminal chosen as `min (min T₁ T₂) T'`. -/
theorem RicciDeTurckChartClosureDataOnIcc.metric_eq_on_common_interval_clipped_shrink_of_shrunk_symmetricCarrier
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    {T' : ℝ} (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
    {a' : ℝ≥0} (ha' : a' ≤ a)
    (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
      a' - (0 : ℝ≥0))
    (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp)
    {t : ℝ}
    (ht : t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T'))
    (x : M) (u v : TangentSpace I x) :
    metricTensor (I := I) (M := M) sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.1.toIntrinsicDeTurckSolution.metric t x u v := by
  let S := min (min sol₁.1.terminalTime sol₂.1.terminalTime) T'
  have hS₀ : ivp.initialTime < S := by
    exact lt_min (lt_min sol₁.1.initial_lt_terminal sol₂.1.initial_lt_terminal) hT'
  have hS₁ : S ≤ sol₁.1.terminalTime := by
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hS₂ : S ≤ sol₂.1.terminalTime := by
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hST' : S ≤ T' := min_le_right _ _
  exact
    RicciDeTurckChartClosureDataOnIcc.metric_eq_on_restricted_interval_of_shrunk_symmetricCarrier
      (M := M) (F := F) (I := I) (D := D)
      hT' hT'le ha' htime sol₁ sol₂ hS₀ hS₁ hS₂ hST' ht x u v

/-- Local uniqueness from shrunk ambient closure data on the full common
candidate interval, assuming that common interval is contained in the selected
shrink. -/
theorem RicciDeTurckChartClosureDataOnIcc.metric_eq_on_common_interval_of_common_terminal_le_shrink_of_shrunk_symmetricCarrier
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    {T' : ℝ} (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
    {a' : ℝ≥0} (ha' : a' ≤ a)
    (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
      a' - (0 : ℝ≥0))
    (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp)
    (hcommonT : min sol₁.1.terminalTime sol₂.1.terminalTime ≤ T')
    {t : ℝ}
    (ht : t ∈ Icc ivp.initialTime (min sol₁.1.terminalTime sol₂.1.terminalTime))
    (x : M) (u v : TangentSpace I x) :
    metricTensor (I := I) (M := M) sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.1.toIntrinsicDeTurckSolution.metric t x u v := by
  have htclip :
      t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T') := by
    simpa [min_eq_left hcommonT] using ht
  exact
    RicciDeTurckChartClosureDataOnIcc.metric_eq_on_common_interval_clipped_shrink_of_shrunk_symmetricCarrier
      (M := M) (F := F) (I := I) (D := D)
      hT' hT'le ha' htime sol₁ sol₂ htclip x u v

/-- Connection-level local uniqueness from shrunk ambient closure data on a prescribed shorter
terminal interval.  This upgrades the metric readout
`RicciDeTurckChartClosureDataOnIcc.metric_eq_on_restricted_interval_of_shrunk_symmetricCarrier`
through the canonical Levi-Civita connection bridge. -/
theorem RicciDeTurckChartClosureDataOnIcc.connection_eq_on_restricted_interval_of_shrunk_symmetricCarrier
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    {T' : ℝ} (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
    {a' : ℝ≥0} (ha' : a' ≤ a)
    (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
      a' - (0 : ℝ≥0))
    (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp)
    {S : ℝ} (hS₀ : ivp.initialTime < S)
    (hS₁ : S ≤ sol₁.1.terminalTime) (hS₂ : S ≤ sol₂.1.terminalTime) (hST' : S ≤ T')
    {t : ℝ} (ht : t ∈ Icc ivp.initialTime S)
    {x : M} {σ : Π y : M, TangentSpace I y} (hσ : MDiffAt (T% σ) x) :
    sol₁.1.canonicalConnection
      (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
      sol₂.1.canonicalConnection
        (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2) t σ x := by
  have ht₁ : t ∈ sol₁.1.toIntrinsicDeTurckSolution.timeSet := by
    exact sol₁.1.interval_subset ⟨ht.1, le_trans ht.2 hS₁⟩
  have ht₂ : t ∈ sol₂.1.toIntrinsicDeTurckSolution.timeSet := by
    exact sol₂.1.interval_subset ⟨ht.1, le_trans ht.2 hS₂⟩
  exact intrinsicDeTurckLocalSolution_connection_eq_of_metric_eq
    (I := I) (M := M) sol₁.1 sol₂.1
    (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2)
    (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2)
    ht₁ ht₂
    (fun y u v ↦
      RicciDeTurckChartClosureDataOnIcc.metric_eq_on_restricted_interval_of_shrunk_symmetricCarrier
        (M := M) (F := F) (I := I) (D := D)
        hT' hT'le ha' htime sol₁ sol₂ hS₀ hS₁ hS₂ hST' ht y u v)
    hσ

/-- Connection-level local uniqueness on the open common candidate overlap,
derived from the prescribed shorter-terminal connection readout. -/
theorem RicciDeTurckChartClosureDataOnIcc.connection_eq_on_common_Ico_of_common_terminal_le_shrink_of_shrunk_symmetricCarrier
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    {T' : ℝ} (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
    {a' : ℝ≥0} (ha' : a' ≤ a)
    (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
      a' - (0 : ℝ≥0))
    (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp)
    (hcommonT : min sol₁.1.terminalTime sol₂.1.terminalTime ≤ T')
    {t : ℝ}
    (ht : t ∈ Ico ivp.initialTime (min sol₁.1.terminalTime sol₂.1.terminalTime))
    {x : M} {σ : Π y : M, TangentSpace I y} (hσ : MDiffAt (T% σ) x) :
    sol₁.1.canonicalConnection
      (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
      sol₂.1.canonicalConnection
        (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2) t σ x := by
  exact
    chosenIntrinsicDeTurckLocalSolution_connection_eq_on_common_Ico_of_restricted_interval
      (M := M) (F := F) (I := I) sol₁ sol₂
      (fun {S} hS₀ hS₁ hS₂ {t} htS {x} {σ} hσ ↦ by
        have hST' : S ≤ T' := le_trans (le_min hS₁ hS₂) hcommonT
        exact
          RicciDeTurckChartClosureDataOnIcc.connection_eq_on_restricted_interval_of_shrunk_symmetricCarrier
            (M := M) (F := F) (I := I) (D := D)
            hT' hT'le ha' htime sol₁ sol₂ hS₀ hS₁ hS₂ hST' (t := t) htS
            (x := x) (σ := σ) hσ)
      ht hσ

/-- Connection-level local uniqueness from shrunk ambient closure data on the whole common interval
visible inside the shrink. -/
theorem RicciDeTurckChartClosureDataOnIcc.connection_eq_on_common_interval_clipped_shrink_of_shrunk_symmetricCarrier
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    {T' : ℝ} (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
    {a' : ℝ≥0} (ha' : a' ≤ a)
    (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
      a' - (0 : ℝ≥0))
    (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp)
    {t : ℝ}
    (ht : t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T'))
    {x : M} {σ : Π y : M, TangentSpace I y} (hσ : MDiffAt (T% σ) x) :
    sol₁.1.canonicalConnection
      (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
      sol₂.1.canonicalConnection
        (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2) t σ x := by
  let S := min (min sol₁.1.terminalTime sol₂.1.terminalTime) T'
  have hS₀ : ivp.initialTime < S := by
    exact lt_min (lt_min sol₁.1.initial_lt_terminal sol₂.1.initial_lt_terminal) hT'
  have hS₁ : S ≤ sol₁.1.terminalTime := by
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hS₂ : S ≤ sol₂.1.terminalTime := by
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hST' : S ≤ T' := min_le_right _ _
  exact
    RicciDeTurckChartClosureDataOnIcc.connection_eq_on_restricted_interval_of_shrunk_symmetricCarrier
      (M := M) (F := F) (I := I) (D := D)
      hT' hT'le ha' htime sol₁ sol₂ hS₀ hS₁ hS₂ hST' ht hσ

/-- Connection-level local uniqueness from shrunk ambient closure data on the
full common candidate interval, assuming that common interval is contained in
the selected shrink. -/
theorem RicciDeTurckChartClosureDataOnIcc.connection_eq_on_common_interval_of_common_terminal_le_shrink_of_shrunk_symmetricCarrier
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    {T' : ℝ} (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
    {a' : ℝ≥0} (ha' : a' ≤ a)
    (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
      a' - (0 : ℝ≥0))
    (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
      (E := F) (H := H) (I := I) (M := M) ivp)
    (hcommonT : min sol₁.1.terminalTime sol₂.1.terminalTime ≤ T')
    {t : ℝ}
    (ht : t ∈ Icc ivp.initialTime (min sol₁.1.terminalTime sol₂.1.terminalTime))
    {x : M} {σ : Π y : M, TangentSpace I y} (hσ : MDiffAt (T% σ) x) :
    sol₁.1.canonicalConnection
      (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
      sol₂.1.canonicalConnection
        (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2) t σ x := by
  have htclip :
      t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T') := by
    simpa [min_eq_left hcommonT] using ht
  exact
    RicciDeTurckChartClosureDataOnIcc.connection_eq_on_common_interval_clipped_shrink_of_shrunk_symmetricCarrier
      (M := M) (F := F) (I := I) (D := D)
      hT' hT'le ha' htime sol₁ sol₂ htclip hσ

/-- A positive-radius ambient interval closure can be shrunk to a genuine symmetric-carrier closure
whose Picard proof and metric-cone containment are derived automatically. The only residual input is
the unavoidable assertion that the candidates being encoded have intervals fitting inside the chosen
shrunk chart. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.exists_metricCone_shrunk_ofRicciDeTurckChartClosureDataOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (hT' : ivp.initialTime < T') (hT'le : T' ≤ T)
      (ha' : a' ≤ a)
      (htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
        a' - (0 : ℝ≥0))
      (hball : Metric.closedBall
        (InitialValueProblem.toSymmetricSectionSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
        riemannianMetricLocusSubmodule (M := M) (F := F)
          (W := (TangentSpace I : M → Type _)) et Kc hKc Ko hKo hKoEq hcover),
      0 < a' ∧
        ((∀ candidate : ChosenIntrinsicDeTurckLocalSolution
            (E := F) (H := H) (I := I) (M := M) ivp,
          (D.encode candidate).sol.terminalTime ≤ T') →
          let chart' := chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha' htime
          ∃ Dsym : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
            x0 et het Kc hKc Ko hKo hKoEq hcover chart', True) := by
  rcases chart.exists_metricCone_shrink_parameters
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover ha with
    ⟨T', a', hT', hT'le, ha'pos, ha'le, htime, hball⟩
  refine ⟨T', a', hT', hT'le, ha'le, htime, hball, ha'pos, ?_⟩
  intro hencode_terminal
  refine ⟨?_, trivial⟩
  exact
    SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.ofShrunkRicciDeTurckChartClosureDataOnIcc
      (M := M) (F := F) (I := I) (D := D)
      hT' hT'le ha'le htime hball hencode_terminal

/-- Chart-derived symmetric-carrier closure data yields the chosen-background DeTurck theorem
package. -/
theorem SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.toChosenIntrinsicDeTurckLocalExistenceUniqueness
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := F) (H := H) (I := I) (M := M) ivp :=
  chosenIntrinsicDeTurckLocalExistenceUniqueness_of_symmetricSubmodulePicard_smoothRealization_and_candidateEncodingOnIcc
    (M := M) (F := F) (I := I)
    x0 et het Kc hKc Ko hKo hKoEq hcover ivp
    (chart.restrictedSymmetricA
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
    chart.A
    (chart.restrictedSymmetricA_coe_of_mem
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
    chart.hT D.picard
    (chart.restrictedSymmetricA_lipschitzOn_Icc
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
    D.realization D.usesChosenBackground D.encode

/-- Chart-derived symmetric-carrier closure data yields the intrinsic Ricci-flow theorem package via
the chosen-background identity `C^3` gauge. -/
noncomputable def SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.toIntrinsicLocalExistenceUniqueness
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    IntrinsicLocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  D.toChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaIdentityDiffeomorph3Gauge

/-- Chart-derived symmetric-carrier closure data yields the ordinary compact point-4 theorem package
via the chosen-background identity `C^3` gauge. -/
noncomputable def SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.toLocalExistenceUniqueness
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    {chart : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate}
    (D : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chart) :
    LocalExistenceUniqueness (E := F) (H := H) (I := I) (M := M) ivp :=
  D.toChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaIdentityDiffeomorph3Gauge

/-- A family of chart-derived symmetric-carrier closure data yields the chosen-background
Ricci-DeTurck theorem family directly. -/
noncomputable def chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_symmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (D : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
        x0 et het Kc hKc Ko hKo hKoEq hcover (chart ivp)) :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (D ivp).toChosenIntrinsicDeTurckLocalExistenceUniqueness

/-- A family of chart-derived symmetric-carrier closure data yields the intrinsic compact point-4
theorem family via the chosen-background identity `C^3` gauge. -/
noncomputable def intrinsicLocalExistenceUniquenessFamily_of_symmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (D : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
        x0 et het Kc hKc Ko hKo hKoEq hcover (chart ivp)) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (D ivp).toIntrinsicLocalExistenceUniqueness

/-- A family of chart-derived symmetric-carrier closure data yields the ordinary compact point-4
theorem family via the chosen-background identity `C^3` gauge. -/
noncomputable def localExistenceUniquenessFamily_of_symmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (D : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
        x0 et het Kc hKc Ko hKo hKoEq hcover (chart ivp)) :
    LocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (D ivp).toLocalExistenceUniqueness

/-- A family of global chart-closure data yields the chosen-background Ricci-DeTurck theorem family
directly. -/
noncomputable def chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_ricciDeTurckChartClosureData
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (D : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover (chart ivp)) :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (D ivp).toChosenIntrinsicDeTurckLocalExistenceUniqueness

/-- A family of global chart-closure data yields the intrinsic compact point-4 theorem family via
the chosen-background identity `C³` gauge. -/
noncomputable def intrinsicLocalExistenceUniquenessFamily_of_ricciDeTurckChartClosureData
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (D : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover (chart ivp)) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (D ivp).toIntrinsicLocalExistenceUniqueness

/-- A family of global chart-closure data yields the ordinary compact point-4 theorem family via
the chosen-background identity `C³` gauge. -/
noncomputable def localExistenceUniquenessFamily_of_ricciDeTurckChartClosureData
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChart
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (D : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover (chart ivp)) :
    LocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (D ivp).toLocalExistenceUniqueness

/-- A family of interval chart-closure data yields the chosen-background Ricci-DeTurck theorem
family directly. -/
noncomputable def chosenIntrinsicDeTurckLocalExistenceUniquenessFamily_of_ricciDeTurckChartClosureDataOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (D : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover (chart ivp)) :
    ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (D ivp).toChosenIntrinsicDeTurckLocalExistenceUniqueness

/-- A family of interval chart-closure data yields the intrinsic compact point-4 theorem family via
the chosen-background identity `C³` gauge. -/
noncomputable def intrinsicLocalExistenceUniquenessFamily_of_ricciDeTurckChartClosureDataOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (D : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover (chart ivp)) :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (D ivp).toIntrinsicLocalExistenceUniqueness

/-- A family of interval chart-closure data yields the ordinary compact point-4 theorem family via
the chosen-background identity `C³` gauge. -/
noncomputable def localExistenceUniquenessFamily_of_ricciDeTurckChartClosureDataOnIcc
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    {x0 : κ → M}
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i)}
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    [FiniteDimensional ℝ F] [Nontrivial F]
    (T : InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ)
    (a L Kpic Kstate :
      InitialValueProblem (E := F) (H := H) (I := I) (M := M) → ℝ≥0)
    (chart : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime
        (T ivp) (a ivp) (L ivp) (Kpic ivp) (Kstate ivp))
    (D : ∀ ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M),
      RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover (chart ivp)) :
    LocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (D ivp).toLocalExistenceUniqueness

/-- **Banach-chart assembly from bounded/Lipschitz field data.**
A time-dependent Banach representative `A` of the Ricci-DeTurck operator that, on the closed
`‖·‖`-ball of radius `a` about the initial metric `g₀`, is uniformly `Kpic`-Lipschitz in the state,
is bounded by `L`, is continuous in time, obeys the one-sided Picard-Lindelöf interval-length
constraint `L·(T − t₀) ≤ a`, is `Kstate`-Lipschitz on the positive-definite locus, and agrees
pointwise with the intrinsic Ricci-DeTurck right-hand side of some geometric background, assembles
into a `TimeDependentGeometricRicciDeTurckBanachChart`.

The Picard-Lindelöf datum (`picard`) is discharged *here* from the bounded/Lipschitz/time-continuous
field data by the standard one-sided interval-length computation
`L · max (T − t₀) (t₀ − t₀) = L · (T − t₀) ≤ a − 0`.  This isolates exactly the analytic inputs a
*bounded* (mild / regularised) chart operator must supply on a ball about the initial metric: the raw
second-order Ricci-DeTurck operator is unbounded on the `C⁰` section space, so it cannot inhabit
`IsPicardLindelof` directly — a bounded representative is what makes the Banach Cauchy-Lipschitz
requirement honest.  This is the `chart`-side constructor consumed by
`intrinsicLocalExistenceUniquenessFamily_of_ricciDeTurckChartClosureData`. -/
noncomputable def TimeDependentGeometricRicciDeTurckBanachChart.ofLipschitzBoundedContinuous
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _))
    (t₀ T : ℝ) (a L Kpic Kstate : ℝ≥0)
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)
    (hT : t₀ < T)
    (hlipBall : ∀ t ∈ Set.Icc t₀ T, LipschitzOnWith Kpic (A t)
      (Metric.closedBall
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) (a : ℝ)))
    (hcontTime : ∀ x ∈ Metric.closedBall
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) (a : ℝ),
      ContinuousOn (fun t : ℝ => A t x) (Set.Icc t₀ T))
    (hbound : ∀ t ∈ Set.Icc t₀ T, ∀ x ∈ Metric.closedBall
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) (a : ℝ),
      ‖A t x‖ ≤ (L : ℝ))
    (hLT : (L : ℝ) * (T - t₀) ≤ (a : ℝ))
    (hlipState : ∀ t : ℝ, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover))
    (hgeom : ∀ τ s, s ∈ positiveDefiniteLocus
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover →
      ∃ (g : MetricFamily (I := I) (M := M))
        (background : ConnectionFamily (I := I) (M := M)),
        ∀ (x : M) (u v : TangentSpace I x),
          A τ s x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x u v) :
    TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate where
  A := A
  hT := hT
  picard :=
    { lipschitzOnWith := fun t ht => hlipBall t ht
      continuousOn := fun x hx => hcontTime x hx
      norm_le := fun t ht x hx => hbound t ht x hx
      mul_max_le := by
        have hmax : max (T - t₀) (t₀ - t₀) = T - t₀ := by
          rw [sub_self]; exact max_eq_left (by linarith)
        show (L : ℝ) * max (T - t₀) (t₀ - t₀) ≤ (a : ℝ) - ((0 : ℝ≥0) : ℝ)
        rw [hmax, NNReal.coe_zero, sub_zero]
        exact hLT }
  lipschitz := hlipState
  geometric := hgeom

/-- **Interval-scoped Banach-chart assembly from bounded/Lipschitz field data.**
The `…OnIcc` analogue of `TimeDependentGeometricRicciDeTurckBanachChart.ofLipschitzBoundedContinuous`:
it assembles a `TimeDependentGeometricRicciDeTurckBanachChartOnIcc` from the same bounded/Lipschitz/
time-continuous field data on the ball about `g₀`, discharging the Picard-Lindelöf datum by the one-
sided interval-length computation, and — matching the interval-scoped chart — requiring the
`Kstate`-Lipschitz control on the positive-definite locus only on the Picard interval `Icc t₀ T`
(field `lipschitzOn_Icc`) rather than for all times.  This is the interval-route `chart`-side
constructor consumed by
`intrinsicLocalExistenceUniquenessFamily_of_ricciDeTurckChartClosureDataOnIcc`. -/
noncomputable def TimeDependentGeometricRicciDeTurckBanachChartOnIcc.ofLipschitzBoundedContinuous
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _))) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F (TangentSpace I : M → Type _))
    (t₀ T : ℝ) (a L Kpic Kstate : ℝ≥0)
    (A : ℝ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
        et Kc hKc Ko hKo hKoEq hcover)
    (hT : t₀ < T)
    (hlipBall : ∀ t ∈ Set.Icc t₀ T, LipschitzOnWith Kpic (A t)
      (Metric.closedBall
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) (a : ℝ)))
    (hcontTime : ∀ x ∈ Metric.closedBall
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) (a : ℝ),
      ContinuousOn (fun t : ℝ => A t x) (Set.Icc t₀ T))
    (hbound : ∀ t ∈ Set.Icc t₀ T, ∀ x ∈ Metric.closedBall
        (⟨g₀.toSection, g₀.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
            (V := _root_.Bundle.BilinearFormBundle (V := (TangentSpace I : M → Type _)))
            et Kc hKc Ko hKo hKoEq hcover) (a : ℝ),
      ‖A t x‖ ≤ (L : ℝ))
    (hLT : (L : ℝ) * (T - t₀) ≤ (a : ℝ))
    (hlipStateOn : ∀ t ∈ Set.Icc t₀ T, LipschitzOnWith Kstate (A t)
      (positiveDefiniteLocus (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover))
    (hgeom : ∀ τ s, s ∈ positiveDefiniteLocus
        (M := M) (F := F) (W := (TangentSpace I : M → Type _))
        et Kc hKc Ko hKo hKoEq hcover →
      ∃ (g : MetricFamily (I := I) (M := M))
        (background : ConnectionFamily (I := I) (M := M)),
        ∀ (x : M) (u v : TangentSpace I x),
          A τ s x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x u v) :
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate where
  A := A
  hT := hT
  picard :=
    { lipschitzOnWith := fun t ht => hlipBall t ht
      continuousOn := fun x hx => hcontTime x hx
      norm_le := fun t ht x hx => hbound t ht x hx
      mul_max_le := by
        have hmax : max (T - t₀) (t₀ - t₀) = T - t₀ := by
          rw [sub_self]; exact max_eq_left (by linarith)
        show (L : ℝ) * max (T - t₀) (t₀ - t₀) ≤ (a : ℝ) - ((0 : ℝ≥0) : ℝ)
        rw [hmax, NNReal.coe_zero, sub_zero]
        exact hLT }
  lipschitzOn_Icc := hlipStateOn
  geometric := hgeom

end MetricLocusEvolution
end AnalyticPDE
end RicciFlow
