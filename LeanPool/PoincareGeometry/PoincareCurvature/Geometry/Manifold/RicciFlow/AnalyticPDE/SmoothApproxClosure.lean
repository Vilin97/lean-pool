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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothRealization
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.RiemannianSectionSmoothApprox

/-!
# Preferred-cover smooth approximation closure for Ricci-DeTurck metric carriers

This thin module specializes the smooth-SPD closure criterion from `SmoothRealization`: on preferred
bilinear-form trivializations, it is enough to produce spatially smooth fiberwise approximants and a
uniform bound on the underlying inverse tangent trivializations.  The finite-cover Banach-norm
estimate is supplied by `RiemannianSectionSmoothApprox`.
-/

@[expose] public noncomputable section

open Set
open scoped Bundle Manifold ContDiff NNReal Topology

namespace RicciFlow
namespace AnalyticPDE
namespace MetricLocusEvolution
namespace SmoothSectionRHSIdentification

open PoincareCurvature.Bundle.Trivialization
open PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace
section PreferredSmoothApproxClosure

variable {M : Type*} [TopologicalSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)
local notation "TM" => (TangentSpace I : M → Type _)
local notation "BilW" => _root_.Bundle.BilinearFormBundle (V := TM)

local instance preferredSmoothApproxBilFNormedAddCommGroup :
    NormedAddCommGroup BilF := inferInstance
local instance preferredSmoothApproxBilFNormedSpace :
    NormedSpace ℝ BilF := inferInstance
local instance (priority := 10) preferredSmoothApproxTMNormedAddCommGroup [ChartedSpace H M] (x : M) :
    NormedAddCommGroup (TM x) := by
  change NormedAddCommGroup F
  infer_instance
local instance (priority := 10) preferredSmoothApproxTMNormedSpace [ChartedSpace H M] (x : M) :
    NormedSpace ℝ (TM x) := by
  change NormedSpace ℝ F
  infer_instance
local instance preferredSmoothApproxTMTopologicalSpace
    [ChartedSpace H M] [IsManifold I ∞ M] :
    TopologicalSpace (_root_.Bundle.TotalSpace F TM) :=
  inferInstance
local instance preferredSmoothApproxTMFiberBundle
    [ChartedSpace H M] [IsManifold I ∞ M] :
    FiberBundle F TM :=
  TangentSpace.fiberBundle (I := I)
local instance preferredSmoothApproxTMVectorBundle
    [ChartedSpace H M] [IsManifold I ∞ M] :
    VectorBundle ℝ F TM :=
  TangentSpace.vectorBundle (I := I)
local instance preferredSmoothApproxCLMNorm [ChartedSpace H M] (x : M) :
    Norm (F →L[ℝ] TM x) := by
  change Norm (F →L[ℝ] F)
  infer_instance
local instance preferredSmoothApproxForwardCLMNorm [ChartedSpace H M] (x : M) :
    Norm (TM x →L[ℝ] F) := by
  change Norm (F →L[ℝ] F)
  infer_instance

local instance preferredSmoothApproxBilWDist [ChartedSpace H M] (x : M) :
    Dist (BilW x) := by
  change Dist BilF
  infer_instance
local instance preferredSmoothApproxBilWTopologicalSpace
    [ChartedSpace H M] [IsManifold I ∞ M] :
    TopologicalSpace (_root_.Bundle.TotalSpace BilF BilW) :=
  _root_.Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) F TM (F →L[ℝ] ℝ) (fun x ↦ TM x →L[ℝ] ℝ)
local instance preferredSmoothApproxBilWFiberBundle
    [ChartedSpace H M] [IsManifold I ∞ M] :
    FiberBundle BilF BilW :=
  _root_.Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) F TM (F →L[ℝ] ℝ) (fun x ↦ TM x →L[ℝ] ℝ)
local instance preferredSmoothApproxBilWVectorBundle
    [ChartedSpace H M] [IsManifold I ∞ M] :
    VectorBundle ℝ BilF BilW :=
  _root_.Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) F TM (F →L[ℝ] ℝ) (fun x ↦ TM x →L[ℝ] ℝ)

/-- Preferred-cover version of the smooth-SPD closure criterion.  Instead of assuming
finite-cover Banach-norm approximation directly, it assumes spatially smooth fiberwise
approximants.  The concrete preferred-bilinear Lipschitz estimate upgrades those approximants to
the Banach norm used by the Ricci-DeTurck carrier. -/
theorem closure_smooth_spd_of_metric_locus_and_smooth_fiberwise_approx_preferredBilinear
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F TM I]
    [IsManifold I (minSmoothness ℝ 3) M]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ i (x : Kc i), ‖(trivializationAt F TM (x0 i)).symmL ℝ x.1‖ ≤ C)
    (hsmoothApprox :
      ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
        s ∈ riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
          et Kc hKc Ko hKo hKoEq hcover →
        ∀ η > 0,
          ∃ g : Cₛ^(2 : ℕ∞)⟮I; BilF, BilW⟯,
            ∀ x : M,
              dist ((s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
                et Kc hKc Ko hKo hKoEq hcover) x) (g x) < η) :
    ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
        et Kc hKc Ko hKo hKoEq hcover →
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover) ∈
        closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover |
            u ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := TM)
              (et := et)
              (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
              (hKoEq := hKoEq) (hcover := hcover) ∧
            ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
              (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}) := by
  have hetFun : et = fun i ↦ trivializationAt BilF BilW (x0 i) := funext het
  subst et
  refine closure_smooth_spd_of_metric_locus_and_forall_dist_lt_unsymmetric
    (M := M) (F := F) (I := I) x0
    (fun i ↦ trivializationAt BilF BilW (x0 i)) (fun _ ↦ rfl)
    Kc hKc Ko hKo hKoEq hcover ?_
  intro s hs ε hε
  exact
    @exists_dist_lt_of_smooth_fiberwise_approx_preferredBilinear_of_symmL_opNorm_le
      F inferInstance inferInstance H inferInstance I M inferInstance inferInstance
      F inferInstance inferInstance TM
      (inferInstance : TopologicalSpace (_root_.Bundle.TotalSpace F TM))
      (inferInstance : (x : M) → NormedAddCommGroup (TM x))
      (inferInstance : (x : M) → NormedSpace ℝ (TM x))
      (TangentSpace.fiberBundle (I := I))
      (TangentSpace.vectorBundle (I := I))
      κ inferInstance inferInstance x0 Kc hKc Ko hKo hKoEq hcover
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i ↦ trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
      C hCpos hC (hsmoothApprox s hs) ε hε

/-- Preferred-cover smooth-SPD closure through symmetric smooth approximants.  The input only has to
produce arbitrary smooth fiberwise approximants: symmetric metric-locus targets are symmetrized in the
finite-cover norm before the positive-definite openness argument is applied. -/
theorem closure_smooth_spd_of_metric_locus_and_symmetrized_smooth_fiberwise_approx_preferredBilinear
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F TM I]
    [IsManifold I (minSmoothness ℝ 3) M]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ i (x : Kc i), ‖(trivializationAt F TM (x0 i)).symmL ℝ x.1‖ ≤ C)
    (hsmoothApprox :
      ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
        s ∈ riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
          et Kc hKc Ko hKo hKoEq hcover →
        ∀ η > 0,
          ∃ g : Cₛ^(2 : ℕ∞)⟮I; BilF, BilW⟯,
            ∀ x : M,
              dist ((s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
                et Kc hKc Ko hKo hKoEq hcover) x) (g x) < η) :
    ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
        et Kc hKc Ko hKo hKoEq hcover →
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover) ∈
        closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover |
            u ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := TM)
              (et := et)
              (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
              (hKoEq := hKoEq) (hcover := hcover) ∧
            ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
              (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}) := by
  have hetFun : et = fun i ↦ trivializationAt BilF BilW (x0 i) := funext het
  subst et
  refine closure_smooth_spd_of_metric_locus_and_forall_dist_lt_symmetric
    (M := M) (F := F) (I := I) x0
    (fun i ↦ trivializationAt BilF BilW (x0 i)) (fun _ ↦ rfl)
    Kc hKc Ko hKo hKoEq hcover ?_
  intro s hs ε hε
  have hspd :
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i ↦ trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) ∈
        symmetricPositiveDefiniteLocus (M := M) (F := F) (W := TM)
          (fun i ↦ trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover :=
    (mem_riemannianMetricLocusSubmodule_iff
      (M := M) (F := F) (W := TM)
      x0 (fun i ↦ trivializationAt BilF BilW (x0 i)) (fun _ ↦ rfl)
      Kc hKc Ko hKo hKoEq hcover s).1 hs
  exact
    @exists_symmetric_dist_lt_of_smooth_fiberwise_approx_preferredBilinear_of_symmL_opNorm_le
      F inferInstance inferInstance H inferInstance I M inferInstance inferInstance
      F inferInstance inferInstance TM
      (inferInstance : TopologicalSpace (_root_.Bundle.TotalSpace F TM))
      (inferInstance : (x : M) → NormedAddCommGroup (TM x))
      (inferInstance : (x : M) → NormedSpace ℝ (TM x))
      (TangentSpace.fiberBundle (I := I))
      (TangentSpace.vectorBundle (I := I))
      κ inferInstance inferInstance x0 Kc hKc Ko hKo hKoEq hcover
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i ↦ trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
      hspd.1 C hCpos hC (hsmoothApprox s hs) ε hε

/-- Preferred-cover smooth-SPD closure with the smooth fiberwise approximation hypothesis produced
from local bounds on the underlying tangent-bundle trivializations.  This removes the abstract
smooth-approximant input from the closure criterion. -/
theorem closure_smooth_spd_of_metric_locus_and_local_trivialization_bounds_preferredBilinear
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ i (x : Kc i), ‖(trivializationAt F TM (x0 i)).symmL ℝ x.1‖ ≤ C)
    (hlocalBound : ∀ x : M, ∃ C > 0,
      ∀ᶠ y in 𝓝 x, ‖(trivializationAt F TM x).continuousLinearMapAt ℝ y‖ < C) :
    ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
        et Kc hKc Ko hKo hKoEq hcover →
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover) ∈
        closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover |
            u ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := TM)
              (et := et)
              (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
              (hKoEq := hKoEq) (hcover := hcover) ∧
            ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
              (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}) := by
  have hetFun : et = fun i ↦ trivializationAt BilF BilW (x0 i) := funext het
  subst et
  refine
    closure_smooth_spd_of_metric_locus_and_symmetrized_smooth_fiberwise_approx_preferredBilinear
    (M := M) (F := F) (I := I) x0
    (fun i ↦ trivializationAt BilF BilW (x0 i)) (fun _ ↦ rfl)
    Kc hKc Ko hKo hKoEq hcover hCpos hC ?_
  intro s _hs η hη
  exact
    @exists_smooth_fiberwise_approx_preferredBilinear_of_eventually_norm_trivializationAt_lt
      F inferInstance inferInstance H inferInstance I M inferInstance inferInstance
      F inferInstance inferInstance TM
      (inferInstance : TopologicalSpace (_root_.Bundle.TotalSpace F TM))
      (inferInstance : (x : M) → NormedAddCommGroup (TM x))
      (inferInstance : (x : M) → NormedSpace ℝ (TM x))
      (TangentSpace.fiberBundle (I := I))
      (TangentSpace.vectorBundle (I := I))
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (inferInstance : ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I)
      hlocalBound κ inferInstance x0
      Kc hKc Ko hKo hKoEq hcover
       (s := (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
         (fun i ↦ trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover))
       η hη

/-- Preferred-cover smooth-SPD closure for continuous Riemannian tangent bundles, with the finite-cover
inverse bound and the local trivialization bound both discharged by the continuous Riemannian bundle
smooth-density theorem. -/
theorem closure_smooth_spd_of_metric_locus_preferredBilinear_of_continuousRiemannianBundle
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [_root_.Bundle.RiemannianBundle TM]
    [IsContinuousRiemannianBundle (B := M) F TM]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F] :
    ∀ s : symmetricSectionSubmodule et Kc hKc Ko hKo hKoEq hcover,
      s ∈ riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
        et Kc hKc Ko hKo hKoEq hcover →
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        et Kc hKc Ko hKo hKoEq hcover) ∈
        closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover |
            u ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := TM)
              (et := et)
              (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
              (hKoEq := hKoEq) (hcover := hcover) ∧
            ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
              (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}) := by
  have hetFun : et = fun i ↦ trivializationAt BilF BilW (x0 i) := funext het
  subst et
  intro s hs
  have hspd :
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i ↦ trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) ∈
        symmetricPositiveDefiniteLocus (M := M) (F := F) (W := TM)
          (fun i ↦ trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover :=
    (mem_riemannianMetricLocusSubmodule_iff
      (M := M) (F := F) (W := TM)
      x0 (fun i ↦ trivializationAt BilF BilW (x0 i)) (fun _ ↦ rfl)
      Kc hKc Ko hKo hKoEq hcover s).1 hs
  exact
    mem_closure_smooth_spd_preferredBilinear_of_continuousRiemannianBundle
      (E := F) (H := H) (I := I) (M := M) (F := F) (W := TM)
      x0
      (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i ↦ trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
      hspd

/-- Build an interval-scoped Ricci-DeTurck Banach chart from Picard data, geometric
identification, and a fibrewise Lipschitz estimate.  The continuous Riemannian tangent-bundle
structure supplies the finite-cover inverse-trivialization bound, so the chart's section-space
Lipschitz constant is chosen existentially instead of being an explicit input. -/
def timeDependentGeometricRicciDeTurckBanachChartOnIccOfForallFiberDistLe
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F TM I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [_root_.Bundle.RiemannianBundle TM]
    [IsContinuousRiemannianBundle (B := M) F TM]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F TM)
    {A : ℝ →
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover →
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {a L Kpic Kfiber : ℝ≥0}
    (picard : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩
      (⟨g₀.toSection, g₀.continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover) a 0 L Kpic)
    (hfiber : ∀ τ, τ ∈ Icc t₀ T → ∀ ⦃s⦄, s ∈ positiveDefiniteLocus
        (M := M) (F := F) (W := TM) et Kc hKc Ko hKo hKoEq hcover →
      ∀ ⦃t⦄, t ∈ positiveDefiniteLocus
        (M := M) (F := F) (W := TM) et Kc hKc Ko hKo hKoEq hcover →
      ∀ x : M, @dist (BilW x)
        (ContinuousLinearMap.toPseudoMetricSpace
          (𝕜 := ℝ) (𝕜₂ := ℝ) (E := TM x) (F := TM x →L[ℝ] ℝ)
          (σ₁₂ := RingHom.id ℝ)).toDist
        ((A τ s) x) ((A τ t) x) ≤ (Kfiber : ℝ) * dist s t)
    (geometric : ∀ τ s, s ∈ positiveDefiniteLocus
        (M := M) (F := F) (W := TM) et Kc hKc Ko hKo hKoEq hcover →
      ∃ (g : MetricFamily (I := I) (M := M))
        (background : ConnectionFamily (I := I) (M := M)),
        ∀ (x : M) (u v : TangentSpace I x),
          A τ s x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x u v) :
    Σ Kstate : ℝ≥0,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate := by
  let hKstate : ∃ Kstate : ℝ≥0,
      ∀ τ ∈ Icc t₀ T,
        LipschitzOnWith Kstate (A τ)
          (positiveDefiniteLocus
            (M := M) (F := F) (W := TM) et Kc hKc Ko hKo hKoEq hcover) :=
    exists_preferredBilinear_lipschitzOnWith_family_of_forall_fiber_dist_le
      (M := M) (F := F) (W := TM) (x0 := x0)
      (timeSet := Icc t₀ T) (et := et) het
      (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
      (hKoEq := hKoEq) (hcover := hcover)
      (stateSet := positiveDefiniteLocus
        (M := M) (F := F) (W := TM) et Kc hKc Ko hKo hKoEq hcover)
      (A := A) (K := Kfiber) hfiber
  let Kstate : ℝ≥0 := Classical.choose hKstate
  have hLip : ∀ τ ∈ Icc t₀ T,
      LipschitzOnWith Kstate (A τ)
        (positiveDefiniteLocus
          (M := M) (F := F) (W := TM) et Kc hKc Ko hKo hKoEq hcover) :=
    Classical.choose_spec hKstate
  exact ⟨Kstate,
    { A := A
      hT := hT
      picard := picard
      lipschitzOn_Icc := hLip
      geometric := geometric }⟩

/-- Build an interval-scoped Ricci-DeTurck Banach chart from preferred-cover coordinate
Lipschitz estimates.  The coordinate estimate is first transported back to a fibrewise estimate
using the preferred bilinear-form trivializations; the existing fibrewise chart builder then
supplies the section-space Lipschitz constant. -/
def timeDependentGeometricRicciDeTurckBanachChartOnIccOfForallCoordDistLe
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F TM I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [_root_.Bundle.RiemannianBundle TM]
    [IsContinuousRiemannianBundle (B := M) F TM]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [het_atlas : ∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F TM)
    {A : ℝ →
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover →
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {a L Kpic Kcoord : ℝ≥0}
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i (x : Kc i),
      @norm (TM x.1 →L[ℝ] F) ContinuousLinearMap.hasOpNorm
        ((trivializationAt F TM (x0 i)).continuousLinearMapAt ℝ x.1) ≤ C)
    (picard : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩
      (⟨g₀.toSection, g₀.continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover) a 0 L Kpic)
    (hcoord : ∀ τ, τ ∈ Icc t₀ T → ∀ ⦃s⦄, s ∈ positiveDefiniteLocus
        (M := M) (F := F) (W := TM) et Kc hKc Ko hKo hKoEq hcover →
      ∀ ⦃t⦄, t ∈ positiveDefiniteLocus
        (M := M) (F := F) (W := TM) et Kc hKc Ko hKo hKoEq hcover →
      ∀ i (x : Kc i),
        dist
            ((equivCompatibleCoordFamilySubmodule
              (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover (A τ s)).1 i x)
            ((equivCompatibleCoordFamilySubmodule
              (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover (A τ t)).1 i x)
          ≤ (Kcoord : ℝ) * dist s t)
    (geometric : ∀ τ s, s ∈ positiveDefiniteLocus
        (M := M) (F := F) (W := TM) et Kc hKc Ko hKo hKoEq hcover →
      ∃ (g : MetricFamily (I := I) (M := M))
        (background : ConnectionFamily (I := I) (M := M)),
        ∀ (x : M) (u v : TangentSpace I x),
          A τ s x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x u v) :
    Σ Kstate : ℝ≥0,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate := by
  let Kfiber : ℝ≥0 :=
    ⟨(C * C) * (Kcoord : ℝ),
      mul_nonneg (mul_nonneg hC0 hC0) (NNReal.coe_nonneg Kcoord)⟩
  have hfiber' :=
    @preferredBilinear_forall_fiber_dist_le_family_of_forall_coord_dist_le_of_eq_trivializationAt
      M _ F _ _ TM
      _ (fun x => inferInstance) (fun x => inferInstance) _ _
      κ _ _ ℝ (Icc t₀ T) x0 et het_atlas het
      Kc hKc Ko hKo hKoEq hcover
      (positiveDefiniteLocus
        (M := M) (F := F) (W := TM) et Kc hKc Ko hKo hKoEq hcover)
      A C (Kcoord : ℝ) hC0 hC hcoord
  exact
    timeDependentGeometricRicciDeTurckBanachChartOnIccOfForallFiberDistLe
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ hT
      (A := A) (a := a) (L := L) (Kpic := Kpic) (Kfiber := Kfiber)
      picard (fun τ hτ s hs t ht x => by
        simpa [Kfiber] using hfiber' τ hτ hs ht x)
      geometric

/-- Real-constant variant of
`timeDependentGeometricRicciDeTurckBanachChartOnIccOfForallCoordDistLe`.  This is the form used by
coordinate estimates whose Lipschitz constant is first produced as a nonnegative real number, such
as the finite schematic Ricci-DeTurck matrix constants. -/
def timeDependentGeometricRicciDeTurckBanachChartOnIccOfForallCoordDistLeReal
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F TM I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [_root_.Bundle.RiemannianBundle TM]
    [IsContinuousRiemannianBundle (B := M) F TM]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F TM)
    {A : ℝ →
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover →
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {a L Kpic : ℝ≥0} {Kcoord : ℝ} (hKcoord : 0 ≤ Kcoord)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i (x : Kc i),
      @norm (TM x.1 →L[ℝ] F) ContinuousLinearMap.hasOpNorm
        ((trivializationAt F TM (x0 i)).continuousLinearMapAt ℝ x.1) ≤ C)
    (picard : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩
      (⟨g₀.toSection, g₀.continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover) a 0 L Kpic)
    (hcoord : ∀ τ, τ ∈ Icc t₀ T → ∀ ⦃s⦄, s ∈ positiveDefiniteLocus
        (M := M) (F := F) (W := TM) et Kc hKc Ko hKo hKoEq hcover →
      ∀ ⦃t⦄, t ∈ positiveDefiniteLocus
        (M := M) (F := F) (W := TM) et Kc hKc Ko hKo hKoEq hcover →
      ∀ i (x : Kc i),
        dist
            ((equivCompatibleCoordFamilySubmodule
              (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover (A τ s)).1 i x)
            ((equivCompatibleCoordFamilySubmodule
              (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover (A τ t)).1 i x)
          ≤ Kcoord * dist s t)
    (geometric : ∀ τ s, s ∈ positiveDefiniteLocus
        (M := M) (F := F) (W := TM) et Kc hKc Ko hKo hKoEq hcover →
      ∃ (g : MetricFamily (I := I) (M := M))
        (background : ConnectionFamily (I := I) (M := M)),
        ∀ (x : M) (u v : TangentSpace I x),
          A τ s x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x u v) :
    Σ Kstate : ℝ≥0,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate := by
  let KcoordNN : ℝ≥0 := ⟨Kcoord, hKcoord⟩
  exact timeDependentGeometricRicciDeTurckBanachChartOnIccOfForallCoordDistLe
    (M := M) (F := F) (I := I)
    x0 et het Kc hKc Ko hKo hKoEq hcover g₀ hT
    (A := A) (a := a) (L := L) (Kpic := Kpic) (Kcoord := KcoordNN)
    hC0 hC picard
    (fun τ hτ s hs t ht i x => by
      simpa [KcoordNN] using hcoord τ hτ hs ht i x)
    geometric

/-- Build an interval-scoped Ricci-DeTurck Banach chart from finite-cover coordinate-family
Lipschitz estimates.  This packages the standard finite-coordinate readout bridge before invoking
the pointwise coordinate-distance constructor. -/
def timeDependentGeometricRicciDeTurckBanachChartOnIccOfCoordFamilyLipschitzOnWith
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F TM I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [_root_.Bundle.RiemannianBundle TM]
    [IsContinuousRiemannianBundle (B := M) F TM]
    {κ : Type*} [Fintype κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F TM)
    {A : ℝ →
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover →
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {a L Kpic Kcoord : ℝ≥0}
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i (x : Kc i),
      @norm (TM x.1 →L[ℝ] F) ContinuousLinearMap.hasOpNorm
        ((trivializationAt F TM (x0 i)).continuousLinearMapAt ℝ x.1) ≤ C)
    (picard : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩
      (⟨g₀.toSection, g₀.continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover) a 0 L Kpic)
    (hcoordLip : ∀ τ, τ ∈ Icc t₀ T →
      LipschitzOnWith Kcoord
        (fun s =>
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF) (V := BilW)
            et Kc hKc Ko hKo hKoEq hcover (A τ s)).1 :
              CoordFamily (F := BilF) Kc))
        (positiveDefiniteLocus
          (M := M) (F := F) (W := TM) et Kc hKc Ko hKo hKoEq hcover))
    (geometric : ∀ τ s, s ∈ positiveDefiniteLocus
        (M := M) (F := F) (W := TM) et Kc hKc Ko hKo hKoEq hcover →
      ∃ (g : MetricFamily (I := I) (M := M))
        (background : ConnectionFamily (I := I) (M := M)),
        ∀ (x : M) (u v : TangentSpace I x),
          A τ s x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x u v) :
    Σ Kstate : ℝ≥0,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate := by
  have hcoord :
      ∀ τ, τ ∈ Icc t₀ T → ∀ ⦃s⦄, s ∈ positiveDefiniteLocus
          (M := M) (F := F) (W := TM) et Kc hKc Ko hKo hKoEq hcover →
        ∀ ⦃t⦄, t ∈ positiveDefiniteLocus
          (M := M) (F := F) (W := TM) et Kc hKc Ko hKo hKoEq hcover →
        ∀ i (x : Kc i),
          dist
              ((equivCompatibleCoordFamilySubmodule
                (𝕜 := ℝ) (F := BilF) (V := BilW)
                et Kc hKc Ko hKo hKoEq hcover (A τ s)).1 i x)
              ((equivCompatibleCoordFamilySubmodule
                (𝕜 := ℝ) (F := BilF) (V := BilW)
                et Kc hKc Ko hKo hKoEq hcover (A τ t)).1 i x)
            ≤ (Kcoord : ℝ) * dist s t :=
    forall_coord_dist_le_family_of_coordFamily_lipschitzOnWith
      (𝕜 := ℝ) (F := BilF) (V := BilW) (timeSet := Icc t₀ T)
      (et := et) (Kc := Kc) (hKc := hKc)
      (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
      (stateSet := positiveDefiniteLocus
        (M := M) (F := F) (W := TM) et Kc hKc Ko hKo hKoEq hcover)
      (A := A) (L := Kcoord) hcoordLip
  exact timeDependentGeometricRicciDeTurckBanachChartOnIccOfForallCoordDistLe
    (M := M) (F := F) (I := I)
    x0 et het Kc hKc Ko hKo hKoEq hcover g₀ hT
    (A := A) (a := a) (L := L) (Kpic := Kpic) (Kcoord := Kcoord)
    hC0 hC picard hcoord geometric

/-- Real-constant variant of
`timeDependentGeometricRicciDeTurckBanachChartOnIccOfCoordFamilyLipschitzOnWith`. -/
def timeDependentGeometricRicciDeTurckBanachChartOnIccOfCoordFamilyLipschitzOnWithReal
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 F TM I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [_root_.Bundle.RiemannianBundle TM]
    [IsContinuousRiemannianBundle (B := M) F TM]
    {κ : Type*} [Fintype κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    [FiniteDimensional ℝ F] [Nontrivial F]
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F TM)
    {A : ℝ →
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover →
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ} (hT : t₀ < T)
    {a L Kpic : ℝ≥0} {Kcoord : ℝ} (hKcoord : 0 ≤ Kcoord)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i (x : Kc i),
      @norm (TM x.1 →L[ℝ] F) ContinuousLinearMap.hasOpNorm
        ((trivializationAt F TM (x0 i)).continuousLinearMapAt ℝ x.1) ≤ C)
    (picard : IsPicardLindelof A (tmin := t₀) (tmax := T)
      ⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩
      (⟨g₀.toSection, g₀.continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover) a 0 L Kpic)
    (hcoordLip : ∀ τ, τ ∈ Icc t₀ T →
      LipschitzOnWith ⟨Kcoord, hKcoord⟩
        (fun s =>
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF) (V := BilW)
            et Kc hKc Ko hKo hKoEq hcover (A τ s)).1 :
              CoordFamily (F := BilF) Kc))
        (positiveDefiniteLocus
          (M := M) (F := F) (W := TM) et Kc hKc Ko hKo hKoEq hcover))
    (geometric : ∀ τ s, s ∈ positiveDefiniteLocus
        (M := M) (F := F) (W := TM) et Kc hKc Ko hKo hKoEq hcover →
      ∃ (g : MetricFamily (I := I) (M := M))
        (background : ConnectionFamily (I := I) (M := M)),
        ∀ (x : M) (u v : TangentSpace I x),
          A τ s x u v = intrinsicRicciDeTurckRHS (I := I) (M := M) g background τ x u v) :
    Σ Kstate : ℝ≥0,
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T a L Kpic Kstate := by
  let KcoordNN : ℝ≥0 := ⟨Kcoord, hKcoord⟩
  exact timeDependentGeometricRicciDeTurckBanachChartOnIccOfCoordFamilyLipschitzOnWith
    (M := M) (F := F) (I := I)
    x0 et het Kc hKc Ko hKo hKoEq hcover g₀ hT
    (A := A) (a := a) (L := L) (Kpic := Kpic) (Kcoord := KcoordNN)
    hC0 hC picard
    (fun τ hτ => by
      simpa [KcoordNN] using hcoordLip τ hτ)
    geometric

/-- Interval Ricci-DeTurck charts can use the preferred-cover smooth-density theorem directly in the
Picard shrink step.  The remaining density inputs are the finite-cover inverse bound used by the
transported Banach norm and the local tangent-trivialization bound used to smooth bilinear sections. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_localBounds_restrictedSymmetricA_picard
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
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
    {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ i (x : Kc i), ‖(trivializationAt F TM (x0 i)).symmL ℝ x.1‖ ≤ C)
    (hlocalBound : ∀ x : M, ∃ C > 0,
      ∀ᶠ y in 𝓝 x, ‖(trivializationAt F TM x).continuousLinearMapAt ℝ y‖ < C)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T') (hT'le : T' ≤ T),
      ∃ _chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover ∧
          IsPicardLindelof
            (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc
              (M := M) (F := F) (I := I)
              x0 et het Kc hKc Ko hKo hKoEq hcover rhs
              (closure_smooth_spd_of_metric_locus_and_local_trivialization_bounds_preferredBilinear
                (M := M) (F := F) (I := I)
                x0 et het Kc hKc Ko hKo hKoEq hcover hCpos hC hlocalBound)
              (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩))
            (tmin := ivp.initialTime) (tmax := T')
            ⟨ivp.initialTime, ⟨le_rfl, le_of_lt _hT'⟩⟩
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a' 0 L Kpic := by
  exact chart.exists_metricCone_shrunk_specificRHS_closure_restrictedSymmetricA_on_Icc_picard
    (M := M) (F := F) (I := I)
    x0 et het Kc hKc Ko hKo hKoEq hcover rhs
    (closure_smooth_spd_of_metric_locus_and_local_trivialization_bounds_preferredBilinear
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover hCpos hC hlocalBound)
    ha

/-- Interval Ricci-DeTurck charts over a continuous Riemannian tangent bundle can use the
preferred-cover smooth-density theorem directly in the Picard shrink step, without exposing the
finite-cover inverse bound or local trivialization bound as hypotheses. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_continuousRiemannianBundle_restrictedSymmetricA_picard
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    [_root_.Bundle.RiemannianBundle TM]
    [IsContinuousRiemannianBundle (B := M) F TM]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
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
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T') (hT'le : T' ≤ T),
      ∃ _chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover ∧
          IsPicardLindelof
            (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc
              (M := M) (F := F) (I := I)
              x0 et het Kc hKc Ko hKo hKoEq hcover rhs
              (closure_smooth_spd_of_metric_locus_preferredBilinear_of_continuousRiemannianBundle
                (M := M) (F := F) (I := I)
                x0 et het Kc hKc Ko hKo hKoEq hcover)
              (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩))
            (tmin := ivp.initialTime) (tmax := T')
            ⟨ivp.initialTime, ⟨le_rfl, le_of_lt _hT'⟩⟩
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a' 0 L Kpic := by
  exact chart.exists_metricCone_shrunk_specificRHS_closure_restrictedSymmetricA_on_Icc_picard
    (M := M) (F := F) (I := I)
    x0 et het Kc hKc Ko hKo hKoEq hcover rhs
    (closure_smooth_spd_of_metric_locus_preferredBilinear_of_continuousRiemannianBundle
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover)
    ha

/-- The IVP's own smooth initial metric installs the continuous Riemannian tangent-bundle structure
needed by the preferred-cover smooth-density Picard shrink, so callers do not need to provide any
external Riemannian-bundle hypotheses. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_initialMetric_restrictedSymmetricA_picard
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
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
    (ha : 0 < a) :
    let g0 := ivp.initialMetric.toContinuousRiemannianMetric
    letI : _root_.Bundle.RiemannianBundle TM := ⟨g0.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle (B := M) F TM := inferInstance
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T') (hT'le : T' ≤ T),
      ∃ _chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover ∧
          IsPicardLindelof
            (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc
              (M := M) (F := F) (I := I)
              x0 et het Kc hKc Ko hKo hKoEq hcover rhs
              (closure_smooth_spd_of_metric_locus_preferredBilinear_of_continuousRiemannianBundle
                (M := M) (F := F) (I := I)
                x0 et het Kc hKc Ko hKo hKoEq hcover)
              (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩))
            (tmin := ivp.initialTime) (tmax := T')
            ⟨ivp.initialTime, ⟨le_rfl, le_of_lt _hT'⟩⟩
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a' 0 L Kpic := by
  let g0 := ivp.initialMetric.toContinuousRiemannianMetric
  letI : _root_.Bundle.RiemannianBundle TM := ⟨g0.toRiemannianMetric⟩
  haveI : IsContinuousRiemannianBundle (B := M) F TM := inferInstance
  exact
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_continuousRiemannianBundle_restrictedSymmetricA_picard
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover chart rhs ha

/-- The preferred-cover local-bounds route gives an actual state-preserving Banach solution for the
interval-scoped density-based specific-RHS carrier after the same metric-cone shrink. This stops short
of identifying that carrier globally with the ungated chart carrier, but packages the ODE consequence
needed on the Picard interval. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_localBounds_banachEvolutionLocalSolutionIn
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
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
    {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ i (x : Kc i), ‖(trivializationAt F TM (x0 i)).symmL ℝ x.1‖ ≤ C)
    (hlocalBound : ∀ x : M, ∃ C > 0,
      ∀ᶠ y in 𝓝 x, ‖(trivializationAt F TM x).continuousLinearMapAt ℝ y‖ < C)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T') (hT'le : T' ≤ T),
      ∃ _chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover ∧
          (let hclosure :=
            closure_smooth_spd_of_metric_locus_and_local_trivialization_bounds_preferredBilinear
              (M := M) (F := F) (I := I)
              x0 et het Kc hKc Ko hKo hKoEq hcover hCpos hC hlocalBound
           let Asub :=
            SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc
              (M := M) (F := F) (I := I)
              x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
              (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩)
           ∃ sol : BanachEvolutionLocalSolutionIn Asub
              (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                et Kc hKc Ko hKo hKoEq hcover)
              ivp.initialTime
              (InitialValueProblem.toSymmetricSectionSubmodule
                (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
             sol.terminalTime ≤ T' ∧
             ∀ sol' : BanachEvolutionLocalSolutionIn Asub
                (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                  et Kc hKc Ko hKo hKoEq hcover)
                ivp.initialTime
                (InitialValueProblem.toSymmetricSectionSubmodule
                  (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
               EqOn sol.curve sol'.curve
                 (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) := by
  rcases
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_localBounds_restrictedSymmetricA_picard
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover chart rhs hCpos hC hlocalBound ha with
    ⟨T', a', hT', hT'le, chart', ha'pos, ha'le, hball, hpicard⟩
  let hclosure :=
    closure_smooth_spd_of_metric_locus_and_local_trivialization_bounds_preferredBilinear
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover hCpos hC hlocalBound
  let Asub :=
    SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
      (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩)
  have hpicardAsub : IsPicardLindelof Asub
      (tmin := ivp.initialTime) (tmax := T')
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT'⟩⟩
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a' 0 L Kpic := by
    simpa [Asub, hclosure] using hpicard
  have hLip : ∀ t ∈ Icc ivp.initialTime T', LipschitzOnWith Kstate (Asub t)
      (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
        et Kc hKc Ko hKo hKoEq hcover) := by
    simpa [Asub, hclosure] using
      (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc_lipschitzOn_Icc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
        (t₀ := ivp.initialTime) (T := T') (Kstate := Kstate)
        (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩))
  rcases
      exists_unique_in_riemannianMetricLocusSubmodule_of_isPicardLindelof_lipschitzOn_Icc_terminal_le
        (M := M) (F := F) (W := TM)
        x0 et het Kc hKc Ko hKo hKoEq hcover inferInstance hT'
        hpicardAsub
        (InitialValueProblem.toSymmetricSectionSubmodule_mem_riemannianMetricLocusSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)
        hLip with
    ⟨sol, hsolT, huniq⟩
  refine ⟨T', a', hT', hT'le, chart', ha'pos, ha'le, hball, ?_⟩
  exact ⟨sol, hsolT, huniq⟩

/-- Continuous Riemannian tangent bundles give the state-preserving Banach solution for the
interval-scoped density-based specific-RHS carrier without exposing the finite-cover inverse bound or
the local tangent-trivialization bound. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_continuousRiemannianBundle_banachEvolutionLocalSolutionIn
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    [_root_.Bundle.RiemannianBundle TM]
    [IsContinuousRiemannianBundle (B := M) F TM]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
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
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T') (hT'le : T' ≤ T),
      ∃ _chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover ∧
          (let hclosure :=
            closure_smooth_spd_of_metric_locus_preferredBilinear_of_continuousRiemannianBundle
              (M := M) (F := F) (I := I)
              x0 et het Kc hKc Ko hKo hKoEq hcover
           let Asub :=
            SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc
              (M := M) (F := F) (I := I)
              x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
              (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩)
           ∃ sol : BanachEvolutionLocalSolutionIn Asub
              (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                et Kc hKc Ko hKo hKoEq hcover)
              ivp.initialTime
              (InitialValueProblem.toSymmetricSectionSubmodule
                (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
             sol.terminalTime ≤ T' ∧
             ∀ sol' : BanachEvolutionLocalSolutionIn Asub
                (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                  et Kc hKc Ko hKo hKoEq hcover)
                ivp.initialTime
                (InitialValueProblem.toSymmetricSectionSubmodule
                  (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
               EqOn sol.curve sol'.curve
                 (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) := by
  rcases
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_continuousRiemannianBundle_restrictedSymmetricA_picard
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover chart rhs ha with
    ⟨T', a', hT', hT'le, chart', ha'pos, ha'le, hball, hpicard⟩
  let hclosure :=
    closure_smooth_spd_of_metric_locus_preferredBilinear_of_continuousRiemannianBundle
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
  let Asub :=
    SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
      (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩)
  have hpicardAsub : IsPicardLindelof Asub
      (tmin := ivp.initialTime) (tmax := T')
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT'⟩⟩
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a' 0 L Kpic := by
    simpa [Asub, hclosure] using hpicard
  have hLip : ∀ t ∈ Icc ivp.initialTime T', LipschitzOnWith Kstate (Asub t)
      (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
        et Kc hKc Ko hKo hKoEq hcover) := by
    simpa [Asub, hclosure] using
      (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc_lipschitzOn_Icc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
        (t₀ := ivp.initialTime) (T := T') (Kstate := Kstate)
        (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩))
  rcases
      exists_unique_in_riemannianMetricLocusSubmodule_of_isPicardLindelof_lipschitzOn_Icc_terminal_le
        (M := M) (F := F) (W := TM)
        x0 et het Kc hKc Ko hKo hKoEq hcover inferInstance hT'
        hpicardAsub
        (InitialValueProblem.toSymmetricSectionSubmodule_mem_riemannianMetricLocusSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)
        hLip with
    ⟨sol, hsolT, huniq⟩
  refine ⟨T', a', hT', hT'le, chart', ha'pos, ha'le, hball, ?_⟩
  exact ⟨sol, hsolT, huniq⟩

/-- The IVP's own smooth initial metric supplies the continuous Riemannian tangent-bundle structure
needed by the preferred-cover smooth-density route, giving a state-preserving density-carrier Banach
solution without external Riemannian-bundle typeclass assumptions. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_initialMetric_banachEvolutionLocalSolutionIn
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
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
    (ha : 0 < a) :
    let g0 := ivp.initialMetric.toContinuousRiemannianMetric
    letI : _root_.Bundle.RiemannianBundle TM := ⟨g0.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle (B := M) F TM := inferInstance
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T') (hT'le : T' ≤ T),
      ∃ _chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover ∧
          (let hclosure :=
            closure_smooth_spd_of_metric_locus_preferredBilinear_of_continuousRiemannianBundle
              (M := M) (F := F) (I := I)
              x0 et het Kc hKc Ko hKo hKoEq hcover
           let Asub :=
            SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc
              (M := M) (F := F) (I := I)
              x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
              (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩)
           ∃ sol : BanachEvolutionLocalSolutionIn Asub
              (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                et Kc hKc Ko hKo hKoEq hcover)
              ivp.initialTime
              (InitialValueProblem.toSymmetricSectionSubmodule
                (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
             sol.terminalTime ≤ T' ∧
             ∀ sol' : BanachEvolutionLocalSolutionIn Asub
                (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                  et Kc hKc Ko hKo hKoEq hcover)
                ivp.initialTime
                (InitialValueProblem.toSymmetricSectionSubmodule
                  (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
               EqOn sol.curve sol'.curve
                 (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) := by
  let g0 := ivp.initialMetric.toContinuousRiemannianMetric
  letI : _root_.Bundle.RiemannianBundle TM := ⟨g0.toRiemannianMetric⟩
  haveI : IsContinuousRiemannianBundle (B := M) F TM := inferInstance
  exact
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_continuousRiemannianBundle_banachEvolutionLocalSolutionIn
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover chart rhs ha

/-- Proof-level existence readout for the density-based interval carrier produced by the
preferred-cover local-bounds smooth-density Picard shrink. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.nonempty_metricCone_shrunk_specificRHS_localBounds_banachEvolutionLocalSolutionIn
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
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
    {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ i (x : Kc i), ‖(trivializationAt F TM (x0 i)).symmL ℝ x.1‖ ≤ C)
    (hlocalBound : ∀ x : M, ∃ C > 0,
      ∀ᶠ y in 𝓝 x, ‖(trivializationAt F TM x).continuousLinearMapAt ℝ y‖ < C)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T') (hT'le : T' ≤ T),
      ∃ _chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover ∧
          (let hclosure :=
            closure_smooth_spd_of_metric_locus_and_local_trivialization_bounds_preferredBilinear
              (M := M) (F := F) (I := I)
              x0 et het Kc hKc Ko hKo hKoEq hcover hCpos hC hlocalBound
           let Asub :=
            SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc
              (M := M) (F := F) (I := I)
              x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
              (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩)
           Nonempty (BanachEvolutionLocalSolutionIn Asub
             (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
               et Kc hKc Ko hKo hKoEq hcover)
             ivp.initialTime
             (InitialValueProblem.toSymmetricSectionSubmodule
               (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp))) := by
  rcases
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_localBounds_banachEvolutionLocalSolutionIn
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover chart rhs hCpos hC hlocalBound ha with
    ⟨T', a', hT', hT'le, chart', ha'pos, ha'le, hball, hsolData⟩
  rcases hsolData with ⟨sol, _hsolT, _huniq⟩
  exact ⟨T', a', hT', hT'le, chart', ha'pos, ha'le, hball, ⟨sol⟩⟩

/-- Proof-level density-carrier Banach solution existence over a continuous Riemannian tangent bundle,
with the smooth-density bounds discharged internally. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.nonempty_metricCone_shrunk_specificRHS_continuousRiemannianBundle_banachEvolutionLocalSolutionIn
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    [_root_.Bundle.RiemannianBundle TM]
    [IsContinuousRiemannianBundle (B := M) F TM]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
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
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T') (hT'le : T' ≤ T),
      ∃ _chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover ∧
          (let hclosure :=
            closure_smooth_spd_of_metric_locus_preferredBilinear_of_continuousRiemannianBundle
              (M := M) (F := F) (I := I)
              x0 et het Kc hKc Ko hKo hKoEq hcover
           let Asub :=
            SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc
              (M := M) (F := F) (I := I)
              x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
              (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩)
           Nonempty (BanachEvolutionLocalSolutionIn Asub
             (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
               et Kc hKc Ko hKo hKoEq hcover)
             ivp.initialTime
             (InitialValueProblem.toSymmetricSectionSubmodule
               (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp))) := by
  rcases
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_continuousRiemannianBundle_banachEvolutionLocalSolutionIn
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover chart rhs ha with
    ⟨T', a', hT', hT'le, chart', ha'pos, ha'le, hball, hsolData⟩
  rcases hsolData with ⟨sol, _hsolT, _huniq⟩
  exact ⟨T', a', hT', hT'le, chart', ha'pos, ha'le, hball, ⟨sol⟩⟩

/-- Proof-level density-carrier Banach solution existence using the IVP's own smooth initial metric to
install the continuous Riemannian tangent-bundle structure internally. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.nonempty_metricCone_shrunk_specificRHS_initialMetric_banachEvolutionLocalSolutionIn
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
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
    (ha : 0 < a) :
    let g0 := ivp.initialMetric.toContinuousRiemannianMetric
    letI : _root_.Bundle.RiemannianBundle TM := ⟨g0.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle (B := M) F TM := inferInstance
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T') (hT'le : T' ≤ T),
      ∃ _chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover ∧
          (let hclosure :=
            closure_smooth_spd_of_metric_locus_preferredBilinear_of_continuousRiemannianBundle
              (M := M) (F := F) (I := I)
              x0 et het Kc hKc Ko hKo hKoEq hcover
           let Asub :=
            SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc
              (M := M) (F := F) (I := I)
              x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
              (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩)
           Nonempty (BanachEvolutionLocalSolutionIn Asub
             (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
               et Kc hKc Ko hKo hKoEq hcover)
             ivp.initialTime
             (InitialValueProblem.toSymmetricSectionSubmodule
               (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp))) := by
  rcases
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_initialMetric_banachEvolutionLocalSolutionIn
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover chart rhs ha with
    ⟨T', a', hT', hT'le, chart', ha'pos, ha'le, hball, hsolData⟩
  rcases hsolData with ⟨sol, _hsolT, _huniq⟩
  exact ⟨T', a', hT', hT'le, chart', ha'pos, ha'le, hball, ⟨sol⟩⟩
/-- The preferred-cover local-bounds route also gives an actual state-preserving Banach solution for
the chart-derived restricted symmetric carrier. Existence is transported from the density-based
interval carrier on the shrunken Picard interval, while uniqueness is read from the chart carrier's
own Lipschitz control on the Riemannian metric locus. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_localBounds_chartRestrictedSymmetricA_banachEvolutionLocalSolutionIn
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
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
    {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ i (x : Kc i), ‖(trivializationAt F TM (x0 i)).symmL ℝ x.1‖ ≤ C)
    (hlocalBound : ∀ x : M, ∃ C > 0,
      ∀ᶠ y in 𝓝 x, ‖(trivializationAt F TM x).continuousLinearMapAt ℝ y‖ < C)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T') (_hT'le : T' ≤ T),
      ∃ _htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
        a' - (0 : ℝ≥0),
      ∃ chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover ∧
          ∃ sol : BanachEvolutionLocalSolutionIn
              (chart'.restrictedSymmetricA
                (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
              (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                et Kc hKc Ko hKo hKoEq hcover)
              ivp.initialTime
              (InitialValueProblem.toSymmetricSectionSubmodule
                (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
             sol.terminalTime ≤ T' ∧
             ∀ sol' : BanachEvolutionLocalSolutionIn
                (chart'.restrictedSymmetricA
                  (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
                (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                  et Kc hKc Ko hKo hKoEq hcover)
                ivp.initialTime
                (InitialValueProblem.toSymmetricSectionSubmodule
                  (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
               EqOn sol.curve sol'.curve
                 (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime)) := by
  rcases chart.exists_metricCone_shrink_parameters
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover ha with
    ⟨T', a', hT', hT'le, ha'pos, ha'le, htime, hball⟩
  let chart' := chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha'le htime
  let hclosure :=
    closure_smooth_spd_of_metric_locus_and_local_trivialization_bounds_preferredBilinear
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover hCpos hC hlocalBound
  let Asub :=
    SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
      (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩)
  have hpicardAmb : IsPicardLindelof chart.A
      (tmin := ivp.initialTime) (tmax := T')
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT'⟩⟩
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)
      a' 0 L Kpic := by
    simpa [chart', TimeDependentGeometricRicciDeTurckBanachChartOnIcc.shrink] using
      chart'.picard
  have hpicardAsub : IsPicardLindelof Asub
      (tmin := ivp.initialTime) (tmax := T')
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT'⟩⟩
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a' 0 L Kpic := by
    have hpicard :=
      SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc_picard_of_closedBall_subset_riemannianMetricLocus
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hT'
        hpicardAmb (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩) hball
    simpa [Asub, hclosure] using hpicard
  have hLipAsub : ∀ t ∈ Icc ivp.initialTime T', LipschitzOnWith Kstate (Asub t)
      (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
        et Kc hKc Ko hKo hKoEq hcover) := by
    simpa [Asub, hclosure] using
      (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc_lipschitzOn_Icc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
        (t₀ := ivp.initialTime) (T := T') (Kstate := Kstate)
        (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩))
  rcases
      exists_unique_in_riemannianMetricLocusSubmodule_of_isPicardLindelof_lipschitzOn_Icc_terminal_le
        (M := M) (F := F) (W := TM)
        x0 et het Kc hKc Ko hKo hKoEq hcover inferInstance hT'
        hpicardAsub
        (InitialValueProblem.toSymmetricSectionSubmodule_mem_riemannianMetricLocusSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)
        hLipAsub with
    ⟨solDensity, hsolDensityT, _huniqDensity⟩
  let solChart : BanachEvolutionLocalSolutionIn
      (chart'.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
        et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) :=
    { terminalTime := solDensity.terminalTime
      initial_lt_terminal := solDensity.initial_lt_terminal
      curve := solDensity.curve
      initial_eq := solDensity.initial_eq
      equation := by
        intro t ht
        have htT' : t ∈ Icc ivp.initialTime T' :=
          ⟨ht.1, le_trans ht.2 hsolDensityT⟩
        have hEq :
            (chart'.restrictedSymmetricA
              (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) t
              (solDensity.curve t) =
            Asub t (solDensity.curve t) := by
          apply Subtype.ext
          calc
            ((chart'.restrictedSymmetricA
              (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) t
                (solDensity.curve t) :
                ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
                  et Kc hKc Ko hKo hKoEq hcover) =
                chart'.A t (solDensity.curve t :
                  ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
                    et Kc hKc Ko hKo hKoEq hcover) := by
              simpa using chart'.restrictedSymmetricA_coe_of_mem
                (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover
                t (solDensity.curve t) (solDensity.mem_state ht)
            _ =
                chart.A t (solDensity.curve t :
                  ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
                    et Kc hKc Ko hKo hKoEq hcover) := by
              simp [chart', TimeDependentGeometricRicciDeTurckBanachChartOnIcc.shrink]
            _ =
                (Asub t (solDensity.curve t) :
                  ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
                    et Kc hKc Ko hKo hKoEq hcover) := by
              simpa [Asub, hclosure] using
                (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc_coe_of_mem
                  (M := M) (F := F) (I := I)
                  x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
                  (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩)
                  t htT' (solDensity.curve t) (solDensity.mem_state ht)).symm
        simpa [Asub, hEq] using solDensity.toBanachEvolutionLocalSolution.equation ht
      mem_state := solDensity.mem_state }
  have huniqChart :
      ∀ sol' : BanachEvolutionLocalSolutionIn
          (chart'.restrictedSymmetricA
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
          (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
            et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toSymmetricSectionSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn solChart.curve sol'.curve
          (Icc ivp.initialTime (min solChart.terminalTime sol'.terminalTime)) := by
    intro sol'
    refine BanachEvolutionLocalSolutionIn.eqOn_Icc_of_lipschitzOn_Icc
      (K := Kstate) solChart sol' ?_
    intro t ht
    exact chart'.restrictedSymmetricA_lipschitzOn_Icc
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover
      t ⟨ht.1, le_trans ht.2 (le_trans (min_le_left _ _) hsolDensityT)⟩
  exact
    ⟨T', a', hT', hT'le, htime, chart', ha'pos, ha'le, hball,
      solChart, hsolDensityT, huniqChart⟩

/-- Continuous Riemannian tangent bundles give the state-preserving Banach solution for the
chart-derived restricted symmetric carrier without exposing the finite-cover inverse bound or the
local tangent-trivialization bound. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_continuousRiemannianBundle_chartRestrictedSymmetricA_banachEvolutionLocalSolutionIn
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    [_root_.Bundle.RiemannianBundle TM]
    [IsContinuousRiemannianBundle (B := M) F TM]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
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
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T') (_hT'le : T' ≤ T),
      ∃ _htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
        a' - (0 : ℝ≥0),
      ∃ chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover ∧
          ∃ sol : BanachEvolutionLocalSolutionIn
              (chart'.restrictedSymmetricA
                (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
              (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                et Kc hKc Ko hKo hKoEq hcover)
              ivp.initialTime
              (InitialValueProblem.toSymmetricSectionSubmodule
                (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
             sol.terminalTime ≤ T' ∧
             ∀ sol' : BanachEvolutionLocalSolutionIn
                (chart'.restrictedSymmetricA
                  (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
                (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                  et Kc hKc Ko hKo hKoEq hcover)
                ivp.initialTime
                (InitialValueProblem.toSymmetricSectionSubmodule
                  (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
               EqOn sol.curve sol'.curve
                 (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime)) := by
  rcases chart.exists_metricCone_shrink_parameters
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover ha with
    ⟨T', a', hT', hT'le, ha'pos, ha'le, htime, hball⟩
  let chart' := chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha'le htime
  let hclosure :=
    closure_smooth_spd_of_metric_locus_preferredBilinear_of_continuousRiemannianBundle
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
  let Asub :=
    SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
      (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩)
  have hpicardAmb : IsPicardLindelof chart.A
      (tmin := ivp.initialTime) (tmax := T')
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT'⟩⟩
      (InitialValueProblem.toContinuousSectionSpace
        (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)
      a' 0 L Kpic := by
    simpa [chart', TimeDependentGeometricRicciDeTurckBanachChartOnIcc.shrink] using
      chart'.picard
  have hpicardAsub : IsPicardLindelof Asub
      (tmin := ivp.initialTime) (tmax := T')
      ⟨ivp.initialTime, ⟨le_rfl, le_of_lt hT'⟩⟩
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) a' 0 L Kpic := by
    have hpicard :=
      SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc_picard_of_closedBall_subset_riemannianMetricLocus
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure hT'
        hpicardAmb (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩) hball
    simpa [Asub, hclosure] using hpicard
  have hLipAsub : ∀ t ∈ Icc ivp.initialTime T', LipschitzOnWith Kstate (Asub t)
      (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
        et Kc hKc Ko hKo hKoEq hcover) := by
    simpa [Asub, hclosure] using
      (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc_lipschitzOn_Icc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
        (t₀ := ivp.initialTime) (T := T') (Kstate := Kstate)
        (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩))
  rcases
      exists_unique_in_riemannianMetricLocusSubmodule_of_isPicardLindelof_lipschitzOn_Icc_terminal_le
        (M := M) (F := F) (W := TM)
        x0 et het Kc hKc Ko hKo hKoEq hcover inferInstance hT'
        hpicardAsub
        (InitialValueProblem.toSymmetricSectionSubmodule_mem_riemannianMetricLocusSubmodule
          (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)
        hLipAsub with
    ⟨solDensity, hsolDensityT, _huniqDensity⟩
  let solChart : BanachEvolutionLocalSolutionIn
      (chart'.restrictedSymmetricA
        (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
      (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
        et Kc hKc Ko hKo hKoEq hcover)
      ivp.initialTime
      (InitialValueProblem.toSymmetricSectionSubmodule
        (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) :=
    { terminalTime := solDensity.terminalTime
      initial_lt_terminal := solDensity.initial_lt_terminal
      curve := solDensity.curve
      initial_eq := solDensity.initial_eq
      equation := by
        intro t ht
        have htT' : t ∈ Icc ivp.initialTime T' :=
          ⟨ht.1, le_trans ht.2 hsolDensityT⟩
        have hEq :
            (chart'.restrictedSymmetricA
              (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) t
              (solDensity.curve t) =
            Asub t (solDensity.curve t) := by
          apply Subtype.ext
          calc
            ((chart'.restrictedSymmetricA
              (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover) t
                (solDensity.curve t) :
                ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
                  et Kc hKc Ko hKo hKoEq hcover) =
                chart'.A t (solDensity.curve t :
                  ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
                    et Kc hKc Ko hKo hKoEq hcover) := by
              simpa using chart'.restrictedSymmetricA_coe_of_mem
                (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover
                t (solDensity.curve t) (solDensity.mem_state ht)
            _ =
                chart.A t (solDensity.curve t :
                  ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
                    et Kc hKc Ko hKo hKoEq hcover) := by
              simp [chart', TimeDependentGeometricRicciDeTurckBanachChartOnIcc.shrink]
            _ =
                (Asub t (solDensity.curve t) :
                  ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
                    et Kc hKc Ko hKo hKoEq hcover) := by
              simpa [Asub, hclosure] using
                (SmoothSectionRHSIdentification.restrictedSymmetricA_of_closure_smooth_spd_on_Icc_coe_of_mem
                  (M := M) (F := F) (I := I)
                  x0 et het Kc hKc Ko hKo hKoEq hcover rhs hclosure
                  (fun t ht => chart.lipschitzOn_Icc t ⟨ht.1, le_trans ht.2 hT'le⟩)
                  t htT' (solDensity.curve t) (solDensity.mem_state ht)).symm
        simpa [Asub, hEq] using solDensity.toBanachEvolutionLocalSolution.equation ht
      mem_state := solDensity.mem_state }
  have huniqChart :
      ∀ sol' : BanachEvolutionLocalSolutionIn
          (chart'.restrictedSymmetricA
            (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
          (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
            et Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (InitialValueProblem.toSymmetricSectionSubmodule
            (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
        EqOn solChart.curve sol'.curve
          (Icc ivp.initialTime (min solChart.terminalTime sol'.terminalTime)) := by
    intro sol'
    refine BanachEvolutionLocalSolutionIn.eqOn_Icc_of_lipschitzOn_Icc
      (K := Kstate) solChart sol' ?_
    intro t ht
    exact chart'.restrictedSymmetricA_lipschitzOn_Icc
      (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover
      t ⟨ht.1, le_trans ht.2 (le_trans (min_le_left _ _) hsolDensityT)⟩
  exact
    ⟨T', a', hT', hT'le, htime, chart', ha'pos, ha'le, hball,
      solChart, hsolDensityT, huniqChart⟩

/-- The IVP's own smooth initial metric supplies the continuous Riemannian tangent-bundle structure
needed by the preferred-cover smooth-density route, giving a chart-restricted Banach solution without
external Riemannian-bundle typeclass assumptions. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_initialMetric_chartRestrictedSymmetricA_banachEvolutionLocalSolutionIn
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
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
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T') (_hT'le : T' ≤ T),
      ∃ _htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
        a' - (0 : ℝ≥0),
      ∃ chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover ∧
          ∃ sol : BanachEvolutionLocalSolutionIn
              (chart'.restrictedSymmetricA
                (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
              (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                et Kc hKc Ko hKo hKoEq hcover)
              ivp.initialTime
              (InitialValueProblem.toSymmetricSectionSubmodule
                (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
             sol.terminalTime ≤ T' ∧
             ∀ sol' : BanachEvolutionLocalSolutionIn
                (chart'.restrictedSymmetricA
                  (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
                (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                  et Kc hKc Ko hKo hKoEq hcover)
                ivp.initialTime
                (InitialValueProblem.toSymmetricSectionSubmodule
                  (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
               EqOn sol.curve sol'.curve
                 (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime)) := by
  let g0 := ivp.initialMetric.toContinuousRiemannianMetric
  letI : _root_.Bundle.RiemannianBundle TM := ⟨g0.toRiemannianMetric⟩
  haveI : IsContinuousRiemannianBundle (B := M) F TM := inferInstance
  exact
    TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_continuousRiemannianBundle_chartRestrictedSymmetricA_banachEvolutionLocalSolutionIn
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover chart rhs ha

/-- Proof-level chart-carrier Banach solution existence from the preferred-cover local-bounds
smooth-density Picard shrink. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.nonempty_metricCone_shrunk_specificRHS_localBounds_chartRestrictedSymmetricA_banachEvolutionLocalSolutionIn
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
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
    {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ i (x : Kc i), ‖(trivializationAt F TM (x0 i)).symmL ℝ x.1‖ ≤ C)
    (hlocalBound : ∀ x : M, ∃ C > 0,
      ∀ᶠ y in 𝓝 x, ‖(trivializationAt F TM x).continuousLinearMapAt ℝ y‖ < C)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T') (_hT'le : T' ≤ T),
      ∃ chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover ∧
          Nonempty (BanachEvolutionLocalSolutionIn
            (chart'.restrictedSymmetricA
              (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
            (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover)
            ivp.initialTime
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)) := by
  rcases
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_localBounds_chartRestrictedSymmetricA_banachEvolutionLocalSolutionIn
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover chart rhs hCpos hC hlocalBound ha with
    ⟨T', a', hT', hT'le, _htime, chart', ha'pos, ha'le, hball,
      sol, _hsolT, _huniq⟩
  exact ⟨T', a', hT', hT'le, chart', ha'pos, ha'le, hball, ⟨sol⟩⟩

/-- Terminal-time and uniqueness retaining proof-level chart-carrier Banach solution from the
preferred-cover local-bounds smooth-density Picard shrink. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.nonempty_metricCone_shrunk_specificRHS_localBounds_chartRestrictedSymmetricA_banachEvolutionLocalSolutionIn_unique
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
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
    {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ i (x : Kc i), ‖(trivializationAt F TM (x0 i)).symmL ℝ x.1‖ ≤ C)
    (hlocalBound : ∀ x : M, ∃ C > 0,
      ∀ᶠ y in 𝓝 x, ‖(trivializationAt F TM x).continuousLinearMapAt ℝ y‖ < C)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T') (_hT'le : T' ≤ T),
      ∃ chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover ∧
          Nonempty { sol : BanachEvolutionLocalSolutionIn
              (chart'.restrictedSymmetricA
                (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
              (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                et Kc hKc Ko hKo hKoEq hcover)
              ivp.initialTime
              (InitialValueProblem.toSymmetricSectionSubmodule
                (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) //
            sol.terminalTime ≤ T' ∧
              ∀ sol' : BanachEvolutionLocalSolutionIn
                (chart'.restrictedSymmetricA
                  (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
                (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                  et Kc hKc Ko hKo hKoEq hcover)
                ivp.initialTime
                (InitialValueProblem.toSymmetricSectionSubmodule
                  (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
              EqOn sol.curve sol'.curve
                (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime)) } := by
  rcases
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_localBounds_chartRestrictedSymmetricA_banachEvolutionLocalSolutionIn
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover chart rhs hCpos hC hlocalBound ha with
    ⟨T', a', hT', hT'le, _htime, chart', ha'pos, ha'le, hball,
      sol, hsolT, huniq⟩
  exact ⟨T', a', hT', hT'le, chart', ha'pos, ha'le, hball, ⟨⟨sol, hsolT, huniq⟩⟩⟩

/-- Proof-level chart-carrier Banach solution existence over a continuous Riemannian tangent bundle,
with the smooth-density bounds discharged internally. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.nonempty_metricCone_shrunk_specificRHS_continuousRiemannianBundle_chartRestrictedSymmetricA_banachEvolutionLocalSolutionIn
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    [_root_.Bundle.RiemannianBundle TM]
    [IsContinuousRiemannianBundle (B := M) F TM]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
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
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T') (_hT'le : T' ≤ T),
      ∃ chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover ∧
          Nonempty (BanachEvolutionLocalSolutionIn
            (chart'.restrictedSymmetricA
              (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
            (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover)
            ivp.initialTime
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)) := by
  rcases
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_continuousRiemannianBundle_chartRestrictedSymmetricA_banachEvolutionLocalSolutionIn
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover chart rhs ha with
    ⟨T', a', hT', hT'le, _htime, chart', ha'pos, ha'le, hball,
      sol, _hsolT, _huniq⟩
  exact ⟨T', a', hT', hT'le, chart', ha'pos, ha'le, hball, ⟨sol⟩⟩

/-- Terminal-time and uniqueness retaining proof-level chart-carrier Banach solution over a
continuous Riemannian tangent bundle, with the smooth-density bounds discharged internally. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.nonempty_metricCone_shrunk_specificRHS_continuousRiemannianBundle_chartRestrictedSymmetricA_banachEvolutionLocalSolutionIn_unique
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    [_root_.Bundle.RiemannianBundle TM]
    [IsContinuousRiemannianBundle (B := M) F TM]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
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
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T') (_hT'le : T' ≤ T),
      ∃ chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover ∧
          Nonempty { sol : BanachEvolutionLocalSolutionIn
              (chart'.restrictedSymmetricA
                (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
              (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                et Kc hKc Ko hKo hKoEq hcover)
              ivp.initialTime
              (InitialValueProblem.toSymmetricSectionSubmodule
                (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) //
            sol.terminalTime ≤ T' ∧
              ∀ sol' : BanachEvolutionLocalSolutionIn
                (chart'.restrictedSymmetricA
                  (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
                (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                  et Kc hKc Ko hKo hKoEq hcover)
                ivp.initialTime
                (InitialValueProblem.toSymmetricSectionSubmodule
                  (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
              EqOn sol.curve sol'.curve
                (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime)) } := by
  rcases
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_continuousRiemannianBundle_chartRestrictedSymmetricA_banachEvolutionLocalSolutionIn
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover chart rhs ha with
    ⟨T', a', hT', hT'le, _htime, chart', ha'pos, ha'le, hball,
      sol, hsolT, huniq⟩
  exact ⟨T', a', hT', hT'le, chart', ha'pos, ha'le, hball, ⟨⟨sol, hsolT, huniq⟩⟩⟩

/-- Proof-level chart-carrier Banach solution existence using the IVP's own smooth initial metric to
install the continuous Riemannian tangent-bundle structure internally. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.nonempty_metricCone_shrunk_specificRHS_initialMetric_chartRestrictedSymmetricA_banachEvolutionLocalSolutionIn
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
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
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T') (_hT'le : T' ≤ T),
      ∃ chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover ∧
          Nonempty (BanachEvolutionLocalSolutionIn
            (chart'.restrictedSymmetricA
              (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
            (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover)
            ivp.initialTime
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp)) := by
  rcases
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_initialMetric_chartRestrictedSymmetricA_banachEvolutionLocalSolutionIn
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover chart rhs ha with
    ⟨T', a', hT', hT'le, _htime, chart', ha'pos, ha'le, hball,
      sol, _hsolT, _huniq⟩
  exact ⟨T', a', hT', hT'le, chart', ha'pos, ha'le, hball, ⟨sol⟩⟩

/-- Terminal-time and uniqueness retaining proof-level chart-carrier Banach solution from the
preferred-cover smooth-density Picard shrink, using the IVP's own smooth initial metric to install
the continuous Riemannian tangent-bundle structure internally. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.nonempty_metricCone_shrunk_specificRHS_initialMetric_chartRestrictedSymmetricA_banachEvolutionLocalSolutionIn_unique
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
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
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T') (_hT'le : T' ≤ T),
      ∃ chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧ a' ≤ a ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover ∧
          Nonempty { sol : BanachEvolutionLocalSolutionIn
              (chart'.restrictedSymmetricA
                (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
              (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                et Kc hKc Ko hKo hKoEq hcover)
              ivp.initialTime
              (InitialValueProblem.toSymmetricSectionSubmodule
                (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) //
            sol.terminalTime ≤ T' ∧
              ∀ sol' : BanachEvolutionLocalSolutionIn
                (chart'.restrictedSymmetricA
                  (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
                (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                  et Kc hKc Ko hKo hKoEq hcover)
                ivp.initialTime
                (InitialValueProblem.toSymmetricSectionSubmodule
                  (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
              EqOn sol.curve sol'.curve
                (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime)) } := by
  rcases
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_initialMetric_chartRestrictedSymmetricA_banachEvolutionLocalSolutionIn
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover chart rhs ha with
    ⟨T', a', hT', hT'le, _htime, chart', ha'pos, ha'le, hball,
      sol, hsolT, huniq⟩
  exact ⟨T', a', hT', hT'le, chart', ha'pos, ha'le, hball, ⟨⟨sol, hsolT, huniq⟩⟩⟩

/-- The initial-metric smooth-approximation route can share one selected metric-cone shrink between
the chart-carrier Banach solution and the ambient closure-data local uniqueness readouts.  The
solution witness comes from the density-based specific-RHS route transported to the chart's
restricted carrier; the metric and connection readouts come from the supplied interval closure
data on that same selected clipped interval. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_initialMetric_chartRestrictedSymmetricA_solution_localMetricConnectionReadout
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
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
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover chart.A)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T') (_hT'le : T' ≤ T)
      (_ha' : a' ≤ a)
      (_htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
        a' - (0 : ℝ≥0)),
      ∃ chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover ∧
          (∃ sol : BanachEvolutionLocalSolutionIn
              (chart'.restrictedSymmetricA
                (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
              (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                et Kc hKc Ko hKo hKoEq hcover)
              ivp.initialTime
              (InitialValueProblem.toSymmetricSectionSubmodule
                (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
             sol.terminalTime ≤ T' ∧
             ∀ sol' : BanachEvolutionLocalSolutionIn
                (chart'.restrictedSymmetricA
                  (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
                (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                  et Kc hKc Ko hKo hKoEq hcover)
                ivp.initialTime
                (InitialValueProblem.toSymmetricSectionSubmodule
                  (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
               EqOn sol.curve sol'.curve
                 (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
          (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
              (E := F) (H := H) (I := I) (M := M) ivp) {t : ℝ},
            t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T') →
            ∀ (x : M) (u v : TM x),
              metricTensor (I := I) (M := M)
                sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
                  metricTensor (I := I) (M := M)
                    sol₂.1.toIntrinsicDeTurckSolution.metric t x u v) ∧
          (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
              (E := F) (H := H) (I := I) (M := M) ivp) {t : ℝ},
            t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T') →
            ∀ {x : M} {σ : Π y : M, TM y},
              MDiffAt (T% σ) x →
              sol₁.1.canonicalConnection
                (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
                sol₂.1.canonicalConnection
                  (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2)
                  t σ x) := by
  rcases
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_initialMetric_chartRestrictedSymmetricA_banachEvolutionLocalSolutionIn
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover chart rhs ha with
    ⟨T', a', hT', hT'le, htime, chart', ha'pos, ha'le, hball, sol, hsolT, huniq⟩
  refine ⟨T', a', hT', hT'le, ha'le, htime, chart', ha'pos, hball, ?_, ?_, ?_⟩
  · exact ⟨sol, hsolT, huniq⟩
  · intro sol₁ sol₂ t ht x u v
    exact
      RicciDeTurckChartClosureDataOnIcc.metric_eq_on_common_interval_clipped_shrink_of_shrunk_symmetricCarrier
        (M := M) (F := F) (I := I) (D := D)
        hT' hT'le ha'le htime sol₁ sol₂ ht x u v
  · intro sol₁ sol₂ t ht x σ hσ
    exact
      RicciDeTurckChartClosureDataOnIcc.connection_eq_on_common_interval_clipped_shrink_of_shrunk_symmetricCarrier
        (M := M) (F := F) (I := I) (D := D)
        hT' hT'le ha'le htime sol₁ sol₂ ht hσ

/-- The initial-metric smooth-approximation route can share one selected
metric-cone shrink between the chart-carrier Banach solution and prescribed
shorter-terminal ambient closure-data metric/connection readouts.  This is the
continuation-oriented version of
`exists_metricCone_shrunk_specificRHS_initialMetric_chartRestrictedSymmetricA_solution_localMetricConnectionReadout`. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_initialMetric_chartRestrictedSymmetricA_solution_localRestrictedMetricConnectionReadout
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
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
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover chart.A)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T') (_hT'le : T' ≤ T)
      (_ha' : a' ≤ a)
      (_htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
        a' - (0 : ℝ≥0)),
      ∃ chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover ∧
          (∃ sol : BanachEvolutionLocalSolutionIn
              (chart'.restrictedSymmetricA
                (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
              (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                et Kc hKc Ko hKo hKoEq hcover)
              ivp.initialTime
              (InitialValueProblem.toSymmetricSectionSubmodule
                (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
             sol.terminalTime ≤ T' ∧
             ∀ sol' : BanachEvolutionLocalSolutionIn
                (chart'.restrictedSymmetricA
                  (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
                (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                  et Kc hKc Ko hKo hKoEq hcover)
                ivp.initialTime
                (InitialValueProblem.toSymmetricSectionSubmodule
                  (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
               EqOn sol.curve sol'.curve
                 (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
          (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
              (E := F) (H := H) (I := I) (M := M) ivp) {S : ℝ},
            ivp.initialTime < S → S ≤ sol₁.1.terminalTime →
            S ≤ sol₂.1.terminalTime → S ≤ T' → ∀ {t : ℝ},
            t ∈ Icc ivp.initialTime S → ∀ (x : M) (u v : TM x),
              metricTensor (I := I) (M := M)
                sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
                  metricTensor (I := I) (M := M)
                    sol₂.1.toIntrinsicDeTurckSolution.metric t x u v) ∧
          (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
              (E := F) (H := H) (I := I) (M := M) ivp) {S : ℝ},
            ivp.initialTime < S → S ≤ sol₁.1.terminalTime →
            S ≤ sol₂.1.terminalTime → S ≤ T' → ∀ {t : ℝ},
            t ∈ Icc ivp.initialTime S →
            ∀ {x : M} {σ : Π y : M, TM y},
              MDiffAt (T% σ) x →
              sol₁.1.canonicalConnection
                (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
                sol₂.1.canonicalConnection
                  (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2)
                  t σ x) := by
  rcases
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_initialMetric_chartRestrictedSymmetricA_banachEvolutionLocalSolutionIn
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover chart rhs ha with
    ⟨T', a', hT', hT'le, htime, chart', ha'pos, ha'le, hball, sol, hsolT, huniq⟩
  refine ⟨T', a', hT', hT'le, ha'le, htime, chart', ha'pos, hball, ?_, ?_, ?_⟩
  · exact ⟨sol, hsolT, huniq⟩
  · intro sol₁ sol₂ S hS₀ hS₁ hS₂ hST' t ht x u v
    exact
      RicciDeTurckChartClosureDataOnIcc.metric_eq_on_restricted_interval_of_shrunk_symmetricCarrier
        (M := M) (F := F) (I := I) (D := D)
        hT' hT'le ha'le htime sol₁ sol₂ hS₀ hS₁ hS₂ hST' ht x u v
  · intro sol₁ sol₂ S hS₀ hS₁ hS₂ hST' t ht x σ hσ
    exact
      RicciDeTurckChartClosureDataOnIcc.connection_eq_on_restricted_interval_of_shrunk_symmetricCarrier
        (M := M) (F := F) (I := I) (D := D)
        hT' hT'le ha'le htime sol₁ sol₂ hS₀ hS₁ hS₂ hST' ht hσ

/-- The initial-metric smooth-approximation route can share one selected
metric-cone shrink between the chart-carrier Banach solution, the terminal-fit
theorem-package handoff, and prescribed shorter-terminal ambient closure-data
metric/connection readouts.  This keeps the Banach solution and the continuation
readouts tied to the same shrink used by the theorem-package route. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_initialMetric_chartRestrictedSymmetricA_solution_theoremPackages_localRestrictedMetricConnectionReadout
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
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
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover chart.A)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T') (_hT'le : T' ≤ T)
      (_ha' : a' ≤ a)
      (_htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
        a' - (0 : ℝ≥0)),
      ∃ chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover ∧
          (∃ sol : BanachEvolutionLocalSolutionIn
              (chart'.restrictedSymmetricA
                (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
              (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                et Kc hKc Ko hKo hKoEq hcover)
              ivp.initialTime
              (InitialValueProblem.toSymmetricSectionSubmodule
                (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
             sol.terminalTime ≤ T' ∧
             ∀ sol' : BanachEvolutionLocalSolutionIn
                (chart'.restrictedSymmetricA
                  (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
                (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                  et Kc hKc Ko hKo hKoEq hcover)
                ivp.initialTime
                (InitialValueProblem.toSymmetricSectionSubmodule
                  (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
               EqOn sol.curve sol'.curve
                 (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
          (((∀ candidate : ChosenIntrinsicDeTurckLocalSolution
              (E := F) (H := H) (I := I) (M := M) ivp,
            (D.encode candidate).sol.terminalTime ≤ T') →
            Nonempty (ChosenIntrinsicDeTurckLocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp) ∧
            Nonempty (IntrinsicLocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp) ∧
            Nonempty (LocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp)) ∧
          (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
              (E := F) (H := H) (I := I) (M := M) ivp) {S : ℝ},
            ivp.initialTime < S → S ≤ sol₁.1.terminalTime →
            S ≤ sol₂.1.terminalTime → S ≤ T' → ∀ {t : ℝ},
            t ∈ Icc ivp.initialTime S → ∀ (x : M) (u v : TM x),
              metricTensor (I := I) (M := M)
                sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
                  metricTensor (I := I) (M := M)
                    sol₂.1.toIntrinsicDeTurckSolution.metric t x u v) ∧
          (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
              (E := F) (H := H) (I := I) (M := M) ivp) {S : ℝ},
            ivp.initialTime < S → S ≤ sol₁.1.terminalTime →
            S ≤ sol₂.1.terminalTime → S ≤ T' → ∀ {t : ℝ},
            t ∈ Icc ivp.initialTime S →
            ∀ {x : M} {σ : Π y : M, TM y},
              MDiffAt (T% σ) x →
              sol₁.1.canonicalConnection
                (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
                sol₂.1.canonicalConnection
                  (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2)
                  t σ x)) := by
  rcases
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_initialMetric_chartRestrictedSymmetricA_solution_localRestrictedMetricConnectionReadout
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover chart D rhs ha with
    ⟨T', a', hT', hT'le, ha'le, htime, chart', ha'pos, hball,
      hsolution, hmetric, hconnection⟩
  refine
    ⟨T', a', hT', hT'le, ha'le, htime, chart', ha'pos, hball,
      hsolution, ?_, hmetric, hconnection⟩
  intro hencode_terminal
  let chartShrink :=
    chart.shrink (M := M) (F := F) (I := I) hT' hT'le ha'le htime
  let Dsym : SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc
      x0 et het Kc hKc Ko hKo hKoEq hcover chartShrink :=
    SymmetricSubmoduleRicciDeTurckChartClosureDataOnIcc.ofShrunkRicciDeTurckChartClosureDataOnIcc
      (M := M) (F := F) (I := I) (D := D)
      hT' hT'le ha'le htime hball hencode_terminal
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨Dsym.toChosenIntrinsicDeTurckLocalExistenceUniqueness⟩
  · exact ⟨Dsym.toIntrinsicLocalExistenceUniqueness⟩
  · exact ⟨Dsym.toLocalExistenceUniqueness⟩

/-- The initial-metric smooth-approximation route can keep the strongest
continuation-facing readouts on a single selected metric-cone shrink: a
chart-carrier Banach solution, the terminal-fit theorem-package handoff,
prescribed shorter-terminal metric/connection uniqueness, and full-common
readouts when the same shrink contains the common candidate terminal. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_initialMetric_chartRestrictedSymmetricA_solution_theoremPackages_localRestrictedMetricConnectionReadout_with_fullCommon
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
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
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover chart.A)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T') (_hT'le : T' ≤ T)
      (_ha' : a' ≤ a)
      (_htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
        a' - (0 : ℝ≥0)),
      ∃ chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover ∧
          (∃ sol : BanachEvolutionLocalSolutionIn
              (chart'.restrictedSymmetricA
                (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
              (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                et Kc hKc Ko hKo hKoEq hcover)
              ivp.initialTime
              (InitialValueProblem.toSymmetricSectionSubmodule
                (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
             sol.terminalTime ≤ T' ∧
             ∀ sol' : BanachEvolutionLocalSolutionIn
                (chart'.restrictedSymmetricA
                  (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
                (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                  et Kc hKc Ko hKo hKoEq hcover)
                ivp.initialTime
                (InitialValueProblem.toSymmetricSectionSubmodule
                  (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
               EqOn sol.curve sol'.curve
                 (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
          (((∀ candidate : ChosenIntrinsicDeTurckLocalSolution
              (E := F) (H := H) (I := I) (M := M) ivp,
            (D.encode candidate).sol.terminalTime ≤ T') →
            Nonempty (ChosenIntrinsicDeTurckLocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp) ∧
            Nonempty (IntrinsicLocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp) ∧
            Nonempty (LocalExistenceUniqueness
              (E := F) (H := H) (I := I) (M := M) ivp)) ∧
          (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
              (E := F) (H := H) (I := I) (M := M) ivp) {S : ℝ},
            ivp.initialTime < S → S ≤ sol₁.1.terminalTime →
            S ≤ sol₂.1.terminalTime → S ≤ T' → ∀ {t : ℝ},
            t ∈ Icc ivp.initialTime S → ∀ (x : M) (u v : TM x),
              metricTensor (I := I) (M := M)
                sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
                  metricTensor (I := I) (M := M)
                    sol₂.1.toIntrinsicDeTurckSolution.metric t x u v) ∧
          (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
              (E := F) (H := H) (I := I) (M := M) ivp) {S : ℝ},
            ivp.initialTime < S → S ≤ sol₁.1.terminalTime →
            S ≤ sol₂.1.terminalTime → S ≤ T' → ∀ {t : ℝ},
            t ∈ Icc ivp.initialTime S →
            ∀ {x : M} {σ : Π y : M, TM y},
              MDiffAt (T% σ) x →
              sol₁.1.canonicalConnection
                (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
                sol₂.1.canonicalConnection
                  (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2)
                  t σ x) ∧
          (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
              (E := F) (H := H) (I := I) (M := M) ivp),
            min sol₁.1.terminalTime sol₂.1.terminalTime ≤ T' → ∀ {t : ℝ},
            t ∈ Icc ivp.initialTime (min sol₁.1.terminalTime sol₂.1.terminalTime) →
            ∀ (x : M) (u v : TM x),
              metricTensor (I := I) (M := M)
                sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
                  metricTensor (I := I) (M := M)
                    sol₂.1.toIntrinsicDeTurckSolution.metric t x u v) ∧
          (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
              (E := F) (H := H) (I := I) (M := M) ivp),
            min sol₁.1.terminalTime sol₂.1.terminalTime ≤ T' → ∀ {t : ℝ},
            t ∈ Icc ivp.initialTime (min sol₁.1.terminalTime sol₂.1.terminalTime) →
            ∀ {x : M} {σ : Π y : M, TM y},
              MDiffAt (T% σ) x →
              sol₁.1.canonicalConnection
                (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
                sol₂.1.canonicalConnection
                  (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2)
                  t σ x)) := by
  rcases
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_initialMetric_chartRestrictedSymmetricA_solution_theoremPackages_localRestrictedMetricConnectionReadout
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover chart D rhs ha with
    ⟨T', a', hT', hT'le, ha'le, htime, chart', ha'pos, hball,
      hsolution, hpackages, hmetric, hconnection⟩
  refine
    ⟨T', a', hT', hT'le, ha'le, htime, chart', ha'pos, hball,
      hsolution, hpackages, hmetric, hconnection, ?_, ?_⟩
  · intro sol₁ sol₂ hcommonT t ht x u v
    exact hmetric sol₁ sol₂
      (S := min sol₁.1.terminalTime sol₂.1.terminalTime)
      (lt_min sol₁.1.initial_lt_terminal sol₂.1.initial_lt_terminal)
      (min_le_left _ _) (min_le_right _ _) hcommonT ht x u v
  · intro sol₁ sol₂ hcommonT t ht x σ hσ
    exact hconnection sol₁ sol₂
      (S := min sol₁.1.terminalTime sol₂.1.terminalTime)
      (lt_min sol₁.1.initial_lt_terminal sol₂.1.initial_lt_terminal)
      (min_le_left _ _) (min_le_right _ _) hcommonT ht hσ

/-- The initial-metric smooth-approximation route can use one selected metric-cone shrink for the
chart-carrier Banach solution, clipped metric/connection uniqueness, and the corresponding
full-common readouts whenever the selected shrink contains the common candidate terminal. -/
theorem TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_initialMetric_chartRestrictedSymmetricA_solution_localMetricConnectionReadout_with_fullCommon
    [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
    [SecondCountableTopology H]
    [ContMDiffVectorBundle 2 F TM I]
    [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    [CompleteSpace F]
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
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
    (D : RicciDeTurckChartClosureDataOnIcc x0 et het Kc hKc Ko hKo hKoEq hcover chart)
    (rhs : SmoothSectionRHSIdentification
      (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover chart.A)
    (ha : 0 < a) :
    ∃ (T' : ℝ) (a' : ℝ≥0) (_hT' : ivp.initialTime < T') (_hT'le : T' ≤ T)
      (_ha' : a' ≤ a)
      (_htime : L * max (T' - ivp.initialTime) (ivp.initialTime - ivp.initialTime) ≤
        a' - (0 : ℝ≥0)),
      ∃ chart' : TimeDependentGeometricRicciDeTurckBanachChartOnIcc
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover
        ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T' a' L Kpic Kstate,
        0 < a' ∧
          Metric.closedBall
            (InitialValueProblem.toSymmetricSectionSubmodule
              (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp) (a' : ℝ) ⊆
            riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
              et Kc hKc Ko hKo hKoEq hcover ∧
          (∃ sol : BanachEvolutionLocalSolutionIn
              (chart'.restrictedSymmetricA
                (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
              (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                et Kc hKc Ko hKo hKoEq hcover)
              ivp.initialTime
              (InitialValueProblem.toSymmetricSectionSubmodule
                (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
             sol.terminalTime ≤ T' ∧
             ∀ sol' : BanachEvolutionLocalSolutionIn
                (chart'.restrictedSymmetricA
                  (M := M) (F := F) (I := I) x0 et het Kc hKc Ko hKo hKoEq hcover)
                (riemannianMetricLocusSubmodule (M := M) (F := F) (W := TM)
                  et Kc hKc Ko hKo hKoEq hcover)
                ivp.initialTime
                (InitialValueProblem.toSymmetricSectionSubmodule
                  (M := M) x0 et het Kc hKc Ko hKo hKoEq hcover ivp),
               EqOn sol.curve sol'.curve
                 (Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
          (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
              (E := F) (H := H) (I := I) (M := M) ivp) {t : ℝ},
            t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T') →
            ∀ (x : M) (u v : TM x),
              metricTensor (I := I) (M := M)
                sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
                  metricTensor (I := I) (M := M)
                    sol₂.1.toIntrinsicDeTurckSolution.metric t x u v) ∧
          (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
              (E := F) (H := H) (I := I) (M := M) ivp) {t : ℝ},
            t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T') →
            ∀ {x : M} {σ : Π y : M, TM y},
              MDiffAt (T% σ) x →
              sol₁.1.canonicalConnection
                (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
                sol₂.1.canonicalConnection
                  (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2)
                  t σ x) ∧
          (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
              (E := F) (H := H) (I := I) (M := M) ivp),
            min sol₁.1.terminalTime sol₂.1.terminalTime ≤ T' → ∀ {t : ℝ},
            t ∈ Icc ivp.initialTime (min sol₁.1.terminalTime sol₂.1.terminalTime) →
            ∀ (x : M) (u v : TM x),
              metricTensor (I := I) (M := M)
                sol₁.1.toIntrinsicDeTurckSolution.metric t x u v =
                  metricTensor (I := I) (M := M)
                    sol₂.1.toIntrinsicDeTurckSolution.metric t x u v) ∧
          (∀ (sol₁ sol₂ : ChosenIntrinsicDeTurckLocalSolution
              (E := F) (H := H) (I := I) (M := M) ivp),
            min sol₁.1.terminalTime sol₂.1.terminalTime ≤ T' → ∀ {t : ℝ},
            t ∈ Icc ivp.initialTime (min sol₁.1.terminalTime sol₂.1.terminalTime) →
            ∀ {x : M} {σ : Π y : M, TM y},
              MDiffAt (T% σ) x →
              sol₁.1.canonicalConnection
                (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₁.1 sol₁.2) t σ x =
                sol₂.1.canonicalConnection
                  (usesChosenBackground_isLeviCivita (I := I) (M := M) sol₂.1 sol₂.2)
                  t σ x) := by
  rcases
      TimeDependentGeometricRicciDeTurckBanachChartOnIcc.exists_metricCone_shrunk_specificRHS_initialMetric_chartRestrictedSymmetricA_solution_localMetricConnectionReadout
        (M := M) (F := F) (I := I)
        x0 et het Kc hKc Ko hKo hKoEq hcover chart D rhs ha with
    ⟨T', a', hT', hT'le, ha'le, htime, chart', ha'pos, hball,
      hsolution, hmetric, hconnection⟩
  refine
    ⟨T', a', hT', hT'le, ha'le, htime, chart', ha'pos, hball,
      hsolution, hmetric, hconnection, ?_, ?_⟩
  · intro sol₁ sol₂ hcommonT t ht x u v
    have htclip :
        t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T') := by
      simpa [min_eq_left hcommonT] using ht
    exact hmetric sol₁ sol₂ htclip x u v
  · intro sol₁ sol₂ hcommonT t ht x σ hσ
    have htclip :
        t ∈ Icc ivp.initialTime (min (min sol₁.1.terminalTime sol₂.1.terminalTime) T') := by
      simpa [min_eq_left hcommonT] using ht
    exact hconnection sol₁ sol₂ htclip hσ

end PreferredSmoothApproxClosure

end SmoothSectionRHSIdentification
end MetricLocusEvolution
end AnalyticPDE
end RicciFlow
