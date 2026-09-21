/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.RiemannianSection
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SectionSpacePicard

/-!
# Section-space Banach evolution for the frozen-coefficient geometric DeTurck reaction

This module closes the loop between the two halves of the geometric Ricci–DeTurck chart operator's
`picard` datum that have been built independently:

* the concrete **coordinate `hlip`/`hcenter` bounds** for the affine frozen-coefficient DeTurck
  reaction operator `A s = bilinearDerivationFieldLinearMap … s + b` on the `BilinearFormBundle`
  continuous section space (`VectorBundle/RiemannianSection.lean`,
  `bilinearDerivationFieldLinearMap_add_source_coord_dist_le` / `_add_source_coord_norm_le`), and

* the **section-space Picard bridge** producing a genuine `BanachEvolutionLocalSolutionIn`
  (`AnalyticPDE/SectionSpacePicard.lean`).

The bridge could not previously be applied to the concrete `BilinearFormBundle` section space because
of a topology-instance diamond: the bridge derived its fibre topology from a
`SeminormedAddCommGroup (V x)` (Path A), while the concrete double-`ContinuousLinearMap` fibre
`BilW x = W x →L[ℝ] W x →L[ℝ] ℝ` carries the (defeq but differently spelled)
`ContinuousLinearMap.topologicalSpace` (Path B) that `FiberBundle`/`VectorBundle` and every concrete
coordinate readout lemma use.  The topological-fibre bridge
`sectionSpace_banachEvolutionLocalSolutionIn_exists_of_forall_coord_centerBound_topFibre` takes the
fibre topology as an *explicit* instance binder, so it consumes the Path-B coordinate bounds verbatim.

The result `bilinearDerivationFieldLinearMap_add_source_banachEvolutionLocalSolutionIn_exists` is the
first genuine `BanachEvolutionLocalSolutionIn` produced from the *geometric* reaction operator (not a
model heat-semigroup): from a uniform bound `Kp` on the frozen endomorphism coefficient `P`'s
model-fibre readout over a finite compact cover, together with the time-radius compatibility
`(Mc + K·a)·(T − t₀) ≤ a` (with `K = 2·Kp`, `Mc = 2·Kp·‖σ0‖ + ‖b‖`) and the Picard-ball containment
`closedBall σ0 a ⊆ locus`, the affine operator `A s = (reaction s) + b` admits a state-constrained
Banach evolution local solution on the window `[t₀, T]`.
-/

@[expose] public noncomputable section

open Bundle
open scoped NNReal Topology
open RicciFlow.AnalyticPDE

namespace PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace

variable {M : Type*} [TopologicalSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {W : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F W)]
  [∀ x, SeminormedAddCommGroup (W x)] [∀ x, NormedSpace ℝ (W x)]
  [FiberBundle F W] [VectorBundle ℝ F W]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)
local notation "BilW" => _root_.Bundle.BilinearFormBundle (V := W)

attribute [local instance] bilFNormedAddCommGroup bilFNormedSpace
  bilWSeminormedAddCommGroup bilWNormedSpace
/-- **Section-space Banach evolution local solution for the frozen-coefficient geometric DeTurck
reaction plus a fixed source.**  For the affine `BilinearFormBundle` section-space operator
`A s = bilinearDerivationFieldLinearMap … s + b` (the two-sided derivation
`x ↦ (s x).bilinearComp (P x) id + (s x).bilinearComp id (P x)` with a *frozen* tangent-endomorphism
coefficient `P`, plus a fixed source section `b`), the already-proved coordinate Lipschitz and
centre-norm bounds
(`bilinearDerivationFieldLinearMap_add_source_coord_dist_le` / `_add_source_coord_norm_le`, with
Lipschitz constant `K = 2·Kp` and centre bound `Mc = 2·Kp·‖σ0‖ + ‖b‖` supplied by a uniform bound
`Kp` on the model-fibre readout of `P` over the finite compact cover) are fed to the topological-fibre
section-space Picard bridge to produce a genuine `BanachEvolutionLocalSolutionIn` on the window
`[t₀, T]`, constrained to the state locus `locus ⊇ closedBall σ0 a`, provided the time-radius
compatibility `(Mc + K·a)·(T − t₀) ≤ a` holds.  This is the first geometric-operator (non-model)
section-space Banach evolution solution, and the object a `RicciDeTurckChartClosureData.realization`
decode consumes. -/
theorem bilinearDerivationFieldLinearMap_add_source_banachEvolutionLocalSolutionIn_exists
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x)))
    (Kp : ℝ) (hKp0 : 0 ≤ Kp)
    (hKp : ∀ (i : κ) (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates F W F W (x0 i) x.1 (x0 i) x.1 (P x.1)‖ ≤ Kp)
    (b σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (locus : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover))
    (t₀ T : ℝ) (hT : t₀ < T) (a : ℝ≥0)
    (hLa : ((2 * Kp * ‖σ0‖ + ‖b‖) + 2 * Kp * (a : ℝ)) * (T - t₀) ≤ (a : ℝ))
    (hsub : Metric.closedBall σ0 (a : ℝ) ⊆ locus) :
    Nonempty (BanachEvolutionLocalSolutionIn
      (fun (_ : ℝ) (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) =>
        bilinearDerivationFieldLinearMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP s + b)
      locus t₀ σ0) := by
  refine sectionSpace_banachEvolutionLocalSolutionIn_exists_of_forall_coord_centerBound_topFibre
    (fun (_ : ℝ) s => bilinearDerivationFieldLinearMap (fun i => trivializationAt BilF BilW (x0 i))
      Kc hKc Ko hKo hKoEq hcover hP s + b)
    σ0 locus t₀ T hT a ⟨2 * Kp, by linarith⟩
    ⟨2 * Kp * ‖σ0‖ + ‖b‖,
      add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hKp0) (norm_nonneg σ0))
        (norm_nonneg b)⟩
    ?_ ?_ ?_ ?_ hsub
  · intro t _ht s _hs s' _hs' i x
    exact bilinearDerivationFieldLinearMap_add_source_coord_dist_le
      x0 Kc hKc Ko hKo hKoEq hcover hP Kp hKp b s s' i x
  · intro s _hs i
    exact continuousOn_const
  · intro t _ht i x
    exact bilinearDerivationFieldLinearMap_add_source_coord_norm_le
      x0 Kc hKc Ko hKo hKoEq hcover hP Kp hKp b σ0 i x
  · exact hLa

/-- **Forward-time `IsPicardLindelof` for the frozen-coefficient geometric DeTurck reaction plus a
fixed source.**  The literal chart `picard`-field shape (an `IsPicardLindelof` datum with an
*automatically chosen* forward endpoint `T ∈ (t₀, T₀]`) for the affine `BilinearFormBundle`
section-space operator `A s = bilinearDerivationFieldLinearMap … s + b`.  Unlike
`bilinearDerivationFieldLinearMap_add_source_banachEvolutionLocalSolutionIn_exists`, no time-radius
compatibility `hLa` need be supplied: from a uniform bound `Kp` on the frozen coefficient `P`'s
model-fibre readout over the finite compact cover, a reference window `Icc t₀ T₀` and a positive
Picard radius `a`, the topological-fibre forward-time endpoint chooser produces the endpoint `T` and
centre size `Mc` itself (the operator being constant in time, its `hcont` is trivial).  This is the
frozen geometric reaction's actual `IsPicardLindelof` picard datum on the `BilinearFormBundle`
(Path-B) section space. -/
theorem bilinearDerivationFieldLinearMap_add_source_exists_forwardTime_isPicardLindelof
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, W x →L[ℝ] W x}
    (hP : Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' (F →L[ℝ] F)
      (E := fun x ↦ W x →L[ℝ] W x) x (P x)))
    (Kp : ℝ) (hKp0 : 0 ≤ Kp)
    (hKp : ∀ (i : κ) (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates F W F W (x0 i) x.1 (x0 i) x.1 (P x.1)‖ ≤ Kp)
    (b σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a : ℝ≥0) (ha : 0 < (a : ℝ)) :
    ∃ (T : ℝ) (hT : t₀ < T) (Mc : ℝ≥0),
      IsPicardLindelof
        (fun (_ : ℝ) (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) =>
          bilinearDerivationFieldLinearMap (fun i => trivializationAt BilF BilW (x0 i))
            Kc hKc Ko hKo hKoEq hcover hP s + b)
        (tmin := t₀) (tmax := T) ⟨t₀, ⟨le_rfl, hT.le⟩⟩ σ0 a 0 (Mc + ⟨2 * Kp, by linarith⟩ * a)
        ⟨2 * Kp, by linarith⟩ := by
  refine exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_continuousOn_topFibre
    (fun (_ : ℝ) s => bilinearDerivationFieldLinearMap (fun i => trivializationAt BilF BilW (x0 i))
      Kc hKc Ko hKo hKoEq hcover hP s + b)
    σ0 t₀ T₀ hT₀ a ⟨2 * Kp, by linarith⟩ ha ?_ ?_
  · intro t _ht s _hs s' _hs' i x
    exact bilinearDerivationFieldLinearMap_add_source_coord_dist_le
      x0 Kc hKc Ko hKo hKoEq hcover hP Kp hKp b s s' i x
  · intro s _hs i
    exact continuousOn_const

end PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace
