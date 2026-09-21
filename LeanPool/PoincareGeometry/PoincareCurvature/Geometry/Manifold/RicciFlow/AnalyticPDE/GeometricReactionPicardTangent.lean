/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.GeometricReactionCoordBounds
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SectionSpacePicard

/-!
# Tangent-bundle DeTurck reaction: section-space Picard coordinate bounds and `IsPicardLindelof`

This module assembles the section-space Picard `hlip`/`hcenter` coordinate obligations for the concrete
**tangent-bundle** DeTurck reaction operator `deTurckReactionSectionMap` (fiber-norm-free, hence
formable at `W := TangentSpace I`), by connecting its model-fibre readout size bounds
(`GeometricReactionCoordBounds`) to the `coord` language of the section-space Picard bridge through a
**fiber-norm-free** coordinate-readout bridge.

The existing coordinate-readout bridge `bilinearFormBundle_coord_eq_trivializationAt_readout` demands
`[∀ x, SeminormedAddCommGroup (W x)]` (the Π-fibre-seminorm) as an explicit binder, which triggers the
derived-module-vs-norm-module diamond at `W := TangentSpace I`.  The bridge
`deTurckReactionSectionMap_coord_eq_readout` below reproves the identity **directly at the tangent
bundle**, where the section-space seminorm `SeminormedAddCommGroup (BilW x)` is supplied per-`x` by the
canonical tangent norm (a global instance) rather than a Π-binder, and the identity itself goes through
the fiber-norm-free `coord_apply` and the `LocalCoordinatePositivity` trivialization lemmas.
-/

@[expose] public noncomputable section

open Bundle RicciFlow
open scoped Manifold ContDiff Topology NNReal
open PoincareCurvature.Bundle.Trivialization

namespace PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "THom" => (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
local notation "BilF" => (E →L[ℝ] E →L[ℝ] ℝ)
local notation "BilW" => (_root_.Bundle.BilinearFormBundle (V := TM))
/-- **Fiber-norm-free coordinate-readout bridge at the tangent bundle (plain sections).**  For any
section `s` of the canonical `BilinearFormBundle` continuous section space at `W := TangentSpace I`,
the compact coordinate `(coord s).1 i x` (`equivCompatibleCoordFamilySubmodule`) equals the raw fibre
readout `(trivializationAt BilF BilW (x0 i) ⟨x, s x⟩).2`.  Same identity as
`bilinearFormBundle_coord_eq_trivializationAt_readout`, but obtained at `W := TangentSpace I` — where
the section-space fibre carries the hom-bundle topology `ContinuousLinearMap.topologicalSpace`, not the
norm-metric topology `coord_apply` resolves to — by unfolding the `coord` definition **directly on the
goal** (so the goal's own hom fibre topology is used consistently), sidestepping the
`ContinuousLinearMap.topologicalSpace`-vs-`PseudoMetricSpace…toTopologicalSpace` fibre-topology diamond
that blocks a direct `coord_apply` rewrite. -/
theorem bilinearFormBundle_coord_eq_trivializationAt_readout_tangent
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (i : κ) (x : Kc i) :
    (equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover s).1 i x
      = (trivializationAt BilF BilW (x0 i)
          (_root_.Bundle.TotalSpace.mk' BilF x.1 (s.toFun x.1))).2 := by
  have hx : (x : M) ∈ (trivializationAt BilF BilW (x0 i)).baseSet := hKc i x.2
  haveI hlin : (trivializationAt BilF BilW (x0 i)).IsLinear ℝ :=
    _root_.Bundle.trivializationAt_bilinearFormBundle_isLinear (F := E) (W := TM) (x0 i)
  change (trivializationAt BilF BilW (x0 i)
      (_root_.Bundle.TotalSpace.mk' BilF x.1 (s.toFun x.1))).2 = _
  rfl

/-- **The tangent-bundle DeTurck reaction operator's coordinate readout equals its `trivializationAt`
fibre readout.**  For the concrete operator `deTurckReactionSectionMap … σ` (fiber-norm-free, formable
at `W := TangentSpace I`), the continuous-section-space coordinate
`(coord (deTurckReactionSectionMap … σ)).1 i x` (`equivCompatibleCoordFamilySubmodule`) equals the raw
fibre readout `(trivializationAt BilF BilW (x0 i) ⟨x, deTurckReactionSectionMap … σ x⟩).2`.  Proved at
`W := TangentSpace I` without any `[∀ x, SeminormedAddCommGroup (W x)]` Π-binder (which would trigger
the derived-module-vs-norm-module diamond): it combines the fiber-norm-free `coord_apply` with the
on-baseSet trivialization identity `continuousLinearMapAt = (e ⟨x, ·⟩).2` (`coe_linearMapAt_of_mem`),
the bilinear-form trivialization's linearity supplied by the fiber-norm-free
`trivializationAt_bilinearFormBundle_isLinear`.  This turns the operator's model-fibre readout size
bounds (`GeometricReactionCoordBounds`) into section-space Picard coordinate bounds. -/
theorem deTurckReactionSectionMap_coord_eq_readout
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (σ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (i : κ) (x : Kc i) :
    (equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover
        (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP σ)).1 i x
      = (trivializationAt BilF BilW (x0 i)
          (_root_.Bundle.TotalSpace.mk' BilF x.1
            (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
              Kc hKc Ko hKo hKoEq hcover hP σ x.1))).2 :=
  bilinearFormBundle_coord_eq_trivializationAt_readout_tangent x0 Kc hKc Ko hKo hKoEq hcover
    (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
      Kc hKc Ko hKo hKoEq hcover hP σ) i x

/-- **Tangent-bundle (`W := TangentSpace I`) hom-topology `coord_apply`.**  For a section `s` of the
canonical `BilinearFormBundle` continuous section space at `W := TangentSpace I`, the compact coordinate
readout `(coord s).1 i x` (`equivCompatibleCoordFamilySubmodule`) equals the trivialization's fibrewise
`continuousLinearMapAt` applied to the pointwise value `s.toFun x`.  This is the fibre-topology-native
(`ContinuousLinearMap.topologicalSpace` on the hom fibre) companion of the seminormed-fibre `coord_apply`,
obtained by unfolding the readout bridge `bilinearFormBundle_coord_eq_trivializationAt_readout_tangent`
into the on-baseSet linear map `(e ⟨x, ·⟩).2 = continuousLinearMapAt x` (`continuousLinearMapAt_apply` +
`coe_linearMapAt_of_mem`), so that only `IsLinear`-level (Pretrivialization) API is used — sidestepping
the `FiberBundle`/fibre-`TopologicalSpace` diamond that blocks the seminormed-track `coord_apply` at
`BilW`. -/
theorem coord_apply_tangent
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (i : κ) (x : Kc i) :
    (equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover s).1 i x
      = (trivializationAt BilF BilW (x0 i)).continuousLinearMapAt ℝ x.1 (s.toFun x.1) := by
  have hx : (x : M) ∈ (trivializationAt BilF BilW (x0 i)).baseSet := hKc i x.2
  haveI hlin : (trivializationAt BilF BilW (x0 i)).IsLinear ℝ :=
    _root_.Bundle.trivializationAt_bilinearFormBundle_isLinear (F := E) (W := TM) (x0 i)
  rw [bilinearFormBundle_coord_eq_trivializationAt_readout_tangent x0 Kc hKc Ko hKo hKoEq hcover s i x]
  simp only [Trivialization.continuousLinearMapAt_apply,
    (trivializationAt BilF BilW (x0 i)).coe_linearMapAt_of_mem hx]

/-- **Pointwise additivity of the tangent-bundle continuous section space at the hom fibre topology.**
`(s + t).toFun x = s.toFun x + t.toFun x` for sections `s t` of the canonical `BilinearFormBundle`
continuous section space at `W := TangentSpace I`.  Unlike the seminormed-track `add_apply`, whose direct
use at `BilW` blows the elaborator's `isDefEq` budget on the transported `AddCommGroup`/`BilinearFormBundle`
fibre diamond, this hom-fibre-topology version routes entirely through the diamond-free coordinate track:
each section value is recovered from its compact coordinate via the trivialization's linear inverse
(`coord_apply_tangent` then `symmₗ_linearMapAt`), the coordinate of the sum splits additively
(`coord_add_apply_topFibre`), and the fibre inverse `symmₗ` is `ℝ`-linear (`map_add`).  Only
`IsLinear`-level (Pretrivialization) API is used, so no `FiberBundle`/fibre-`TopologicalSpace` diamond is
triggered.  This is the wall-free pointwise-add companion that lets an affine section-space chart operator
`A t s = L s + b` be evaluated at a fibre point (`A t s x u v = (L s) x u v + b x u v`), connecting its
coordinate-level Picard data to a geometric fibre-value identification. -/
theorem add_apply_tangent
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s t : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (x : M) :
    (s + t).toFun x = s.toFun x + t.toFun x := by
  obtain ⟨i, hi⟩ : ∃ i, x ∈ (Kc i : Set M) :=
    Set.mem_iUnion.mp (by rw [hcover]; exact Set.mem_univ x)
  have hx : x ∈ (trivializationAt BilF BilW (x0 i)).baseSet := hKc i hi
  haveI hlin : (trivializationAt BilF BilW (x0 i)).IsLinear ℝ :=
    _root_.Bundle.trivializationAt_bilinearFormBundle_isLinear (F := E) (W := TM) (x0 i)
  have hsymm : ∀ (σ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover),
      σ.toFun x = (trivializationAt BilF BilW (x0 i)).symmₗ ℝ x
        ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
          (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover σ).1 i ⟨x, hi⟩) := by
    intro σ
    rw [coord_apply_tangent x0 Kc hKc Ko hKo hKoEq hcover σ i ⟨x, hi⟩,
      Trivialization.continuousLinearMapAt_apply]
    exact ((trivializationAt BilF BilW (x0 i)).symmₗ_linearMapAt hx (σ.toFun x)).symm
  rw [hsymm s, hsymm t, hsymm (s + t),
    coord_add_apply_topFibre s t i ⟨x, hi⟩, map_add]

/-- **The concrete affine frozen geometric Ricci–DeTurck chart operator, evaluated at the metric
section, reproduces the intrinsic Ricci–DeTurck RHS at the fibre value.**  For the actual CSS-sum
chart operator `A τ s = deTurckReactionSectionMap ∇W s + intrinsicRicciFlowRHSSectionSpace g t` (the
frozen reaction plus the `(-2)•Ric` source, on the concrete tangent `BilinearFormBundle` section space),
its *pointwise fibre value* at the metric section `⟨(g t).toSection, …⟩` equals the geometric
`intrinsicRicciDeTurckRHS g background t x u v`.  This is the fibre-value (`x u v`) form of the chart's
`geometric`/`chartRHS_eq_intrinsic` identification at the center metric — obtained by pushing the CSS sum
through the just-committed diamond-free pointwise add `add_apply_tangent`
(`(L s + b) x = (L s) x + b x`), splitting the bilinear sum with `ContinuousLinearMap.add_apply`, and
closing with the committed scalar identity
`deTurckReactionSectionMap_metricSection_add_ricciFlowRHSSection_apply_eq_intrinsicRicciDeTurckRHS`.
Unlike that scalar identity (a bare sum `source x u v + reaction x u v`), this states the identity for the
genuine `ContinuousSectionSpace`-valued operator the chart field `A` is, so it directly certifies
`A t (metricSection) x u v = intrinsicRicciDeTurckRHS …` — the `s = metricSection` instance of the chart's
`geometric` field, previously blocked by the `BilinearFormBundle` CSS-add wall. -/
theorem deTurckReactionSectionMap_add_source_metricSection_apply_eq_intrinsicRicciDeTurckRHS
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (x : M) (u v : TM x) :
    (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover
          (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
            g background t hbackground).continuous
          ⟨(g t).toSection, (g t).continuous_toSection⟩
        + RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (x0 i))
            Kc hKc Ko hKo hKoEq hcover g t) x u v
      = RicciFlow.intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v := by
  have hpt : (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover
          (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
            g background t hbackground).continuous
          ⟨(g t).toSection, (g t).continuous_toSection⟩
        + RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (x0 i))
            Kc hKc Ko hKo hKoEq hcover g t) x
      = (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover
          (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
            g background t hbackground).continuous
          ⟨(g t).toSection, (g t).continuous_toSection⟩).toFun x
        + (RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (x0 i))
            Kc hKc Ko hKo hKoEq hcover g t).toFun x :=
    add_apply_tangent x0 Kc hKc Ko hKo hKoEq hcover _ _ x
  rw [hpt, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, add_comm]
  exact deTurckReactionSectionMap_metricSection_add_ricciFlowRHSSection_apply_eq_intrinsicRicciDeTurckRHS
    (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover
    g background t hbackground x u v

/-- **Fibre-value decomposition of the affine frozen chart operator at an arbitrary state.**  For any
state section `s`, frozen tangent-endomorphism coefficient `P`, and fixed source section `b`, the affine
chart operator `A s = deTurckReactionSectionMap P s + b` has the explicit fibre value
`(A s) x u v = s x (P x u) v + s x (P x v) u + b x u v`.  Obtained by pushing the CSS sum through the
diamond-free pointwise add `add_apply_tangent`, splitting the bilinear sum with
`ContinuousLinearMap.add_apply`, and unfolding the reaction fibre value with the raw-`Pi` reaction
identity `deTurckReactionSectionMap_apply` — entirely wall-free at `BilW`.  This is the general-state
companion of the metric-section identity above: it gives the chart velocity's fibre value at *every*
positive-definite section, the shape the chart's `geometric`/`lipschitz` fibre reasoning consumes. -/
theorem deTurckReactionSectionMap_add_source_apply
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (b s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (x : M) (u v : TM x) :
    (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP s + b) x u v
      = s.toFun x (P x u) v + s.toFun x (P x v) u + b.toFun x u v := by
  have hpt : (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP s + b) x
      = (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP s).toFun x + b.toFun x :=
    add_apply_tangent x0 Kc hKc Ko hKo hKoEq hcover _ _ x
  rw [hpt, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
  simp only [deTurckReactionSectionMap_apply]

/-- **The tangent-bundle DeTurck reaction operator's section-space Picard `hlip` coordinate bound.**
For the concrete operator `deTurckReactionSectionMap … hP` on the tangent-bundle `BilinearFormBundle`
continuous section space, the pointwise coordinate readout is Lipschitz-in-state:
`dist (coord (deTurck s) i x) (coord (deTurck s') i x) ≤ 2·Kp·dist s s'` for any uniform bound
`Kp ≥ ‖inCoordinates E TM E TM (x₀ i) x (x₀ i) x (P x)‖`.  This is EXACTLY the `hlip` hypothesis of the
topological-fibre section-space Picard bridge
`exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_continuousOn_topFibre`
(with `K := 2·Kp`), assembled at `W := TangentSpace I` where the seminormed-fibre coordinate lemmas
diverge.  Proof: rewrite both operator coordinates to their `trivializationAt` readouts
(`deTurckReactionSectionMap_coord_eq_readout`), bound the readout distance by the reaction's
Lipschitz-in-state fibre bound (`deTurckReactionSectionMap_readout_sub_dist_le_inCoordinates`, with the
`BilF`↔`TM` base-set membership supplied by `simpa`), rewrite the plain-section readouts back to
coordinates (`bilinearFormBundle_coord_eq_trivializationAt_readout_tangent`), and close with the
hom-topology-native coordinate contraction `coord_dist_le_dist_topFibre` (`dist (coord s i x)
(coord s' i x) ≤ dist s s'`) and `‖inCoord (P x)‖ ≤ Kp`. -/
theorem deTurckReactionSectionMap_coord_dist_le_inCoordinates
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (s s' : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (i : κ) (x : Kc i) (Kp : ℝ)
    (hKp : ‖ContinuousLinearMap.inCoordinates E TM E TM (x0 i) x (x0 i) x (P x)‖ ≤ Kp) :
    dist
      ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover
        (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP s)).1 i x)
      ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover
        (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP s')).1 i x)
      ≤ 2 * Kp * dist s s' := by
  have hxTM : (x : M) ∈ (trivializationAt E TM (x0 i)).baseSet := by simpa using hKc i x.2
  rw [deTurckReactionSectionMap_coord_eq_readout x0 Kc hKc Ko hKo hKoEq hcover hP s i x,
      deTurckReactionSectionMap_coord_eq_readout x0 Kc hKc Ko hKo hKoEq hcover hP s' i x]
  refine (deTurckReactionSectionMap_readout_sub_dist_le_inCoordinates
    (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover hP s s'
    (x0 i) x hxTM).trans ?_
  rw [← bilinearFormBundle_coord_eq_trivializationAt_readout_tangent x0 Kc hKc Ko hKo hKoEq hcover s i x,
      ← bilinearFormBundle_coord_eq_trivializationAt_readout_tangent x0 Kc hKc Ko hKo hKoEq hcover s' i x]
  have hcd := coord_dist_le_dist_topFibre s s' i x
  have hIC : (0:ℝ) ≤ ‖ContinuousLinearMap.inCoordinates E TM E TM (x0 i) x (x0 i) x (P x)‖ :=
    norm_nonneg _
  nlinarith [hcd, hKp, hIC,
    dist_nonneg (α := ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) (x := s) (y := s'),
    dist_nonneg (α := BilF)
      (x := (equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover s).1 i x)
      (y := (equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover s').1 i x)]

/-- **`IsPicardLindelof` for the frozen-coefficient geometric DeTurck reaction operator on the
tangent-bundle continuous section space.**  Given a uniform bound `Kp` on the endomorphism coordinate
readout `‖inCoordinates E TM E TM (xc i) x (xc i) x (P x)‖` over the finite compact cover, the
time-independent (frozen) reaction operator `t ↦ deTurckReactionSectionMap … hP` satisfies
`IsPicardLindelof` about any initial section `σ₀`, with radius `a`, Lipschitz constant `2·Kp`, and an
auto-chosen forward endpoint `T ∈ (t₀, T₀]` and centre size `Mc`.  This is the concrete tangent-bundle
chart operator's `picard` datum (Path B, no seminormed-fibre diamond): its `hlip` field is the just-proved
`deTurckReactionSectionMap_coord_dist_le_inCoordinates` (with `K := 2·Kp`, the uniform bound feeding each
per-point `‖inCoord (P x)‖ ≤ Kp`), and its `hcont` field is `continuousOn_const` (the operator is
constant in time, so its coordinate readouts are trivially time-continuous).  Feeding the affine
`A t s = deTurckReactionSectionMap ∇W s + (-2)•Ric` source and identifying `P := ∇W` yields the chart's
`picard`; the uniform `Kp` is supplied by compactness of the cover and continuity of the frozen
coefficient's coordinate readout. -/
theorem deTurckReactionSectionMap_exists_isPicardLindelof_of_uniform_inCoordinates
    {κ : Type*} [Finite κ]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a Kp : ℝ≥0) (ha : 0 < (a : ℝ))
    (hKpU : ∀ i (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates E TM E TM (xc i) x (xc i) x (P x)‖ ≤ (Kp : ℝ)) :
    ∃ (T : ℝ) (hT : t₀ < T) (Mc : ℝ≥0),
      IsPicardLindelof
        (fun _ : ℝ => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover hP)
        (tmin := t₀) (tmax := T) ⟨t₀, ⟨le_rfl, hT.le⟩⟩ σ0 a 0 (Mc + (2 * Kp) * a) (2 * Kp) := by
  refine exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_continuousOn_topFibre
    (fun _ : ℝ => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
      Kc hKc Ko hKo hKoEq hcover hP)
    σ0 t₀ T₀ hT₀ a (2 * Kp) ha ?_ ?_
  · intro t _ht s _hs s' _hs' i x
    have h := deTurckReactionSectionMap_coord_dist_le_inCoordinates xc Kc hKc Ko hKo hKoEq hcover hP
      s s' i x (Kp : ℝ) (hKpU i x)
    calc dist _ _ ≤ 2 * (Kp : ℝ) * dist s s' := h
      _ = ((2 * Kp : ℝ≥0) : ℝ) * dist s s' := by push_cast; ring
  · intro s _hs i
    exact continuousOn_const

/-- **`ContinuousOn` of the frozen coefficient's coordinate readout on a compact piece, at `TM`.**
For a continuous tangent-endomorphism section `P` (into the endomorphism bundle `THom = TM →L[ℝ] TM`),
`x ↦ inCoordinates E TM E TM x₀ x x₀ x (P x)` is continuous on the trivializing set
`(trivializationAt (E →L[ℝ] E) THom x₀).baseSet`.  Proved DIRECTLY at `TM` (the seminormed-fibre
`continuousOn_inCoordinates_of_continuous_homSection` fails to synthesize `FiberBundle E TM` when
applied here): the fixed-centre readout equals `(trivₓ₀ ⟨x, P x⟩).2` (`hom_trivializationAt_apply`),
and the hom trivialization is continuous on its source, which the section maps the base set into.  This
is the per-piece ingredient of the uniform inCoordinates bound. -/
theorem contOn_inCoord_tangent
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (x₀ : M) :
    ContinuousOn (fun x => ContinuousLinearMap.inCoordinates E TM E TM x₀ x x₀ x (P x))
      (trivializationAt (E →L[ℝ] E) THom x₀).baseSet := by
  set et := trivializationAt (E →L[ℝ] E) THom x₀ with het
  have hEq : (fun x => ContinuousLinearMap.inCoordinates E TM E TM x₀ x x₀ x (P x))
      = fun x => (et (TotalSpace.mk' (E →L[ℝ] E) x (P x))).2 := by
    funext x; rw [het, hom_trivializationAt_apply]
  rw [hEq]
  have hsrc : Set.MapsTo (fun x => TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x))
      et.baseSet et.source := fun x hx => by rw [Trivialization.mem_source]; exact hx
  exact continuous_snd.comp_continuousOn (et.continuousOn.comp hP.continuousOn hsrc)

/-- **Uniform bound on the frozen coefficient's coordinate readout over a finite compact cover.**  For
a continuous tangent-endomorphism section `P` and a finite family of compact pieces `Kc i`, each inside
the `THom` trivializing set of its centre `xc i`, there is a single `Kp ≥ 0` with
`‖inCoordinates E TM E TM (xc i) x (xc i) x (P x)‖ ≤ Kp` for all `i` and `x ∈ Kc i`.  Each per-piece
readout is continuous (`contOn_inCoord_tangent`) hence bounded on the compact `Kc i`
(`IsCompact.exists_bound_of_continuousOn`), and a `Finite κ` supremum of the finitely many bounds gives
the uniform `Kp`.  This discharges the uniform-`Kp` hypothesis of
`deTurckReactionSectionMap_exists_isPicardLindelof_of_uniform_inCoordinates`. -/
theorem exists_uniform_inCoord_bound
    {κ : Type*} [Finite κ] (xc : κ → M) (Kc : κ → TopologicalSpace.Compacts M)
    (hKcTM : ∀ i, (Kc i : Set M) ⊆ (trivializationAt (E →L[ℝ] E) THom (xc i)).baseSet)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x))) :
    ∃ Kp : ℝ, 0 ≤ Kp ∧ ∀ i (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates E TM E TM (xc i) x (xc i) x (P x)‖ ≤ Kp := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  have hcont : ∀ i, ContinuousOn
      (fun x => ContinuousLinearMap.inCoordinates E TM E TM (xc i) x (xc i) x (P x))
      (Kc i) :=
    fun i => (contOn_inCoord_tangent hP (xc i)).mono (hKcTM i)
  choose C hC using fun i => (Kc i).isCompact.exists_bound_of_continuousOn (hcont i)
  obtain ⟨D, hD⟩ := (Set.finite_range C).bddAbove
  refine ⟨max D 0, le_max_right _ _, fun i x => ?_⟩
  exact le_trans (hC i (x : M) x.2) (le_trans (hD (Set.mem_range_self i)) (le_max_left _ _))

/-- **Unconditional `IsPicardLindelof` for the frozen-coefficient geometric DeTurck reaction operator
at `TM`.**  Combining the uniform inCoordinates bound `exists_uniform_inCoord_bound` (which supplies the
uniform Lipschitz constant `Kp` by compactness of the finite cover + continuity of the frozen
coefficient `P`) with the conditional construction
`deTurckReactionSectionMap_exists_isPicardLindelof_of_uniform_inCoordinates`, the frozen (time-independent)
reaction operator `t ↦ deTurckReactionSectionMap … hP` satisfies `IsPicardLindelof` about any initial
section `σ₀` — with NO uniform-`Kp` hypothesis, only continuity of `P` and the compact cover.  The
cover's `BilinearFormBundle` trivializing sets coincide with the `THom` trivializing sets (both reduce to
the underlying `TangentSpace` trivializing set), supplied by `simpa`.  This is the frozen reaction's
`picard` datum on the Path-B tangent-bundle section space, fully constructed for a general continuous
frozen coefficient. -/
theorem deTurckReactionSectionMap_exists_isPicardLindelof
    {κ : Type*} [Finite κ]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a : ℝ≥0) (ha : 0 < (a : ℝ)) :
    ∃ (Kp : ℝ≥0) (T : ℝ) (hT : t₀ < T) (Mc : ℝ≥0),
      IsPicardLindelof
        (fun _ : ℝ => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover hP)
        (tmin := t₀) (tmax := T) ⟨t₀, ⟨le_rfl, hT.le⟩⟩ σ0 a 0 (Mc + (2 * Kp) * a) (2 * Kp) := by
  have hKcTM : ∀ i, (Kc i : Set M) ⊆ (trivializationAt (E →L[ℝ] E) THom (xc i)).baseSet := by
    intro i x hx
    have hxi := hKc i hx
    simpa using hxi
  obtain ⟨Kp, hKp0, hKpb⟩ := exists_uniform_inCoord_bound xc Kc hKcTM hP
  have hcast : ((Kp.toNNReal : ℝ≥0) : ℝ) = Kp := Real.coe_toNNReal Kp hKp0
  obtain ⟨T, hT, Mc, hPL⟩ := deTurckReactionSectionMap_exists_isPicardLindelof_of_uniform_inCoordinates
    xc Kc hKc Ko hKo hKoEq hcover hP σ0 t₀ T₀ hT₀ a Kp.toNNReal ha
    (fun i x => by rw [hcast]; exact hKpb i x)
  exact ⟨Kp.toNNReal, T, hT, Mc, hPL⟩

/-- **`IsPicardLindelof` for the affine geometric DeTurck operator (frozen reaction + fixed source) on
the tangent-bundle section space, conditional on a uniform inCoordinates bound.**  Given a uniform bound
`Kp` on the endomorphism coordinate readout `‖inCoordinates E TM E TM (xc i) x (xc i) x (P x)‖` over the
finite compact cover, the affine operator `A t s = deTurckReactionSectionMap … hP s + b` — the frozen
DeTurck reaction plus a FIXED source section `b` (typically the `(-2)•Ric` principal Ricci source frozen
at `g₀`, `b := intrinsicRicciFlowRHSSectionSpace g₀`) — satisfies `IsPicardLindelof` about any initial
section `σ₀`, with radius `a`, Lipschitz constant `2·Kp`, and an auto-chosen forward endpoint
`T ∈ (t₀, T₀]` and centre size `Mc`.  The affine part is DIAGNOSTIC-FREE for the Lipschitz bound: the
fixed source `b` contributes the SAME coordinate summand to `A t s` and `A t s'`, so it cancels in the
coordinate distance (`coord_add_apply_topFibre` then `dist_add_right`), leaving the frozen reaction's
`hlip` bound `deTurckReactionSectionMap_coord_dist_le_inCoordinates` unchanged (constant `2·Kp`).  The
`hcont` field is again `continuousOn_const` (both summands are frozen in time), and the centre size `Mc`
is derived internally by the bridge (absorbing `‖coord b‖`).  This is the affine chart operator's
`picard` datum on the Path-B tangent-bundle section space (no seminormed-fibre diamond). -/
theorem deTurckReactionSectionMap_add_source_exists_isPicardLindelof_of_uniform_inCoordinates
    {κ : Type*} [Finite κ]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a Kp : ℝ≥0) (ha : 0 < (a : ℝ))
    (hKpU : ∀ i (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates E TM E TM (xc i) x (xc i) x (P x)‖ ≤ (Kp : ℝ)) :
    ∃ (T : ℝ) (hT : t₀ < T) (Mc : ℝ≥0),
      IsPicardLindelof
        (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover hP s + b)
        (tmin := t₀) (tmax := T) ⟨t₀, ⟨le_rfl, hT.le⟩⟩ σ0 a 0 (Mc + (2 * Kp) * a) (2 * Kp) := by
  refine exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_continuousOn_topFibre
    (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
      Kc hKc Ko hKo hKoEq hcover hP s + b)
    σ0 t₀ T₀ hT₀ a (2 * Kp) ha ?_ ?_
  · intro t _ht s _hs s' _hs' i x
    simp only [coord_add_apply_topFibre, dist_add_right]
    have h := deTurckReactionSectionMap_coord_dist_le_inCoordinates xc Kc hKc Ko hKo hKoEq hcover hP
      s s' i x (Kp : ℝ) (hKpU i x)
    calc dist _ _ ≤ 2 * (Kp : ℝ) * dist s s' := h
      _ = ((2 * Kp : ℝ≥0) : ℝ) * dist s s' := by push_cast; ring
  · intro s _hs i
    exact continuousOn_const

/-- **Unconditional `IsPicardLindelof` for the affine geometric DeTurck operator (frozen reaction +
fixed source) at `TM`.**  Combining the uniform inCoordinates bound `exists_uniform_inCoord_bound`
(which supplies the uniform Lipschitz constant `Kp` by compactness of the finite cover + continuity of
the frozen coefficient `P`) with the conditional affine construction
`deTurckReactionSectionMap_add_source_exists_isPicardLindelof_of_uniform_inCoordinates`, the affine
operator `A t s = deTurckReactionSectionMap … hP s + b` — frozen reaction plus a FIXED source `b` —
satisfies `IsPicardLindelof` about any initial section `σ₀` with NO uniform-`Kp` hypothesis, only
continuity of `P` and the compact cover.  This is the full frozen chart operator's `picard` datum:
feeding `b := intrinsicRicciFlowRHSSectionSpace g₀` (the `(-2)•Ric` principal Ricci source) and
`P := ∇W` (the frozen DeTurck coefficient) yields the concrete Ricci–DeTurck chart's `picard`, whose
Banach evolution solution decodes to `RicciDeTurckChartClosureData.realization`. -/
theorem deTurckReactionSectionMap_add_source_exists_isPicardLindelof
    {κ : Type*} [Finite κ]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a : ℝ≥0) (ha : 0 < (a : ℝ)) :
    ∃ (Kp : ℝ≥0) (T : ℝ) (hT : t₀ < T) (Mc : ℝ≥0),
      IsPicardLindelof
        (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover hP s + b)
        (tmin := t₀) (tmax := T) ⟨t₀, ⟨le_rfl, hT.le⟩⟩ σ0 a 0 (Mc + (2 * Kp) * a) (2 * Kp) := by
  have hKcTM : ∀ i, (Kc i : Set M) ⊆ (trivializationAt (E →L[ℝ] E) THom (xc i)).baseSet := by
    intro i x hx
    have hxi := hKc i hx
    simpa using hxi
  obtain ⟨Kp, hKp0, hKpb⟩ := exists_uniform_inCoord_bound xc Kc hKcTM hP
  have hcast : ((Kp.toNNReal : ℝ≥0) : ℝ) = Kp := Real.coe_toNNReal Kp hKp0
  obtain ⟨T, hT, Mc, hPL⟩ :=
    deTurckReactionSectionMap_add_source_exists_isPicardLindelof_of_uniform_inCoordinates
      xc Kc hKc Ko hKo hKoEq hcover hP b σ0 t₀ T₀ hT₀ a Kp.toNNReal ha
      (fun i x => by rw [hcast]; exact hKpb i x)
  exact ⟨Kp.toNNReal, T, hT, Mc, hPL⟩

/-- **`BanachEvolutionLocalSolutionIn` for the affine geometric DeTurck operator (frozen reaction +
fixed source) at `TM`.**  Feeding the unconditional affine `IsPicardLindelof`
`deTurckReactionSectionMap_add_source_exists_isPicardLindelof` to the closed-ball a-posteriori bridge
`IsPicardLindelof.exists_banachEvolutionLocalSolutionIn_of_closedBall_subset`, the affine operator
`A t s = deTurckReactionSectionMap … hP s + b` — the frozen DeTurck reaction plus a fixed source `b` —
admits a genuine `BanachEvolutionLocalSolutionIn` in any state locus containing the Picard closed ball
`closedBall σ₀ a`, on a forward window `[t₀, T]` with `T ∈ (t₀, T₀]` auto-chosen.  The tangent-bundle
section space is complete (`instCompleteSpace`, since the model fibre `BilF = E →L[ℝ] E →L[ℝ] ℝ` is
complete), so the closed-ball bridge applies.  This is precisely the state-constrained Banach evolution
solution the downstream `realization` decode into a genuine intrinsic De Turck local solution consumes:
taking `b := intrinsicRicciFlowRHSSectionSpace g₀` (the `(-2)•Ric` principal Ricci source), `P := ∇W`
(the frozen DeTurck coefficient), and `locus :=` the positive-definite / Riemannian-metric cone
(containing the ball for suitably small `a`) yields the chart's `realization` input. -/
theorem deTurckReactionSectionMap_add_source_nonempty_banachEvolutionLocalSolutionIn
    {κ : Type*} [Finite κ]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a : ℝ≥0) (ha : 0 < (a : ℝ))
    (locus : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover))
    (hsub : Metric.closedBall σ0 (a : ℝ) ⊆ locus) :
    ∃ (T : ℝ) (_ : t₀ < T),
      Nonempty (RicciFlow.AnalyticPDE.BanachEvolutionLocalSolutionIn
        (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover hP s + b) locus t₀ σ0) := by
  obtain ⟨Kp, T, hT, Mc, hPL⟩ := deTurckReactionSectionMap_add_source_exists_isPicardLindelof
    xc Kc hKc Ko hKo hKoEq hcover hP b σ0 t₀ T₀ hT₀ a ha
  exact ⟨T, hT,
    IsPicardLindelof.exists_banachEvolutionLocalSolutionIn_of_closedBall_subset hT hPL hsub⟩

/-- **`BanachEvolutionLocalSolutionIn` for the CONCRETE geometric frozen Ricci–DeTurck operator at
`TM`.**  Specialising `deTurckReactionSectionMap_add_source_nonempty_banachEvolutionLocalSolutionIn` to
the genuine geometric data: the frozen DeTurck coefficient `P := ∇W = (chosenLeviCivitaFamily g t)
(intrinsicDeTurckVectorField g background t)` (continuous by
`intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero`, which needs only a `C¹` background
slice `hbackground`), and the principal Ricci source `b := intrinsicRicciFlowRHSSectionSpace … g t`
(the `(-2)•Ric` term as a named `ContinuousSectionSpace` value, pointwise identity
`intrinsicRicciFlowRHSSectionSpace_apply`).  The frozen geometric operator
`A τ s = deTurckReactionSectionMap ∇W s + intrinsicRicciFlowRHSSectionSpace g t` admits a genuine
`BanachEvolutionLocalSolutionIn` in any state locus containing the Picard closed ball `closedBall σ₀ a`,
on a forward window `[t₀, T]` with `T ∈ (t₀, T₀]` auto-chosen — unconditionally (the uniform Lipschitz
`Kp` is discharged by compactness of the finite cover + continuity of `∇W`).  At the metric section
`s = (g t).toSection` this operator reproduces the full intrinsic Ricci–DeTurck RHS
(`deTurckReactionSectionMap_metricSection_add_ricciFlowRHSSection_apply_eq_intrinsicRicciDeTurckRHS`),
so it is the concrete geometric Banach evolution solution the chart-closure `realization` decode into a
genuine intrinsic De Turck local solution consumes. -/
theorem deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn
    {κ : Type*} [Finite κ]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a : ℝ≥0) (ha : 0 < (a : ℝ))
    (locus : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover))
    (hsub : Metric.closedBall σ0 (a : ℝ) ⊆ locus) :
    ∃ (T : ℝ) (_ : t₀ < T),
      Nonempty (RicciFlow.AnalyticPDE.BanachEvolutionLocalSolutionIn
        (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover
          (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
            g background t hbackground).continuous s
          + RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
              Kc hKc Ko hKo hKoEq hcover g t)
        locus t₀ σ0) :=
  deTurckReactionSectionMap_add_source_nonempty_banachEvolutionLocalSolutionIn
    xc Kc hKc Ko hKo hKoEq hcover
    (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
      g background t hbackground).continuous
    (RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
      Kc hKc Ko hKo hKoEq hcover g t)
    σ0 t₀ T₀ hT₀ a ha locus hsub

/-- **The frozen geometric DeTurck reaction operator is `LipschitzOnWith 2·Kp` on any state locus.**
The section-space chart `lipschitz` field for the bare reaction operator `deTurckReactionSectionMap …`:
from a *uniform* bound `Kp` on the frozen coefficient `P`'s model-fibre readout over the finite compact
cover, the per-coordinate Lipschitz bound `deTurckReactionSectionMap_coord_dist_le_inCoordinates` is
lifted to a genuine `LipschitzOnWith ⟨2·Kp, _⟩` on the section space via
`lipschitzOnWith_of_forall_coord_dist_le` (the finite-cover coordinate-to-global norm handoff).  This
is the substantive Lipschitz content of the chart operator's `lipschitz` field. -/
theorem deTurckReactionSectionMap_lipschitzOnWith_of_uniform_inCoordinates
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (Kp : ℝ) (hKp0 : 0 ≤ Kp)
    (hKp : ∀ (i : κ) (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates E TM E TM (x0 i) x (x0 i) x (P x)‖ ≤ Kp)
    (stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)) :
    LipschitzOnWith (NNReal.mk (2 * Kp) (mul_nonneg (by norm_num) hKp0))
      (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP)
      stateSet := by
  refine lipschitzOnWith_of_forall_coord_dist_le ?_
  intro s _hs s' _hs' i x
  simpa only [NNReal.coe_mk] using
    deTurckReactionSectionMap_coord_dist_le_inCoordinates
      x0 Kc hKc Ko hKo hKoEq hcover hP s s' i x Kp (hKp i x)

/-- **The affine frozen geometric DeTurck chart operator `A τ s = deTurckReactionSectionMap ∇W s + b`
is `LipschitzOnWith 2·Kp` on any state locus — the literal chart `lipschitz` field.**  Adding the fixed
source section `b` contributes the same coordinate summand to `A τ s` and `A τ s'`, which cancels in
every compact coordinate distance (`coord_add_apply_topFibre` then the fibre translation isometry
`dist_add_right`), so the reaction's per-coordinate Lipschitz bound
`deTurckReactionSectionMap_coord_dist_le_inCoordinates` transfers verbatim through
`lipschitzOnWith_of_forall_coord_dist_le`.  This is exactly the
`lipschitz : ∀ t, LipschitzOnWith Kstate (A t) locus` field of the
`TimeDependentGeometricRicciDeTurckBanachChart` for the concrete tangent-bundle frozen operator, with
`Kstate = 2·Kp` (uniform over `t`, the operator being time-independent). -/
theorem deTurckReactionSectionMap_add_source_lipschitzOnWith_of_uniform_inCoordinates
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (Kp : ℝ) (hKp0 : 0 ≤ Kp)
    (hKp : ∀ (i : κ) (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates E TM E TM (x0 i) x (x0 i) x (P x)‖ ≤ Kp)
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)) :
    LipschitzOnWith (NNReal.mk (2 * Kp) (mul_nonneg (by norm_num) hKp0))
      (fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP s + b)
      stateSet := by
  refine lipschitzOnWith_of_forall_coord_dist_le ?_
  intro s _hs s' _hs' i x
  simp only [coord_add_apply_topFibre, dist_add_right, NNReal.coe_mk]
  exact deTurckReactionSectionMap_coord_dist_le_inCoordinates
    x0 Kc hKc Ko hKo hKoEq hcover hP s s' i x Kp (hKp i x)

/-- **Global `LipschitzWith 2·Kp` for the bare frozen geometric DeTurck reaction operator.**  The
unconstrained (`LipschitzWith`) strengthening of
`deTurckReactionSectionMap_lipschitzOnWith_of_uniform_inCoordinates`: from a uniform bound `Kp` on the
frozen coefficient `P`'s model-fibre readout over the finite compact cover, the reaction operator
`deTurckReactionSectionMap …` is globally `LipschitzWith ⟨2·Kp, _⟩` on the whole `ContinuousSectionSpace`
via the global finite-cover coordinate handoff `lipschitzWith_of_forall_coord_dist_le` — the exact
`hlip` shape the Banach-space Picard–Lindelöf foundation consumes, and in particular giving global
continuity of the mild representative (`LipschitzWith.continuous`). -/
theorem deTurckReactionSectionMap_lipschitzWith_of_uniform_inCoordinates
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (Kp : ℝ) (hKp0 : 0 ≤ Kp)
    (hKp : ∀ (i : κ) (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates E TM E TM (x0 i) x (x0 i) x (P x)‖ ≤ Kp) :
    LipschitzWith (NNReal.mk (2 * Kp) (mul_nonneg (by norm_num) hKp0))
      (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP) := by
  rw [← lipschitzOnWith_univ]
  exact deTurckReactionSectionMap_lipschitzOnWith_of_uniform_inCoordinates
    x0 Kc hKc Ko hKo hKoEq hcover hP Kp hKp0 hKp Set.univ

/-- **Global `LipschitzWith 2·Kp` for the affine frozen geometric DeTurck chart operator
`A τ s = deTurckReactionSectionMap ∇W s + b`.**  The unconstrained strengthening of
`deTurckReactionSectionMap_add_source_lipschitzOnWith_of_uniform_inCoordinates`: the fixed source `b`
cancels in every coordinate distance (`coord_add_apply_topFibre` + fibre `dist_add_right`), so the affine
chart operator is globally `LipschitzWith ⟨2·Kp, _⟩` on the whole section space — the `hlip` datum of the
Banach-space Picard–Lindelöf foundation for the concrete tangent-bundle chart operator `A`, and giving
its global continuity as a section-space map (`LipschitzWith.continuous`). -/
theorem deTurckReactionSectionMap_add_source_lipschitzWith_of_uniform_inCoordinates
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (Kp : ℝ) (hKp0 : 0 ≤ Kp)
    (hKp : ∀ (i : κ) (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates E TM E TM (x0 i) x (x0 i) x (P x)‖ ≤ Kp)
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    LipschitzWith (NNReal.mk (2 * Kp) (mul_nonneg (by norm_num) hKp0))
      (fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP s + b) := by
  rw [← lipschitzOnWith_univ]
  exact deTurckReactionSectionMap_add_source_lipschitzOnWith_of_uniform_inCoordinates
    x0 Kc hKc Ko hKo hKoEq hcover hP Kp hKp0 hKp b Set.univ

/-- **The affine frozen geometric DeTurck chart operator `A τ s = deTurckReactionSectionMap ∇W s + b`
is continuous as a section-space map.**  Immediate from its global Lipschitz bound
`deTurckReactionSectionMap_add_source_lipschitzWith_of_uniform_inCoordinates`
(`LipschitzWith.continuous`); the concrete geometric chart operator `A`, being globally Lipschitz, is in
particular a continuous self-map of the `ContinuousSectionSpace`. -/
theorem deTurckReactionSectionMap_add_source_continuous_of_uniform_inCoordinates
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (Kp : ℝ) (hKp0 : 0 ≤ Kp)
    (hKp : ∀ (i : κ) (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates E TM E TM (x0 i) x (x0 i) x (P x)‖ ≤ Kp)
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    Continuous
      (fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP s + b) :=
  (deTurckReactionSectionMap_add_source_lipschitzWith_of_uniform_inCoordinates
    x0 Kc hKc Ko hKo hKoEq hcover hP Kp hKp0 hKp b).continuous

/-- **`BanachEvolutionLocalSolutionIn` for the concrete geometric frozen Ricci–DeTurck operator, in the
positive-definite locus, at the initial-metric section.**  Specialising
`deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn` to `locus := positiveDefiniteLocus`
and `σ₀ := g₀.toSection` for a genuine continuous Riemannian metric `g₀`: the geometric a-priori
positivity containment `ContinuousRiemannianMetric.exists_pos_closedBall_toSection_subset_positiveDefiniteLocus`
(openness of the positive-definite locus, from continuity of positive-definiteness on the finite compact
cover) supplies a positive Picard radius `a` whose whole closed ball `closedBall g₀.toSection a` stays
inside the locus, discharging the closed-ball Banach-solution bridge's `hsub` hypothesis.  Hence the
frozen geometric operator `A τ s = deTurckReactionSectionMap ∇W s + intrinsicRicciFlowRHSSectionSpace g t`
admits a genuine `BanachEvolutionLocalSolutionIn` **constrained to the positive-definite locus**, at the
metric section of `g₀`, on a forward window `[t₀, T]` with `T ∈ (t₀, T₀]` auto-chosen — unconditionally
(the uniform Lipschitz `Kp` is discharged by compactness of the finite cover + continuity of `∇W`).  This
is the precise positive-definite-locus-constrained Banach evolution solution the chart-closure
`realization` field consumes (its `sol : BanachEvolutionLocalSolutionIn chart.A (positiveDefiniteLocus …)
ivp.initialTime (ivp initial section)`), assembled here from the two previously independent halves: the
geometric Banach existence and the a-priori positivity containment. -/
theorem deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn_positiveDefiniteLocus
    {κ : Type*} [Finite κ] [Nontrivial E]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric E TM)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) :
    ∃ (T : ℝ) (_ : t₀ < T),
      Nonempty (RicciFlow.AnalyticPDE.BanachEvolutionLocalSolutionIn
        (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover
          (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
            g background t hbackground).continuous s
          + RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
              Kc hKc Ko hKo hKoEq hcover g t)
        (positiveDefiniteLocus (M := M) (F := E) (W := TM)
          (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
        t₀ ⟨g₀.toSection, g₀.continuous_toSection⟩) := by
  obtain ⟨a, ha, hsub⟩ := g₀.exists_pos_closedBall_toSection_subset_positiveDefiniteLocus
    (M := M) (F := E) (W := TM) xc (fun i => trivializationAt BilF BilW (xc i))
    (fun _ => rfl) Kc hKc Ko hKo hKoEq hcover
  exact deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn
    xc Kc hKc Ko hKo hKoEq hcover g background t hbackground
    ⟨g₀.toSection, g₀.continuous_toSection⟩ t₀ T₀ hT₀ a (NNReal.coe_pos.mpr ha) _ hsub

/-- **`BanachEvolutionLocalSolutionIn` for the frozen geometric Ricci–DeTurck operator, in the
positive-definite locus, at the initial section of a Ricci–DeTurck initial value problem.**  The
IVP-vocabulary specialisation of
`deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn_positiveDefiniteLocus` obtained with
`g₀ := ivp.initialMetric.toContinuousRiemannianMetric` and `t₀ := ivp.initialTime`: since
`InitialValueProblem.toContinuousSectionSpace … ivp` is by definition
`⟨ivp.initialMetric.toContinuousRiemannianMetric.toSection, …⟩`, the produced Banach evolution local
solution is anchored exactly at the IVP's initial section, on the IVP's initial time, constrained to the
positive-definite locus.  This is *precisely* the shape of the `sol` argument the chart-closure
`realization` field consumes
(`BanachEvolutionLocalSolutionIn chart.A (positiveDefiniteLocus …) ivp.initialTime
(InitialValueProblem.toContinuousSectionSpace … ivp)`), modulo the identification of the frozen
geometric operator with the chart's `A`. -/
theorem deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn_positiveDefiniteLocus_ivp
    {κ : Type*} [Finite κ] [Nontrivial E]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (ivp : RicciFlow.InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (T₀ : ℝ) (hT₀ : ivp.initialTime < T₀) :
    ∃ (T : ℝ) (_ : ivp.initialTime < T),
      Nonempty (RicciFlow.AnalyticPDE.BanachEvolutionLocalSolutionIn
        (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover
          (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
            g background t hbackground).continuous s
          + RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
              Kc hKc Ko hKo hKoEq hcover g t)
        (positiveDefiniteLocus (M := M) (F := E) (W := TM)
          (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (RicciFlow.AnalyticPDE.MetricLocusEvolution.InitialValueProblem.toContinuousSectionSpace
          (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover ivp)) :=
  deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn_positiveDefiniteLocus
    xc Kc hKc Ko hKo hKoEq hcover g background t hbackground
    ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T₀ hT₀

/-- **`IsPicardLindelof` for the concrete geometric frozen Ricci–DeTurck operator at `TM` — the chart
`picard`-field datum.**  Specialising `deTurckReactionSectionMap_add_source_exists_isPicardLindelof` to
the genuine geometric data: the frozen DeTurck coefficient `P := ∇W = (chosenLeviCivitaFamily g t)
(intrinsicDeTurckVectorField g background t)` (continuous by
`intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero`, needing only a `C¹` background slice
`hbackground`) and the principal Ricci source `b := intrinsicRicciFlowRHSSectionSpace … g t` (the
`(-2)•Ric` term as a named `ContinuousSectionSpace` value).  The frozen geometric operator
`A τ s = deTurckReactionSectionMap ∇W s + intrinsicRicciFlowRHSSectionSpace g t` satisfies
`IsPicardLindelof` about any initial section `σ₀`, on an auto-chosen forward window `[t₀, T]` with
`T ∈ (t₀, T₀]`, with radius `a`, Lipschitz constant `2·Kp` and centre size `Mc + 2·Kp·a` — all produced
internally (the uniform Lipschitz `Kp` discharged by compactness of the finite cover + continuity of
`∇W`, the centre bound derived from continuity of the readout on the compact window).  This is the
literal `picard` datum of the `TimeDependentGeometricRicciDeTurckBanachChart` for the concrete
tangent-bundle geometric operator; the companion
`deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn` feeds this very datum to the
closed-ball a-posteriori bridge to obtain the chart's Banach evolution solution. -/
theorem deTurckFrozenGeometric_exists_isPicardLindelof
    {κ : Type*} [Finite κ]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) (a : ℝ≥0) (ha : 0 < (a : ℝ)) :
    ∃ (Kp : ℝ≥0) (T : ℝ) (hT : t₀ < T) (Mc : ℝ≥0),
      IsPicardLindelof
        (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover
          (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
            g background t hbackground).continuous s
          + RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
              Kc hKc Ko hKo hKoEq hcover g t)
        (tmin := t₀) (tmax := T) ⟨t₀, ⟨le_rfl, hT.le⟩⟩ σ0 a 0 (Mc + (2 * Kp) * a) (2 * Kp) :=
  deTurckReactionSectionMap_add_source_exists_isPicardLindelof
    xc Kc hKc Ko hKo hKoEq hcover
    (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
      g background t hbackground).continuous
    (RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
      Kc hKc Ko hKo hKoEq hcover g t)
    σ0 t₀ T₀ hT₀ a ha

/-- **The tangent-bundle DeTurck reaction operator lands in the pointwise symmetric locus.**  By
`deTurckReactionSectionMap_apply`, `deTurckReactionSectionMap … hP s x u v = s x (P x u) v +
s x (P x v) u` is manifestly symmetric in `(u, v)` (the two summands merely swap), so the reaction
operator maps *every* section `s` — symmetric or not — into the symmetric locus.  This is the
operator-level (set-membership) companion of the pointwise `intrinsicDeTurckCorrectionSectionSpace_symm`
value symmetry: it is exactly the datum certifying that the reaction summand of the affine chart split
`A τ s = reaction s + b` keeps the Banach velocity in `symmetricLocus`. -/
theorem deTurckReactionSectionMap_mem_symmetricLocus
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization BilF
      (TotalSpace.proj : TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) :
    deTurckReactionSectionMap et Kc hKc Ko hKo hKoEq hcover hP s
      ∈ symmetricLocus (M := M) (F := E) (W := TM) et Kc hKc Ko hKo hKoEq hcover := by
  intro x u v
  simp only [deTurckReactionSectionMap_apply]
  ring

/-- **The affine DeTurck reaction operator preserves the symmetric locus.**  Adding a symmetric
source `b` to the reaction value keeps the result symmetric: `deTurckReactionSectionMap … hP s + b`
lies in the pointwise symmetric locus whenever `b` does.  This is the operator-level statement for the
whole affine chart split `A τ s = reaction s + b`; combined with symmetry of the concrete `(-2)•Ric`
source it certifies the geometric Ricci–DeTurck chart velocity is symmetric. -/
theorem deTurckReactionSectionMap_add_mem_symmetricLocus
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (et : κ → Trivialization BilF
      (TotalSpace.proj : TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)
    (hb : b ∈ symmetricLocus (M := M) (F := E) (W := TM) et Kc hKc Ko hKo hKoEq hcover)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) :
    (deTurckReactionSectionMap et Kc hKc Ko hKo hKoEq hcover hP s + b)
      ∈ symmetricLocus (M := M) (F := E) (W := TM) et Kc hKc Ko hKo hKoEq hcover := by
  have hr := deTurckReactionSectionMap_mem_symmetricLocus
    et Kc hKc Ko hKo hKoEq hcover hP s
  rw [← mem_symmetricSectionSubmodule_iff x0 et het Kc hKc Ko hKo hKoEq hcover] at hr hb ⊢
  exact add_mem hr hb

/-- **The concrete geometric frozen Ricci–DeTurck chart operator lands in the symmetric locus.**
For every section `s`, the frozen geometric operator value
`A s = deTurckReactionSectionMap ∇W s + intrinsicRicciFlowRHSSectionSpace g t` — the operator whose
`IsPicardLindelof` is `deTurckFrozenGeometric_exists_isPicardLindelof` — lies in the pointwise
symmetric locus.  The `∇W` reaction summand is symmetric unconditionally
(`deTurckReactionSectionMap_mem_symmetricLocus`) and the principal `(-2)•Ric` source is symmetric by
`intrinsicRicciFlowRHSSectionSpace_symm`.  This is the direct (frozen-operator) analogue of
`TimeDependentGeometricRicciDeTurckBanachChart.A_mem_symmetricLocus`, established here without routing
through the chart's `geometric` identification field: it certifies that the Banach evolution velocity
of the geometric chart operator is symmetric, so its solution curve stays a symmetric metric family. -/
theorem deTurckFrozenGeometric_A_mem_symmetricLocus
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover) :
    (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
        Kc hKc Ko hKo hKoEq hcover
        (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
          g background t hbackground).continuous s
      + RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover g t)
      ∈ symmetricLocus (M := M) (F := E) (W := TM)
          (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover :=
  deTurckReactionSectionMap_add_mem_symmetricLocus
    xc (fun i => trivializationAt BilF BilW (xc i)) (fun _ => rfl) Kc hKc Ko hKo hKoEq hcover
    (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
      g background t hbackground).continuous
    (RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
      Kc hKc Ko hKo hKoEq hcover g t)
    (fun x u v => RicciFlow.intrinsicRicciFlowRHSSectionSpace_symm
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover g t x u v)
    s

/-- **The geometric frozen Ricci–DeTurck chart operator has vanishing coordinatewise symmetry
defect.**  The `coordwiseSymmetryDefectContinuousLinearMap` form of
`deTurckFrozenGeometric_A_mem_symmetricLocus`, obtained through
`coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff`: the transported coordinatewise
antisymmetric-defect readout of the frozen geometric operator value vanishes.  This is the direct
(frozen-operator) analogue of
`TimeDependentGeometricRicciDeTurckBanachChart.A_coordwiseSymmetryDefect_eq_zero` — the defect-zero
datum the symmetric-carrier / interval-defect chart machinery consumes — obtained here without the
chart's `geometric` identification field. -/
theorem deTurckFrozenGeometric_A_coordwiseSymmetryDefect_eq_zero
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover) :
    coordwiseSymmetryDefectContinuousLinearMap (F := E) (V := BilW)
        (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover
        (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
            Kc hKc Ko hKo hKoEq hcover
            (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
              g background t hbackground).continuous s
          + RicciFlow.intrinsicRicciFlowRHSSectionSpace
              (fun i => trivializationAt BilF BilW (xc i))
              Kc hKc Ko hKo hKoEq hcover g t) = 0 :=
  (coordwiseSymmetryDefectContinuousLinearMap_eq_zero_iff
    (M := M) (F := E) (W := TM)
    xc (fun i => trivializationAt BilF BilW (xc i)) (fun _ => rfl)
    Kc hKc Ko hKo hKoEq hcover
    (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
        Kc hKc Ko hKo hKoEq hcover
        (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
          g background t hbackground).continuous s
      + RicciFlow.intrinsicRicciFlowRHSSectionSpace
          (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover g t)).2
    (deTurckFrozenGeometric_A_mem_symmetricLocus
      xc Kc hKc Ko hKo hKoEq hcover g background t hbackground s)

/-- **The frozen geometric Ricci–DeTurck operator's Banach evolution solution stays in the symmetric
positive-definite locus.**  Strengthening
`deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn_positiveDefiniteLocus` with a *symmetric*
conclusion: the concrete frozen geometric operator
`A τ s = deTurckReactionSectionMap ∇W s + intrinsicRicciFlowRHSSectionSpace g t`, whose
`IsPicardLindelof` datum is `deTurckFrozenGeometric_exists_isPicardLindelof` and whose uniform Lipschitz
control is `deTurckReactionSectionMap_add_source_lipschitzOnWith_of_uniform_inCoordinates`, admits a
Banach evolution local solution — anchored at the metric section `g₀.toSection` of a genuine continuous
Riemannian metric `g₀`, constrained to the positive-definite locus, forward-unique on the overlap of
Picard intervals — whose curve additionally stays in the *symmetric* positive-definite locus at every
time of its interval.  The symmetric containment is obtained WITHOUT the chart's `geometric`
identification field: it is fed purely by the frozen operator's velocity symmetry
`deTurckFrozenGeometric_A_mem_symmetricLocus` (`A τ s ∈ symmetricLocus` for every section `s`) through
the ODE symmetric-carrier invariance
`exists_unique_in_symmetricPositiveDefiniteLocus_of_symmetricTimeDependentVectorField_isPicardLindelof_lipschitzOn`
(the coordinatewise antisymmetric defect satisfies the same linear ODE, starts at `0` since `g₀` is
symmetric, hence stays `0`).  This certifies the frozen geometric Banach solution curve is a genuine
symmetric-positive-definite metric family — the realization-side consistency datum a `RicciDeTurckChart`
closure needs for its `sol` to decode into an intrinsic metric evolution — available independently of
the `geometric`/`realization` parabolic reconciliation. -/
theorem deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn_symmetricPositiveDefiniteLocus
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [Nontrivial E]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric E TM)
    (t₀ T₀ : ℝ) (hT₀ : t₀ < T₀) :
    ∃ sol : RicciFlow.AnalyticPDE.BanachEvolutionLocalSolutionIn
        (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover
          (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
            g background t hbackground).continuous s
          + RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
              Kc hKc Ko hKo hKoEq hcover g t)
        (positiveDefiniteLocus (M := M) (F := E) (W := TM)
          (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
        t₀ ⟨g₀.toSection, g₀.continuous_toSection⟩,
      (∀ sol' : RicciFlow.AnalyticPDE.BanachEvolutionLocalSolutionIn
          (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
            Kc hKc Ko hKo hKoEq hcover
            (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
              g background t hbackground).continuous s
            + RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
                Kc hKc Ko hKo hKoEq hcover g t)
          (positiveDefiniteLocus (M := M) (F := E) (W := TM)
            (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
          t₀ ⟨g₀.toSection, g₀.continuous_toSection⟩,
        Set.EqOn sol.curve sol'.curve
          (Set.Icc t₀ (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃τ : ℝ⦄, τ ∈ Set.Icc t₀ sol.terminalTime →
        sol.curve τ ∈ symmetricPositiveDefiniteLocus (M := M) (F := E) (W := TM)
          (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover := by
  have hKcTM : ∀ i, (Kc i : Set M) ⊆ (trivializationAt (E →L[ℝ] E) THom (xc i)).baseSet := by
    intro i x hx
    have hxi := hKc i hx
    simpa using hxi
  obtain ⟨Kp', hKp'0, hKp'b⟩ := exists_uniform_inCoord_bound xc Kc hKcTM
    (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
      g background t hbackground).continuous
  obtain ⟨Kp, T, hT, Mc, hPL⟩ := deTurckFrozenGeometric_exists_isPicardLindelof
    xc Kc hKc Ko hKo hKoEq hcover g background t hbackground
    ⟨g₀.toSection, g₀.continuous_toSection⟩ t₀ T₀ hT₀ 1 (by norm_num)
  exact RicciFlow.AnalyticPDE.MetricLocusEvolution.exists_unique_in_symmetricPositiveDefiniteLocus_of_symmetricTimeDependentVectorField_isPicardLindelof_lipschitzOn
    (M := M) (F := E) (W := TM)
    xc (fun i => trivializationAt BilF BilW (xc i)) (fun _ => rfl)
    Kc hKc Ko hKo hKoEq hcover inferInstance hT hPL
    (mem_symmetricPositiveDefiniteLocus_of_continuousRiemannianMetric
      (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover g₀)
    (fun _ => deTurckReactionSectionMap_add_source_lipschitzOnWith_of_uniform_inCoordinates
      xc Kc hKc Ko hKo hKoEq hcover
      (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
        g background t hbackground).continuous Kp' hKp'0 hKp'b
      (RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
        Kc hKc Ko hKo hKoEq hcover g t)
      (positiveDefiniteLocus (M := M) (F := E) (W := TM)
        (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover))
    (fun _ s _ => deTurckFrozenGeometric_A_mem_symmetricLocus
      xc Kc hKc Ko hKo hKoEq hcover g background t hbackground s)

/-- **The frozen geometric Ricci–DeTurck Banach solution stays symmetric positive-definite, in the
IVP vocabulary the chart-closure `realization` field consumes.**  The initial-value-problem
specialisation of
`deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn_symmetricPositiveDefiniteLocus`
obtained with `g₀ := ivp.initialMetric.toContinuousRiemannianMetric` and `t₀ := ivp.initialTime`: since
`InitialValueProblem.toContinuousSectionSpace … ivp` is by definition
`⟨ivp.initialMetric.toContinuousRiemannianMetric.toSection, …⟩`, the produced solution is anchored
exactly at the IVP's initial section, on the IVP's initial time, constrained to the positive-definite
locus, forward-unique, and — the new content — its curve stays in the *symmetric* positive-definite
locus at every time of its interval.  This is *precisely* the shape of the `sol` argument the
chart-closure `realization` field consumes
(`BanachEvolutionLocalSolutionIn chart.A (positiveDefiniteLocus …) ivp.initialTime
(InitialValueProblem.toContinuousSectionSpace … ivp)`), now additionally certified to trace a
symmetric-positive-definite metric family — modulo the identification of the frozen geometric operator
with the chart's `A`.  The symmetric containment is fed purely by the frozen operator's velocity
symmetry (`deTurckFrozenGeometric_A_mem_symmetricLocus`), independent of the chart's `geometric`
identification field. -/
theorem deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn_symmetricPositiveDefiniteLocus_ivp
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    {κ : Type*} [Finite κ] [Nontrivial E]
    (xc : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (xc i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : RicciFlow.MetricFamily (I := I) (M := M))
    (background : RicciFlow.ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (ivp : RicciFlow.InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (T₀ : ℝ) (hT₀ : ivp.initialTime < T₀) :
    ∃ sol : RicciFlow.AnalyticPDE.BanachEvolutionLocalSolutionIn
        (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
          Kc hKc Ko hKo hKoEq hcover
          (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
            g background t hbackground).continuous s
          + RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
              Kc hKc Ko hKo hKoEq hcover g t)
        (positiveDefiniteLocus (M := M) (F := E) (W := TM)
          (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
        ivp.initialTime
        (RicciFlow.AnalyticPDE.MetricLocusEvolution.InitialValueProblem.toContinuousSectionSpace
          (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover ivp),
      (∀ sol' : RicciFlow.AnalyticPDE.BanachEvolutionLocalSolutionIn
          (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (xc i))
            Kc hKc Ko hKo hKoEq hcover
            (RicciFlow.intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
              g background t hbackground).continuous s
            + RicciFlow.intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (xc i))
                Kc hKc Ko hKo hKoEq hcover g t)
          (positiveDefiniteLocus (M := M) (F := E) (W := TM)
            (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover)
          ivp.initialTime
          (RicciFlow.AnalyticPDE.MetricLocusEvolution.InitialValueProblem.toContinuousSectionSpace
            (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover ivp),
        Set.EqOn sol.curve sol'.curve
          (Set.Icc ivp.initialTime (min sol.terminalTime sol'.terminalTime))) ∧
      ∀ ⦃τ : ℝ⦄, τ ∈ Set.Icc ivp.initialTime sol.terminalTime →
        sol.curve τ ∈ symmetricPositiveDefiniteLocus (M := M) (F := E) (W := TM)
          (fun i => trivializationAt BilF BilW (xc i)) Kc hKc Ko hKo hKoEq hcover :=
  deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn_symmetricPositiveDefiniteLocus
    xc Kc hKc Ko hKo hKoEq hcover g background t hbackground
    ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T₀ hT₀

/-! ### Linearity of the frozen-coefficient DeTurck reaction operator (raw-function level)

The frozen (coefficient-frozen) DeTurck reaction operator `deTurckReactionSectionMap … hP`, whose
pointwise action `s x u v = s x (P x u) v + s x (P x v) u` is manifestly **linear** in the section `s`,
is the bounded-linear generator whose autonomous resolvent `exp ((t - t₀) • ·)`
(`AutonomousResolventExp`) is intended to supply the `SmoothMetricSectionCurveData.contMDiff`
realization field of the frozen geometric chart.

This section establishes the **raw-function-level linearity** of the underlying map
`bilinearFormSectionDeTurckReaction` (`bilinearFormSectionDeTurckReaction_add`/`_smul`), proved at the
canonical `BilinearFormBundle` fibre (fibre-diamond-free), together with the definitional bridge
`deTurckReactionSectionMap_toFun` from the operator to that raw map.  These are the wall-free ingredients
of the section-space `map_add'`/`map_smul'` linear packaging; the final packaging as a
`ContinuousLinearMap` additionally requires transporting these through the `ContinuousSectionSpace`
add/smul, which meets the `BilinearFormBundle` concreteness whnf wall on the *reaction sections* and is
the remaining obstruction to the bundled `CSS →L[ℝ] CSS` generator. -/

/-- **The raw (Pi-function-level) DeTurck reaction is additive in the section function.**  Proved at the
canonical `BilinearFormBundle` fibre `BilW x = TM x →L[ℝ] TM x →L[ℝ] ℝ` (standard `ContinuousLinearMap`
instances, *not* the transported section-space add), so `ContinuousLinearMap.add_apply` and `Pi.add_apply`
reduce it to the scalar rearrangement `add_add_add_comm`.  This is the fibre-diamond-free core of the
section-map additivity: it avoids the `ContinuousSectionSpace` transported-add whnf wall by working on the
underlying `Π x, BilW x` function. -/
theorem bilinearFormSectionDeTurckReaction_add
    (f g : Π x : M, BilW x)
    (P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x) :
    RicciFlow.bilinearFormSectionDeTurckReaction (I := I) (M := M) (f + g) P
      = RicciFlow.bilinearFormSectionDeTurckReaction (I := I) (M := M) f P
        + RicciFlow.bilinearFormSectionDeTurckReaction (I := I) (M := M) g P := by
  funext x
  refine ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun v => ?_
  simp only [Pi.add_apply, RicciFlow.bilinearFormSectionDeTurckReaction_apply,
    ContinuousLinearMap.add_apply]
  exact add_add_add_comm _ _ _ _

/-- **The raw (Pi-function-level) DeTurck reaction is homogeneous in the section function.**  Companion of
`bilinearFormSectionDeTurckReaction_add`; proved at the canonical fibre so `ContinuousLinearMap.smul_apply`
and `Pi.smul_apply` reduce it to `smul_add`, avoiding the transported section-space smul. -/
theorem bilinearFormSectionDeTurckReaction_smul
    (c : ℝ) (f : Π x : M, BilW x)
    (P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x) :
    RicciFlow.bilinearFormSectionDeTurckReaction (I := I) (M := M) (c • f) P
      = c • RicciFlow.bilinearFormSectionDeTurckReaction (I := I) (M := M) f P := by
  funext x
  refine ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun v => ?_
  simp only [Pi.smul_apply, RicciFlow.bilinearFormSectionDeTurckReaction_apply,
    ContinuousLinearMap.smul_apply]
  exact (smul_add c _ _).symm

/-- The underlying section function of the frozen DeTurck reaction operator is the raw
`bilinearFormSectionDeTurckReaction`; definitional, used to bridge the operator to the raw
Pi-function-level additivity/homogeneity lemmas. -/
@[simp] theorem deTurckReactionSectionMap_toFun
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization BilF
      (TotalSpace.proj : TotalSpace BilF BilW → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover) :
    (deTurckReactionSectionMap et Kc hKc Ko hKo hKoEq hcover hP s).toFun
      = RicciFlow.bilinearFormSectionDeTurckReaction (I := I) (M := M) s.toFun P :=
  rfl

/-- **CSS-level additivity of the frozen tangent-bundle DeTurck reaction operator.**  The concrete
section-space DeTurck reaction map `deTurckReactionSectionMap … hP` is additive as a map of
`ContinuousSectionSpace`s: `A (s + t) = A s + A t`.  Proved wall-free at `W := TangentSpace I` by
reducing to the raw-`Pi` reaction additivity `bilinearFormSectionDeTurckReaction_add` after splitting
both the input sum `(s + t).toFun` and the output sum `(A s + A t).toFun` through the diamond-free
pointwise add `add_apply_tangent` (which avoids the seminormed-track `add_apply`'s `BilinearFormBundle`
fibre `isDefEq` timeout).  This is the additivity half of the bounded-linear packaging of the frozen
reaction operator (`CSS →L[ℝ] CSS`) that feeds the autonomous resolvent. -/
theorem deTurckReactionSectionMap_map_add
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (s t : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP (s + t)
      = deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP s
        + deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP t := by
  refine ContinuousSectionSpace.ext (fun x => ?_)
  rw [add_apply_tangent x0 Kc hKc Ko hKo hKoEq hcover
      (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP s)
      (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP t) x]
  simp only [deTurckReactionSectionMap_toFun]
  rw [show (s + t).toFun = s.toFun + t.toFun from
      funext (add_apply_tangent x0 Kc hKc Ko hKo hKoEq hcover s t),
    bilinearFormSectionDeTurckReaction_add]
  rfl

/-- **Pointwise homogeneity of the tangent-bundle continuous section space at the hom fibre topology.**
`(c • s).toFun x = c • s.toFun x` for a scalar `c` and a section `s` of the canonical
`BilinearFormBundle` continuous section space at `W := TangentSpace I`.  The scalar companion of
`add_apply_tangent`: same wall-free coordinate route (recover each section value from its compact
coordinate via the trivialization's linear inverse `symmₗ`, split the coordinate of `c • s`
homogeneously through the compact-coordinate `ContinuousLinearMap`'s `map_smul`, then use that `symmₗ`
is `ℝ`-linear), touching only `IsLinear`-level (Pretrivialization) API so the
`FiberBundle`/fibre-`TopologicalSpace` diamond is never triggered. -/
theorem smul_apply_tangent
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (c : ℝ)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (x : M) :
    (c • s).toFun x = c • s.toFun x := by
  obtain ⟨i, hi⟩ : ∃ i, x ∈ (Kc i : Set M) :=
    Set.mem_iUnion.mp (by rw [hcover]; exact Set.mem_univ x)
  have hx : x ∈ (trivializationAt BilF BilW (x0 i)).baseSet := hKc i hi
  haveI hlin : (trivializationAt BilF BilW (x0 i)).IsLinear ℝ :=
    _root_.Bundle.trivializationAt_bilinearFormBundle_isLinear (F := E) (W := TM) (x0 i)
  have hsymm : ∀ (σ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover),
      σ.toFun x = (trivializationAt BilF BilW (x0 i)).symmₗ ℝ x
        ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
          (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover σ).1 i ⟨x, hi⟩) := by
    intro σ
    rw [coord_apply_tangent x0 Kc hKc Ko hKo hKoEq hcover σ i ⟨x, hi⟩,
      Trivialization.continuousLinearMapAt_apply]
    exact ((trivializationAt BilF BilW (x0 i)).symmₗ_linearMapAt hx (σ.toFun x)).symm
  have hcoord : (equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover (c • s)).1 i ⟨x, hi⟩
      = c • (equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
          (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover s).1 i ⟨x, hi⟩ := by
    have he : equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
          (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover (c • s)
        = c • equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
            (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover s := by
      rw [← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
            (𝕜 := ℝ) (F := BilF) (V := BilW)
            (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover,
        ← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
            (𝕜 := ℝ) (F := BilF) (V := BilW)
            (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover (s := s),
        map_smul]
    rw [he]
    simp only [SetLike.val_smul, Pi.smul_apply, ContinuousMap.smul_apply]
  rw [hsymm s, hsymm (c • s), hcoord, map_smul]

/-- **CSS-level homogeneity of the frozen tangent-bundle DeTurck reaction operator.**  Companion of
`deTurckReactionSectionMap_map_add`: the concrete section-space DeTurck reaction map is homogeneous as a
map of `ContinuousSectionSpace`s, `A (c • s) = c • A s`.  Same wall-free strategy — reduce to the
raw-`Pi` reaction homogeneity `bilinearFormSectionDeTurckReaction_smul` after splitting both the input
`(c • s).toFun` and the output `(c • A s).toFun` through the diamond-free pointwise smul
`smul_apply_tangent`.  With `deTurckReactionSectionMap_map_add` this is the linear-map data for packaging
the frozen reaction operator as a bounded `CSS →L[ℝ] CSS`. -/
theorem deTurckReactionSectionMap_map_smul
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (c : ℝ)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP (c • s)
      = c • deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP s := by
  refine ContinuousSectionSpace.ext (fun x => ?_)
  rw [smul_apply_tangent x0 Kc hKc Ko hKo hKoEq hcover c
      (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP s) x]
  simp only [deTurckReactionSectionMap_toFun]
  rw [show (c • s).toFun = c • s.toFun from
      funext (smul_apply_tangent x0 Kc hKc Ko hKo hKoEq hcover c s),
    bilinearFormSectionDeTurckReaction_smul]
  rfl

/-- **The frozen tangent-bundle DeTurck reaction operator bundled as a bounded linear map
`CSS →L[ℝ] CSS`.**  Packages the raw section-space reaction self-map `deTurckReactionSectionMap … hP`
into a `ContinuousLinearMap`: its additivity/homogeneity are the just-committed
`deTurckReactionSectionMap_map_add`/`deTurckReactionSectionMap_map_smul`, and its continuity is
UNCONDITIONAL — the uniform inCoordinates bound `exists_uniform_inCoord_bound` (from continuity of the
frozen coefficient `P` on the compact cover) feeds the global Lipschitz bound
`deTurckReactionSectionMap_lipschitzWith_of_uniform_inCoordinates`, whose `.continuous` discharges the
`cont` field with no `Kp` hypothesis.  This is the bounded-linear operator consumed by the autonomous
resolvent `exp((t - t₀) • ·)` for the frozen (linear-part) Ricci–DeTurck evolution. -/
noncomputable def deTurckReactionSectionMapL
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x))) :
    ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover
      →L[ℝ] ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover where
  toFun := deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
    Kc hKc Ko hKo hKoEq hcover hP
  map_add' := deTurckReactionSectionMap_map_add x0 Kc hKc Ko hKo hKoEq hcover hP
  map_smul' := deTurckReactionSectionMap_map_smul x0 Kc hKc Ko hKo hKoEq hcover hP
  cont := by
    obtain ⟨Kp, hKp0, hKpb⟩ :=
      exists_uniform_inCoord_bound x0 Kc (fun i x hx => by simpa using hKc i hx) hP
    exact (deTurckReactionSectionMap_lipschitzWith_of_uniform_inCoordinates
      x0 Kc hKc Ko hKo hKoEq hcover hP Kp hKp0 hKpb).continuous

/-- The bounded-linear packaging `deTurckReactionSectionMapL` applies as the raw reaction self-map. -/
@[simp] theorem deTurckReactionSectionMapL_apply
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    deTurckReactionSectionMapL x0 Kc hKc Ko hKo hKoEq hcover hP s
      = deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP s :=
  rfl

/-- **Operator-norm bound `‖deTurckReactionSectionMapL‖ ≤ 2·Kp` for the frozen geometric DeTurck
reaction as a bounded linear map.**  The genuine operator-norm control of the *real* (geometric,
non-model) zeroth-order Ricci–DeTurck reaction generator on the `BilinearFormBundle` continuous section
space: from a uniform bound `Kp` on the model-fibre readout of the frozen tangent-endomorphism
coefficient `P` over the finite compact cover, the bounded-linear reaction map has operator norm at most
`2·Kp`.  Obtained from its global `LipschitzWith ⟨2·Kp, _⟩`
(`deTurckReactionSectionMap_lipschitzWith_of_uniform_inCoordinates`) evaluated against the origin
(`map_zero`), fed to `ContinuousLinearMap.opNorm_le_bound`.  This is the operator-norm growth constant a
mild/semigroup formulation consumes to bound the affine resolvent `exp(τ·L)` of the frozen chart split
`A τ s = L s + b` — a coordinate/operator bound for the honest geometric reaction operator, not a model
heat-kernel estimate. -/
theorem deTurckReactionSectionMapL_opNorm_le
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (Kp : ℝ) (hKp0 : 0 ≤ Kp)
    (hKp : ∀ (i : κ) (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates E TM E TM (x0 i) x (x0 i) x (P x)‖ ≤ Kp) :
    ‖deTurckReactionSectionMapL x0 Kc hKc Ko hKo hKoEq hcover hP‖ ≤ 2 * Kp := by
  have hlip := deTurckReactionSectionMap_lipschitzWith_of_uniform_inCoordinates
    x0 Kc hKc Ko hKo hKoEq hcover hP Kp hKp0 hKp
  let z : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover := 0
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun s => ?_)
  have h0 : deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
      Kc hKc Ko hKo hKoEq hcover hP 0 = 0 :=
    (deTurckReactionSectionMapL x0 Kc hKc Ko hKo hKoEq hcover hP).map_zero
  rw [deTurckReactionSectionMapL_apply]
  calc ‖deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP s‖
      = dist (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP s)
          (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP 0) := by
        rw [h0]
        exact (dist_zero_right
          (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
            Kc hKc Ko hKo hKoEq hcover hP s)).symm
    _ ≤ 2 * Kp * dist s 0 := by simpa [z] using hlip.dist_le_mul s z
    _ = 2 * Kp * ‖s‖ := congrArg (fun t => 2 * Kp * t) (dist_zero_right s)

/-- **Whole-section growth bound `‖A σ‖ ≤ 2·Kp·‖σ‖ + ‖b‖` for the affine frozen geometric DeTurck
chart operator `A σ = deTurckReactionSectionMap ∇W σ + b`.**  The continuous-section-space-norm (not
per-coordinate) growth/centre bound of the *real* geometric chart operator: the linear reaction part is
controlled by its operator norm `‖deTurckReactionSectionMapL ∇W‖ ≤ 2·Kp`
(`deTurckReactionSectionMapL_opNorm_le`, via `ContinuousLinearMap.le_opNorm`), and the fixed source `b`
adds at most `‖b‖` through the triangle inequality `norm_add_le`.  Evaluated at `σ = σ0` this is exactly
the `Mc = 2·Kp·‖σ0‖ + ‖b‖` centre-size shape the section-space Picard/mild estimates consume — the honest
geometric operator's growth bound in clean whole-section-norm form, complementing the per-coordinate
`bilinearDerivationFieldLinearMap_add_source_coord_norm_le`. -/
theorem deTurckReactionSectionMap_add_source_norm_le
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {P : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x}
    (hP : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x (P x)))
    (Kp : ℝ) (hKp0 : 0 ≤ Kp)
    (hKp : ∀ (i : κ) (x : Kc i),
      ‖ContinuousLinearMap.inCoordinates E TM E TM (x0 i) x (x0 i) x (P x)‖ ≤ Kp)
    (b σ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    ‖deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP σ + b‖ ≤ 2 * Kp * ‖σ‖ + ‖b‖ := by
  have hop := deTurckReactionSectionMapL_opNorm_le
    x0 Kc hKc Ko hKo hKoEq hcover hP Kp hKp0 hKp
  have hL : ‖deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
      Kc hKc Ko hKo hKoEq hcover hP σ‖ ≤ 2 * Kp * ‖σ‖ := by
    rw [← deTurckReactionSectionMapL_apply]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hop (norm_nonneg σ))
  calc ‖deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP σ + b‖
      ≤ ‖deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP σ‖ + ‖b‖ := norm_add_le
          (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
            Kc hKc Ko hKo hKoEq hcover hP σ) b
    _ ≤ 2 * Kp * ‖σ‖ + ‖b‖ := by linarith [hL]

end PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace
