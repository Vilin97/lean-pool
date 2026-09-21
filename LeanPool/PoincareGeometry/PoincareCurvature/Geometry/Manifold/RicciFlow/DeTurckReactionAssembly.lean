/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurckCorrectionRegularity
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.RiemannianSection

/-!
# Assembling the intrinsic DeTurck reaction operator on the section space

The intrinsic Ricci–DeTurck reaction term is the two-sided derivation
`intrinsicDeTurckCorrection g background t x u v = (g t).inner x (∇W u) v + (g t).inner x u (∇W v)`,
where `∇W = (chosenLeviCivitaFamily g t) (intrinsicDeTurckVectorField g background t)` is the
covariant derivative of the intrinsic DeTurck vector field.  The frozen-coefficient section-space
representative of this operator is the bounded operator
`ContinuousSectionSpace.bilinearDerivationField` (built in `VectorBundle/RiemannianSection.lean`),
whose fiberwise action on a section `s` is `x ↦ s(P·, ·) + s(·, P·)` for a continuous
tangent-endomorphism section `P` (its defining identity is `bilinearDerivationField_apply_apply`).

This module supplies the **assembly identity** connecting the two at the fiber-value level: with the
frozen coefficient `P := ∇W`, the fiberwise two-sided derivation of any `ContinuousSectionSpace`
element `sMetric` that agrees pointwise with the metric `(g t).inner` reproduces exactly the geometric
`intrinsicDeTurckCorrectionSection`.  Composed with `bilinearDerivationField_apply_apply` this is the
DeTurck half of the chart operator `A`'s `geometric` identification field: the abstract bounded
reaction operator and the concrete geometric DeTurck term coincide on the metric section.

The result is stated at the fiber-value level (the two-sided derivation applied to `sMetric`) rather
than through a formed `bilinearDerivationField` instance, because instantiating that operator at the
tangent bundle `W := TangentSpace I` triggers an instance diamond: the operator-norm size datum
`‖P x‖` needs `Norm (TangentSpace I x →L[ℝ] TangentSpace I x)`, which is only reachable through the
definitional equality `TangentSpace I x = E`, and it must moreover be mutually consistent with the
`FiberBundle`/`VectorBundle` tangent structure that the same operator demands.  The fiber-value form
here is exactly what such a formed operator evaluates to, so it is directly consumable by the chart
assembly once that instance datum is supplied at the construction site.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff Topology
open PoincareCurvature.Bundle.Trivialization

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)
/-- **The frozen-coefficient DeTurck reaction of the metric section is the geometric DeTurck
correction.**  Let `∇W = (chosenLeviCivitaFamily g t) (intrinsicDeTurckVectorField g background t)` be
the covariant derivative of the intrinsic DeTurck vector field (the frozen endomorphism coefficient).
For any `ContinuousSectionSpace` element `sMetric` agreeing pointwise with the metric `(g t).inner`,
the fiberwise two-sided derivation
`x ↦ sMetric x (∇W x u) v + sMetric x u (∇W x v)` equals, at every base point and tangent pair,
the geometric `intrinsicDeTurckCorrectionSection g background t`.

This is the fiber-value content of applying the section-space reaction operator
`ContinuousSectionSpace.bilinearDerivationField` (whose fiberwise action is exactly this two-sided
derivation, `bilinearDerivationField_apply_apply`) with frozen coefficient `P := ∇W` to `sMetric`:
the abstract bounded reaction operator reproduces the concrete geometric Ricci–DeTurck reaction term
on the metric section, i.e. the DeTurck half of the chart operator `A`'s `geometric` field. -/
theorem metricSection_deTurckDerivation_eq_intrinsicDeTurckCorrectionSection
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (sMetric : ContinuousSectionSpace (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ)
      (V := _root_.Bundle.BilinearFormBundle (V := TM)) et Kc hKc Ko hKo hKoEq hcover)
    (hsMetric : ∀ (x : M) (u v : TM x), sMetric x u v = (g t).inner x u v)
    (x : M) (u v : TM x) :
    sMetric x
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x u) v
      + sMetric x u
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x v)
      = intrinsicDeTurckCorrectionSection (I := I) (M := M) g background t x u v := by
  rw [hsMetric, hsMetric, intrinsicDeTurckCorrectionSection_apply,
    intrinsicDeTurckCorrection_apply]

/-- **The canonical metric section instance of the DeTurck reaction assembly identity.**  Specialises
`metricSection_deTurckDerivation_eq_intrinsicDeTurckCorrectionSection` to the canonical
`ContinuousSectionSpace` element `⟨(g t).toSection, (g t).continuous_toSection⟩` built directly from the
time-`t` metric slice: the frozen-`∇W` two-sided derivation of the metric section reproduces the
geometric `intrinsicDeTurckCorrectionSection` pointwise, with no auxiliary agreement hypothesis (it is
discharged by `ContMDiffRiemannianMetric.toSection_apply`).  This is the exact section a Ricci–DeTurck
chart's metric state is packaged as, so it is the directly-consumable form of the DeTurck-reaction
half of the chart operator `A`'s `geometric` field. -/
theorem metricToSection_deTurckDerivation_eq_intrinsicDeTurckCorrectionSection
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (x : M) (u v : TM x) :
    (⟨(g t).toSection, (g t).continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ)
          (V := _root_.Bundle.BilinearFormBundle (V := TM)) et Kc hKc Ko hKo hKoEq hcover) x
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x u) v
      + (⟨(g t).toSection, (g t).continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ)
          (V := _root_.Bundle.BilinearFormBundle (V := TM)) et Kc hKc Ko hKo hKoEq hcover) x u
        ((chosenLeviCivitaFamily (I := I) (M := M) g t)
          (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x v)
      = intrinsicDeTurckCorrectionSection (I := I) (M := M) g background t x u v :=
  metricSection_deTurckDerivation_eq_intrinsicDeTurckCorrectionSection
    et Kc hKc Ko hKo hKoEq hcover g background t
    ⟨(g t).toSection, (g t).continuous_toSection⟩
    (fun x u v => by
      simp only [ContMDiffRiemannianMetric.toSection_apply]) x u v

/-- **The full geometric Ricci–DeTurck right-hand side splits as the Ricci-flow principal part plus the
frozen-coefficient DeTurck reaction of the metric section.**  For any `ContinuousSectionSpace` element
`sMetric` agreeing pointwise with the metric `(g t).inner`, the geometric `intrinsicRicciDeTurckRHS`
equals, at every base point and tangent pair, the intrinsic Ricci-flow right-hand side plus the
two-sided derivation `sMetric x (∇W x u) v + sMetric x u (∇W x v)`.

This is the exact fiber-value form of the affine chart operator `A τ s = principalSource + reaction s`
evaluated at the metric section: composing the second-order Ricci-flow principal part
(`intrinsicRicciFlowRHS`) with the already-identified zeroth-order DeTurck reaction
(`metricSection_deTurckDerivation_eq_intrinsicDeTurckCorrectionSection`) reproduces the full geometric
Ricci–DeTurck operator.  It is the center-point verification of the chart's `geometric` field: an `A`
whose reaction half is the frozen two-sided derivation and whose source half has fiber value
`intrinsicRicciFlowRHS` agrees with `intrinsicRicciDeTurckRHS` on the metric state. -/
theorem intrinsicRicciDeTurckRHS_eq_intrinsicRicciFlowRHS_add_metricSection_deTurckDerivation
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (sMetric : ContinuousSectionSpace (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ)
      (V := _root_.Bundle.BilinearFormBundle (V := TM)) et Kc hKc Ko hKo hKoEq hcover)
    (hsMetric : ∀ (x : M) (u v : TM x), sMetric x u v = (g t).inner x u v)
    (x : M) (u v : TM x) :
    intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v
      = intrinsicRicciFlowRHS (I := I) (M := M) g t x u v
        + (sMetric x
            ((chosenLeviCivitaFamily (I := I) (M := M) g t)
              (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x u) v
          + sMetric x u
            ((chosenLeviCivitaFamily (I := I) (M := M) g t)
              (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x v)) := by
  rw [intrinsicRicciDeTurckRHS_apply,
    metricSection_deTurckDerivation_eq_intrinsicDeTurckCorrectionSection
      et Kc hKc Ko hKo hKoEq hcover g background t sMetric hsMetric x u v,
    intrinsicDeTurckCorrectionSection_apply]

/-- **The named section-space Ricci–DeTurck RHS value splits as the Ricci-flow principal part plus the
frozen-coefficient DeTurck reaction of the metric section.**  The section-space companion of
`intrinsicRicciDeTurckRHS_eq_intrinsicRicciFlowRHS_add_metricSection_deTurckDerivation`: the named
`intrinsicRicciDeTurckRHSSectionSpace` value (the geometric operator `A`'s / source `b`'s directly
referenceable right-hand side) agrees, on any metric section, with the Ricci-flow principal part plus
the two-sided DeTurck derivation.  This is the directly-consumable form of the chart's `geometric`
field at the metric state: the named RHS source decomposes into the principal part and the reaction the
affine section-space Picard route applies. -/
theorem intrinsicRicciDeTurckRHSSectionSpace_eq_intrinsicRicciFlowRHS_add_metricSection_deTurckDerivation
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (sMetric : ContinuousSectionSpace (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ)
      (V := _root_.Bundle.BilinearFormBundle (V := TM)) et Kc hKc Ko hKo hKoEq hcover)
    (hsMetric : ∀ (x : M) (u v : TM x), sMetric x u v = (g t).inner x u v)
    (x : M) (u v : TM x) :
    intrinsicRicciDeTurckRHSSectionSpace et Kc hKc Ko hKo hKoEq hcover g background t hbackground x u v
      = intrinsicRicciFlowRHS (I := I) (M := M) g t x u v
        + (sMetric x
            ((chosenLeviCivitaFamily (I := I) (M := M) g t)
              (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x u) v
          + sMetric x u
            ((chosenLeviCivitaFamily (I := I) (M := M) g t)
              (intrinsicDeTurckVectorField (I := I) (M := M) g background t) x v)) := by
  rw [intrinsicRicciDeTurckRHSSectionSpace_apply]
  exact intrinsicRicciDeTurckRHS_eq_intrinsicRicciFlowRHS_add_metricSection_deTurckDerivation
    et Kc hKc Ko hKo hKoEq hcover g background t sMetric hsMetric x u v


/-- **The tangent-bundle DeTurck reaction operator, evaluated at the metric section with the frozen
DeTurck coefficient `∇W`, is the geometric DeTurck correction.**  Feeding the frozen coefficient
`P := ∇W = (chosenLeviCivitaFamily g t) (intrinsicDeTurckVectorField g background t)` (continuous by
`intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero`) and the metric section
`⟨(g t).toSection, (g t).continuous_toSection⟩` to the fiber-norm-free tangent-bundle reaction operator
`deTurckReactionSectionMap` reproduces, at every base point and tangent pair, the geometric intrinsic
`intrinsicDeTurckCorrection`.  The operator's symmetrized fiber value `s(∇W u, v) + s(∇W v, u)` matches
the DeTurck correction `s(∇W u, v) + s(u, ∇W v)` on the *symmetric* metric section via metric symmetry
(`ContMDiffRiemannianMetric.symm`).  This identifies the concrete tangent-bundle chart reaction operator
with the DeTurck half of the Ricci–DeTurck chart operator `A`'s `geometric` field on the metric
state. -/
theorem deTurckReactionSectionMap_metricSection_apply_eq_intrinsicDeTurckCorrection
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (x : M) (u v : TM x) :
    deTurckReactionSectionMap (I := I) (M := M) et Kc hKc Ko hKo hKoEq hcover
        (intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
          (I := I) (M := M) g background t hbackground).continuous
        ⟨(g t).toSection, (g t).continuous_toSection⟩ x u v
      = intrinsicDeTurckCorrection (I := I) (M := M) g background t x u v := by
  rw [deTurckReactionSectionMap_apply]
  have h := metricToSection_deTurckDerivation_eq_intrinsicDeTurckCorrectionSection
    et Kc hKc Ko hKo hKoEq hcover g background t x u v
  rw [intrinsicDeTurckCorrectionSection_apply] at h
  rw [← h]
  congr 1
  simp only [ContMDiffRiemannianMetric.toSection_apply]
  exact (g t).symm x _ u


/-- **The affine tangent-bundle chart operator (Ricci source + DeTurck reaction), evaluated at the
metric section, is the full geometric Ricci–DeTurck right-hand side.**  Summing the named second-order
Ricci-flow principal source `intrinsicRicciFlowRHSSectionSpace g t` (whose fiber value is
`intrinsicRicciFlowRHS`) with the fiber-norm-free tangent-bundle DeTurck reaction operator
`deTurckReactionSectionMap` at the frozen coefficient `∇W`, evaluated on the metric section, reproduces
at every base point and tangent pair the full geometric `intrinsicRicciDeTurckRHS`.  This is the
center-point verification of the Ricci–DeTurck chart operator `A`'s `geometric` field, entirely in
terms of the concrete tangent-bundle section-space operator and the named Ricci source: on the metric
state, `A = (principal Ricci source) + (DeTurck reaction)` coincides with the geometric operator. -/
theorem deTurckReactionSectionMap_metricSection_add_ricciFlowRHSSection_apply_eq_intrinsicRicciDeTurckRHS
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (x : M) (u v : TM x) :
    intrinsicRicciFlowRHSSectionSpace et Kc hKc Ko hKo hKoEq hcover g t x u v
      + deTurckReactionSectionMap (I := I) (M := M) et Kc hKc Ko hKo hKoEq hcover
          (intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
            (I := I) (M := M) g background t hbackground).continuous
          ⟨(g t).toSection, (g t).continuous_toSection⟩ x u v
      = intrinsicRicciDeTurckRHS (I := I) (M := M) g background t x u v := by
  rw [deTurckReactionSectionMap_metricSection_apply_eq_intrinsicDeTurckCorrection
      et Kc hKc Ko hKo hKoEq hcover g background t hbackground x u v,
    intrinsicRicciFlowRHSSectionSpace_apply, intrinsicRicciDeTurckRHS_apply]

/-- **On a Levi–Civita background the tangent-bundle DeTurck reaction operator annihilates the metric
section.**  When the fixed background connection is the Levi–Civita connection of the evolving metric
`g` (`IsLeviCivita g background`), the intrinsic DeTurck vector field vanishes, so the geometric DeTurck
correction is zero (`intrinsicDeTurckCorrection_eq_zero_of_isLeviCivita`); combined with the center-point
identification `deTurckReactionSectionMap_metricSection_apply_eq_intrinsicDeTurckCorrection`, the concrete
fiber-norm-free tangent-bundle reaction operator `deTurckReactionSectionMap` at the frozen coefficient
`∇W` contributes nothing on the metric state.  This is the operator-level Levi–Civita (self-DeTurck)
reduction: in the metric's own Levi–Civita gauge the reaction half of the chart operator `A` drops out. -/
theorem deTurckReactionSectionMap_metricSection_apply_eq_zero_of_isLeviCivita
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (hLeviCivita : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background)
    (x : M) (u v : TM x) :
    deTurckReactionSectionMap (I := I) (M := M) et Kc hKc Ko hKo hKoEq hcover
        (intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
          (I := I) (M := M) g background t hbackground).continuous
        ⟨(g t).toSection, (g t).continuous_toSection⟩ x u v
      = 0 := by
  rw [deTurckReactionSectionMap_metricSection_apply_eq_intrinsicDeTurckCorrection
      et Kc hKc Ko hKo hKoEq hcover g background t hbackground x u v]
  simpa using congrArg (fun F => F t x u v)
    (intrinsicDeTurckCorrection_eq_zero_of_isLeviCivita (I := I) (M := M) g background hLeviCivita)

/-- **On a Levi–Civita background the affine tangent-bundle chart operator, evaluated at the metric
section, is the pure intrinsic Ricci-flow right-hand side.**  Summing the second-order Ricci-flow
principal source `intrinsicRicciFlowRHSSectionSpace g t` with the tangent-bundle DeTurck reaction
`deTurckReactionSectionMap` at the frozen coefficient `∇W`, evaluated on the metric state, reproduces
`intrinsicRicciDeTurckRHS g background`
(`deTurckReactionSectionMap_metricSection_add_ricciFlowRHSSection_apply_eq_intrinsicRicciDeTurckRHS`),
which on a Levi–Civita background collapses to `intrinsicRicciFlowRHS g`
(`intrinsicRicciDeTurckRHS_eq_intrinsicRicciFlowRHS_of_isLeviCivita`) — the flowing metric's DeTurck term
vanishes in its own Levi–Civita gauge.  This is the concrete operator-level form of the chart-closure
`chartRHS_eq_intrinsic` reduction: in the chosen Levi–Civita gauge the chart operator `A` on the metric
state is exactly the geometric Ricci-flow right-hand side. -/
theorem deTurckReactionSectionMap_metricSection_add_ricciFlowRHSSection_apply_eq_intrinsicRicciFlowRHS_of_isLeviCivita
    {κ : Type*} [Finite κ]
    (et : κ → Trivialization (E →L[ℝ] E →L[ℝ] ℝ)
      (TotalSpace.proj :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M)) (t : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (hLeviCivita : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g background)
    (x : M) (u v : TM x) :
    intrinsicRicciFlowRHSSectionSpace et Kc hKc Ko hKo hKoEq hcover g t x u v
      + deTurckReactionSectionMap (I := I) (M := M) et Kc hKc Ko hKo hKoEq hcover
          (intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
            (I := I) (M := M) g background t hbackground).continuous
          ⟨(g t).toSection, (g t).continuous_toSection⟩ x u v
      = intrinsicRicciFlowRHS (I := I) (M := M) g t x u v := by
  rw [deTurckReactionSectionMap_metricSection_add_ricciFlowRHSSection_apply_eq_intrinsicRicciDeTurckRHS
      et Kc hKc Ko hKo hKoEq hcover g background t hbackground x u v]
  exact congrArg (fun F => F t x u v)
    (intrinsicRicciDeTurckRHS_eq_intrinsicRicciFlowRHS_of_isLeviCivita
      (I := I) (M := M) g background hLeviCivita)

end RicciFlow
