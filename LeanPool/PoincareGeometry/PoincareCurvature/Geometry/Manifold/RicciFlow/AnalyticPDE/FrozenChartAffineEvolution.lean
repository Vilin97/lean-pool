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

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.GeometricReactionPicardTangent
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.AutonomousResolventExp
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SectionPointwiseDeriv

/-!
# The frozen (affine) Ricci–DeTurck chart operator's explicit global evolution

The **frozen** geometric Ricci–DeTurck chart operator is *affine*: with the DeTurck coefficient
`P := ∇W` frozen at the initial data and the principal Ricci source `b` frozen as a fixed
`ContinuousSectionSpace` value, it acts as

`A τ s = deTurckReactionSectionMap P s + b = L s + b`,

where `L := deTurckReactionSectionMapL … hP : CSS →L[ℝ] CSS` is the bounded-linear reaction
generator (`GeometricReactionPicardTangent`).  Since the continuous section space `CSS` is a
**complete** normed `ℝ`-space, the abstract affine autonomous ODE machinery
(`AutonomousResolventExp`: `affineFundamentalSolution` via the augmentation trick, its
`HasDerivAt`, initial value, and uniqueness) applies verbatim.

This module performs the **Duhamel assembly** the plan named as NEXT: it imports both frontier
files and specialises the abstract affine resolvent to `L` and a general frozen source `b`, giving
the concrete frozen chart operator a genuine, *explicit and global* solution
`deTurckFrozenAffineEvolution`.  We prove it starts at `σ₀`, solves the exact frozen ODE
`σ' = deTurckReactionSectionMap P σ + b`, and is the **unique** such global solution — the
existence-and-uniqueness core the chart-closure `realization`/`encode` fields consume for the
frozen (autonomous) chart.  A geometric corollary specialises `P`/`b` to the genuine geometric
data `∇W` / `intrinsicRicciFlowRHSSectionSpace g t`, matching the operator solved by
`deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn`.

No parabolic Schauder content is used: the frozen operator is bounded-linear, so its evolution is
the operator exponential of the augmented generator.
-/

noncomputable section
open Bundle RicciFlow
open scoped Manifold ContDiff Topology NNReal
open PoincareCurvature.Bundle.Trivialization
open RicciFlow.AnalyticPDE.SmoothDependenceCk

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

/-- **The frozen (affine) Ricci–DeTurck chart operator's explicit global evolution.**  With the
bounded-linear reaction generator `L := deTurckReactionSectionMapL … hP` and a fixed source
`b : CSS`, this is the affine autonomous fundamental solution `t ↦ affineFundamentalSolution L b t₀ σ₀`
on the complete section space `CSS`.  It is the global-in-time explicit solution of the frozen chart
ODE `σ' = L σ + b`, `σ t₀ = σ₀`. -/
noncomputable def deTurckFrozenAffineEvolution
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
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover :=
  affineFundamentalSolution
    (deTurckReactionSectionMapL x0 Kc hKc Ko hKo hKoEq hcover hP) b t₀ σ0

/-- The frozen affine evolution starts at the initial section `σ₀`. -/
theorem deTurckFrozenAffineEvolution_initial
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
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    deTurckFrozenAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover hP b t₀ σ0 t₀ = σ0 :=
  affineFundamentalSolution_initial
    (deTurckReactionSectionMapL x0 Kc hKc Ko hKo hKoEq hcover hP) b t₀ σ0

/-- **The frozen affine evolution solves the frozen chart ODE
`σ' = deTurckReactionSectionMap P σ + b`.**  Immediate from the abstract affine ODE solution
(`hasDerivAt_affineFundamentalSolution`) once the bounded-linear generator's value is decoded to the
raw reaction self-map (`deTurckReactionSectionMapL_apply`). -/
theorem hasDerivAt_deTurckFrozenAffineEvolution
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
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (t : ℝ) :
    HasDerivAt (deTurckFrozenAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover hP b t₀ σ0)
      (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover hP
          (deTurckFrozenAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover hP b t₀ σ0 t)
        + b) t := by
  have h := hasDerivAt_affineFundamentalSolution
    (deTurckReactionSectionMapL x0 Kc hKc Ko hKo hKoEq hcover hP) b t₀ σ0 t
  rwa [deTurckReactionSectionMapL_apply] at h

/-- **Uniqueness for the frozen chart ODE.**  Any global solution `σ` of
`σ' = deTurckReactionSectionMap P σ + b` with `σ t₀ = σ₀` coincides with the explicit affine
evolution.  The uniqueness half of the frozen chart's Cauchy problem, consumed by the `encode`
field. -/
theorem deTurckFrozenAffineEvolution_unique
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
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    {y : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover}
    (hy : ∀ t, HasDerivAt y
      (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP (y t) + b) t)
    (h0 : y t₀ = σ0) (t : ℝ) :
    y t = deTurckFrozenAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover hP b t₀ σ0 t := by
  refine eq_affineFundamentalSolution_of_hasDerivAt
    (deTurckReactionSectionMapL x0 Kc hKc Ko hKo hKoEq hcover hP) b t₀ σ0 ?_ h0 t
  intro s
  rw [deTurckReactionSectionMapL_apply]
  exact hy s

/-- **The concrete geometric frozen Ricci–DeTurck chart operator's explicit global evolution.**
Specialising `deTurckFrozenAffineEvolution` to the genuine geometric data: the DeTurck coefficient
`P := ∇W = (chosenLeviCivitaFamily g tFreeze) (intrinsicDeTurckVectorField g background tFreeze)`
(continuous via `intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero`, needing only a `C¹`
background slice) and the principal Ricci source `b := intrinsicRicciFlowRHSSectionSpace … g tFreeze`.
This is the explicit global-in-time solution of the exact frozen geometric operator solved by
`deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn`. -/
noncomputable def deTurckFrozenGeometricAffineEvolution
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M))
    (tFreeze : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background tFreeze) 1)
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover :=
  deTurckFrozenAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover
    (intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
      g background tFreeze hbackground).continuous
    (intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (x0 i))
      Kc hKc Ko hKo hKoEq hcover g tFreeze)
    t₀ σ0

/-- The concrete geometric frozen evolution starts at the initial section `σ₀`. -/
theorem deTurckFrozenGeometricAffineEvolution_initial
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M))
    (tFreeze : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background tFreeze) 1)
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    deTurckFrozenGeometricAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover
      g background tFreeze hbackground t₀ σ0 t₀ = σ0 :=
  deTurckFrozenAffineEvolution_initial x0 Kc hKc Ko hKo hKoEq hcover _ _ t₀ σ0

/-- **The concrete geometric frozen evolution solves the exact frozen Ricci–DeTurck chart ODE.**
`σ' = deTurckReactionSectionMap ∇W σ + intrinsicRicciFlowRHSSectionSpace g tFreeze` — the operator
form fed to `deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn`.  Its explicit global
solution is the affine operator-exponential evolution. -/
theorem hasDerivAt_deTurckFrozenGeometricAffineEvolution
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M))
    (tFreeze : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background tFreeze) 1)
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (t : ℝ) :
    HasDerivAt
      (deTurckFrozenGeometricAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover
        g background tFreeze hbackground t₀ σ0)
      (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover
          (intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
            g background tFreeze hbackground).continuous
          (deTurckFrozenGeometricAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover
            g background tFreeze hbackground t₀ σ0 t)
        + intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (x0 i))
            Kc hKc Ko hKo hKoEq hcover g tFreeze) t :=
  hasDerivAt_deTurckFrozenAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover _ _ t₀ σ0 t

/-- **Uniqueness for the concrete geometric frozen chart ODE.**  Any global solution of the exact
frozen Ricci–DeTurck operator with value `σ₀` at `t₀` coincides with the explicit affine evolution. -/
theorem deTurckFrozenGeometricAffineEvolution_unique
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M))
    (tFreeze : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background tFreeze) 1)
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    {y : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover}
    (hy : ∀ t, HasDerivAt y
      (deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover
          (intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
            g background tFreeze hbackground).continuous (y t)
        + intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (x0 i))
            Kc hKc Ko hKo hKoEq hcover g tFreeze) t)
    (h0 : y t₀ = σ0) (t : ℝ) :
    y t = deTurckFrozenGeometricAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover
      g background tFreeze hbackground t₀ σ0 t :=
  deTurckFrozenAffineEvolution_unique x0 Kc hKc Ko hKo hKoEq hcover _ _ t₀ σ0 hy h0 t

section AbstractAffineSmooth

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- **The affine autonomous fundamental solution is smooth in time.**  `t ↦ affineFundamentalSolution
L b t₀ y₀ t` is `ContDiff ℝ n` for every `n`: it is the first coordinate of the operator-exponential
orbit `t ↦ exp ((t - t₀) • affineAugment L b) (y₀, 1)`, and `NormedSpace.exp` is analytic on the
(complete) augmented operator algebra, composed with the smooth affine scalar rescaling in `t`, the
continuous-linear evaluation at `(y₀, 1)`, and the coordinate projection.  This is the parabolic-free
time-regularity of the frozen (bounded-linear) chart evolution. -/
theorem contDiff_affineFundamentalSolution (L : G →L[ℝ] G) (b : G) (t₀ : ℝ) (y₀ : G)
    {n : WithTop ℕ∞} :
    ContDiff ℝ n (affineFundamentalSolution L b t₀ y₀) := by
  have hana : AnalyticOnNhd ℝ
      (NormedSpace.exp : ((G × ℝ) →L[ℝ] (G × ℝ)) → ((G × ℝ) →L[ℝ] (G × ℝ))) Set.univ :=
    fun x _ => NormedSpace.exp_analytic x
  have hsmul : ContDiff ℝ n (fun t : ℝ => (t - t₀) • affineAugment L b) :=
    (contDiff_id.sub contDiff_const).smul contDiff_const
  have hexp : ContDiff ℝ n (fun t : ℝ => NormedSpace.exp ((t - t₀) • affineAugment L b)) :=
    hana.contDiff.comp hsmul
  have happly : ContDiff ℝ n
      (fun t : ℝ => NormedSpace.exp ((t - t₀) • affineAugment L b) (y₀, 1)) :=
    hexp.clm_apply contDiff_const
  exact contDiff_fst.comp happly

/-- **Abstract within-interval uniqueness of Banach evolution solutions for an affine autonomous
field.**  Any `BanachEvolutionLocalSolution` of `F t = fun y ↦ L y + b` (bounded-linear generator `L`
plus a constant source `b`) has its curve equal to the explicit affine fundamental solution on its
interval.  The field is globally `‖L‖`-Lipschitz (translation by the constant `b` is an
`edist`-isometry, so only `L`'s bounded-linear Lipschitz bound remains), and both the given solution
and the explicit `affineFundamentalSolution` solve the same ODE from the same initial value, so
Grönwall uniqueness (`ODE_solution_unique`) forces them to agree.  This is the reusable Banach-level
uniqueness core that the frozen Ricci–DeTurck chart's `encode`/`realization` fields consume once the
section-space affine generator is supplied. -/
theorem banachEvolutionLocalSolution_curve_eq_affineFundamentalSolution
    (L : G →L[ℝ] G) (b : G) (t₀ : ℝ) (y₀ : G)
    (sol : RicciFlow.AnalyticPDE.BanachEvolutionLocalSolution
      (fun _ : ℝ => fun y => L y + b) t₀ y₀)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ sol.terminalTime) :
    sol.curve t = affineFundamentalSolution L b t₀ y₀ t := by
  have hF : ∀ τ : ℝ, LipschitzWith ‖L‖₊ ((fun _ : ℝ => fun y => L y + b) τ) := by
    intro _ x y
    simp only [edist_add_right]
    exact L.lipschitz x y
  exact ODE_solution_unique
    (v := fun _ : ℝ => fun y => L y + b) (K := ‖L‖₊) (a := t₀) (b := sol.terminalTime) hF
    (sol.continuousOn_Icc_of_le_terminal le_rfl)
    (fun τ hτ => sol.equation_hasDerivWithinAt_Ici_of_mem_Ico hτ)
    (contDiff_affineFundamentalSolution L b t₀ y₀ (n := 1)).continuous.continuousOn
    (fun τ _ => (hasDerivAt_affineFundamentalSolution L b t₀ y₀ τ).hasDerivWithinAt)
    (by rw [sol.initial_eq, affineFundamentalSolution_initial]) ht

end AbstractAffineSmooth

/-- The frozen affine chart evolution is `ContDiff ℝ n` in time. -/
theorem contDiff_deTurckFrozenAffineEvolution
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
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    {n : WithTop ℕ∞} :
    ContDiff ℝ n (deTurckFrozenAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover hP b t₀ σ0) :=
  contDiff_affineFundamentalSolution
    (deTurckReactionSectionMapL x0 Kc hKc Ko hKo hKoEq hcover hP) b t₀ σ0

/-- The concrete geometric frozen chart evolution is `ContDiff ℝ n` in time — the explicit,
parabolic-free time-regularity fed to the smooth realization. -/
theorem contDiff_deTurckFrozenGeometricAffineEvolution
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M))
    (tFreeze : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background tFreeze) 1)
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    {n : WithTop ℕ∞} :
    ContDiff ℝ n (deTurckFrozenGeometricAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover
      g background tFreeze hbackground t₀ σ0) :=
  contDiff_deTurckFrozenAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover _ _ t₀ σ0

/-- **CSS-concrete within-interval uniqueness of the frozen affine chart operator's Banach evolution
— WALL-FREE.**  Any `BanachEvolutionLocalSolution` of the concrete section-space frozen chart field
`F τ s = deTurckReactionSectionMap ∇W s + b` has its curve equal to the explicit affine evolution
`deTurckFrozenAffineEvolution` on the whole solution interval `Icc t₀ sol.terminalTime`.

This is the CSS specialisation of `banachEvolutionLocalSolution_curve_eq_affineFundamentalSolution`
that earlier sessions could not close: routing the field's Lipschitz bound through
`L.lipschitz` (the operator-norm route) forced a `whnf`/`edist` normalisation of the
`BilinearFormBundle` section fibre and walled at 2 000 000 heartbeats.  Here the *identical*
Grönwall-uniqueness argument (`ODE_solution_unique`) is fed the **coordinate-route** Lipschitz bound
`deTurckReactionSectionMap_add_source_lipschitzWith_of_uniform_inCoordinates` — a genuine global
`LipschitzWith ⟨2·Kp, _⟩` for `s ↦ deTurckReactionSectionMap ∇W s + b` obtained from the finite-cover
coordinate distance handoff (`lipschitzWith_of_forall_coord_dist_le`), whose uniform bound `Kp` on the
coefficient's model-fibre readout comes free from compactness of the finite cover + continuity of `P`
(`exists_uniform_inCoord_bound`).  This route never evaluates the CSS `edist`, so the wall does not
arise, and the explicit evolution's own `HasDerivAt`/`ContDiff`/initial-value data
(`hasDerivAt_deTurckFrozenAffineEvolution`, `contDiff_deTurckFrozenAffineEvolution`,
`deTurckFrozenAffineEvolution_initial`) close the uniqueness.  This is the CSS-concrete
`encode`/`realization` uniqueness datum the abstract Banach-level core previously delivered only over a
generic Banach space. -/
theorem banachEvolution_curve_eq_deTurckFrozenAffineEvolution
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
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (sol : RicciFlow.AnalyticPDE.BanachEvolutionLocalSolution
      (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP s + b) t₀ σ0)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ sol.terminalTime) :
    sol.curve t = deTurckFrozenAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover hP b t₀ σ0 t := by
  have hKcTM : ∀ i, (Kc i : Set M) ⊆ (trivializationAt (E →L[ℝ] E) THom (x0 i)).baseSet := by
    intro i x hx
    have hxi := hKc i hx
    simpa using hxi
  obtain ⟨Kp, hKp0, hKpb⟩ := exists_uniform_inCoord_bound x0 Kc hKcTM hP
  have hF : ∀ τ : ℝ, LipschitzWith ⟨2 * Kp, mul_nonneg (by norm_num) hKp0⟩
      ((fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP s + b) τ) :=
    fun _ => deTurckReactionSectionMap_add_source_lipschitzWith_of_uniform_inCoordinates
      x0 Kc hKc Ko hKo hKoEq hcover hP Kp hKp0 hKpb b
  exact ODE_solution_unique
    (v := fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
      Kc hKc Ko hKo hKoEq hcover hP s + b)
    (K := ⟨2 * Kp, mul_nonneg (by norm_num) hKp0⟩) (a := t₀) (b := sol.terminalTime) hF
    (sol.continuousOn_Icc_of_le_terminal le_rfl)
    (fun τ hτ => sol.equation_hasDerivWithinAt_Ici_of_mem_Ico hτ)
    (contDiff_deTurckFrozenAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover hP b t₀ σ0
      (n := 1)).continuous.continuousOn
    (fun τ _ => (hasDerivAt_deTurckFrozenAffineEvolution
      x0 Kc hKc Ko hKo hKoEq hcover hP b t₀ σ0 τ).hasDerivWithinAt)
    (by rw [sol.initial_eq, deTurckFrozenAffineEvolution_initial]) ht

/-- **State-constrained (`BanachEvolutionLocalSolutionIn`) CSS-concrete uniqueness for the frozen
affine chart operator — WALL-FREE.**  The `locus`-constrained specialisation of
`banachEvolution_curve_eq_deTurckFrozenAffineEvolution`: any state-preserving Banach evolution
`sol : BanachEvolutionLocalSolutionIn (fun _ ↦ fun s ↦ deTurckReactionSectionMap ∇W s + b) locus t₀ σ₀`
has its curve equal to the explicit affine evolution on its interval.  Immediate by forgetting the
state-set data (`sol.toBanachEvolutionLocalSolution`), whose field, curve and terminal time coincide
with `sol`'s.  This is exactly the uniqueness shape the chart-closure `encode`/`realization` fields
consume, since they carry `BanachEvolutionLocalSolutionIn chart.A (positiveDefiniteLocus …)`. -/
theorem banachEvolutionIn_curve_eq_deTurckFrozenAffineEvolution
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
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (locus : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover))
    (sol : RicciFlow.AnalyticPDE.BanachEvolutionLocalSolutionIn
      (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP s + b) locus t₀ σ0)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ sol.terminalTime) :
    sol.curve t = deTurckFrozenAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover hP b t₀ σ0 t :=
  banachEvolution_curve_eq_deTurckFrozenAffineEvolution
    x0 Kc hKc Ko hKo hKoEq hcover hP b t₀ σ0 sol.toBanachEvolutionLocalSolution ht

/-- **CSS-concrete uniqueness for the CONCRETE geometric frozen Ricci–DeTurck chart operator —
WALL-FREE.**  The geometric specialisation of `banachEvolution_curve_eq_deTurckFrozenAffineEvolution`
at the genuine data `P := ∇W` and `b := intrinsicRicciFlowRHSSectionSpace g tFreeze`: any Banach
evolution of the exact frozen geometric field
`F τ s = deTurckReactionSectionMap ∇W s + intrinsicRicciFlowRHSSectionSpace g tFreeze`
(the operator solved by `deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn`) equals the
explicit geometric affine evolution `deTurckFrozenGeometricAffineEvolution` on its interval.  The
identity `deTurckFrozenGeometricAffineEvolution = deTurckFrozenAffineEvolution` at the geometric
`∇W`/Ricci-source data holds by definition, so the general wall-free uniqueness applies verbatim. -/
theorem banachEvolution_curve_eq_deTurckFrozenGeometricAffineEvolution
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M))
    (tFreeze : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background tFreeze) 1)
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (sol : RicciFlow.AnalyticPDE.BanachEvolutionLocalSolution
      (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover
          (intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
            g background tFreeze hbackground).continuous s
        + intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (x0 i))
            Kc hKc Ko hKo hKoEq hcover g tFreeze) t₀ σ0)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ sol.terminalTime) :
    sol.curve t = deTurckFrozenGeometricAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover
      g background tFreeze hbackground t₀ σ0 t :=
  banachEvolution_curve_eq_deTurckFrozenAffineEvolution
    x0 Kc hKc Ko hKo hKoEq hcover _ _ t₀ σ0 sol ht

/-- **Any frozen affine chart Banach solution has a `ContDiffOn` (smooth-in-time) curve — WALL-FREE.**
Combining the wall-free uniqueness `banachEvolution_curve_eq_deTurckFrozenAffineEvolution` (the curve
equals the explicit affine evolution on its interval) with the explicit evolution's global time
smoothness `contDiff_deTurckFrozenAffineEvolution` (via `ContDiffOn.congr`): the curve of *any* Banach
evolution of the frozen field `F τ s = deTurckReactionSectionMap ∇W s + b` is `ContDiffOn ℝ n` on
`Icc t₀ sol.terminalTime`.  This is the parabolic-free time-regularity of the Banach curve that the
smooth realization consumes at the interval endpoints. -/
theorem banachEvolution_curve_contDiffOn_of_frozen
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
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (sol : RicciFlow.AnalyticPDE.BanachEvolutionLocalSolution
      (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP s + b) t₀ σ0)
    {n : WithTop ℕ∞} :
    ContDiffOn ℝ n sol.curve (Set.Icc t₀ sol.terminalTime) :=
  (contDiff_deTurckFrozenAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover hP b t₀ σ0
    (n := n)).contDiffOn.congr
    (fun t ht => banachEvolution_curve_eq_deTurckFrozenAffineEvolution
      x0 Kc hKc Ko hKo hKoEq hcover hP b t₀ σ0 sol ht)

/-- **Any CONCRETE geometric frozen Ricci–DeTurck Banach solution has a `ContDiffOn` curve —
WALL-FREE.**  The geometric specialisation of `banachEvolution_curve_contDiffOn_of_frozen` at the
genuine data `P := ∇W`, `b := intrinsicRicciFlowRHSSectionSpace g tFreeze`: the curve of any Banach
evolution of the exact frozen geometric field (the operator solved by
`deTurckFrozenGeometric_nonempty_banachEvolutionLocalSolutionIn`) is `ContDiffOn ℝ n` in time on its
interval — the smooth-in-time realization ingredient for the concrete Ricci–DeTurck chart. -/
theorem banachEvolution_curve_contDiffOn_of_frozenGeometric
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M))
    (tFreeze : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background tFreeze) 1)
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (sol : RicciFlow.AnalyticPDE.BanachEvolutionLocalSolution
      (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover
          (intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
            g background tFreeze hbackground).continuous s
        + intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (x0 i))
            Kc hKc Ko hKo hKoEq hcover g tFreeze) t₀ σ0)
    {n : WithTop ℕ∞} :
    ContDiffOn ℝ n sol.curve (Set.Icc t₀ sol.terminalTime) :=
  banachEvolution_curve_contDiffOn_of_frozen
    x0 Kc hKc Ko hKo hKoEq hcover _ _ t₀ σ0 sol

/-- **Scalar pointwise section-curve derivative of the concrete geometric frozen chart evolution
(everywhere, including interval endpoints).**  Pushing the globally-smooth `CSS`-level frozen ODE
`hasDerivAt_deTurckFrozenGeometricAffineEvolution` through the scalar evaluation `sectionScalarEvalCLM`
gives, for every `t` and fibre point `(x, u, v)`, the scalar derivative of
`τ ↦ (frozen evolution) τ x u v`.  Unlike the interior `hasDerivAt_scalarEval_banachEvolution_of_mem_Ioo`
form (valid only on the open interval), this holds at the endpoints too — the explicit affine
evolution is globally `HasDerivAt` — so it supplies the endpoint scalar `HasDerivAt` data that the
smooth-realization `boundary_hasTimeDerivative`/`initial`/`terminal` obligations demand for the frozen
chart. -/
theorem hasDerivAt_scalarEval_deTurckFrozenGeometricAffineEvolution
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M))
    (tFreeze : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background tFreeze) 1)
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (t : ℝ) (x : M) (u v : TangentSpace I x) :
    HasDerivAt
      (fun τ : ℝ ↦ deTurckFrozenGeometricAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover
        g background tFreeze hbackground t₀ σ0 τ x u v)
      ((deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
            Kc hKc Ko hKo hKoEq hcover
            (intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
              g background tFreeze hbackground).continuous
            (deTurckFrozenGeometricAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover
              g background tFreeze hbackground t₀ σ0 t)
          + intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (x0 i))
              Kc hKc Ko hKo hKoEq hcover g tFreeze) x u v) t :=
  hasDerivAt_scalarEval_of_hasDerivAt x0 Kc hKc Ko hKo hKoEq hcover
    (hasDerivAt_deTurckFrozenGeometricAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover
      g background tFreeze hbackground t₀ σ0 t) x u v

/-- **Full time-smoothness of the scalar section-curve of a frozen chart Banach solution.**  Pushing
the wall-free time-regularity `banachEvolution_curve_contDiffOn_of_frozen` (the `CSS`-valued curve is
`ContDiffOn ℝ n` on its interval, being the explicit affine evolution) through the diamond-free scalar
evaluation `sectionScalarEvalCLM` (a `CSS →L[ℝ] ℝ`, hence `C^∞`): for every fibre point `(x, u, v)`
the scalar curve `τ ↦ sol.curve τ x u v` is `ContDiffOn ℝ n` on `Icc t₀ sol.terminalTime`.  This is the
all-order strengthening of the first-order interior `hasDerivAt_scalarEval_banachEvolution_of_mem_Ioo`,
and the `C^k`-in-time realization ingredient the smooth realization consumes for the frozen chart. -/
theorem contDiffOn_scalarEval_banachEvolution_of_frozen
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
    (b : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (sol : RicciFlow.AnalyticPDE.BanachEvolutionLocalSolution
      (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
        Kc hKc Ko hKo hKoEq hcover hP s + b) t₀ σ0)
    {n : WithTop ℕ∞}
    (x : M) (u v : TangentSpace I x) :
    ContDiffOn ℝ n (fun τ : ℝ ↦ sol.curve τ x u v) (Set.Icc t₀ sol.terminalTime) := by
  obtain ⟨i, hi⟩ : ∃ i, x ∈ (Kc i : Set M) :=
    Set.mem_iUnion.mp (by rw [hcover]; exact Set.mem_univ x)
  have hcurve : ContDiffOn ℝ n sol.curve (Set.Icc t₀ sol.terminalTime) :=
    banachEvolution_curve_contDiffOn_of_frozen x0 Kc hKc Ko hKo hKoEq hcover hP b t₀ σ0 sol
  exact ((sectionScalarEvalCLM x0 Kc hKc Ko hKo hKoEq hcover i x hi u v).contDiff.comp_contDiffOn
    hcurve).congr (fun τ _ => by
      simp only [Function.comp_apply, sectionScalarEvalCLM_apply])

/-- **Full time-smoothness of the scalar section-curve of the CONCRETE geometric frozen Ricci–DeTurck
Banach solution.**  The geometric specialisation of `contDiffOn_scalarEval_banachEvolution_of_frozen`
at the genuine data `P := ∇W`, `b := intrinsicRicciFlowRHSSectionSpace g tFreeze`: for every fibre
point `(x, u, v)` the scalar curve `τ ↦ sol.curve τ x u v` of any Banach evolution of the exact frozen
geometric field is `ContDiffOn ℝ n` in time on its interval — the `C^k`-in-time realization ingredient
for the concrete Ricci–DeTurck chart. -/
theorem contDiffOn_scalarEval_banachEvolution_of_frozenGeometric
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M))
    (tFreeze : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background tFreeze) 1)
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (sol : RicciFlow.AnalyticPDE.BanachEvolutionLocalSolution
      (fun _ : ℝ => fun s => deTurckReactionSectionMap (fun i => trivializationAt BilF BilW (x0 i))
          Kc hKc Ko hKo hKoEq hcover
          (intrinsicDeTurckVectorField_covariantDerivative_contMDiff_zero
            g background tFreeze hbackground).continuous s
        + intrinsicRicciFlowRHSSectionSpace (fun i => trivializationAt BilF BilW (x0 i))
            Kc hKc Ko hKo hKoEq hcover g tFreeze) t₀ σ0)
    {n : WithTop ℕ∞}
    (x : M) (u v : TangentSpace I x) :
    ContDiffOn ℝ n (fun τ : ℝ ↦ sol.curve τ x u v) (Set.Icc t₀ sol.terminalTime) :=
  contDiffOn_scalarEval_banachEvolution_of_frozen
    x0 Kc hKc Ko hKo hKoEq hcover _ _ t₀ σ0 sol x u v

/-- **Global all-order time-smoothness of the scalar section-curve of the explicit geometric frozen
Ricci–DeTurck affine evolution.**  Pushing the `CSS`-level global smoothness
`contDiff_deTurckFrozenGeometricAffineEvolution` through the diamond-free scalar evaluation
`sectionScalarEvalCLM`: for every fibre point `(x, u, v)` the scalar curve
`τ ↦ (frozen geometric evolution) τ x u v` is `ContDiff ℝ n` on all of `ℝ` (not merely on an
interval — the explicit affine evolution is globally smooth).  This is the all-order companion of the
first-order endpoint datum `hasDerivAt_scalarEval_deTurckFrozenGeometricAffineEvolution`. -/
theorem contDiff_scalarEval_deTurckFrozenGeometricAffineEvolution
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g : MetricFamily (I := I) (M := M)) (background : ConnectionFamily (I := I) (M := M))
    (tFreeze : ℝ)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background tFreeze) 1)
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    {n : WithTop ℕ∞}
    (x : M) (u v : TangentSpace I x) :
    ContDiff ℝ n (fun τ : ℝ ↦ deTurckFrozenGeometricAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover
      g background tFreeze hbackground t₀ σ0 τ x u v) := by
  obtain ⟨i, hi⟩ : ∃ i, x ∈ (Kc i : Set M) :=
    Set.mem_iUnion.mp (by rw [hcover]; exact Set.mem_univ x)
  have hcomp : ContDiff ℝ n
      (fun τ : ℝ ↦ sectionScalarEvalCLM x0 Kc hKc Ko hKo hKoEq hcover i x hi u v
        (deTurckFrozenGeometricAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover
          g background tFreeze hbackground t₀ σ0 τ)) := by
    simpa [Function.comp_def] using
      (sectionScalarEvalCLM x0 Kc hKc Ko hKo hKoEq hcover i x hi u v).contDiff.comp
        (contDiff_deTurckFrozenGeometricAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover
          g background tFreeze hbackground t₀ σ0)
  have e1 : (fun τ : ℝ ↦ deTurckFrozenGeometricAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover
        g background tFreeze hbackground t₀ σ0 τ x u v)
      = fun τ : ℝ ↦ sectionScalarEvalCLM x0 Kc hKc Ko hKo hKoEq hcover i x hi u v
          (deTurckFrozenGeometricAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover
            g background tFreeze hbackground t₀ σ0 τ) := by
    funext τ; rw [sectionScalarEvalCLM_apply]
  rw [e1]
  exact hcomp

/-- **Exponential-in-time whole-section growth bound for the frozen (affine) Ricci–DeTurck chart
evolution.**  `‖deTurckFrozenAffineEvolution … hP b t₀ σ0 t‖ ≤
Real.exp (|t - t₀| · (2·Kp + ‖b‖)) · ‖(σ0, 1)‖`, where `Kp` is any uniform bound on the model-fibre
readout of the frozen reaction coefficient `P` over the finite compact cover.  The explicit evolution
is the affine operator-exponential fundamental solution of `σ' = deTurckReactionSectionMap P σ + b`; its
generator norm is `‖deTurckReactionSectionMapL P‖ ≤ 2·Kp` (`deTurckReactionSectionMapL_opNorm_le`), so
the abstract growth estimate `norm_affineFundamentalSolution_le` — itself the resolvent bound
`‖exp(τ·L)‖ ≤ exp(|τ|·‖L‖)` applied to the augmented generator — specialises to this concrete
at-most-exponential bound for the honest geometric section-space operator.  This is the whole-section
stability control that a mild/Duhamel a-posteriori argument for the real Ricci–DeTurck chart consumes. -/
theorem norm_deTurckFrozenAffineEvolution_le
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
    (t₀ : ℝ)
    (σ0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (t : ℝ) :
    ‖deTurckFrozenAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover hP b t₀ σ0 t‖
      ≤ Real.exp (|t - t₀| * (2 * Kp + ‖b‖)) * ‖(σ0, (1 : ℝ))‖ := by
  have hop := deTurckReactionSectionMapL_opNorm_le x0 Kc hKc Ko hKo hKoEq hcover hP Kp hKp0 hKp
  rw [deTurckFrozenAffineEvolution]
  refine (norm_affineFundamentalSolution_le
    (deTurckReactionSectionMapL x0 Kc hKc Ko hKo hKoEq hcover hP) b t₀ σ0 t).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine Real.exp_le_exp.2 ?_
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  linarith [hop]

/-- **Continuous dependence on initial data for the concrete geometric frozen Ricci–DeTurck chart
evolution.**  `‖deTurckFrozenAffineEvolution … hP b t₀ σ0 t − deTurckFrozenAffineEvolution … hP b t₀
σ0' t‖ ≤ Real.exp (|t - t₀| · (2·Kp + ‖b‖)) · ‖σ0 − σ0'‖`.  Composes the abstract
Lipschitz-in-initial-data bound `norm_affineFundamentalSolution_sub_le` (difference of two affine
orbits is the homogeneous orbit of the difference) with the real operator's generator-norm bound
`deTurckReactionSectionMapL_opNorm_le` (`‖L‖ ≤ 2·Kp`).  Together with
`norm_deTurckFrozenAffineEvolution_le` this is the pair of well-posedness stability estimates —
at-most-exponential growth and Lipschitz dependence on the initial metric — of the honest geometric
section-space operator's evolution. -/
theorem norm_deTurckFrozenAffineEvolution_sub_le
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
    (t₀ : ℝ)
    (σ0 σ0' : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (t : ℝ) :
    ‖deTurckFrozenAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover hP b t₀ σ0 t
        - deTurckFrozenAffineEvolution x0 Kc hKc Ko hKo hKoEq hcover hP b t₀ σ0' t‖
      ≤ Real.exp (|t - t₀| * (2 * Kp + ‖b‖)) * ‖σ0 - σ0'‖ := by
  have hop := deTurckReactionSectionMapL_opNorm_le x0 Kc hKc Ko hKo hKoEq hcover hP Kp hKp0 hKp
  simp only [deTurckFrozenAffineEvolution]
  refine (norm_affineFundamentalSolution_sub_le
    (deTurckReactionSectionMapL x0 Kc hKc Ko hKo hKoEq hcover hP) b t₀ σ0 σ0' t).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine Real.exp_le_exp.2 ?_
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  linarith [hop]

end PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace
