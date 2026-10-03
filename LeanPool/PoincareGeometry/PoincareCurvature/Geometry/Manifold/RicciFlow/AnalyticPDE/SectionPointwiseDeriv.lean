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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.GeometricReactionPicardTangent

/-!
# Pointwise scalar evaluation of tangent bilinear-form section curves

For the tangent-bundle bilinear-form continuous section space
`CSS := ContinuousSectionSpace … (fun i ↦ trivializationAt BilF BilW (x0 i)) Kc …` (the space the
concrete geometric Ricci–DeTurck chart operator and its frozen affine evolution act on), the *scalar
pointwise evaluation* `s ↦ s x u v` — evaluate the section at `x`, then feed the resulting fibrewise
bilinear form the two tangent vectors `u v : TangentSpace I x` — is a **continuous linear functional**
`CSS →L[ℝ] ℝ`.

It is built **diamond-free**, on the hom-fibre-topology (Path B) track that `s` itself carries:

* the finite-dimensional **model coordinate readout** `coordReadoutContinuousLinearMap … : CSS →L[ℝ] BilF`
  (whose codomain carries the clean model-fibre norm on `E →L[ℝ] E →L[ℝ] ℝ`), followed by
* the trivialization's fibrewise **linear** inverse `Trivialization.symmₗ` (which needs only `IsLinear`
  and the fibre module structure — *no* fibre `NormedAddCommGroup` — supplied here by
  `trivializationAt_bilinearFormBundle_isLinear`), whose coordinate identity is discharged by the
  hom-fibre `coord_apply_tangent` (not the seminormed-track `coord_apply`, which resolves the fibre
  topology to `PseudoMetricSpace…` and triggers the transported-instance diamond), followed by
* the fibrewise bilinear evaluation `bilinearFormEvalₗ`.

Because `BilF` is finite-dimensional, the composed bare `ℝ`-linear map is automatically continuous
(`LinearMap.toContinuousLinearMap`).

The payoff is `hasDerivAt_scalarEval_of_hasDerivAt`: a `HasDerivAt` of a `CSS`-valued curve pushes
through the scalar evaluation to a genuine scalar `HasDerivAt (fun τ ↦ f τ x u v) (f' x u v) t` — the
scalar section-curve `HasDerivAt` datum the smooth-realization endpoint time-derivative obligations
(`hasTimeDerivativeAt_of_sectionCurve_hasDerivAt`) consume, including at the interval endpoints where
the interior Banach ODE does not by itself supply a full `HasDerivAt`.
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
local notation "BilF" => (E →L[ℝ] E →L[ℝ] ℝ)
local notation "BilW" => (_root_.Bundle.BilinearFormBundle (V := TM))
local instance instTangentBilFNormedAddCommGroup : NormedAddCommGroup BilF :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
local instance instTangentBilFNormedSpace : NormedSpace ℝ BilF :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))
local instance instTangentBilFFiniteDimensional : FiniteDimensional ℝ BilF :=
  (inferInstance : FiniteDimensional ℝ (E →L[ℝ] E →L[ℝ] ℝ))

/-- Pointwise scalar evaluation of a fibrewise tangent bilinear form, packaged as an `ℝ`-linear map. -/
def bilinearFormEvalₗ {x : M} (u v : TM x) :
    (TM x →L[ℝ] TM x →L[ℝ] ℝ) →ₗ[ℝ] ℝ where
  toFun w := w u v
  map_add' w₁ w₂ := by simp only [ContinuousLinearMap.add_apply]
  map_smul' c w := by
    simp only [ContinuousLinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]

@[simp] theorem bilinearFormEvalₗ_apply {x : M} (u v : TM x) (w : TM x →L[ℝ] TM x →L[ℝ] ℝ) :
    bilinearFormEvalₗ (I := I) u v w = w u v := rfl

/-- **Scalar pointwise evaluation `s ↦ s x u v` of the tangent bilinear-form continuous section space,
as a continuous linear functional.** Built directly as a `ContinuousLinearMap` structure (the flat
form, which avoids the `BilinearFormBundle` CSS-type `whnf` blow-up of nested constructors) on the
hom-fibre-topology (Path B) track that `s` itself carries: the algebra fields are the diamond-free
pointwise `add_apply_tangent`/`smul_apply_tangent`, and continuity is `continuous_of_linear_of_bound`
with the operator bound `|s x u v| ≤ C·‖s‖` obtained from the model coordinate bound
`coord_norm_le_norm` (`‖coord s i x‖ ≤ ‖s‖`) and the operator norm of the automatically-continuous
finite-dimensional linear map `w ↦ (symmₗ w) u v` on `BilF` (the fibrewise linear inverse `symmₗ`
followed by the bilinear evaluation), never touching the transported `BilinearFormBundle` fibre norm. -/
noncomputable def sectionScalarEvalCLM
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (i : κ) (x : M) (hx : x ∈ (Kc i : Set M)) (u v : TM x) :
    ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover →L[ℝ] ℝ where
  toFun s := s x u v
  map_add' s t := by
    show (s + t).toFun x u v = s.toFun x u v + t.toFun x u v
    rw [add_apply_tangent x0 Kc hKc Ko hKo hKoEq hcover s t x]
    simp only [ContinuousLinearMap.add_apply]
  map_smul' c s := by
    show (c • s).toFun x u v = (RingHom.id ℝ) c • (s.toFun x u v)
    rw [smul_apply_tangent x0 Kc hKc Ko hKo hKoEq hcover c s x]
    simp only [ContinuousLinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
  cont := by
    haveI : (trivializationAt BilF BilW (x0 i)).IsLinear ℝ :=
      _root_.Bundle.trivializationAt_bilinearFormBundle_isLinear (F := E) (W := TM) (x0 i)
    refine continuous_of_linear_of_bound (𝕜 := ℝ)
      (C := ‖LinearMap.toContinuousLinearMap
        (bilinearFormEvalₗ (I := I) u v ∘ₗ (trivializationAt BilF BilW (x0 i)).symmₗ ℝ x)‖)
      (fun s t => ?_) (fun (c : ℝ) s => ?_) (fun s => ?_)
    · show (s + t).toFun x u v = s.toFun x u v + t.toFun x u v
      rw [add_apply_tangent x0 Kc hKc Ko hKo hKoEq hcover s t x]
      simp only [ContinuousLinearMap.add_apply]
    · show (c • s).toFun x u v = c • (s.toFun x u v)
      rw [smul_apply_tangent x0 Kc hKc Ko hKo hKoEq hcover c s x]
      simp only [ContinuousLinearMap.smul_apply]
    · have hid : LinearMap.toContinuousLinearMap
            (bilinearFormEvalₗ (I := I) u v ∘ₗ (trivializationAt BilF BilW (x0 i)).symmₗ ℝ x)
            ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
              (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover s).1 i ⟨x, hx⟩)
            = s x u v := by
        rw [LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
          coord_apply_tangent x0 Kc hKc Ko hKo hKoEq hcover s i ⟨x, hx⟩,
          Trivialization.continuousLinearMapAt_apply,
          (trivializationAt BilF BilW (x0 i)).symmₗ_linearMapAt (hKc i hx) (s x),
          bilinearFormEvalₗ_apply]
      have hop := (LinearMap.toContinuousLinearMap
          (bilinearFormEvalₗ (I := I) u v ∘ₗ
            (trivializationAt BilF BilW (x0 i)).symmₗ ℝ x)).le_opNorm
          ((equivCompatibleCoordFamilySubmodule (𝕜 := ℝ) (F := BilF) (V := BilW)
            (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover s).1 i ⟨x, hx⟩)
      rw [hid] at hop
      exact hop.trans (mul_le_mul_of_nonneg_left
        (coord_norm_le_norm_topFibre (𝕜 := ℝ) (F := BilF) (V := BilW)
          (et := fun i => trivializationAt BilF BilW (x0 i)) (Kc := Kc) (hKc := hKc)
          (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover) s i ⟨x, hx⟩)
        (norm_nonneg _))

@[simp] theorem sectionScalarEvalCLM_apply
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (i : κ) (x : M) (hx : x ∈ (Kc i : Set M)) (u v : TM x)
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    sectionScalarEvalCLM x0 Kc hKc Ko hKo hKoEq hcover i x hx u v s = s x u v := rfl

/-- **Push a `CSS`-valued `HasDerivAt` through scalar pointwise evaluation.** If a curve
`f : ℝ → CSS` has derivative `f'` at `t`, then for any base point `x` and tangent vectors
`u v : TangentSpace I x`, the scalar curve `τ ↦ f τ x u v` has derivative `f' x u v` at `t`. Proved
by feeding the derivative through the continuous linear functional `sectionScalarEvalCLM`. -/
theorem hasDerivAt_scalarEval_of_hasDerivAt
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {f : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover}
    {f' : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover}
    {t : ℝ} (hf : HasDerivAt f f' t)
    (x : M) (u v : TM x) :
    HasDerivAt (fun τ : ℝ ↦ f τ x u v) (f' x u v) t := by
  letI : ∀ y : M, ContinuousAdd (TM y →L[ℝ] ℝ) := fun y => inferInstance
  obtain ⟨i, hi⟩ : ∃ i, x ∈ (Kc i : Set M) :=
    Set.mem_iUnion.mp (by rw [hcover]; exact Set.mem_univ x)
  have hcomp : HasDerivAt
      (fun τ : ℝ ↦ sectionScalarEvalCLM x0 Kc hKc Ko hKo hKoEq hcover i x hi u v (f τ))
      (sectionScalarEvalCLM x0 Kc hKc Ko hKo hKoEq hcover i x hi u v f') t := by
    simpa [Function.comp_def] using
      ((sectionScalarEvalCLM x0 Kc hKc Ko hKo hKoEq hcover i x hi u v).hasFDerivAt.comp t
        hf.hasFDerivAt).hasDerivAt
  have e1 : (fun τ : ℝ ↦ f τ x u v)
      = fun τ : ℝ ↦ sectionScalarEvalCLM x0 Kc hKc Ko hKo hKoEq hcover i x hi u v (f τ) := by
    funext τ; rw [sectionScalarEvalCLM_apply]
  have e2 : f' x u v
      = sectionScalarEvalCLM x0 Kc hKc Ko hKo hKoEq hcover i x hi u v f' := by
    rw [sectionScalarEvalCLM_apply]
  rw [e1, e2]
  exact hcomp

/-- **Interior scalar section-curve derivative of a Banach evolution local solution.** For `t` in the
open evolution interval, the scalar curve `τ ↦ sol.curve τ x u v` has time-derivative
`A t (sol.curve t) x u v`.  This is the interior scalar section-curve `HasDerivAt` datum that the
smooth-realization bridge `hasTimeDerivativeAt_of_sectionCurve_hasDerivAt` consumes (obtained by
pushing the `CSS`-level Banach ODE `equation_hasDerivAt_of_mem_Ioo` through `sectionScalarEvalCLM`). -/
theorem hasDerivAt_scalarEval_banachEvolution_of_mem_Ioo
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {A : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover}
    {t₀ : ℝ}
    {u₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover}
    (sol : RicciFlow.AnalyticPDE.BanachEvolutionLocalSolution A t₀ u₀)
    {t : ℝ} (ht : t ∈ Set.Ioo t₀ sol.terminalTime)
    (x : M) (u v : TM x) :
    HasDerivAt (fun τ : ℝ ↦ sol.curve τ x u v) (A t (sol.curve t) x u v) t :=
  hasDerivAt_scalarEval_of_hasDerivAt x0 Kc hKc Ko hKo hKoEq hcover
    (sol.equation_hasDerivAt_of_mem_Ioo ht) x u v

/-- The state-constrained (`BanachEvolutionLocalSolutionIn`) form of
`hasDerivAt_scalarEval_banachEvolution_of_mem_Ioo`: the exact shape the chart-closure
`realization` field carries for the interior of the solution interval. -/
theorem hasDerivAt_scalarEval_banachEvolutionIn_of_mem_Ioo
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt BilF BilW (x0 i)).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {A : ℝ → ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)}
    {t₀ : ℝ}
    {u₀ : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover}
    (sol : RicciFlow.AnalyticPDE.BanachEvolutionLocalSolutionIn A stateSet t₀ u₀)
    {t : ℝ} (ht : t ∈ Set.Ioo t₀ sol.terminalTime)
    (x : M) (u v : TM x) :
    HasDerivAt (fun τ : ℝ ↦ sol.curve τ x u v) (A t (sol.curve t) x u v) t :=
  hasDerivAt_scalarEval_of_hasDerivAt x0 Kc hKc Ko hKo hKoEq hcover
    (sol.toBanachEvolutionLocalSolution.equation_hasDerivAt_of_mem_Ioo ht) x u v

end PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace
