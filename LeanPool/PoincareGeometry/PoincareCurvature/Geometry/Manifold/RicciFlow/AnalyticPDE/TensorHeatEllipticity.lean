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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatCoordinateOperator
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteCylinderCauchyOperator
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Ellipticity and the frozen operator for tensor heat flow

This file proves that the principal coefficient obtained from the *actual*
connection Laplacian is strongly elliptic.  The proof is geometric rather
than axiomatic: the local tangent frame has a positive-definite Riemannian
Gram matrix, its inverse is positive definite, and the frame pulled into a
manifold chart is still a basis of the model space.

The final section freezes this coefficient at a chart point and packages
`∂ₜ - AₓD²` as a bounded operator between the finite-cylinder parabolic
Banach spaces.  Its evaluation theorem is the bridge needed by the frozen
parametrix construction.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff BigOperators

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The inverse of the actual Riemannian Gram matrix of a genuine local
tangent frame is positive definite. -/
theorem localFrameInverseGramMatrix_posDef
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet) :
    (show Matrix ι ι ℝ from
      localFrameInverseGramMatrix (I := I) e b x).PosDef := by
  apply Matrix.PosDef.inv
  change (Matrix.gram ℝ (fun i => e.localFrame b i x)).PosDef
  apply Matrix.posDef_gram_of_linearIndependent
  simpa [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
    (e := e) (b := b) hx] using (e.basisAt b hx).linearIndependent

/-- Strict positivity of the inverse-Gram quadratic form in local-frame
coordinates. -/
theorem localFrameInverseGramMatrix_quadratic_pos
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M} (hx : x ∈ e.baseSet)
    {c : ι → ℝ} (hc : c ≠ 0) :
    0 < ∑ i : ι, ∑ j : ι,
      localFrameInverseGramMatrix (I := I) e b x i j * c i * c j := by
  have h := (localFrameInverseGramMatrix_posDef (I := I) e b hx).dotProduct_mulVec_pos hc
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm] using h

/-- Evaluation of a fixed-chart inverse-Gram coefficient at the chart image
of a point returns the corresponding intrinsic coefficient. -/
theorem localFrameInverseGramMatrixInChart_apply
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M}
    (hx : x ∈ (extChartAt I p).source) (i j : ι) :
    localFrameInverseGramMatrixInChart (I := I)
        p e b i j ((extChartAt I p) x) =
      localFrameInverseGramMatrix (I := I) e b x i j := by
  simp [localFrameInverseGramMatrixInChart, writtenInExtChartAt]
  simp_all only [mfld_simps, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply]

/-- Pulling a genuine local tangent frame back through a manifold chart
preserves linear independence. -/
theorem linearIndependent_localFrameInChart
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source) :
    LinearIndependent ℝ (fun i =>
      localFrameInChart (I := I) p e b i ((extChartAt I p) x)) := by
  let φ := extChartAt I p
  let z := φ x
  have hz : z ∈ φ.target := φ.map_source hxChart
  have hxy : φ.symm z = x := φ.left_inv hxChart
  have hInv := isInvertible_mfderivWithin_extChartAt_symm hz
  rw [hxy] at hInv
  rcases hInv with ⟨L, hL⟩
  have hV (i : ι) :
      localFrameInChart (I := I) p e b i z =
        L.symm (e.localFrame b i x) := by
    unfold localFrameInChart
    rw [VectorField.mpullbackWithin_apply]
    change (mfderiv[Set.range I] φ.symm z).inverse
        (e.localFrame b i (φ.symm z)) = _
    rw [hxy, ← hL, ContinuousLinearMap.inverse_equiv]
    rfl
  have hframe : LinearIndependent ℝ (fun i => e.localFrame b i x) := by
    simpa [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
      (e := e) (b := b) hxFrame] using (e.basisAt b hxFrame).linearIndependent
  have hmap : LinearIndependent ℝ (fun i => L.symm (e.localFrame b i x)) :=
    hframe.map' L.symm.toLinearMap (LinearMap.ker_eq_bot.mpr L.symm.injective)
  rw [show (fun i =>
      localFrameInChart (I := I) p e b i ((extChartAt I p) x)) =
      (fun i => L.symm (e.localFrame b i x)) by
    funext i
    exact hV i]
  exact hmap

/-- A nonzero covector cannot vanish on every member of a finite family
which has the same cardinality as a basis and is linearly independent. -/
theorem basisReadout_ne_zero
    (b : Module.Basis ι ℝ E) (V : ι → E)
    (hV : LinearIndependent ℝ V)
    {ξ : E →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    (fun i => ξ (V i)) ≠ 0 := by
  intro hread
  apply hξ
  have hspan : Submodule.span ℝ (Set.range V) = ⊤ :=
    hV.span_eq_top_of_card_eq_finrank'
      (Module.finrank_eq_card_basis b).symm
  have hlin : ξ.toLinearMap = 0 := LinearMap.ext_on hspan (by
    intro v hv
    rcases hv with ⟨i, rfl⟩
    simpa using congrFun hread i)
  exact ContinuousLinearMap.ext fun v => LinearMap.congr_fun hlin v

/-- Every nonzero chart covector has a nonzero coordinate readout on the
pulled-back local frame. -/
theorem localFrameInChart_readout_ne_zero
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {ξ : E →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    (fun i => ξ (localFrameInChart (I := I)
      p e b i ((extChartAt I p) x))) ≠ 0 :=
  basisReadout_ne_zero b _
    (linearIndependent_localFrameInChart
      (I := I) p e b hxFrame hxChart) hξ

/-- Strict positivity of the genuine connection-Laplacian principal symbol
in a fixed manifold chart. -/
theorem localFrameInverseGramMatrixInChart_symbol_pos
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {ξ : E →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    0 < ∑ i : ι, ∑ j : ι,
      localFrameInverseGramMatrixInChart (I := I)
          p e b i j ((extChartAt I p) x) *
        ξ (localFrameInChart (I := I)
          p e b i ((extChartAt I p) x)) *
        ξ (localFrameInChart (I := I)
          p e b j ((extChartAt I p) x)) := by
  simpa only [localFrameInverseGramMatrixInChart_apply
    (I := I) p e b hxChart] using
    localFrameInverseGramMatrix_quadratic_pos (I := I) e b hxFrame
      (localFrameInChart_readout_ne_zero
        (I := I) p e b hxFrame hxChart hξ)

end CovariantDerivative

namespace RicciFlow
namespace AnalyticPDE

open CovariantDerivative

variable {X W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The `W`-valued rank-one Hessian `ξ ⊗ ξ ⊗ w`. -/
def rankOneHessian (ξ : X →L[ℝ] ℝ) (w : W) :
    X →L[ℝ] X →L[ℝ] W :=
  ξ.smulRight (ξ.smulRight w)

@[simp]
theorem rankOneHessian_apply
    (ξ : X →L[ℝ] ℝ) (w : W) (v₁ v₂ : X) :
    rankOneHessian ξ w v₁ v₂ = (ξ v₁ * ξ v₂) • w := by
  simp [rankOneHessian, mul_smul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "TW" => (ι × ι → ℝ)

local instance tensorEllipticityNormedAddCommGroup :
    NormedAddCommGroup TW := Pi.normedAddCommGroup
local instance tensorEllipticityNormedSpace :
    NormedSpace ℝ TW := Pi.normedSpace

/-- The principal coefficient sends a rank-one Hessian to scalar
multiplication by the inverse-metric quadratic form. -/
theorem localTensorHeatPrincipalCoefficient_rankOne
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (z : E)
    (ξ : E →L[ℝ] ℝ) (w : TW) :
    localTensorHeatPrincipalCoefficient (I := I) p e b z
        (rankOneHessian ξ w) =
      (∑ i : ι, ∑ j : ι,
        localFrameInverseGramMatrixInChart (I := I) p e b i j z *
          ξ (localFrameInChart (I := I) p e b i z) *
          ξ (localFrameInChart (I := I) p e b j z)) • w := by
  funext out
  simp [localTensorHeatPrincipalCoefficient, rankOneHessian_apply,
    Finset.sum_mul, mul_assoc]

/-- The frozen principal coefficient at a manifold point, expressed in a
fixed chart. -/
def frozenLocalTensorHeatPrincipalCoefficient
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (x : M) :
    (E →L[ℝ] E →L[ℝ] TW) →L[ℝ] TW :=
  localTensorHeatPrincipalCoefficient (I := I) p e b ((extChartAt I p) x)

/-- **Strong ellipticity of the actual frozen tensor-heat coefficient.**
For every nonzero chart covector, the system symbol is multiplication by a
strictly positive scalar. -/
theorem frozenLocalTensorHeatPrincipalCoefficient_stronglyElliptic
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {ξ : E →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    ∃ q : ℝ, 0 < q ∧ ∀ w : TW,
      frozenLocalTensorHeatPrincipalCoefficient (I := I) p e b x
          (rankOneHessian ξ w) = q • w := by
  let q := ∑ i : ι, ∑ j : ι,
    localFrameInverseGramMatrixInChart (I := I)
        p e b i j ((extChartAt I p) x) *
      ξ (localFrameInChart (I := I)
        p e b i ((extChartAt I p) x)) *
      ξ (localFrameInChart (I := I)
        p e b j ((extChartAt I p) x))
  refine ⟨q, localFrameInverseGramMatrixInChart_symbol_pos
    (I := I) p e b hxFrame hxChart hξ, ?_⟩
  intro w
  exact localTensorHeatPrincipalCoefficient_rankOne
    (I := I) p e b ((extChartAt I p) x) ξ w

/-- The bounded frozen tensor-heat Cauchy operator `∂ₜ - AₓD²` on a finite
parabolic cylinder. -/
def frozenTensorHeatCauchyL
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (x : M)
    (t₀ T α : ℝ) :
    FiniteParabolicC2AlphaBanach E TW t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach E TW α
        (parabolicFiniteCylinder E t₀ T) :=
  FiniteParabolicC2AlphaBanach.timeDerivComponentL -
    (ParabolicC0AlphaBanach.compL
      (frozenLocalTensorHeatPrincipalCoefficient (I := I) p e b x)).comp
      FiniteParabolicC2AlphaBanach.spaceSecondDerivComponentL

/-- Pointwise evaluation of the genuine frozen Cauchy operator. -/
theorem evalCLM_frozenTensorHeatCauchyL
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) (x : M)
    {t₀ T α : ℝ}
    (u : FiniteParabolicC2AlphaBanach E TW t₀ T α)
    (z : ℝ × E) (hz : z ∈ parabolicFiniteCylinder E t₀ T) :
    ParabolicC0AlphaBanach.evalCLM z hz
        (frozenTensorHeatCauchyL (I := I) p e b x t₀ T α u) =
      FiniteParabolicC2AlphaBanach.timeDeriv u z -
        frozenLocalTensorHeatPrincipalCoefficient (I := I) p e b x
          (FiniteParabolicC2AlphaBanach.spaceSecondDeriv u z) := by
  rw [frozenTensorHeatCauchyL, ContinuousLinearMap.sub_apply, map_sub,
    FiniteParabolicC2AlphaBanach.evalCLM_timeDerivComponentL,
    ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_compL_apply,
    FiniteParabolicC2AlphaBanach.evalCLM_spaceSecondDerivComponentL]

end AnalyticPDE
end RicciFlow
