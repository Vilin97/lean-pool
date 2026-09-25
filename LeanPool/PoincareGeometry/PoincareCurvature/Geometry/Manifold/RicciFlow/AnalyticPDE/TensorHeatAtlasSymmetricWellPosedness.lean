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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasSpatialData

/-!
# Symmetric closed tensor heat

This file passes from the ambient covariant-two-tensor well-posedness theorem
to the advertised symmetric system.  Slot transposition and symmetrization are
performed on the actual atlas higher jets.  Their reconstructed geometric
fields are shown to be the genuine fiberwise transpose and symmetrization,
and the latter commutes with the intrinsic connection Laplacian.
-/

@[expose] public section

@[expose] public noncomputable section
open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff Topology

namespace RicciFlow
namespace AnalyticPDE

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

@[reducible] local instance symmetricWellPosedTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedAddCommGroup x
@[reducible] local instance symmetricWellPosedTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedSpace x
@[reducible] local instance symmetricWellPosedThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedAddCommGroup
@[reducible] local instance symmetricWellPosedThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedSpace
@[reducible] local instance symmetricWellPosedThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedAddCommGroup x
@[reducible] local instance symmetricWellPosedThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedSpace x
local instance symmetricWellPosedThreeTotalSpaceTopology :
    TopologicalSpace (TotalSpace
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance symmetricWellPosedThreeFiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance symmetricWellPosedThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂

/-- Fiberwise transposition using the tangent bundle's canonical bilinear
slot-flip. -/
def transposeTensorSection (h : ∀ x : M, T₂ x) : ∀ x : M, T₂ x :=
  fun x => _root_.CovariantDerivative.flipLastTwo (I := I) x (h x)

@[simp] theorem transposeTensorSection_apply
    (h : ∀ x : M, T₂ x) (x : M) (u v : TM x) :
    transposeTensorSection h x u v = h x v u := rfl

/-- The induced two-tensor connection commutes with fiberwise transposition
whenever both sections have their genuine first derivatives at the point. -/
theorem covariantTwoTensorCovariantDerivative_flip
    (cov : _root_.CovariantDerivative I E TM) (h : ∀ x : M, T₂ x) (x : M)
    (hh : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) y (h y)) x)
    (hflip : MDiffAt (fun y => TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) y
        (transposeTensorSection h y)) x)
    (X u v : TM x) :
    _root_.CovariantDerivative.covariantTwoTensorCovariantDerivative cov
        (transposeTensorSection h) x X u v =
      _root_.CovariantDerivative.covariantTwoTensorCovariantDerivative
        cov h x X v u := by
  rw [_root_.CovariantDerivative.covariantTwoTensorCovariantDerivative_apply_of_mdifferentiableAt
      cov hflip X u v,
    _root_.CovariantDerivative.covariantTwoTensorCovariantDerivative_apply_of_mdifferentiableAt
      cov hh X v u]
  simp only [transposeTensorSection_apply]
  ring

/-- On two genuine second-order-domain sections related by fiberwise
transposition, the connection Laplacian transposes in the same way. -/
theorem connectionLaplacian_flip_of_mem_domain
    (cov : _root_.CovariantDerivative I E TM)
    (h hflip : _root_.CovariantDerivative.ConnectionLaplacianDomain
      (E := E) (I := I) (M := M) cov)
    (heq : hflip.1 = transposeTensorSection h.1)
    (x : M) (u v : TM x) :
    _root_.CovariantDerivative.connectionLaplacian cov hflip.1 x u v =
      _root_.CovariantDerivative.connectionLaplacian cov h.1 x v u := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  rw [_root_.CovariantDerivative.connectionLaplacian_eq_sum_orthonormalBasis
      cov hflip.1 x b,
    _root_.CovariantDerivative.connectionLaplacian_eq_sum_orthonormalBasis
      cov h.1 x b]
  simp only [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [heq]
  have hflipFirst := hflip.2.2 x
  rw [heq] at hflipFirst
  rw [_root_.CovariantDerivative.covariantHessianTwoTensor_apply_of_mdifferentiableAt
      cov _ hflipFirst (b i) (b i) u v,
    _root_.CovariantDerivative.covariantHessianTwoTensor_apply_of_mdifferentiableAt
      cov _ (h.2.2 x) (b i) (b i) v u]
  have hfirst : ∀ y X a c,
      _root_.CovariantDerivative.covariantTwoTensorCovariantDerivative cov
          (transposeTensorSection h.1) y X a c =
        _root_.CovariantDerivative.covariantTwoTensorCovariantDerivative
          cov h.1 y X c a := by
    intro y X a c
    exact covariantTwoTensorCovariantDerivative_flip cov h.1 y
      (h.2.1 y) (heq ▸ hflip.2.1 y) X a c
  simp_rw [hfirst]
  ring

namespace FiniteTensorHeatParametrixAtlas

open CovariantDerivative

/-- Swap the two finite tensor-component indices. -/
def pairTransposeL : W₂ →L[ℝ] W₂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q ij => q (ij.2, ij.1)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

@[simp] theorem pairTransposeL_apply (q : W₂) (ij : Fin d × Fin d) :
    pairTransposeL q ij = q (ij.2, ij.1) := rfl

/-- Transpose every value and every derivative in a finite-cylinder higher
jet by postcomposition on the tensor-component fiber. -/
def transposeHigherCoefficient :
    FiniteParabolicC2AlphaBanach E W₂ t₀ T α →L[ℝ]
      FiniteParabolicC2AlphaBanach E W₂ t₀ T α :=
  FiniteParabolicC2AlphaBanach.fiberPostcompL pairTransposeL

@[simp] theorem value_transposeHigherCoefficient
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (z : ℝ × E) (hz : z ∈ parabolicFiniteCylinder E t₀ T)
    (ij : Fin d × Fin d) :
    FiniteParabolicC2AlphaBanach.value (transposeHigherCoefficient u) z ij =
      FiniteParabolicC2AlphaBanach.value u z (ij.2, ij.1) := by
  rw [transposeHigherCoefficient,
    FiniteParabolicC2AlphaBanach.value_fiberPostcompL _ _ z hz]
  rfl

@[simp] theorem timeDeriv_transposeHigherCoefficient
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (z : ℝ × E) (hz : z ∈ parabolicFiniteCylinder E t₀ T)
    (ij : Fin d × Fin d) :
    FiniteParabolicC2AlphaBanach.timeDeriv
        (transposeHigherCoefficient u) z ij =
      FiniteParabolicC2AlphaBanach.timeDeriv u z (ij.2, ij.1) := by
  rw [transposeHigherCoefficient,
    FiniteParabolicC2AlphaBanach.timeDeriv_fiberPostcompL _ _ z hz]
  rfl

/-- The matrix reconstructed from a transposed pair-indexed higher jet is
the transpose of the original reconstructed matrix. -/
theorem normalizedHigherSolution_transpose_value
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (z : ℝ × E) (hz : z ∈ parabolicFiniteCylinder E t₀ T)
    (i j : Fin d) :
    FiniteParabolicC2AlphaBanach.value
        (normalizedHigherSolution (transposeHigherCoefficient u)) z i j =
      FiniteParabolicC2AlphaBanach.value
        (normalizedHigherSolution u) z j i := by
  unfold normalizedHigherSolution
  rw [FiniteParabolicC2AlphaBanach.value_fiberPostcompL _ _ z hz,
    FiniteParabolicC2AlphaBanach.value_fiberPostcompL _ _ z hz]
  change FiniteParabolicC2AlphaBanach.value
      (transposeHigherCoefficient u) z (j, i) =
    FiniteParabolicC2AlphaBanach.value u z (i, j)
  exact value_transposeHigherCoefficient u z hz (j, i)

/-- The time-derivative matrix reconstructed from a transposed higher jet is
also the transpose of the original one. -/
theorem normalizedHigherSolution_transpose_timeDeriv
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (z : ℝ × E) (hz : z ∈ parabolicFiniteCylinder E t₀ T)
    (i j : Fin d) :
    FiniteParabolicC2AlphaBanach.timeDeriv
        (normalizedHigherSolution (transposeHigherCoefficient u)) z i j =
      FiniteParabolicC2AlphaBanach.timeDeriv
        (normalizedHigherSolution u) z j i := by
  unfold normalizedHigherSolution
  rw [FiniteParabolicC2AlphaBanach.timeDeriv_fiberPostcompL _ _ z hz,
    FiniteParabolicC2AlphaBanach.timeDeriv_fiberPostcompL _ _ z hz]
  change FiniteParabolicC2AlphaBanach.timeDeriv
      (transposeHigherCoefficient u) z (j, i) =
    FiniteParabolicC2AlphaBanach.timeDeriv u z (i, j)
  exact timeDeriv_transposeHigherCoefficient u z hz (j, i)

/-- Transpose each member of a finite atlas higher family. -/
def transposeHigherFamily
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A) : HigherCoefficientSpace cov A :=
  fun i => transposeHigherCoefficient (u i)

/-- On the actual common interval, transposing one higher chart jet flips the
two slots of its reconstructed local geometric tensor. -/
theorem localFieldOfHigher_transpose_toFun
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (t : ℝ) (ht : t ∈ Ioc t₀ A.commonTerminalTime)
    (x : M) (v w : TM x) :
    (localFieldOfHigher cov A i (transposeHigherCoefficient u)).toFun t x v w =
      (localFieldOfHigher cov A i u).toFun t x w v := by
  let s := FiniteClassicalTensorHeatField.normalizedTime
    t₀ (A.radius (i : M)) t
  let xi := normalizedTensorHeatCoordinate (I := I)
    (i : M) (A.radius (i : M)) x
  have hs : s ∈ Ioc t₀ T := by
    apply FiniteClassicalTensorHeatField.normalizedTime_mem_Ioc
      (ne_of_gt (A.radius_pos (i : M)))
    exact ⟨ht.1, ht.2.trans (A.commonTerminalTime_le cov i)⟩
  have hz : (s, xi) ∈ parabolicFiniteCylinder E t₀ T := by
    simpa [xi] using hs
  change cutoffLocalTensorOfMatrix (I := I)
      (trivializationAt E TM (i : M)) b (A.cover.partition i)
      (normalizedTensorHeatCoefficientSlice (I := I) (i : M)
        (A.radius (i : M))
        (normalizedHigherSolution (transposeHigherCoefficient u)) s) x v w =
    cutoffLocalTensorOfMatrix (I := I)
      (trivializationAt E TM (i : M)) b (A.cover.partition i)
      (normalizedTensorHeatCoefficientSlice (I := I) (i : M)
        (A.radius (i : M)) (normalizedHigherSolution u) s) x w v
  have hcoeff :
      (fun y p k => normalizedTensorHeatCoefficientSlice (I := I)
        (i : M) (A.radius (i : M))
        (normalizedHigherSolution (transposeHigherCoefficient u)) s y k p) =
      normalizedTensorHeatCoefficientSlice (I := I) (i : M)
        (A.radius (i : M)) (normalizedHigherSolution u) s := by
    funext y p k
    apply normalizedHigherSolution_transpose_value u
    simpa [normalizedTensorHeatCoefficientSlice, s] using hs
  rw [← cutoffLocalTensorOfMatrix_transpose_apply, hcoeff]

/-- The transposed local field's time derivative is the slot-flip of the
original time derivative. -/
theorem localFieldOfHigher_transpose_timeDerivative
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α)
    (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime)
    (x : M) (v w : TM x) :
    (localFieldOfHigher cov A i
        (transposeHigherCoefficient u)).timeDerivative t x v w =
      (localFieldOfHigher cov A i u).timeDerivative t x w v := by
  let s := FiniteClassicalTensorHeatField.normalizedTime
    t₀ (A.radius (i : M)) t
  let xi := normalizedTensorHeatCoordinate (I := I)
    (i : M) (A.radius (i : M)) x
  have hs : s ∈ Ioc t₀ T := by
    exact A.normalizedTime_mem_Ioc_of_mem_commonInterval cov i ht
  have hz : (s, xi) ∈ parabolicFiniteCylinder E t₀ T := by
    simpa [xi] using hs
  change (A.radius (i : M))⁻¹ ^ 2 *
      cutoffLocalTensorOfMatrix (I := I)
        (trivializationAt E TM (i : M)) b (A.cover.partition i)
        (fun y => FiniteParabolicC2AlphaBanach.timeDeriv
          (normalizedHigherSolution (transposeHigherCoefficient u))
          (s, normalizedTensorHeatCoordinate (I := I)
            (i : M) (A.radius (i : M)) y)) x v w =
    (A.radius (i : M))⁻¹ ^ 2 *
      cutoffLocalTensorOfMatrix (I := I)
        (trivializationAt E TM (i : M)) b (A.cover.partition i)
        (fun y => FiniteParabolicC2AlphaBanach.timeDeriv
          (normalizedHigherSolution u)
          (s, normalizedTensorHeatCoordinate (I := I)
            (i : M) (A.radius (i : M)) y)) x w v
  congr 1
  have hcoeff :
      (fun y p k => FiniteParabolicC2AlphaBanach.timeDeriv
        (normalizedHigherSolution (transposeHigherCoefficient u))
        (s, normalizedTensorHeatCoordinate (I := I)
          (i : M) (A.radius (i : M)) y) k p) =
      (fun y => FiniteParabolicC2AlphaBanach.timeDeriv
        (normalizedHigherSolution u)
        (s, normalizedTensorHeatCoordinate (I := I)
          (i : M) (A.radius (i : M)) y)) := by
    funext y p k
    apply normalizedHigherSolution_transpose_timeDeriv u
    simpa [s] using hs
  rw [← cutoffLocalTensorOfMatrix_transpose_apply, hcoeff]

/-- The atlas reconstruction of the componentwise transposed higher family
is the genuine fiberwise transpose of the original atlas field. -/
theorem atlasFieldOfHigher_transpose_toFun
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A)
    (t : ℝ) (ht : t ∈ Ioc t₀ A.commonTerminalTime)
    (x : M) (v w : TM x) :
    (atlasFieldOfHigher cov A (transposeHigherFamily cov A u)).toFun t x v w =
      (atlasFieldOfHigher cov A u).toFun t x w v := by
  simp only [atlasFieldOfHigher_toFun, _root_.sum_apply,
    transposeHigherFamily]
  apply Finset.sum_congr rfl
  intro i _hi
  exact localFieldOfHigher_transpose_toFun cov A i (u i) t ht x v w

/-- The atlas time derivative commutes with componentwise transposition. -/
theorem atlasFieldOfHigher_transpose_timeDerivative
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A)
    (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime)
    (x : M) (v w : TM x) :
    (atlasFieldOfHigher cov A
        (transposeHigherFamily cov A u)).timeDerivative t x v w =
      (atlasFieldOfHigher cov A u).timeDerivative t x w v := by
  simp only [atlasFieldOfHigher, FiniteClassicalTensorHeatField.finsetSum_timeDerivative,
    _root_.sum_apply, transposeHigherFamily]
  apply Finset.sum_congr rfl
  intro i _hi
  exact localFieldOfHigher_transpose_timeDerivative cov A i (u i) t ht x v w

/-- Fiberwise symmetrization of an arbitrary covariant two-tensor section. -/
def symmetrizeTensorSection (h : ∀ x : M, T₂ x) : ∀ x : M, T₂ x :=
  (2⁻¹ : ℝ) • (h + transposeTensorSection h)

@[simp] theorem symmetrizeTensorSection_apply
    (h : ∀ x : M, T₂ x) (x : M) (u v : TM x) :
    symmetrizeTensorSection h x u v = (h x u v + h x v u) / 2 := by
  simp [symmetrizeTensorSection, div_eq_mul_inv]
  ring

/-- The symmetrization is a genuinely symmetric covariant two-tensor. -/
theorem symmetrizeTensorSection_isSymmetric (h : ∀ x : M, T₂ x) :
    ∀ x : M, ∀ u v : TM x,
      symmetrizeTensorSection h x u v =
        symmetrizeTensorSection h x v u := by
  intro x u v
  simp only [symmetrizeTensorSection_apply]
  rw [add_comm]

/-- Average an atlas field with the atlas reconstruction of its transposed
higher jets.  Both summands are independently in the genuine second-order
domain, so this definition does not assume regularity of an abstract
fiberwise symmetrization. -/
def symmetrizedAtlasField
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A) :
    FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ A.commonTerminalTime := by
  let U := atlasFieldOfHigher cov A u
  let Ut := atlasFieldOfHigher cov A (transposeHigherFamily cov A u)
  exact
    { toFun := fun t => (2⁻¹ : ℝ) • (U.toFun t + Ut.toFun t)
      slice_mem := by
        intro t ht
        exact (ConnectionLaplacianDomain cov).smul_mem (2⁻¹ : ℝ)
          ((ConnectionLaplacianDomain cov).add_mem
            (U.slice_mem t ht) (Ut.slice_mem t ht))
      timeDerivative := fun t =>
        (2⁻¹ : ℝ) • (U.timeDerivative t + Ut.timeDerivative t)
      hasTimeDerivative := by
        intro t ht x v w
        have hU := U.hasTimeDerivative t ht x v w
        have hUt := Ut.hasTimeDerivative t ht x v w
        have hadd := hU.add hUt
        simpa only [Pi.add_apply, add_apply,
          Pi.smul_apply, smul_apply, smul_eq_mul,
          mul_comm] using hadd.const_mul (2⁻¹ : ℝ) }

@[simp] theorem symmetrizedAtlasField_toFun
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A) (t : ℝ) :
    (symmetrizedAtlasField cov A u).toFun t =
      (2⁻¹ : ℝ) • ((atlasFieldOfHigher cov A u).toFun t +
        (atlasFieldOfHigher cov A
          (transposeHigherFamily cov A u)).toFun t) := rfl

@[simp] theorem symmetrizedAtlasField_timeDerivative
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A) (t : ℝ) :
    (symmetrizedAtlasField cov A u).timeDerivative t =
      (2⁻¹ : ℝ) •
        ((atlasFieldOfHigher cov A u).timeDerivative t +
          (atlasFieldOfHigher cov A
            (transposeHigherFamily cov A u)).timeDerivative t) := rfl

/-- The reconstructed averaged field is pointwise symmetric on its entire
genuine solution interval. -/
theorem symmetrizedAtlasField_isSymmetric
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A) (t : ℝ)
    (ht : t ∈ Ioc t₀ A.commonTerminalTime) :
    ∀ x : M, ∀ v w : TM x,
      (symmetrizedAtlasField cov A u).toFun t x v w =
        (symmetrizedAtlasField cov A u).toFun t x w v := by
  intro x v w
  simp only [symmetrizedAtlasField_toFun, Pi.smul_apply, Pi.add_apply,
    smul_apply, add_apply,
    smul_eq_mul]
  rw [atlasFieldOfHigher_transpose_toFun cov A u t ht x v w,
    atlasFieldOfHigher_transpose_toFun cov A u t ht x w v]
  ring

/-- Fiberwise symmetrization commutes with the actual finite-interval tensor
heat operator on reconstructed atlas fields. -/
theorem symmetrizedAtlasField_tensorHeatOperator
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A)
    (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime)
    (x : M) (v w : TM x) :
    (symmetrizedAtlasField cov A u).tensorHeatOperator cov t ht x v w =
      ((atlasFieldOfHigher cov A u).tensorHeatOperator cov t ht x v w +
        (atlasFieldOfHigher cov A u).tensorHeatOperator cov t ht x w v) / 2 := by
  let U := atlasFieldOfHigher cov A u
  let Ut := atlasFieldOfHigher cov A (transposeHigherFamily cov A u)
  have ht' : t ∈ Ioc t₀ A.commonTerminalTime := ⟨ht.1, ht.2.le⟩
  have heq : (Ut.slice cov t ht').1 = transposeTensorSection (U.slice cov t ht').1 := by
    funext y
    ext a c
    exact atlasFieldOfHigher_transpose_toFun cov A u t ht' y a c
  have hlap := connectionLaplacian_flip_of_mem_domain cov
    (U.slice cov t ht') (Ut.slice cov t ht') heq x v w
  have hlap' : connectionLaplacian cov (Ut.toFun t) x v w =
      connectionLaplacian cov (U.toFun t) x w v := by
    simpa only [FiniteClassicalTensorHeatField.slice] using hlap
  have htime := atlasFieldOfHigher_transpose_timeDerivative
    cov A u t ht x v w
  have hlinsum : connectionLaplacian cov
      ((symmetrizedAtlasField cov A u).toFun t) x =
      (2⁻¹ : ℝ) • (connectionLaplacian cov (U.toFun t) x +
        connectionLaplacian cov (Ut.toFun t) x) := by
    have hlinear : connectionLaplacian cov
        (↑((2⁻¹ : ℝ) • ((U.slice cov t ht') + (Ut.slice cov t ht')))) x =
        (2⁻¹ : ℝ) • (connectionLaplacian cov
          (↑(U.slice cov t ht')) x + connectionLaplacian cov
            (↑(Ut.slice cov t ht')) x) := by
      change connectionLaplacianLinearMapAt cov x
          ((2⁻¹ : ℝ) • ((U.slice cov t ht') + (Ut.slice cov t ht'))) = _
      rw [map_smul, map_add]
      rfl
    simpa only [Submodule.coe_smul, Submodule.coe_add,
      FiniteClassicalTensorHeatField.slice,
      symmetrizedAtlasField_toFun] using hlinear
  change ((symmetrizedAtlasField cov A u).timeDerivative t x -
      connectionLaplacian cov
        ((symmetrizedAtlasField cov A u).toFun t) x) v w = _
  rw [hlinsum]
  simp only [symmetrizedAtlasField_timeDerivative, Pi.smul_apply, Pi.add_apply,
    sub_apply, smul_apply, add_apply, smul_eq_mul]
  change (2⁻¹ : ℝ) * (U.timeDerivative t x v w +
      Ut.timeDerivative t x v w) -
      (2⁻¹ : ℝ) * (connectionLaplacian cov (U.toFun t) x v w +
        connectionLaplacian cov (Ut.toFun t) x v w) = _
  rw [htime, hlap']
  simp only [FiniteClassicalTensorHeatField.tensorHeatOperator_apply,
    sub_apply]
  ring

/-! ## Symmetric geometric data and well-posedness -/

/-- The concrete spatial datum reconstructs to a symmetric covariant
two-tensor. -/
def AtlasSpatialInitialData.IsSymmetric
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (D : AtlasSpatialInitialData cov A) : Prop :=
  ∀ x : M, ∀ v w : TM x,
    spatialInitialTensor cov A D x v w =
      spatialInitialTensor cov A D x w v

/-- The physical tensor represented by the atlas source is symmetric on the
actual solution cylinder. -/
def SourceSpace.IsSymmetric
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    {A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α}
    (f : SourceSpace cov A) : Prop :=
  ∀ (t : ℝ), t ∈ Ioo t₀ A.commonTerminalTime → ∀ x : M, ∀ v w : TM x,
    A.physicalAtlasSourceSlice cov f t x v w =
      A.physicalAtlasSourceSlice cov f t x w v

/-- Symmetrizing a reconstructed atlas field symmetrizes its initial trace.
The proof acts by the continuous fiberwise flip on the genuine trace limit. -/
theorem hasInitialTrace_symmetrizedAtlasField
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A) (u₀ : ∀ x : M, T₂ x)
    (hu : FiniteClassicalTensorHeatField.HasInitialTrace cov
      (atlasFieldOfHigher cov A u) u₀) :
    FiniteClassicalTensorHeatField.HasInitialTrace cov
      (symmetrizedAtlasField cov A u) (symmetrizeTensorSection u₀) := by
  intro x
  let U := atlasFieldOfHigher cov A u
  let idL : T₂ x →L[ℝ] T₂ x := ContinuousLinearMap.id ℝ (T₂ x)
  let flipL : T₂ x →L[ℝ] T₂ x :=
    _root_.CovariantDerivative.flipLastTwo (I := I) x
  let Sx : T₂ x →L[ℝ] T₂ x :=
    (2⁻¹ : ℝ) • (idL + flipL)
  have hmap : Tendsto (fun t : ℝ => Sx (U.toFun t x))
      (nhdsWithin t₀ (Ioc t₀ A.commonTerminalTime))
      (nhds (Sx (u₀ x))) :=
    Sx.continuous.continuousAt.tendsto.comp (hu x)
  have htarget : Sx (u₀ x) = symmetrizeTensorSection u₀ x := by
    ext v w
    simp [Sx, idL, flipL, symmetrizeTensorSection]
  rw [← htarget]
  apply hmap.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change Sx (U.toFun t x) = (symmetrizedAtlasField cov A u).toFun t x
  simp only [symmetrizedAtlasField_toFun, Sx, idL, flipL,
    smul_apply, add_apply, ContinuousLinearMap.id_apply]
  ext v w
  simp only [Pi.smul_apply, Pi.add_apply, smul_apply,
    add_apply, smul_eq_mul]
  rw [atlasFieldOfHigher_transpose_toFun cov A u t ht x v w]
  simp [U]

/-- For symmetric spatial data, the averaged field has the original (rather
than merely symmetrized) geometric initial trace. -/
theorem hasInitialTrace_symmetrizedAtlasField_spatial
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (D : AtlasSpatialInitialData cov A) (u : HigherCoefficientSpace cov A)
    (hD : D.IsSymmetric cov)
    (hu : FiniteClassicalTensorHeatField.HasInitialTrace cov
      (atlasFieldOfHigher cov A u) (spatialInitialTensor cov A D)) :
    FiniteClassicalTensorHeatField.HasInitialTrace cov
      (symmetrizedAtlasField cov A u) (spatialInitialTensor cov A D) := by
  have htrace := hasInitialTrace_symmetrizedAtlasField cov A u
    (spatialInitialTensor cov A D) hu
  have heq : symmetrizeTensorSection (spatialInitialTensor cov A D) =
      spatialInitialTensor cov A D := by
    funext x
    ext v w
    simp only [symmetrizeTensorSection_apply]
    rw [hD x w v]
    ring
  rwa [heq] at htrace

/-- For a symmetric physical source, the averaged field solves the same
intrinsic tensor heat equation. -/
theorem symmetrizedAtlasField_tensorHeatOperator_eq_source
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (u : HigherCoefficientSpace cov A) (f : SourceSpace cov A)
    (hf : f.IsSymmetric cov)
    (hu : ∀ (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime) (x : M),
      (atlasFieldOfHigher cov A u).tensorHeatOperator cov t ht x =
        A.physicalAtlasSourceSlice cov f t x)
    (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime) (x : M) :
    (symmetrizedAtlasField cov A u).tensorHeatOperator cov t ht x =
      A.physicalAtlasSourceSlice cov f t x := by
  ext v w
  rw [symmetrizedAtlasField_tensorHeatOperator cov A u t ht x v w,
    hu t ht x]
  change
    (A.physicalAtlasSourceSlice cov f t x v w +
      A.physicalAtlasSourceSlice cov f t x w v) / 2 = _
  rw [hf t ht x w v]
  ring

/-- The precise symmetric solution class used by the closed-manifold
theorem.  Its coefficient witness belongs to the already unique strong atlas
class, while its reconstructed geometric field is explicitly symmetrized. -/
def SymmetricAtlasSpatialClassicalSolution
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
  AtlasSpatialClassicalSolution cov Hlift D f u ∧
    FiniteClassicalTensorHeatField.HasInitialTrace cov
      (symmetrizedAtlasField cov A u) (spatialInitialTensor cov A D) ∧
    (∀ (t : ℝ), t ∈ Ioc t₀ A.commonTerminalTime → ∀ x : M, ∀ v w : TM x,
      (symmetrizedAtlasField cov A u).toFun t x v w =
        (symmetrizedAtlasField cov A u).toFun t x w v) ∧
    ∀ (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime) (x : M),
      (symmetrizedAtlasField cov A u).tensorHeatOperator cov t ht x =
        A.physicalAtlasSourceSlice cov f t x

/-- Existence and uniqueness in the symmetric atlas classical class.  The
solution field is the explicit geometric symmetrization of the unique ambient
covariant-two-tensor solution. -/
theorem existsUnique_symmetricAtlasSpatialClassicalSolution
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
    (hD : D.IsSymmetric cov) (hf : f.IsSymmetric cov) :
    ∃! u : HigherCoefficientSpace cov A,
      SymmetricAtlasSpatialClassicalSolution cov Hlift D f u := by
  obtain ⟨u, hu, huniq⟩ :=
    existsUnique_atlasSpatialClassicalSolution cov hunique Hlift D f
  refine ⟨u, ⟨hu, ?_, ?_, ?_⟩, ?_⟩
  · exact hasInitialTrace_symmetrizedAtlasField_spatial cov A D u hD hu.2.1
  · intro t ht x v w
    exact symmetrizedAtlasField_isSymmetric cov A u t ht x v w
  · intro t ht x
    exact symmetrizedAtlasField_tensorHeatOperator_eq_source
      cov A u f hf hu.2.2 t ht x
  · intro v hv
    exact huniq v hv.1

/-- The symmetric solution inherits the standard global finite-atlas
Schauder estimate from the unique ambient coefficient witness. -/
theorem norm_le_strongAtlasSchauderConstant_mul_symmetricData
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
    (hu : SymmetricAtlasSpatialClassicalSolution cov Hlift D f u) :
    ‖u‖ ≤ strongAtlasSchauderConstant cov Hlift *
      (spatialInitialSize cov A D + ‖f‖) := by
  exact norm_le_strongAtlasSchauderConstant_mul_data
    cov hunique Hlift D f u
      ((atlasSpatialClassicalSolution_iff_strong cov Hlift D f u).1 hu.1)

/-- **Linear parabolic well-posedness for symmetric two-tensors on a closed
Riemannian manifold.**

For a Levi-Civita background connection and `0 < α < 1`, this theorem
constructs a positive interval, a finite normalized atlas, and a strict
parametrix correction.  Every symmetric spatial `C²ᵃ` atlas datum and
symmetric parabolic `Cᵃ` atlas source have a unique symmetric classical
atlas solution.  Its genuine geometric field satisfies
`\partialₜ u - Δ u = f`, where `Δ` is the actual connection Laplacian,
and it obeys the standard global estimate
`\|u\|₂₊ᵃ ≤ C (\|u₀\|₂₊ᵃ + \|f\|ᵃ)`.

No atlas, Euclidean inverse, contraction, or other analytic solvability datum
is assumed; all are constructed from the closed background. -/
theorem exists_short_symmetric_tensorHeat_wellPosed
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
    (_hLevi : cov.IsLeviCivita)
    (b : Module.Basis (Fin d) ℝ E)
    (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ (S : ℝ) (_hS : t₀ < S) (_hST : S ≤ T)
      (A : FiniteTensorHeatParametrixAtlas
        (E := E) (I := I) (M := M) cov b t₀ S α)
      (Hlift : StrongCommutatorLift cov A),
      HasLocalZeroTraceUniqueness cov A ∧
        ∀ (D : AtlasSpatialInitialData cov A) (f : SourceSpace cov A),
          D.IsSymmetric cov → f.IsSymmetric cov →
          (∃! u : HigherCoefficientSpace cov A,
            SymmetricAtlasSpatialClassicalSolution cov Hlift D f u) ∧
          ∀ u : HigherCoefficientSpace cov A,
            SymmetricAtlasSpatialClassicalSolution cov Hlift D f u →
              ‖u‖ ≤ strongAtlasSchauderConstant cov Hlift *
                (spatialInitialSize cov A D + ‖f‖) := by
  obtain ⟨S, hS, hST, A, Hlift, hunique, _hwell⟩ :=
    exists_short_spatial_tensorHeat_wellPosed cov b hT hα hα1
  refine ⟨S, hS, hST, A, Hlift, hunique, ?_⟩
  intro D f hD hf
  refine ⟨existsUnique_symmetricAtlasSpatialClassicalSolution
    cov hunique Hlift D f hD hf, ?_⟩
  intro u hu
  exact norm_le_strongAtlasSchauderConstant_mul_symmetricData
    cov hunique Hlift D f u hu

end FiniteTensorHeatParametrixAtlas

end AnalyticPDE
end RicciFlow
