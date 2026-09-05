/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Recognition.Smale2
public import LeanPool.HopfProblem.Uniformization.SpecialPeriods1
import all LeanPool.HopfProblem.Foundations.LineBundleTransport
import all LeanPool.HopfProblem.Recognition.Smale1
import all LeanPool.HopfProblem.Recognition.Smale2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods1

/-!
# Hopf problem: recognition · smale 3

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private theorem Smale.NativeEuclideanEmbedding.finrank_tangent_add_normal {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) (x : M) :
    Module.finrank ℝ E + Module.finrank ℝ (e.normalFiber x) = e.ambientDimension := by
  calc
    Module.finrank ℝ E + Module.finrank ℝ (e.normalFiber x) =
        Module.finrank ℝ (e.tangentImage x) + Module.finrank ℝ (e.tangentImage x)ᗮ :=
      congrArg (fun n => n + Module.finrank ℝ (e.normalFiber x)) (e.finrank_tangentImage x).symm
    _ = Module.finrank ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
      (e.tangentImage x).finrank_add_finrank_orthogonal
    _ = e.ambientDimension := finrank_euclideanSpace_fin

private theorem Smale.NativeEuclideanEmbedding.tangentSpaceT2 {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (x : M) :
    T2Space (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (T2Space E)

attribute [local instance] Smale.NativeEuclideanEmbedding.tangentSpaceT2 in
private theorem Smale.NativeEuclideanEmbedding.tangentSpaceFiniteDimensional {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [FiniteDimensional ℝ E] (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

attribute [local instance] Smale.NativeEuclideanEmbedding.tangentSpaceT2
    Smale.NativeEuclideanEmbedding.tangentSpaceFiniteDimensional in
private def Smale.NativeEuclideanEmbedding.tangentImageEquiv {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) [FiniteDimensional ℝ E] (x : M) :
    TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] e.tangentImage x :=
  (LinearEquiv.ofInjective (mvfderiv 𝓘(ℝ, E) e.toFun x).toLinearMap
      (e.injective_mvfderiv x)).toContinuousLinearEquiv

attribute [local instance] Smale.NativeEuclideanEmbedding.tangentSpaceT2
    Smale.NativeEuclideanEmbedding.tangentSpaceFiniteDimensional in
private def Smale.NativeEuclideanEmbedding.tangentNormalEquiv {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) [FiniteDimensional ℝ E] (x : M) :
    (TangentSpace 𝓘(ℝ, E) x × e.normalFiber x) ≃L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
  ((LinearEquiv.prodCongr (e.tangentImageEquiv x).toLinearEquiv
          (LinearEquiv.refl ℝ (e.normalFiber x))).trans
      ((e.tangentImage x).prodEquivOfIsCompl (e.normalFiber x)
        (e.tangentImage x).isCompl_orthogonal)).toContinuousLinearEquiv

attribute [local instance] Smale.NativeEuclideanEmbedding.tangentSpaceT2
    Smale.NativeEuclideanEmbedding.tangentSpaceFiniteDimensional in
private theorem Smale.NativeEuclideanEmbedding.contMDiff_normalProjection {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] :
    ContMDiff 𝓘(ℝ, E)
      𝓘(ℝ,
        EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension))
      ∞ e.normalProjection := by
  have heq : e.normalProjection = fun x => 1 - e.tangentProjection x :=
    funext e.normalProjection_eq
  rw [heq]
  exact contMDiff_const.sub e.contMDiff_tangentProjection

private def NoExotic.projectionIntertwiner {R : Type*} [Ring R] (P Q : R) : R :=
  Q * P + (1 - Q) * (1 - P)

private theorem NoExotic.projectionIntertwiner_self {R : Type*} [Ring R] (P : R)
    (hP : IsIdempotentElem P) : projectionIntertwiner P P = 1 := by
  unfold projectionIntertwiner
  rw [hP, hP.one_sub]
  simpa only [add_sub_assoc] using add_sub_cancel_left P 1

private theorem NoExotic.projectionIntertwiner_intertwines {R : Type*} [Ring R] (P Q : R)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) :
    Q * projectionIntertwiner P Q = projectionIntertwiner P Q * P := by
  calc
    Q * projectionIntertwiner P Q = (Q * Q) * P + (Q * (1 - Q)) * (1 - P) := by
      simp only [projectionIntertwiner, mul_add, mul_assoc]
    _ = Q * P := by rw [hQ, hQ.mul_one_sub_self, MulZeroClass.zero_mul, add_zero]
    _ = Q * (P * P) + (1 - Q) * ((1 - P) * P) := by
      rw [hP, hP.one_sub_mul_self, MulZeroClass.mul_zero, add_zero]
    _ = projectionIntertwiner P Q * P := by simp only [projectionIntertwiner, add_mul, mul_assoc]

private theorem NoExotic.projectionIntertwiner_map_range {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (P Q : F →L[ℝ] F) (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hR : (projectionIntertwiner P Q).IsInvertible) :
    Submodule.map (projectionIntertwiner P Q).toLinearMap P.range = Q.range := by
  have hcomm := projectionIntertwiner_intertwines P Q hP hQ
  have hsurj : Function.Surjective (projectionIntertwiner P Q : F →L[ℝ] F) := by
    obtain ⟨r, hr⟩ := hR
    simpa only [← hr, ContinuousLinearEquiv.coe_coe] using r.surjective
  rw [← LinearMap.range_comp]
  have hlin :
    (projectionIntertwiner P Q).toLinearMap.comp P.toLinearMap =
      Q.toLinearMap.comp (projectionIntertwiner P Q).toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap hcomm.symm
  rw [hlin]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hsurj)

private noncomputable def NoExotic.invertibleOperatorEquiv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (A : F →L[ℝ] F) (hA : A.IsInvertible) : F ≃L[ℝ] F
    where
  toLinearEquiv :=
    { A.toLinearMap with
      invFun := A.inverse
      left_inv := hA.inverse_apply_self
      right_inv := hA.self_apply_inverse }
  continuous_toFun := A.continuous
  continuous_invFun := A.inverse.continuous

private noncomputable def NoExotic.projectionRangeEquiv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (P Q : F →L[ℝ] F) (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hR : (projectionIntertwiner P Q).IsInvertible) : P.range ≃L[ℝ] Q.range :=
  (invertibleOperatorEquiv (projectionIntertwiner P Q) hR).ofSubmodules P.range Q.range
    (projectionIntertwiner_map_range P Q hP hQ hR)

private theorem
    NoExotic.projectionRangeEquiv_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P Q : F →L[ℝ] F) (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hR : (projectionIntertwiner P Q).IsInvertible) (v : P.range) :
    (projectionRangeEquiv P Q hP hQ hR v : F) = projectionIntertwiner P Q v :=
  rfl

private theorem NoExotic.projectionRangeEquiv_symm_apply {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (P Q : F →L[ℝ] F) (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hR : (projectionIntertwiner P Q).IsInvertible) (v : Q.range) :
    ((projectionRangeEquiv P Q hP hQ hR).symm v : F) = (projectionIntertwiner P Q).inverse v :=
  rfl

private theorem NoExotic.projection_apply_range {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : F →L[ℝ] F) (hP : IsIdempotentElem P) (v : P.range) : P v = v := by
  obtain ⟨w, hw⟩ := v.property
  rw [← hw]
  exact congrArg (fun A : F →L[ℝ] F ↦ A w) hP

private def NoExotic.projectionTransportDomain {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M : Type*} (P : M → F →L[ℝ] F) (x₀ : M) : Set M :=
  {x | (projectionIntertwiner (P x₀) (P x)).IsInvertible}

private theorem NoExotic.contMDiff_projectionIntertwiner {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (P : M → F →L[ℝ] F) (hP : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) (x₀ : M) :
    ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ (fun x ↦ projectionIntertwiner (P x₀) (P x)) :=
  (hP.clm_comp contMDiff_const).add ((contMDiff_const.sub hP).clm_comp contMDiff_const)

private theorem NoExotic.isOpen_projectionTransportDomain {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (P : M → F →L[ℝ] F) (hP : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) (x₀ : M) :
    IsOpen (projectionTransportDomain P x₀) := by
  have hi : IsOpen {A : F →L[ℝ] F | A.IsInvertible} := ContinuousLinearEquiv.isOpen
  exact hi.preimage (contMDiff_projectionIntertwiner P hP x₀).continuous

private theorem NoExotic.mem_projectionTransportDomain {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {M : Type*} (P : M → F →L[ℝ] F) (hP : ∀ x, IsIdempotentElem (P x))
    (x₀ : M) : x₀ ∈ projectionTransportDomain P x₀ := by
  change (projectionIntertwiner (P x₀) (P x₀)).IsInvertible
  rw [projectionIntertwiner_self _ (hP x₀)]
  exact ⟨ContinuousLinearEquiv.refl ℝ F, rfl⟩

private theorem
    NoExotic.contMDiffOn_projectionIntertwiner_inverse {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (P : M → F →L[ℝ] F) (hP : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) (x₀ : M) :
    ContMDiffOn I 𝓘(ℝ, F →L[ℝ] F) ∞ (fun x ↦ (projectionIntertwiner (P x₀) (P x)).inverse)
      (projectionTransportDomain P x₀) := by
  intro x hx
  have hi := hx.contDiffAt_map_inverse (n := ∞)
  exact
    (ContDiffAt.comp_contMDiffAt (f := fun y ↦ projectionIntertwiner (P x₀) (P y)) (x := x) hi
        (contMDiff_projectionIntertwiner P hP x₀).contMDiffAt).contMDiffWithinAt

private noncomputable def
    NoExotic.ProjectionBundle.toCoordinates {F K : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K] {M : Type*} (P : M → F →L[ℝ] F)
    (q : ∀ x, (P x).range ≃L[ℝ] K) (x₀ x : M) : (P x).range →L[ℝ] K :=
  (q x₀).toContinuousLinearMap.comp
    ((P x₀).rangeRestrict.comp
      ((NoExotic.projectionIntertwiner (P x₀) (P x)).inverse.comp (P x).range.subtypeL))

private noncomputable def
    NoExotic.ProjectionBundle.fromCoordinates {F K : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K] {M : Type*} (P : M → F →L[ℝ] F)
    (q : ∀ x, (P x).range ≃L[ℝ] K) (x₀ x : M) : K →L[ℝ] (P x).range :=
  (P x).rangeRestrict.comp
    ((NoExotic.projectionIntertwiner (P x₀) (P x)).comp
      ((P x₀).range.subtypeL.comp (q x₀).symm.toContinuousLinearMap))

private noncomputable def
    NoExotic.ProjectionBundle.coordinateEquiv {F K : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K] {M : Type*} (P : M → F →L[ℝ] F)
    (hP : ∀ x, IsIdempotentElem (P x)) (q : ∀ x, (P x).range ≃L[ℝ] K) (x₀ x : M)
    (hx : x ∈ NoExotic.projectionTransportDomain P x₀) : (P x).range ≃L[ℝ] K :=
  (NoExotic.projectionRangeEquiv (P x₀) (P x) (hP x₀) (hP x) hx).symm.trans (q x₀)

private theorem NoExotic.ProjectionBundle.toCoordinates_eq {F K : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K] {M : Type*} (P : M → F →L[ℝ] F)
    (hP : ∀ x, IsIdempotentElem (P x)) (q : ∀ x, (P x).range ≃L[ℝ] K) (x₀ x : M)
    (hx : x ∈ NoExotic.projectionTransportDomain P x₀) :
    toCoordinates P q x₀ x = (coordinateEquiv P hP q x₀ x hx).toContinuousLinearMap := by
  ext v
  change
    q x₀ ((P x₀).rangeRestrict ((NoExotic.projectionIntertwiner (P x₀) (P x)).inverse v)) =
      q x₀ ((NoExotic.projectionRangeEquiv (P x₀) (P x) (hP x₀) (hP x) hx).symm v)
  congr 1
  apply Subtype.ext
  change P x₀ ((NoExotic.projectionIntertwiner (P x₀) (P x)).inverse v) = _
  rw [← NoExotic.projectionRangeEquiv_symm_apply (P x₀) (P x) (hP x₀) (hP x) hx v]
  exact NoExotic.projection_apply_range (P x₀) (hP x₀) _

private theorem NoExotic.ProjectionBundle.fromCoordinates_eq {F K : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K] {M : Type*} (P : M → F →L[ℝ] F)
    (hP : ∀ x, IsIdempotentElem (P x)) (q : ∀ x, (P x).range ≃L[ℝ] K) (x₀ x : M)
    (hx : x ∈ NoExotic.projectionTransportDomain P x₀) :
    fromCoordinates P q x₀ x = (coordinateEquiv P hP q x₀ x hx).symm.toContinuousLinearMap := by
  ext v
  change
    P x (NoExotic.projectionIntertwiner (P x₀) (P x) ((q x₀).symm v)) =
      (NoExotic.projectionRangeEquiv (P x₀) (P x) (hP x₀) (hP x) hx ((q x₀).symm v) : F)
  rw [← NoExotic.projectionRangeEquiv_apply (P x₀) (P x) (hP x₀) (hP x) hx ((q x₀).symm v)]
  exact NoExotic.projection_apply_range (P x) (hP x) _

private theorem NoExotic.ProjectionBundle.fromCoordinates_toCoordinates {F K : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K] {M : Type*}
    (P : M → F →L[ℝ] F) (hP : ∀ x, IsIdempotentElem (P x)) (q : ∀ x, (P x).range ≃L[ℝ] K)
    (x₀ x : M) (hx : x ∈ NoExotic.projectionTransportDomain P x₀) (v : (P x).range) :
    fromCoordinates P q x₀ x (toCoordinates P q x₀ x v) = v := by
  rw [toCoordinates_eq P hP q x₀ x hx, fromCoordinates_eq P hP q x₀ x hx]
  exact (coordinateEquiv P hP q x₀ x hx).symm_apply_apply v

private theorem NoExotic.ProjectionBundle.toCoordinates_fromCoordinates {F K : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K] {M : Type*}
    (P : M → F →L[ℝ] F) (hP : ∀ x, IsIdempotentElem (P x)) (q : ∀ x, (P x).range ≃L[ℝ] K)
    (x₀ x : M) (hx : x ∈ NoExotic.projectionTransportDomain P x₀) (v : K) :
    toCoordinates P q x₀ x (fromCoordinates P q x₀ x v) = v := by
  rw [toCoordinates_eq P hP q x₀ x hx, fromCoordinates_eq P hP q x₀ x hx]
  exact (coordinateEquiv P hP q x₀ x hx).apply_symm_apply v

private noncomputable def NoExotic.ProjectionBundle.ambientFromCoordinates {F K : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K] {M : Type*}
    (P : M → F →L[ℝ] F) (q : ∀ x, (P x).range ≃L[ℝ] K) (x₀ x : M) : K →L[ℝ] F :=
  (P x).comp
    ((NoExotic.projectionIntertwiner (P x₀) (P x)).comp
      ((P x₀).range.subtypeL.comp (q x₀).symm.toContinuousLinearMap))

private theorem NoExotic.ProjectionBundle.contMDiff_ambientFromCoordinates {F K : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K]
    {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M] (P : M → F →L[ℝ] F)
    (q : ∀ x, (P x).range ≃L[ℝ] K) (hs : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) (x₀ : M) :
    ContMDiff I 𝓘(ℝ, K →L[ℝ] F) ∞ (ambientFromCoordinates P q x₀) :=
  hs.clm_comp ((NoExotic.contMDiff_projectionIntertwiner P hs x₀).clm_comp contMDiff_const)

private noncomputable def
    NoExotic.ProjectionBundle.pretrivialization {F K : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup K] [NormedSpace ℝ K] {B H M : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
    [TopologicalSpace M] [ChartedSpace H M] (P : M → F →L[ℝ] F) (hP : ∀ x, IsIdempotentElem (P x))
    (q : ∀ x, (P x).range ≃L[ℝ] K) (hs : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) (x₀ : M) :
    Bundle.Pretrivialization K (Bundle.TotalSpace.proj (F := K) (E := fun x ↦ (P x).range))
    where
  toFun p := ⟨p.1, toCoordinates P q x₀ p.1 p.2⟩
  invFun p := ⟨p.1, fromCoordinates P q x₀ p.1 p.2⟩
  source := Bundle.TotalSpace.proj ⁻¹' NoExotic.projectionTransportDomain P x₀
  target := NoExotic.projectionTransportDomain P x₀ ×ˢ Set.univ
  map_source' := fun _ h ↦ ⟨h, Set.mem_univ _⟩
  map_target' := fun _ h ↦ h.1
  left_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [Bundle.TotalSpace.mk_inj]
    exact fromCoordinates_toCoordinates P hP q x₀ x hx v
  right_inv' := by
    rintro ⟨x, v⟩ ⟨hx, _⟩
    simp only [Prod.mk_right_inj]
    exact toCoordinates_fromCoordinates P hP q x₀ x hx v
  open_target := (NoExotic.isOpen_projectionTransportDomain P hs x₀).prod isOpen_univ
  baseSet := NoExotic.projectionTransportDomain P x₀
  open_baseSet := NoExotic.isOpen_projectionTransportDomain P hs x₀
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

private instance
    NoExotic.ProjectionBundle.pretrivialization_isLinear {F K : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup K] [NormedSpace ℝ K] {B H M : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
    [TopologicalSpace M] [ChartedSpace H M] (P : M → F →L[ℝ] F) (hP : ∀ x, IsIdempotentElem (P x))
    (q : ∀ x, (P x).range ≃L[ℝ] K) (hs : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) (x₀ : M) :
    (pretrivialization P hP q hs x₀).IsLinear ℝ where
  linear x _ := (toCoordinates P q x₀ x).toLinearMap.isLinear

private theorem NoExotic.ProjectionBundle.pretrivialization_symm_apply {F K : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup K]
    [NormedSpace ℝ K] {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (P : M → F →L[ℝ] F) (hP : ∀ x, IsIdempotentElem (P x)) (q : ∀ x, (P x).range ≃L[ℝ] K)
    (hs : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) (x₀ x : M)
    (hx : x ∈ NoExotic.projectionTransportDomain P x₀) (v : K) :
    (pretrivialization P hP q hs x₀).symm x v = fromCoordinates P q x₀ x v := by
  rw [Bundle.Pretrivialization.symm_apply]
  · rfl
  · exact hx

private noncomputable def
    NoExotic.ProjectionBundle.coordinateChange {F K : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup K] [NormedSpace ℝ K] {M : Type*} (P : M → F →L[ℝ] F)
    (q : ∀ x, (P x).range ≃L[ℝ] K) (x₀ x₁ x : M) : K →L[ℝ] K :=
  (q x₁).toContinuousLinearMap.comp
    ((P x₁).rangeRestrict.comp
      ((NoExotic.projectionIntertwiner (P x₁) (P x)).inverse.comp
        ((P x).comp
          ((NoExotic.projectionIntertwiner (P x₀) (P x)).comp
            ((P x₀).range.subtypeL.comp (q x₀).symm.toContinuousLinearMap)))))

private theorem NoExotic.ProjectionBundle.contMDiffOn_coordinateChange {F K : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup K]
    [NormedSpace ℝ K] {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (P : M → F →L[ℝ] F) (q : ∀ x, (P x).range ≃L[ℝ] K) (hs : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P)
    (x₀ x₁ : M) :
    ContMDiffOn I 𝓘(ℝ, K →L[ℝ] K) ∞ (coordinateChange P q x₀ x₁)
      (NoExotic.projectionTransportDomain P x₀ ∩ NoExotic.projectionTransportDomain P x₁) := by
  have hi :=
    (NoExotic.contMDiffOn_projectionIntertwiner_inverse P hs x₁).mono
      (Set.inter_subset_right (s := NoExotic.projectionTransportDomain P x₀))
  exact
    contMDiffOn_const.clm_comp
      (contMDiffOn_const.clm_comp
        (hi.clm_comp
          (hs.contMDiffOn.clm_comp
            ((NoExotic.contMDiff_projectionIntertwiner P hs x₀).contMDiffOn.clm_comp
              contMDiffOn_const))))

private theorem
    NoExotic.ProjectionBundle.coordinateChange_apply {F K : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup K] [NormedSpace ℝ K] {B H M : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
    [TopologicalSpace M] [ChartedSpace H M] (P : M → F →L[ℝ] F) (hP : ∀ x, IsIdempotentElem (P x))
    (q : ∀ x, (P x).range ≃L[ℝ] K) (hs : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) (x₀ x₁ x : M)
    (hx : x ∈ NoExotic.projectionTransportDomain P x₀ ∩ NoExotic.projectionTransportDomain P x₁)
    (v : K) :
    coordinateChange P q x₀ x₁ x v =
      ((pretrivialization P hP q hs x₁) ⟨x, (pretrivialization P hP q hs x₀).symm x v⟩).2 := by
  rw [pretrivialization_symm_apply P hP q hs x₀ x hx.1]
  rfl

private noncomputable def
    NoExotic.ProjectionBundle.vectorPrebundle {F K : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup K] [NormedSpace ℝ K] {B H M : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
    [TopologicalSpace M] [ChartedSpace H M] (P : M → F →L[ℝ] F) (hP : ∀ x, IsIdempotentElem (P x))
    (q : ∀ x, (P x).range ≃L[ℝ] K) (hs : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) :
    VectorPrebundle ℝ K (fun x ↦ (P x).range)
    where
  pretrivializationAtlas := Set.range (pretrivialization P hP q hs)
  pretrivialization_linear' := by
    rintro _ ⟨x₀, rfl⟩
    infer_instance
  pretrivializationAt := pretrivialization P hP q hs
  mem_base_pretrivializationAt := NoExotic.mem_projectionTransportDomain P hP
  pretrivialization_mem_atlas x := ⟨x, rfl⟩
  exists_coordChange := by
    rintro _ ⟨x₀, rfl⟩ _ ⟨x₁, rfl⟩
    exact
      ⟨coordinateChange P q x₀ x₁, (contMDiffOn_coordinateChange P q hs x₀ x₁).continuousOn,
        coordinateChange_apply P hP q hs x₀ x₁⟩
  totalSpaceMk_isInducing := by
    intro x
    change Topology.IsInducing (fun v : (P x).range ↦ (x, toCoordinates P q x x v))
    have hx := NoExotic.mem_projectionTransportDomain P hP x
    rw [toCoordinates_eq P hP q x x hx]
    exact
      Topology.isInducing_const_prod.mpr (coordinateEquiv P hP q x x hx).toHomeomorph.isInducing

private instance NoExotic.ProjectionBundle.vectorPrebundle_isContMDiff {F K : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup K]
    [NormedSpace ℝ K] {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (P : M → F →L[ℝ] F) (hP : ∀ x, IsIdempotentElem (P x)) (q : ∀ x, (P x).range ≃L[ℝ] K)
    (hs : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P) : (vectorPrebundle P hP q hs).IsContMDiff I ∞ where
  exists_contMDiffCoordChange := by
    rintro _ ⟨x₀, rfl⟩ _ ⟨x₁, rfl⟩
    exact
      ⟨coordinateChange P q x₀ x₁, contMDiffOn_coordinateChange P q hs x₀ x₁,
        coordinateChange_apply P hP q hs x₀ x₁⟩

private abbrev Smale.NativeEuclideanEmbedding.NormalSpace {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) (x : M) :=
  ↥(e.normalProjection x).range

private abbrev Smale.NativeEuclideanEmbedding.NormalModel {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) :=
  EuclideanSpace ℝ (Fin (e.ambientDimension - Module.finrank ℝ E))

private noncomputable def Smale.NativeEuclideanEmbedding.normalSpaceEquiv {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) (x : M) : e.NormalSpace x ≃L[ℝ] e.normalFiber x :=
  ContinuousLinearEquiv.ofEq _ _ (e.range_normalProjection x)

private theorem
    Smale.NativeEuclideanEmbedding.finrank_normalSpace {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) (x : M) :
    Module.finrank ℝ (e.NormalSpace x) = e.ambientDimension - Module.finrank ℝ E := by
  have h := e.finrank_tangent_add_normal x
  rw [(e.normalSpaceEquiv x).toLinearEquiv.finrank_eq]
  omega

private noncomputable def Smale.NativeEuclideanEmbedding.normalModelEquiv {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) (x : M) : e.NormalSpace x ≃L[ℝ] e.NormalModel :=
  (LinearEquiv.ofFinrankEq (e.NormalSpace x) e.NormalModel
      (by
        rw [e.finrank_normalSpace x]
        exact finrank_euclideanSpace_fin.symm)).toContinuousLinearEquiv

private noncomputable def Smale.NativeEuclideanEmbedding.normalPrebundle {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (e : Smale.NativeEuclideanEmbedding E M) [IsManifold 𝓘(ℝ, E) ∞ M] :
    VectorPrebundle ℝ e.NormalModel e.NormalSpace :=
  NoExotic.ProjectionBundle.vectorPrebundle e.normalProjection e.normalProjection_idempotent
    e.normalModelEquiv e.contMDiff_normalProjection

private instance Smale.NativeEuclideanEmbedding.normalPrebundle_isContMDiff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (e : Smale.NativeEuclideanEmbedding E M) [IsManifold 𝓘(ℝ, E) ∞ M] :
    e.normalPrebundle.IsContMDiff 𝓘(ℝ, E) ∞ :=
  NoExotic.ProjectionBundle.vectorPrebundle_isContMDiff e.normalProjection
    e.normalProjection_idempotent e.normalModelEquiv e.contMDiff_normalProjection

private abbrev Smale.NativeEuclideanEmbedding.NormalBundle {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) :=
  Bundle.TotalSpace e.NormalModel e.NormalSpace

private noncomputable instance Smale.NativeEuclideanEmbedding.normalBundleTopology {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (e : Smale.NativeEuclideanEmbedding E M) [IsManifold 𝓘(ℝ, E) ∞ M] :
    TopologicalSpace e.NormalBundle :=
  e.normalPrebundle.totalSpaceTopology

private noncomputable instance Smale.NativeEuclideanEmbedding.normalFiberBundle {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (e : Smale.NativeEuclideanEmbedding E M) [IsManifold 𝓘(ℝ, E) ∞ M] :
    FiberBundle e.NormalModel e.NormalSpace :=
  e.normalPrebundle.toFiberBundle

private instance
    Smale.NativeEuclideanEmbedding.normalVectorBundle {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) [IsManifold 𝓘(ℝ, E) ∞ M] :
    VectorBundle ℝ e.NormalModel e.NormalSpace :=
  e.normalPrebundle.toVectorBundle

private instance Smale.NativeEuclideanEmbedding.normalContMDiffVectorBundle {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (e : Smale.NativeEuclideanEmbedding E M) [IsManifold 𝓘(ℝ, E) ∞ M] :
    ContMDiffVectorBundle ∞ e.NormalModel e.NormalSpace 𝓘(ℝ, E) :=
  e.normalPrebundle.contMDiffVectorBundle 𝓘(ℝ, E)

private def Smale.NativeEuclideanEmbedding.normalVector {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) (v : e.NormalBundle) :
    EuclideanSpace ℝ (Fin e.ambientDimension) :=
  v.2

private theorem
    Smale.NativeEuclideanEmbedding.contMDiff_normalVector {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (e : Smale.NativeEuclideanEmbedding E M) :
    ContMDiff ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞ e.normalVector := by
  intro z
  have hp :
    ContMDiffAt ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓘(ℝ, E)) ∞ (fun v : e.NormalBundle ↦ v.proj)
      z :=
    Bundle.contMDiffAt_proj e.NormalSpace
  have hc :
    ContMDiffAt ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) 𝓘(ℝ, e.NormalModel) ∞
      (fun v : e.NormalBundle ↦
        NoExotic.ProjectionBundle.toCoordinates e.normalProjection e.normalModelEquiv z.1 v.1 v.2)
      z := by
    have h :=
      (Bundle.contMDiffAt_totalSpace (IB := 𝓘(ℝ, E)) (IM := (𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel))
            (n := ∞) (f := id) (x₀ := z)).mp
        contMDiffAt_id
    exact h.2
  have hf :=
    ((NoExotic.ProjectionBundle.contMDiff_ambientFromCoordinates e.normalProjection
              e.normalModelEquiv e.contMDiff_normalProjection z.1).contMDiffAt.comp
          z hp).clm_apply
      hc
  have heq :
    e.normalVector =ᶠ[𝓝 z]
      (fun v : e.NormalBundle ↦
        NoExotic.ProjectionBundle.ambientFromCoordinates e.normalProjection e.normalModelEquiv z.1
          v.1
          (NoExotic.ProjectionBundle.toCoordinates e.normalProjection e.normalModelEquiv z.1 v.1
            v.2)) := by
    have ho :=
      NoExotic.isOpen_projectionTransportDomain e.normalProjection e.contMDiff_normalProjection
        z.1
    have hn :=
      hp.continuousAt
        (ho.mem_nhds
          (NoExotic.mem_projectionTransportDomain e.normalProjection e.normalProjection_idempotent
            z.1))
    filter_upwards [hn] with v hv
    exact
      (congrArg Subtype.val
          (NoExotic.ProjectionBundle.fromCoordinates_toCoordinates e.normalProjection
            e.normalProjection_idempotent e.normalModelEquiv z.1 v.1 hv v.2)).symm
  exact heq.contMDiffAt_iff.mpr hf

private def Smale.NativeEuclideanEmbedding.normalDisplacement {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) (v : e.NormalBundle) :
    EuclideanSpace ℝ (Fin e.ambientDimension) :=
  e.toFun v.proj + e.normalVector v

private theorem Smale.NativeEuclideanEmbedding.contMDiff_normalDisplacement {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : Smale.NativeEuclideanEmbedding E M) :
    ContMDiff ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
      e.normalDisplacement :=
  (e.smooth.comp (Bundle.contMDiff_proj e.NormalSpace)).add e.contMDiff_normalVector

private theorem Smale.NativeEuclideanEmbedding.normalDisplacement_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) (x : M) :
    e.normalDisplacement (Bundle.zeroSection e.NormalModel e.NormalSpace x) = e.toFun x := by
  simp [normalDisplacement, normalVector, Bundle.zeroSection]

private noncomputable def Smale.NativeEuclideanEmbedding.localNormalDisplacement {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) (x₀ : M) (p : M × e.NormalModel) :
    EuclideanSpace ℝ (Fin e.ambientDimension) :=
  e.toFun p.1 +
    NoExotic.ProjectionBundle.ambientFromCoordinates e.normalProjection e.normalModelEquiv x₀ p.1
      p.2

private theorem Smale.NativeEuclideanEmbedding.contMDiff_localNormalDisplacement {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : Smale.NativeEuclideanEmbedding E M)
    (x₀ : M) :
    ContMDiff ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
      (e.localNormalDisplacement x₀) :=
  (e.smooth.comp contMDiff_fst).add
    (((NoExotic.ProjectionBundle.contMDiff_ambientFromCoordinates e.normalProjection
              e.normalModelEquiv e.contMDiff_normalProjection x₀).comp
          contMDiff_fst).clm_apply
      contMDiff_snd)

private theorem Smale.NativeEuclideanEmbedding.localNormalDisplacement_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) (x₀ x : M) :
    e.localNormalDisplacement x₀ (x, 0) = e.toFun x := by simp [localNormalDisplacement]

private theorem Smale.NativeEuclideanEmbedding.ambientNormalCoordinates_self {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) (x : M) (v : e.NormalModel) :
    NoExotic.ProjectionBundle.ambientFromCoordinates e.normalProjection e.normalModelEquiv x x v =
      ((e.normalModelEquiv x).symm v : EuclideanSpace ℝ (Fin e.ambientDimension)) := by
  change
    e.normalProjection x
        (NoExotic.projectionIntertwiner (e.normalProjection x) (e.normalProjection x)
          ((e.normalModelEquiv x).symm v)) =
      _
  rw [NoExotic.projectionIntertwiner_self _ (e.normalProjection_idempotent x)]
  exact NoExotic.projection_apply_range (e.normalProjection x) (e.normalProjection_idempotent x) _

private noncomputable def Smale.NativeEuclideanEmbedding.normalLinearSplitting {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (e : Smale.NativeEuclideanEmbedding E M) (x : M) :
    (TangentSpace (𝓘(ℝ, E)) x × e.NormalModel) ≃L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
  ((ContinuousLinearEquiv.refl ℝ (TangentSpace (𝓘(ℝ, E)) x)).prodCongr
        ((e.normalModelEquiv x).symm.trans (e.normalSpaceEquiv x))).trans
    (e.tangentNormalEquiv x)

private theorem Smale.NativeEuclideanEmbedding.mvfderiv_localNormalDisplacement_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : Smale.NativeEuclideanEmbedding E M) (x : M) :
    mvfderiv ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (e.localNormalDisplacement x) (x, 0) =
      (e.normalLinearSplitting x).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  have hd := (e.contMDiff_localNormalDisplacement x).mdifferentiable (by simp) (x, 0)
  have hprod :=
    mfderiv_prod_eq_add_apply (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, e.NormalModel)) (I'' :=
      𝓡 e.ambientDimension) (v := v) hd
  have hleft : (fun y : M ↦ e.localNormalDisplacement x (y, 0)) = e.toFun :=
    funext (e.localNormalDisplacement_zero x)
  let C : e.NormalModel →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
    (e.normalProjection x).range.subtypeL.comp (e.normalModelEquiv x).symm.toContinuousLinearMap
  have hright :
    (fun y : e.NormalModel ↦ e.localNormalDisplacement x (x, y)) = (fun y ↦ e.toFun x + C y) := by
    funext y
    exact congrArg (e.toFun x + ·) (e.ambientNormalCoordinates_self x y)
  have hC :
    mfderiv 𝓘(ℝ, e.NormalModel) (𝓡 e.ambientDimension) (fun y ↦ e.toFun x + C y)
        (0 : e.NormalModel) =
      C :=
    (C.hasFDerivAt.const_add (e.toFun x)).hasMFDerivAt.mfderiv
  change
    mfderiv ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension)
        (e.localNormalDisplacement x) (x, 0) v =
      _
  rw [hprod, hleft, hright, hC]
  rfl

private theorem Smale.NativeEuclideanEmbedding.localNormalDisplacement_derivative_isInvertible
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (e : Smale.NativeEuclideanEmbedding E M) (x : M) :
    (mvfderiv ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (e.localNormalDisplacement x)
        (x, 0)).IsInvertible :=
  ⟨e.normalLinearSplitting x, (e.mvfderiv_localNormalDisplacement_zero x).symm⟩

private theorem Smale.NativeEuclideanEmbedding.localNormalDisplacement_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) (x₀ : M) (p : M × e.NormalModel) :
    e.localNormalDisplacement x₀ p =
      e.normalDisplacement
        ⟨p.1,
          NoExotic.ProjectionBundle.fromCoordinates e.normalProjection e.normalModelEquiv x₀ p.1
            p.2⟩ :=
  rfl

private theorem
    Smale.NativeEuclideanEmbedding.isLocalDiffeomorphAt_localNormalDisplacement {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : Smale.NativeEuclideanEmbedding E M) (x : M) :
    IsLocalDiffeomorphAt ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
      (e.localNormalDisplacement x) (x, 0) := by
  exact
    NoExotic.isLocalDiffeomorphAt_of_invertible_mvfderiv (e.contMDiff_localNormalDisplacement x)
      (e.localNormalDisplacement_derivative_isInvertible x)

private noncomputable def Smale.NativeEuclideanEmbedding.normalChartPartialDiffeomorph {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : Smale.NativeEuclideanEmbedding E M) (x : M) :
    PartialDiffeomorph ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel))
      e.NormalBundle (M × e.NormalModel) ∞
    where
  toPartialEquiv :=
    (FiberBundle.trivializationAt e.NormalModel e.NormalSpace
        x).toOpenPartialHomeomorph.toPartialEquiv
  open_source := (FiberBundle.trivializationAt e.NormalModel e.NormalSpace x).open_source
  open_target := (FiberBundle.trivializationAt e.NormalModel e.NormalSpace x).open_target
  contMDiffOn_toFun := (FiberBundle.trivializationAt e.NormalModel e.NormalSpace x).contMDiffOn
  contMDiffOn_invFun :=
    (FiberBundle.trivializationAt e.NormalModel e.NormalSpace x).contMDiffOn_symm

private theorem Smale.NativeEuclideanEmbedding.normalChartPartialDiffeomorph_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : Smale.NativeEuclideanEmbedding E M) (x : M) :
    e.normalChartPartialDiffeomorph x (Bundle.zeroSection e.NormalModel e.NormalSpace x) =
      (x, 0) := by
  change
    (x, NoExotic.ProjectionBundle.toCoordinates e.normalProjection e.normalModelEquiv x x 0) =
      (x, 0)
  rw [map_zero]

private theorem Smale.NativeEuclideanEmbedding.normalChart_source_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : Smale.NativeEuclideanEmbedding E M) (x : M) :
    Bundle.zeroSection e.NormalModel e.NormalSpace x ∈
      (e.normalChartPartialDiffeomorph x).source := by
  change x ∈ NoExotic.projectionTransportDomain e.normalProjection x
  exact NoExotic.mem_projectionTransportDomain e.normalProjection e.normalProjection_idempotent x

private theorem Smale.NativeEuclideanEmbedding.localNormalDisplacement_chart_apply {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : Smale.NativeEuclideanEmbedding E M) (x : M)
    (v : e.NormalBundle) (hv : v ∈ (e.normalChartPartialDiffeomorph x).source) :
    e.localNormalDisplacement x (e.normalChartPartialDiffeomorph x v) = e.normalDisplacement v := by
  have hbase : v.proj ∈ NoExotic.projectionTransportDomain e.normalProjection x := hv
  have hback :=
    NoExotic.ProjectionBundle.fromCoordinates_toCoordinates e.normalProjection
      e.normalProjection_idempotent e.normalModelEquiv x v.proj hbase v.2
  rw [e.localNormalDisplacement_eq]
  change
    e.normalDisplacement
        ⟨v.proj,
          NoExotic.ProjectionBundle.fromCoordinates e.normalProjection e.normalModelEquiv x v.proj
            (NoExotic.ProjectionBundle.toCoordinates e.normalProjection e.normalModelEquiv x
              v.proj v.2)⟩ =
      _
  rw [hback]

private theorem
    Smale.NativeEuclideanEmbedding.isLocalDiffeomorphAt_normalDisplacement_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : Smale.NativeEuclideanEmbedding E M) (x : M) :
    IsLocalDiffeomorphAt ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
      e.normalDisplacement (Bundle.zeroSection e.NormalModel e.NormalSpace x) := by
  obtain ⟨d, hd, heq⟩ := e.isLocalDiffeomorphAt_localNormalDisplacement x
  let c := e.normalChartPartialDiffeomorph x
  have hc : Bundle.zeroSection e.NormalModel e.NormalSpace x ∈ c.source :=
    e.normalChart_source_zero x
  have hcd : c (Bundle.zeroSection e.NormalModel e.NormalSpace x) ∈ d.source := by
    rw [e.normalChartPartialDiffeomorph_zero]
    exact hd
  refine ⟨c.trans d, ⟨hc, hcd⟩, ?_⟩
  intro v hv
  exact (e.localNormalDisplacement_chart_apply x v hv.1).symm.trans (heq hv.2)

private def Smale.NativeEuclideanEmbedding.regularNormalLocus {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (e : Smale.NativeEuclideanEmbedding E M) : Set e.NormalBundle :=
  {v |
    IsLocalDiffeomorphAt ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
      e.normalDisplacement v}

private theorem Smale.NativeEuclideanEmbedding.isOpen_regularNormalLocus {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : Smale.NativeEuclideanEmbedding E M) :
    IsOpen e.regularNormalLocus := by
  rw [isOpen_iff_mem_nhds]
  rintro v ⟨φ, hv, heq⟩
  exact Filter.mem_of_superset (φ.open_source.mem_nhds hv) (fun w hw ↦ ⟨φ, hw, heq⟩)

private theorem Smale.NativeEuclideanEmbedding.normalDisplacement_injOn_zeroSection {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) :
    Set.InjOn e.normalDisplacement (Set.range (Bundle.zeroSection e.NormalModel e.NormalSpace)) :=
  by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
  have hxy : e.toFun x = e.toFun y := by simpa only [e.normalDisplacement_zero] using h
  exact
    congrArg (Bundle.zeroSection e.NormalModel e.NormalSpace) (e.closedEmbedding.injective hxy)

private theorem
    Smale.NativeEuclideanEmbedding.normalDisplacement_locally_injective_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : Smale.NativeEuclideanEmbedding E M) (x : M) :
    ∃ U ∈ 𝓝 (Bundle.zeroSection e.NormalModel e.NormalSpace x),
      Set.InjOn e.normalDisplacement U := by
  obtain ⟨φ, hx, heq⟩ := e.isLocalDiffeomorphAt_normalDisplacement_zero x
  exact ⟨φ.source, φ.open_source.mem_nhds hx, heq.injOn_iff.mpr φ.toPartialEquiv.injOn⟩

private theorem Smale.NativeEuclideanEmbedding.exists_injective_normalNeighborhood {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : Smale.NativeEuclideanEmbedding E M)
    [CompactSpace M] :
    ∃ U : Set e.NormalBundle,
      IsOpen U ∧
        Set.range (Bundle.zeroSection e.NormalModel e.NormalSpace) ⊆ U ∧
          Set.InjOn e.normalDisplacement U ∧
            IsLocalDiffeomorphOn ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
              e.normalDisplacement U := by
  have hc : IsCompact (Set.range (Bundle.zeroSection e.NormalModel e.NormalSpace)) :=
    isCompact_range (Bundle.Trivialization.continuous_zeroSection ℝ)
  obtain ⟨V, hV, hsV, hInj⟩ :=
    e.normalDisplacement_injOn_zeroSection.exists_isOpen_superset hc
      (fun v _ ↦ e.contMDiff_normalDisplacement.continuous.continuousAt)
      (by rintro _ ⟨x, rfl⟩; exact e.normalDisplacement_locally_injective_zero x)
  refine
    ⟨V ∩ e.regularNormalLocus, hV.inter e.isOpen_regularNormalLocus, ?_,
      hInj.mono Set.inter_subset_left, ?_⟩
  · intro v hv
    refine ⟨hsV hv, ?_⟩
    obtain ⟨x, rfl⟩ := hv
    exact e.isLocalDiffeomorphAt_normalDisplacement_zero x
  · intro v
    exact v.property.2

private theorem Smale.NativeEuclideanEmbedding.isOpen_normalNeighborhood_image {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : Smale.NativeEuclideanEmbedding E M)
    {U : Set e.NormalBundle} (hU : IsOpen U)
    (hloc :
      IsLocalDiffeomorphOn ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
        e.normalDisplacement U) :
    IsOpen (e.normalDisplacement '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨v, hv, rfl⟩
  rw [← hloc.isLocalHomeomorphOn.map_nhds_eq hv]
  exact Filter.image_mem_map (hU.mem_nhds hv)

private theorem
    Smale.NativeEuclideanEmbedding.normalBundle_nonempty {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) [Nonempty M] : Nonempty e.NormalBundle :=
  ⟨Bundle.zeroSection e.NormalModel e.NormalSpace (Classical.choice ‹Nonempty M›)⟩

attribute [local instance] Smale.NativeEuclideanEmbedding.normalBundle_nonempty in
private noncomputable def Smale.NativeEuclideanEmbedding.normalNeighborhoodEquiv {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) [Nonempty M] {U : Set e.NormalBundle}
    (hinj : Set.InjOn e.normalDisplacement U) :
    PartialEquiv e.NormalBundle (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
  hinj.toPartialEquiv e.normalDisplacement U

attribute [local instance] Smale.NativeEuclideanEmbedding.normalBundle_nonempty in
private theorem Smale.NativeEuclideanEmbedding.contMDiffAt_normalNeighborhood_inverse {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : Smale.NativeEuclideanEmbedding E M)
    [Nonempty M] {U : Set e.NormalBundle} (hU : IsOpen U)
    (hinj : Set.InjOn e.normalDisplacement U)
    (hloc :
      IsLocalDiffeomorphOn ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
        e.normalDisplacement U)
    {y : EuclideanSpace ℝ (Fin e.ambientDimension)}
    (hy : y ∈ (e.normalNeighborhoodEquiv hinj).target) :
    ContMDiffAt (𝓡 e.ambientDimension) ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) ∞
      (e.normalNeighborhoodEquiv hinj).symm y := by
  let p := e.normalNeighborhoodEquiv hinj
  have hx : p.symm y ∈ U := p.map_target hy
  obtain ⟨φ, hφx, heq⟩ := hloc ⟨p.symm y, hx⟩
  have hφxy : φ (p.symm y) = y := (heq hφx).symm.trans (p.right_inv hy)
  have hφy : y ∈ φ.target := hφxy ▸ φ.map_source' hφx
  have hφyx : φ.symm y = p.symm y := by
    calc
      φ.symm y = φ.symm (φ (p.symm y)) := congrArg φ.symm hφxy.symm
      _ = p.symm y := φ.left_inv' hφx
  have hg : ContMDiffAt (𝓡 e.ambientDimension) ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) ∞ φ.symm y :=
    φ.contMDiffOn_invFun.contMDiffAt (φ.open_target.mem_nhds hφy)
  have hNU : U ∈ 𝓝 (φ.symm y) := by
    rw [hφyx]
    exact hU.mem_nhds hx
  have hfg : p.symm =ᶠ[𝓝 y] φ.symm := by
    filter_upwards [φ.open_target.mem_nhds hφy, hg.continuousAt hNU] with z hz hzU
    have hfz : e.normalDisplacement (φ.symm z) = z :=
      (heq (φ.map_target' hz)).trans (φ.right_inv' hz)
    exact (congrArg p.symm hfz.symm).trans (p.left_inv hzU)
  exact hfg.contMDiffAt_iff.mpr hg

attribute [local instance] Smale.NativeEuclideanEmbedding.normalBundle_nonempty in
private noncomputable def Smale.NativeEuclideanEmbedding.normalNeighborhoodPartialDiffeomorph
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (e : Smale.NativeEuclideanEmbedding E M) [Nonempty M] {U : Set e.NormalBundle} (hU : IsOpen U)
    (hinj : Set.InjOn e.normalDisplacement U)
    (hloc :
      IsLocalDiffeomorphOn ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
        e.normalDisplacement U) :
    PartialDiffeomorph ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) e.NormalBundle
      (EuclideanSpace ℝ (Fin e.ambientDimension)) ∞
    where
  toPartialEquiv := e.normalNeighborhoodEquiv hinj
  open_source := hU
  open_target := e.isOpen_normalNeighborhood_image hU hloc
  contMDiffOn_toFun := e.contMDiff_normalDisplacement.contMDiffOn
  contMDiffOn_invFun := fun _ hy ↦
    (e.contMDiffAt_normalNeighborhood_inverse hU hinj hloc hy).contMDiffWithinAt

attribute [local instance] Smale.NativeEuclideanEmbedding.normalBundle_nonempty in
private theorem Smale.NativeEuclideanEmbedding.exists_tubularNeighborhood {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : Smale.NativeEuclideanEmbedding E M)
    [Nonempty M] [CompactSpace M] :
    ∃ Φ :
      PartialDiffeomorph ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension)
        e.NormalBundle (EuclideanSpace ℝ (Fin e.ambientDimension)) ∞,
      Set.range (Bundle.zeroSection e.NormalModel e.NormalSpace) ⊆ Φ.source ∧
        (Φ : e.NormalBundle → EuclideanSpace ℝ (Fin e.ambientDimension)) = e.normalDisplacement ∧
          Set.range e.toFun ⊆ Φ.target := by
  obtain ⟨U, hU, hzero, hinj, hloc⟩ := e.exists_injective_normalNeighborhood
  let Φ := e.normalNeighborhoodPartialDiffeomorph hU hinj hloc
  refine ⟨Φ, hzero, rfl, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx : Bundle.zeroSection e.NormalModel e.NormalSpace x ∈ Φ.source := hzero ⟨x, rfl⟩
  have hy := Φ.map_source' hx
  simpa only [Φ, normalNeighborhoodPartialDiffeomorph, normalNeighborhoodEquiv,
    Set.InjOn.toPartialEquiv, Set.BijOn.toPartialEquiv, e.normalDisplacement_zero] using hy

private structure
    Smale.NativeEuclideanEmbedding.SmoothRetraction {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (e : Smale.NativeEuclideanEmbedding E M) where
  domain : Set (EuclideanSpace ℝ (Fin e.ambientDimension))
  open_domain : IsOpen domain
  contains : Set.range e.toFun ⊆ domain
  toFun : EuclideanSpace ℝ (Fin e.ambientDimension) → M
  smooth : ContMDiffOn (𝓡 e.ambientDimension) 𝓘(ℝ, E) ∞ toFun domain
  retract : ∀ x, toFun (e.toFun x) = x

private theorem Smale.NativeEuclideanEmbedding.nonempty_smoothRetraction {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (e : Smale.NativeEuclideanEmbedding E M)
    [CompactSpace M] [Nonempty M] : Nonempty e.SmoothRetraction := by
  obtain ⟨Φ, hzero, hΦ, hrange⟩ := e.exists_tubularNeighborhood
  refine
    ⟨⟨Φ.target, Φ.open_target, hrange, fun y => (Φ.symm y).proj,
        (Bundle.contMDiff_proj e.NormalSpace).comp_contMDiffOn Φ.contMDiffOn_invFun, ?_⟩⟩
  intro x
  have hx : Bundle.zeroSection e.NormalModel e.NormalSpace x ∈ Φ.source := hzero ⟨x, rfl⟩
  have heq : Φ (Bundle.zeroSection e.NormalModel e.NormalSpace x) = e.toFun x := by
    rw [hΦ, e.normalDisplacement_zero]
  have hinv := Φ.left_inv' hx
  rw [heq] at hinv
  exact congrArg Bundle.TotalSpace.proj hinv

private theorem Smale.NativeEuclideanEmbedding.SmoothRetraction.mfderiv_retract_comp {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) (x : M) :
    (mfderiv (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun (e.toFun x)).comp
        (mfderiv 𝓘(ℝ, E) (𝓡 e.ambientDimension) e.toFun x) =
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E) x) := by
  have hr : r.toFun ∘ e.toFun = id := funext r.retract
  have hd :=
    mfderiv_comp x
      ((r.smooth.contMDiffAt (r.open_domain.mem_nhds (r.contains ⟨x, rfl⟩))).mdifferentiableAt
        (by simp))
      (e.smooth.mdifferentiableAt (by simp))
  rw [hr, mfderiv_id] at hd
  exact hd.symm

private theorem
    Smale.NativeEuclideanEmbedding.SmoothRetraction.embedding_derivative_retract {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {x : M}
    {v : EuclideanSpace ℝ (Fin e.ambientDimension)} (hv : v ∈ e.tangentImage x) :
    (mvfderiv 𝓘(ℝ, E) e.toFun x)
        ((mfderiv (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun (e.toFun x)) v) =
      v := by
  obtain ⟨w, rfl⟩ := hv
  have h := congrArg (fun A => A w) (r.mfderiv_retract_comp x)
  exact congrArg (mvfderiv 𝓘(ℝ, E) e.toFun x) h

private theorem Smale.NativeEuclideanEmbedding.contMDiff_embeddedField {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (e : Smale.NativeEuclideanEmbedding E M)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ContMDiff 𝓘(ℝ, E) (𝓡 e.ambientDimension) ∞ (fun x => mvfderiv 𝓘(ℝ, E) e.toFun x (V x)) := by
  have ht := (e.smooth.contMDiff_tangentMap (m := ∞) (by simp)).comp hV
  have hp :=
    (contMDiff_tangentBundleModelSpaceHomeomorph (I := 𝓡 e.ambientDimension) (n := ∞)).comp ht
  rw [← modelWithCornersSelf_prod] at hp
  convert contDiff_snd.contMDiff.comp hp using 1 <;> rfl

private def
    Smale.RegularLevel.levelDisplacement {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {b : ℝ}
    {e : Smale.NativeEuclideanEmbedding E M} (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (z : { x : M // f x = b } × ℝ) : EuclideanSpace ℝ (Fin e.ambientDimension) :=
  e.toFun z.1 + z.2 • mvfderiv 𝓘(ℝ, E) e.toFun z.1 (V z.1)

private def Smale.RegularLevel.transverseCoordinateDomain {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {b : ℝ}
    {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) : Set ({ x : M // f x = b } × ℝ) :=
  levelDisplacement V ⁻¹' r.domain

private def Smale.RegularLevel.transverseCoordinates {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {b : ℝ}
    {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) : ({ x : M // f x = b } × ℝ) → M :=
  r.toFun ∘ levelDisplacement V

private theorem Smale.RegularLevel.transverseCoordinates_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {b : ℝ}
    {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (x : { x : M // f x = b }) :
    transverseCoordinates r V (x, 0) = x := by
  simp only [transverseCoordinates, Function.comp_apply, levelDisplacement, zero_smul, add_zero]
  exact r.retract x

private theorem Smale.RegularLevel.zero_mem_transverseCoordinateDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {b : ℝ} {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (x : { x : M // f x = b }) :
    (x, 0) ∈ transverseCoordinateDomain r V := by
  change e.toFun x + (0 : ℝ) • _ ∈ r.domain
  simp only [zero_smul, add_zero]
  exact r.contains ⟨x, rfl⟩

private theorem Smale.RegularLevel.contMDiff_levelDisplacement {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} {e : Smale.NativeEuclideanEmbedding E M}
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    letI := chartedSpace hf hreg
    ContMDiff (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) (𝓡 e.ambientDimension) ∞
      (levelDisplacement (e := e) (f := f) (b := b) V) := by
  let _ := chartedSpace hf hreg
  have hi :
    ContMDiff (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun z : { x : M // f x = b } × ℝ => (z.1 : M)) :=
    (Smale.RegularLevel.contMDiff_inclusion hf hreg).comp contMDiff_fst
  have hfirst := e.smooth.comp hi
  have hfield := (e.contMDiff_embeddedField hV).comp hi
  have htime :
    ContMDiff (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (Prod.snd : { x : M // f x = b } × ℝ → ℝ) :=
    contMDiff_snd
  exact hfirst.add (htime.smul hfield)

private theorem
    Smale.RegularLevel.isOpen_transverseCoordinateDomain {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} {e : Smale.NativeEuclideanEmbedding E M}
    (r : e.SmoothRetraction) (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    IsOpen (transverseCoordinateDomain (f := f) (b := b) r V) := by
  let _ := chartedSpace hf hreg
  exact r.open_domain.preimage (contMDiff_levelDisplacement (e := e) V hf hreg hV).continuous

private theorem
    Smale.RegularLevel.contMDiffOn_transverseCoordinates {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} {e : Smale.NativeEuclideanEmbedding E M}
    (r : e.SmoothRetraction) (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    letI := chartedSpace hf hreg
    ContMDiffOn (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (transverseCoordinates r V)
      (transverseCoordinateDomain (f := f) (b := b) r V) := by
  let _ := chartedSpace hf hreg
  exact
    r.smooth.comp (contMDiff_levelDisplacement (e := e) V hf hreg hV).contMDiffOn (fun _ hz => hz)

private theorem Smale.RegularLevel.mfderiv_transverseCoordinates_time_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {b : ℝ} {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (x : { x : M // f x = b }) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => transverseCoordinates r V (x, t)) 0 =
      (ContinuousLinearMap.id ℝ ℝ).smulRight (V x) := by
  let A := mvfderiv 𝓘(ℝ, E) e.toFun (x : M) (V x)
  let line : ℝ → EuclideanSpace ℝ (Fin e.ambientDimension) := fun t => e.toFun x + t • A
  have hline : HasFDerivAt line ((ContinuousLinearMap.id ℝ ℝ).smulRight A) 0 :=
    ((ContinuousLinearMap.id ℝ ℝ).smulRight A).hasFDerivAt.const_add (e.toFun x)
  have hzero : line 0 = e.toFun x := by simp [line]
  have hr : MDifferentiableAt (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun (line 0) := by
    rw [hzero]
    exact
      (r.smooth.contMDiffAt (r.open_domain.mem_nhds (r.contains ⟨x, rfl⟩))).mdifferentiableAt
        (by simp)
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (r.toFun ∘ line) 0 = _
  rw [mfderiv_comp 0 hr hline.differentiableAt.mdifferentiableAt, mfderiv_eq_fderiv, hline.fderiv,
    hzero]
  apply ContinuousLinearMap.ext
  intro t
  change ℝ at t
  let R : EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ] E :=
    mfderiv (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun (e.toFun x)
  change R (t • A) = t • (V x : E)
  rw [map_smul]
  congr 1
  exact congrArg (fun L => L (V x)) (r.mfderiv_retract_comp (x : M))

private theorem
    Smale.RegularLevel.mfderiv_transverseCoordinates_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ} {e : Smale.NativeEuclideanEmbedding E M}
    (r : e.SmoothRetraction) (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (x : { x : M // f x = b }) :
    letI := chartedSpace hf hreg
    mfderiv (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (transverseCoordinates r V) (x, 0) =
      transverseTangentMap hf hreg x (V x) := by
  let _ := chartedSpace hf hreg
  have hs :=
    (contMDiffOn_transverseCoordinates r V hf hreg hV).contMDiffAt
      ((isOpen_transverseCoordinateDomain r V hf hreg hV).mem_nhds
        (zero_mem_transverseCoordinateDomain r V x))
  have hbase : (fun y : { x : M // f x = b } => transverseCoordinates r V (y, 0)) = Subtype.val :=
    funext (transverseCoordinates_zero r V)
  apply ContinuousLinearMap.ext
  intro w
  rw [mfderiv_prod_eq_add_apply (hs.mdifferentiableAt (by simp)), hbase,
    mfderiv_transverseCoordinates_time_zero r V x]
  rfl

private theorem Smale.RegularLevel.isLocalDiffeomorphAt_transverseCoordinates_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ}
    {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (x : { x : M // f x = b }) (hunit : mvfderiv 𝓘(ℝ, E) f (x : M) (V x) = 1) :
    letI := chartedSpace hf hreg
    IsLocalDiffeomorphAt (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (transverseCoordinates r V)
      (x, 0) := by
  let _ := chartedSpace hf hreg
  let _ := isManifold hf hreg
  have hs := contMDiffOn_transverseCoordinates r V hf hreg hV
  have hi :
    (mfderiv (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (transverseCoordinates r V)
        (x, 0)).IsInvertible := by
    rw [mfderiv_transverseCoordinates_zero r V hf hreg hV x]
    let A := transverseTangentMap hf hreg x (V x)
    exact
      ⟨(LinearEquiv.ofBijective A.toLinearMap
            (bijective_transverseTangentMap hf hreg x (V x) hunit)).toContinuousLinearEquiv,
        rfl⟩
  exact
    Smale.isLocalDiffeomorphAt_between_manifolds
      (isOpen_transverseCoordinateDomain r V hf hreg hV)
      (zero_mem_transverseCoordinateDomain r V x) hs hi

private theorem Smale.RegularLevel.hasDerivAt_height_transverseCoordinates_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {b : ℝ}
    {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (x : { x : M // f x = b }) (hunit : mvfderiv 𝓘(ℝ, E) f (x : M) (V x) = 1) :
    HasDerivAt (fun t : ℝ => f (transverseCoordinates r V (x, t))) 1 0 := by
  let _ := chartedSpace hf hreg
  have hs :=
    (contMDiffOn_transverseCoordinates r V hf hreg hV).contMDiffAt
      ((isOpen_transverseCoordinateDomain r V hf hreg hV).mem_nhds
        (zero_mem_transverseCoordinateDomain r V x))
  have hpair : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => (x, t)) 0 :=
    contMDiffAt_const.prodMk contMDiffAt_id
  have hcurve := ((hs.comp 0 hpair).mdifferentiableAt (by simp)).hasMFDerivAt
  change
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => transverseCoordinates r V (x, t)) 0
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => transverseCoordinates r V (x, t)) 0) at hcurve
  rw [mfderiv_transverseCoordinates_time_zero r V x] at hcurve
  have hc := (hf.mdifferentiableAt (by simp)).hasMFDerivAt.comp 0 hcurve
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasMFDerivAt_iff_hasFDerivAt.mp
  apply hc.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro t
  change ℝ at t
  let L : E →L[ℝ] ℝ := mvfderiv 𝓘(ℝ, E) f (x : M)
  have hd : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (transverseCoordinates r V (x, 0)) : E →L[ℝ] ℝ) = L := by
    rw [transverseCoordinates_zero r V x]
    rfl
  change
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (transverseCoordinates r V (x, 0)) : E →L[ℝ] ℝ) (t • (V x : E)) =
      t • (1 : ℝ)
  exact
    (congrArg (fun T : E →L[ℝ] ℝ => T (t • (V x : E))) hd).trans
      ((L.map_smul t (V x)).trans (congrArg (fun a : ℝ => t • a) hunit))

private theorem
    Smale.DiskFraming.starProjection_orthogonal_inf_eq_sub {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {U V : Submodule ℝ F} (h : U ≤ V) :
    (Uᗮ ⊓ V).starProjection = V.starProjection - U.starProjection := by
  ext x
  change (Uᗮ ⊓ V).starProjection x = V.starProjection x - U.starProjection x
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · refine ⟨?_, V.sub_mem (V.starProjection_apply_mem x) (h (U.starProjection_apply_mem x))⟩
    rw [← U.ker_starProjection]
    change U.starProjection (V.starProjection x - U.starProjection x) = 0
    rw [map_sub]
    have hc : U.starProjection (V.starProjection x) = U.starProjection x :=
      congrArg (fun A : F →L[ℝ] F => A x) (Submodule.starProjection_comp_starProjection_of_le h)
    rw [hc, Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x), sub_self]
  · have h₁ : x - V.starProjection x ∈ (Uᗮ ⊓ V)ᗮ :=
      Submodule.orthogonal_le inf_le_right (V.sub_starProjection_mem_orthogonal x)
    have h₂ : U.starProjection x ∈ (Uᗮ ⊓ V)ᗮ :=
      Submodule.orthogonal_le inf_le_left
        (U.le_orthogonal_orthogonal (U.starProjection_apply_mem x))
    convert (Uᗮ ⊓ V)ᗮ.add_mem h₁ h₂ using 1
    abel

private def Smale.NativeEuclideanEmbedding.diskTangentImage {E M D : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] (e : Smale.NativeEuclideanEmbedding E M) (f : D → M) (x : D) :
    Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
  (fderiv ℝ (e.toFun ∘ f) x).range

private def Smale.NativeEuclideanEmbedding.diskNormalSpace {E M D : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] (e : Smale.NativeEuclideanEmbedding E M) (f : D → M) (x : D) :
    Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
  (e.diskTangentImage f x)ᗮ ⊓ e.tangentImage (f x)

private theorem Smale.NativeEuclideanEmbedding.fderiv_comp_eq {E M D : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] (e : Smale.NativeEuclideanEmbedding E M) {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) (x : D) :
    fderiv ℝ (e.toFun ∘ f) x =
      (mvfderiv 𝓘(ℝ, E) e.toFun (f x)).comp (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x) := by
  rw [← mfderiv_eq_fderiv,
    mfderiv_comp x (e.smooth.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  rfl

private theorem
    Smale.NativeEuclideanEmbedding.diskTangentImage_le {E M D : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] (e : Smale.NativeEuclideanEmbedding E M) {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) (x : D) :
    e.diskTangentImage f x ≤ e.tangentImage (f x) := by
  rw [diskTangentImage, e.fderiv_comp_eq hf x]
  exact LinearMap.range_comp_le_range _ _

private theorem Smale.NativeEuclideanEmbedding.injective_fderiv_comp {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] (e : Smale.NativeEuclideanEmbedding E M)
    {f : D → M} (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {x : D}
    (hi : Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) :
    Function.Injective (fderiv ℝ (e.toFun ∘ f) x) := by
  rw [e.fderiv_comp_eq hf x]
  exact (e.injective_mvfderiv (f x)).comp hi

private theorem Smale.NativeEuclideanEmbedding.finrank_diskTangent_add_normal {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] (e : Smale.NativeEuclideanEmbedding E M)
    {f : D → M} (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {x : D}
    (hi : Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) :
    Module.finrank ℝ D + Module.finrank ℝ (e.diskNormalSpace f x) = Module.finrank ℝ E := by
  have hd : Module.finrank ℝ (e.diskTangentImage f x) = Module.finrank ℝ D :=
    LinearMap.finrank_range_of_inj (e.injective_fderiv_comp hf hi)
  calc
    Module.finrank ℝ D + Module.finrank ℝ (e.diskNormalSpace f x) =
        Module.finrank ℝ (e.diskTangentImage f x) + Module.finrank ℝ (e.diskNormalSpace f x) :=
      congrArg (fun n => n + Module.finrank ℝ (e.diskNormalSpace f x)) hd.symm
    _ = Module.finrank ℝ (e.tangentImage (f x)) :=
      (Submodule.finrank_add_inf_finrank_orthogonal (e.diskTangentImage_le hf x))
    _ = Module.finrank ℝ E := e.finrank_tangentImage (f x)

private def
    Smale.NativeEuclideanEmbedding.diskNormalProjection {E M D : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] (e : Smale.NativeEuclideanEmbedding E M)
    (f : D → M) (x : D) :
    EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
  e.tangentProjection (f x) - NoExotic.gramProjection (fderiv ℝ (e.toFun ∘ f) x)

private theorem Smale.NativeEuclideanEmbedding.diskNormalProjection_eq {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
    (e : Smale.NativeEuclideanEmbedding E M) {f : D → M} (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    {x : D} (hi : Function.Injective (fderiv ℝ (e.toFun ∘ f) x)) :
    e.diskNormalProjection f x = (e.diskNormalSpace f x).starProjection := by
  rw [diskNormalProjection, NoExotic.gramProjection_eq_starProjection _ hi]
  exact (Smale.DiskFraming.starProjection_orthogonal_inf_eq_sub (e.diskTangentImage_le hf x)).symm

private theorem Smale.NativeEuclideanEmbedding.contDiffOn_diskNormalProjection {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D] (e : Smale.NativeEuclideanEmbedding E M) {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) :
    ContDiffOn ℝ ∞ (e.diskNormalProjection f)
      {x | Function.Injective (fderiv ℝ (e.toFun ∘ f) x)} := by
  have hs : ContDiff ℝ ∞ (e.toFun ∘ f) := (e.smooth.comp hf).contDiff
  have hd : ContDiff ℝ ∞ (fderiv ℝ (e.toFun ∘ f)) := (contDiff_infty_iff_fderiv.mp hs).2
  have hT : ContDiff ℝ ∞ (fun x => e.tangentProjection (f x)) :=
    (e.contMDiff_tangentProjection.comp hf).contDiff
  intro x hx
  have hp : ContDiffAt ℝ ∞ (e.diskNormalProjection f) x :=
    hT.contDiffAt.sub (NoExotic.contMDiffAt_gramProjection hd.contMDiff.contMDiffAt hx).contDiffAt
  exact hp.contDiffWithinAt

private theorem Smale.NativeEuclideanEmbedding.exists_open_diskNormalProjection {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D] (e : Smale.NativeEuclideanEmbedding E M) {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {K : Set D}
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) :
    ∃ U : Set D,
      IsOpen U ∧
        K ⊆ U ∧
          ContDiffOn ℝ ∞ (e.diskNormalProjection f) U ∧
            ∀ x ∈ U, e.diskNormalProjection f x = (e.diskNormalSpace f x).starProjection := by
  have hs : ContDiff ℝ ∞ (e.toFun ∘ f) := (e.smooth.comp hf).contDiff
  have hd : ContDiff ℝ ∞ (fderiv ℝ (e.toFun ∘ f)) := (contDiff_infty_iff_fderiv.mp hs).2
  refine
    ⟨{x | Function.Injective (fderiv ℝ (e.toFun ∘ f) x)},
      ContinuousLinearMap.isOpen_injective.preimage hd.continuous, fun x hx =>
      e.injective_fderiv_comp hf (hi x hx), e.contDiffOn_diskNormalProjection hf, ?_⟩
  exact fun _ hx => e.diskNormalProjection_eq hf hx

private structure Smale.DiskFraming.SmoothRangeTransportOn {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Set E)
    (P Q : E → F →L[ℝ] F) where
  toFun : E → F →L[ℝ] F
  neighborhood : Set E
  open_neighborhood : IsOpen neighborhood
  contains : K ⊆ neighborhood
  smooth : ContDiffOn ℝ ∞ toFun neighborhood
  invertible : ∀ x ∈ K, (toFun x).IsInvertible
  intertwines : ∀ x ∈ K, Q x * toFun x = toFun x * P x

private def Smale.DiskFraming.SmoothRangeTransportOn.refl {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Set E) (P : E → F →L[ℝ] F) :
    Smale.DiskFraming.SmoothRangeTransportOn K P P
    where
  toFun _ := 1
  neighborhood := Set.univ
  open_neighborhood := isOpen_univ
  contains := Set.subset_univ _
  smooth := contDiffOn_const
  invertible _ _ := ⟨ContinuousLinearEquiv.refl ℝ F, rfl⟩
  intertwines _ _ := by rw [mul_one, one_mul]

private def Smale.DiskFraming.SmoothRangeTransportOn.trans {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E} {P Q R : E → F →L[ℝ] F}
    (a : Smale.DiskFraming.SmoothRangeTransportOn K P Q)
    (b : Smale.DiskFraming.SmoothRangeTransportOn K Q R) :
    Smale.DiskFraming.SmoothRangeTransportOn K P R
    where
  toFun x := b.toFun x * a.toFun x
  neighborhood := a.neighborhood ∩ b.neighborhood
  open_neighborhood := a.open_neighborhood.inter b.open_neighborhood
  contains := fun _ hx => ⟨a.contains hx, b.contains hx⟩
  smooth := (b.smooth.mono Set.inter_subset_right).clm_comp (a.smooth.mono Set.inter_subset_left)
  invertible x hx := (b.invertible x hx).comp (a.invertible x hx)
  intertwines x
    hx := by
    calc
      R x * (b.toFun x * a.toFun x) = (R x * b.toFun x) * a.toFun x := (mul_assoc _ _ _).symm
      _ = (b.toFun x * Q x) * a.toFun x := by rw [b.intertwines x hx]
      _ = b.toFun x * (Q x * a.toFun x) := (mul_assoc _ _ _)
      _ = b.toFun x * (a.toFun x * P x) := by rw [a.intertwines x hx]
      _ = (b.toFun x * a.toFun x) * P x := (mul_assoc _ _ _).symm

private def Smale.DiskFraming.SmoothRangeTransportOn.symm {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E} {P Q : E → F →L[ℝ] F}
    [CompleteSpace F] (a : Smale.DiskFraming.SmoothRangeTransportOn K P Q) :
    Smale.DiskFraming.SmoothRangeTransportOn K Q P
    where
  toFun x := (a.toFun x).inverse
  neighborhood := a.neighborhood ∩ {x | (a.toFun x).IsInvertible}
  open_neighborhood :=
    a.smooth.continuousOn.isOpen_inter_preimage a.open_neighborhood ContinuousLinearEquiv.isOpen
  contains := fun x hx => ⟨a.contains hx, a.invertible x hx⟩
  smooth := by
    intro x hx
    exact
      (hx.2.contDiffAt_map_inverse.comp x
          (a.smooth.contDiffAt (a.open_neighborhood.mem_nhds hx.1))).contDiffWithinAt
  invertible x hx := (a.invertible x hx).inverse
  intertwines x
    hx := by
    apply ContinuousLinearMap.ext
    intro v
    change P x ((a.toFun x).inverse v) = (a.toFun x).inverse (Q x v)
    apply (a.invertible x hx).injective
    rw [(a.invertible x hx).self_apply_inverse]
    have h := congrArg (fun L : F →L[ℝ] F => L ((a.toFun x).inverse v)) (a.intertwines x hx)
    change Q x (a.toFun x ((a.toFun x).inverse v)) = a.toFun x (P x ((a.toFun x).inverse v)) at h
    rw [(a.invertible x hx).self_apply_inverse] at h
    exact h.symm

private theorem
    Smale.DiskFraming.SmoothRangeTransportOn.map_range {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E} {P Q : E → F →L[ℝ] F}
    (a : Smale.DiskFraming.SmoothRangeTransportOn K P Q) (x : E) (hx : x ∈ K) :
    Submodule.map (a.toFun x).toLinearMap (P x).range = (Q x).range := by
  rw [← LinearMap.range_comp]
  have hlin :
    (a.toFun x).toLinearMap.comp (P x).toLinearMap =
      (Q x).toLinearMap.comp (a.toFun x).toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap (a.intertwines x hx).symm
  rw [hlin]
  exact
    LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (a.invertible x hx).surjective)

private def
    Smale.DiskFraming.SmoothRangeTransportOn.ofProjections {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E} {P Q : E → F →L[ℝ] F}
    (hP : ∀ x ∈ K, IsIdempotentElem (P x)) (hQ : ∀ x ∈ K, IsIdempotentElem (Q x)) {U V : Set E}
    (hU : IsOpen U) (hV : IsOpen V) (hKU : K ⊆ U) (hKV : K ⊆ V) (hsP : ContDiffOn ℝ ∞ P U)
    (hsQ : ContDiffOn ℝ ∞ Q V)
    (hinv : ∀ x ∈ K, (NoExotic.projectionIntertwiner (P x) (Q x)).IsInvertible) :
    Smale.DiskFraming.SmoothRangeTransportOn K P Q
    where
  toFun x := NoExotic.projectionIntertwiner (P x) (Q x)
  neighborhood := U ∩ V
  open_neighborhood := hU.inter hV
  contains := fun _ hx => ⟨hKU hx, hKV hx⟩
  smooth :=
    ((hsQ.mono Set.inter_subset_right).clm_comp (hsP.mono Set.inter_subset_left)).add
      ((contDiffOn_const.sub (hsQ.mono Set.inter_subset_right)).clm_comp
        (contDiffOn_const.sub (hsP.mono Set.inter_subset_left)))
  invertible := hinv
  intertwines x hx := NoExotic.projectionIntertwiner_intertwines (P x) (Q x) (hP x hx) (hQ x hx)

private theorem
    NoExotic.isOpen_forall_compact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace Y] {R : X → Y → Prop} (ho : IsOpen {p : X × Y | R p.1 p.2}) :
    IsOpen {x | ∀ y, R x y} := by
  have hclosed := isClosedMap_fst_of_compactSpace _ ho.isClosed_compl
  have heq : {x | ∀ y, R x y} = (Prod.fst '' {p : X × Y | ¬R p.1 p.2})ᶜ := by
    ext x
    constructor
    · rintro h ⟨⟨x', y⟩, hn, he⟩
      change x' = x at he
      subst x'
      exact hn (h y)
    · intro h y
      by_contra hn
      exact h ⟨(x, y), hn, rfl⟩
  rw [heq]
  exact hclosed.isOpen_compl

private def NoExotic.homotopyTransportDomain {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M : Type*} {T : Type*} (P : T → M → F →L[ℝ] F) (s : T) : Set T :=
  {t | ∀ x, (projectionIntertwiner (P s x) (P t x)).IsInvertible}

private theorem
    NoExotic.mem_homotopyTransportDomain {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M : Type*} {T : Type*} (P : T → M → F →L[ℝ] F) (hP : ∀ t x, IsIdempotentElem (P t x))
    (s : T) : s ∈ homotopyTransportDomain P s := by
  intro x
  rw [projectionIntertwiner_self _ (hP s x)]
  exact ⟨ContinuousLinearEquiv.refl ℝ F, rfl⟩

private theorem NoExotic.isOpen_continuousHomotopyTransportDomain {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {M T : Type*} [TopologicalSpace M] [CompactSpace M]
    [TopologicalSpace T] (P : T → M → F →L[ℝ] F) (hc : Continuous (fun p : T × M ↦ P p.1 p.2))
    (s : T) : IsOpen (homotopyTransportDomain P s) := by
  have hp : Continuous (fun p : T × M ↦ P s p.2) :=
    hc.comp (continuous_const.prodMk continuous_snd)
  have hr : Continuous (fun p : T × M ↦ projectionIntertwiner (P s p.2) (P p.1 p.2)) :=
    (hc.clm_comp hp).add ((continuous_const.sub hc).clm_comp (continuous_const.sub hp))
  have hi : IsOpen {A : F →L[ℝ] F | A.IsInvertible} := ContinuousLinearEquiv.isOpen
  exact isOpen_forall_compact (hi.preimage hr)

private theorem Smale.DiskFraming.isOpen_transportOnClass {E F T : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [TopologicalSpace T] {K : Set E} (hK : IsCompact K) (P : T → E → F →L[ℝ] F)
    (hP : ∀ t x, x ∈ K → IsIdempotentElem (P t x))
    (hc : Continuous (fun q : T × K => P q.1 q.2.1))
    (hs : ∀ t, ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧ ContDiffOn ℝ ∞ (P t) U) (s : T) :
    IsOpen {t | Nonempty (SmoothRangeTransportOn K (P s) (P t))} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let R (t : T) (x : K) := P t x.1
  have hR (t : T) (x : K) : IsIdempotentElem (R t x) := hP t x.1 x.property
  rw [isOpen_iff_mem_nhds]
  rintro t ⟨a⟩
  have hdom := NoExotic.isOpen_continuousHomotopyTransportDomain R hc t
  have ht := NoExotic.mem_homotopyTransportDomain R hR t
  apply Filter.mem_of_superset (hdom.mem_nhds ht)
  intro u hu
  obtain ⟨Ut, hUt, hKt, hst⟩ := hs t
  obtain ⟨Uu, hUu, hKu, hsu⟩ := hs u
  exact
    ⟨a.trans
        (SmoothRangeTransportOn.ofProjections (hP t) (hP u) hUt hUu hKt hKu hst hsu
          (fun x hx => hu ⟨x, hx⟩))⟩

private theorem
    Smale.DiskFraming.isOpen_compl_transportOnClass {E F T : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [TopologicalSpace T] {K : Set E} (hK : IsCompact K) (P : T → E → F →L[ℝ] F)
    (hP : ∀ t x, x ∈ K → IsIdempotentElem (P t x))
    (hc : Continuous (fun q : T × K => P q.1 q.2.1))
    (hs : ∀ t, ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧ ContDiffOn ℝ ∞ (P t) U) (s : T) :
    IsOpen {t | ¬Nonempty (SmoothRangeTransportOn K (P s) (P t))} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let R (t : T) (x : K) := P t x.1
  have hR (t : T) (x : K) : IsIdempotentElem (R t x) := hP t x.1 x.property
  rw [isOpen_iff_mem_nhds]
  intro t ht
  have hdom := NoExotic.isOpen_continuousHomotopyTransportDomain R hc t
  have htmem := NoExotic.mem_homotopyTransportDomain R hR t
  apply Filter.mem_of_superset (hdom.mem_nhds htmem)
  rintro u hu ⟨a⟩
  obtain ⟨Ut, hUt, hKt, hst⟩ := hs t
  obtain ⟨Uu, hUu, hKu, hsu⟩ := hs u
  exact
    ht
      ⟨a.trans
          (SmoothRangeTransportOn.ofProjections (hP t) (hP u) hUt hUu hKt hKu hst hsu
              (fun x hx => hu ⟨x, hx⟩)).symm⟩

private theorem Smale.DiskFraming.nonempty_smoothRangeTransportOn_of_homotopy {E F T : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] [TopologicalSpace T] {K : Set E} (hK : IsCompact K) (P : T → E → F →L[ℝ] F)
    (hP : ∀ t x, x ∈ K → IsIdempotentElem (P t x))
    (hc : Continuous (fun q : T × K => P q.1 q.2.1))
    (hs : ∀ t, ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧ ContDiffOn ℝ ∞ (P t) U) [PreconnectedSpace T]
    (s t : T) : Nonempty (SmoothRangeTransportOn K (P s) (P t)) := by
  let C : Set T := {u | Nonempty (SmoothRangeTransportOn K (P s) (P u))}
  have hclosed : IsClosed C := by
    simpa only [C, Set.compl_ofPred, Classical.not_not] using
      (isOpen_compl_transportOnClass hK P hP hc hs s).isClosed_compl
  have hclopen : IsClopen C := ⟨hclosed, isOpen_transportOnClass hK P hP hc hs s⟩
  have hall : C = Set.univ := hclopen.eq_univ ⟨s, ⟨SmoothRangeTransportOn.refl K (P s)⟩⟩
  have ht : t ∈ C := by rw [hall]; exact Set.mem_univ t
  exact ht

private theorem
    Smale.DiskFraming.nonempty_transportOn_starConvex {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {K U : Set E}
    (hK : IsCompact K) (hstar : StarConvex ℝ (0 : E) K) (hU : IsOpen U) (hKU : K ⊆ U)
    (P : E → F →L[ℝ] F) (hP : ∀ x ∈ K, IsIdempotentElem (P x)) (hs : ContDiffOn ℝ ∞ P U) :
    Nonempty (SmoothRangeTransportOn K (fun _ => P 0) P) := by
  let Q (t : unitInterval) (x : E) := P ((t : ℝ) • x)
  have hQ : ∀ t x, x ∈ K → IsIdempotentElem (Q t x) := fun t x hx =>
    hP _ (hstar.smul_mem hx t.property.1 t.property.2)
  have hmul : Continuous (fun q : unitInterval × K => (q.1 : ℝ) • (q.2 : E)) :=
    (continuous_subtype_val.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd)
  have hc : Continuous (fun q : unitInterval × K => Q q.1 q.2.1) :=
    hs.continuousOn.comp_continuous hmul
      (fun q => hKU (hstar.smul_mem q.2.property q.1.property.1 q.1.property.2))
  have hslice : ∀ t, ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ ContDiffOn ℝ ∞ (Q t) V := by
    intro t
    let V : Set E := (fun x : E => (t : ℝ) • x) ⁻¹' U
    have hV : IsOpen V := hU.preimage (continuous_const.smul continuous_id)
    have hKV : K ⊆ V := fun x hx => hKU (hstar.smul_mem hx t.property.1 t.property.2)
    exact ⟨V, hV, hKV, hs.comp (contDiff_const.smul contDiff_id).contDiffOn (fun _ hx => hx)⟩
  have hstart : Q 0 = fun _ => P 0 := by
    funext x
    change P ((0 : ℝ) • x) = P 0
    rw [zero_smul]
  have hend : Q 1 = P := by
    funext x
    change P ((1 : ℝ) • x) = P x
    rw [one_smul]
  simpa only [hstart, hend] using
    nonempty_smoothRangeTransportOn_of_homotopy hK Q hQ hc hslice 0 1

private theorem
    Smale.DiskFraming.exists_smooth_frame_near_starConvex {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {K U : Set E}
    (hK : IsCompact K) (hstar : StarConvex ℝ (0 : E) K) (hU : IsOpen U) (hKU : K ⊆ U)
    (P : E → F →L[ℝ] F) (hP : ∀ x ∈ K, IsIdempotentElem (P x)) (hs : ContDiffOn ℝ ∞ P U) :
    ∃ V : Set E,
      IsOpen V ∧
        K ⊆ V ∧
          ∃ A : E → (P 0).range →L[ℝ] F,
            ContDiffOn ℝ ∞ A V ∧ ∀ x ∈ K, Function.Injective (A x) ∧ (A x).range = (P x).range := by
  obtain ⟨a⟩ := nonempty_transportOn_starConvex hK hstar hU hKU P hP hs
  let A (x : E) : (P 0).range →L[ℝ] F := (a.toFun x).comp (P 0).range.subtypeL
  refine
    ⟨a.neighborhood, a.open_neighborhood, a.contains, A, a.smooth.clm_comp contDiffOn_const, ?_⟩
  intro x hx
  refine ⟨(a.invertible x hx).injective.comp Subtype.val_injective, ?_⟩
  change ((a.toFun x).toLinearMap.comp (P 0).range.subtype).range = (P x).range
  rw [LinearMap.range_comp, Submodule.range_subtype]
  exact a.map_range x hx

private theorem Smale.DiskFraming.exists_smooth_frame_on_neighborhood_closedBall {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {U : Set E} (hU : IsOpen U)
    (hballU : Metric.closedBall (0 : E) 1 ⊆ U) (P : E → F →L[ℝ] F)
    (hP : ∀ x ∈ U, IsIdempotentElem (P x)) (hs : ContDiffOn ℝ ∞ P U) :
    ∃ V : Set E,
      IsOpen V ∧
        Metric.closedBall (0 : E) 1 ⊆ V ∧
          V ⊆ U ∧
            ∃ A : E → (P 0).range →L[ℝ] F,
              ContDiffOn ℝ ∞ A V ∧
                ∀ x ∈ V, Function.Injective (A x) ∧ (A x).range = (P x).range := by
  obtain ⟨δ, hδ, hthick⟩ :=
    (ProperSpace.isCompact_closedBall (0 : E) 1).exists_cthickening_subset_open hU hballU
  have hbU : Metric.closedBall (0 : E) (δ + 1) ⊆ U := by
    simpa only [cthickening_closedBall hδ.le zero_le_one] using hthick
  have hr : 1 < δ + 1 := by linarith
  obtain ⟨W, hW, hbW, A, hA, hArange⟩ :=
    exists_smooth_frame_near_starConvex (ProperSpace.isCompact_closedBall (0 : E) (δ + 1))
      ((convex_closedBall (0 : E) (δ + 1)).starConvex (Metric.mem_closedBall_self (by linarith)))
      hU hbU P (fun x hx => hP x (hbU hx)) hs
  refine
    ⟨W ∩ Metric.ball 0 (δ + 1), hW.inter Metric.isOpen_ball, ?_, ?_, A,
      hA.mono Set.inter_subset_left, ?_⟩
  · intro x hx
    exact
      ⟨hbW (Metric.closedBall_subset_closedBall hr.le hx), Metric.closedBall_subset_ball hr hx⟩
  · exact fun _ hx => hbU (Metric.ball_subset_closedBall hx.2)
  · exact fun x hx => hArange x (Metric.ball_subset_closedBall hx.2)

private theorem
    Smale.NativeEuclideanEmbedding.exists_smooth_normalFrame_near_closedBall {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D] (e : Smale.NativeEuclideanEmbedding E M) {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    (hi : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (n : ℕ) (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) :
    ∃ V : Set D,
      IsOpen V ∧
        Metric.closedBall (0 : D) 1 ⊆ V ∧
          ∃ A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension),
            ContDiffOn ℝ ∞ A V ∧
              ∀ x ∈ V, Function.Injective (A x) ∧ (A x).range = e.diskNormalSpace f x := by
  obtain ⟨U, hU, hKU, hsP, hP⟩ := e.exists_open_diskNormalProjection hf hi
  have hidem : ∀ x ∈ U, IsIdempotentElem (e.diskNormalProjection f x) := by
    intro x hx
    rw [hP x hx]
    exact (e.diskNormalSpace f x).isIdempotentElem_starProjection
  obtain ⟨V, hV, hKV, hVU, A, hA, hAi⟩ :=
    Smale.DiskFraming.exists_smooth_frame_on_neighborhood_closedBall hU hKU
      (e.diskNormalProjection f) hidem hsP
  have hz : (0 : D) ∈ Metric.closedBall (0 : D) 1 := Metric.mem_closedBall_self zero_le_one
  have hr : (e.diskNormalProjection f 0).range = e.diskNormalSpace f 0 := by
    rw [hP 0 (hKU hz), Submodule.range_starProjection]
  have hdim : Module.finrank ℝ (e.diskNormalSpace f 0) = n := by
    have h := e.finrank_diskTangent_add_normal hf (hi 0 hz)
    omega
  have hcenter : Module.finrank ℝ (e.diskNormalProjection f 0).range = n :=
    (congrArg
          (fun S : Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) => Module.finrank ℝ S)
          hr).trans
      hdim
  let φ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (e.diskNormalProjection f 0).range :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin.trans hcenter.symm)
  refine
    ⟨V, hV, hKV, fun x => (A x).comp φ.toContinuousLinearMap, hA.clm_comp contDiffOn_const, ?_⟩
  intro x hx
  refine ⟨((hAi x hx).1).comp φ.injective, ?_⟩
  calc
    ((A x).comp φ.toContinuousLinearMap).range = (A x).range :=
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr φ.surjective)
    _ = (e.diskNormalProjection f x).range := (hAi x hx).2
    _ = e.diskNormalSpace f x := by rw [hP x (hVU hx), Submodule.range_starProjection]

private def
    Smale.DiskFraming.normalSplitEquiv {D Z F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (L : D →L[ℝ] F) (A : Z →L[ℝ] F)
    {V : Submodule ℝ F} (hL : Function.Injective L) (hA : Function.Injective A)
    (hLV : L.range ≤ V) (hAr : A.range = L.rangeᗮ ⊓ V) : (D × Z) ≃L[ℝ] V := by
  let a : D × Z →ₗ[ℝ] F := L.toLinearMap.coprod A.toLinearMap
  have har : a.range = V := by
    rw [LinearMap.range_coprod, hAr]
    exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hLV
  have had : Disjoint L.range A.range := by
    rw [hAr]
    exact L.range.orthogonal_disjoint.mono_right inf_le_left
  have hai : Function.Injective a := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range _ _ had,
      LinearMap.ker_eq_bot.mpr hL, LinearMap.ker_eq_bot.mpr hA, Submodule.prod_bot]
  let b : D × Z →ₗ[ℝ] V := a.codRestrict V (fun q => har ▸ LinearMap.mem_range_self a q)
  have hbi : Function.Injective b := fun _ _ h => hai (congrArg Subtype.val h)
  have hbs : Function.Surjective b := by
    intro v
    have hv : (v : F) ∈ a.range := har.symm ▸ v.property
    obtain ⟨q, hq⟩ := hv
    exact ⟨q, Subtype.ext hq⟩
  exact (LinearEquiv.ofBijective b ⟨hbi, hbs⟩).toContinuousLinearEquiv

private def
    Smale.NativeEuclideanEmbedding.diskTangentNormalEquiv {E M D : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] (e : Smale.NativeEuclideanEmbedding E M)
    {f : D → M} (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {x : D}
    (hi : Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension))
    (hA : Function.Injective A) (hAr : A.range = e.diskNormalSpace f x) :
    (D × EuclideanSpace ℝ (Fin n)) ≃L[ℝ] e.tangentImage (f x) :=
  Smale.DiskFraming.normalSplitEquiv (fderiv ℝ (e.toFun ∘ f) x) A (e.injective_fderiv_comp hf hi)
    hA (e.diskTangentImage_le hf x) hAr

private def Smale.DiskFraming.displacement {D Z F : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (H : D → F) (A : D → Z →L[ℝ] F) (p : D × Z) : F :=
  H p.1 + A p.1 p.2

private theorem Smale.DiskFraming.displacement_zero {D Z F : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F] (H : D → F) (A : D → Z →L[ℝ] F)
    (x : D) : displacement H A (x, 0) = H x := by simp [displacement]

private theorem Smale.DiskFraming.contDiffOn_displacement {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {H : D → F} {A : D → Z →L[ℝ] F} {V : Set D} (hH : ContDiff ℝ ∞ H)
    (hA : ContDiffOn ℝ ∞ A V) : ContDiffOn ℝ ∞ (displacement H A) (V ×ˢ Set.univ) :=
  (hH.comp contDiff_fst).contDiffOn.add
    ((hA.comp contDiffOn_fst (fun _ hp => hp.1)).clm_apply contDiffOn_snd)

private theorem
    Smale.DiskFraming.hasFDerivAt_displacement_zero {D Z F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {H : D → F} {A : D → Z →L[ℝ] F} {x : D} (hH : ContDiffAt ℝ ∞ H x)
    (hA : ContDiffAt ℝ ∞ A x) :
    HasFDerivAt (displacement H A) ((fderiv ℝ H x).coprod (A x)) (x, 0) := by
  have hfst : HasFDerivAt (Prod.fst : D × Z → D) (ContinuousLinearMap.fst ℝ D Z) (x, 0) :=
    hasFDerivAt_fst
  have hsnd : HasFDerivAt (Prod.snd : D × Z → Z) (ContinuousLinearMap.snd ℝ D Z) (x, 0) :=
    hasFDerivAt_snd
  have h₁ :
    HasFDerivAt (fun p : D × Z => H p.1) ((fderiv ℝ H x).comp (ContinuousLinearMap.fst ℝ D Z))
      (x, 0) :=
    (hH.differentiableAt (by simp)).hasFDerivAt.comp (x, 0) hfst
  have h₂ :
    HasFDerivAt (fun p : D × Z => A p.1) ((fderiv ℝ A x).comp (ContinuousLinearMap.fst ℝ D Z))
      (x, 0) :=
    (hA.differentiableAt (by simp)).hasFDerivAt.comp (x, 0) hfst
  have h := h₁.add (h₂.clm_apply hsnd)
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro q
  change fderiv ℝ H x q.1 + (A x q.2 + (fderiv ℝ A x q.1) 0) = fderiv ℝ H x q.1 + A x q.2
  rw [map_zero, add_zero]

private def Smale.NativeEuclideanEmbedding.SmoothRetraction.diskCoordinates {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ} (f : D → M)
    (A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)) :
    D × EuclideanSpace ℝ (Fin n) → M :=
  r.toFun ∘ Smale.DiskFraming.displacement (e.toFun ∘ f) A

private def Smale.NativeEuclideanEmbedding.SmoothRetraction.diskCoordinateDomain {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ} (f : D → M)
    (A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension))
    (V : Set D) : Set (D × EuclideanSpace ℝ (Fin n)) :=
  (V ×ˢ Set.univ) ∩ Smale.DiskFraming.displacement (e.toFun ∘ f) A ⁻¹' r.domain

private theorem Smale.NativeEuclideanEmbedding.SmoothRetraction.diskCoordinates_zero {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ} (f : D → M)
    (A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)) (x : D) :
    r.diskCoordinates f A (x, 0) = f x := by
  rw [diskCoordinates, Function.comp_apply, Smale.DiskFraming.displacement_zero]
  exact r.retract (f x)

private theorem Smale.NativeEuclideanEmbedding.SmoothRetraction.isOpen_diskCoordinateDomain
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ} {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)} {V : Set D}
    (hV : IsOpen V) (hA : ContDiffOn ℝ ∞ A V) : IsOpen (r.diskCoordinateDomain f A V) := by
  have hc :=
    (Smale.DiskFraming.contDiffOn_displacement (e.smooth.comp hf).contDiff hA).continuousOn
  exact hc.isOpen_inter_preimage (hV.prod isOpen_univ) r.open_domain

private theorem Smale.NativeEuclideanEmbedding.SmoothRetraction.zero_mem_diskCoordinateDomain
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ}
    (f : D → M) (A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension))
    {V : Set D} {x : D} (hx : x ∈ V) : (x, 0) ∈ r.diskCoordinateDomain f A V := by
  refine ⟨⟨hx, Set.mem_univ _⟩, ?_⟩
  change Smale.DiskFraming.displacement (e.toFun ∘ f) A (x, 0) ∈ r.domain
  rw [Smale.DiskFraming.displacement_zero]
  exact r.contains ⟨f x, rfl⟩

private theorem Smale.NativeEuclideanEmbedding.SmoothRetraction.contMDiffOn_diskCoordinates
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ} {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)} {V : Set D}
    (hA : ContDiffOn ℝ ∞ A V) :
    ContMDiffOn 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ (r.diskCoordinates f A)
      (r.diskCoordinateDomain f A V) :=
  r.smooth.comp
    ((Smale.DiskFraming.contDiffOn_displacement (e.smooth.comp hf).contDiff hA).contMDiffOn.mono
      Set.inter_subset_left)
    (fun _ hp => hp.2)

private theorem Smale.NativeEuclideanEmbedding.SmoothRetraction.mfderiv_diskCoordinates_zero
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ} {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)} {x : D}
    (hA : ContDiffAt ℝ ∞ A x) :
    mfderiv 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) (r.diskCoordinates f A) (x, 0) =
      (mfderiv (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun (e.toFun (f x))).comp
        ((fderiv ℝ (e.toFun ∘ f) x).coprod (A x)) := by
  have hd :=
    Smale.DiskFraming.hasFDerivAt_displacement_zero (e.smooth.comp hf).contDiff.contDiffAt hA
  have hr :
    MDifferentiableAt (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun
      (Smale.DiskFraming.displacement (e.toFun ∘ f) A (x, 0)) := by
    rw [Smale.DiskFraming.displacement_zero]
    exact
      (r.smooth.contMDiffAt (r.open_domain.mem_nhds (r.contains ⟨f x, rfl⟩))).mdifferentiableAt
        (by simp)
  rw [diskCoordinates, mfderiv_comp (x, 0) hr hd.differentiableAt.mdifferentiableAt,
    mfderiv_eq_fderiv, hd.fderiv, Smale.DiskFraming.displacement_zero]
  rfl

private theorem
    Smale.NativeEuclideanEmbedding.SmoothRetraction.isInvertible_mfderiv_diskCoordinates_zero
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    [FiniteDimensional ℝ D] {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    {n : ℕ} {f : D → M} (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)} {x : D}
    (hA : ContDiffAt ℝ ∞ A x) (hi : Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (hAi : Function.Injective (A x)) (hAr : (A x).range = e.diskNormalSpace f x) :
    (mfderiv 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) (r.diskCoordinates f A)
        (x, 0)).IsInvertible := by
  let L := e.diskTangentNormalEquiv hf hi (A x) hAi hAr
  let T := L.trans (e.tangentImageEquiv (f x)).symm
  refine ⟨T, ?_⟩
  apply ContinuousLinearMap.ext
  intro q
  rw [r.mfderiv_diskCoordinates_zero hf hA]
  apply e.injective_mvfderiv (f x)
  have hleft := congrArg Subtype.val ((e.tangentImageEquiv (f x)).apply_symm_apply (L q))
  exact hleft.trans (r.embedding_derivative_retract (L q).property).symm

private theorem
    Smale.NativeEuclideanEmbedding.SmoothRetraction.isLocalDiffeomorphAt_diskCoordinates_zero
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] {e : Smale.NativeEuclideanEmbedding E M}
    (r : e.SmoothRetraction) {n : ℕ} {f : D → M} (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)} {V : Set D}
    (hV : IsOpen V) (hA : ContDiffOn ℝ ∞ A V) {x : D} (hx : x ∈ V)
    (hi : Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x)) (hAi : Function.Injective (A x))
    (hAr : (A x).range = e.diskNormalSpace f x) :
    IsLocalDiffeomorphAt 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ (r.diskCoordinates f A)
      (x, 0) :=
  Smale.isLocalDiffeomorphAt_of_contMDiffOn (r.isOpen_diskCoordinateDomain hf hV hA)
    (r.zero_mem_diskCoordinateDomain f A hx) (r.contMDiffOn_diskCoordinates hf hA)
    (r.isInvertible_mfderiv_diskCoordinates_zero hf (hA.contDiffAt (hV.mem_nhds hx)) hi hAi hAr)

public
theorem Smale.DiskFraming.exists_pos_prod_closedBall_subset {D Z : Type*} [TopologicalSpace D]
    [NormedAddCommGroup Z] {K : Set D} {U : Set (D × Z)} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ×ˢ {(0 : Z)} ⊆ U) : ∃ ε : ℝ, 0 < ε ∧ K ×ˢ Metric.closedBall (0 : Z) ε ⊆ U := by
  obtain ⟨A, B, -, hB, hKA, hzeroB, hAB⟩ :=
    generalized_tube_lemma hK (isCompact_singleton (x := (0 : Z))) hU hKU
  obtain ⟨ε, hε, hball⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hB.mem_nhds (hzeroB (Set.mem_singleton (0 : Z))))
  refine ⟨ε, hε, ?_⟩
  rintro ⟨x, z⟩ ⟨hx, hz⟩
  exact hAB ⟨hKA hx, hball hz⟩

private theorem Smale.NativeEuclideanEmbedding.SmoothRetraction.exists_diskTubularNeighborhood
    {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
    {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ} {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {K V : Set D} (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) (hinj : Set.InjOn f K)
    (hi : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)}
    (hA : ContDiffOn ℝ ∞ A V) (hAi : ∀ x ∈ K, Function.Injective (A x))
    (hAr : ∀ x ∈ K, (A x).range = e.diskNormalSpace f x) :
    ∃ Φ :
      PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) (D × EuclideanSpace ℝ (Fin n))
        M ∞,
      K ×ˢ {(0 : EuclideanSpace ℝ (Fin n))} ⊆ Φ.source ∧
        Φ.source ⊆ r.diskCoordinateDomain f A V ∧
          (Φ : D × EuclideanSpace ℝ (Fin n) → M) = r.diskCoordinates f A := by
  have hzeroInj : Set.InjOn (r.diskCoordinates f A) (K ×ˢ {(0 : EuclideanSpace ℝ (Fin n))}) := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩ ⟨y, w⟩ ⟨hy, hw⟩ hxy
    have hv0 : v = 0 := hv
    have hw0 : w = 0 := hw
    subst v
    subst w
    rw [r.diskCoordinates_zero, r.diskCoordinates_zero] at hxy
    exact Prod.ext (hinj hx hy hxy) rfl
  have hlocal :
    ∀ p ∈ K ×ˢ {(0 : EuclideanSpace ℝ (Fin n))},
      IsLocalDiffeomorphAt 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ (r.diskCoordinates f A)
        p := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    have hv0 : v = 0 := hv
    subst v
    exact
      r.isLocalDiffeomorphAt_diskCoordinates_zero hf hV hA (hKV hx) (hi x hx) (hAi x hx)
        (hAr x hx)
  apply
    Smale.exists_partialDiffeomorph_near_compact (hK.prod isCompact_singleton) hzeroInj hlocal
      (r.isOpen_diskCoordinateDomain hf hV hA)
  rintro ⟨x, v⟩ ⟨hx, hv⟩
  have hv0 : v = 0 := hv
  subst v
  exact r.zero_mem_diskCoordinateDomain f A (hKV hx)

private theorem Smale.exists_tubularNeighborhood_in_open_of_embedded_closedBall {E M D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) (hinj : Set.InjOn f (Metric.closedBall (0 : D) 1))
    (hi : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (n : ℕ) (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E) {O : Set M} (hO : IsOpen O)
    (hfO : Set.MapsTo f (Metric.closedBall (0 : D) 1) O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
            (D × EuclideanSpace ℝ (Fin n)) M ∞,
          Metric.closedBall (0 : D) 1 ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
            (∀ x ∈ Metric.closedBall (0 : D) 1, Φ (x, 0) = f x) ∧ Φ.target ⊆ O := by
  let : Nonempty M := ⟨f 0⟩
  obtain ⟨e⟩ := nonempty_nativeEuclideanEmbedding (E := E) (M := M)
  obtain ⟨r⟩ := e.nonempty_smoothRetraction
  obtain ⟨V, hV, hKV, A, hA, hframe⟩ := e.exists_smooth_normalFrame_near_closedBall hf hi n hcodim
  obtain ⟨Φ, hzero, -, hΦ⟩ :=
    r.exists_diskTubularNeighborhood hf (ProperSpace.isCompact_closedBall 0 1) hV hKV hinj hi hA
      (fun x hx => (hframe x (hKV hx)).1) (fun x hx => (hframe x (hKV hx)).2)
  let W := Φ.source ∩ Φ ⁻¹' O
  have hW : IsOpen W := Φ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ.open_source hO
  have hWloc : IsLocalDiffeomorphOn 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ Φ W := fun p =>
    ⟨Φ, p.property.1, fun _ _ => rfl⟩
  let Ψ :=
    partialDiffeomorphOfInjectiveLocal hW (Φ.toPartialEquiv.injOn.mono Set.inter_subset_left)
      hWloc
  have hzeroΨ : Metric.closedBall (0 : D) 1 ×ˢ {(0 : EuclideanSpace ℝ (Fin n))} ⊆ Ψ.source := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    have hv0 : v = 0 := hv
    subst v
    refine ⟨hzero ⟨hx, rfl⟩, ?_⟩
    change Φ (x, 0) ∈ O
    rw [hΦ, r.diskCoordinates_zero]
    exact hfO hx
  obtain ⟨ε, hε, hprod⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset (ProperSpace.isCompact_closedBall 0 1)
      Ψ.open_source hzeroΨ
  refine ⟨ε, hε, Ψ, hprod, ?_, ?_⟩
  · intro x _
    change Φ (x, 0) = f x
    rw [hΦ, r.diskCoordinates_zero]
  · change Φ '' W ⊆ O
    rintro _ ⟨p, hp, rfl⟩
    exact hp.2

private theorem Smale.RegularLevel.exists_unitHeightField {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        ∀ x : { x : M // f x = b }, mvfderiv 𝓘(ℝ, E) f (x : M) (V x) = 1 := by
  have hband : ∀ x, f x ∈ Set.Icc b b → x ∉ Smale.ManifoldMorse.criticalPoints E f := fun x hx =>
    hreg x (le_antisymm hx.2 hx.1)
  obtain ⟨φ, W, -, -, hW, hφ, V, hV, hheight⟩ :=
    Smale.FlowConstruction.exists_regularBandField hf hband
  refine ⟨V, hV, ?_⟩
  intro x
  exact (hheight x).trans (hφ (hW (by rw [x.property]; exact ⟨le_rfl, le_rfl⟩)))

private theorem Smale.RegularLevel.exists_transverseCollar {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    [Nonempty { x : M // f x = b }] :
    letI := chartedSpace hf hreg
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ({ x : M // f x = b } × ℝ) M ∞,
          (Set.univ : Set { x : M // f x = b }) ×ˢ Metric.closedBall (0 : ℝ) ε ⊆ Φ.source ∧
            (∀ x : { x : M // f x = b }, Φ (x, 0) = x) ∧
              ∀ x : { x : M // f x = b }, HasDerivAt (fun t : ℝ => f (Φ (x, t))) 1 0 := by
  let _ := chartedSpace hf hreg
  let _ := isManifold hf hreg
  let _ : CompactSpace { x : M // f x = b } :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Nonempty M := Nonempty.map (fun x : { x : M // f x = b } => (x : M)) inferInstance
  obtain ⟨e⟩ := Smale.nonempty_nativeEuclideanEmbedding (E := E) (M := M)
  obtain ⟨r⟩ := e.nonempty_smoothRetraction
  obtain ⟨V, hV, hunit⟩ := exists_unitHeightField hf hreg
  let K : Set ({ x : M // f x = b } × ℝ) := Set.univ ×ˢ {(0 : ℝ)}
  have hK : IsCompact K := isCompact_univ.prod isCompact_singleton
  have hinj : Set.InjOn (transverseCoordinates r V) K := by
    rintro ⟨x, s⟩ ⟨-, hs⟩ ⟨y, t⟩ ⟨-, ht⟩ hxy
    have hs0 : s = 0 := hs
    have ht0 : t = 0 := ht
    subst s
    subst t
    rw [transverseCoordinates_zero r V x, transverseCoordinates_zero r V y] at hxy
    exact Prod.ext (Subtype.ext hxy) rfl
  have hloc :
    ∀ z ∈ K,
      IsLocalDiffeomorphAt (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ (transverseCoordinates r V) z :=
    by
    rintro ⟨x, t⟩ ⟨-, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact isLocalDiffeomorphAt_transverseCoordinates_zero r V hf hreg hV x (hunit x)
  have hKD : K ⊆ transverseCoordinateDomain r V := by
    rintro ⟨x, t⟩ ⟨-, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact zero_mem_transverseCoordinateDomain r V x
  obtain ⟨Φ, hKΦ, -, heq⟩ :=
    Smale.exists_partialDiffeomorph_near_compact hK hinj hloc
      (isOpen_transverseCoordinateDomain r V hf hreg hV) hKD
  obtain ⟨ε, hε, hsource⟩ :=
    Smale.DiskFraming.exists_pos_prod_closedBall_subset isCompact_univ Φ.open_source hKΦ
  refine ⟨ε, hε, Φ, hsource, ?_, ?_⟩
  · intro x
    exact (congrFun heq (x, 0)).trans (transverseCoordinates_zero r V x)
  · intro x
    have hh : (fun t : ℝ => f (Φ (x, t))) = fun t : ℝ => f (transverseCoordinates r V (x, t)) :=
      funext (fun t => congrArg f (congrFun heq (x, t)))
    rw [hh]
    exact hasDerivAt_height_transverseCoordinates_zero r V hf hreg hV x (hunit x)

private theorem Smale.RegularLevel.exists_heightBand_subset_open {X : Type*} [TopologicalSpace X]
    [CompactSpace X] {g : X → ℝ} (hg : Continuous g) {a : ℝ} {U : Set X} (hU : IsOpen U)
    (hlevel : ∀ x, g x = a → x ∈ U) : ∃ δ : ℝ, 0 < δ ∧ g ⁻¹' Metric.ball a δ ⊆ U := by
  have hclosed : IsClosed (g '' Uᶜ) := (hU.isClosed_compl.isCompact.image hg).isClosed
  have ha : a ∉ g '' Uᶜ := by
    rintro ⟨x, hx, hxa⟩
    exact hx (hlevel x hxa)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl a ha
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  by_contra hnot
  exact hball hx ⟨x, hnot, rfl⟩

private theorem Smale.RegularLevel.exists_heightCollar {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    [Nonempty { x : M // f x = b }] :
    letI := chartedSpace hf hreg
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Ψ :
          PartialDiffeomorph (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ({ x : M // f x = b } × ℝ) M ∞,
          (Set.univ : Set { x : M // f x = b }) ×ˢ Metric.closedBall (0 : ℝ) ε ⊆ Ψ.source ∧
            (∀ x : { x : M // f x = b }, Ψ (x, 0) = x) ∧ ∀ z ∈ Ψ.source, f (Ψ z) = b + z.2 := by
  let _ := chartedSpace hf hreg
  let _ := isManifold hf hreg
  let _ : CompactSpace { x : M // f x = b } :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  obtain ⟨ε, hε, Φ, hsource, hzero, hderiv⟩ := exists_transverseCollar hf hreg
  let H : { x : M // f x = b } × ℝ → ℝ := fun z => f (Φ z) - b
  have hH : ContMDiffOn (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ H Φ.source :=
    (hf.comp_contMDiffOn Φ.contMDiffOn_toFun).sub contMDiff_const.contMDiffOn
  have hH0 (x : { x : M // f x = b }) : H (x, 0) = 0 := by
    change f (Φ (x, 0)) - b = 0
    rw [hzero x, x.property, sub_self]
  have hzeroSource (x : { x : M // f x = b }) : (x, 0) ∈ Φ.source :=
    hsource ⟨Set.mem_univ x, Metric.mem_closedBall_self hε.le⟩
  have hHt (x : { x : M // f x = b }) : HasDerivAt (fun t : ℝ => H (x, t)) 1 0 :=
    (hderiv x).sub_const b
  obtain ⟨χ, hKχ, -, hχ⟩ :=
    Smale.CollarHeight.exists_heightChangeChart Φ.open_source hH hH0 hzeroSource hHt
  have hχzero (x : { x : M // f x = b }) : χ (x, 0) = (x, 0) :=
    (congrFun hχ (x, 0)).trans (Smale.CollarHeight.heightChange_zero hH0 x)
  have hχtarget (x : { x : M // f x = b }) : (x, 0) ∈ χ.target := by
    rw [← hχzero x]
    exact χ.map_source' (hKχ ⟨Set.mem_univ x, rfl⟩)
  have hχinv (x : { x : M // f x = b }) : χ.symm (x, 0) = (x, 0) := by
    have hh : χ.symm (χ (x, 0)) = (x, 0) := χ.left_inv' (hKχ ⟨Set.mem_univ x, rfl⟩)
    rwa [hχzero x] at hh
  let Ψ := χ.symm.trans Φ
  have hzeroΨ : (Set.univ : Set { x : M // f x = b }) ×ˢ {(0 : ℝ)} ⊆ Ψ.source := by
    rintro ⟨x, t⟩ ⟨-, ht⟩
    have ht0 : t = 0 := ht
    subst t
    refine ⟨hχtarget x, ?_⟩
    change χ.symm (x, 0) ∈ Φ.source
    rw [hχinv x]
    exact hzeroSource x
  obtain ⟨δ, hδ, hproduct⟩ :=
    Smale.DiskFraming.exists_pos_prod_closedBall_subset isCompact_univ Ψ.open_source hzeroΨ
  refine ⟨δ, hδ, Ψ, hproduct, ?_, ?_⟩
  · intro x
    change Φ (χ.symm (x, 0)) = x
    rw [hχinv x, hzero x]
  · intro z hz
    have hheight : H (χ.symm z) = z.2 := by
      calc
        H (χ.symm z) = (χ (χ.symm z)).2 := (congrArg Prod.snd (congrFun hχ (χ.symm z))).symm
        _ = z.2 := congrArg Prod.snd (χ.right_inv' hz.1)
    change f (Φ (χ.symm z)) = b + z.2
    change f (Φ (χ.symm z)) - b = z.2 at hheight
    linarith

private theorem
    Smale.RegularLevel.exists_heightCollar_with_band {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    [Nonempty { x : M // f x = b }] :
    letI := chartedSpace hf hreg
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ Ψ :
          PartialDiffeomorph (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ({ x : M // f x = b } × ℝ) M ∞,
          (Set.univ : Set { x : M // f x = b }) ×ˢ Metric.closedBall (0 : ℝ) ε ⊆ Ψ.source ∧
            (∀ x : { x : M // f x = b }, Ψ (x, 0) = x) ∧
              (∀ z ∈ Ψ.source, f (Ψ z) = b + z.2) ∧ f ⁻¹' Metric.ball b ε ⊆ Ψ.target := by
  let _ := chartedSpace hf hreg
  obtain ⟨ε, hε, Ψ, hsource, hzero, hheight⟩ := exists_heightCollar hf hreg
  have hlevel : ∀ x, f x = b → x ∈ Ψ.target := by
    intro x hx
    let y : { x : M // f x = b } := ⟨x, hx⟩
    have hmem : Ψ (y, 0) ∈ Ψ.target :=
      Ψ.map_source' (hsource ⟨Set.mem_univ y, Metric.mem_closedBall_self hε.le⟩)
    have hy : Ψ (y, 0) = x := hzero y
    exact hy ▸ hmem
  obtain ⟨δ, hδ, hband⟩ := exists_heightBand_subset_open hf.continuous Ψ.open_target hlevel
  refine ⟨Min.min ε δ, lt_min hε hδ, Ψ, ?_, hzero, hheight, ?_⟩
  · exact fun z hz => hsource ⟨hz.1, Metric.closedBall_subset_closedBall (min_le_left ε δ) hz.2⟩
  · exact fun x hx => hband (Metric.ball_subset_ball (min_le_right ε δ) hx)

private theorem
    Smale.SmallPerturbation.injective_id_add {E : Type*} [NormedAddCommGroup E] {u : E → E}
    {k : ℝ≥0} (hu : LipschitzWith k u) (hk : k < 1) : Function.Injective (fun x => x + u x) :=
  (AntilipschitzWith.id.add_lipschitzWith hu (by simpa only [inv_one] using hk)).injective

private theorem Smale.SmallPerturbation.surjective_id_add {E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] {u : E → E} {k : ℝ≥0} (hu : LipschitzWith k u) (hk : k < 1) :
    Function.Surjective (fun x => x + u x) := by
  intro y
  have hlip : LipschitzWith k (fun x => y - u x) := by
    simpa only [zero_add] using (LipschitzWith.const y).sub hu
  have hc : ContractingWith k (fun x => y - u x) := ⟨hk, hlip⟩
  let x := ContractingWith.fixedPoint (fun x => y - u x) hc
  refine ⟨x, ?_⟩
  have hx : y - u x = x := hc.fixedPoint_isFixedPt.eq
  exact eq_sub_iff_add_eq.mp hx.symm

private theorem Smale.SmallPerturbation.bijective_id_add {E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] {u : E → E} {k : ℝ≥0} (hu : LipschitzWith k u) (hk : k < 1) :
    Function.Bijective (fun x => x + u x) :=
  ⟨injective_id_add hu hk, surjective_id_add hu hk⟩

private theorem
    Smale.SmallPerturbation.isInvertible_fderiv_id_add {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {u : E → E} {k : ℝ≥0} (hs : ContDiff ℝ ∞ u)
    (hu : LipschitzWith k u) (hk : k < 1) (x : E) :
    (fderiv ℝ (fun y => y + u y) x).IsInvertible := by
  have hn : ‖fderiv ℝ u x‖ < 1 :=
    (norm_fderiv_le_of_lipschitz ℝ hu).trans_lt (show (k : ℝ) < 1 from hk)
  have hnn : ‖fderiv ℝ u x‖₊ < 1 := hn
  have hi : Function.Injective (ContinuousLinearMap.id ℝ E + fderiv ℝ u x) :=
    injective_id_add (fderiv ℝ u x).lipschitz hnn
  have hd : fderiv ℝ (fun y => y + u y) x = ContinuousLinearMap.id ℝ E + fderiv ℝ u x :=
    ((hasFDerivAt_id x).add (hs.contDiffAt.differentiableAt (by simp)).hasFDerivAt).fderiv
  rw [hd]
  let L :=
    (LinearEquiv.ofInjectiveEndo (ContinuousLinearMap.id ℝ E + fderiv ℝ u x).toLinearMap
        hi).toContinuousLinearEquiv
  exact ⟨L, by ext v; rfl⟩

private def
    Smale.SmallPerturbation.diffeomorphIdAdd {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {u : E → E} {k : ℝ≥0} (hs : ContDiff ℝ ∞ u)
    (hu : LipschitzWith k u) (hk : k < 1) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ := by
  have hloc : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun x => x + u x) := by
    intro x
    apply
      Smale.isLocalDiffeomorphAt_of_contMDiffOn isOpen_univ (Set.mem_univ x)
        (contDiff_id.add hs).contMDiff.contMDiffOn
    rw [mfderiv_eq_fderiv]
    exact isInvertible_fderiv_id_add hs hu hk x
  exact hloc.diffeomorphOfBijective (bijective_id_add hu hk)

private theorem Smale.SmallPerturbation.lipschitzWith_smul_const {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {β : E → ℝ} {k : ℝ≥0} (hβ : LipschitzWith k β) (a : E) :
    LipschitzWith (k * ‖a‖₊) (fun x => β x • a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    Dist.dist (β x • a) (β y • a) = ‖β x - β y‖ * ‖a‖ := by
      rw [dist_eq_norm, ← sub_smul, norm_smul]
    _ ≤ ((k : ℝ) * Dist.dist x y) * ‖a‖ :=
      (mul_le_mul_of_nonneg_right (hβ.dist_le_mul x y) (norm_nonneg a))
    _ = (k * ‖a‖₊ : ℝ≥0) * Dist.dist x y := by
      simp only [NNReal.coe_mul, coe_nnnorm]
      ring

private def
    Smale.SmallPerturbation.bumpTranslation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {β : E → ℝ} {k : ℝ≥0} (hs : ContDiff ℝ ∞ β) (hβ : LipschitzWith k β)
    (a : E) (ha : k * ‖a‖₊ < 1) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
  diffeomorphIdAdd (hs.smul contDiff_const) (lipschitzWith_smul_const hβ a) ha

private theorem Smale.SmallPerturbation.bumpTranslation_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {β : E → ℝ} {k : ℝ≥0} (hs : ContDiff ℝ ∞ β)
    (hβ : LipschitzWith k β) (a : E) (ha : k * ‖a‖₊ < 1) (x : E) :
    bumpTranslation hs hβ a ha x = x + β x • a :=
  rfl

private theorem
    Smale.SmallPerturbation.bumpTranslation_eq_of_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {β : E → ℝ} {k : ℝ≥0} (hs : ContDiff ℝ ∞ β)
    (hβ : LipschitzWith k β) (a : E) (ha : k * ‖a‖₊ < 1) {x : E} (hx : β x = 0) :
    bumpTranslation hs hβ a ha x = x := by rw [bumpTranslation_apply, hx, zero_smul, add_zero]

private theorem
    Smale.SmallPerturbation.exists_radius_bumpTranslation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {β : E → ℝ} (hs : ContDiff ℝ ∞ β)
    (hcompact : HasCompactSupport β) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ a : E,
          ‖a‖ < ε →
            ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
              (∀ x, d x = x + β x • a) ∧ ∀ x ∉ tsupport β, d x = x := by
  obtain ⟨k, hk⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcompact hs (by simp)
  have hkpos : 0 < (k : ℝ) + 1 := by positivity
  refine ⟨((k : ℝ) + 1)⁻¹, inv_pos.mpr hkpos, ?_⟩
  intro a ha
  have hmul : ((k : ℝ) + 1) * ‖a‖ < 1 := by
    calc
      ((k : ℝ) + 1) * ‖a‖ < ((k : ℝ) + 1) * ((k : ℝ) + 1)⁻¹ := mul_lt_mul_of_pos_left ha hkpos
      _ = 1 := mul_inv_cancel₀ hkpos.ne'
  have hsmall : k * ‖a‖₊ < 1 := by
    have hreal : (k : ℝ) * ‖a‖ < 1 := by nlinarith [norm_nonneg a]
    exact hreal
  refine ⟨bumpTranslation hs hk a hsmall, fun _ => rfl, ?_⟩
  intro x hx
  apply bumpTranslation_eq_of_zero
  by_contra hne
  exact hx (subset_tsupport β hne)

private theorem
    Smale.SupportedDiffeomorph.mapsTo_of_fixed_outside {X : Type*} (d : X ≃ X) {S : Set X}
    (hfix : ∀ x ∉ S, d x = x) : Set.MapsTo d S S := by
  intro x hx
  by_contra hdx
  have heq : d x = x := d.injective (hfix (d x) hdx)
  exact hdx (heq.symm ▸ hx)

private theorem Smale.SupportedDiffeomorph.inverse_fixed_outside {X : Type*} (d : X ≃ X) {S : Set X}
    (hfix : ∀ x ∉ S, d x = x) : ∀ x ∉ S, d.symm x = x := by
  intro x hx
  apply d.injective
  rw [d.apply_symm_apply, hfix x hx]

private def Smale.SupportedDiffeomorph.extendMap {E F H H' X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] (Φ : PartialDiffeomorph I J X Y ∞)
    (f : X → X) (y : Y) : Y := by classical exact if y ∈ Φ.target then Φ (f (Φ.symm y)) else y

private theorem
    Smale.SupportedDiffeomorph.extendMap_of_mem {E F H H' X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] (Φ : PartialDiffeomorph I J X Y ∞)
    (f : X → X) {y : Y} (hy : y ∈ Φ.target) : extendMap Φ f y = Φ (f (Φ.symm y)) := by
  simp only [extendMap, hy, ite_eq_left]

private theorem Smale.SupportedDiffeomorph.extendMap_of_notMem {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (Φ : PartialDiffeomorph I J X Y ∞) (f : X → X) {y : Y} (hy : y ∉ Φ.target) :
    extendMap Φ f y = y := by simp only [extendMap, hy, ite_false]

private theorem
    Smale.SupportedDiffeomorph.extendMap_id {E F H H' X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] (Φ : PartialDiffeomorph I J X Y ∞)
    (y : Y) : extendMap Φ id y = y := by
  by_cases hy : y ∈ Φ.target
  · rw [extendMap_of_mem Φ id hy]
    exact Φ.right_inv' hy
  · exact extendMap_of_notMem Φ id hy

private theorem
    Smale.SupportedDiffeomorph.extendMap_chart {E F H H' X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] (Φ : PartialDiffeomorph I J X Y ∞)
    (f : X → X) {x : X} (hx : x ∈ Φ.source) : extendMap Φ f (Φ x) = Φ (f x) := by
  rw [extendMap_of_mem Φ f (Φ.map_source' hx)]
  exact congrArg (fun z => Φ (f z)) (Φ.left_inv' hx)

private theorem Smale.SupportedDiffeomorph.extendMap_mem_target {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (Φ : PartialDiffeomorph I J X Y ∞) {f : X → X} (hf : Set.MapsTo f Φ.source Φ.source) {y : Y}
    (hy : y ∈ Φ.target) : extendMap Φ f y ∈ Φ.target := by
  rw [extendMap_of_mem Φ f hy]
  exact Φ.map_source' (hf (Φ.map_target' hy))

private theorem Smale.SupportedDiffeomorph.extendMap_leftInverse {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (Φ : PartialDiffeomorph I J X Y ∞) (d : X ≃ X) (hd : Set.MapsTo d Φ.source Φ.source) :
    Function.LeftInverse (extendMap Φ d.symm) (extendMap Φ d) := by
  intro y
  by_cases hy : y ∈ Φ.target
  · rw [extendMap_of_mem Φ d.symm (extendMap_mem_target Φ hd hy), extendMap_of_mem Φ d hy]
    change Φ (d.symm (Φ.invFun (Φ (d (Φ.invFun y))))) = y
    rw [Φ.left_inv' (hd (Φ.map_target' hy)), d.symm_apply_apply]
    exact Φ.right_inv' hy
  · rw [extendMap_of_notMem Φ d hy, extendMap_of_notMem Φ d.symm hy]

private theorem Smale.SupportedDiffeomorph.extendMap_eq_of_notMem_image {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (Φ : PartialDiffeomorph I J X Y ∞) {f : X → X} {K : Set X} (hfix : ∀ x ∉ K, f x = x) {y : Y}
    (hy : y ∉ Φ '' K) : extendMap Φ f y = y := by
  by_cases hyt : y ∈ Φ.target
  · have hback : Φ.symm y ∉ K := fun h => hy ⟨Φ.symm y, h, Φ.right_inv' hyt⟩
    rw [extendMap_of_mem Φ f hyt, hfix _ hback]
    exact Φ.right_inv' hyt
  · exact extendMap_of_notMem Φ f hyt

private theorem
    Smale.SupportedDiffeomorph.mapsTo_source {E F H H' X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] (Φ : PartialDiffeomorph I J X Y ∞)
    (d : X ≃ X) {K : Set X} (hKΦ : K ⊆ Φ.source) (hfix : ∀ x ∉ K, d x = x) :
    Set.MapsTo d Φ.source Φ.source :=
  mapsTo_of_fixed_outside d (fun x hx => hfix x (fun hk => hx (hKΦ hk)))

private theorem Smale.SupportedDiffeomorph.contMDiff_extendMap {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (Φ : PartialDiffeomorph I J X Y ∞) [T2Space Y] {f : X → X} (hf : ContMDiff I I ∞ f)
    {K : Set X} (hK : IsCompact K) (hKΦ : K ⊆ Φ.source) (hfix : ∀ x ∉ K, f x = x)
    (hsource : Set.MapsTo f Φ.source Φ.source) : ContMDiff J J ∞ (extendMap Φ f) := by
  intro y
  by_cases hy : y ∈ Φ.target
  · have hback := Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hy)
    have hforward :=
      Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hsource (Φ.map_target' hy)))
    have hs := hforward.comp y (hf.contMDiffAt.comp y hback)
    apply hs.congr_of_eventuallyEq
    filter_upwards [Φ.open_target.mem_nhds hy] with z hz
    exact extendMap_of_mem Φ f hz
  · have hc : IsClosed (Φ '' K) :=
      (hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKΦ)).isClosed
    have hnot : y ∉ Φ '' K := by
      rintro ⟨x, hx, rfl⟩
      exact hy (Φ.map_source' (hKΦ hx))
    apply (contMDiffAt_id : ContMDiffAt J J ∞ id y).congr_of_eventuallyEq
    filter_upwards [hc.isOpen_compl.mem_nhds hnot] with z hz
    exact extendMap_eq_of_notMem_image Φ hfix hz

private def Smale.SupportedDiffeomorph.extension {E F H H' X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] (Φ : PartialDiffeomorph I J X Y ∞)
    [T2Space Y] (d : Diffeomorph I I X X ∞) {K : Set X} (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hfix : ∀ x ∉ K, d x = x) : Diffeomorph J J Y Y ∞ := by
  have hdi : ∀ x ∉ K, d.symm x = x := inverse_fixed_outside d.toEquiv hfix
  have hdS : Set.MapsTo d Φ.source Φ.source := mapsTo_source Φ d.toEquiv hKΦ hfix
  have hdiS : Set.MapsTo d.symm Φ.source Φ.source := mapsTo_source Φ d.symm.toEquiv hKΦ hdi
  exact
    { toFun := extendMap Φ d
      invFun := extendMap Φ d.symm
      left_inv := extendMap_leftInverse Φ d.toEquiv hdS
      right_inv := extendMap_leftInverse Φ d.symm.toEquiv hdiS
      contMDiff_toFun := contMDiff_extendMap Φ d.contMDiff hK hKΦ hfix hdS
      contMDiff_invFun := contMDiff_extendMap Φ d.symm.contMDiff hK hKΦ hdi hdiS }

private theorem
    Smale.SupportedDiffeomorph.extension_chart {E F H H' X Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] (Φ : PartialDiffeomorph I J X Y ∞)
    [T2Space Y] (d : Diffeomorph I I X X ∞) {K : Set X} (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hfix : ∀ x ∉ K, d x = x) {x : X} (hx : x ∈ Φ.source) :
    extension Φ d hK hKΦ hfix (Φ x) = Φ (d x) :=
  extendMap_chart Φ d hx

private theorem Smale.SupportedDiffeomorph.extension_eq_of_notMem_image {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (Φ : PartialDiffeomorph I J X Y ∞) [T2Space Y] (d : Diffeomorph I I X X ∞) {K : Set X}
    (hK : IsCompact K) (hKΦ : K ⊆ Φ.source) (hfix : ∀ x ∉ K, d x = x) {y : Y} (hy : y ∉ Φ '' K) :
    extension Φ d hK hKΦ hfix y = y :=
  extendMap_eq_of_notMem_image Φ hfix hy

private theorem Smale.SupportedDiffeomorph.extension_eq_of_notMem_target {E F H H' X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (Φ : PartialDiffeomorph I J X Y ∞) [T2Space Y] (d : Diffeomorph I I X X ∞) {K : Set X}
    (hK : IsCompact K) (hKΦ : K ⊆ Φ.source) (hfix : ∀ x ∉ K, d x = x) {y : Y}
    (hy : y ∉ Φ.target) : extension Φ d hK hKΦ hfix y = y :=
  extendMap_of_notMem Φ d hy

private theorem Smale.RegularLevel.le_shift_iff_of_abs_sub_ge {u b t ε : ℝ} (ht : |t| < ε)
    (hu : ε ≤ |u - b|) : u ≤ b + t ↔ u ≤ b := by
  by_cases hbelow : u ≤ b
  · rw [abs_of_nonpos (sub_nonpos.mpr hbelow)] at hu
    exact ⟨fun _ => hbelow, fun _ => by linarith [(abs_lt.mp ht).1]⟩
  · have habove : b ≤ u := le_of_not_ge hbelow
    rw [abs_of_nonneg (sub_nonneg.mpr habove)] at hu
    constructor <;> intro hh <;> exfalso <;> linarith [(abs_lt.mp ht).2]

private theorem Smale.RegularLevel.exists_ambientTransport_of_heightCollar {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f) (ε : ℝ) (hε : 0 < ε) :
    letI := chartedSpace hf hreg
    ∀ Ψ : PartialDiffeomorph (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ({ x : M // f x = b } × ℝ) M ∞,
      ((Set.univ : Set { x : M // f x = b }) ×ˢ Metric.closedBall (0 : ℝ) ε ⊆ Ψ.source) →
        (∀ x : { x : M // f x = b }, Ψ (x, 0) = x) →
          (∀ z ∈ Ψ.source, f (Ψ z) = b + z.2) →
            (f ⁻¹' Metric.ball b ε ⊆ Ψ.target) →
              ∃ δ : ℝ,
                0 < δ ∧
                  δ ≤ ε ∧
                    ∃ K : Set M,
                      IsCompact K ∧
                        K ⊆ Ψ.target ∧
                          ∀ t : ℝ,
                            |t| < δ →
                              ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
                                (∀ y, y ∉ K → D y = y) ∧
                                  (∀ x : { x : M // f x = b }, D x = Ψ (x, t)) ∧
                                    D '' {x : M | f x = b} = {x : M | f x = b + t} ∧
                                      D '' {x : M | f x ≤ b} = {x : M | f x ≤ b + t} := by
  let _ := chartedSpace hf hreg
  let _ : CompactSpace { x : M // f x = b } :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  intro Ψ hsource hzero hheight hband
  obtain ⟨β, hβ, hsupp, W, -, hW, -, hβW⟩ :=
    LineBundleTransport.exists_smooth_cutoff_near_closed (K := {(0 : ℝ)}) (U :=
      Metric.ball (0 : ℝ) ε) isClosed_singleton Metric.isOpen_ball
      (by
        simpa only [Set.singleton_subset_iff] using
          (Metric.mem_ball_self hε : (0 : ℝ) ∈ Metric.ball 0 ε))
  have hβ0 : β 0 = 1 := hβW (hW (Set.mem_singleton 0))
  have hcompact : HasCompactSupport β :=
    (ProperSpace.isCompact_closedBall (0 : ℝ) ε).of_isClosed_subset (isClosed_tsupport β)
      (hsupp.trans Metric.ball_subset_closedBall)
  obtain ⟨η, hη, htranslations⟩ :=
    Smale.SmallPerturbation.exists_radius_bumpTranslation hβ hcompact
  let C : Set ({ x : M // f x = b } × ℝ) := Set.univ ×ˢ tsupport β
  have hC : IsCompact C := isCompact_univ.prod hcompact
  have hCsource : C ⊆ Ψ.source := fun z hz =>
    hsource ⟨hz.1, Metric.ball_subset_closedBall (hsupp hz.2)⟩
  let K : Set M := Ψ '' C
  have hK : IsCompact K :=
    hC.image_of_continuousOn (Ψ.contMDiffOn_toFun.continuousOn.mono hCsource)
  have hKtarget : K ⊆ Ψ.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact Ψ.map_source' (hCsource hz)
  refine ⟨Min.min ε η, lt_min hε hη, min_le_left ε η, K, hK, hKtarget, ?_⟩
  intro t ht
  have htε : |t| < ε := lt_of_lt_of_le ht (min_le_left ε η)
  have htη : ‖t‖ < η := by
    simpa only [Real.norm_eq_abs] using lt_of_lt_of_le ht (min_le_right ε η)
  obtain ⟨d, hd, hdfix⟩ := htranslations t htη
  have hd0 : d 0 = t := by
    rw [hd 0, hβ0]
    simp
  have hdfar (s : ℝ) (hs : ε ≤ s) : d s = s := by
    apply hdfix
    intro hsupps
    have hball : |s| < ε := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hsupp hsupps
    rw [abs_of_nonneg (hε.le.trans hs)] at hball
    exact (not_lt_of_ge hs) hball
  have hdmono : StrictMono d := by
    rcases d.contMDiff.continuous.strictMono_of_inj d.injective with hm | ha
    · exact hm
    · have hh := ha (show ε < ε + 1 by linarith)
      rw [hdfar ε le_rfl, hdfar (ε + 1) (by linarith)] at hh
      linarith
  let P := (Diffeomorph.refl 𝓘(ℝ, Model E) { x : M // f x = b } ∞).prodCongr d
  have hPfix : ∀ z, z ∉ C → P z = z := by
    intro z hz
    have hzβ : z.2 ∉ tsupport β := fun hh => hz ⟨Set.mem_univ z.1, hh⟩
    exact Prod.ext rfl (hdfix z.2 hzβ)
  let D := Smale.SupportedDiffeomorph.extension Ψ P hC hCsource hPfix
  have hpoint (x : { x : M // f x = b }) : D x = Ψ (x, t) := by
    have hx0 : (x, 0) ∈ Ψ.source := hsource ⟨Set.mem_univ x, Metric.mem_closedBall_self hε.le⟩
    have hP0 : P (x, 0) = (x, t) := by exact Prod.ext rfl hd0
    have hh := Smale.SupportedDiffeomorph.extension_chart Ψ P hC hCsource hPfix hx0
    change D (Ψ (x, 0)) = Ψ (P (x, 0)) at hh
    rwa [hzero x, hP0] at hh
  refine ⟨D, ?_, hpoint, ?_, ?_⟩
  · intro y hy
    exact Smale.SupportedDiffeomorph.extension_eq_of_notMem_image Ψ P hC hCsource hPfix hy
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      let z : { x : M // f x = b } := ⟨x, hx⟩
      have hDx : D x = Ψ (z, t) := hpoint z
      change f (D x) = b + t
      rw [hDx]
      exact
        hheight (z, t)
          (hsource
            ⟨Set.mem_univ z, by
              simpa only [mem_closedBall_zero_iff, Real.norm_eq_abs] using htε.le⟩)
    · intro hy
      have hy' : f y = b + t := hy
      have hyTarget : y ∈ Ψ.target := by
        apply hband
        change Dist.dist (f y) b < ε
        simpa only [hy', Real.dist_eq, add_sub_cancel_left] using htε
      have hback := Ψ.map_target' hyTarget
      have hright : Ψ (Ψ.symm y) = y := Ψ.right_inv' hyTarget
      have htime : (Ψ.symm y).2 = t := by
        have hh := hheight (Ψ.symm y) hback
        rw [hright, hy'] at hh
        linarith
      refine ⟨((Ψ.symm y).1 : M), (Ψ.symm y).1.property, ?_⟩
      have hpair : ((Ψ.symm y).1, t) = Ψ.symm y := Prod.ext rfl htime.symm
      exact (hpoint (Ψ.symm y).1).trans ((congrArg Ψ hpair).trans hright)
  · have hsublevel (y : M) : f (D y) ≤ b + t ↔ f y ≤ b := by
      by_cases hy : y ∈ Ψ.target
      · let z := Ψ.symm y
        have hz : z ∈ Ψ.source := Ψ.map_target' hy
        have hPz : P z ∈ Ψ.source :=
          Smale.SupportedDiffeomorph.mapsTo_source Ψ P.toEquiv hCsource hPfix hz
        have hDy : D y = Ψ (P z) := Smale.SupportedDiffeomorph.extendMap_of_mem Ψ P hy
        have hfy : f y = b + z.2 := by
          have hh := hheight z hz
          have hzy : Ψ z = y := Ψ.right_inv' hy
          rwa [hzy] at hh
        have hfd : f (D y) = b + d z.2 := by
          rw [hDy]
          exact hheight (P z) hPz
        have horder : d z.2 ≤ t ↔ z.2 ≤ 0 := by
          rw [← hd0]
          exact hdmono.le_iff_le
        rw [hfd, hfy]
        constructor
        · intro hh
          have hz0 := horder.mp (by linarith)
          linarith
        · intro hh
          have hdz := horder.mpr (by linarith)
          linarith
      · have hDy : D y = y :=
          Smale.SupportedDiffeomorph.extension_eq_of_notMem_target Ψ P hC hCsource hPfix hy
        rw [hDy]
        have hfar : ε ≤ |f y - b| := by
          apply le_of_not_gt
          intro hh
          apply hy
          apply hband
          change Dist.dist (f y) b < ε
          simpa only [Metric.mem_ball, Real.dist_eq] using hh
        exact le_shift_iff_of_abs_sub_ge htε hfar
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hsublevel x).mpr hx
    · intro hy
      obtain ⟨x, rfl⟩ := D.surjective y
      exact ⟨x, (hsublevel x).mp hy, rfl⟩

private theorem
    Smale.RegularLevel.exists_nearby_ambient_level_diffeomorphs_of_nonempty {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    [Nonempty { x : M // f x = b }] :
    ∃ δ : ℝ,
      0 < δ ∧
        ∃ K : Set M,
          IsCompact K ∧
            ∀ t : ℝ,
              |t| < δ →
                ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
                  (∀ y, y ∉ K → D y = y) ∧
                    D '' {x : M | f x = b} = {x : M | f x = b + t} ∧
                      D '' {x : M | f x ≤ b} = {x : M | f x ≤ b + t} := by
  let _ := chartedSpace hf hreg
  obtain ⟨ε, hε, Ψ, hsource, hzero, hheight, hband⟩ := exists_heightCollar_with_band hf hreg
  obtain ⟨δ, hδ, -, K, hK, -, htransport⟩ :=
    exists_ambientTransport_of_heightCollar hf hreg ε hε Ψ hsource hzero hheight hband
  refine ⟨δ, hδ, K, hK, ?_⟩
  intro t ht
  obtain ⟨D, hfix, -, hlevel, hsublevel⟩ := htransport t ht
  exact ⟨D, hfix, hlevel, hsublevel⟩

private theorem Smale.RegularLevel.exists_nearby_ambient_level_diffeomorphs {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    ∃ δ : ℝ,
      0 < δ ∧
        ∃ K : Set M,
          IsCompact K ∧
            ∀ t : ℝ,
              |t| < δ →
                ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
                  (∀ y, y ∉ K → D y = y) ∧
                    D '' {x : M | f x = b} = {x : M | f x = b + t} ∧
                      D '' {x : M | f x ≤ b} = {x : M | f x ≤ b + t} := by
  classical
  by_cases hb : Nonempty { x : M // f x = b }
  · let _ := hb
    exact exists_nearby_ambient_level_diffeomorphs_of_nonempty hf hreg
  · have hlevel : ∀ x, f x = b → x ∈ (∅ : Set M) := fun x hx => (hb ⟨⟨x, hx⟩⟩).elim
    obtain ⟨δ, hδ, hband⟩ := exists_heightBand_subset_open hf.continuous isOpen_empty hlevel
    refine ⟨δ, hδ, ∅, isCompact_empty, ?_⟩
    intro t ht
    refine ⟨Diffeomorph.refl 𝓘(ℝ, E) M ∞, fun _ _ => rfl, ?_, ?_⟩
    · change id '' {x : M | f x = b} = {x : M | f x = b + t}
      rw [Set.image_id]
      ext x
      constructor
      · intro hx
        exact (hb ⟨⟨x, hx⟩⟩).elim
      · intro hx
        have hball : x ∈ f ⁻¹' Metric.ball b δ := by
          change Dist.dist (f x) b < δ
          simpa only [show f x = b + t from hx, Real.dist_eq, add_sub_cancel_left] using ht
        exact (hband hball).elim
    · change id '' {x : M | f x ≤ b} = {x : M | f x ≤ b + t}
      rw [Set.image_id]
      ext x
      have hfar : δ ≤ |f x - b| := by
        apply le_of_not_gt
        intro hh
        apply hband
        change Dist.dist (f x) b < δ
        simpa only [Real.dist_eq] using hh
      exact (le_shift_iff_of_abs_sub_ge ht hfar).symm

private def
    Smale.RegularLevel.AmbientEquivalent {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (a b : ℝ) : Prop :=
  ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
    D '' {x : M | f x = a} = {x : M | f x = b} ∧ D '' {x : M | f x ≤ a} = {x : M | f x ≤ b}

private theorem Smale.RegularLevel.ambientEquivalent_refl {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (a : ℝ) :
    AmbientEquivalent (E := E) f a a := by
  refine ⟨Diffeomorph.refl 𝓘(ℝ, E) M ∞, ?_, ?_⟩ <;> exact Set.image_id _

private theorem Smale.RegularLevel.ambientEquivalent_symm {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {a b : ℝ}
    (h : AmbientEquivalent (E := E) f a b) : AmbientEquivalent (E := E) f b a := by
  obtain ⟨D, hlevel, hsublevel⟩ := h
  have hreverse (S T : Set M) (hST : D '' S = T) : D.symm '' T = S := by
    rw [← hST, Set.image_image]
    have heq : (fun x : M => D.symm (D x)) = id := funext D.symm_apply_apply
    rw [heq, Set.image_id]
  exact ⟨D.symm, hreverse _ _ hlevel, hreverse _ _ hsublevel⟩

private theorem Smale.RegularLevel.ambientEquivalent_trans {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {a b c : ℝ}
    (hab : AmbientEquivalent (E := E) f a b) (hbc : AmbientEquivalent (E := E) f b c) :
    AmbientEquivalent (E := E) f a c := by
  obtain ⟨e, he, he'⟩ := hab
  obtain ⟨d, hd, hd'⟩ := hbc
  refine ⟨e.trans d, ?_, ?_⟩
  · change (fun x => d (e x)) '' {x : M | f x = a} = {x : M | f x = c}
    rw [← Set.image_image, he, hd]
  · change (fun x => d (e x)) '' {x : M | f x ≤ a} = {x : M | f x ≤ c}
    rw [← Set.image_image, he', hd']

private theorem Smale.RegularLevel.exists_ambient_regularBand_transport {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      D '' {x : M | f x = a} = {x : M | f x = b} ∧ D '' {x : M | f x ≤ a} = {x : M | f x ≤ b} := by
  classical
  let B := Set.Icc a b
  let left : B := ⟨a, ⟨le_rfl, hab⟩⟩
  let right : B := ⟨b, ⟨hab, le_rfl⟩⟩
  let reg (t : B) : ∀ x, f x = (t : ℝ) → x ∉ Smale.ManifoldMorse.criticalPoints E f := fun x hx =>
    hband x (hx ▸ t.property)
  let P : B → Prop := fun t => AmbientEquivalent (E := E) f a (t : ℝ)
  have hlocal : IsLocallyConstant P := by
    apply (IsLocallyConstant.iff_eventually_eq P).mpr
    intro t
    obtain ⟨δ, hδ, K, -, htransport⟩ := exists_nearby_ambient_level_diffeomorphs hf (reg t)
    filter_upwards [Metric.ball_mem_nhds t hδ] with s hs
    have hdist : |(s : ℝ) - (t : ℝ)| < δ := by
      change Dist.dist (s : ℝ) (t : ℝ) < δ at hs
      simpa only [Real.dist_eq] using hs
    obtain ⟨D, -, hlevel, hsublevel⟩ := htransport ((s : ℝ) - (t : ℝ)) hdist
    have hts : AmbientEquivalent (E := E) f (t : ℝ) (s : ℝ) := by
      have heq : (t : ℝ) + ((s : ℝ) - (t : ℝ)) = (s : ℝ) := by ring
      refine ⟨D, ?_, ?_⟩
      · simpa only [heq] using hlevel
      · simpa only [heq] using hsublevel
    apply propext
    constructor
    · intro hs
      exact ambientEquivalent_trans hs (ambientEquivalent_symm hts)
    · intro ht
      exact ambientEquivalent_trans ht hts
  let _ : PreconnectedSpace B := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hconstant : P left = P right := hlocal.apply_eq_of_preconnectedSpace left right
  have hleft : P left := ambientEquivalent_refl f a
  have hright : P right := hconstant ▸ hleft
  exact hright

private theorem
    Smale.RegularLevel.exists_levelDiffeomorph_of_ambient {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (ha : ∀ x, f x = a → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hb : ∀ x, f x = b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (hlevel : D '' {x : M | f x = a} = {x : M | f x = b}) :
    letI := chartedSpace hf ha
    letI := chartedSpace hf hb
    ∃ e : Diffeomorph 𝓘(ℝ, Model E) 𝓘(ℝ, Model E) { x : M // f x = a } { x : M // f x = b } ∞,
      ∀ x, (e x : M) = D x := by
  let _ := chartedSpace hf ha
  let _ := chartedSpace hf hb
  have hiff (x : M) : f x = a ↔ f (D x) = b := by
    constructor
    · intro hx
      have hh : D x ∈ D '' {x : M | f x = a} := ⟨x, hx, rfl⟩
      rwa [hlevel] at hh
    · intro hx
      have hh : D x ∈ D '' {x : M | f x = a} := by rw [hlevel]; exact hx
      obtain ⟨z, hz, hzx⟩ := hh
      exact D.injective hzx ▸ hz
  let e := D.toHomeomorph.subtype (p := fun x => f x = a) (q := fun x => f x = b) hiff
  have he : ContMDiff 𝓘(ℝ, Model E) 𝓘(ℝ, Model E) ∞ e :=
    (contMDiff_iff_inclusion hf hb 𝓘(ℝ, Model E) e).mpr
      (D.contMDiff.comp (Smale.RegularLevel.contMDiff_inclusion hf ha))
  have hei : ContMDiff 𝓘(ℝ, Model E) 𝓘(ℝ, Model E) ∞ e.symm :=
    (contMDiff_iff_inclusion hf ha 𝓘(ℝ, Model E) e.symm).mpr
      (D.symm.contMDiff.comp (Smale.RegularLevel.contMDiff_inclusion hf hb))
  let F : Diffeomorph 𝓘(ℝ, Model E) 𝓘(ℝ, Model E) { x : M // f x = a } { x : M // f x = b } ∞ :=
    { e.toEquiv with
      contMDiff_toFun := he
      contMDiff_invFun := hei }
  exact ⟨F, fun _ => rfl⟩

private def Smale.SphereCoordinates.ofLinearIsometry {N P : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [NormedAddCommGroup P] [InnerProductSpace ℝ P] {n : ℕ}
    [Fact (Module.finrank ℝ N = n + 1)] [Fact (Module.finrank ℝ P = n + 1)] (L : N ≃ₗᵢ[ℝ] P) :
    Diffeomorph (𝓡 n) (𝓡 n) (Metric.sphere (0 : N) 1) (Metric.sphere (0 : P) 1) ∞ := by
  have hforward (x : Metric.sphere (0 : N) 1) : L (x : N) ∈ Metric.sphere (0 : P) 1 := by
    simpa only [mem_sphere_zero_iff_norm, L.norm_map] using x.property
  have hinverse (y : Metric.sphere (0 : P) 1) : L.symm (y : P) ∈ Metric.sphere (0 : N) 1 := by
    simpa only [mem_sphere_zero_iff_norm, L.symm.norm_map] using y.property
  have hs : ContMDiff (𝓡 n) 𝓘(ℝ, P) ∞ (fun x : Metric.sphere (0 : N) 1 => L (x : N)) :=
    L.contDiff.contMDiff.comp (contMDiff_coe_sphere (n := n))
  have hi : ContMDiff (𝓡 n) 𝓘(ℝ, N) ∞ (fun y : Metric.sphere (0 : P) 1 => L.symm (y : P)) :=
    L.symm.contDiff.contMDiff.comp (contMDiff_coe_sphere (n := n))
  exact
    { toFun := fun x => ⟨L x, hforward x⟩
      invFun := fun y => ⟨L.symm y, hinverse y⟩
      left_inv := fun x => Subtype.ext (L.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (L.apply_symm_apply y)
      contMDiff_toFun := hs.codRestrict_sphere hforward
      contMDiff_invFun := hi.codRestrict_sphere hinverse }

private def Smale.SphereCoordinates.standardParametrization (N : Type*) [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] (n : ℕ) [Fact (Module.finrank ℝ N = n + 1)] [FiniteDimensional ℝ N] :
    Diffeomorph (𝓡 n) (𝓡 n) (Smale.Hemisphere.Sphere n) (Metric.sphere (0 : N) 1) ∞ := by
  let _ : Fact (Module.finrank ℝ (Smale.Hemisphere.Ambient (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let b := (stdOrthonormalBasis ℝ N).reindex (finCongr (Fact.out : Module.finrank ℝ N = n + 1))
  exact ofLinearIsometry b.repr.symm

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.MorseSurgeryData.transportedAttachingSphere {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p q : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (d' : Smale.ManifoldMorse.MorseSurgeryData E f q) (n : ℕ)
    [Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = n + 1)]
    (e : d.UpperLevel ≃ₜ d'.LowerLevel) : C(Smale.Hemisphere.Sphere n, d.UpperLevel) :=
  ⟨fun x =>
    e.symm
      (d'.surgery.attachingSphere
        (Smale.SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates n x)),
    e.symm.continuous.comp
      (d'.surgery.attachingSphere.continuous.comp
        (Smale.SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates
            n).continuous)⟩

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.transportedAttachingSphere_apply {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p q : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (d' : Smale.ManifoldMorse.MorseSurgeryData E f q) (n : ℕ)
    [Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = n + 1)]
    (e : d.UpperLevel ≃ₜ d'.LowerLevel) (x : Smale.Hemisphere.Sphere n) :
    e (d.transportedAttachingSphere d' n e x) =
      d'.surgery.attachingSphere
        (Smale.SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates n x) :=
  e.apply_symm_apply _

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.range_transportedAttachingSphere {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p q : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (d' : Smale.ManifoldMorse.MorseSurgeryData E f q) (n : ℕ)
    [Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = n + 1)]
    (e : d.UpperLevel ≃ₜ d'.LowerLevel) :
    Set.range (d.transportedAttachingSphere d' n e) =
      e ⁻¹' Set.range d'.surgery.attachingSphere := by
  let s := Smale.SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates n
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨s x, (d.transportedAttachingSphere_apply d' n e x).symm⟩
  · rintro ⟨z, hz⟩
    obtain ⟨x, hx⟩ := s.surjective z
    refine ⟨x, e.injective ?_⟩
    rw [d.transportedAttachingSphere_apply d' n e]
    exact (congrArg d'.surgery.attachingSphere hx).trans hz

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.transportedAttachingSphere_smooth {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p q : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (d' : Smale.ManifoldMorse.MorseSurgeryData E f q) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    [Fact (Module.finrank ℝ d'.chart.NegativeCoordinates = n + 1)] :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    letI := Smale.RegularLevel.chartedSpace hf d'.lower_regular
    ∀ e :
      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E) d.UpperLevel
        d'.LowerLevel ∞,
      ContMDiff (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞
        (d.transportedAttachingSphere d' n e.toHomeomorph) := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  let _ := Smale.RegularLevel.chartedSpace hf d'.lower_regular
  intro e
  exact
    e.symm.contMDiff.comp
      ((d'.attaching_smooth hf n).comp
        (Smale.SphereCoordinates.standardParametrization d'.chart.NegativeCoordinates
            n).contMDiff)

private theorem Smale.ManifoldMorse.MorseSurgeryData.exists_smoothBandBridge {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p q : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (d' : Smale.ManifoldMorse.MorseSurgeryData E f q) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) [T2Space M] [CompactSpace M]
    (hgap : f p + d.radius ^ 2 ≤ f q - d'.radius ^ 2)
    (hband :
      ∀ x,
        f x ∈ Set.Icc (f p + d.radius ^ 2) (f q - d'.radius ^ 2) →
          x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    letI := Smale.RegularLevel.chartedSpace hf d'.lower_regular
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      ∃ e :
        Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E) d.UpperLevel
          d'.LowerLevel ∞,
        D '' {x : M | f x ≤ f p + d.radius ^ 2} = {x : M | f x ≤ f q - d'.radius ^ 2} ∧
          ∀ x : d.UpperLevel, (e x : M) = D x := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  let _ := Smale.RegularLevel.chartedSpace hf d'.lower_regular
  obtain ⟨D, hlevel, hsublevel⟩ :=
    Smale.RegularLevel.exists_ambient_regularBand_transport hf hgap hband
  obtain ⟨e, he⟩ :=
    Smale.RegularLevel.exists_levelDiffeomorph_of_ambient hf d.upper_regular d'.lower_regular D
      hlevel
  exact ⟨D, e, hsublevel, he⟩

attribute [local instance 100] Classical.propDecidable in
private structure
    Smale.ManifoldMorse.SurgeryWindows (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) where
  finite : (criticalPoints E f).Finite
  distinct : Set.InjOn f (criticalPoints E f)
  data : ∀ p : criticalPoints E f, MorseSurgeryData E f p.val
  isolated :
    ∀ (p : criticalPoints E f) (x : M),
      x ∈ criticalPoints E f →
        f x ∈ Set.Icc (f p - (data p).radius ^ 2) (f p + (data p).radius ^ 2) → x = p.val
  separated :
    ∀ p q : criticalPoints E f, f p < f q → f p + (data p).radius ^ 2 < f q - (data q).radius ^ 2

private def Smale.ManifoldMorse.SurgeryWindows.lower {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (p : Smale.ManifoldMorse.criticalPoints E f) :
    ℝ :=
  f p - (S.data p).radius ^ 2

private def Smale.ManifoldMorse.SurgeryWindows.upper {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (p : Smale.ManifoldMorse.criticalPoints E f) :
    ℝ :=
  f p + (S.data p).radius ^ 2

private theorem
    Smale.ManifoldMorse.SurgeryWindows.lower_lt_value {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (p : Smale.ManifoldMorse.criticalPoints E f) :
    S.lower p < f p := by
  dsimp [Smale.ManifoldMorse.SurgeryWindows.lower]
  nlinarith [(S.data p).radius_pos]

private theorem
    Smale.ManifoldMorse.SurgeryWindows.value_lt_upper {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (p : Smale.ManifoldMorse.criticalPoints E f) :
    f p < S.upper p := by
  dsimp [Smale.ManifoldMorse.SurgeryWindows.upper]
  nlinarith [(S.data p).radius_pos]

private theorem
    Smale.ManifoldMorse.SurgeryWindows.upper_lt_lower {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hpq : f p < f q) : S.upper p < S.lower q :=
  S.separated p q hpq

private theorem
    Smale.ManifoldMorse.SurgeryWindows.regular_between {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hconsecutive : ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q)) :
    ∀ x, f x ∈ Set.Icc (S.upper p) (S.lower q) → x ∉ Smale.ManifoldMorse.criticalPoints E f := by
  intro x hx hcrit
  exact
    hconsecutive ⟨x, hcrit⟩
      ⟨(S.value_lt_upper p).trans_le hx.1, hx.2.trans_lt (S.lower_lt_value q)⟩

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SurgeryWindows.exists_bandBridge {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q)) :
    letI := Smale.RegularLevel.chartedSpace hf (S.data p).upper_regular
    letI := Smale.RegularLevel.chartedSpace hf (S.data q).lower_regular
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      ∃ b :
        Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
          (S.data p).UpperLevel (S.data q).LowerLevel ∞,
        D '' {x : M | f x ≤ S.upper p} = {x : M | f x ≤ S.lower q} ∧
          ∀ x : (S.data p).UpperLevel, (b x : M) = D x :=
  (S.data p).exists_smoothBandBridge (S.data q) hf (S.upper_lt_lower p q hpq).le
    (S.regular_between p q hconsecutive)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.nonempty_surgeryWindows {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hinj : Set.InjOn f (criticalPoints E f)) :
    Nonempty (SurgeryWindows E f) := by
  obtain ⟨r, hr, hgap⟩ := exists_separated_value_radii (finite_criticalPoints hf hm) hinj
  have hex :
    ∀ p : criticalPoints E f,
      ∃ d : MorseSurgeryData E f p.val,
        d.radius < r p ∧
          ∀ x ∈ criticalPoints E f,
            f x ∈ Set.Icc (f p - d.radius ^ 2) (f p + d.radius ^ 2) → x = p.val := by
    intro p
    exact
      exists_morseSurgeryData_lt hf hm p.property (fun x hx hfx => hinj hx p.property hfx) (hr p)
  choose d hd hisolated using hex
  refine
    ⟨{  finite := finite_criticalPoints hf hm
        distinct := hinj
        data := d
        isolated := hisolated
        separated := ?_ }⟩
  intro p q hpq
  have hp : (d p).radius ^ 2 < (r p) ^ 2 := by
    have h := mul_pos (sub_pos.mpr (hd p)) (add_pos (hr p) (d p).radius_pos)
    nlinarith
  have hq : (d q).radius ^ 2 < (r q) ^ 2 := by
    have h := mul_pos (sub_pos.mpr (hd q)) (add_pos (hr q) (d q).radius_pos)
    nlinarith
  linarith [hgap p q hpq]

attribute [local instance 100] Classical.propDecidable in
private structure AdaptedWindows (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (f : M → ℝ) extends
    Smale.ManifoldMorse.SurgeryWindows E f where
  field : (x : M) → TangentSpace 𝓘(ℝ, E) x
  flow : Flow ℝ M
  smooth :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, field x⟩ : TangentBundle 𝓘(ℝ, E) M))
  integral : ∀ x, IsMIntegralCurve (fun t => flow t x) field
  zero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, field x = 0
  descent : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (field x) < 0
  model_germ :
    ∀ (p : Smale.ManifoldMorse.criticalPoints E f) z,
      z ∈
          Metric.closedBall (0 : (data p).chart.NegativeCoordinates) (2 * (data p).radius) ×ˢ
            Metric.closedBall (0 : (data p).chart.PositiveCoordinates) (2 * (data p).radius) →
        ∀ᶠ y in 𝓝 ((data p).chart.splitChart.symm z), field y = (data p).chart.descentField y

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.nonempty_adaptedSurgeryWindows {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f)) :
    Nonempty (AdaptedWindows E f) := by
  have hfinite := Smale.ManifoldMorse.finite_criticalPoints hf hm
  let : Finite (Smale.ManifoldMorse.criticalPoints E f) := hfinite.to_subtype
  obtain ⟨r, hr, hgap⟩ := Smale.ManifoldMorse.exists_separated_value_radii hfinite hinj
  have hex :
    ∀ p : Smale.ManifoldMorse.criticalPoints E f,
      ∃ d : Smale.ManifoldMorse.MorseSurgeryData E f p.val,
        d.radius < r p / 3 ∧
          ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
            f x ∈ Set.Icc (f p - d.radius ^ 2) (f p + d.radius ^ 2) → x = p.val := by
    intro p
    exact
      Smale.ManifoldMorse.exists_morseSurgeryData_lt hf hm p.property
        (fun x hx hfx => hinj hx p.property hfx) (div_pos (hr p) (by norm_num))
  choose d hd hisolated using hex
  have hsq (p : Smale.ManifoldMorse.criticalPoints E f) : 9 * (d p).radius ^ 2 < (r p) ^ 2 := by
    have hsmall : 3 * (d p).radius < r p := by linarith [hd p]
    have hsum : 0 < r p + 3 * (d p).radius :=
      add_pos (hr p) (mul_pos (by norm_num) (d p).radius_pos)
    nlinarith [mul_pos (sub_pos.mpr hsmall) hsum]
  have hwide (p q : Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q) :
    f p + 9 * (d p).radius ^ 2 < f q - 9 * (d q).radius ^ 2 := by
    linarith [hgap p q hpq, hsq p, hsq q]
  have hintervals :
    Pairwise
      (fun p q : Smale.ManifoldMorse.criticalPoints E f =>
        Disjoint (Set.Icc (f p - 9 * (d p).radius ^ 2) (f p + 9 * (d p).radius ^ 2))
          (Set.Icc (f q - 9 * (d q).radius ^ 2) (f q + 9 * (d q).radius ^ 2))) := by
    intro p q hpq
    have hne : f p ≠ f q := fun h => hpq (Subtype.ext (hinj p.property q.property h))
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · linarith [hwide p q hlt, hx.2, hy.1]
    · linarith [hwide q p hgt, hy.2, hx.1]
  obtain ⟨V, F, hV, hF, hzero, hdesc, hmodel⟩ :=
    exists_disjoint_surgery_block_field hf hm
      (fun p : Smale.ManifoldMorse.criticalPoints E f => p.val) (fun p => p.property)
      (fun p => (d p).chart) (fun p => (d p).radius) (fun p => (d p).radius_pos)
      (fun p => (d p).block) hintervals
  refine
    ⟨{  finite := hfinite
        distinct := hinj
        data := d
        isolated := hisolated
        separated := ?_
        field := V
        flow := F
        smooth := hV
        integral := hF
        zero := hzero
        descent := hdesc
        model_germ := hmodel }⟩
  intro p q hpq
  nlinarith [hwide p q hpq, sq_nonneg (d p).radius, sq_nonneg (d q).radius]

private theorem MorseCancel.exists_forward_morse_model_exit {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {r : ℝ} (hr : 0 < r) {z : N × P}
    (hzn : ‖z.1‖ < r) (hzp : ‖z.2‖ < r) (hne : z.1 ≠ 0) :
    ∃ T : ℝ,
      0 < T ∧
        (∀ t ∈ Set.Icc (0 : ℝ) T,
            Smale.MorseHandle.descentFlow t z ∈
              Metric.closedBall (0 : N) r ×ˢ Metric.closedBall (0 : P) r) ∧
          Smale.MorseHandle.quadratic (Smale.MorseHandle.descentFlow T z) < 0 := by
  let T := Real.log (r / ‖z.1‖)
  have hn : 0 < ‖z.1‖ := norm_pos_iff.mpr hne
  have hratio : 1 < r / ‖z.1‖ := (one_lt_div hn).mpr hzn
  have hT : 0 < T := Real.log_pos hratio
  have hexp : Real.exp T = r / ‖z.1‖ := Real.exp_log (div_pos hr hn)
  have hnorm : ‖(Smale.MorseHandle.descentFlow T z).1‖ = r := by
    rw [Smale.MorseHandle.norm_descentFlow_fst, hexp]
    exact div_mul_cancel₀ r hn.ne'
  have hsmall : ‖(Smale.MorseHandle.descentFlow T z).2‖ < r :=
    (Smale.MorseHandle.norm_snd_descentFlow_le hT.le z).trans_lt hzp
  refine ⟨T, hT, ?_, ?_⟩
  · intro t ht
    constructor
    · rw [mem_closedBall_zero_iff, Smale.MorseHandle.norm_descentFlow_fst]
      calc
        Real.exp t * ‖z.1‖ ≤ Real.exp T * ‖z.1‖ :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ht.2) (norm_nonneg _)
        _ = r := by rw [hexp, div_mul_cancel₀ r hn.ne']
    · exact
        mem_closedBall_zero_iff.mpr
          ((Smale.MorseHandle.norm_snd_descentFlow_le ht.1 z).trans hzp.le)
  · change
      -‖(Smale.MorseHandle.descentFlow T z).1‖ ^ 2 + ‖(Smale.MorseHandle.descentFlow T z).2‖ ^ 2 <
        0
    rw [hnorm]
    have hs := (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr hsmall
    linarith

private theorem MorseCancel.exists_backward_morse_model_exit {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {r : ℝ} (hr : 0 < r) {z : N × P}
    (hzn : ‖z.1‖ < r) (hzp : ‖z.2‖ < r) (hne : z.2 ≠ 0) :
    ∃ T : ℝ,
      T < 0 ∧
        (∀ t ∈ Set.Icc T (0 : ℝ),
            Smale.MorseHandle.descentFlow t z ∈
              Metric.closedBall (0 : N) r ×ˢ Metric.closedBall (0 : P) r) ∧
          0 < Smale.MorseHandle.quadratic (Smale.MorseHandle.descentFlow T z) := by
  let T := -Real.log (r / ‖z.2‖)
  have hn : 0 < ‖z.2‖ := norm_pos_iff.mpr hne
  have hratio : 1 < r / ‖z.2‖ := (one_lt_div hn).mpr hzp
  have hT : T < 0 := neg_neg_of_pos (Real.log_pos hratio)
  have hexp : Real.exp (-T) = r / ‖z.2‖ := by
    dsimp [T]
    rw [neg_neg, Real.exp_log (div_pos hr hn)]
  have hnorm : ‖(Smale.MorseHandle.descentFlow T z).2‖ = r := by
    rw [Smale.MorseHandle.norm_descentFlow_snd, hexp]
    exact div_mul_cancel₀ r hn.ne'
  have hsmall (t : ℝ) (ht : t ≤ 0) : ‖(Smale.MorseHandle.descentFlow t z).1‖ < r := by
    rw [Smale.MorseHandle.norm_descentFlow_fst]
    exact (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr ht)).trans_lt hzn
  refine ⟨T, hT, ?_, ?_⟩
  · intro t ht
    constructor
    · exact mem_closedBall_zero_iff.mpr (hsmall t ht.2).le
    · rw [mem_closedBall_zero_iff, Smale.MorseHandle.norm_descentFlow_snd]
      calc
        Real.exp (-t) * ‖z.2‖ ≤ Real.exp (-T) * ‖z.2‖ :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg ht.1)) (norm_nonneg _)
        _ = r := by rw [hexp, div_mul_cancel₀ r hn.ne']
  · change
      0 <
        -‖(Smale.MorseHandle.descentFlow T z).1‖ ^ 2 + ‖(Smale.MorseHandle.descentFlow T z).2‖ ^ 2
    rw [hnorm]
    have hs := (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr (hsmall T hT.le)
    linarith

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.exists_native_morse_field_block {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    ∃ r : ℝ,
      0 < r ∧
        Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
              Metric.closedBall (0 : c.PositiveCoordinates) r ⊆
            c.splitChart.target ∧
          ∀
            z ∈
              Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
                Metric.closedBall (0 : c.PositiveCoordinates) r,
            ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y := by
  have h0 : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ c.splitChart.target := by
    rw [← c.splitChart_center]
    exact c.splitChart.map_source' c.splitChart_mem_source
  have hcenter : c.splitChart.symm 0 = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have hcont :
    Filter.Tendsto c.splitChart.symm (𝓝 (0 : c.NegativeCoordinates × c.PositiveCoordinates))
      (𝓝 p) := by
    have hh :
      Filter.Tendsto c.splitChart.symm (𝓝 (0 : c.NegativeCoordinates × c.PositiveCoordinates))
        (𝓝 (c.splitChart.symm 0)) :=
      c.splitChart.toOpenPartialHomeomorph.symm.continuousAt h0
    rwa [hcenter] at hh
  have htarget :
    ∀ᶠ z in 𝓝 (0 : c.NegativeCoordinates × c.PositiveCoordinates), z ∈ c.splitChart.target :=
    c.splitChart.open_target.mem_nhds h0
  have hgerm : ∀ᶠ y in 𝓝 p, ∀ᶠ x in 𝓝 y, V x = c.descentField x :=
    eventually_eventually_nhds.mpr heq
  obtain ⟨r, hr, hsub⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp (htarget.and (hcont.eventually hgerm))
  have hblock (z)
    (hz :
      z ∈
        Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) r) :=
    hsub
      (by
        rw [closedBall_prod_same] at hz
        convert! hz using 1)
  exact ⟨r, hr, fun z hz => (hblock z hz).1, fun z hz => (hblock z hz).2⟩

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.exists_native_forward_morse_exit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {r : ℝ} (hr : 0 < r)
    (hbox :
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) r ⊆
        c.splitChart.target)
    (heq :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) r,
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {x : M} (hx : x ∈ c.splitChart.source) (hn : ‖(c.splitChart x).1‖ < r)
    (hp : ‖(c.splitChart x).2‖ < r) (hne : (c.splitChart x).1 ≠ 0) :
    ∃ T : ℝ, 0 < T ∧ f (F T x) < f p := by
  obtain ⟨T, hT, hstay, hheight⟩ := exists_forward_morse_model_exit hr hn hp hne
  have hdomain (s : ℝ) (hs : s ∈ Set.uIcc (0 : ℝ) T) :
    Smale.MorseHandle.descentFlow s (c.splitChart x) ∈
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) r :=
    hstay s (by simpa only [Set.uIcc_of_le hT.le] using hs)
  have hflow :=
    c.flow_eq_descentModel_of_mem_uIcc hV F hF hx (fun s hs => hbox (hdomain s hs))
      (fun s hs => heq _ (hdomain s hs))
  refine ⟨T, hT, ?_⟩
  rw [hflow, c.splitChart_inverse_equation (hbox (hstay T ⟨hT.le, le_rfl⟩))]
  change
    -‖(Smale.MorseHandle.descentFlow T (c.splitChart x)).1‖ ^ 2 +
        ‖(Smale.MorseHandle.descentFlow T (c.splitChart x)).2‖ ^ 2 <
      0 at hheight
  linarith

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.exists_native_backward_morse_exit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {r : ℝ} (hr : 0 < r)
    (hbox :
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) r ⊆
        c.splitChart.target)
    (heq :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) r,
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {x : M} (hx : x ∈ c.splitChart.source) (hn : ‖(c.splitChart x).1‖ < r)
    (hp : ‖(c.splitChart x).2‖ < r) (hne : (c.splitChart x).2 ≠ 0) :
    ∃ T : ℝ, T < 0 ∧ f p < f (F T x) := by
  obtain ⟨T, hT, hstay, hheight⟩ := exists_backward_morse_model_exit hr hn hp hne
  have hdomain (s : ℝ) (hs : s ∈ Set.uIcc (0 : ℝ) T) :
    Smale.MorseHandle.descentFlow s (c.splitChart x) ∈
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) r :=
    hstay s (by simpa only [Set.uIcc_of_ge hT.le] using hs)
  have hflow :=
    c.flow_eq_descentModel_of_mem_uIcc hV F hF hx (fun s hs => hbox (hdomain s hs))
      (fun s hs => heq _ (hdomain s hs))
  refine ⟨T, hT, ?_⟩
  rw [hflow, c.splitChart_inverse_equation (hbox (hstay T ⟨le_rfl, hT.le⟩))]
  change
    0 <
      -‖(Smale.MorseHandle.descentFlow T (c.splitChart x)).1‖ ^ 2 +
        ‖(Smale.MorseHandle.descentFlow T (c.splitChart x)).2‖ ^ 2 at hheight
  linarith

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.native_morse_positive_plane_limit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {r : ℝ} (hr : 0 < r)
    (hbox :
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) r ⊆
        c.splitChart.target)
    (heq :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) r,
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {x : M} (hx : x ∈ c.splitChart.source) (hp : ‖(c.splitChart x).2‖ < r)
    (hzero : (c.splitChart x).1 = 0) : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) := by
  have hstay (t : ℝ) (ht : t ∈ Set.Ici (0 : ℝ)) :
    Smale.MorseHandle.descentFlow t (c.splitChart x) ∈
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) r := by
    constructor
    · rw [mem_closedBall_zero_iff, Smale.MorseHandle.norm_descentFlow_fst, hzero, norm_zero,
        MulZeroClass.mul_zero]
      exact hr.le
    · exact
        mem_closedBall_zero_iff.mpr
          ((Smale.MorseHandle.norm_snd_descentFlow_le ht (c.splitChart x)).trans hp.le)
  have hflow :=
    c.flow_eqOn_descentModel hV F hF hx isPreconnected_Ici (le_refl (0 : ℝ))
      (fun t ht => hbox (hstay t ht)) (fun t ht => heq _ (hstay t ht))
  have hfirst :
    Filter.Tendsto (fun t : ℝ => Real.exp t • (c.splitChart x).1) Filter.atTop
      (𝓝 (0 : c.NegativeCoordinates)) := by
    simp only [hzero, smul_zero]
    exact tendsto_const_nhds
  have hsecond :
    Filter.Tendsto (fun t : ℝ => Real.exp (-t) • (c.splitChart x).2) Filter.atTop
      (𝓝 (0 : c.PositiveCoordinates)) := by
    simpa only [Function.comp_def, zero_smul] using
      (Real.tendsto_exp_atBot.comp Filter.tendsto_neg_atTop_atBot).smul_const (c.splitChart x).2
  have hlim :
    Filter.Tendsto (fun t => Smale.MorseHandle.descentFlow t (c.splitChart x)) Filter.atTop
      (𝓝 (0 : c.NegativeCoordinates × c.PositiveCoordinates)) :=
    hfirst.prodMk_nhds hsecond
  have h0 : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ c.splitChart.target :=
    hbox ⟨Metric.mem_closedBall_self hr.le, Metric.mem_closedBall_self hr.le⟩
  have hcenter : c.splitChart.symm 0 = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have hn :
    Filter.Tendsto (fun t => c.splitChart.symm (Smale.MorseHandle.descentFlow t (c.splitChart x)))
      Filter.atTop (𝓝 (c.splitChart.symm 0)) :=
    c.splitChart.toOpenPartialHomeomorph.symm.continuousAt h0 |>.tendsto.comp hlim
  rw [hcenter] at hn
  apply hn.congr'
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  exact (hflow ht).symm

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.native_morse_negative_plane_limit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {r : ℝ} (hr : 0 < r)
    (hbox :
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) r ⊆
        c.splitChart.target)
    (heq :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) r,
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {x : M} (hx : x ∈ c.splitChart.source) (hn : ‖(c.splitChart x).1‖ < r)
    (hzero : (c.splitChart x).2 = 0) : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p) := by
  have hstay (t : ℝ) (ht : t ∈ Set.Iic (0 : ℝ)) :
    Smale.MorseHandle.descentFlow t (c.splitChart x) ∈
      Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) r := by
    constructor
    · rw [mem_closedBall_zero_iff, Smale.MorseHandle.norm_descentFlow_fst]
      exact (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr ht)).trans hn.le
    · rw [mem_closedBall_zero_iff, Smale.MorseHandle.norm_descentFlow_snd, hzero, norm_zero,
        MulZeroClass.mul_zero]
      exact hr.le
  have hflow :=
    c.flow_eqOn_descentModel hV F hF hx isPreconnected_Iic (le_refl (0 : ℝ))
      (fun t ht => hbox (hstay t ht)) (fun t ht => heq _ (hstay t ht))
  have hfirst :
    Filter.Tendsto (fun t : ℝ => Real.exp t • (c.splitChart x).1) Filter.atBot
      (𝓝 (0 : c.NegativeCoordinates)) := by
    simpa only [zero_smul] using Real.tendsto_exp_atBot.smul_const (c.splitChart x).1
  have hsecond :
    Filter.Tendsto (fun t : ℝ => Real.exp (-t) • (c.splitChart x).2) Filter.atBot
      (𝓝 (0 : c.PositiveCoordinates)) := by
    simp only [hzero, smul_zero]
    exact tendsto_const_nhds
  have hlim :
    Filter.Tendsto (fun t => Smale.MorseHandle.descentFlow t (c.splitChart x)) Filter.atBot
      (𝓝 (0 : c.NegativeCoordinates × c.PositiveCoordinates)) :=
    hfirst.prodMk_nhds hsecond
  have h0 : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ c.splitChart.target :=
    hbox ⟨Metric.mem_closedBall_self hr.le, Metric.mem_closedBall_self hr.le⟩
  have hcenter : c.splitChart.symm 0 = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have hh :
    Filter.Tendsto (fun t => c.splitChart.symm (Smale.MorseHandle.descentFlow t (c.splitChart x)))
      Filter.atBot (𝓝 (c.splitChart.symm 0)) :=
    c.splitChart.toOpenPartialHomeomorph.symm.continuousAt h0 |>.tendsto.comp hlim
  rw [hcenter] at hh
  apply hh.congr'
  filter_upwards [Filter.eventually_le_atBot (0 : ℝ)] with t ht
  exact (hflow ht).symm

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.exists_native_morse_basin_block {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : Continuous f) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    ∃ r : ℝ,
      0 < r ∧
        Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
              Metric.closedBall (0 : c.PositiveCoordinates) r ⊆
            c.splitChart.target ∧
          ∀ x ∈ c.splitChart.source,
            ‖(c.splitChart x).1‖ < r →
              ‖(c.splitChart x).2‖ < r →
                (Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) ↔ (c.splitChart x).1 = 0) ∧
                  (Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p) ↔ (c.splitChart x).2 = 0) :=
  by
  obtain ⟨r, hr, hbox, hfield⟩ := exists_native_morse_field_block c heq
  refine ⟨r, hr, hbox, ?_⟩
  intro x hx hn hp
  constructor
  · constructor
    · intro hlim
      by_contra hne
      obtain ⟨T, hT, hexit⟩ :=
        exists_native_forward_morse_exit c hV F hF hr hbox hfield hx hn hp hne
      have hheight : Filter.Tendsto (fun t => f (F t x)) Filter.atTop (𝓝 (f p)) :=
        hf.continuousAt.tendsto.comp hlim
      exact (not_lt_of_ge ((hmono x).le_of_tendsto hheight T)) hexit
    · exact native_morse_positive_plane_limit c hV F hF hr hbox hfield hx hp
  · constructor
    · intro hlim
      by_contra hne
      obtain ⟨T, hT, hexit⟩ :=
        exists_native_backward_morse_exit c hV F hF hr hbox hfield hx hn hp hne
      have hheight : Filter.Tendsto (fun t => f (F t x)) Filter.atBot (𝓝 (f p)) :=
        hf.continuousAt.tendsto.comp hlim
      exact (not_lt_of_ge ((hmono x).ge_of_tendsto hheight T)) hexit
    · exact native_morse_negative_plane_limit c hV F hF hr hbox hfield hx hn

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.exists_descending_morse_basin_block {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    ∃ r : ℝ,
      0 < r ∧
        Metric.closedBall (0 : c.NegativeCoordinates) r ×ˢ
              Metric.closedBall (0 : c.PositiveCoordinates) r ⊆
            c.splitChart.target ∧
          ∀ x ∈ c.splitChart.source,
            ‖(c.splitChart x).1‖ < r →
              ‖(c.splitChart x).2‖ < r →
                (Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) ↔ (c.splitChart x).1 = 0) ∧
                  (Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p) ↔ (c.splitChart x).2 = 0) :=
  exists_native_morse_basin_block c hf.continuous hV F hF
    (Smale.FlowConstruction.antitone_flow_height hf F hF hzero hdesc) heq

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.native_attaching_core_backward_limit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (r : ℝ) (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (hfield :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (u : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates) :
    Filter.Tendsto (fun t => F t (c.attachingCoreMap r hr hblock u)) Filter.atBot (𝓝 p) := by
  have hu : ‖(u : c.NegativeCoordinates)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  have hn : ‖r • (u : c.NegativeCoordinates)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu, mul_one]
  have hcoords :
    (r • (u : c.NegativeCoordinates), (0 : c.PositiveCoordinates)) ∈ c.splitChart.target := by
    apply hblock
    constructor
    · rw [mem_closedBall_zero_iff, hn]
      linarith
    · rw [mem_closedBall_zero_iff, norm_zero]
      positivity
  have hcoord :
    c.splitChart
        (c.splitChart.symm (r • (u : c.NegativeCoordinates), (0 : c.PositiveCoordinates))) =
      (r • (u : c.NegativeCoordinates), 0) :=
    c.splitChart.right_inv' hcoords
  have hh :=
    native_morse_negative_plane_limit c hV F hF (x :=
      c.splitChart.symm (r • (u : c.NegativeCoordinates), (0 : c.PositiveCoordinates)))
      (show 0 < 2 * r by positivity) hblock hfield (c.splitChart.map_target' hcoords)
      (by rw [hcoord]; change ‖r • (u : c.NegativeCoordinates)‖ < 2 * r; rw [hn]; linarith)
      (by rw [hcoord])
  simpa only [c.attachingCoreMap_coe] using hh

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.native_belt_core_forward_limit {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (r : ℝ) (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (hfield :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (v : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates) :
    Filter.Tendsto (fun t => F t (c.beltCoreMap r hr hblock v)) Filter.atTop (𝓝 p) := by
  have hv : ‖(v : c.PositiveCoordinates)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  have hn : ‖r • (v : c.PositiveCoordinates)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hv, mul_one]
  have hcoords :
    ((0 : c.NegativeCoordinates), r • (v : c.PositiveCoordinates)) ∈ c.splitChart.target := by
    apply hblock
    constructor
    · rw [mem_closedBall_zero_iff, norm_zero]
      positivity
    · rw [mem_closedBall_zero_iff, hn]
      linarith
  have hcoord :
    c.splitChart
        (c.splitChart.symm ((0 : c.NegativeCoordinates), r • (v : c.PositiveCoordinates))) =
      (0, r • (v : c.PositiveCoordinates)) :=
    c.splitChart.right_inv' hcoords
  have hh :=
    native_morse_positive_plane_limit c hV F hF (x :=
      c.splitChart.symm ((0 : c.NegativeCoordinates), r • (v : c.PositiveCoordinates)))
      (show 0 < 2 * r by positivity) hblock hfield (c.splitChart.map_target' hcoords)
      (by rw [hcoord]; change ‖r • (v : c.PositiveCoordinates)‖ < 2 * r; rw [hn]; linarith)
      (by rw [hcoord])
  simpa only [c.beltCoreMap_coe] using hh

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.native_attaching_core_flow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (r : ℝ) (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (hfield :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (u : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates) {t : ℝ} (ht : t ≤ 0) :
    F t (c.attachingCoreMap r hr hblock u) =
      c.splitChart.symm (Smale.MorseHandle.descentFlow t (r • (u : c.NegativeCoordinates), 0)) := by
  let z : c.NegativeCoordinates × c.PositiveCoordinates := (r • (u : c.NegativeCoordinates), 0)
  have hn : ‖z.1‖ = r := by
    change ‖r • (u : c.NegativeCoordinates)‖ = r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp u.property,
      mul_one]
  have hstay (s : ℝ) (hs : s ≤ 0) :
    Smale.MorseHandle.descentFlow s z ∈
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) := by
    constructor
    · rw [mem_closedBall_zero_iff, Smale.MorseHandle.norm_descentFlow_fst, hn]
      have hh := mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr hs) hr.le
      nlinarith
    · rw [mem_closedBall_zero_iff, Smale.MorseHandle.norm_descentFlow_snd]
      change Real.exp (-s) * ‖(0 : c.PositiveCoordinates)‖ ≤ 2 * r
      simp only [norm_zero, MulZeroClass.mul_zero]
      positivity
  have hz : z ∈ c.splitChart.target := by
    have hh := hblock (hstay 0 le_rfl)
    simpa only [Flow.map_zero_apply] using hh
  have hcoord : c.splitChart (c.splitChart.symm z) = z := c.splitChart.right_inv' hz
  have hflow :=
    c.flow_eqOn_descentModel hV F hF (x := c.splitChart.symm z) (c.splitChart.map_target' hz)
      isPreconnected_Iic (le_refl (0 : ℝ)) (fun s hs => by rw [hcoord]; exact hblock (hstay s hs))
      (fun s hs => by rw [hcoord]; exact hfield _ (hstay s hs))
  have hh := hflow ht
  rw [hcoord] at hh
  simpa only [c.attachingCoreMap_coe] using hh

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.native_belt_core_flow {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (r : ℝ) (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (hfield :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (v : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates) {t : ℝ} (ht : 0 ≤ t) :
    F t (c.beltCoreMap r hr hblock v) =
      c.splitChart.symm (Smale.MorseHandle.descentFlow t (0, r • (v : c.PositiveCoordinates))) := by
  let z : c.NegativeCoordinates × c.PositiveCoordinates := (0, r • (v : c.PositiveCoordinates))
  have hn : ‖z.2‖ = r := by
    change ‖r • (v : c.PositiveCoordinates)‖ = r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp v.property,
      mul_one]
  have hstay (s : ℝ) (hs : 0 ≤ s) :
    Smale.MorseHandle.descentFlow s z ∈
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) := by
    constructor
    · rw [mem_closedBall_zero_iff, Smale.MorseHandle.norm_descentFlow_fst]
      change Real.exp s * ‖(0 : c.NegativeCoordinates)‖ ≤ 2 * r
      simp only [norm_zero, MulZeroClass.mul_zero]
      positivity
    · rw [mem_closedBall_zero_iff, Smale.MorseHandle.norm_descentFlow_snd, hn]
      have hh := mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs)) hr.le
      nlinarith
  have hz : z ∈ c.splitChart.target := by
    have hh := hblock (hstay 0 le_rfl)
    simpa only [Flow.map_zero_apply] using hh
  have hcoord : c.splitChart (c.splitChart.symm z) = z := c.splitChart.right_inv' hz
  have hflow :=
    c.flow_eqOn_descentModel hV F hF (x := c.splitChart.symm z) (c.splitChart.map_target' hz)
      isPreconnected_Ici (le_refl (0 : ℝ)) (fun s hs => by rw [hcoord]; exact hblock (hstay s hs))
      (fun s hs => by rw [hcoord]; exact hfield _ (hstay s hs))
  have hh := hflow ht
  rw [hcoord] at hh
  simpa only [c.beltCoreMap_coe] using hh

private theorem MorseCancel.exists_negative_core_ray_parameter {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] {r : ℝ} (hr : 0 < r) {z : A} (hz : z ≠ 0) (hzr : ‖z‖ < r) :
    ∃ (u : Smale.PuncturedHandle.UnitSphere A) (t : ℝ), t < 0 ∧ Real.exp t • (r • (u : A)) = z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let u : Smale.PuncturedHandle.UnitSphere A :=
    ⟨‖z‖⁻¹ • z, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hz)⟩
  have hratio : 0 < ‖z‖ / r := div_pos hn hr
  have hratio1 : ‖z‖ / r < 1 := (div_lt_one hr).mpr hzr
  have hcoef : Real.exp (Real.log (‖z‖ / r)) * r * ‖z‖⁻¹ = 1 := by
    rw [Real.exp_log hratio]
    field_simp
  refine ⟨u, Real.log (‖z‖ / r), Real.log_neg hratio hratio1, ?_⟩
  change Real.exp (Real.log (‖z‖ / r)) • (r • (‖z‖⁻¹ • z)) = z
  rw [smul_smul, smul_smul, hcoef, one_smul]

private theorem MorseCancel.exists_positive_core_ray_parameter {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] {r : ℝ} (hr : 0 < r) {z : A} (hz : z ≠ 0) (hzr : ‖z‖ < r) :
    ∃ (u : Smale.PuncturedHandle.UnitSphere A) (t : ℝ),
      0 < t ∧ Real.exp (-t) • (r • (u : A)) = z := by
  obtain ⟨u, t, ht, heq⟩ := exists_negative_core_ray_parameter hr hz hzr
  exact ⟨u, -t, neg_pos.mpr ht, by simpa only [neg_neg] using heq⟩

private theorem
    Degree.FlowCancellation.exists_local_strict_flow_descent {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {x : X} (hx : D x < 0) :
    ∃ ε : ℝ, 0 < ε ∧ StrictAntiOn (fun t : ℝ => f (F t x)) (Set.Icc (-ε) ε) := by
  have hcont : Continuous (fun t : ℝ => D (F t x)) :=
    hD.comp (F.continuous continuous_id continuous_const)
  have he : ∀ᶠ t : ℝ in 𝓝 0, D (F t x) < 0 := by
    have hx0 : D (F 0 x) < 0 := by simpa only [F.map_zero_apply] using hx
    exact hcont.continuousAt (eventually_lt_nhds hx0)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r / 2, half_pos hr, ?_⟩
  have hfc : Continuous (fun t : ℝ => f (F t x)) :=
    hf.comp (F.continuous continuous_id continuous_const)
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hfc.continuousOn
  intro t ht
  rw [(hder x t).deriv]
  apply hball
  rw [Real.dist_eq, sub_zero, abs_lt]
  have ht' := interior_subset ht
  constructor <;> linarith [ht'.1, ht'.2]

private theorem Degree.FlowCancellation.exists_local_strict_sublevel_entry {X : Type*}
    [TopologicalSpace X] (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) {x : X} (hx : f x ≤ c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Ioc (0 : ℝ) ε, f (F t x) < c := by
  rcases hx.lt_or_eq with hx | hx
  · have he : ∀ᶠ t : ℝ in 𝓝 0, f (F t x) < c := by
      have hfc : Continuous (fun t : ℝ => f (F t x)) :=
        hf.comp (F.continuous continuous_id continuous_const)
      have hx0 : f (F 0 x) < c := by simpa only [F.map_zero_apply] using hx
      exact hfc.continuousAt (eventually_lt_nhds hx0)
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
    refine ⟨r / 2, half_pos hr, ?_⟩
    intro t ht
    apply hball
    rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
    linarith [ht.2]
  · obtain ⟨ε, hε, hanti⟩ := exists_local_strict_flow_descent F hf hD hder (hboundary x hx)
    refine ⟨ε, hε, ?_⟩
    intro t ht
    have hh :=
      hanti (show (0 : ℝ) ∈ Set.Icc (-ε) ε from ⟨by linarith, hε.le⟩)
        (show t ∈ Set.Icc (-ε) ε from ⟨by linarith [ht.1], ht.2⟩) ht.1
    simpa only [F.map_zero_apply, hx] using hh

private theorem Degree.FlowCancellation.forwardInvariant_sublevel_of_boundary {X : Type*}
    [TopologicalSpace X] (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) : ∀ x, f x ≤ c → ∀ t : ℝ, 0 ≤ t → f (F t x) ≤ c := by
  apply Smale.FlowConstruction.forwardInvariant_of_local F (isClosed_le hf continuous_const)
  intro x hx
  obtain ⟨ε, hε, hentry⟩ := exists_local_strict_sublevel_entry F hf hD hder hboundary hx
  refine ⟨ε, hε, ?_⟩
  intro t ht
  rcases ht.1.eq_or_lt with ht0 | htpos
  · simpa only [← ht0, F.map_zero_apply] using hx
  · exact (hentry t ⟨htpos, ht.2⟩).le

private theorem
    Degree.FlowCancellation.interior_sublevel_eq_of_boundary {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) : interior {x | f x ≤ c} = {x | f x < c} := by
  apply Set.Subset.antisymm
  · intro x hx
    have hle : f x ≤ c := (interior_subset : interior {y | f y ≤ c} ⊆ {y | f y ≤ c}) hx
    apply lt_of_le_of_ne hle
    intro heq
    have hnhds : ∀ᶠ t : ℝ in 𝓝 0, F t x ∈ interior {y | f y ≤ c} := by
      have hfc : Continuous (fun t : ℝ => F t x) := F.continuous continuous_id continuous_const
      have hx0 : F 0 x ∈ interior {y | f y ≤ c} := by simpa only [F.map_zero_apply] using hx
      exact hfc.continuousAt (isOpen_interior.mem_nhds hx0)
    have hmax : IsLocalMax (fun t : ℝ => f (F t x)) 0 := by
      filter_upwards [hnhds] with t ht
      change f (F t x) ≤ f (F 0 x)
      rw [F.map_zero_apply, heq]
      exact (interior_subset : interior {y | f y ≤ c} ⊆ {y | f y ≤ c}) ht
    have hz := hmax.hasDerivAt_eq_zero (hder x 0)
    rw [F.map_zero_apply] at hz
    exact (hboundary x heq).ne hz
  · exact interior_maximal (fun _ (hx : f _ < c) => hx.le) (isOpen_lt hf continuous_const)

private theorem
    Degree.FlowCancellation.strict_sublevel_entry_of_boundary {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) : ∀ x, f x ≤ c → ∀ t : ℝ, 0 < t → f (F t x) < c := by
  have hforward := forwardInvariant_sublevel_of_boundary F hf hD hder hboundary
  have hlocal :
    ∀ x ∈ {y | f y ≤ c}, ∃ ε > (0 : ℝ), ∀ t ∈ Set.Ioc 0 ε, F t x ∈ interior {y | f y ≤ c} := by
    intro x hx
    obtain ⟨ε, hε, hentry⟩ := exists_local_strict_sublevel_entry F hf hD hder hboundary hx
    refine ⟨ε, hε, ?_⟩
    intro t ht
    rw [interior_sublevel_eq_of_boundary F hf hder hboundary]
    exact hentry t ht
  intro x hx t ht
  have hi := Smale.FlowConstruction.interior_entry_of_local F hforward hlocal x hx t ht
  have hi' : F t x ∈ interior {y | f y ≤ c} := hi
  exact
    Eq.mp
      (congrArg (fun S : Set X => F t x ∈ S)
        (interior_sublevel_eq_of_boundary F hf hder hboundary))
      hi'

private def
    Degree.FlowCancellation.levelBasin {X : Type*} [TopologicalSpace X] (F : Flow ℝ X) (f : X → ℝ)
    (c : ℝ) : Set X :=
  {x | ∃ t : ℝ, f (F t x) = c}

private def Degree.FlowCancellation.signedLevelTime {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (f : X → ℝ) (c : ℝ) (x : X) : ℝ := by
  classical exact if h : x ∈ levelBasin F f c then h.choose else 0

private theorem Degree.FlowCancellation.signedLevelTime_hits {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) (f : X → ℝ) (c : ℝ) {x : X} (hx : x ∈ levelBasin F f c) :
    f (F (signedLevelTime F f c x) x) = c := by
  rw [signedLevelTime, dite_eq_left hx]
  exact hx.choose_spec

private theorem Degree.FlowCancellation.levelBasin_flow_iff {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) (f : X → ℝ) (c s : ℝ) (x : X) :
    F s x ∈ levelBasin F f c ↔ x ∈ levelBasin F f c := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t + s, by simpa only [F.map_add] using ht⟩
  · rintro ⟨t, ht⟩
    refine ⟨t - s, ?_⟩
    simpa only [← F.map_add, sub_add_cancel] using ht

private theorem Degree.FlowCancellation.flow_level_time_unique {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) (x : X) {s t : ℝ} (hs : f (F s x) = c)
    (ht : f (F t x) = c) : s = t := by
  have hnot {a b : ℝ} (ha : f (F a x) = c) (hb : f (F b x) = c) : ¬a < b := by
    intro hab
    have hh :=
      strict_sublevel_entry_of_boundary F hf hD hder hboundary (F a x) ha.le (b - a)
        (sub_pos.mpr hab)
    rw [← F.map_add, sub_add_cancel, hb] at hh
    exact lt_irrefl _ hh
  exact le_antisymm (le_of_not_gt (hnot ht hs)) (le_of_not_gt (hnot hs ht))

private theorem Degree.FlowCancellation.signedLevelTime_eq_of_level {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) {x : X} {t : ℝ} (ht : f (F t x) = c) :
    signedLevelTime F f c x = t :=
  flow_level_time_unique F hf hD hder hboundary x (signedLevelTime_hits F f c ⟨t, ht⟩) ht

private theorem Degree.FlowCancellation.signedLevelTime_eq_zero {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) {x : X} (hx : f x = c) : signedLevelTime F f c x = 0 :=
  signedLevelTime_eq_of_level F hf hD hder hboundary (by simpa only [F.map_zero_apply] using hx)

private theorem Degree.FlowCancellation.signedLevelTime_flow {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) {x : X} (hx : x ∈ levelBasin F f c) (s : ℝ) :
    signedLevelTime F f c (F s x) = signedLevelTime F f c x - s := by
  apply signedLevelTime_eq_of_level F hf hD hder hboundary
  rw [← F.map_add, sub_add_cancel]
  exact signedLevelTime_hits F f c hx

private theorem Smale.FlowConstruction.exists_enlarged_interval {a b : ℝ} (hab : a ≤ b) {W : Set ℝ}
    (hW : IsOpen W) (hIW : Set.Icc a b ⊆ W) : ∃ l u : ℝ, l < a ∧ b < u ∧ Set.Ioo l u ⊆ W := by
  obtain ⟨l, r, hla, hL⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hW.mem_nhds (hIW ⟨le_rfl, hab⟩))
  obtain ⟨s, u, hbu, hR⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hW.mem_nhds (hIW ⟨hab, le_rfl⟩))
  refine ⟨l, u, hla.1, hbu.2, ?_⟩
  intro y hy
  by_cases hya : y < a
  · exact hL ⟨hy.1, hya.trans hla.2⟩
  by_cases hby : b < y
  · exact hR ⟨hbu.1.trans hby, hy.2⟩
  exact hIW ⟨le_of_not_gt hya, le_of_not_gt hby⟩

private theorem Smale.FlowConstruction.scalar_height_translation {φ γ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {W : Set ℝ} (hW : IsOpen W) {a b c t : ℝ} (hIW : Set.Icc a b ⊆ W)
    (hφW : Set.EqOn φ (fun _ => 1) W) (hγ : ∀ s, HasDerivAt γ (φ (γ s)) s) (hγ₀ : γ 0 = c)
    (hc : c ∈ Set.Icc a b) (ht : c + t ∈ Set.Icc a b) : γ t = c + t := by
  obtain ⟨l, u, hl, hu, hlu⟩ := exists_enlarged_interval (hc.1.trans hc.2) hW hIW
  let V : (x : ℝ) → TangentSpace 𝓘(ℝ, ℝ) x := fun x => (NormedSpace.fromTangentSpace x).symm (φ x)
  have hV :
    ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr (hφ.of_le (by simp))
  have hactual : IsMIntegralCurveOn γ V (Set.Ioo (l - c) (u - c)) := by
    intro s hs
    exact (hγ s).hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
  have hlinear : IsMIntegralCurveOn (fun s => c + s) V (Set.Ioo (l - c) (u - c)) := by
    intro s hs
    have hcs : c + s ∈ W := hlu ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hd : HasDerivAt (fun r => c + r) (φ (c + s)) s := by
      rw [hφW hcs]
      exact (hasDerivAt_id s).const_add c
    exact hd.hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
  have hzero : (0 : ℝ) ∈ Set.Ioo (l - c) (u - c) := ⟨by linarith [hc.1], by linarith [hc.2]⟩
  have htime : t ∈ Set.Ioo (l - c) (u - c) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hzero hV hactual hlinear
      (by simpa only [add_zero] using hγ₀) htime

private theorem
    Smale.FlowConstruction.exists_heightTranslatingFlow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    ∃ F : Flow ℝ M, ∀ x t, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b → f (F t x) = f x + t := by
  obtain ⟨φ, W, F, hφ, hW, hIW, hφW, hF⟩ := exists_regularBandFlow hf hband
  refine ⟨F, ?_⟩
  intro x t hx ht
  exact scalar_height_translation hφ hW hIW hφW (hF x) (by simp only [Flow.map_zero_apply]) hx ht

private theorem MorseCancel.contMDiff_directionalDerivative {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => mvfderiv 𝓘(ℝ, E) f x (V x)) := by
  have ht := (hf.contMDiff_tangentMap (m := ∞) (by simp)).comp hV
  exact (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp ht

private theorem MorseCancel.contMDiff_supported_division {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {χ D : M → ℝ}
    (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ χ) (hD : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ D)
    (hsupp : ∀ x ∈ tsupport χ, D x ≠ 0) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => χ x / D x) := by
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact (hχ x).div₀ (hD x) (hsupp x hx)
  · apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
    simp only [image_eq_zero_of_notMem_tsupport hy, zero_div]

private theorem MorseCancel.native_same_level_orbit_points {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ}
    (hboundary : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) {x y : M} {s t : ℝ} (hx : f x = c)
    (hy : f y = c) (hxy : F s x = F t y) : x = y := by
  have hmove : F (s - t) x = y := by
    calc
      F (s - t) x = F (-t) (F s x) := by
        rw [← F.map_add]
        congr 1
        ring
      _ = F (-t) (F t y) := (congrArg (F (-t)) hxy)
      _ = y := by rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  have htime :=
    Degree.FlowCancellation.flow_level_time_unique F hf.continuous
      (contMDiff_directionalDerivative hf hV).continuous
      (fun z u => Smale.FlowConstruction.hasDerivAt_comp_integralCurve hf (hF z) u) hboundary x
      (hmove ▸ hy) (show f (F 0 x) = c by rw [F.map_zero_apply]; exact hx)
  simpa only [htime, F.map_zero_apply] using hmove

private abbrev MorseCancel.Model (m : ℕ) :=
  ℝ × (Fin m → ℝ)

private def MorseCancel.cubic {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) : ℝ :=
  p.1 ^ 3 / 3 + t * p.1 + ∑ i, σ i * (p.2 i) ^ 2

private def
    MorseCancel.differential {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) : Model m →L[ℝ] ℝ :=
  (p.1 ^ 2 + t) • ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ) +
    ∑ i,
      (2 * σ i * p.2 i) •
        ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ)))

private theorem MorseCancel.differential_apply {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p v : Model m) :
    differential σ t p v = (p.1 ^ 2 + t) * v.1 + ∑ i, 2 * σ i * p.2 i * v.2 i := by
  simp [differential]

private theorem MorseCancel.contDiff_cubic_family {m : ℕ} (σ : Fin m → ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × Model m => cubic σ p.1 p.2) := by
  unfold cubic
  fun_prop

private theorem
    MorseCancel.contDiff_cubic {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) : ContDiff ℝ ∞ (cubic σ t) :=
  (contDiff_cubic_family σ).comp (contDiff_const.prodMk contDiff_id)

private theorem MorseCancel.hasFDerivAt_cubic {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) :
    HasFDerivAt (cubic σ t) (differential σ t p) p := by
  have hx := (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).hasFDerivAt (x := p)
  have hy (i : Fin m) :=
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))).hasFDerivAt
      (x := p)
  have hq := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => ((hy i).pow 2).const_mul (σ i))
  convert! (((hx.pow 3).mul_const (1 / 3)).add (hx.const_mul t)).add hq using 1
  · funext q
    simp [cubic, div_eq_mul_inv]
  · apply ContinuousLinearMap.ext
    intro v
    simp [differential]
    ring_nf

private theorem MorseCancel.fderiv_cubic {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) :
    fderiv ℝ (cubic σ t) p = differential σ t p :=
  (hasFDerivAt_cubic σ t p).fderiv

private theorem MorseCancel.critical_iff {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0) (t : ℝ)
    (p : Model m) : fderiv ℝ (cubic σ t) p = 0 ↔ p.1 ^ 2 + t = 0 ∧ p.2 = 0 := by
  rw [fderiv_cubic]
  constructor
  · intro h
    have hx := congrArg (fun L : Model m →L[ℝ] ℝ => L (1, 0)) h
    have hx' : p.1 ^ 2 + t = 0 := by simpa [differential_apply] using hx
    refine ⟨hx', ?_⟩
    funext i
    have hy := congrArg (fun L : Model m →L[ℝ] ℝ => L (0, Pi.single i 1)) h
    have hy' : 2 * σ i * p.2 i = 0 := by simpa [differential_apply, Pi.single_apply] using hy
    exact (mul_eq_zero.mp hy').resolve_left (mul_ne_zero (by norm_num) (hσ i))
  · rintro ⟨hx, hy⟩
    apply ContinuousLinearMap.ext
    intro v
    simp [differential_apply, hx, hy]

private theorem MorseCancel.cubic_zero_unique_critical {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    (p : Model m) : fderiv ℝ (cubic σ 0) p = 0 ↔ p = 0 := by
  rw [critical_iff σ hσ]
  constructor
  · rintro ⟨hx, hy⟩
    have hx' : p.1 = 0 := by nlinarith [sq_nonneg p.1]
    exact Prod.ext hx' hy
  · rintro rfl
    simp

private theorem
    MorseCancel.positive_parameter_no_critical {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    {t : ℝ} (ht : 0 < t) (p : Model m) : fderiv ℝ (cubic σ t) p ≠ 0 := by
  intro h
  have hx := ((critical_iff σ hσ t p).mp h).1
  nlinarith [sq_nonneg p.1]

private theorem
    MorseCancel.negative_parameter_critical_iff {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    (a : ℝ) (p : Model m) : fderiv ℝ (cubic σ (-(a ^ 2))) p = 0 ↔ p = (a, 0) ∨ p = (-a, 0) := by
  rw [critical_iff σ hσ]
  constructor
  · rintro ⟨hx, hy⟩
    have hs : p.1 = a ∨ p.1 = -a := by
      have he : (p.1 - a) * (p.1 + a) = 0 := by nlinarith
      rcases mul_eq_zero.mp he with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    exact hs.elim (fun h => Or.inl (Prod.ext h hy)) (fun h => Or.inr (Prod.ext h hy))
  · rintro (rfl | rfl) <;> simp

private theorem MorseCancel.cubic_critical_values {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) :
    cubic σ (-(a ^ 2)) (a, 0) = -(2 * a ^ 3 / 3) ∧ cubic σ (-(a ^ 2)) (-a, 0) = 2 * a ^ 3 / 3 := by
  constructor <;> simp [cubic] <;> ring

private def MorseCancel.endpointCoordinate (a e s : ℝ) : ℝ :=
  (s - e * a) * Real.sqrt (a + e * (s - e * a) / 3)

private def MorseCancel.endpointDomain (a e : ℝ) : Set ℝ :=
  {s | 0 < a + e * (s - e * a) / 3}

private theorem MorseCancel.endpointDomain_open (a e : ℝ) : IsOpen (endpointDomain a e) := by
  apply isOpen_lt continuous_const
  fun_prop

private theorem MorseCancel.endpoint_mem_domain {a : ℝ} (ha : 0 < a) (e : ℝ) :
    e * a ∈ endpointDomain a e := by simpa [endpointDomain] using ha

private theorem
    MorseCancel.endpointCoordinate_center (a e : ℝ) : endpointCoordinate a e (e * a) = 0 := by
  simp [endpointCoordinate]

private theorem MorseCancel.contDiffOn_endpointCoordinate (a e : ℝ) :
    ContDiffOn ℝ ∞ (endpointCoordinate a e) (endpointDomain a e) := by
  intro s hs
  have hlin : ContDiffAt ℝ ∞ (fun t : ℝ => t - e * a) s := contDiffAt_id.sub contDiffAt_const
  exact
    (hlin.mul
        ((contDiffAt_const.add ((contDiffAt_const.mul hlin).div_const 3)).sqrt
          (ne_of_gt hs))).contDiffWithinAt

private theorem MorseCancel.hasDerivAt_endpointCoordinate {a : ℝ} (ha : 0 < a) (e : ℝ) :
    HasDerivAt (endpointCoordinate a e) (Real.sqrt a) (e * a) := by
  have hd :=
    ((hasDerivAt_id (e * a)).sub_const (e * a)).mul
      ((((hasDerivAt_id (e * a)).sub_const (e * a)).const_mul e).div_const 3 |>.const_add
          a |>.sqrt
        (by simpa using ha.ne'))
  convert! hd using 1; simp []

private theorem MorseCancel.cubic_endpoint_square {m : ℕ} (σ : Fin m → ℝ) (a e : ℝ) (he : e ^ 2 = 1)
    {p : Model m} (hp : p.1 ∈ endpointDomain a e) :
    cubic σ (-(a ^ 2)) p =
      cubic σ (-(a ^ 2)) (e * a, 0) + e * endpointCoordinate a e p.1 ^ 2 + ∑ i, σ i * p.2 i ^ 2 :=
  by
  simp only [cubic, endpointCoordinate, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
    MulZeroClass.mul_zero, Finset.sum_const_zero, add_zero, mul_pow, Real.sq_sqrt (le_of_lt hp)]
  rcases sq_eq_one_iff.mp he with h | h <;> rw [h] <;> ring

private theorem MorseCancel.exists_endpoint_scalar_chart {a : ℝ} (ha : 0 < a) (e : ℝ) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      e * a ∈ Φ.source ∧
        Φ.source ⊆ endpointDomain a e ∧ (Φ : ℝ → ℝ) = endpointCoordinate a e ∧ Φ (e * a) = 0 := by
  have hd := (hasDerivAt_endpointCoordinate ha e).hasFDerivAt
  have hi : Function.Injective (fderiv ℝ (endpointCoordinate a e) (e * a)) := by
    rw [hd.fderiv]
    intro x y hxy
    change x * Real.sqrt a = y * Real.sqrt a at hxy
    exact mul_right_cancel₀ (Real.sqrt_pos.mpr ha).ne' hxy
  let A : ℝ ≃L[ℝ] ℝ :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ (endpointCoordinate a e) (e * a)).toLinearMap
        hi).toContinuousLinearEquiv
  obtain ⟨Φ, hp, hsub, hΦ⟩ :=
    NoExotic.exists_partialDiffeomorph_of_contDiffOn (endpointDomain_open a e)
      (endpoint_mem_domain ha e) (contDiffOn_endpointCoordinate a e) ⟨A, rfl⟩
  exact ⟨Φ, hp, hsub, hΦ, by rw [hΦ, endpointCoordinate_center]⟩

private def MorseCancel.scalarProductChart {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) (ℝ × V) (ℝ × V) ∞
    where
  toPartialEquiv := (Φ.toOpenPartialHomeomorph.prod (OpenPartialHomeomorph.refl V)).toPartialEquiv
  open_source := Φ.open_source.prod isOpen_univ
  open_target := Φ.open_target.prod isOpen_univ
  contMDiffOn_toFun := by
    have h : ContDiffOn ℝ ∞ (fun p : ℝ × V => (Φ p.1, p.2)) (Φ.source ×ˢ Set.univ) :=
      (Φ.contMDiffOn_toFun.contDiffOn.comp contDiff_fst.contDiffOn (fun _ hp => hp.1)).prodMk
        contDiff_snd.contDiffOn
    exact h.contMDiffOn
  contMDiffOn_invFun := by
    have h : ContDiffOn ℝ ∞ (fun p : ℝ × V => (Φ.symm p.1, p.2)) (Φ.target ×ˢ Set.univ) :=
      (Φ.contMDiffOn_invFun.contDiffOn.comp contDiff_fst.contDiffOn (fun _ hp => hp.1)).prodMk
        contDiff_snd.contDiffOn
    exact h.contMDiffOn

private theorem
    MorseCancel.exists_endpoint_product_chart {m : ℕ} (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (e : ℝ) (he : e ^ 2 = 1) :
    ∃ P : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, Model m) (Model m) (Model m) ∞,
      (e * a, (0 : Fin m → ℝ)) ∈ P.source ∧
        P (e * a, 0) = 0 ∧
          (∀ p, (P p).2 = p.2) ∧
            (∀ p ∈ P.source,
              cubic σ (-(a ^ 2)) p =
                cubic σ (-(a ^ 2)) (e * a, 0) + e * (P p).1 ^ 2 + ∑ i, σ i * (P p).2 i ^ 2) := by
  obtain ⟨Φ, hp, hsource, hΦ, hcenter⟩ := exists_endpoint_scalar_chart ha e
  let P := scalarProductChart (V := Fin m → ℝ) Φ
  have hP (p : Model m) : P p = (endpointCoordinate a e p.1, p.2) :=
    Prod.ext (congrFun hΦ p.1) rfl
  refine ⟨P, ⟨hp, Set.mem_univ _⟩, ?_, fun _ => rfl, ?_⟩
  · rw [hP, endpointCoordinate_center]
    rfl
  · intro p hp
    rw [hP]
    exact cubic_endpoint_square σ a e he (hsource hp.1)

private def Degree.LocalFunctionReplacement.replace {E B H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (f : M → ℝ) (b : E → ℝ) (y : M) : ℝ := by
  classical exact if y ∈ Φ.target then b (Φ.symm y) else f y

private theorem
    Degree.LocalFunctionReplacement.replace_of_mem {E B H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (f : M → ℝ) (b : E → ℝ) {y : M} (hy : y ∈ Φ.target) :
    replace Φ f b y = b (Φ.symm y) := by simp [replace, hy]

private theorem
    Degree.LocalFunctionReplacement.replace_of_notMem {E B H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (f : M → ℝ) (b : E → ℝ) {y : M} (hy : y ∉ Φ.target) :
    replace Φ f b y = f y := by simp [replace, hy]

private theorem
    Degree.LocalFunctionReplacement.replace_chart {E B H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (f : M → ℝ) (b : E → ℝ) {x : E} (hx : x ∈ Φ.source) :
    replace Φ f b (Φ x) = b x := by
  rw [replace_of_mem Φ f b (Φ.map_source' hx)]
  exact congrArg b (Φ.left_inv' hx)

private theorem Degree.LocalFunctionReplacement.replace_germ_chart {E B H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (f : M → ℝ) (b : E → ℝ) {y : M} (hy : y ∈ Φ.target) :
    replace Φ f b =ᶠ[𝓝 y] b ∘ Φ.symm := by
  filter_upwards [Φ.open_target.mem_nhds hy] with z hz
  exact replace_of_mem Φ f b hz

private theorem
    Degree.LocalFunctionReplacement.replace_self {E B H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) {f : M → ℝ} {b : E → ℝ}
    (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b x) : replace Φ f b = f := by
  funext y
  by_cases hy : y ∈ Φ.target
  · rw [replace_of_mem Φ f b hy]
    exact (hmodel (Φ.symm y) (Φ.map_target' hy)).symm.trans (congrArg f (Φ.right_inv' hy))
  · exact replace_of_notMem Φ f b hy

private theorem Degree.LocalFunctionReplacement.replace_eq_off_support {E B H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) {f : M → ℝ} {b₀ b₁ : E → ℝ} {K : Set E}
    (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b₀ x) (hfix : ∀ x ∉ K, b₁ x = b₀ x) {y : M}
    (hy : y ∉ Φ '' K) : replace Φ f b₁ y = f y := by
  by_cases hyt : y ∈ Φ.target
  · have hx : Φ.symm y ∉ K := fun h => hy ⟨Φ.symm y, h, Φ.right_inv' hyt⟩
    rw [replace_of_mem Φ f b₁ hyt, hfix _ hx]
    exact (hmodel (Φ.symm y) (Φ.map_target' hyt)).symm.trans (congrArg f (Φ.right_inv' hyt))
  · exact replace_of_notMem Φ f b₁ hyt

private theorem Degree.LocalFunctionReplacement.replace_germ_off_support {E B H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) [T2Space M] {f : M → ℝ} {b₀ b₁ : E → ℝ} {K : Set E}
    (hK : IsCompact K) (hKΦ : K ⊆ Φ.source) (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b₀ x)
    (hfix : ∀ x ∉ K, b₁ x = b₀ x) {y : M} (hy : y ∉ Φ '' K) : replace Φ f b₁ =ᶠ[𝓝 y] f := by
  have hc : IsClosed (Φ '' K) :=
    (hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKΦ)).isClosed
  filter_upwards [hc.isOpen_compl.mem_nhds hy] with z hz
  exact replace_eq_off_support Φ hmodel hfix hz

private theorem
    Degree.LocalFunctionReplacement.contMDiff_replace {E B H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
    {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) [T2Space M] {f : M → ℝ} {b₀ b₁ : E → ℝ} {K : Set E}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hb : ContDiff ℝ ∞ b₁) (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b₀ x) (hfix : ∀ x ∉ K, b₁ x = b₀ x) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (replace Φ f b₁) := by
  intro y
  by_cases hy : y ∈ Φ.target
  · have hs :=
      hb.contMDiff.contMDiffAt.comp y
        (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hy))
    exact hs.congr_of_eventuallyEq (replace_germ_chart Φ f b₁ hy)
  · have hnot : y ∉ Φ '' K := by
      rintro ⟨x, hx, rfl⟩
      exact hy (Φ.map_source' (hKΦ hx))
    exact
      hf.contMDiffAt.congr_of_eventuallyEq (replace_germ_off_support Φ hK hKΦ hmodel hfix hnot)

private theorem Degree.LocalFunctionReplacement.replace_critical_iff {E B H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (f : M → ℝ) {b : E → ℝ} (hb : ContDiff ℝ ∞ b) {y : M}
    (hy : y ∈ Φ.target) : mfderiv I 𝓘(ℝ, ℝ) (replace Φ f b) y = 0 ↔ fderiv ℝ b (Φ.symm y) = 0 := by
  have hΦ : IsLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ Φ.symm y := ⟨Φ.symm, hy, fun _ _ => rfl⟩
  have hsurj := (hΦ.mfderivToContinuousLinearEquiv (by simp)).surjective
  rw [(replace_germ_chart Φ f b hy).mfderiv_eq,
    mfderiv_comp y (hb.contMDiff.mdifferentiableAt (by simp))
      (Φ.symm.mdifferentiableAt (by simp) hy),
    mfderiv_eq_fderiv]
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨w, hw⟩ := hsurj v
    have he := congrArg (fun L : TangentSpace I y →L[ℝ] ℝ => L w) h
    change fderiv ℝ b (Φ.symm y) (mfderiv I 𝓘(ℝ, E) Φ.symm y w) = 0 at he
    change mfderiv I 𝓘(ℝ, E) Φ.symm y w = v at hw
    simpa only [hw, zero_apply] using he
  · intro h
    rw [h]
    rfl

private def MorseCancel.cubicDescent {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) : Model m :=
  (-(p.1 ^ 2 + t), fun i => -σ i * p.2 i)

private theorem
    MorseCancel.differential_cubicDescent {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) :
    differential σ t p (cubicDescent σ t p) = -(p.1 ^ 2 + t) ^ 2 - 2 * ∑ i, (σ i * p.2 i) ^ 2 := by
  rw [differential_apply]
  simp only [cubicDescent]
  have hs : (∑ i, 2 * σ i * p.2 i * (-σ i * p.2 i)) = -2 * ∑ i, (σ i * p.2 i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

private theorem MorseCancel.cubicDescent_strict {m : ℕ} (σ : Fin m → ℝ) {t : ℝ} {p : Model m}
    (hp : fderiv ℝ (cubic σ t) p ≠ 0) : fderiv ℝ (cubic σ t) p (cubicDescent σ t p) < 0 := by
  rw [fderiv_cubic, differential_cubicDescent]
  by_contra hh
  have hsum : 0 ≤ ∑ i, (σ i * p.2 i) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hx : p.1 ^ 2 + t = 0 := by nlinarith [sq_nonneg (p.1 ^ 2 + t)]
  have hz : (∑ i, (σ i * p.2 i) ^ 2) = 0 := by
    have hle := le_of_not_gt hh
    rw [hx] at hle
    linarith
  have hy (i : Fin m) : σ i * p.2 i = 0 := by
    have hi :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (σ i * p.2 i))).mp hz i
        (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp hi
  apply hp
  rw [fderiv_cubic]
  apply ContinuousLinearMap.ext
  intro v
  rw [differential_apply, hx]
  simp only [MulZeroClass.zero_mul, zero_add, zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  calc
    2 * σ i * p.2 i * v.2 i = 2 * (σ i * p.2 i) * v.2 i := by ring
    _ = 0 := by rw [hy, MulZeroClass.mul_zero, MulZeroClass.zero_mul]

private theorem
    MorseCancel.cubicDescent_zero_of_critical {m : ℕ} (σ : Fin m → ℝ) {t : ℝ} {p : Model m}
    (hp : fderiv ℝ (cubic σ t) p = 0) : cubicDescent σ t p = 0 := by
  rw [fderiv_cubic] at hp
  have hx := congrArg (fun L : Model m →L[ℝ] ℝ => L (1, 0)) hp
  have hx' : p.1 ^ 2 + t = 0 := by simpa [differential_apply] using hx
  apply Prod.ext
  · simpa only [cubicDescent, Prod.fst_zero, neg_eq_zero] using hx'
  · funext i
    have hi := congrArg (fun L : Model m →L[ℝ] ℝ => L (0, Pi.single i 1)) hp
    have hi' : 2 * σ i * p.2 i = 0 := by simpa [differential_apply, Pi.single_apply] using hi
    change -σ i * p.2 i = 0
    nlinarith

private def
    MorseCancel.nativeCubicDescent {m : ℕ} (σ : Fin m → ℝ) {B M : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [TopologicalSpace M] [ChartedSpace B M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, B) (Model m) M ∞) (t : ℝ) :
    (x : M) → TangentSpace 𝓘(ℝ, B) x :=
  Smale.FlowConstruction.partialChartField Φ.symm (cubicDescent σ t)

private def MorseCancel.endpointFieldCoordinate (a e s : ℝ) : ℝ :=
  (s - e * a) / (a + e * s)

private def MorseCancel.endpointFieldDomain (a e : ℝ) : Set ℝ :=
  {s | 0 < a + e * s}

private theorem
    MorseCancel.endpointFieldDomain_open (a e : ℝ) : IsOpen (endpointFieldDomain a e) := by
  apply isOpen_lt continuous_const
  fun_prop

private theorem MorseCancel.endpointField_mem_domain {a : ℝ} (ha : 0 < a) {e : ℝ} (he : e ^ 2 = 1) :
    e * a ∈ endpointFieldDomain a e := by
  change 0 < a + e * (e * a)
  have h : e * (e * a) = a := by rw [← mul_assoc, ← pow_two, he, one_mul]
  rw [h]
  linarith

private theorem MorseCancel.endpointFieldCoordinate_center (a e : ℝ) :
    endpointFieldCoordinate a e (e * a) = 0 := by simp [endpointFieldCoordinate]

private theorem MorseCancel.contDiffOn_endpointFieldCoordinate (a e : ℝ) :
    ContDiffOn ℝ ∞ (endpointFieldCoordinate a e) (endpointFieldDomain a e) := by
  intro s hs
  exact
    ((contDiffAt_id.sub contDiffAt_const).div
        (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id))
        (ne_of_gt hs)).contDiffWithinAt

private theorem
    MorseCancel.hasDerivAt_endpointFieldCoordinate (a : ℝ) {e : ℝ} (he : e ^ 2 = 1) {s : ℝ}
    (hs : s ∈ endpointFieldDomain a e) :
    HasDerivAt (endpointFieldCoordinate a e) (2 * a / (a + e * s) ^ 2) s := by
  have hd :=
    ((hasDerivAt_id s).sub_const (e * a)).div (((hasDerivAt_id s).const_mul e).const_add a)
      (ne_of_gt hs)
  convert! hd using 1
  congr 1
  rcases sq_eq_one_iff.mp he with h | h <;> rw [h] <;> ring

private theorem
    MorseCancel.endpointFieldCoordinate_pushforward (a : ℝ) {e : ℝ} (he : e ^ 2 = 1) {s : ℝ}
    (hs : s ∈ endpointFieldDomain a e) :
    deriv (endpointFieldCoordinate a e) s * (a ^ 2 - s ^ 2) =
      (-2 * e * a) * endpointFieldCoordinate a e s := by
  rw [(hasDerivAt_endpointFieldCoordinate a he hs).deriv]
  unfold endpointFieldCoordinate
  have hn : a + e * s ≠ 0 := ne_of_gt hs
  field_simp
  rcases sq_eq_one_iff.mp he with h | h <;> rw [h] <;> ring

private theorem MorseCancel.exists_endpoint_field_scalar_chart {a : ℝ} (ha : 0 < a) {e : ℝ}
    (he : e ^ 2 = 1) :
    ∃ P : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      e * a ∈ P.source ∧
        P.source ⊆ endpointFieldDomain a e ∧
          (P : ℝ → ℝ) = endpointFieldCoordinate a e ∧ P (e * a) = 0 := by
  have hm := endpointField_mem_domain ha he
  have hd := (hasDerivAt_endpointFieldCoordinate a he hm).hasFDerivAt
  have hn : 2 * a / (a + e * (e * a)) ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) ha.ne') (pow_ne_zero _ (ne_of_gt hm))
  have hi : Function.Injective (fderiv ℝ (endpointFieldCoordinate a e) (e * a)) := by
    rw [hd.fderiv]
    intro x y hxy
    change x * (2 * a / (a + e * (e * a)) ^ 2) = y * (2 * a / (a + e * (e * a)) ^ 2) at hxy
    exact mul_right_cancel₀ hn hxy
  let A : ℝ ≃L[ℝ] ℝ :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ (endpointFieldCoordinate a e) (e * a)).toLinearMap
        hi).toContinuousLinearEquiv
  obtain ⟨P, hp, hsub, hP⟩ :=
    NoExotic.exists_partialDiffeomorph_of_contDiffOn (endpointFieldDomain_open a e) hm
      (contDiffOn_endpointFieldCoordinate a e) ⟨A, rfl⟩
  exact ⟨P, hp, hsub, hP, by rw [hP, endpointFieldCoordinate_center]⟩

private def
    MorseCancel.endpointLinearField {m : ℕ} (σ : Fin m → ℝ) (a e : ℝ) (p : Model m) : Model m :=
  ((-2 * e * a) * p.1, fun i => -σ i * p.2 i)

private def MorseCancel.endpointFieldProduct {m : ℕ} (a e : ℝ) (p : Model m) : Model m :=
  (endpointFieldCoordinate a e p.1, p.2)

private theorem
    MorseCancel.fderiv_endpointFieldProduct_cubic {m : ℕ} (σ : Fin m → ℝ) (a : ℝ) {e : ℝ}
    (he : e ^ 2 = 1) {p : Model m} (hp : p.1 ∈ endpointFieldDomain a e) :
    fderiv ℝ (endpointFieldProduct a e) p (cubicDescent σ (-(a ^ 2)) p) =
      endpointLinearField σ a e (endpointFieldProduct a e p) := by
  have hd :=
    ((hasDerivAt_endpointFieldCoordinate a he hp).comp_hasFDerivAt p
          (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).prodMk
      (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  change HasFDerivAt (endpointFieldProduct a e) _ p at hd
  rw [hd.fderiv]
  apply Prod.ext
  · change
      (2 * a / (a + e * p.1) ^ 2) * (-(p.1 ^ 2 + -(a ^ 2))) =
        (-2 * e * a) * endpointFieldCoordinate a e p.1
    have hh := endpointFieldCoordinate_pushforward a he hp
    rw [(hasDerivAt_endpointFieldCoordinate a he hp).deriv] at hh
    convert! hh using 1; ring
  · rfl

private theorem MorseCancel.exists_endpoint_field_product_chart {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) {e : ℝ} (he : e ^ 2 = 1) :
    ∃ P : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, Model m) (Model m) (Model m) ∞,
      (e * a, (0 : Fin m → ℝ)) ∈ P.source ∧
        P (e * a, 0) = 0 ∧
          (P : Model m → Model m) = endpointFieldProduct a e ∧
            ∀ p ∈ P.source,
              fderiv ℝ P p (cubicDescent σ (-(a ^ 2)) p) = endpointLinearField σ a e (P p) := by
  obtain ⟨Q, hq, hsub, hQ, hzero⟩ := exists_endpoint_field_scalar_chart ha he
  let P := scalarProductChart (V := Fin m → ℝ) Q
  have hP : (P : Model m → Model m) = endpointFieldProduct a e := by
    funext p
    exact Prod.ext (congrFun hQ p.1) rfl
  refine ⟨P, ⟨hq, Set.mem_univ _⟩, ?_, hP, ?_⟩
  · rw [hP]
    simp [endpointFieldProduct, endpointFieldCoordinate_center]
  · intro p hp
    rw [hP]
    exact fderiv_endpointFieldProduct_cubic σ a he (hsub hp.1)

private theorem
    MorseCancel.partialChartField_of_model_conjugacy {D F E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (P : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, F) D F ∞) (Q : PartialDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, E) F M ∞)
    (W : D → D) (U : F → F) (hpush : ∀ p ∈ P.source, fderiv ℝ P p (W p) = U (P p)) {x : M}
    (hx : x ∈ (P.trans Q).target) :
    Smale.FlowConstruction.partialChartField (P.trans Q).symm W x =
      Smale.FlowConstruction.partialChartField Q.symm U x := by
  have hxQ : x ∈ Q.target := hx.1
  have hxP : Q.symm x ∈ P.target := hx.2
  have hdiff : P.symm.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ, F) 𝓘(ℝ, D) :=
    ⟨P.symm.mdifferentiableOn (by simp), P.mdifferentiableOn (by simp)⟩
  have hinv : (mfderivWithin 𝓘(ℝ, F) 𝓘(ℝ, D) P.symm Set.univ (Q.symm x)).IsInvertible := by
    rw [mfderivWithin_univ]
    exact ⟨hdiff.mfderiv hxP, rfl⟩
  have hh :=
    VectorField.mpullbackWithin_comp_of_left (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, F)) (I'' := 𝓘(ℝ, D)) (f :=
      (Q.symm : M → F)) (g := (P.symm : F → D)) (V := fun y =>
      (NormedSpace.fromTangentSpace y).symm (W y)) (s := Set.univ) (t := Set.univ)
      (Q.symm.mdifferentiableAt (by simp) hxQ).mdifferentiableWithinAt (Set.mapsTo_univ _ _)
      (uniqueMDiffWithinAt_univ 𝓘(ℝ, E)) hinv
  simp only [VectorField.mpullbackWithin_univ] at hh
  have hv :
    VectorField.mpullback 𝓘(ℝ, F) 𝓘(ℝ, D) P.symm
        (fun y => (NormedSpace.fromTangentSpace y).symm (W y)) (Q.symm x) =
      (NormedSpace.fromTangentSpace (Q.symm x)).symm (U (Q.symm x)) := by
    change Smale.FlowConstruction.partialChartField P.symm W (Q.symm x) = _
    rw [Smale.FlowConstruction.partialChartField_eq_mfderiv_symm P.symm W hxP]
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ P (P.symm (Q.symm x)) (W (P.symm (Q.symm x))) = U (Q.symm x)
    have hp : P.symm (Q.symm x) ∈ P.source := P.map_target' hxP
    rw [hpush (P.symm (Q.symm x)) hp]
    exact congrArg U (P.right_inv' hxP)
  change
    VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, D) (P.symm ∘ Q.symm)
        (fun y => (NormedSpace.fromTangentSpace y).symm (W y)) x =
      _
  rw [hh, VectorField.mpullback_apply, hv]
  rfl

private theorem MorseCancel.exists_native_cubic_field_endpoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) {e : ℝ} (he : e ^ 2 = 1)
    (Q : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) (h0 : (0 : Model m) ∈ Q.source)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hmodel :
      ∀ x ∈ Q.target,
        V x = Smale.FlowConstruction.partialChartField Q.symm (endpointLinearField σ a e) x) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (e * a, (0 : Fin m → ℝ)) ∈ Φ.source ∧
        Φ (e * a, 0) = Q 0 ∧
          Φ.target ⊆ Q.target ∧
            (∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) ∧
              (Φ : Model m → M) = Q ∘ endpointFieldProduct a e := by
  obtain ⟨P, hp, hcenter, hP, hpush⟩ := exists_endpoint_field_product_chart σ ha he
  let Φ := P.trans Q
  have hsource : (e * a, (0 : Fin m → ℝ)) ∈ Φ.source := by
    change (e * a, (0 : Fin m → ℝ)) ∈ P.source ∧ P (e * a, 0) ∈ Q.source
    exact ⟨hp, hcenter.symm ▸ h0⟩
  refine ⟨Φ, hsource, ?_, fun _ hx => hx.1, ?_, ?_⟩
  · change Q (P (e * a, 0)) = Q 0
    rw [hcenter]
  · intro x hx
    rw [hmodel x hx.1]
    exact
      (partialChartField_of_model_conjugacy P Q (cubicDescent σ (-(a ^ 2)))
          (endpointLinearField σ a e) hpush hx).symm
  · change Q ∘ P = Q ∘ endpointFieldProduct a e
    rw [hP]

private def
    MorseCancel.splitLinear {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) : Model m ≃ₗ[ℝ] (Fin n → ℝ)
    where
  toFun p j := (ρ.symm j).elim p.1 p.2
  invFun f := (f (ρ Option.none), fun i => f (ρ (Option.some i)))
  left_inv
    p := by
    apply Prod.ext
    · simp
    · funext i
      simp
  right_inv
    f := by
    funext j
    have hj := ρ.apply_symm_apply j
    cases h : ρ.symm j with
    | none => simpa only [h, Option.elim_none] using congrArg f hj
    | some i => simpa only [h, Option.elim_some] using congrArg f hj
  map_add' p
    q := by
    funext j
    cases h : ρ.symm j <;> simp [h]
  map_smul' t
    p := by
    funext j
    cases h : ρ.symm j <;> simp [h]

private def
    MorseCancel.splitEquiv {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) : Model m ≃L[ℝ] (Fin n → ℝ) :=
  (splitLinear ρ).toContinuousLinearEquiv

private theorem
    MorseCancel.splitEquiv_apply_none {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) (p : Model m) :
    splitEquiv ρ p (ρ Option.none) = p.1 := by
  change (ρ.symm (ρ Option.none)).elim p.1 p.2 = p.1
  simp

private theorem
    MorseCancel.splitEquiv_apply_some {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) (p : Model m)
    (i : Fin m) : splitEquiv ρ p (ρ (Option.some i)) = p.2 i := by
  change (ρ.symm (ρ (Option.some i))).elim p.1 p.2 = p.2 i
  simp

private theorem MorseCancel.split_signed_sum {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) (w : Fin n → ℝ)
    (p : Model m) :
    (∑ j, w j * splitEquiv ρ p j ^ 2) =
      w (ρ Option.none) * p.1 ^ 2 + ∑ i, w (ρ (Option.some i)) * p.2 i ^ 2 := by
  rw [← ρ.sum_comp]
  simp only [Fintype.sum_option, splitEquiv_apply_none, splitEquiv_apply_some]

private theorem MorseCancel.splitEquiv_endpoint_field {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n)
    (w : Fin n → ℝ) (p : Model m) :
    splitEquiv ρ
        (endpointLinearField (fun i => w (ρ (Option.some i))) (1 / 2) (w (ρ Option.none)) p) =
      fun j => -w j * splitEquiv ρ p j := by
  funext j
  obtain ⟨k, rfl⟩ := ρ.surjective j
  cases k with
  | none =>
    rw [splitEquiv_apply_none, splitEquiv_apply_none]
    change (-2 * w (ρ Option.none) * (1 / 2)) * p.1 = -w (ρ Option.none) * p.1
    ring
  | some i =>
    rw [splitEquiv_apply_some, splitEquiv_apply_some]
    rfl

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.splitCoordinates_signed_descent {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, w i = -1 ∨ w i = 1) (z : ι → ℝ) :
    Smale.MorseHandle.splitCoordinates w (fun i => -w i * z i) =
      Smale.MorseHandle.descent (Smale.MorseHandle.splitCoordinates w z) := by
  apply Prod.ext
  · ext i
    change -w i.1 * z i.1 = z i.1
    rw [i.2]
    ring
  · ext i
    change -w i.1 * z i.1 = -z i.1
    rw [(hw i.1).resolve_left i.2]
    ring

attribute [local instance 100] Classical.propDecidable in
private def
    MorseCancel.selectedMorseFieldEquiv {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) :
    Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates) :=
  (splitEquiv ρ).trans (Smale.MorseHandle.splitCoordinates c.weights)

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.selectedMorseFieldEquiv_descent {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (p : Model m) :
    selectedMorseFieldEquiv c ρ
        (endpointLinearField (fun i => c.weights (ρ (Option.some i))) (1 / 2)
          (c.weights (ρ Option.none)) p) =
      Smale.MorseHandle.descent (selectedMorseFieldEquiv c ρ p) := by
  change
    Smale.MorseHandle.splitCoordinates c.weights (splitEquiv ρ _) =
      Smale.MorseHandle.descent (Smale.MorseHandle.splitCoordinates c.weights (splitEquiv ρ p))
  rw [splitEquiv_endpoint_field]
  exact splitCoordinates_signed_descent c.weights c.signs (splitEquiv ρ p)

private def MorseCancel.transverseFieldChange {m : ℕ} (T : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ)) :
    Model m ≃L[ℝ] Model m :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr T

private theorem MorseCancel.transverseFieldChange_cubicDescent {m : ℕ} (σ : Fin m → ℝ)
    (T : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ))
    (hcomm : ∀ z, T (fun i => σ i * z i) = fun i => σ i * T z i) (t : ℝ) (p : Model m) :
    transverseFieldChange T (cubicDescent σ t p) = cubicDescent σ t (transverseFieldChange T p) :=
  by
  apply Prod.ext
  · rfl
  · change T (fun i => -σ i * p.2 i) = fun i => -σ i * T p.2 i
    have hleft : (fun i => -σ i * p.2 i) = -(fun i => σ i * p.2 i) := by
      funext i
      simp only [Pi.neg_apply, neg_mul]
    rw [hleft, map_neg, hcomm]
    funext i
    simp only [Pi.neg_apply, neg_mul]

private def MorseCancel.splitTransverseChange {m : ℕ} {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] (e : (Fin m → ℝ) ≃L[ℝ] (A × B))
    (P : A ≃L[ℝ] A) (S : B ≃L[ℝ] B) : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ) :=
  (e.trans (P.prodCongr S)).trans e.symm

private theorem
    MorseCancel.splitTransverseChange_commutes {m : ℕ} {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] (σ : Fin m → ℝ)
    (e : (Fin m → ℝ) ≃L[ℝ] (A × B)) (α β : ℝ)
    (he : ∀ z, e (fun i => σ i * z i) = (α • (e z).1, β • (e z).2)) (P : A ≃L[ℝ] A)
    (S : B ≃L[ℝ] B) (z : Fin m → ℝ) :
    splitTransverseChange e P S (fun i => σ i * z i) = fun i =>
      σ i * splitTransverseChange e P S z i := by
  apply e.injective
  simp only [splitTransverseChange, ContinuousLinearEquiv.trans_apply, e.apply_symm_apply, he,
    ContinuousLinearEquiv.prodCongr_apply, map_smul]

private theorem MorseCancel.morse_block_change_descent {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (A : N ≃L[ℝ] N) (B : P ≃L[ℝ] P)
    (z : N × P) :
    (A.prodCongr B) (Smale.MorseHandle.descent z) =
      Smale.MorseHandle.descent ((A.prodCongr B) z) := by
  apply Prod.ext
  · rfl
  · change B (-z.2) = -B z.2
    exact B.map_neg _

private theorem MorseCancel.exists_positive_ray_alignment {D : Type*} [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] {u v : D} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ (r : ℝ) (A : D ≃ₗᵢ[ℝ] D), 0 < r ∧ A (r • u) = v ∧ ∀ s : ℝ, A ((s * r) • u) = s • v := by
  let r := ‖v‖ / ‖u‖
  have hr : 0 < r := div_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hu)
  have hnorm : ‖r • u‖ = ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact div_mul_cancel₀ ‖v‖ (norm_ne_zero_iff.mpr hu)
  let A : D ≃ₗᵢ[ℝ] D := (ℝ ∙ (r • u - v))ᗮ.reflection
  have hA : A (r • u) = v := Submodule.reflection_sub hnorm
  refine ⟨r, A, hr, hA, ?_⟩
  intro s
  rw [← smul_smul, A.map_smul, hA]

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.selectedMorseFieldEquiv_axis_ne_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) :
    selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ)) ≠ 0 := by
  intro h
  have hh :=
    (selectedMorseFieldEquiv c ρ).injective
      (h.trans (map_zero (selectedMorseFieldEquiv c ρ)).symm)
  have h1 := congrArg Prod.fst hh
  norm_num at h1

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.selectedMorseFieldEquiv_negative_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ Option.none) = -1) :
    (selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))).2 = 0 ∧
      (selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))).1 ≠ 0 := by
  let z := selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))
  have hw :
    endpointLinearField (fun i => c.weights (ρ (Option.some i))) (1 / 2)
        (c.weights (ρ Option.none)) (1, (0 : Fin m → ℝ)) =
      (1, 0) := by ext i <;> simp [endpointLinearField, he]
  have hh := selectedMorseFieldEquiv_descent c ρ (1, (0 : Fin m → ℝ))
  rw [hw] at hh
  have h2 : z.2 = -z.2 := congrArg Prod.snd hh
  have hs : (2 : ℝ) • z.2 = 0 := by
    rw [two_smul]
    exact (congrArg (fun v => v + z.2) h2).trans (neg_add_cancel z.2)
  have hz : z.2 = 0 := (smul_eq_zero.mp hs).resolve_left (by norm_num)
  refine ⟨hz, ?_⟩
  intro h1
  exact selectedMorseFieldEquiv_axis_ne_zero c ρ (Prod.ext h1 hz)

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.selectedMorseFieldEquiv_positive_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ Option.none) = 1) :
    (selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))).1 = 0 ∧
      (selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))).2 ≠ 0 := by
  let z := selectedMorseFieldEquiv c ρ (1, (0 : Fin m → ℝ))
  have hw :
    endpointLinearField (fun i => c.weights (ρ (Option.some i))) (1 / 2)
        (c.weights (ρ Option.none)) (1, (0 : Fin m → ℝ)) =
      -(1, 0) := by ext i <;> simp [endpointLinearField, he]
  have hh := selectedMorseFieldEquiv_descent c ρ (1, (0 : Fin m → ℝ))
  rw [hw, map_neg] at hh
  have h1 : z.1 = -z.1 := (congrArg Prod.fst hh).symm
  have hs : (2 : ℝ) • z.1 = 0 := by
    rw [two_smul]
    exact (congrArg (fun v => v + z.1) h1).trans (neg_add_cancel z.1)
  have hz : z.1 = 0 := (smul_eq_zero.mp hs).resolve_left (by norm_num)
  refine ⟨hz, ?_⟩
  intro h2
  exact selectedMorseFieldEquiv_axis_ne_zero c ρ (Prod.ext hz h2)

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.exists_selected_outgoing_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ Option.none) = -1)
    {v : c.NegativeCoordinates} (hv : v ≠ 0) :
    ∃ (r : ℝ) (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates)),
      0 < r ∧
        L (r, 0) = (v, 0) ∧
          ∀ p,
            L
                (endpointLinearField (fun i => c.weights (ρ (Option.some i))) (1 / 2)
                  (c.weights (ρ Option.none)) p) =
              Smale.MorseHandle.descent (L p) := by
  let L₀ := selectedMorseFieldEquiv c ρ
  obtain ⟨hz, hn⟩ := selectedMorseFieldEquiv_negative_axis c ρ he
  obtain ⟨r, A, hr, hA, _⟩ := exists_positive_ray_alignment hn hv
  let B :=
    A.toContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ c.PositiveCoordinates)
  let L := L₀.trans B
  refine ⟨r, L, hr, ?_, ?_⟩
  · have hp : (r, (0 : Fin m → ℝ)) = r • (1, 0) := by simp
    rw [hp, L.map_smul]
    apply Prod.ext
    · change r • A ((L₀ (1, 0)).1) = v
      rw [← A.map_smul]
      exact hA
    · change r • (L₀ (1, 0)).2 = 0
      rw [hz, smul_zero]
  · intro p
    change B (L₀ _) = Smale.MorseHandle.descent (B (L₀ p))
    rw [selectedMorseFieldEquiv_descent]
    exact morse_block_change_descent _ _ _

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.exists_selected_incoming_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ Option.none) = 1)
    {v : c.PositiveCoordinates} (hv : v ≠ 0) :
    ∃ (r : ℝ) (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates)),
      0 < r ∧
        L (-r, 0) = (0, v) ∧
          ∀ p,
            L
                (endpointLinearField (fun i => c.weights (ρ (Option.some i))) (1 / 2)
                  (c.weights (ρ Option.none)) p) =
              Smale.MorseHandle.descent (L p) := by
  let L₀ := selectedMorseFieldEquiv c ρ
  obtain ⟨hz, hn⟩ := selectedMorseFieldEquiv_positive_axis c ρ he
  obtain ⟨r, A, hr, hA, _⟩ := exists_positive_ray_alignment hn (neg_ne_zero.mpr hv)
  let B :=
    (ContinuousLinearEquiv.refl ℝ c.NegativeCoordinates).prodCongr A.toContinuousLinearEquiv
  let L := L₀.trans B
  refine ⟨r, L, hr, ?_, ?_⟩
  · have hp : (-r, (0 : Fin m → ℝ)) = (-r) • (1, 0) := by simp
    rw [hp, L.map_smul]
    apply Prod.ext
    · change (-r) • (L₀ (1, 0)).1 = 0
      rw [hz, smul_zero]
    · change (-r) • A ((L₀ (1, 0)).2) = v
      rw [neg_smul, ← A.map_smul, hA, neg_neg]
  · intro p
    change B (L₀ _) = Smale.MorseHandle.descent (B (L₀ p))
    rw [selectedMorseFieldEquiv_descent]
    exact morse_block_change_descent _ _ _

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.exists_cubic_field_endpoint_with_alignment {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ} (σ : Fin m → ℝ)
    {e : ℝ} (he : e ^ 2 = 1) (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hL : ∀ p, L (endpointLinearField σ (1 / 2) e p) = Smale.MorseHandle.descent (L p)) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (e / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧
        Φ (e / 2, 0) = x ∧
          Φ.target ⊆ c.splitChart.source ∧
            (∀ y ∈ Φ.target, c.descentField y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
              (Φ : Model m → M) = c.splitChart.symm ∘ L ∘ endpointFieldProduct (1 / 2) e := by
  let P := L.toDiffeomorph.toPartialDiffeomorph
  let Q := P.trans c.splitChart.symm
  have h0 : (0 : Model m) ∈ Q.source := by
    change (0 : Model m) ∈ Set.univ ∧ L 0 ∈ c.splitChart.target
    rw [map_zero, ← c.splitChart_center]
    exact ⟨Set.mem_univ _, c.splitChart.map_source' c.splitChart_mem_source⟩
  have hQzero : Q 0 = x := by
    change c.splitChart.symm (L 0) = x
    rw [map_zero, ← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have hmodel :
    ∀ y ∈ Q.target,
      c.descentField y =
        Smale.FlowConstruction.partialChartField Q.symm (endpointLinearField σ (1 / 2) e) y := by
    intro y hy
    have hpush (p : Model m) (_ : p ∈ P.source) :
      fderiv ℝ P p (endpointLinearField σ (1 / 2) e p) = Smale.MorseHandle.descent (P p) := by
      change fderiv ℝ L p (endpointLinearField σ (1 / 2) e p) = Smale.MorseHandle.descent (L p)
      rw [L.fderiv]
      exact hL p
    exact
      (partialChartField_of_model_conjugacy P c.splitChart.symm (endpointLinearField σ (1 / 2) e)
          Smale.MorseHandle.descent hpush hy).symm
  obtain ⟨Φ, hp, hc, hsub, hf, hmap⟩ :=
    exists_native_cubic_field_endpoint σ (by norm_num : 0 < (1 / 2 : ℝ)) he Q h0 c.descentField
      hmodel
  refine ⟨Φ, ?_, ?_, fun y hy => (hsub hy).1, hf, hmap⟩
  · simpa only [mul_one_div] using hp
  · simpa only [mul_one_div, hQzero] using hc

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.exists_original_field_endpoint_with_alignment {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {x : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ} (σ : Fin m → ℝ)
    {e : ℝ} (he : e ^ 2 = 1) (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hL : ∀ p, L (endpointLinearField σ (1 / 2) e p) = Smale.MorseHandle.descent (L p))
    (V : (y : M) → TangentSpace 𝓘(ℝ, E) y) (heq : ∀ᶠ y in 𝓝 x, V y = c.descentField y) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (e / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧
        Φ (e / 2, 0) = x ∧
          Φ.target ⊆ c.splitChart.source ∧
            (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
              (Φ : Model m → M) = c.splitChart.symm ∘ L ∘ endpointFieldProduct (1 / 2) e := by
  obtain ⟨Φ, hp, hc, hsub, hf, hmap⟩ := exists_cubic_field_endpoint_with_alignment c σ he L hL
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp heq
  let Ψ := Smale.PartialChart.restrictTarget Φ hU
  have hpΨ : (e / 2, (0 : Fin m → ℝ)) ∈ Ψ.source := by
    change (e / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (e / 2, 0) ∈ U
    exact ⟨hp, hc.symm ▸ hxU⟩
  refine ⟨Ψ, hpΨ, hc, fun y hy => hsub hy.1, ?_, hmap⟩
  intro y hy
  exact (hUsub hy.2).trans (hf y hy.1)

private theorem
    MorseCancel.endpointFieldCoordinate_mem_open_axis {a : ℝ} {e : ℝ} (he : e ^ 2 = 1) {s : ℝ}
    (hs : s ∈ endpointFieldDomain a e) (hdir : 0 < -e * endpointFieldCoordinate a e s) :
    s ∈ Set.Ioo (-a) a := by
  rcases sq_eq_one_iff.mp he with h | h
  · subst e
    have hd : 0 < a + s := by simpa [endpointFieldDomain] using hs
    have hy : (s - a) / (a + s) < 0 := by simpa [endpointFieldCoordinate] using hdir
    have hn : s - a < 0 := by simpa using (div_lt_iff₀ hd).mp hy
    exact ⟨by linarith, by linarith⟩
  · subst e
    have hd : 0 < a - s := by simpa [endpointFieldDomain] using hs
    have hy : 0 < (s + a) / (a - s) := by
      simpa [endpointFieldCoordinate, sub_eq_add_neg] using hdir
    have hn : 0 < s + a := by simpa using (lt_div_iff₀ hd).mp hy
    exact ⟨by linarith, by linarith⟩

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.exists_controlled_morse_field_endpoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x) {m : ℕ} (σ : Fin m → ℝ) {e : ℝ}
    (he : e ^ 2 = 1) (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hL : ∀ p, L (endpointLinearField σ (1 / 2) e p) = Smale.MorseHandle.descent (L p))
    (V : (y : M) → TangentSpace 𝓘(ℝ, E) y) (heq : ∀ᶠ y in 𝓝 x, V y = c.descentField y) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (e / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧
        Φ (e / 2, 0) = x ∧
          Φ.target ⊆ c.splitChart.source ∧
            (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
              ∀ p ∈ Φ.source,
                p.1 ∈ endpointFieldDomain (1 / 2) e ∧
                  c.splitChart (Φ p) = L (endpointFieldProduct (1 / 2) e p) := by
  obtain ⟨Φ, hp, hc, hsub, hf, hmap⟩ :=
    exists_original_field_endpoint_with_alignment c σ he L hL V heq
  let q : Model m := (e / 2, 0)
  have hq : q.1 ∈ endpointFieldDomain (1 / 2) e := by
    simpa only [q, mul_one_div] using endpointField_mem_domain (by norm_num : 0 < (1 / 2 : ℝ)) he
  have hd : ContinuousAt (endpointFieldCoordinate (1 / 2) e) q.1 :=
    ((contDiffOn_endpointFieldCoordinate (1 / 2) e).contDiffAt
        ((endpointFieldDomain_open (1 / 2) e).mem_nhds hq)).continuousAt
  have hprod : ContinuousAt (endpointFieldProduct (m := m) (1 / 2) e) q :=
    (hd.comp continuousAt_fst).prodMk continuousAt_snd
  have hzero : L (endpointFieldProduct (1 / 2) e q) = 0 := by
    have hq' : q = (e * (1 / 2), (0 : Fin m → ℝ)) := by
      apply Prod.ext
      · dsimp [q]
        ring
      · rfl
    rw [hq']
    simp [endpointFieldProduct, endpointFieldCoordinate_center]
  have hct : ContinuousAt (fun p : Model m => L (endpointFieldProduct (1 / 2) e p)) q :=
    L.continuous.continuousAt.comp hprod
  have htarget0 : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ c.splitChart.target := by
    rw [← c.splitChart_center]
    exact c.splitChart.map_source' c.splitChart_mem_source
  have htarget : ∀ᶠ p in 𝓝 q, L (endpointFieldProduct (1 / 2) e p) ∈ c.splitChart.target := by
    have hn : ∀ᶠ z in 𝓝 (L (endpointFieldProduct (1 / 2) e q)), z ∈ c.splitChart.target :=
      c.splitChart.open_target.mem_nhds (hzero.symm ▸ htarget0)
    exact hct.eventually hn
  have hdomain : ∀ᶠ p in 𝓝 q, p.1 ∈ endpointFieldDomain (1 / 2) e :=
    continuousAt_fst.eventually ((endpointFieldDomain_open (1 / 2) e).mem_nhds hq)
  obtain ⟨U, hUsub, hU, hqU⟩ := mem_nhds_iff.mp (hdomain.and htarget)
  let Ψ := Smale.PartialChart.restrictSource Φ hU
  have hpΨ : q ∈ Ψ.source := ⟨hp, hqU⟩
  refine ⟨Ψ, hpΨ, hc, fun y hy => hsub hy.1, ?_, ?_⟩
  · intro y hy
    exact hf y hy.1
  · intro p hp
    obtain ⟨hpd, hpt⟩ := hUsub hp.2
    refine ⟨hpd, ?_⟩
    change c.splitChart (Φ p) = L (endpointFieldProduct (1 / 2) e p)
    rw [hmap]
    exact c.splitChart.right_inv' hpt

private theorem
    MorseCancel.descentFlow_outgoing_aligned_ray {m : ℕ} {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (L : Model m ≃L[ℝ] (N × P)) {r : ℝ}
    {v : N} (hL : L (r, 0) = (v, 0)) (t : ℝ) :
    Smale.MorseHandle.descentFlow t (L (r, 0)) = L (r * Real.exp t, 0) := by
  have he : (r * Real.exp t, (0 : Fin m → ℝ)) = Real.exp t • (r, 0) := by
    apply Prod.ext
    · change r * Real.exp t = Real.exp t * r
      ring
    · simp
  rw [he, L.map_smul, hL]
  change (Real.exp t • v, Real.exp (-t) • (0 : P)) = (Real.exp t • v, Real.exp t • (0 : P))
  simp

private theorem
    MorseCancel.descentFlow_incoming_aligned_ray {m : ℕ} {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] (L : Model m ≃L[ℝ] (N × P)) {r : ℝ}
    {v : P} (hL : L (-r, 0) = (0, v)) (t : ℝ) :
    Smale.MorseHandle.descentFlow t (L (-r, 0)) = L (-r * Real.exp (-t), 0) := by
  have he : (-r * Real.exp (-t), (0 : Fin m → ℝ)) = Real.exp (-t) • (-r, 0) := by
    apply Prod.ext
    · change -r * Real.exp (-t) = Real.exp (-t) * -r
      ring
    · simp
  rw [he, L.map_smul, hL]
  change (Real.exp t • (0 : N), Real.exp (-t) • v) = (Real.exp (-t) • (0 : N), Real.exp (-t) • v)
  simp

private theorem
    MorseCancel.cubic_axis_of_aligned_morse_ray {m : ℕ} {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) (C : M → N × P)
    (L : Model m ≃L[ℝ] (N × P)) {a : ℝ} {e : ℝ} (he : e ^ 2 = 1)
    (hcoord :
      ∀ p ∈ Φ.source, p.1 ∈ endpointFieldDomain a e ∧ C (Φ p) = L (endpointFieldProduct a e p))
    {x : M} (hx : x ∈ Φ.target) {r : ℝ} (hr : 0 < -e * r) (hCx : C x = L (r, 0)) :
    ∃ s ∈ Set.Ioo (-a) a,
      (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = x ∧ endpointFieldCoordinate a e s = r := by
  let p := Φ.symm x
  have hp : p ∈ Φ.source := Φ.map_target' hx
  have hpx : Φ p = x := Φ.right_inv' hx
  obtain ⟨hdom, hCp⟩ := hcoord p hp
  rw [hpx, hCx] at hCp
  have hlin : endpointFieldProduct a e p = (r, 0) := L.injective hCp.symm
  have hscalar : endpointFieldCoordinate a e p.1 = r := congrArg Prod.fst hlin
  have hzero : p.2 = 0 := congrArg Prod.snd hlin
  have haxis : p = (p.1, 0) := Prod.ext rfl hzero
  have hdir : 0 < -e * endpointFieldCoordinate a e p.1 := hscalar.symm ▸ hr
  refine ⟨p.1, endpointFieldCoordinate_mem_open_axis he hdom hdir, ?_, ?_, hscalar⟩
  · exact haxis ▸ hp
  · exact (congrArg Φ haxis).symm.trans hpx

private theorem
    MorseCancel.flow_formula_of_local_shifts {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (γ : ℝ → X) {S : Set ℝ} (hS : IsPreconnected S)
    (hlocal : ∀ t ∈ S, ∀ᶠ s in 𝓝 t, γ s = F (s - t) (γ t)) {t₀ t : ℝ} (h₀ : t₀ ∈ S) (ht : t ∈ S) :
    γ t = F (t - t₀) (γ t₀) := by
  let β : S → X := fun u => F (-u.1) (γ u.1)
  have hc : IsLocallyConstant β := by
    apply (IsLocallyConstant.iff_eventually_eq β).mpr
    intro u
    filter_upwards [continuousAt_subtype_val.eventually (hlocal u.1 u.2)] with v hv
    change F (-v.1) (γ v.1) = F (-u.1) (γ u.1)
    rw [hv, ← F.map_add]
    congr 1
    ring
  let : PreconnectedSpace S := Subtype.preconnectedSpace hS
  have hb : β ⟨t, ht⟩ = β ⟨t₀, h₀⟩ :=
    hc.apply_eq_of_isPreconnected PreconnectedSpace.isPreconnected_univ (Set.mem_univ _)
      (Set.mem_univ _)
  have hh := congrArg (F t) hb
  change F t (F (-t) (γ t)) = F t (F (-t₀) (γ t₀)) at hh
  simpa only [← F.map_add, add_neg_cancel, F.map_zero_apply, ← sub_eq_add_neg] using hh

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.eventually_morse_coordinate_flow {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (x : M) (t : ℝ)
    (ht : F t x ∈ c.splitChart.source) (heq : ∀ᶠ y in 𝓝 (F t x), V y = c.descentField y) :
    ∀ᶠ s in 𝓝 t,
      c.splitChart (F s x) = Smale.MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) := by
  have hlocal :
    ∀ᶠ u in 𝓝 (0 : ℝ),
      F u (F t x) = c.splitChart.symm (Smale.MorseHandle.descentFlow u (c.splitChart (F t x))) :=
    c.eventually_flow_eq_descentModel hV F hF ht heq
  have htime : Filter.Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 0) := by
    have hc : Continuous (fun s : ℝ => s - t) := continuous_id.sub continuous_const
    simpa only [sub_self] using hc.tendsto t
  have hmodel :
    Continuous (fun u : ℝ => Smale.MorseHandle.descentFlow u (c.splitChart (F t x))) :=
    Smale.MorseHandle.descentFlow.continuous continuous_id continuous_const
  have htarget :
    ∀ᶠ u in 𝓝 (0 : ℝ),
      Smale.MorseHandle.descentFlow u (c.splitChart (F t x)) ∈ c.splitChart.target := by
    have hnhds : ∀ᶠ y in 𝓝 (c.splitChart (F t x)), y ∈ c.splitChart.target :=
      c.splitChart.open_target.mem_nhds (c.splitChart.map_source' ht)
    have hm0 :
      Filter.Tendsto (fun u : ℝ => Smale.MorseHandle.descentFlow u (c.splitChart (F t x))) (𝓝 0)
        (𝓝 (c.splitChart (F t x))) := by simpa only [Flow.map_zero_apply] using hmodel.tendsto 0
    exact hm0.eventually hnhds
  filter_upwards [htime.eventually hlocal, htime.eventually htarget] with s hs hst
  rw [← F.map_add, sub_add_cancel] at hs
  have hh := congrArg c.splitChart hs
  exact hh.trans (c.splitChart.right_inv' hst)

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.morse_coordinates_of_actual_trajectory {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (x : M) {S : Set ℝ}
    (hS : IsPreconnected S) (htarget : ∀ t ∈ S, F t x ∈ c.splitChart.source)
    (heq : ∀ t ∈ S, ∀ᶠ y in 𝓝 (F t x), V y = c.descentField y) {t₀ t : ℝ} (h₀ : t₀ ∈ S)
    (ht : t ∈ S) :
    c.splitChart (F t x) = Smale.MorseHandle.descentFlow (t - t₀) (c.splitChart (F t₀ x)) :=
  flow_formula_of_local_shifts Smale.MorseHandle.descentFlow (fun s => c.splitChart (F s x)) hS
    (fun s hs => eventually_morse_coordinate_flow c hV F hF x s (htarget s hs) (heq s hs)) h₀ ht

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.morse_endpoint_tail_data {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (F : Flow ℝ M) (x : M) {l : Filter ℝ}
    (hlim : Filter.Tendsto (fun t => F t x) l (𝓝 p)) (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    Filter.Tendsto (fun t => c.splitChart (F t x)) l (𝓝 0) ∧
      ∀ᶠ t in l, F t x ∈ c.splitChart.source ∧ ∀ᶠ y in 𝓝 (F t x), V y = c.descentField y := by
  have hc := c.splitChart.toOpenPartialHomeomorph.continuousAt c.splitChart_mem_source
  have hcoord : Filter.Tendsto (fun t => c.splitChart (F t x)) l (𝓝 0) := by
    have hh : Filter.Tendsto (fun t => c.splitChart (F t x)) l (𝓝 (c.splitChart p)) :=
      hc.tendsto.comp hlim
    simpa only [c.splitChart_center] using hh
  have hsource : ∀ᶠ y in 𝓝 p, y ∈ c.splitChart.source :=
    c.splitChart.open_source.mem_nhds c.splitChart_mem_source
  have hgerm : ∀ᶠ y in 𝓝 p, ∀ᶠ z in 𝓝 y, V z = c.descentField z :=
    eventually_eventually_nhds.mpr heq
  exact ⟨hcoord, hlim.eventually (hsource.and hgerm)⟩

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.exists_incoming_morse_tail {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (x : M)
    (hlim : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    ∃ T : ℝ,
      (∀ t ≥ T, F t x ∈ c.splitChart.source) ∧
        (∀ t ≥ T, (c.splitChart (F t x)).1 = 0) ∧
          ∀ t ≥ T,
            ∀ s ≥ T,
              c.splitChart (F s x) =
                Smale.MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) := by
  obtain ⟨hcoord, htail⟩ := morse_endpoint_tail_data c F x hlim heq
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp htail
  have hformula (t : ℝ) (ht : T ≤ t) (s : ℝ) (hs : T ≤ s) :
    c.splitChart (F s x) = Smale.MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) :=
    morse_coordinates_of_actual_trajectory c hV F hF x isPreconnected_Ici
      (fun u hu => (hT u hu).1) (fun u hu => (hT u hu).2) ht hs
  refine ⟨T, fun t ht => (hT t ht).1, ?_, hformula⟩
  intro t ht
  have hnorm : Filter.Tendsto (fun s => ‖(c.splitChart (F s x)).1‖) Filter.atTop (𝓝 0) := by
    simpa only [Function.comp_def, Prod.fst_zero, norm_zero] using
      (continuous_fst.norm.tendsto (0 : c.NegativeCoordinates × c.PositiveCoordinates)).comp
        hcoord
  have hbound : ∀ᶠ s in Filter.atTop, ‖(c.splitChart (F t x)).1‖ ≤ ‖(c.splitChart (F s x)).1‖ := by
    filter_upwards [Filter.eventually_ge_atTop T, Filter.eventually_ge_atTop t] with s hs hst
    rw [hformula t ht s hs]
    exact Smale.MorseHandle.norm_fst_le_descentFlow (sub_nonneg.mpr hst) _
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto hnorm hbound) (norm_nonneg _))

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.exists_outgoing_morse_tail {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (x : M)
    (hlim : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    ∃ T : ℝ,
      (∀ t ≤ T, F t x ∈ c.splitChart.source) ∧
        (∀ t ≤ T, (c.splitChart (F t x)).2 = 0) ∧
          ∀ t ≤ T,
            ∀ s ≤ T,
              c.splitChart (F s x) =
                Smale.MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) := by
  obtain ⟨hcoord, htail⟩ := morse_endpoint_tail_data c F x hlim heq
  obtain ⟨T, hT⟩ := Filter.eventually_atBot.mp htail
  have hformula (t : ℝ) (ht : t ≤ T) (s : ℝ) (hs : s ≤ T) :
    c.splitChart (F s x) = Smale.MorseHandle.descentFlow (s - t) (c.splitChart (F t x)) :=
    morse_coordinates_of_actual_trajectory c hV F hF x isPreconnected_Iic
      (fun u hu => (hT u hu).1) (fun u hu => (hT u hu).2) ht hs
  refine ⟨T, fun t ht => (hT t ht).1, ?_, hformula⟩
  intro t ht
  have hnorm : Filter.Tendsto (fun s => ‖(c.splitChart (F s x)).2‖) Filter.atBot (𝓝 0) := by
    simpa only [Function.comp_def, Prod.snd_zero, norm_zero] using
      (continuous_snd.norm.tendsto (0 : c.NegativeCoordinates × c.PositiveCoordinates)).comp
        hcoord
  have hbound : ∀ᶠ s in Filter.atBot, ‖(c.splitChart (F t x)).2‖ ≤ ‖(c.splitChart (F s x)).2‖ := by
    filter_upwards [Filter.eventually_le_atBot T, Filter.eventually_le_atBot t] with s hs hst
    rw [hformula t ht s hs, Smale.MorseHandle.norm_descentFlow_snd]
    exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp_iff.mpr (by linarith))
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto hnorm hbound) (norm_nonneg _))

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.incoming_tail_on_cubic_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {m : ℕ}
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hcenter : (1 / 2, (0 : Fin m → ℝ)) ∈ Φ.source) (hvalue : Φ (1 / 2, 0) = p)
    (hcoord :
      ∀ q ∈ Φ.source,
        q.1 ∈ endpointFieldDomain (1 / 2) 1 ∧
          c.splitChart (Φ q) = L (endpointFieldProduct (1 / 2) 1 q))
    (F : Flow ℝ M) (x : M) (hlim : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)) {T r : ℝ}
    (hr : 0 < r) {v : c.PositiveCoordinates} (hL : L (-r, 0) = (0, v))
    (hbase : c.splitChart (F T x) = (0, v))
    (hmodel :
      ∀ t ≥ T,
        c.splitChart (F t x) = Smale.MorseHandle.descentFlow (t - T) (c.splitChart (F T x))) :
    ∀ᶠ t in Filter.atTop,
      ∃ s ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2), (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x := by
  have hp : p ∈ Φ.target := hvalue ▸ Φ.map_source' hcenter
  have htarget : ∀ᶠ t in Filter.atTop, F t x ∈ Φ.target :=
    hlim.eventually (Φ.open_target.mem_nhds hp)
  filter_upwards [htarget, Filter.eventually_ge_atTop T] with t ht hT
  have hline : c.splitChart (F t x) = L (-r * Real.exp (-(t - T)), 0) := by
    rw [hmodel t hT, hbase, ← hL]
    exact descentFlow_incoming_aligned_ray L hL (t - T)
  have hdir : 0 < -(1 : ℝ) * (-r * Real.exp (-(t - T))) := by nlinarith [Real.exp_pos (-(t - T))]
  obtain ⟨s, hs, hsource, hpoint, _⟩ :=
    cubic_axis_of_aligned_morse_ray Φ c.splitChart L (by norm_num : (1 : ℝ) ^ 2 = 1) hcoord ht
      hdir hline
  exact ⟨s, hs, hsource, hpoint⟩

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.outgoing_tail_on_cubic_axis {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {m : ℕ}
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates))
    (hcenter : (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) ∈ Φ.source) (hvalue : Φ (-(1 / 2 : ℝ), 0) = p)
    (hcoord :
      ∀ q ∈ Φ.source,
        q.1 ∈ endpointFieldDomain (1 / 2) (-1) ∧
          c.splitChart (Φ q) = L (endpointFieldProduct (1 / 2) (-1) q))
    (F : Flow ℝ M) (x : M) (hlim : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p)) {T r : ℝ}
    (hr : 0 < r) {v : c.NegativeCoordinates} (hL : L (r, 0) = (v, 0))
    (hbase : c.splitChart (F T x) = (v, 0))
    (hmodel :
      ∀ t ≤ T,
        c.splitChart (F t x) = Smale.MorseHandle.descentFlow (t - T) (c.splitChart (F T x))) :
    ∀ᶠ t in Filter.atBot,
      ∃ s ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2), (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x := by
  have hp : p ∈ Φ.target := hvalue ▸ Φ.map_source' hcenter
  have htarget : ∀ᶠ t in Filter.atBot, F t x ∈ Φ.target :=
    hlim.eventually (Φ.open_target.mem_nhds hp)
  filter_upwards [htarget, Filter.eventually_le_atBot T] with t ht hT
  have hline : c.splitChart (F t x) = L (r * Real.exp (t - T), 0) := by
    rw [hmodel t hT, hbase, ← hL]
    exact descentFlow_outgoing_aligned_ray L hL (t - T)
  have hdir : 0 < -(-1 : ℝ) * (r * Real.exp (t - T)) := by
    simpa using mul_pos hr (Real.exp_pos (t - T))
  obtain ⟨s, hs, hsource, hpoint, _⟩ :=
    cubic_axis_of_aligned_morse_ray Φ c.splitChart L (by norm_num : (-1 : ℝ) ^ 2 = 1) hcoord ht
      hdir hline
  exact ⟨s, hs, hsource, hpoint⟩

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.morse_coordinates_nonzero_on_nonstationary_orbit {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {x : M} (hxp : x ≠ p)
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) {t : ℝ} (ht : F t x ∈ c.splitChart.source) :
    c.splitChart (F t x) ≠ 0 := by
  have heqp : V p = c.descentField p :=
    mem_of_mem_nhds (x := p) (s := {y : M | V y = c.descentField y}) heq
  have hVp : V p = 0 := heqp.trans c.descentField_center
  have hfixed := Smale.FlowConstruction.flow_fixed_of_zero hV F hF hVp
  intro hz
  have hpoint : F t x = p :=
    c.splitChart.toOpenPartialHomeomorph.injOn ht c.splitChart_mem_source
      (hz.trans c.splitChart_center.symm)
  have hh := congrArg (F (-t)) hpoint
  rw [← F.map_add, neg_add_cancel, F.map_zero_apply, hfixed] at hh
  exact hxp hh

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.exists_actual_incoming_cubic_endpoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ Option.none) = 1)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {x : M} (hxp : x ≠ p)
    (hlim : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    let σ := fun i : Fin m => c.weights (ρ (Option.some i))
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (1 / 2, (0 : Fin m → ℝ)) ∈ Φ.source ∧
        Φ (1 / 2, 0) = p ∧
          Φ.target ⊆ c.splitChart.source ∧
            (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
              (∀ᶠ t in Filter.atTop,
                  ∃ s ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2),
                    (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x) ∧
                ∃ L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates),
                  (∀ z, L (endpointLinearField σ (1 / 2) 1 z) = Smale.MorseHandle.descent (L z)) ∧
                    ∀ z ∈ Φ.source, c.splitChart (Φ z) = L (endpointFieldProduct (1 / 2) 1 z) := by
  let σ := fun i : Fin m => c.weights (ρ (Option.some i))
  obtain ⟨T, hsource, hzero, hformula⟩ := exists_incoming_morse_tail c hV F hF x hlim heq
  let v := (c.splitChart (F T x)).2
  have hbase : c.splitChart (F T x) = (0, v) := Prod.ext (hzero T le_rfl) rfl
  have hv : v ≠ 0 := by
    intro hv
    exact
      morse_coordinates_nonzero_on_nonstationary_orbit c hV F hF hxp heq (hsource T le_rfl)
        (hbase.trans (Prod.ext rfl hv))
  obtain ⟨r, L, hr, hLray, hL⟩ := exists_selected_incoming_axis c ρ he hv
  have hL' : ∀ q, L (endpointLinearField σ (1 / 2) 1 q) = Smale.MorseHandle.descent (L q) := by
    simpa only [he] using hL
  obtain ⟨Φ, hc, hval, hsub, hfield, hcoord⟩ :=
    exists_controlled_morse_field_endpoint c σ (by norm_num : (1 : ℝ) ^ 2 = 1) L hL' V heq
  refine ⟨Φ, hc, hval, hsub, hfield, ?_, L, hL', ?_⟩
  · exact
      incoming_tail_on_cubic_axis c Φ L hc hval hcoord F x hlim hr hLray hbase (hformula T le_rfl)
  · exact fun z hz => (hcoord z hz).2

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.exists_actual_outgoing_cubic_endpoint {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {m : ℕ}
    (ρ : Option (Fin m) ≃ Fin (Module.finrank ℝ E)) (he : c.weights (ρ Option.none) = -1)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) {x : M} (hxp : x ≠ p)
    (hlim : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p))
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) :
    let σ := fun i : Fin m => c.weights (ρ (Option.some i))
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) ∈ Φ.source ∧
        Φ (-(1 / 2 : ℝ), 0) = p ∧
          Φ.target ⊆ c.splitChart.source ∧
            (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(1 / 2 : ℝ) ^ 2) y) ∧
              (∀ᶠ t in Filter.atBot,
                  ∃ s ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2),
                    (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x) ∧
                ∃ L : Model m ≃L[ℝ] (c.NegativeCoordinates × c.PositiveCoordinates),
                  (∀ z,
                      L (endpointLinearField σ (1 / 2) (-1) z) =
                        Smale.MorseHandle.descent (L z)) ∧
                    ∀ z ∈ Φ.source,
                      c.splitChart (Φ z) = L (endpointFieldProduct (1 / 2) (-1) z) := by
  let σ := fun i : Fin m => c.weights (ρ (Option.some i))
  obtain ⟨T, hsource, hzero, hformula⟩ := exists_outgoing_morse_tail c hV F hF x hlim heq
  let v := (c.splitChart (F T x)).1
  have hbase : c.splitChart (F T x) = (v, 0) := Prod.ext rfl (hzero T le_rfl)
  have hv : v ≠ 0 := by
    intro hv
    exact
      morse_coordinates_nonzero_on_nonstationary_orbit c hV F hF hxp heq (hsource T le_rfl)
        (hbase.trans (Prod.ext hv rfl))
  obtain ⟨r, L, hr, hLray, hL⟩ := exists_selected_outgoing_axis c ρ he hv
  have hL' : ∀ q, L (endpointLinearField σ (1 / 2) (-1) q) = Smale.MorseHandle.descent (L q) := by
    simpa only [he] using hL
  obtain ⟨Φ, hc, hval, hsub, hfield, hcoord⟩ :=
    exists_controlled_morse_field_endpoint c σ (by norm_num : (-1 : ℝ) ^ 2 = 1) L hL' V heq
  have hc' : (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) ∈ Φ.source := by convert! hc using 1; norm_num
  have hval' : Φ (-(1 / 2 : ℝ), 0) = p := by convert! hval using 1; norm_num
  refine ⟨Φ, hc', hval', hsub, hfield, ?_, L, hL', ?_⟩
  · exact
      outgoing_tail_on_cubic_axis c Φ L hc' hval' hcoord F x hlim hr hLray hbase
        (hformula T le_rfl)
  · exact fun z hz => (hcoord z hz).2

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.native_backward_basin_mem_attaching_core {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (r : ℝ) (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (hfield :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (hboundary : ∀ x, f x = f p - r ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) {x : M}
    (hlevel : f x = f p - r ^ 2) (hlim : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p)) :
    ∃ u : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates,
      (c.attachingCoreMap r hr hblock u : M) = x := by
  have hV₁ := hV.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  have hcenter : c.splitChart.symm (0 : c.NegativeCoordinates × c.PositiveCoordinates) = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have heq :=
    hfield (0 : c.NegativeCoordinates × c.PositiveCoordinates)
      ⟨Metric.mem_closedBall_self (by positivity), Metric.mem_closedBall_self (by positivity)⟩
  rw [hcenter] at heq
  obtain ⟨T, hsource, hplane, -⟩ := exists_outgoing_morse_tail c hV₁ F hF x hlim heq
  obtain ⟨hcoord, -⟩ := morse_endpoint_tail_data c F x hlim heq
  have hnorm : Filter.Tendsto (fun t => ‖(c.splitChart (F t x)).1‖) Filter.atBot (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Prod.fst_zero, norm_zero] using
      (continuous_fst.norm.tendsto (0 : c.NegativeCoordinates × c.PositiveCoordinates)).comp
        hcoord
  obtain ⟨s, hsmall, hs⟩ :=
    ((hnorm.eventually (eventually_lt_nhds hr)).and (Filter.eventually_le_atBot T)).exists
  have hxp : x ≠ p := by
    intro hh
    rw [hh] at hlevel
    nlinarith [sq_pos_of_pos hr]
  have hnonzero :=
    morse_coordinates_nonzero_on_nonstationary_orbit c hV₁ F hF hxp heq (hsource s hs)
  have hn : (c.splitChart (F s x)).1 ≠ 0 := fun hz => hnonzero (Prod.ext hz (hplane s hs))
  obtain ⟨u, t, ht, hu⟩ := exists_negative_core_ray_parameter hr hn hsmall
  have hmodel :
    Smale.MorseHandle.descentFlow t
        (r • (u : c.NegativeCoordinates), (0 : c.PositiveCoordinates)) =
      c.splitChart (F s x) := by
    apply Prod.ext
    · exact hu
    · change Real.exp (-t) • (0 : c.PositiveCoordinates) = (c.splitChart (F s x)).2
      rw [smul_zero, hplane s hs]
  have hcore := native_attaching_core_flow c hV₁ F hF r hr hblock hfield u ht.le
  rw [hmodel] at hcore
  have hsame : F t (c.attachingCoreMap r hr hblock u) = F s x :=
    hcore.trans (c.splitChart.left_inv' (hsource s hs))
  exact
    ⟨u,
      native_same_level_orbit_points hf hV F hF hboundary
        (c.attachingCoreMap r hr hblock u).property hlevel hsame⟩

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.native_attaching_core_basin_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (r : ℝ) (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (hfield :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (hboundary : ∀ x, f x = f p - r ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) {x : M}
    (hlevel : f x = f p - r ^ 2) :
    Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p) ↔
      ∃ u : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates,
        (c.attachingCoreMap r hr hblock u : M) = x := by
  constructor
  · exact
      native_backward_basin_mem_attaching_core c hf hV F hF r hr hblock hfield hboundary hlevel
  · rintro ⟨u, rfl⟩
    exact native_attaching_core_backward_limit c (hV.of_le (by simp)) F hF r hr hblock hfield u

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.native_forward_basin_mem_belt_core {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (r : ℝ) (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (hfield :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (hboundary : ∀ x, f x = f p + r ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) {x : M}
    (hlevel : f x = f p + r ^ 2) (hlim : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)) :
    ∃ u : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates,
      (c.beltCoreMap r hr hblock u : M) = x := by
  have hV₁ := hV.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  have hcenter : c.splitChart.symm (0 : c.NegativeCoordinates × c.PositiveCoordinates) = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have heq :=
    hfield (0 : c.NegativeCoordinates × c.PositiveCoordinates)
      ⟨Metric.mem_closedBall_self (by positivity), Metric.mem_closedBall_self (by positivity)⟩
  rw [hcenter] at heq
  obtain ⟨T, hsource, hplane, -⟩ := exists_incoming_morse_tail c hV₁ F hF x hlim heq
  obtain ⟨hcoord, -⟩ := morse_endpoint_tail_data c F x hlim heq
  have hnorm : Filter.Tendsto (fun t => ‖(c.splitChart (F t x)).2‖) Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Prod.snd_zero, norm_zero] using
      (continuous_snd.norm.tendsto (0 : c.NegativeCoordinates × c.PositiveCoordinates)).comp
        hcoord
  obtain ⟨s, hsmall, hs⟩ :=
    ((hnorm.eventually (eventually_lt_nhds hr)).and (Filter.eventually_ge_atTop T)).exists
  have hxp : x ≠ p := by
    intro hh
    rw [hh] at hlevel
    nlinarith [sq_pos_of_pos hr]
  have hnonzero :=
    morse_coordinates_nonzero_on_nonstationary_orbit c hV₁ F hF hxp heq (hsource s hs)
  have hn : (c.splitChart (F s x)).2 ≠ 0 := fun hz => hnonzero (Prod.ext (hplane s hs) hz)
  obtain ⟨u, t, ht, hu⟩ := exists_positive_core_ray_parameter hr hn hsmall
  have hmodel :
    Smale.MorseHandle.descentFlow t
        ((0 : c.NegativeCoordinates), r • (u : c.PositiveCoordinates)) =
      c.splitChart (F s x) := by
    apply Prod.ext
    · change Real.exp t • (0 : c.NegativeCoordinates) = (c.splitChart (F s x)).1
      rw [smul_zero, hplane s hs]
    · exact hu
  have hcore := native_belt_core_flow c hV₁ F hF r hr hblock hfield u ht.le
  rw [hmodel] at hcore
  have hsame : F t (c.beltCoreMap r hr hblock u) = F s x :=
    hcore.trans (c.splitChart.left_inv' (hsource s hs))
  exact
    ⟨u,
      native_same_level_orbit_points hf hV F hF hboundary (c.beltCoreMap r hr hblock u).property
        hlevel hsame⟩

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.native_belt_core_basin_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {f : M → ℝ} {p : M} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (r : ℝ) (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (hfield :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    (hboundary : ∀ x, f x = f p + r ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) {x : M}
    (hlevel : f x = f p + r ^ 2) :
    Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) ↔
      ∃ u : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates,
        (c.beltCoreMap r hr hblock u : M) = x := by
  constructor
  · exact native_forward_basin_mem_belt_core c hf hV F hF r hr hblock hfield hboundary hlevel
  · rintro ⟨u, rfl⟩
    exact native_belt_core_forward_limit c (hV.of_le (by simp)) F hF r hr hblock hfield u

attribute [local instance 100] Classical.propDecidable in
private theorem
    AdaptedWindows.attaching_basin_iff {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : Smale.ManifoldMorse.criticalPoints E f) (x : (S.data p).LowerLevel) :
    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val) ↔
      x ∈ Set.range (S.data p).surgery.attachingSphere := by
  let d := S.data p
  have hh :=
    MorseCancel.native_attaching_core_basin_iff d.chart hf S.smooth S.flow S.integral d.radius
      d.radius_pos d.block (S.model_germ p) (fun y hy => S.descent y (d.lower_regular y hy))
      x.property
  rw [d.attaching_eq]
  exact hh.trans ⟨fun ⟨u, hu⟩ => ⟨u, Subtype.ext hu⟩, fun ⟨u, hu⟩ => ⟨u, congrArg Subtype.val hu⟩⟩

attribute [local instance 100] Classical.propDecidable in
private theorem AdaptedWindows.belt_basin_iff {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : Smale.ManifoldMorse.criticalPoints E f) (x : (S.data p).UpperLevel) :
    Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val) ↔
      x ∈ Set.range (S.data p).surgery.beltSphere := by
  let d := S.data p
  have hh :=
    MorseCancel.native_belt_core_basin_iff d.chart hf S.smooth S.flow S.integral d.radius
      d.radius_pos d.block (S.model_germ p) (fun y hy => S.descent y (d.upper_regular y hy))
      x.property
  rw [d.belt_eq]
  exact hh.trans ⟨fun ⟨u, hu⟩ => ⟨u, Subtype.ext hu⟩, fun ⟨u, hu⟩ => ⟨u, congrArg Subtype.val hu⟩⟩

attribute [local instance 100] Classical.propDecidable in
private theorem
    AdaptedWindows.critical_model_germ {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (p : Smale.ManifoldMorse.criticalPoints E f) :
    ∀ᶠ y in 𝓝 p.val, S.field y = (S.data p).chart.descentField y := by
  let d := S.data p
  have hcenter :
    d.chart.splitChart.symm (0 : d.chart.NegativeCoordinates × d.chart.PositiveCoordinates) =
      p.val := by
    rw [← d.chart.splitChart_center]
    exact d.chart.splitChart.left_inv' d.chart.splitChart_mem_source
  have hg :=
    S.model_germ p (0 : d.chart.NegativeCoordinates × d.chart.PositiveCoordinates)
      ⟨Metric.mem_closedBall_self (le_of_lt (mul_pos (by norm_num) d.radius_pos)),
        Metric.mem_closedBall_self (le_of_lt (mul_pos (by norm_num) d.radius_pos))⟩
  rw [hcenter] at hg
  exact hg

private theorem
    MorseCancel.hasDerivAt_tanh (t : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh t ^ 2) t := by
  have h := (Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) (Real.cosh_pos t).ne'
  have hf : (fun x => Real.sinh x / Real.cosh x) = Real.tanh :=
    funext (fun x => (Real.tanh_eq_sinh_div_cosh x).symm)
  change HasDerivAt (fun x => Real.sinh x / Real.cosh x) _ t at h
  rw [hf] at h
  convert h using 1
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

private theorem MorseCancel.strictMono_tanh : StrictMono Real.tanh :=
  strictMono_of_hasDerivAt_pos hasDerivAt_tanh (fun t => sub_pos.mpr (Real.tanh_sq_lt_one t))

private theorem MorseCancel.range_tanh : Set.range Real.tanh = Set.Ioo (-1 : ℝ) 1 := by
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨Real.neg_one_lt_tanh t, Real.tanh_lt_one t⟩
  · intro hs
    obtain ⟨t, -, ht⟩ := Real.tanh_surjOn hs
    exact ⟨t, ht⟩

private theorem
    MorseCancel.tendsto_tanh_atTop : Filter.Tendsto Real.tanh Filter.atTop (𝓝 (1 : ℝ)) := by
  apply tendsto_atTop_isLUB strictMono_tanh.monotone
  rw [range_tanh]
  exact isLUB_Ioo (by norm_num)

private theorem
    MorseCancel.tendsto_tanh_atBot : Filter.Tendsto Real.tanh Filter.atBot (𝓝 (-1 : ℝ)) := by
  apply tendsto_atBot_isGLB strictMono_tanh.monotone
  rw [range_tanh]
  exact isGLB_Ioo (by norm_num)

private def MorseCancel.cubicAxisParameter (a t : ℝ) : ℝ :=
  a * Real.tanh (a * t)

private theorem MorseCancel.hasDerivAt_cubicAxisParameter (a t : ℝ) :
    HasDerivAt (cubicAxisParameter a) (a ^ 2 - cubicAxisParameter a t ^ 2) t := by
  have h := ((hasDerivAt_tanh (a * t)).comp t ((hasDerivAt_id t).const_mul a)).const_mul a
  change HasDerivAt (cubicAxisParameter a) (a * ((1 - Real.tanh (a * t) ^ 2) * (a * 1))) t at h
  convert h using 1
  dsimp [cubicAxisParameter]
  ring

private theorem MorseCancel.cubicAxisParameter_mem {a : ℝ} (ha : 0 < a) (t : ℝ) :
    cubicAxisParameter a t ∈ Set.Ioo (-a) a := by
  have hlo := mul_lt_mul_of_pos_left (Real.neg_one_lt_tanh (a * t)) ha
  have hhi := mul_lt_mul_of_pos_left (Real.tanh_lt_one (a * t)) ha
  constructor
  · simpa only [cubicAxisParameter, mul_neg, mul_one] using hlo
  · simpa only [cubicAxisParameter, mul_one] using hhi

private theorem MorseCancel.range_cubicAxisParameter {a : ℝ} (ha : 0 < a) :
    Set.range (cubicAxisParameter a) = Set.Ioo (-a) a := by
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    exact cubicAxisParameter_mem ha t
  · intro hs
    have hs' : s / a ∈ Set.Ioo (-1 : ℝ) 1 := by
      constructor
      · apply (lt_div_iff₀ ha).mpr
        simpa only [neg_one_mul] using hs.1
      · apply (div_lt_iff₀ ha).mpr
        simpa only [one_mul] using hs.2
    refine ⟨Real.artanh (s / a) / a, ?_⟩
    simp only [cubicAxisParameter, mul_div_cancel₀ _ ha.ne', Real.tanh_artanh hs']

private theorem MorseCancel.tendsto_cubicAxisParameter_atTop {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (cubicAxisParameter a) Filter.atTop (𝓝 a) := by
  have h := (tendsto_tanh_atTop.comp (Filter.tendsto_id.const_mul_atTop ha)).const_mul a
  change Filter.Tendsto (cubicAxisParameter a) Filter.atTop (𝓝 (a * 1)) at h
  simpa only [mul_one] using h

private theorem MorseCancel.tendsto_cubicAxisParameter_atBot {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (cubicAxisParameter a) Filter.atBot (𝓝 (-a)) := by
  have h := (tendsto_tanh_atBot.comp (Filter.tendsto_id.const_mul_atBot ha)).const_mul a
  change Filter.Tendsto (cubicAxisParameter a) Filter.atBot (𝓝 (a * -1)) at h
  simpa only [mul_neg, mul_one] using h

private def MorseCancel.cubicModelOrbit {m : ℕ} (a t : ℝ) : Model m :=
  (cubicAxisParameter a t, 0)

private theorem
    MorseCancel.cubicModelOrbit_zero {m : ℕ} (a : ℝ) : cubicModelOrbit (m := m) a 0 = 0 := by
  simp [cubicModelOrbit, cubicAxisParameter, Real.tanh_zero]

private theorem MorseCancel.hasDerivAt_cubicModelOrbit {m : ℕ} (σ : Fin m → ℝ) (a t : ℝ) :
    HasDerivAt (cubicModelOrbit a) (cubicDescent σ (-(a ^ 2)) (cubicModelOrbit a t)) t := by
  have h := (hasDerivAt_cubicAxisParameter a t).prodMk (hasDerivAt_const t (0 : Fin m → ℝ))
  change HasDerivAt (cubicModelOrbit a) (a ^ 2 - cubicAxisParameter a t ^ 2, 0) t at h
  convert h using 1
  apply Prod.ext
  · change -(cubicAxisParameter a t ^ 2 + -(a ^ 2)) = a ^ 2 - cubicAxisParameter a t ^ 2
    ring
  · funext i
    simp only [cubicDescent, cubicModelOrbit, Pi.zero_apply, MulZeroClass.mul_zero]

private theorem MorseCancel.range_cubicModelOrbit {m : ℕ} {a : ℝ} (ha : 0 < a) :
    Set.range (cubicModelOrbit (m := m) a) = Set.Ioo (-a) a ×ˢ {(0 : Fin m → ℝ)} := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨cubicAxisParameter_mem ha t, rfl⟩
  · rintro ⟨hs, hz⟩
    obtain ⟨t, ht⟩ := (range_cubicAxisParameter ha).symm ▸ hs
    refine ⟨t, ?_⟩
    exact Prod.ext ht (show (0 : Fin m → ℝ) = p.2 from hz.symm)

private theorem MorseCancel.tendsto_cubicModelOrbit_atTop {m : ℕ} {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (cubicModelOrbit (m := m) a) Filter.atTop (𝓝 (a, 0)) :=
  (tendsto_cubicAxisParameter_atTop ha).prodMk_nhds tendsto_const_nhds

private theorem MorseCancel.tendsto_cubicModelOrbit_atBot {m : ℕ} {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (cubicModelOrbit (m := m) a) Filter.atBot (𝓝 (-a, 0)) :=
  (tendsto_cubicAxisParameter_atBot ha).prodMk_nhds tendsto_const_nhds

private theorem MorseCancel.contDiffAt_artanh {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ContDiffAt ℝ ∞ Real.artanh x := by
  have hp : 0 < (1 + x) / (1 - x) := div_pos (by linarith [hx.1]) (by linarith [hx.2])
  have hr : ContDiffAt ℝ ∞ (fun y : ℝ => (1 + y) / (1 - y)) x :=
    (contDiffAt_const.add contDiffAt_id).div (contDiffAt_const.sub contDiffAt_id)
      (by linarith [hx.2])
  exact (hr.sqrt hp.ne').log (Real.sqrt_pos.mpr hp).ne'

end Mathoverflow1973

end
