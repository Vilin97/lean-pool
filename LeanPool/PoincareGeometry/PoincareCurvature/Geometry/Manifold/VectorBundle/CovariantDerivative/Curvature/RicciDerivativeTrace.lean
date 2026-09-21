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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurckCorrectionRegularity
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearEvaluation

/-!
# Covariant differentiation of the geometric Ricci contraction

This file identifies the covariant derivative of the genuine Ricci tensor with the metric trace of
the covariant derivative of the genuine curvature tensor.  The proof differentiates a fibrewise
endomorphism trace, using actual local frames and the induced hom-bundle connection.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff BigOperators

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [SigmaCompactSpace M]
  [IsManifold I ∞ M]
  [hContTangent : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsManifold I (minSmoothness ℝ 2) M] [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I (minSmoothness ℝ 4) M]
  [IsManifold I ((2 : ℕ∞) + 1) M] [IsManifold I ((3 : ℕ∞) + 1) M]

local notation "TM" => (TangentSpace I : M → Type _)

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]

/-- The curvature endomorphism obtained by fixing the final two curvature arguments along canonical
smooth extensions is differentiable at the base point. -/
theorem curvatureEndomorphism_mdifferentiableAt
    (x : M) (u v : TM x) :
    MDiffAt
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M ↦ TM z →L[ℝ] TM z) y
        (LinearMap.toContinuousLinearMap
          (ricciEndomorphism cov y
            (smoothExtend (I := I) (F := E) (V := TM) x u y)
            (smoothExtend (I := I) (F := E) (V := TM) x v y)))) x := by
  classical
  let e := trivializationAt E TM x
  let b := Module.finBasis ℝ E
  let U : ∀ y : M, TM y := smoothExtend (I := I) (F := E) (V := TM) x u
  let V : ∀ y : M, TM y := smoothExtend (I := I) (F := E) (V := TM) x v
  refine (contMDiffAt_homBundle_of_forall_apply_localFrame
    (IB := I) (E₁ := TM) (E₂ := TM) x b ?_).mdifferentiableAt one_ne_zero
  intro i
  have hbase : IsOpen e.baseSet := e.open_baseSet
  have hframe : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
      (fun y ↦ TotalSpace.mk' E y (e.localFrame b i y)) e.baseSet :=
    e.contMDiffOn_localFrame_baseSet (I := I) (n := 2) b i
  have hU : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (T% U) e.baseSet :=
    (smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x u).contMDiffOn
  have hV : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3 (T% V) e.baseSet :=
    (smoothExtend_contMDiff_three (I := I) (E := E) (M := M) x v).contMDiffOn
  have hcurv := RicciFlow.curvatureTensor_contMDiffOn_frame_one
    (cov := cov) hbase hframe hU hV
  have hat := hcurv.contMDiffAt
    (hbase.mem_nhds (FiberBundle.mem_baseSet_trivializationAt E TM x))
  refine hat.congr_of_eventuallyEq ?_
  filter_upwards [] with y
  apply congrArg (TotalSpace.mk' E y)
  rfl

/-- Differentiating the curvature endomorphism gives the actual covariant derivative of curvature,
plus exactly the two correction terms from its moving fixed arguments. -/
theorem curvatureEndomorphismDerivative_apply
    (x : M) (p z u v : TM x) :
    let W : ∀ y : M, TM y := smoothExtend (I := I) (F := E) (V := TM) x z
    let U : ∀ y : M, TM y := smoothExtend (I := I) (F := E) (V := TM) x u
    let V : ∀ y : M, TM y := smoothExtend (I := I) (F := E) (V := TM) x v
    cov (fun y ↦ curvatureTensor (cov := cov) y (W y) (U y) (V y)) x p -
        curvatureTensor (cov := cov) x (cov W x p) u v =
      curvatureCovariantDerivative cov x p z u v +
        curvatureTensor (cov := cov) x z (cov U x p) v +
        curvatureTensor (cov := cov) x z u (cov V x p) := by
  classical
  dsimp only
  let X : ∀ y : M, TM y := smoothExtend (I := I) (F := E) (V := TM) x p
  let W : ∀ y : M, TM y := smoothExtend (I := I) (F := E) (V := TM) x z
  let U : ∀ y : M, TM y := smoothExtend (I := I) (F := E) (V := TM) x u
  let V : ∀ y : M, TM y := smoothExtend (I := I) (F := E) (V := TM) x v
  have hX2 : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% X) :=
    smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x p
  have hW3 : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% W) :=
    smoothExtend_contMDiff_three (I := I) (E := E) (M := M) x z
  have hU3 : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% U) :=
    smoothExtend_contMDiff_three (I := I) (E := E) (M := M) x u
  have hV3 : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% V) :=
    smoothExtend_contMDiff_three (I := I) (E := E) (M := M) x v
  have hraw :
      (fun y ↦ curvatureTensor (cov := cov) y (W y) (U y) (V y)) =
        cov.curvatureAux W U V := by
    funext y
    exact (RicciFlow.curvatureAux_apply_eq_curvatureTensor_of_contMDiffOn_frame
      (cov := cov) isOpen_univ (Set.mem_univ y)
      (hW3.contMDiffOn.of_le (by norm_num)) (hU3.contMDiffOn.of_le (by norm_num))
      (hV3.contMDiffOn.of_le (by norm_num))).symm
  have hcovraw := congrArg (fun S : ∀ y : M, TM y ↦ cov S x p) hraw
  have hXW2 : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% (cov.along X W)) :=
    cov.contMDiff_along (n := 2) hX2 hW3
  have hXU2 : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% (cov.along X U)) :=
    cov.contMDiff_along (n := 2) hX2 hU3
  have hXV2 : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% (cov.along X V)) :=
    cov.contMDiff_along (n := 2) hX2 hV3
  have hslotW := RicciFlow.curvatureAux_apply_eq_curvatureTensor_of_contMDiffOn_frame
    (cov := cov) isOpen_univ (Set.mem_univ x) hXW2.contMDiffOn
    (hU3.contMDiffOn.of_le (by norm_num)) (hV3.contMDiffOn.of_le (by norm_num))
  have hslotU := RicciFlow.curvatureAux_apply_eq_curvatureTensor_of_contMDiffOn_frame
    (cov := cov) isOpen_univ (Set.mem_univ x) (hW3.contMDiffOn.of_le (by norm_num))
    hXU2.contMDiffOn (hV3.contMDiffOn.of_le (by norm_num))
  have hslotV := RicciFlow.curvatureAux_apply_eq_curvatureTensor_of_contMDiffOn_frame
    (cov := cov) isOpen_univ (Set.mem_univ x) (hW3.contMDiffOn.of_le (by norm_num))
    (hU3.contMDiffOn.of_le (by norm_num)) hXV2.contMDiffOn
  rw [hcovraw]
  simp only [curvatureCovariantDerivative, secondBianchiAux_apply]
  simp only [X, W, U, V, smoothExtend_apply] at hslotW hslotU hslotV ⊢
  rw [hslotW, hslotU, hslotV]
  simp only [CovariantDerivative.along_apply, smoothExtend_apply]
  abel

/-! ### The Ricci contraction -/

/- The derivative of the curvature endomorphism with two moving curvature
arguments, using the model-space norm internally. -/
def curvatureEndomorphismCovariantDerivativeApply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
    (x : M) (p u v z : TangentSpace I x) : TangentSpace I x := by
  letI nTM : ∀ y : M, NormedAddCommGroup (TangentSpace I y) := fun y =>
    PoincareCurvature.instNormedAddCommGroupTangentSpace I y
  letI sTM : ∀ y : M, NormedSpace ℝ (TangentSpace I y) := fun _ =>
    PoincareCurvature.instNormedSpaceTangentSpace I _
  letI fTM : ∀ y : M, FiniteDimensional ℝ (TangentSpace I y) := fun _ =>
    inferInstanceAs (FiniteDimensional ℝ E)
  let U : ∀ y : M, TangentSpace I y :=
    smoothExtend (I := I) (F := E) (V := TangentSpace I) x u
  let V : ∀ y : M, TangentSpace I y :=
    smoothExtend (I := I) (F := E) (V := TangentSpace I) x v
  let A : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y := fun y =>
    LinearMap.toContinuousLinearMap
      (ricciEndomorphism (cov := cov) y (U y) (V y))
  let hContOne : ContMDiffVectorBundle 1 E TM I :=
    @ContMDiffVectorBundle.of_le
      ℝ M E TM _ E _ _ H _ I _ _ _ _ _ _ _ _
      TangentSpace.fiberBundle TangentSpace.vectorBundle
      1 2 one_le_two hContTangent
  let d := @inducedHomCovariantDerivative
    E _ _ H _ I M _ _ _ _ _ _
    E E _ _ _ _ _
    (TangentSpace I : M → Type _) (TangentSpace I : M → Type _)
      _ _ nTM sTM fTM nTM sTM
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    hContTangent hContOne cov cov
  exact d A x p z

/- The product rule for the internal curvature-endomorphism derivative. -/
theorem curvatureEndomorphismCovariantDerivativeApply_eq
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
    (x : M) (p u v z : TangentSpace I x) :
    curvatureEndomorphismCovariantDerivativeApply cov x p u v z =
      curvatureCovariantDerivative cov x p z u v +
        curvatureTensor (cov := cov) x z
          (cov (smoothExtend (I := I) (F := E)
            (V := TangentSpace I) x u) x p) v +
        curvatureTensor (cov := cov) x z u
          (cov (smoothExtend (I := I) (F := E)
            (V := TangentSpace I) x v) x p) := by
  classical
  unfold curvatureEndomorphismCovariantDerivativeApply
  dsimp only
  let U : ∀ y : M, TangentSpace I y :=
    smoothExtend (I := I) (F := E) (V := TangentSpace I) x u
  let V : ∀ y : M, TangentSpace I y :=
    smoothExtend (I := I) (F := E) (V := TangentSpace I) x v
  let A : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y := fun y =>
    LinearMap.toContinuousLinearMap
      (ricciEndomorphism (cov := cov) y (U y) (V y))
  let hA : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun q : M => TangentSpace I q →L[ℝ] TangentSpace I q) y (A y)) x := by
    simpa [A, U, V] using
      (curvatureEndomorphism_mdifferentiableAt
        (I := I) (E := E) (M := M) cov x u v)
  let hContOne : ContMDiffVectorBundle 1 E TM I :=
    @ContMDiffVectorBundle.of_le
      ℝ M E TM _ E _ _ H _ I _ _ _ _ _ _ _ _
      TangentSpace.fiberBundle TangentSpace.vectorBundle
      1 2 one_le_two hContTangent
  let d := @inducedHomCovariantDerivative
    E _ _ H _ I M _ _ _ _ _ _
    E E _ _ _ _ _
    (TangentSpace I : M → Type _) (TangentSpace I : M → Type _)
      _ _ (PoincareCurvature.instNormedAddCommGroupTangentSpace I)
        (PoincareCurvature.instNormedSpaceTangentSpace I)
        (fun _ => inferInstanceAs (FiniteDimensional ℝ E))
        (PoincareCurvature.instNormedAddCommGroupTangentSpace I)
        (PoincareCurvature.instNormedSpaceTangentSpace I)
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    hContTangent hContOne cov cov
  change d A x p z = _
  have hbase : d A x p z =
      cov (fun y => A y
        (smoothExtend (I := I) (F := E) (V := TangentSpace I) x z y)) x p -
        A x (cov (smoothExtend (I := I) (F := E)
          (V := TangentSpace I) x z) x p) := by
    unfold d inducedHomCovariantDerivative
    dsimp only
    split
    next _ => rfl
    next h => exact (h hA).elim
  rw [hbase]
  have hcurv := curvatureEndomorphismDerivative_apply
    (I := I) (E := E) (M := M) cov x p z u v
  have hAeval : (fun y => A y
      (smoothExtend (I := I) (F := E) (V := TangentSpace I) x z y)) =
      (fun y => curvatureTensor (cov := cov) y
        (smoothExtend (I := I) (F := E) (V := TangentSpace I) x z y)
        (U y) (V y)) := by
    funext y
    change ricciEndomorphism (cov := cov) y (U y) (V y)
      (smoothExtend (I := I) (F := E) (V := TangentSpace I) x z y) = _
    rfl
  have hAat : A x
      (cov (smoothExtend (I := I) (F := E) (V := TangentSpace I) x z) x p) =
      curvatureTensor (cov := cov) x
        (cov (smoothExtend (I := I) (F := E) (V := TangentSpace I) x z) x p)
        u v := by
    change ricciEndomorphism (cov := cov) x (U x) (V x)
      (cov (smoothExtend (I := I) (F := E) (V := TangentSpace I) x z) x p) = _
    simp only [ricciEndomorphism_apply, U, V, smoothExtend_apply]
  rw [hAeval, hAat]
  simpa only [U, V, smoothExtend_apply] using hcurv

/- Trace of the internal derivative in a module basis. -/
def curvatureEndomorphismTraceCovariantDerivative
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
    (x : M) (p u v : TangentSpace I x) : ℝ := by
  letI nTM : ∀ y : M, NormedAddCommGroup (TangentSpace I y) := fun y =>
    PoincareCurvature.instNormedAddCommGroupTangentSpace I y
  letI sTM : ∀ y : M, NormedSpace ℝ (TangentSpace I y) := fun _ =>
    PoincareCurvature.instNormedSpaceTangentSpace I _
  letI fTM : ∀ y : M, FiniteDimensional ℝ (TangentSpace I y) := fun _ =>
    inferInstanceAs (FiniteDimensional ℝ E)
  let U : ∀ y : M, TangentSpace I y :=
    smoothExtend (I := I) (F := E) (V := TangentSpace I) x u
  let V : ∀ y : M, TangentSpace I y :=
    smoothExtend (I := I) (F := E) (V := TangentSpace I) x v
  let A : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y := fun y =>
    LinearMap.toContinuousLinearMap
      (ricciEndomorphism (cov := cov) y (U y) (V y))
  let hContOne : ContMDiffVectorBundle 1 E TM I :=
    @ContMDiffVectorBundle.of_le
      ℝ M E TM _ E _ _ H _ I _ _ _ _ _ _ _ _
      TangentSpace.fiberBundle TangentSpace.vectorBundle
      1 2 one_le_two hContTangent
  let d := @inducedHomCovariantDerivative
    E _ _ H _ I M _ _ _ _ _ _
    E E _ _ _ _ _
    (TangentSpace I : M → Type _) (TangentSpace I : M → Type _)
      _ _ nTM sTM fTM nTM sTM
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    hContTangent hContOne cov cov
  exact LinearMap.trace ℝ (TangentSpace I x) ((d A x p).toLinearMap)

theorem curvatureEndomorphismTraceCovariantDerivative_eq_sum_basis
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
    (x : M) (p u v : TangentSpace I x)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ (TangentSpace I x)) :
    curvatureEndomorphismTraceCovariantDerivative cov x p u v =
      ∑ i, b.repr (curvatureEndomorphismCovariantDerivativeApply
        cov x p u v (b i)) i := by
  classical
  letI nTM : ∀ y : M, NormedAddCommGroup (TangentSpace I y) := fun y =>
    PoincareCurvature.instNormedAddCommGroupTangentSpace I y
  letI sTM : ∀ y : M, NormedSpace ℝ (TangentSpace I y) := fun _ =>
    PoincareCurvature.instNormedSpaceTangentSpace I _
  letI fTM : ∀ y : M, FiniteDimensional ℝ (TangentSpace I y) := fun _ =>
    inferInstanceAs (FiniteDimensional ℝ E)
  let U : ∀ y : M, TangentSpace I y :=
    smoothExtend (I := I) (F := E) (V := TangentSpace I) x u
  let V : ∀ y : M, TangentSpace I y :=
    smoothExtend (I := I) (F := E) (V := TangentSpace I) x v
  let A : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y := fun y =>
    LinearMap.toContinuousLinearMap
      (ricciEndomorphism (cov := cov) y (U y) (V y))
  let hContOne : ContMDiffVectorBundle 1 E TM I :=
    @ContMDiffVectorBundle.of_le
      ℝ M E TM _ E _ _ H _ I _ _ _ _ _ _ _ _
      TangentSpace.fiberBundle TangentSpace.vectorBundle
      1 2 one_le_two hContTangent
  let d := @inducedHomCovariantDerivative
    E _ _ H _ I M _ _ _ _ _ _
    E E _ _ _ _ _
    (TangentSpace I : M → Type _) (TangentSpace I : M → Type _)
      _ _ nTM sTM fTM nTM sTM
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    hContTangent hContOne cov cov
  let L : TangentSpace I x →ₗ[ℝ] TangentSpace I x :=
    (d A x p).toLinearMap
  change LinearMap.trace ℝ (TangentSpace I x) L =
    ∑ i, b.repr (L (b i)) i
  rw [LinearMap.trace_eq_matrix_trace ℝ b]
  apply Finset.sum_congr rfl
  intro i hi
  change LinearMap.toMatrix b b _ i i = _
  rw [LinearMap.toMatrix_apply]

/- Differentiating the Ricci trace gives the internal trace above. -/
theorem ricciCurvature_mvfderiv_eq_curvatureEndomorphismTraceCovariantDerivative
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (x : M) (hRicci : raisedRicciEndomorphismMDiffAt cov x)
    (p u v : TangentSpace I x) :
    mvfderiv (I := I) (fun y => ricciCurvature (cov := cov) y
      (smoothExtend (I := I) (F := E) (V := TangentSpace I) x u y)
      (smoothExtend (I := I) (F := E) (V := TangentSpace I) x v y)) x p =
      curvatureEndomorphismTraceCovariantDerivative cov x p u v := by
  classical
  let U : ∀ y : M, TangentSpace I y :=
    smoothExtend (I := I) (F := E) (V := TangentSpace I) x u
  let V : ∀ y : M, TangentSpace I y :=
    smoothExtend (I := I) (F := E) (V := TangentSpace I) x v
  letI nTM : ∀ y : M, NormedAddCommGroup (TangentSpace I y) := fun y =>
    PoincareCurvature.instNormedAddCommGroupTangentSpace I y
  letI sTM : ∀ y : M, NormedSpace ℝ (TangentSpace I y) := fun _ =>
    PoincareCurvature.instNormedSpaceTangentSpace I _
  letI fTM : ∀ y : M, FiniteDimensional ℝ (TangentSpace I y) := fun _ =>
    inferInstanceAs (FiniteDimensional ℝ E)
  let A : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y := fun y =>
    LinearMap.toContinuousLinearMap (ricciEndomorphism (cov := cov) y (U y) (V y))
  let hContOne : ContMDiffVectorBundle 1 E TM I :=
    @ContMDiffVectorBundle.of_le
      ℝ M E TM _ E _ _ H _ I _ _ _ _ _ _ _ _
      TangentSpace.fiberBundle TangentSpace.vectorBundle
      1 2 one_le_two hContTangent
  let d := @inducedHomCovariantDerivative
    E _ _ H _ I M _ _ _ _ _ _
    E E _ _ _ _ _
    (TangentSpace I : M → Type _) (TangentSpace I : M → Type _)
      _ _ nTM sTM fTM nTM sTM
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    TangentSpace.fiberBundle TangentSpace.vectorBundle
    hContTangent hContOne cov cov
  let trA : M → ℝ := @endomorphismTrace
    E _ _ M _ _ (TangentSpace I : M → Type _) nTM sTM _
    TangentSpace.fiberBundle TangentSpace.vectorBundle A
  have hA : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun q : M => TangentSpace I q →L[ℝ] TangentSpace I q) y (A y)) x := by
    simpa [A, U, V] using
      (curvatureEndomorphism_mdifferentiableAt
        (I := I) (E := E) (M := M) cov x u v)
  have heq : (fun y => ricciCurvature (cov := cov) y (U y) (V y)) = trA := by
    funext y
    rfl
  change mvfderiv (I := I) (fun y => ricciCurvature (cov := cov) y
    (U y) (V y)) x p = _
  rw [heq]
  change _ = LinearMap.trace ℝ (TangentSpace I x) ((d A x p).toLinearMap)
  exact @mvfderiv_endomorphismTrace_eq_trace_inducedHom
    E E _ _ _ _ H _ I M _ _ _ _ _ _ _ _
    (TangentSpace I : M → Type _) nTM sTM _
      TangentSpace.fiberBundle TangentSpace.vectorBundle
    hContTangent _ fTM cov A x hA p

/- The genuine Ricci derivative is the curvature trace after the two moving
arguments are removed. -/
theorem covariantTwoTensorCovariantDerivative_ricci_eq_curvatureTrace
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (x : M) (hRicci : raisedRicciEndomorphismMDiffAt cov x)
    (p u v : TangentSpace I x) :
    covariantTwoTensorCovariantDerivative cov
        (ricciCovariantTwoTensor cov) x p u v =
      ∑ i : Fin (Module.finrank ℝ (TangentSpace I x)),
        curvatureCovariantDerivativeInner cov x p
          ((stdOrthonormalBasis ℝ (TangentSpace I x)) i) u v
          ((stdOrthonormalBasis ℝ (TangentSpace I x)) i) := by
  classical
  let b : OrthonormalBasis (Fin (Module.finrank ℝ (TangentSpace I x))) ℝ
      (TangentSpace I x) := stdOrthonormalBasis ℝ (TangentSpace I x)
  let bb := b.toBasis
  have hRicciTwo :=
    ricciCovariantTwoTensorMDiffAt_of_raisedRicciEndomorphismMDiffAt
      (I := I) (E := E) (M := M) cov x hRicci
  have htwo := covariantTwoTensorCovariantDerivative_apply_of_mdifferentiableAt
    (I := I) (E := E) (M := M) cov hRicciTwo p u v
  let U : ∀ y : M, TangentSpace I y :=
    smoothExtend (I := I) (F := E) (V := TangentSpace I) x u
  let V : ∀ y : M, TangentSpace I y :=
    smoothExtend (I := I) (F := E) (V := TangentSpace I) x v
  have hf := ricciCurvature_mvfderiv_eq_curvatureEndomorphismTraceCovariantDerivative
    (I := I) (E := E) (M := M) cov x hRicci p u v
  have hsum := curvatureEndomorphismTraceCovariantDerivative_eq_sum_basis
    (I := I) (E := E) (M := M) cov x p u v bb
  have htwo' :
      covariantTwoTensorCovariantDerivative cov
          (ricciCovariantTwoTensor cov) x p u v =
        mvfderiv (I := I) (fun y => ricciCurvature (cov := cov) y
          (U y) (V y)) x p -
          ricciCurvature (cov := cov) x (cov U x p) v -
          ricciCurvature (cov := cov) x u (cov V x p) := by
    simpa only [ricciCovariantTwoTensor_apply, U, V] using htwo
  rw [htwo']
  rw [hf]
  rw [hsum]
  have hprod : ∀ i,
      curvatureEndomorphismCovariantDerivativeApply cov x p u v (bb i) =
        curvatureCovariantDerivative cov x p (bb i) u v +
          curvatureTensor (cov := cov) x (bb i) (cov U x p) v +
          curvatureTensor (cov := cov) x (bb i) u (cov V x p) := by
    intro i
    simpa [U, V] using curvatureEndomorphismCovariantDerivativeApply_eq
      (I := I) (E := E) (M := M) cov x p u v (bb i)
  simp_rw [hprod]
  have hrepr : ∀ (i : Fin (Module.finrank ℝ (TangentSpace I x)))
      (w : TangentSpace I x), bb.repr w i = inner ℝ (b i) w := by
    intro i w
    simpa [bb] using (b.repr_apply_apply w i)
  have hcoord :
      (∑ i, bb.repr
        (curvatureCovariantDerivative cov x p (bb i) u v +
          curvatureTensor (cov := cov) x (bb i) (cov U x p) v +
          curvatureTensor (cov := cov) x (bb i) u (cov V x p)) i) =
        ∑ i, inner ℝ (b i)
          (curvatureCovariantDerivative cov x p (bb i) u v +
            curvatureTensor (cov := cov) x (bb i) (cov U x p) v +
            curvatureTensor (cov := cov) x (bb i) u (cov V x p)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hrepr i _
  rw [hcoord]
  simp only [inner_add_right]
  have hbb : ∀ i : Fin (Module.finrank ℝ (TangentSpace I x)), bb i = b i := by
    intro i
    rfl
  simp_rw [hbb]
  simp_rw [Finset.sum_add_distrib]
  rw [← ricciCurvature_eq_sum_curvature_orthonormalBasis
      (I := I) (E := E) (M := M) cov x b (cov U x p) v]
  rw [← ricciCurvature_eq_sum_curvature_orthonormalBasis
      (I := I) (E := E) (M := M) cov x b u (cov V x p)]
  simp only [curvatureCovariantDerivativeInner]
  ring_nf
  apply Finset.sum_congr rfl
  intro i hi
  exact real_inner_comm _ _

end CovariantDerivative
