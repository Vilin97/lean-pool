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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasRestriction
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatFrozenUniqueness

/-!
# Local uniqueness on shortened tensor-heat atlas cylinders

The atlas is chosen with a strict one-third frozen post-error margin.  On a
shorter terminal interval we reuse the genuine frozen inverse by the same
extension--solution--restriction construction as the local atlas inverse.
The short post-error is the long post-error sandwiched between restriction
and extension, hence still has norm strictly below one.  Genuine Euclidean
heat uniqueness therefore propagates to every local operator of the
restricted atlas.
-/

@[expose] public section

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology

namespace RicciFlow
namespace AnalyticPDE
namespace FiniteTensorHeatParametrixAtlas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [CompactSpace M] [SigmaCompactSpace M] [I.Boundaryless]

variable {d : ℕ} {t₀ S T α : ℝ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "W₂" => (Fin d × Fin d → ℝ)

@[reducible] local instance localUniqueFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance localUniqueFirstDerivativeNormedSpace :
    NormedSpace ℝ (E →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance localUniqueHessianNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance localUniqueHessianNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance localUniquePrincipalNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] E →L[ℝ] W₂) →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance localUniquePrincipalNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] E →L[ℝ] W₂) →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance localUniqueFirstNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] W₂) →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance localUniqueFirstNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] W₂) →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedSpace

/-- A time-independent frozen principal coefficient restricts to the same
coefficient on the shorter cylinder. -/
theorem restrictL_frozenTensorHeatPrincipalField
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) (x : M)
    (hST : S ≤ T) :
    ParabolicC0AlphaSpace.restrictL
        (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST)
        (frozenTensorHeatPrincipalField (I := I) p e b x t₀ T α) =
      frozenTensorHeatPrincipalField (I := I) p e b x t₀ S α := by
  apply Subtype.ext
  rfl

/-- The long-cylinder genuine frozen inverse, reused on a shorter cylinder. -/
def shortFrozenTensorHeatInverse
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source)
    (d : ℕ) (hS : t₀ < S) (hST : S ≤ T)
    (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
        (parabolicFiniteCylinder E t₀ S) →L[ℝ]
      FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ S α :=
  (FiniteParabolicC2AlphaBanach.restrictTerminalL hST).comp
    ((frozenTensorHeatFiniteZeroInitialInverseL
      (I := I) p x hxChart d hT hα hα1).comp
      (ParabolicC0AlphaBanach.extendTerminalL hS hST hα))

/-- The frozen Cauchy operator commutes with terminal restriction. -/
theorem frozenTensorHeatCauchyL_restrictTerminal
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) (x : M)
    (hST : S ≤ T)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α) :
    frozenTensorHeatCauchyL (I := I) p e b x t₀ S α
        (FiniteParabolicC2AlphaBanach.restrictTerminal hST u) =
      ParabolicC0AlphaBanach.restrictL
        (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST)
        (frozenTensorHeatCauchyL (I := I) p e b x t₀ T α u) := by
  let hsub := parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST
  have hcoord := FiniteParabolicC2AlphaBanach.coordinateCauchyL_restrictTerminal
    hST (frozenTensorHeatPrincipalField (I := I) p e b x t₀ T α)
      (0 : FiniteParabolicC2AlphaBanach.FirstCoefficientSpace
        (X := E) (E := W₂) (t₀ := t₀) (T := T) (α := α))
      (0 : FiniteParabolicC2AlphaBanach.ZeroCoefficientSpace
        (X := E) (E := W₂) (t₀ := t₀) (T := T) (α := α)) u
  have hfirst : ParabolicC0AlphaSpace.restrictL hsub
      (0 : FiniteParabolicC2AlphaBanach.FirstCoefficientSpace
        (X := E) (E := W₂) (t₀ := t₀) (T := T) (α := α)) = 0 :=
    map_zero _
  have hzero : ParabolicC0AlphaSpace.restrictL hsub
      (0 : FiniteParabolicC2AlphaBanach.ZeroCoefficientSpace
        (X := E) (E := W₂) (t₀ := t₀) (T := T) (α := α)) = 0 :=
    map_zero _
  rw [restrictL_frozenTensorHeatPrincipalField
      (I := I) p e b x hST, hfirst, hzero,
    coordinateCauchyL_frozen_eq (I := I) p e b x t₀ S α,
    coordinateCauchyL_frozen_eq (I := I) p e b x t₀ T α] at hcoord
  exact hcoord

/-- The reused frozen inverse is an exact short-cylinder right inverse. -/
theorem frozenTensorHeatCauchyL_comp_shortFrozenTensorHeatInverse
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    (hS : t₀ < S) (hST : S ≤ T)
    (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    (frozenTensorHeatCauchyL (I := I) p e b x t₀ S α).comp
        (shortFrozenTensorHeatInverse
          (I := I) p x hxChart d hS hST hT hα hα1) =
      ContinuousLinearMap.id ℝ
        (ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀ S)) := by
  ext q
  let qlong := ParabolicC0AlphaBanach.extendTerminalL hS hST hα q
  let Qlong := frozenTensorHeatFiniteZeroInitialInverseL
    (I := I) p x hxChart d hT hα hα1
  have hright := congrArg (fun L => L qlong)
    (frozenTensorHeatCauchyL_comp_finiteZeroInitialInverseL
      (I := I) p e b hxFrame hxChart hT hα hα1)
  change frozenTensorHeatCauchyL (I := I) p e b x t₀ S α
      (FiniteParabolicC2AlphaBanach.restrictTerminal hST
        (Qlong qlong)) = q
  rw [frozenTensorHeatCauchyL_restrictTerminal
    (I := I) p e b x hST (Qlong qlong)]
  rw [show frozenTensorHeatCauchyL (I := I) p e b x t₀ T α
      (Qlong qlong) = qlong by simpa [Qlong] using hright]
  exact ParabolicC0AlphaBanach.restrict_extendTerminalL hS hST hα q

/-- The reused frozen inverse has zero initial trace. -/
theorem initialTraceL_shortFrozenTensorHeatInverse
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source)
    (d : ℕ) (hS : t₀ < S) (hST : S ≤ T)
    (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    (FiniteParabolicC2AlphaBanach.initialTraceL
      (X := E) (E := Fin d × Fin d → ℝ) hS hα).comp
        (shortFrozenTensorHeatInverse
          (I := I) p x hxChart d hS hST hT hα hα1) = 0 := by
  apply ContinuousLinearMap.ext
  intro q
  let qlong := ParabolicC0AlphaBanach.extendTerminalL hS hST hα q
  change FiniteParabolicC2AlphaBanach.initialTraceL hS hα
      (FiniteParabolicC2AlphaBanach.restrictTerminal hST
        (frozenTensorHeatFiniteZeroInitialInverseL
          (I := I) p x hxChart d hT hα hα1 qlong)) = 0
  rw [FiniteParabolicC2AlphaBanach.initialTraceL_restrictTerminal]
  exact initialTraceL_frozenTensorHeatFiniteZeroInitialInverseL
    (I := I) p x hxChart d hT hα hα1 qlong

/-- The atlas local coordinate Cauchy operator commutes with terminal
restriction. -/
theorem shortLocalCauchyL_restrictTerminal
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (p : M) (hST : S ≤ T)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α) :
    shortLocalCauchyL cov A p hST
        (FiniteParabolicC2AlphaBanach.restrictTerminal hST u) =
      ParabolicC0AlphaBanach.restrictL
        (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST)
        (atlasLocalCauchyL cov A p u) := by
  exact FiniteParabolicC2AlphaBanach.coordinateCauchyL_restrictTerminal
    hST _ _ _ u

/-- Exact factorization of the shortened post-frozen error through the
parent post-error. -/
theorem short_postFrozenError_factorization
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (p : M) (hS : t₀ < S) (hST : S ≤ T) :
    ((shortLocalCauchyL cov A p hST -
        frozenTensorHeatCauchyL (I := I) p
          (trivializationAt E TM p) b p t₀ S α).comp
      (shortFrozenTensorHeatInverse (I := I) p p
        (mem_extChartAt_source p) d hS hST A.time_lt
        A.alpha_pos A.alpha_lt_one)) =
      (ParabolicC0AlphaBanach.restrictL
        (E := W₂)
        (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST)).comp
        ((frozenTensorHeatPerturbationL (I := I) p
          (trivializationAt E TM p) b p (mem_extChartAt_source p)
          A.time_lt A.alpha_pos A.alpha_lt_one
          (atlasLocalCauchyL cov A p)).comp
          (ParabolicC0AlphaBanach.extendTerminalL
            (E := W₂) hS hST A.alpha_pos)) := by
  apply ContinuousLinearMap.ext
  intro q
  let qlong := ParabolicC0AlphaBanach.extendTerminalL
    (X := E) (E := W₂) hS hST A.alpha_pos q
  let Qlong := frozenTensorHeatFiniteZeroInitialInverseL
    (I := I) p p (mem_extChartAt_source p) d A.time_lt
      A.alpha_pos A.alpha_lt_one
  let u := Qlong qlong
  change shortLocalCauchyL cov A p hST
        (FiniteParabolicC2AlphaBanach.restrictTerminal hST u) -
      frozenTensorHeatCauchyL (I := I) p
        (trivializationAt E TM p) b p t₀ S α
        (FiniteParabolicC2AlphaBanach.restrictTerminal hST u) =
    ParabolicC0AlphaBanach.restrictL
      (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST)
      ((atlasLocalCauchyL cov A p -
        frozenTensorHeatCauchyL (I := I) p
          (trivializationAt E TM p) b p t₀ T α) u)
  rw [shortLocalCauchyL_restrictTerminal cov A p hST u,
    frozenTensorHeatCauchyL_restrictTerminal
      (I := I) p (trivializationAt E TM p) b p hST u]
  rw [sub_apply]
  exact (map_sub _ _ _).symm

/-- The reserved one-third parent margin survives the factor-three terminal
extension cost and yields a strict short-cylinder contraction. -/
theorem norm_short_postFrozenError_lt_one
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (hmargin : HasFrozenPostErrorMargin cov A (1 / 3))
    (p : M) (hS : t₀ < S) (hST : S ≤ T) :
    ‖(shortLocalCauchyL cov A p hST -
        frozenTensorHeatCauchyL (I := I) p
          (trivializationAt E TM p) b p t₀ S α).comp
      (shortFrozenTensorHeatInverse (I := I) p p
        (mem_extChartAt_source p) d hS hST A.time_lt
        A.alpha_pos A.alpha_lt_one)‖ < 1 := by
  rw [short_postFrozenError_factorization cov A p hS hST]
  let R := frozenTensorHeatPerturbationL (I := I) p
    (trivializationAt E TM p) b p (mem_extChartAt_source p)
    A.time_lt A.alpha_pos A.alpha_lt_one (atlasLocalCauchyL cov A p)
  let restrictL := ParabolicC0AlphaBanach.restrictL
    (E := W₂) (α := α)
      (parabolicFiniteCylinder_mono (X := E) (t₀ := t₀) hST)
  let extendL := ParabolicC0AlphaBanach.extendTerminalL
    (X := E) (E := W₂) hS hST A.alpha_pos
  change ‖restrictL.comp (R.comp extendL)‖ < 1
  have hcomp : ‖restrictL.comp (R.comp extendL)‖ ≤
      ‖restrictL‖ * (‖R‖ * ‖extendL‖) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
  have hrestrict : ‖restrictL‖ ≤ 1 :=
    ParabolicC0AlphaBanach.norm_restrictL_le _
  have hextend : ‖extendL‖ ≤ 3 :=
    ParabolicC0AlphaBanach.norm_extendTerminalL_le hS hST A.alpha_pos
  have hR : ‖R‖ < 1 / 3 := by
    simpa [R, atlasLocalCauchyL] using hmargin p
  have hnonnegR : 0 ≤ ‖R‖ := norm_nonneg _
  have hnonnegRestrict : 0 ≤ ‖restrictL‖ := norm_nonneg _
  have hnonnegExtend : 0 ≤ ‖extendL‖ := norm_nonneg _
  calc
    ‖restrictL.comp (R.comp extendL)‖
        ≤ ‖restrictL‖ * (‖R‖ * ‖extendL‖) := hcomp
    _ ≤ 1 * (‖R‖ * 3) := by gcongr
    _ < 1 := by
      norm_num at hR ⊢
      linarith

/-- Every zero-trace homogeneous solution of a shortened atlas local
coordinate operator vanishes. -/
theorem eq_zero_of_shortLocalCauchy_eq_zero_of_initialTrace_eq_zero
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (hmargin : HasFrozenPostErrorMargin cov A (1 / 3))
    (p : M) (hS : t₀ < S) (hST : S ≤ T)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ S α)
    (hu : shortLocalCauchyL cov A p hST u = 0)
    (hu0 : FiniteParabolicC2AlphaBanach.initialTraceL hS A.alpha_pos u = 0) :
    u = 0 := by
  apply eq_zero_of_postFrozenError_norm_lt_one
    (I := I) p (trivializationAt E TM p) b
      (mem_baseSet_trivializationAt E TM p) (mem_extChartAt_source p)
      hS A.alpha_pos
      (shortLocalCauchyL cov A p hST)
      (shortFrozenTensorHeatInverse (I := I) p p
        (mem_extChartAt_source p) d hS hST A.time_lt
        A.alpha_pos A.alpha_lt_one)
  · exact frozenTensorHeatCauchyL_comp_shortFrozenTensorHeatInverse
      (I := I) p (trivializationAt E TM p) b
        (mem_baseSet_trivializationAt E TM p) (mem_extChartAt_source p)
        hS hST A.time_lt A.alpha_pos A.alpha_lt_one
  · exact initialTraceL_shortFrozenTensorHeatInverse
      (I := I) p p (mem_extChartAt_source p) d hS hST A.time_lt
        A.alpha_pos A.alpha_lt_one
  · exact norm_short_postFrozenError_lt_one cov A hmargin p hS hST
  · exact hu
  · exact hu0

/-- The shortened local operator is exactly the local operator stored in the
restricted atlas. -/
theorem shortLocalCauchyL_eq_restrictTerminalAtlas_coordinateCauchyL
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (p : M) (hS : t₀ < S) (hST : S ≤ T) :
    shortLocalCauchyL cov A p hST =
      FiniteParabolicC2AlphaBanach.coordinateCauchyL
        (((A.restrictTerminalAtlas cov hS hST).coefficients p).principalField
          (A.restrictTerminalAtlas cov hS hST).alpha_pos
          (A.restrictTerminalAtlas cov hS hST).alpha_lt_one
          ((A.restrictTerminalAtlas cov hS hST).radius p))
        (((A.restrictTerminalAtlas cov hS hST).coefficients p).firstField
          (A.restrictTerminalAtlas cov hS hST).alpha_pos
          (A.restrictTerminalAtlas cov hS hST).alpha_lt_one
          ((A.restrictTerminalAtlas cov hS hST).radius p))
        (((A.restrictTerminalAtlas cov hS hST).coefficients p).zeroField
          (A.restrictTerminalAtlas cov hS hST).alpha_pos
          (A.restrictTerminalAtlas cov hS hST).alpha_lt_one
          ((A.restrictTerminalAtlas cov hS hST).radius p)) := by
  unfold shortLocalCauchyL
  rw [restrictL_principalField (S := S) (T := T)
      (A.coefficients p) A.alpha_pos A.alpha_lt_one (A.radius p) hST,
    restrictL_firstField (S := S) (T := T)
      (A.coefficients p) A.alpha_pos A.alpha_lt_one (A.radius p) hST,
    restrictL_zeroField (S := S) (T := T)
      (A.coefficients p) A.alpha_pos A.alpha_lt_one (A.radius p) hST]
  rfl

/-- Local uniqueness in the exact coefficient notation of the restricted
atlas. -/
theorem eq_zero_of_restrictTerminalAtlas_coordinateCauchy_eq_zero_of_initialTrace_eq_zero
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (hmargin : HasFrozenPostErrorMargin cov A (1 / 3))
    (p : M) (hS : t₀ < S) (hST : S ≤ T)
    (u : FiniteParabolicC2AlphaBanach E W₂ t₀ S α)
    (hu : FiniteParabolicC2AlphaBanach.coordinateCauchyL
        (((A.restrictTerminalAtlas cov hS hST).coefficients p).principalField
          (A.restrictTerminalAtlas cov hS hST).alpha_pos
          (A.restrictTerminalAtlas cov hS hST).alpha_lt_one
          ((A.restrictTerminalAtlas cov hS hST).radius p))
        (((A.restrictTerminalAtlas cov hS hST).coefficients p).firstField
          (A.restrictTerminalAtlas cov hS hST).alpha_pos
          (A.restrictTerminalAtlas cov hS hST).alpha_lt_one
          ((A.restrictTerminalAtlas cov hS hST).radius p))
        (((A.restrictTerminalAtlas cov hS hST).coefficients p).zeroField
          (A.restrictTerminalAtlas cov hS hST).alpha_pos
          (A.restrictTerminalAtlas cov hS hST).alpha_lt_one
          ((A.restrictTerminalAtlas cov hS hST).radius p)) u = 0)
    (hu0 : FiniteParabolicC2AlphaBanach.initialTraceL hS A.alpha_pos u = 0) :
    u = 0 := by
  apply eq_zero_of_shortLocalCauchy_eq_zero_of_initialTrace_eq_zero
    cov A hmargin p hS hST u
  · rw [shortLocalCauchyL_eq_restrictTerminalAtlas_coordinateCauchyL
      cov A p hS hST]
    exact hu
  · exact hu0

/-- Every local coordinate Cauchy operator of an atlas is injective on the
zero-initial-trace subspace. -/
def HasLocalZeroTraceUniqueness
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α) : Prop :=
  ∀ p (u : FiniteParabolicC2AlphaBanach E W₂ t₀ T α),
    FiniteParabolicC2AlphaBanach.coordinateCauchyL
        ((A.coefficients p).principalField A.alpha_pos A.alpha_lt_one (A.radius p))
        ((A.coefficients p).firstField A.alpha_pos A.alpha_lt_one (A.radius p))
        ((A.coefficients p).zeroField A.alpha_pos A.alpha_lt_one (A.radius p)) u = 0 →
    FiniteParabolicC2AlphaBanach.initialTraceL A.time_lt A.alpha_pos u = 0 →
    u = 0

/-- The one-third parent margin supplies local zero-trace uniqueness for the
entire restricted atlas. -/
theorem hasLocalZeroTraceUniqueness_restrictTerminalAtlas
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (hmargin : HasFrozenPostErrorMargin cov A (1 / 3))
    (hS : t₀ < S) (hST : S ≤ T) :
    HasLocalZeroTraceUniqueness cov
      (A.restrictTerminalAtlas cov hS hST) := by
  intro p u hu hu0
  exact eq_zero_of_restrictTerminalAtlas_coordinateCauchy_eq_zero_of_initialTrace_eq_zero
    cov A hmargin p hS hST u hu hu0

end FiniteTensorHeatParametrixAtlas
end AnalyticPDE
end RicciFlow
