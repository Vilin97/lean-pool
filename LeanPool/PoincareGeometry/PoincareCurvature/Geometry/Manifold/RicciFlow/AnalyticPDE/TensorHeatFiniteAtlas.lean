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

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatFiniteIntervalReconstruction
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatCoefficientLocalization
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatFrozenUniqueness

/-!
# A finite radius-adapted tensor-heat atlas

This module freezes all choices made by the local tensor-heat construction:
the radius at every possible center, the localized coefficient data and its
zero-trace inverse, and the finite smooth partition selected by compactness.

For a nonempty closed manifold, the finitely many selected radii have a
strictly positive minimum.  Parabolic scaling therefore gives one strictly
positive physical time interval common to every reconstructed local field.
The final construction in this file is the genuine finite tensor sum on that
common interval; it is not merely a family of unrelated coordinate solutions.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology

namespace RicciFlow
namespace AnalyticPDE

open CovariantDerivative
open PoincareCurvature.Bundle.Trivialization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]

variable {d : ℕ} {t₀ T α : ℝ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "W₂" => (Fin d × Fin d → ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

-- Select the same nested operator norms as the geometric coefficient
-- regularity layer.  Stating them explicitly prevents the three-tensor
-- instance search from cycling while the atlas hypotheses are elaborated.
@[reducible] local instance finiteAtlasTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateTwoModelNormedAddCommGroup
@[reducible] local instance finiteAtlasTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateTwoModelNormedSpace
@[reducible] local instance finiteAtlasTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedAddCommGroup x
@[reducible] local instance finiteAtlasTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) :=
  CovariantDerivative.coordinateTwoFiberNormedSpace x
@[reducible] local instance finiteAtlasThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedAddCommGroup
@[reducible] local instance finiteAtlasThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedSpace
@[reducible] local instance finiteAtlasThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedAddCommGroup x
@[reducible] local instance finiteAtlasThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedSpace x
@[reducible] local instance finiteAtlasWFirstNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance finiteAtlasWFirstNormedSpace :
    NormedSpace ℝ (E →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance finiteAtlasWSecondNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance finiteAtlasWSecondNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance finiteAtlasWPrincipalNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] E →L[ℝ] W₂) →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance finiteAtlasWPrincipalNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] E →L[ℝ] W₂) →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance finiteAtlasWFirstCoeffNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] W₂) →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance finiteAtlasWFirstCoeffNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] W₂) →L[ℝ] W₂) :=
  ContinuousLinearMap.toNormedSpace

/-- All local analytic and finite-cover choices used by the closed-manifold
tensor-heat parametrix.  The identities stored here are exact operator
identities for the actual connection-Laplacian chart coefficients. -/
structure FiniteTensorHeatParametrixAtlas
    (cov : CovariantDerivative I E TM)
    (b : Module.Basis (Fin d) ℝ E) (t₀ T α : ℝ) where
  time_lt : t₀ < T
  alpha_pos : 0 < α
  alpha_lt_one : α < 1
  radius : M → ℝ
  coefficients : M → TensorHeatLocalizedCoefficientData E W₂
  localInverse : M →
    ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      FiniteParabolicC2AlphaBanach E W₂ t₀ T α
  radius_pos : ∀ p, 0 < radius p
  center_eq : ∀ p, (coefficients p).center = (extChartAt I p) p
  fields_agree : ∀ p,
    TensorHeatLocalizedCoefficientData.FieldsAgreeOnUnitBall
      (t₀ := t₀) (T := T) (coefficients p)
      (localTensorHeatPrincipalCoefficient (I := I) p
        (trivializationAt E TM p) b)
      (localTensorHeatFirstCoefficient (I := I) cov p
        (trivializationAt E TM p) b)
      (localTensorHeatZeroCoefficient (I := I) cov p
        (trivializationAt E TM p) b)
      ((extChartAt I p).target ∩
        (extChartAt I p).symm ⁻¹' (trivializationAt E TM p).baseSet)
      ((extChartAt I p) p) alpha_pos alpha_lt_one (radius p)
  right_inverse : ∀ p,
    (FiniteParabolicC2AlphaBanach.coordinateCauchyL
      ((coefficients p).principalField alpha_pos alpha_lt_one
        (radius p))
      ((coefficients p).firstField alpha_pos alpha_lt_one
        (radius p))
      ((coefficients p).zeroField alpha_pos alpha_lt_one
        (radius p))).comp (localInverse p) =
      ContinuousLinearMap.id ℝ
        (ParabolicC0AlphaBanach E W₂ α
          (parabolicFiniteCylinder E t₀ T))
  zero_trace : ∀ p,
    (FiniteParabolicC2AlphaBanach.initialTraceL
      (X := E) (E := W₂) time_lt alpha_pos).comp
        (localInverse p) = 0
  patch_subset_trivialization : ∀ p,
    actualLocalTensorHeatPatch (I := I) p (radius p) ⊆
      (trivializationAt E TM p).baseSet
  cover : FiniteSmoothPointwiseSubordinateCover I
    (fun p => actualLocalTensorHeatPatch (I := I) p (radius p))

namespace FiniteTensorHeatParametrixAtlas

variable [CompactSpace M] [SigmaCompactSpace M] [I.Boundaryless]

/-- A quantitative frozen-error margin retained separately from the base
atlas structure.  It is consumed once when the atlas is shortened in time. -/
def HasFrozenPostErrorMargin
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (c : ℝ) : Prop :=
  ∀ p,
    ‖frozenTensorHeatPerturbationL (I := I) p
      (trivializationAt E TM p) b p (mem_extChartAt_source p)
      A.time_lt A.alpha_pos A.alpha_lt_one
      (FiniteParabolicC2AlphaBanach.coordinateCauchyL
        ((A.coefficients p).principalField A.alpha_pos A.alpha_lt_one (A.radius p))
        ((A.coefficients p).firstField A.alpha_pos A.alpha_lt_one (A.radius p))
        ((A.coefficients p).zeroField A.alpha_pos A.alpha_lt_one (A.radius p)))‖ < c

/-- Compactness and local perturbative solvability produce a finite atlas
with a strict one-third frozen-error reserve for later time restriction. -/
theorem exists_atlas_with_frozen_margin
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (b : Module.Basis (Fin d) ℝ E)
    (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ∃ A : FiniteTensorHeatParametrixAtlas
        (E := E) (I := I) (M := M) (d := d) cov b t₀ T α,
      HasFrozenPostErrorMargin cov A (1 / 3) := by
  classical
  have hall : ∀ p : M,
      ∃ D : TensorHeatLocalizedCoefficientData E W₂,
        D.center = (extChartAt I p) p ∧
        (∀ z ∈ Metric.closedBall (0 : E) 1, D.cutoff z = 1) ∧
        ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ →
          TensorHeatLocalizedCoefficientData.FieldsAgreeOnUnitBall
            (t₀ := t₀) (T := T) D
            (localTensorHeatPrincipalCoefficient (I := I) p
              (trivializationAt E TM p) b)
            (localTensorHeatFirstCoefficient (I := I) cov p
              (trivializationAt E TM p) b)
            (localTensorHeatZeroCoefficient (I := I) cov p
              (trivializationAt E TM p) b)
            ((extChartAt I p).target ∩
              (extChartAt I p).symm ⁻¹' (trivializationAt E TM p).baseSet)
            ((extChartAt I p) p) hα hα1 r ∧
          ∃ Q : ParabolicC0AlphaBanach E W₂ α
                (parabolicFiniteCylinder E t₀ T) →L[ℝ]
              FiniteParabolicC2AlphaBanach E W₂ t₀ T α,
            (FiniteParabolicC2AlphaBanach.coordinateCauchyL
              (D.principalField hα hα1 r) (D.firstField hα hα1 r)
              (D.zeroField hα hα1 r)).comp Q =
                ContinuousLinearMap.id ℝ
                  (ParabolicC0AlphaBanach E W₂ α
                    (parabolicFiniteCylinder E t₀ T)) ∧
            (FiniteParabolicC2AlphaBanach.initialTraceL
              (X := E) (E := W₂) hT hα).comp Q = 0 := fun p =>
    exists_radius_actualLocalTensorHeatUnitBall_zeroTrace
      (I := I) cov p (trivializationAt E TM p)
      (mem_baseSet_trivializationAt E TM p) b hT hα hα1
  choose D hDcenter hDcut δ hδ hrun using hall
  have hmargin : ∀ p : M, ∃ ε > 0, ∀ r : ℝ, |r| < ε →
      (D p).errorMajorant
        (frozenTensorHeatFiniteZeroInitialInverseL
          (I := I) p p (mem_extChartAt_source p) d hT hα hα1) r <
        1 / 3 := fun p =>
    (D p).exists_radius_errorMajorant_lt
      (frozenTensorHeatFiniteZeroInitialInverseL
        (I := I) p p (mem_extChartAt_source p) d hT hα hα1)
      (by norm_num)
  choose ε hε hmarginRun using hmargin
  let radius : M → ℝ := fun p => min (δ p) (ε p) / 2
  have hradius : ∀ p, 0 < radius p := fun p => by
    dsimp [radius]
    exact div_pos (lt_min (hδ p) (hε p)) (by norm_num)
  have hradiusδ : ∀ p, radius p < δ p := fun p => by
    dsimp [radius]
    have hm : 0 < min (δ p) (ε p) := lt_min (hδ p) (hε p)
    calc
      min (δ p) (ε p) / 2 < min (δ p) (ε p) := by linarith
      _ ≤ δ p := min_le_left _ _
  have hradiusε : ∀ p, radius p < ε p := fun p => by
    dsimp [radius]
    have hm : 0 < min (δ p) (ε p) := lt_min (hδ p) (hε p)
    calc
      min (δ p) (ε p) / 2 < min (δ p) (ε p) := by linarith
      _ ≤ ε p := min_le_right _ _
  have hselected := fun p => hrun p (radius p) (hradius p) (hradiusδ p)
  let Q : M → ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      FiniteParabolicC2AlphaBanach E W₂ t₀ T α :=
    fun p => Classical.choose (hselected p).2
  have hQspec := fun p => Classical.choose_spec (hselected p).2
  have hprincipal : ∀ p,
      (D p).principal (D p).center =
        frozenLocalTensorHeatPrincipalCoefficient (I := I) p
          (trivializationAt E TM p) b p := by
    intro p
    let z : ℝ × E := (t₀, 0)
    have hz0 : z.2 ∈ Metric.closedBall (0 : E) 1 := by
      simp [z, Metric.mem_closedBall]
    have hcut0 : (D p).cutoff z.2 = 1 := hDcut p z.2 hz0
    have hformula := (D p).toFun_principalField_of_cutoff_eq_one
      (t₀ := t₀) (T := T) hα hα1 (radius p) z hcut0
    have hactual := ((hselected p).1 z hz0).2.1
    have heq : (D p).principal (D p).center =
        localTensorHeatPrincipalCoefficient (I := I) p
          (trivializationAt E TM p) b ((extChartAt I p) p) := by
      rw [show (D p).center + radius p • z.2 = (D p).center by
        simp [z]] at hformula
      rw [show (extChartAt I p) p + radius p • z.2 =
          (extChartAt I p) p by simp [z]] at hactual
      exact hformula.symm.trans hactual
    simpa [frozenLocalTensorHeatPrincipalCoefficient, hDcenter p] using heq
  have hpatch : ∀ p,
      actualLocalTensorHeatPatch (I := I) p (radius p) ⊆
        (trivializationAt E TM p).baseSet := fun p =>
    actualLocalTensorHeatPatch_subset_of_fieldsAgree
      (I := I) (p := p) (D p) hα hα1 (hradius p) (hselected p).1
  have hcover :=
    FiniteSmoothPointwiseSubordinateCover.exists_of_isOpen_mem
      (I := I)
      (fun p => actualLocalTensorHeatPatch (I := I) p (radius p))
      (fun p => isOpen_actualLocalTensorHeatPatch (I := I) p (radius p))
      (fun p => mem_actualLocalTensorHeatPatch (I := I) p (hradius p))
  refine ⟨
    { time_lt := hT
      alpha_pos := hα
      alpha_lt_one := hα1
      radius := radius
      coefficients := D
      localInverse := Q
      radius_pos := hradius
      center_eq := hDcenter
      fields_agree := fun p => (hselected p).1
      right_inverse := fun p => (hQspec p).1
      zero_trace := fun p => (hQspec p).2
      patch_subset_trivialization := hpatch
      cover := Classical.choice hcover }, ?_⟩
  intro p
  have hfreeze : ParabolicC0AlphaSpace.constL
      (X := E) (α := α) (s := parabolicFiniteCylinder E t₀ T)
      ((D p).principal (D p).center) =
      frozenTensorHeatPrincipalField (I := I) p
        (trivializationAt E TM p) b p t₀ T α := by
    simp [frozenTensorHeatPrincipalField, hprincipal p]
  apply lt_of_le_of_lt
    (norm_frozenTensorHeatPerturbationL_coordinateCauchyL_le
      (I := I) p (trivializationAt E TM p) b
      (mem_extChartAt_source p) hT hα hα1
      ((D p).principalField hα hα1 (radius p))
      ((D p).firstField hα hα1 (radius p))
      ((D p).zeroField hα hα1 (radius p)))
  rw [← hfreeze]
  exact (localizedCoordinatePostErrorBound_le_errorMajorant
    hα hα1 (radius p) (D p) _).trans_lt
      (hmarginRun p (radius p) (by
        rw [abs_of_pos (hradius p)]
        exact hradiusε p))

/-- Compactness and local perturbative solvability produce a frozen finite
parametrix atlas. -/
theorem exists_atlas
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (b : Module.Basis (Fin d) ℝ E)
    (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    Nonempty (FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) (d := d) cov b t₀ T α) := by
  obtain ⟨A, _hmargin⟩ :=
    exists_atlas_with_frozen_margin cov b hT hα hα1
  exact ⟨A⟩

variable {b : Module.Basis (Fin d) ℝ E}

/-- The finite cover index type is nonempty whenever the manifold is. -/
theorem index_nonempty [hM : Nonempty M]
    (cov : CovariantDerivative I E TM)
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) (d := d) cov b t₀ T α) :
    Nonempty A.cover.Index := by
  let p : M := Classical.choice hM
  obtain ⟨i, _hi⟩ :=
    A.cover.partition.exists_pos_of_mem (Set.mem_univ p)
  exact ⟨i⟩

/-- The least of the finitely many radii actually used by the subordinate
cover. -/
def commonRadius [Nonempty M]
    (cov : CovariantDerivative I E TM)
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) (d := d) cov b t₀ T α) : ℝ := by
  letI : Nonempty A.cover.Index := A.index_nonempty
  exact Finset.univ.inf' Finset.univ_nonempty
    (fun i : A.cover.Index => A.radius (i : M))

theorem commonRadius_pos [Nonempty M]
    (cov : CovariantDerivative I E TM)
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) (d := d) cov b t₀ T α) :
    0 < A.commonRadius := by
  unfold commonRadius
  apply Finset.inf'_mem (Set.Ioi (0 : ℝ))
  · intro x hx y hy
    change 0 < min x y
    exact lt_min hx hy
  · intro i _hi
    exact A.radius_pos (i : M)

theorem commonRadius_le [Nonempty M]
    (cov : CovariantDerivative I E TM)
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) (d := d) cov b t₀ T α)
    (i : A.cover.Index) :
    A.commonRadius ≤ A.radius (i : M) := by
  unfold commonRadius
  exact Finset.inf'_le _ (Finset.mem_univ i)

/-- The physical time shared by every radius-rescaled local cylinder. -/
def commonTerminalTime [Nonempty M]
    (cov : CovariantDerivative I E TM)
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) (d := d) cov b t₀ T α) : ℝ :=
  CovariantDerivative.FiniteClassicalTensorHeatField.physicalTerminalTime
    t₀ T A.commonRadius

theorem lt_commonTerminalTime [Nonempty M]
    (cov : CovariantDerivative I E TM)
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) (d := d) cov b t₀ T α) :
    t₀ < A.commonTerminalTime :=
  CovariantDerivative.FiniteClassicalTensorHeatField.lt_physicalTerminalTime
    A.time_lt (ne_of_gt A.commonRadius_pos)

theorem commonTerminalTime_le [Nonempty M]
    (cov : CovariantDerivative I E TM)
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) (d := d) cov b t₀ T α)
    (i : A.cover.Index) :
    A.commonTerminalTime ≤
      CovariantDerivative.FiniteClassicalTensorHeatField.physicalTerminalTime
        t₀ T (A.radius (i : M)) := by
  have hc0 : 0 ≤ A.commonRadius := A.commonRadius_pos.le
  have hci := A.commonRadius_le cov i
  have hsq : A.commonRadius ^ 2 ≤ A.radius (i : M) ^ 2 :=
    (sq_le_sq₀ hc0 (A.radius_pos (i : M)).le).2 hci
  unfold commonTerminalTime
    CovariantDerivative.FiniteClassicalTensorHeatField.physicalTerminalTime
  simpa [add_comm] using add_le_add_left
    (mul_le_mul_of_nonneg_right hsq (sub_nonneg.mpr A.time_lt.le)) t₀

/-- Pair-indexed tensor coordinates use the convention `(second, first)`,
because `localTwoTensorComponent ... (q,p)` evaluates a tensor on frame
vectors `(p,q)`.  This equivalence performs exactly that swap while passing
to the curried matrices consumed by geometric reconstruction. -/
def tensorCoordinateReconstructionLinearEquiv (d : ℕ) :
    (Fin d × Fin d → ℝ) ≃ₗ[ℝ] (Fin d → Fin d → ℝ) where
  toFun q i j := q (j, i)
  invFun u ij := u ij.2 ij.1
  left_inv q := by
    funext ij
    rcases ij with ⟨i, j⟩
    rfl
  right_inv u := by
    funext i j
    rfl
  map_add' q r := by
    funext i j
    rfl
  map_smul' c q := by
    funext i j
    rfl

/-- Continuous form of the coordinate-to-reconstruction index equivalence. -/
def tensorCoordinateReconstructionEquiv (d : ℕ) :
    (Fin d × Fin d → ℝ) ≃L[ℝ] (Fin d → Fin d → ℝ) :=
  (tensorCoordinateReconstructionLinearEquiv d).toContinuousLinearEquiv

@[simp] theorem tensorCoordinateReconstructionEquiv_apply
    (d : ℕ) (q : Fin d × Fin d → ℝ) (i j : Fin d) :
    tensorCoordinateReconstructionEquiv d q i j = q (j, i) :=
  rfl

@[simp] theorem tensorCoordinateReconstructionEquiv_symm_apply
    (d : ℕ) (u : Fin d → Fin d → ℝ) (ij : Fin d × Fin d) :
    (tensorCoordinateReconstructionEquiv d).symm u ij = u ij.2 ij.1 :=
  rfl

/-- Curry the pair-indexed output of one selected local inverse into the
matrix convention used by geometric tensor reconstruction, including the
index swap forced by the intrinsic component convention. -/
def normalizedLocalSolution
    (cov : CovariantDerivative I E TM)
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) (d := d) cov b t₀ T α)
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T)) :
    FiniteParabolicC2AlphaBanach E (Fin d → Fin d → ℝ) t₀ T α :=
  FiniteParabolicC2AlphaBanach.fiberPostcompL
    (tensorCoordinateReconstructionEquiv d).toContinuousLinearMap
    (A.localInverse (i : M) q)

/-- Reconstruct one local inverse output as a genuine tensor field, rescale
it to physical time, and restrict it to the common finite horizon. -/
def localField [Nonempty M]
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) (d := d) cov b t₀ T α)
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T)) :
    CovariantDerivative.FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ A.commonTerminalTime :=
  CovariantDerivative.FiniteClassicalTensorHeatField.restrictTerminal cov
    (physicalFiniteClassicalTensorHeatField
      (I := I) cov (i : M) (A.radius (i : M))
      (ne_of_gt (A.radius_pos (i : M))) b (A.cover.partition i)
      ((A.cover.partition i).contMDiff.of_le
        (show (2 : WithTop ℕ∞) ≤ ∞ by decide))
      (A.cover.pieces_subset_domain i)
      (A.patch_subset_trivialization (i : M))
      (A.normalizedLocalSolution cov i q) A.alpha_pos)
    A.commonTerminalTime (A.commonTerminalTime_le cov i)

/-- The uncorrected finite local-to-global tensor parametrix on its common
physical interval. -/
def parametrixField [Nonempty M]
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) (d := d) cov b t₀ T α)
    (q : A.cover.Index →
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ T)) :
    CovariantDerivative.FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ A.commonTerminalTime :=
  CovariantDerivative.FiniteClassicalTensorHeatField.finsetSum cov
    Finset.univ (fun i => A.localField cov i (q i))

@[simp] theorem parametrixField_toFun [Nonempty M]
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) (d := d) cov b t₀ T α)
    (q : A.cover.Index →
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ T))
    (t : ℝ) (x : M) :
    (A.parametrixField cov q).toFun t x =
      ∑ i : A.cover.Index, (A.localField cov i (q i)).toFun t x :=
  rfl

end FiniteTensorHeatParametrixAtlas
end AnalyticPDE
end RicciFlow
