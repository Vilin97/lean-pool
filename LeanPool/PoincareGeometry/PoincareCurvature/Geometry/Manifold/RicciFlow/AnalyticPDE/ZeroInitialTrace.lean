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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.MatrixAffineInitialOperator
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteInitialTrace
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.AffineCauchyCorrection

/-!
# Canonical traces of the Euclidean heat solution operators

The explicit closed-time heat trajectories are identified with the canonical
endpoint completion of the finite-cylinder Hölder value component.  Thus the
zero-initial solution operators genuinely land in the kernel of the bounded
initial-trace map, while the homogeneous and affine matrix solutions attain
their prescribed initial data.
-/

@[expose] public noncomputable section
open Real Set Filter
open scoped Topology

namespace RicciFlow
namespace AnalyticPDE

section ScalarTrace

variable {n : ℕ}

/-- The canonical trace of the scalar zero-initial heat solution vanishes. -/
theorem finiteInitialTrace_euclideanZeroInitialSolution_eq_zero
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    ParabolicC0AlphaBanach.finiteInitialTrace hT hα
        (FiniteParabolicC2AlphaBanach.valueComponentL
          (euclideanZeroInitialSolution hT hα hα1 q)) = 0 := by
  rw [ParabolicC0AlphaBanach.finiteInitialTrace_eq_of_continuous
    hT hα _ (euclideanZeroInitialValuePathIcc hT hα q)
    (euclideanZeroInitialValuePathIcc hT hα q).continuous]
  · exact euclideanZeroInitialValuePathIcc_initial hT hα q
  · intro t
    ext x
    let τ : ↥(Set.Ioc t₀ T) := ⟨(t : ℝ), t.2, t.1.2.2⟩
    calc
      euclideanZeroInitialValuePathIcc hT hα q
          (t : ↥(Set.Icc t₀ T)) x =
          FiniteParabolicC2AlphaBanach.value
            (euclideanZeroInitialSolution hT hα hα1 q) (t, x) := by
        simpa [τ] using
          euclideanZeroInitialValuePathIcc_eq_solution hT hα hα1 q τ x
      _ = ParabolicC0AlphaBanach.evalCLM ((t : ℝ), x)
          (ParabolicC0AlphaBanach.positiveTimeInIcc_mem_parabolicFiniteCylinder t x)
          (FiniteParabolicC2AlphaBanach.valueComponentL
            (euclideanZeroInitialSolution hT hα hα1 q)) := by
        rw [FiniteParabolicC2AlphaBanach.evalCLM_valueComponentL]
      _ = ParabolicC0AlphaBanach.finiteTimeSlice hα
          (FiniteParabolicC2AlphaBanach.valueComponentL
            (euclideanZeroInitialSolution hT hα hα1 q)) t x := rfl

@[simp]
theorem initialTraceL_euclideanZeroInitialSolution
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    FiniteParabolicC2AlphaBanach.initialTraceL hT hα
      (euclideanZeroInitialSolution hT hα hα1 q) = 0 := by
  exact finiteInitialTrace_euclideanZeroInitialSolution_eq_zero
    hT hα hα1 q

/-- The scalar zero-initial solution operator lands in the closed zero-trace
subspace. -/
def euclideanZeroInitialOperatorToKernel
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
        (Set.univ : Set (ℝ × (Fin n → ℝ))) →L[ℝ]
      FiniteParabolicC2AlphaBanach.zeroInitialSubmodule
        (X := Fin n → ℝ) (E := ℝ) hT hα :=
  (euclideanZeroInitialOperator (n := n) hT hα hα1).codRestrict
    (FiniteParabolicC2AlphaBanach.zeroInitialSubmodule hT hα)
    (fun q => (FiniteParabolicC2AlphaBanach.mem_zeroInitialSubmodule_iff
      hT hα _).2 (initialTraceL_euclideanZeroInitialSolution hT hα hα1 q))

@[simp]
theorem euclideanZeroInitialOperatorToKernel_apply
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) ℝ α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    (euclideanZeroInitialOperatorToKernel hT hα hα1 q :
      FiniteParabolicC2AlphaBanach (Fin n → ℝ) ℝ t₀ T α) =
        euclideanZeroInitialSolution hT hα hα1 q :=
  rfl

end ScalarTrace

section MatrixTrace

variable {n d : ℕ}

/-- The canonical trace of the matrix zero-initial heat solution vanishes. -/
theorem finiteInitialTrace_matrixZeroInitialSolution_eq_zero
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) (Fin d → Fin d → ℝ) α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    ParabolicC0AlphaBanach.finiteInitialTrace hT hα
        (FiniteParabolicC2AlphaBanach.valueComponentL
          (matrixZeroInitialSolution hT hα hα1 q)) = 0 := by
  rw [ParabolicC0AlphaBanach.finiteInitialTrace_eq_of_continuous
    hT hα _ (matrixZeroInitialValuePathIcc hT hα q)
    (matrixZeroInitialValuePathIcc hT hα q).continuous]
  · exact matrixZeroInitialValuePathIcc_initial hT hα q
  · intro t
    ext x i j
    let τ : ↥(Set.Ioc t₀ T) := ⟨(t : ℝ), t.2, t.1.2.2⟩
    calc
      matrixZeroInitialValuePathIcc hT hα q
          (t : ↥(Set.Icc t₀ T)) x i j =
          FiniteParabolicC2AlphaBanach.value
            (matrixZeroInitialSolution hT hα hα1 q) (t, x) i j := by
        exact congrFun (congrFun
          (matrixZeroInitialValuePathIcc_eq_solution hT hα hα1 q τ x) i) j
      _ = ParabolicC0AlphaBanach.evalCLM ((t : ℝ), x)
          (ParabolicC0AlphaBanach.positiveTimeInIcc_mem_parabolicFiniteCylinder t x)
          (FiniteParabolicC2AlphaBanach.valueComponentL
            (matrixZeroInitialSolution hT hα hα1 q)) i j := by
        rw [FiniteParabolicC2AlphaBanach.evalCLM_valueComponentL]
      _ = ParabolicC0AlphaBanach.finiteTimeSlice hα
          (FiniteParabolicC2AlphaBanach.valueComponentL
            (matrixZeroInitialSolution hT hα hα1 q)) t x i j := rfl

@[simp]
theorem initialTraceL_matrixZeroInitialSolution
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) (Fin d → Fin d → ℝ) α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    FiniteParabolicC2AlphaBanach.initialTraceL hT hα
      (matrixZeroInitialSolution hT hα hα1 q) = 0 := by
  exact finiteInitialTrace_matrixZeroInitialSolution_eq_zero
    hT hα hα1 q

/-- The matrix zero-initial solution operator with codomain restricted to the
closed zero-trace subspace. -/
def matrixZeroInitialOperatorToKernel
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ParabolicC0AlphaBanach (Fin n → ℝ) (Fin d → Fin d → ℝ) α
        (Set.univ : Set (ℝ × (Fin n → ℝ))) →L[ℝ]
      FiniteParabolicC2AlphaBanach.zeroInitialSubmodule
        (X := Fin n → ℝ) (E := Fin d → Fin d → ℝ) hT hα :=
  (matrixZeroInitialOperator (n := n) (d := d) hT hα hα1).codRestrict
    (FiniteParabolicC2AlphaBanach.zeroInitialSubmodule hT hα)
    (fun q => (FiniteParabolicC2AlphaBanach.mem_zeroInitialSubmodule_iff
      hT hα _).2 (initialTraceL_matrixZeroInitialSolution hT hα hα1 q))

@[simp]
theorem matrixZeroInitialOperatorToKernel_apply
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) (Fin d → Fin d → ℝ) α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    (matrixZeroInitialOperatorToKernel (n := n) (d := d) hT hα hα1 q :
      FiniteParabolicC2AlphaBanach (Fin n → ℝ)
        (Fin d → Fin d → ℝ) t₀ T α) =
      matrixZeroInitialSolution hT hα hα1 q :=
  rfl

/-- The canonical initial trace of the homogeneous heat evolution is exactly
the prescribed matrix-valued initial datum. -/
theorem finiteInitialTrace_homogeneousSolution
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : MatrixC2AlphaInitialData n d α) :
    ParabolicC0AlphaBanach.finiteInitialTrace hT hα
        (FiniteParabolicC2AlphaBanach.valueComponentL
          (D.homogeneousSolution hT hα hα1)) = D.valueBcf := by
  rw [ParabolicC0AlphaBanach.finiteInitialTrace_eq_of_continuous
    hT hα _ (D.homogeneousValuePathIcc hT)
    (D.homogeneousValuePathIcc hT).continuous]
  · exact D.homogeneousValuePathIcc_initial hT
  · intro t
    ext x i j
    let τ : ↥(Set.Ioc t₀ T) := ⟨(t : ℝ), t.2, t.1.2.2⟩
    calc
      D.homogeneousValuePathIcc hT (t : ↥(Set.Icc t₀ T)) x i j =
          FiniteParabolicC2AlphaBanach.value
            (D.homogeneousSolution hT hα hα1) (t, x) i j := by
        exact congrFun (congrFun
          (D.homogeneousValuePathIcc_eq_solution hT hα hα1 τ x) i) j
      _ = ParabolicC0AlphaBanach.evalCLM ((t : ℝ), x)
          (ParabolicC0AlphaBanach.positiveTimeInIcc_mem_parabolicFiniteCylinder t x)
          (FiniteParabolicC2AlphaBanach.valueComponentL
            (D.homogeneousSolution hT hα hα1)) i j := by
        rw [FiniteParabolicC2AlphaBanach.evalCLM_valueComponentL]
      _ = ParabolicC0AlphaBanach.finiteTimeSlice hα
          (FiniteParabolicC2AlphaBanach.valueComponentL
            (D.homogeneousSolution hT hα hα1)) t x i j := rfl

@[simp]
theorem initialTraceL_homogeneousSolution
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : MatrixC2AlphaInitialData n d α) :
    FiniteParabolicC2AlphaBanach.initialTraceL hT hα
      (D.homogeneousSolution hT hα hα1) = D.valueBcf :=
  finiteInitialTrace_homogeneousSolution hT hα hα1 D

/-- The canonical initial trace of the affine solution is its prescribed
initial datum, independently of the forcing. -/
@[simp]
theorem initialTraceL_affineSolution
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : MatrixC2AlphaInitialData n d α)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) (Fin d → Fin d → ℝ) α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    FiniteParabolicC2AlphaBanach.initialTraceL hT hα
      (D.affineSolution hT hα hα1 q) = D.valueBcf := by
  rw [MatrixC2AlphaInitialData.affineSolution, map_add,
    initialTraceL_homogeneousSolution hT hα hα1 D,
    initialTraceL_matrixZeroInitialSolution hT hα hα1 q, add_zero]

/-- The Euclidean matrix heat Cauchy operator augmented by canonical initial
trace. -/
def euclideanMatrixHeatCauchyTraceL
    (n d : ℕ) {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) :
    FiniteParabolicC2AlphaBanach (Fin n → ℝ) (Fin d → Fin d → ℝ)
        t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach (Fin n → ℝ) (Fin d → Fin d → ℝ) α
          (parabolicFiniteCylinder (Fin n → ℝ) t₀ T) ×
        BoundedContinuousFunction (Fin n → ℝ) (Fin d → Fin d → ℝ) :=
  (euclideanMatrixHeatCauchyL n d t₀ T α).prod
    (FiniteParabolicC2AlphaBanach.initialTraceL hT hα)

@[simp]
theorem euclideanMatrixHeatCauchyTraceL_apply
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach (Fin n → ℝ)
      (Fin d → Fin d → ℝ) t₀ T α) :
    euclideanMatrixHeatCauchyTraceL n d hT hα u =
      (euclideanMatrixHeatCauchyL n d t₀ T α u,
        FiniteParabolicC2AlphaBanach.initialTraceL hT hα u) :=
  rfl

/-- The explicit affine heat solution realizes both components of the
Euclidean Cauchy problem: its equation is the prescribed forcing restricted
to the finite cylinder, and its initial trace is the prescribed datum. -/
theorem euclideanMatrixHeatCauchyTraceL_affineSolution
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : MatrixC2AlphaInitialData n d α)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) (Fin d → Fin d → ℝ) α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    euclideanMatrixHeatCauchyTraceL n d hT hα
        (D.affineSolution hT hα hα1 q) =
      (restrictGlobalMatrixSourceToFiniteL n d t₀ T α q, D.valueBcf) := by
  rw [euclideanMatrixHeatCauchyTraceL_apply,
    D.euclideanMatrixHeatCauchyL_affineSolution hT hα hα1 q,
    initialTraceL_affineSolution hT hα hα1 D q]

end MatrixTrace

end AnalyticPDE
end RicciFlow
