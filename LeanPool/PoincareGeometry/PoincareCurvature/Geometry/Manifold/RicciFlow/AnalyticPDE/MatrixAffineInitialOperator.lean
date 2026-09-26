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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.MatrixZeroInitialOperator
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The Euclidean matrix heat problem with fixed nonzero initial data

This file complements the bounded linear zero-initial Duhamel operator with
the homogeneous heat evolution of a prescribed matrix of bounded
`C^{2,α}` data.  Their sum is the affine solution operator.  The construction
retains a strong closed-time trace in the spatial `C_b` norm, the classical
coefficientwise heat equation, symmetry, and an explicit Schauder bound.
-/

@[expose] public noncomputable section
open Real Set MeasureTheory Metric Filter
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

section FixedInitialMatrixHeat

variable {n d : ℕ}

namespace EuclideanBoundedC2Data

/-- The genuine full Frechet derivative assembled from the stored coordinate
first derivatives. -/
def valueGradient (D : EuclideanBoundedC2Data n) (x : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  coordinateLinearFunctional (fun k => D.first k x)

theorem continuous_valueGradient (D : EuclideanBoundedC2Data n) :
    Continuous D.valueGradient := by
  classical
  unfold valueGradient coordinateLinearFunctional
  apply continuous_finsetSum
  intro k _
  exact D.first k |>.continuous.smul continuous_const

/-- The stored coordinate derivatives assemble to the actual full Frechet
derivative of the initial value. -/
theorem hasFDerivAt_value (D : EuclideanBoundedC2Data n)
    (x : Fin n → ℝ) :
    HasFDerivAt D.value (D.valueGradient x) x := by
  classical
  refine hasFDerivAt_of_continuous_coordinate_derivatives
    D.value D.valueGradient D.continuous_valueGradient ?_ x
  intro y k
  rw [valueGradient, coordinateLinearFunctional_single]
  exact (D.hasDeriv_value k y).hasFDerivAt

/-- A uniform operator-norm bound for the assembled initial gradient. -/
theorem norm_valueGradient_le (D : EuclideanBoundedC2Data n)
    (x : Fin n → ℝ) :
    ‖D.valueGradient x‖ ≤ ∑ k : Fin n, ‖D.first k‖ := by
  refine (norm_coordinateLinearFunctional_le _).trans ?_
  apply Finset.sum_le_sum
  intro k _
  simpa only [Real.norm_eq_abs] using (D.first k).norm_coe_le_norm x

/-- The bounded first derivatives already present in `EuclideanBoundedC2Data`
imply the Lipschitz estimate needed for a strong `C_b` initial trace. -/
theorem value_lipschitz_bound (D : EuclideanBoundedC2Data n)
    (x y : Fin n → ℝ) :
    |D.value x - D.value y| ≤
      (∑ k : Fin n, ‖D.first k‖) * ‖x - y‖ := by
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℝ) (s := (Set.univ : Set (Fin n → ℝ)))
    (f := fun z => D.value z) (C := ∑ k : Fin n, ‖D.first k‖)
    (x := y) (y := x)
    (fun z _ => (D.hasFDerivAt_value z).differentiableAt)
    (fun z _ => by
      rw [(D.hasFDerivAt_value z).fderiv]
      exact D.norm_valueGradient_le z)
    convex_univ (Set.mem_univ _) (Set.mem_univ _)
  simpa only [Real.norm_eq_abs] using h

theorem firstNormSum_nonneg (D : EuclideanBoundedC2Data n) :
    0 ≤ ∑ k : Fin n, ‖D.first k‖ :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

end EuclideanBoundedC2Data

/-- A fixed matrix-valued `C^{2,α}` initial datum, with the Hölder modulus of
its actual Hessian recorded uniformly over all coefficients. -/
structure MatrixC2AlphaInitialData (n d : ℕ) (α : ℝ) where
  initial : Matrix (Fin d) (Fin d) (EuclideanBoundedC2Data n)
  hessianHolderConstant : ℝ
  hessianHolderConstant_nonneg : 0 ≤ hessianHolderConstant
  hessianHolder : ∀ i j a b x y,
    |(initial i j).second a b x - (initial i j).second a b y| ≤
      hessianHolderConstant * ∑ ell : Fin n, |(x - y) ell| ^ α

namespace MatrixC2AlphaInitialData

variable {α : ℝ}

/-- The homogeneous finite-cylinder data associated to a fixed initial
matrix. -/
def homogeneousFiniteData
    {t₀ T : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : MatrixC2AlphaInitialData n d α) :
    MatrixHeatFiniteData n d t₀ T α where
  hT := hT.le
  hr0 := hα
  hr1 := hα1
  initial := D.initial
  initialHessianHolderConstant := D.hessianHolderConstant
  initialHessianHolderConstant_nonneg := D.hessianHolderConstant_nonneg
  initialHessianHolder := D.hessianHolder
  source := 0
  source_continuous := by
    intro i j
    exact continuous_const
  sourceBound := 0
  sourceSpatialHolderConstant := 0
  sourceParabolicHolderConstant := 0
  sourceBound_nonneg := le_rfl
  sourceSpatialHolderConstant_nonneg := le_rfl
  sourceParabolicHolderConstant_nonneg := le_rfl
  source_bounded := by simp
  source_spatialHolder := by simp
  source_parabolicHolder := by
    intro i j
    exact ParabolicHolderWith.const 0 le_rfl

/-- The homogeneous heat evolution of the prescribed initial matrix as one
finite-cylinder `C^{2+α,1+α/2}` Banach element. -/
def homogeneousSolution
    {t₀ T : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : MatrixC2AlphaInitialData n d α) :
    FiniteParabolicC2AlphaBanach (Fin n → ℝ)
      (Fin d → Fin d → ℝ) t₀ T α :=
  (D.homogeneousFiniteData hT hα hα1).solution

theorem norm_homogeneousSolution_le
    {t₀ T : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : MatrixC2AlphaInitialData n d α) :
    ‖D.homogeneousSolution hT hα hα1‖ ≤
      (D.homogeneousFiniteData hT hα hα1).schauderRadius :=
  (D.homogeneousFiniteData hT hα hα1).norm_solution_le

/-- The homogeneous solution satisfies `∂ₜu - Δu = 0` at positive time. -/
theorem homogeneousSolution_heatEquation
    {t₀ T : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : MatrixC2AlphaInitialData n d α)
    {t : ℝ} (ht : t ∈ Set.Ioc t₀ T) (x : Fin n → ℝ) :
    FiniteParabolicC2AlphaBanach.timeDeriv
        (D.homogeneousSolution hT hα hα1) (t, x) =
      ∑ k : Fin n, FiniteParabolicC2AlphaBanach.spaceSecondDeriv
        (D.homogeneousSolution hT hα hα1) (t, x)
          (Pi.single k 1) (Pi.single k 1) := by
  change FiniteParabolicC2AlphaBanach.timeDeriv
      (D.homogeneousFiniteData hT hα hα1).solution (t, x) =
    ∑ k : Fin n, FiniteParabolicC2AlphaBanach.spaceSecondDeriv
      (D.homogeneousFiniteData hT hα hα1).solution (t, x)
        (Pi.single k 1) (Pi.single k 1)
  rw [(D.homogeneousFiniteData hT hα hα1).solution_heatEquation ht x]
  ext i j
  simp [homogeneousFiniteData]

/-- One initial coefficient evolved homogeneously on the closed time
interval.  Its continuity at the left endpoint is in the spatial `C_b` norm. -/
def homogeneousCoefficientValuePathIcc
    {t₀ T : ℝ} (_hT : t₀ < T) (A : EuclideanBoundedC2Data n) :
    BoundedContinuousFunction (↥(Set.Icc t₀ T))
      (BoundedContinuousFunction (Fin n → ℝ) ℝ) :=
  heatMildValuePathBcfIcc t₀ T A.value A.firstNormSum_nonneg
    A.value_lipschitz_bound
    (q := fun _ : ℝ => (0 : BoundedContinuousFunction (Fin n → ℝ) ℝ))
    continuous_const (C := 0) (by simp)

@[simp] theorem homogeneousCoefficientValuePathIcc_initial
    {t₀ T : ℝ} (hT : t₀ < T) (A : EuclideanBoundedC2Data n) :
    homogeneousCoefficientValuePathIcc hT A
      ⟨t₀, le_rfl, hT.le⟩ = A.value := by
  exact heatMildValuePathBcf_initial t₀ A.value continuous_const (by simp)

/-- The prescribed initial matrix as one bounded continuous matrix-valued
function of space. -/
def valueBcf (D : MatrixC2AlphaInitialData n d α) :
    BoundedContinuousFunction (Fin n → ℝ) (Fin d → Fin d → ℝ) :=
  ∑ i : Fin d, ∑ j : Fin d,
    (matrixSingleCLM d i j).compLeftContinuousBounded (Fin n → ℝ)
      (D.initial i j).value

@[simp] theorem valueBcf_apply (D : MatrixC2AlphaInitialData n d α)
    (x : Fin n → ℝ) :
    D.valueBcf x = fun i j => (D.initial i j).value x := by
  classical
  calc
    D.valueBcf x = ∑ i : Fin d, ∑ j : Fin d,
        matrixSingleCLM d i j ((D.initial i j).value x) := by
      simp [valueBcf]
    _ = _ := sum_matrixSingleCLM (fun i j => (D.initial i j).value x)

/-- The homogeneous matrix trajectory on the closed time interval, as a
bounded continuous path in the uniform spatial norm. -/
def homogeneousValuePathIcc
    {t₀ T : ℝ} (hT : t₀ < T) (D : MatrixC2AlphaInitialData n d α) :
    BoundedContinuousFunction (↥(Set.Icc t₀ T))
      (BoundedContinuousFunction (Fin n → ℝ) (Fin d → Fin d → ℝ)) :=
  ∑ i : Fin d, ∑ j : Fin d,
    ((matrixSingleCLM d i j).compLeftContinuousBounded (Fin n → ℝ)).compLeftContinuousBounded
      (↥(Set.Icc t₀ T))
      (homogeneousCoefficientValuePathIcc hT (D.initial i j))

@[simp] theorem homogeneousValuePathIcc_initial
    {t₀ T : ℝ} (hT : t₀ < T) (D : MatrixC2AlphaInitialData n d α) :
    D.homogeneousValuePathIcc hT ⟨t₀, le_rfl, hT.le⟩ = D.valueBcf := by
  classical
  ext x
  simp [homogeneousValuePathIcc,
    homogeneousCoefficientValuePathIcc_initial hT, valueBcf]

/-- At positive times, the closed homogeneous trajectory is exactly the value
component of the packaged higher-parabolic solution. -/
theorem homogeneousValuePathIcc_eq_solution
    {t₀ T : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : MatrixC2AlphaInitialData n d α)
    (t : ↥(Set.Ioc t₀ T)) (x : Fin n → ℝ) :
    D.homogeneousValuePathIcc hT
        ⟨(t : ℝ), ⟨(Set.mem_Ioc.mp t.2).1.le,
          (Set.mem_Ioc.mp t.2).2⟩⟩ x =
      FiniteParabolicC2AlphaBanach.value
        (D.homogeneousSolution hT hα hα1) (t, x) := by
  classical
  have hz : ((t : ℝ), x) ∈
      parabolicFiniteCylinder (Fin n → ℝ) t₀ T := by
    simp [parabolicFiniteCylinder, t.2]
  change D.homogeneousValuePathIcc hT
      ⟨(t : ℝ), ⟨(Set.mem_Ioc.mp t.2).1.le,
        (Set.mem_Ioc.mp t.2).2⟩⟩ x =
    FiniteParabolicC2AlphaBanach.value
      (D.homogeneousFiniteData hT hα hα1).solution (t, x)
  rw [(D.homogeneousFiniteData hT hα hα1).solution_value hz]
  ext i j
  calc
    D.homogeneousValuePathIcc hT
          ⟨(t : ℝ), ⟨(Set.mem_Ioc.mp t.2).1.le,
            (Set.mem_Ioc.mp t.2).2⟩⟩ x i j =
        (∑ a : Fin d, ∑ b : Fin d, matrixSingleCLM d a b
          (homogeneousCoefficientValuePathIcc hT (D.initial a b)
            ⟨(t : ℝ), ⟨(Set.mem_Ioc.mp t.2).1.le,
              (Set.mem_Ioc.mp t.2).2⟩⟩ x)) i j := by
      simp [homogeneousValuePathIcc]
    _ =
        homogeneousCoefficientValuePathIcc hT (D.initial i j)
          ⟨(t : ℝ), ⟨(Set.mem_Ioc.mp t.2).1.le,
            (Set.mem_Ioc.mp t.2).2⟩⟩ x := by
      rw [sum_matrixSingleCLM]
    _ = heatMildSpaceTimeND t₀ (D.initial i j).value
          (fun _ : ℝ => (0 : BoundedContinuousFunction (Fin n → ℝ) ℝ)) (t, x) := by
      rw [homogeneousCoefficientValuePathIcc,
        heatMildValuePathBcfIcc_apply,
        heatMildValuePathBcf_of_lt (Set.mem_Ioc.mp t.2).1,
        heatMildValueNDbcf_apply]
      rfl
    _ = (D.homogeneousFiniteData hT hα hα1).solutionFunction (t, x) i j := by
      rfl

/-- The affine solution with fixed initial datum `D` and variable forcing
`q`. -/
def affineSolution
    {t₀ T : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : MatrixC2AlphaInitialData n d α)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) (Fin d → Fin d → ℝ) α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    FiniteParabolicC2AlphaBanach (Fin n → ℝ)
      (Fin d → Fin d → ℝ) t₀ T α :=
  D.homogeneousSolution hT hα hα1 +
    matrixZeroInitialSolution hT hα hα1 q

@[simp] theorem affineSolution_eq
    {t₀ T : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : MatrixC2AlphaInitialData n d α)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) (Fin d → Fin d → ℝ) α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    D.affineSolution hT hα hα1 q =
      D.homogeneousSolution hT hα hα1 +
        matrixZeroInitialOperator hT hα hα1 q :=
  rfl

/-- The fixed-initial affine solution satisfies the inhomogeneous matrix heat
equation at every positive cylinder time. -/
theorem affineSolution_heatEquation
    {t₀ T : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : MatrixC2AlphaInitialData n d α)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) (Fin d → Fin d → ℝ) α
      (Set.univ : Set (ℝ × (Fin n → ℝ))))
    {t : ℝ} (ht : t ∈ Set.Ioc t₀ T) (x : Fin n → ℝ) :
    FiniteParabolicC2AlphaBanach.timeDeriv
        (D.affineSolution hT hα hα1 q) (t, x) =
      (∑ k : Fin n, FiniteParabolicC2AlphaBanach.spaceSecondDeriv
        (D.affineSolution hT hα hα1 q) (t, x)
          (Pi.single k 1) (Pi.single k 1)) +
        ParabolicC0AlphaBanach.evalCLM (t, x) (Set.mem_univ (t, x)) q := by
  rw [affineSolution, FiniteParabolicC2AlphaBanach.timeDeriv_add,
    D.homogeneousSolution_heatEquation hT hα hα1 ht x,
    matrixZeroInitialSolution_heatEquation hT hα hα1 q ht x]
  simp only [FiniteParabolicC2AlphaBanach.spaceSecondDeriv_add,
    add_apply, Finset.sum_add_distrib]
  abel

/-- The affine solution's closed-time value trajectory in the spatial
uniform norm. -/
def affineValuePathIcc
    {t₀ T : ℝ} (hT : t₀ < T) (hα : 0 < α)
    (D : MatrixC2AlphaInitialData n d α)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) (Fin d → Fin d → ℝ) α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    BoundedContinuousFunction (↥(Set.Icc t₀ T))
      (BoundedContinuousFunction (Fin n → ℝ) (Fin d → Fin d → ℝ)) :=
  D.homogeneousValuePathIcc hT + matrixZeroInitialValuePathIcc hT hα q

@[simp] theorem affineValuePathIcc_initial
    {t₀ T : ℝ} (hT : t₀ < T) (hα : 0 < α)
    (D : MatrixC2AlphaInitialData n d α)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) (Fin d → Fin d → ℝ) α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    D.affineValuePathIcc hT hα q ⟨t₀, le_rfl, hT.le⟩ = D.valueBcf := by
  simp [affineValuePathIcc, D.homogeneousValuePathIcc_initial hT,
    matrixZeroInitialValuePathIcc_initial hT hα]

/-- The closed affine trajectory agrees with the higher-parabolic solution at
every positive time. -/
theorem affineValuePathIcc_eq_solution
    {t₀ T : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : MatrixC2AlphaInitialData n d α)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) (Fin d → Fin d → ℝ) α
      (Set.univ : Set (ℝ × (Fin n → ℝ))))
    (t : ↥(Set.Ioc t₀ T)) (x : Fin n → ℝ) :
    D.affineValuePathIcc hT hα q
        ⟨(t : ℝ), ⟨(Set.mem_Ioc.mp t.2).1.le,
          (Set.mem_Ioc.mp t.2).2⟩⟩ x =
      FiniteParabolicC2AlphaBanach.value
        (D.affineSolution hT hα hα1 q) (t, x) := by
  rw [affineValuePathIcc, BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.add_apply,
    D.homogeneousValuePathIcc_eq_solution hT hα hα1 t x,
    matrixZeroInitialValuePathIcc_eq_solution hT hα hα1 q t x,
    affineSolution, FiniteParabolicC2AlphaBanach.value_add]

/-- Explicit affine Schauder bound: the fixed homogeneous cost plus the
operator norm bound times the source norm. -/
def affineSchauderBound
    {t₀ T : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : MatrixC2AlphaInitialData n d α)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) (Fin d → Fin d → ℝ) α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) : ℝ :=
  (D.homogeneousFiniteData hT hα hα1).schauderRadius +
    matrixZeroInitialSchauderConstant n d t₀ T α * ‖q‖

theorem norm_affineSolution_le
    {t₀ T : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : MatrixC2AlphaInitialData n d α)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) (Fin d → Fin d → ℝ) α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    ‖D.affineSolution hT hα hα1 q‖ ≤
      D.affineSchauderBound hT hα hα1 q := by
  exact (norm_add_le _ _).trans (add_le_add
    (D.norm_homogeneousSolution_le hT hα hα1)
    (norm_matrixZeroInitialSolution_le hT hα hα1 q))

/-- Applying the Euclidean Cauchy operator to the homogeneous evolution gives
zero. -/
theorem euclideanMatrixHeatCauchyL_homogeneousSolution_eq_zero
    {t₀ T : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : MatrixC2AlphaInitialData n d α) :
    euclideanMatrixHeatCauchyL n d t₀ T α
        (D.homogeneousSolution hT hα hα1) = 0 := by
  apply (ParabolicC0AlphaBanach.eq_iff_forall_evalCLM _ _).2
  intro z hz
  rcases z with ⟨t, x⟩
  have ht : t ∈ Set.Ioc t₀ T := by
    simpa [parabolicFiniteCylinder] using hz
  rw [evalCLM_euclideanMatrixHeatCauchyL,
    D.homogeneousSolution_heatEquation hT hα hα1 ht x]
  exact sub_self _

/-- The fixed-initial affine operator is a right inverse for the Euclidean
matrix heat Cauchy operator. -/
theorem euclideanMatrixHeatCauchyL_affineSolution
    {t₀ T : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : MatrixC2AlphaInitialData n d α)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) (Fin d → Fin d → ℝ) α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    euclideanMatrixHeatCauchyL n d t₀ T α
        (D.affineSolution hT hα hα1 q) =
      restrictGlobalMatrixSourceToFiniteL n d t₀ T α q := by
  rw [affineSolution, map_add,
    D.euclideanMatrixHeatCauchyL_homogeneousSolution_eq_zero hT hα hα1,
    zero_add]
  change ((euclideanMatrixHeatCauchyL n d t₀ T α).comp
    (matrixZeroInitialOperator hT hα hα1)) q = _
  rw [euclideanMatrixHeatCauchyL_comp_zeroInitialOperator hT hα hα1]

/-- Difference formula showing that the fixed-initial solution map is affine
with linear part the zero-initial Duhamel operator. -/
theorem affineSolution_sub
    {t₀ T : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : MatrixC2AlphaInitialData n d α)
    (q r : ParabolicC0AlphaBanach (Fin n → ℝ) (Fin d → Fin d → ℝ) α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    D.affineSolution hT hα hα1 q - D.affineSolution hT hα hα1 r =
      matrixZeroInitialOperator hT hα hα1 (q - r) := by
  rw [affineSolution_eq, affineSolution_eq, map_sub]
  abel

/-- Lipschitz dependence of the fixed-initial affine solution on its source. -/
theorem norm_affineSolution_sub_le
    {t₀ T : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : MatrixC2AlphaInitialData n d α)
    (q r : ParabolicC0AlphaBanach (Fin n → ℝ) (Fin d → Fin d → ℝ) α
      (Set.univ : Set (ℝ × (Fin n → ℝ)))) :
    ‖D.affineSolution hT hα hα1 q - D.affineSolution hT hα hα1 r‖ ≤
      matrixZeroInitialSchauderConstant n d t₀ T α * ‖q - r‖ := by
  rw [D.affineSolution_sub hT hα hα1 q r,
    matrixZeroInitialOperator_apply]
  exact norm_matrixZeroInitialSolution_le hT hα hα1 (q - r)

/-- Symmetry condition on the prescribed matrix-valued initial field. -/
def IsSymmetric (D : MatrixC2AlphaInitialData n d α) : Prop :=
  ∀ i j, (D.initial i j).value = (D.initial j i).value

theorem homogeneousSolution_isSymmetric
    {t₀ T : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : MatrixC2AlphaInitialData n d α) (hD : D.IsSymmetric)
    {z : ℝ × (Fin n → ℝ)}
    (hz : z ∈ parabolicFiniteCylinder (Fin n → ℝ) t₀ T) :
    ∀ i j, FiniteParabolicC2AlphaBanach.value
        (D.homogeneousSolution hT hα hα1) z i j =
      FiniteParabolicC2AlphaBanach.value
        (D.homogeneousSolution hT hα hα1) z j i := by
  exact (D.homogeneousFiniteData hT hα hα1).solution_isSymm hD
    (by intro s i j; rfl) hz

theorem affineSolution_isSymmetric
    {t₀ T : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : MatrixC2AlphaInitialData n d α) (hD : D.IsSymmetric)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) (Fin d → Fin d → ℝ) α
      (Set.univ : Set (ℝ × (Fin n → ℝ))))
    (hq : ∀ z i j,
      ParabolicC0AlphaBanach.evalCLM z (Set.mem_univ z) q i j =
        ParabolicC0AlphaBanach.evalCLM z (Set.mem_univ z) q j i)
    {z : ℝ × (Fin n → ℝ)}
    (hz : z ∈ parabolicFiniteCylinder (Fin n → ℝ) t₀ T) :
    ∀ i j, FiniteParabolicC2AlphaBanach.value
        (D.affineSolution hT hα hα1 q) z i j =
      FiniteParabolicC2AlphaBanach.value
        (D.affineSolution hT hα hα1 q) z j i := by
  intro i j
  simp only [affineSolution, FiniteParabolicC2AlphaBanach.value_add,
    Pi.add_apply]
  rw [D.homogeneousSolution_isSymmetric hT hα hα1 hD hz i j,
    matrixZeroInitialSolution_isSymm hT hα hα1 q hq hz i j]

end MatrixC2AlphaInitialData

end FixedInitialMatrixHeat

end AnalyticPDE
end RicciFlow
