/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Ambient.ScalarMatrix
public import LeanPool.CoarseGraining.Homogenization.PDE.DirichletRHS
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.AxisCube
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.AxisCubeHarmonicCovariance
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2Realization

/-! # H10Adjoint -/

@[expose] public section

namespace Homogenization

open MeasureTheory

noncomputable section

namespace CubeCalderonZygmund

/-!
# Zero-trace scalar divergence solutions on cubes

This file packages the existing Riesz/Dirichlet construction as a canonical
zero-trace solution of a scalar constant-coefficient divergence equation.  Its
weak equation has the negative-divergence sign used by finite-`q` comparisons.
-/

private abbrev scalarCoeffField {d : ℕ} (sigma0 : ℝ) : CoeffField d :=
  fun _ => scalarMatrix (d := d) sigma0

private theorem isEllipticFieldOn_scalarCoeffField {d : ℕ}
    {U : Set (Vec d)} {sigma0 : ℝ} (hU : MeasurableSet U)
    (hsigma0 : 0 < sigma0) :
    IsEllipticFieldOn sigma0 sigma0 U (scalarCoeffField sigma0) := by
  classical
  constructor
  · apply measurable_pi_iff.2
    intro i
    apply measurable_pi_iff.2
    intro j
    have hpiece :
        Measurable
          (U.piecewise
            (fun _ : Vec d => scalarMatrix (d := d) sigma0 i j)
            (fun _ => 0)) :=
      measurable_const.piecewise hU measurable_const
    simpa [Set.piecewise, scalarCoeffField] using! hpiece
  · intro x hx
    simpa [scalarCoeffField] using
      (isEllipticMatrix_scalarMatrix (d := d) hsigma0)

private theorem nonempty_axisCube_of_pos {d : ℕ} (z : Vec d) {L : ℝ}
    (hL : 0 < L) :
    Set.Nonempty (axisCube z L) := by
  refine ⟨fun i => z i + L / 2, ?_⟩
  simp only [axisCube, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ioo]
  intro i
  constructor <;> linarith

/-- A zero-trace solution of the scalar constant-coefficient divergence
equation on an open axis cube, with its sharp Hilbert-vector energy estimate.
-/
theorem exists_axisCubeScalarDivergenceSolution
    {d : ℕ} [NeZero d] (z : Vec d) {L sigma0 : ℝ}
    (hL : 0 < L) (hsigma0 : 0 < sigma0)
    (G : Vec d → Vec d) (hG : MemVectorL2 (axisCube z L) G) :
    ∃ v : H10Function (axisCube z L),
      (∀ ψ : H10Function (axisCube z L),
        sigma0 *
            ∫ x in axisCube z L,
              vecDot (v.toH1Function.grad x) (ψ.toH1Function.grad x)
                ∂MeasureTheory.volume =
          -∫ x in axisCube z L,
            vecDot (G x) (ψ.toH1Function.grad x) ∂MeasureTheory.volume) ∧
      ‖v.toH1Function.gradToHilbertVectorL2‖ ≤
        sigma0⁻¹ * ‖toHilbertVectorL2OfVecField hG‖ := by
  let U : Set (Vec d) := axisCube z L
  let g : Vec d → Vec d := fun x => -G x
  have hUgeom : IsOpenBoundedConvexDomain U := by
    simpa [U] using isOpenBoundedConvexDomain_axisCube z L
  let : IsFiniteMeasure (volumeMeasureOn U) :=
    hUgeom.isFiniteMeasure_restrict_volume
  have hg : MemVectorL2 U g := by
    simpa [U, g] using! hG.neg
  have hRealize :
      PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization U :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      hUgeom
  have hne : Set.Nonempty U := by
    simpa [U] using nonempty_axisCube_of_pos z hL
  have hEll :
      IsEllipticFieldOn sigma0 sigma0 U (scalarCoeffField sigma0) :=
    isEllipticFieldOn_scalarCoeffField hUgeom.isOpen.measurableSet hsigma0
  obtain ⟨v, hv⟩ :=
    exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := scalarCoeffField sigma0) (U := U) (g := g)
      (lam := sigma0) (Lam := sigma0) hg hRealize hne hEll
  have hv_divergence :
      ∀ ψ : H10Function U,
        sigma0 *
            ∫ x in U,
              vecDot (v.toH1Function.grad x) (ψ.toH1Function.grad x)
                ∂MeasureTheory.volume =
          -∫ x in U,
            vecDot (G x) (ψ.toH1Function.grad x) ∂MeasureTheory.volume := by
    intro ψ
    have hsolver := hv ψ
    rw [show
      (fun x =>
        vecDot (matVecMul ((scalarCoeffField sigma0) x)
          (v.toH1Function.grad x)) (ψ.toH1Function.grad x)) =
        fun x => sigma0 *
          vecDot (v.toH1Function.grad x) (ψ.toH1Function.grad x) by
            funext x
            simp [scalarCoeffField, matVecMul_scalarMatrix, vecDot_smul_left],
      MeasureTheory.integral_const_mul] at hsolver
    calc
      sigma0 *
          ∫ x in U,
            vecDot (v.toH1Function.grad x) (ψ.toH1Function.grad x)
              ∂MeasureTheory.volume =
          ∫ x in U, vecDot (g x) (ψ.toH1Function.grad x)
              ∂MeasureTheory.volume := hsolver
      _ =
          -∫ x in U, vecDot (G x) (ψ.toH1Function.grad x)
              ∂MeasureTheory.volume := by
        rw [show
          (fun x => vecDot (g x) (ψ.toH1Function.grad x)) =
            fun x => -vecDot (G x) (ψ.toH1Function.grad x) by
              funext x
              simp [g, vecDot_neg_left],
          MeasureTheory.integral_neg]
  have hGU : MemVectorL2 U G := by
    simpa [U] using hG
  have hv_energy :
      ‖v.toH1Function.gradToHilbertVectorL2‖ ≤
        sigma0⁻¹ * ‖toHilbertVectorL2OfVecField hGU‖ := by
    let V : HilbertVectorL2 U := v.toH1Function.gradToHilbertVectorL2
    let H : HilbertVectorL2 U := toHilbertVectorL2OfVecField hGU
    have hgrad_integral :
        ∫ x in U,
            vecDot (v.toH1Function.grad x) (v.toH1Function.grad x)
              ∂MeasureTheory.volume =
          ‖V‖ ^ 2 := by
      calc
        ∫ x in U,
            vecDot (v.toH1Function.grad x) (v.toH1Function.grad x)
              ∂MeasureTheory.volume =
            inner ℝ V V := by
              simpa [V, H1Function.gradToHilbertVectorL2] using
                (inner_toHilbertVectorL2OfVecField_eq_integral
                  (U := U) v.toH1Function.grad_memVectorL2
                  v.toH1Function.grad_memVectorL2).symm
        _ = ‖V‖ ^ 2 := real_inner_self_eq_norm_sq V
    have hpair_integral :
        ∫ x in U, vecDot (G x) (v.toH1Function.grad x)
            ∂MeasureTheory.volume =
          inner ℝ H V := by
      simpa [H, V, H1Function.gradToHilbertVectorL2] using
        (inner_toHilbertVectorL2OfVecField_eq_integral
          (U := U) hGU v.toH1Function.grad_memVectorL2).symm
    have henergy := hv_divergence v
    rw [hgrad_integral, hpair_integral] at henergy
    have henergy_le : sigma0 * ‖V‖ ^ 2 ≤ ‖H‖ * ‖V‖ := by
      calc
        sigma0 * ‖V‖ ^ 2 = -inner ℝ H V := henergy
        _ ≤ |inner ℝ H V| := neg_le_abs _
        _ ≤ ‖H‖ * ‖V‖ := abs_real_inner_le_norm H V
    by_cases hVzero : ‖V‖ = 0
    · rw [hVzero]
      exact mul_nonneg (inv_nonneg.mpr hsigma0.le) (norm_nonneg H)
    · have hVpos : 0 < ‖V‖ :=
        lt_of_le_of_ne (norm_nonneg V) (Ne.symm hVzero)
      have hsigmaV : sigma0 * ‖V‖ ≤ ‖H‖ := by
        apply le_of_mul_le_mul_right _ hVpos
        simpa [pow_two, mul_assoc] using henergy_le
      have hdiv : ‖V‖ ≤ ‖H‖ / sigma0 := by
        apply (le_div_iff₀ hsigma0).2
        simpa [mul_comm] using hsigmaV
      simpa [V, H, div_eq_mul_inv, mul_comm] using hdiv
  refine ⟨v, ?_, ?_⟩
  · simpa [U] using hv_divergence
  · simpa [U] using hv_energy

/-- The canonical zero-trace solution of the scalar constant-coefficient
divergence equation on an open axis cube. -/
noncomputable def axisCubeScalarDivergenceSolution
    {d : ℕ} [NeZero d] (z : Vec d) {L sigma0 : ℝ}
    (hL : 0 < L) (hsigma0 : 0 < sigma0)
    (G : Vec d → Vec d) (hG : MemVectorL2 (axisCube z L) G) :
    H10Function (axisCube z L) :=
  Classical.choose (exists_axisCubeScalarDivergenceSolution z hL hsigma0 G hG)

/-- The canonical axis-cube solution satisfies the scalar divergence equation
against every zero-trace Sobolev test function. -/
theorem axisCubeScalarDivergenceSolution_weak
    {d : ℕ} [NeZero d] (z : Vec d) {L sigma0 : ℝ}
    (hL : 0 < L) (hsigma0 : 0 < sigma0)
    (G : Vec d → Vec d) (hG : MemVectorL2 (axisCube z L) G)
    (ψ : H10Function (axisCube z L)) :
    sigma0 *
        ∫ x in axisCube z L,
          vecDot ((axisCubeScalarDivergenceSolution z hL hsigma0 G hG).toH1Function.grad x)
            (ψ.toH1Function.grad x) ∂MeasureTheory.volume =
      -∫ x in axisCube z L,
          vecDot (G x) (ψ.toH1Function.grad x) ∂MeasureTheory.volume := by
  exact (Classical.choose_spec
    (exists_axisCubeScalarDivergenceSolution z hL hsigma0 G hG)).1 ψ

/-- The canonical axis-cube solution has the sharp Hilbert-vector energy
bound. -/
theorem norm_axisCubeScalarDivergenceSolution_gradToHilbertVectorL2_le
    {d : ℕ} [NeZero d] (z : Vec d) {L sigma0 : ℝ}
    (hL : 0 < L) (hsigma0 : 0 < sigma0)
    (G : Vec d → Vec d) (hG : MemVectorL2 (axisCube z L) G) :
    ‖(axisCubeScalarDivergenceSolution z hL hsigma0 G hG).toH1Function.gradToHilbertVectorL2‖ ≤
      sigma0⁻¹ * ‖toHilbertVectorL2OfVecField hG‖ := by
  exact (Classical.choose_spec
    (exists_axisCubeScalarDivergenceSolution z hL hsigma0 G hG)).2

private theorem cubeScaleFactor_pos {d : ℕ} (Q : TriadicCube d) :
    0 < cubeScaleFactor Q := by
  simpa [cubeScaleFactor] using
    (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)

/-- Existence form on the open realization of a triadic cube.  In particular
this supplies the centered origin-cube interface used by the source-facing CZ
estimates. -/
theorem exists_openCubeSetScalarDivergenceSolution
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0)
    (G : Vec d → Vec d) (hG : MemVectorL2 (openCubeSet Q) G) :
    ∃ v : H10Function (openCubeSet Q),
      (∀ ψ : H10Function (openCubeSet Q),
        sigma0 *
            ∫ x in openCubeSet Q,
              vecDot (v.toH1Function.grad x) (ψ.toH1Function.grad x)
                ∂MeasureTheory.volume =
          -∫ x in openCubeSet Q,
            vecDot (G x) (ψ.toH1Function.grad x) ∂MeasureTheory.volume) ∧
      ‖v.toH1Function.gradToHilbertVectorL2‖ ≤
        sigma0⁻¹ * ‖toHilbertVectorL2OfVecField hG‖ := by
  let e : openCubeSet Q =
      axisCube (triadicCubeAxisCorner Q) (cubeScaleFactor Q) :=
    openCubeSet_eq_axisCube_triadicCube Q
  have hAxis :
      ∀ hG : MemVectorL2
          (axisCube (triadicCubeAxisCorner Q) (cubeScaleFactor Q)) G,
        ∃ v : H10Function
            (axisCube (triadicCubeAxisCorner Q) (cubeScaleFactor Q)),
          (∀ ψ : H10Function
              (axisCube (triadicCubeAxisCorner Q) (cubeScaleFactor Q)),
            sigma0 *
                ∫ x in axisCube (triadicCubeAxisCorner Q) (cubeScaleFactor Q),
                  vecDot (v.toH1Function.grad x) (ψ.toH1Function.grad x)
                    ∂MeasureTheory.volume =
              -∫ x in axisCube (triadicCubeAxisCorner Q) (cubeScaleFactor Q),
                vecDot (G x) (ψ.toH1Function.grad x)
                  ∂MeasureTheory.volume) ∧
          ‖v.toH1Function.gradToHilbertVectorL2‖ ≤
            sigma0⁻¹ * ‖toHilbertVectorL2OfVecField hG‖ := by
    intro hG
    exact exists_axisCubeScalarDivergenceSolution (triadicCubeAxisCorner Q)
      (cubeScaleFactor_pos Q) hsigma0 G hG
  have hOpen :
      ∀ hG : MemVectorL2 (openCubeSet Q) G,
        ∃ v : H10Function (openCubeSet Q),
          (∀ ψ : H10Function (openCubeSet Q),
            sigma0 *
                ∫ x in openCubeSet Q,
                  vecDot (v.toH1Function.grad x) (ψ.toH1Function.grad x)
                    ∂MeasureTheory.volume =
              -∫ x in openCubeSet Q,
                vecDot (G x) (ψ.toH1Function.grad x)
                  ∂MeasureTheory.volume) ∧
          ‖v.toH1Function.gradToHilbertVectorL2‖ ≤
            sigma0⁻¹ * ‖toHilbertVectorL2OfVecField hG‖ := by
    exact e.symm ▸ hAxis
  exact hOpen hG

/-- The canonical scalar divergence solution on an open triadic cube. -/
noncomputable def openCubeSetScalarDivergenceSolution
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0)
    (G : Vec d → Vec d) (hG : MemVectorL2 (openCubeSet Q) G) :
    H10Function (openCubeSet Q) :=
  Classical.choose (exists_openCubeSetScalarDivergenceSolution Q hsigma0 G hG)

/-- The canonical open-triadic-cube solution satisfies the scalar divergence
equation against every zero-trace Sobolev test function. -/
theorem openCubeSetScalarDivergenceSolution_weak
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0)
    (G : Vec d → Vec d) (hG : MemVectorL2 (openCubeSet Q) G)
    (ψ : H10Function (openCubeSet Q)) :
    sigma0 *
        ∫ x in openCubeSet Q,
          vecDot ((openCubeSetScalarDivergenceSolution Q hsigma0 G hG).toH1Function.grad x)
            (ψ.toH1Function.grad x) ∂MeasureTheory.volume =
      -∫ x in openCubeSet Q,
          vecDot (G x) (ψ.toH1Function.grad x) ∂MeasureTheory.volume := by
  exact (Classical.choose_spec
    (exists_openCubeSetScalarDivergenceSolution Q hsigma0 G hG)).1 ψ

/-- The canonical open-triadic-cube solution has the sharp Hilbert-vector
energy bound. -/
theorem norm_openCubeSetScalarDivergenceSolution_gradToHilbertVectorL2_le
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0)
    (G : Vec d → Vec d) (hG : MemVectorL2 (openCubeSet Q) G) :
    ‖(openCubeSetScalarDivergenceSolution Q hsigma0 G hG).toH1Function.gradToHilbertVectorL2‖ ≤
      sigma0⁻¹ * ‖toHilbertVectorL2OfVecField hG‖ := by
  exact (Classical.choose_spec
    (exists_openCubeSetScalarDivergenceSolution Q hsigma0 G hG)).2

end CubeCalderonZygmund

end

end Homogenization
