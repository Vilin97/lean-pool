/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ScalarPoissonHessian
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.CubeVector
public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.CubeVectorH1

/-!
# Paired-witness scalar divergence gradient endpoint

This internal bridge converts synchronized `H¹` and `W^{1,q}` vector
representatives into the `W^{1,q}` gradient endpoint supplied by the scalar
Poisson Hessian estimate.  The `H¹` witness supplies the `L²` divergence and
the integration-by-parts identity; the `W^{1,q}` witness supplies the finite
exponent control.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace CubeCalderonZygmund

private def vectorW1pDivergence {d : ℕ} {Q : TriadicCube d}
    {q : FiniteLpExponent} (G : CubeVectorW1pFunction Q q) : Vec d → ℝ :=
  fun x ↦ ∑ i : Fin d, G.jacobian x i i

private theorem vectorW1pDivergence_memLp
    {d : ℕ} {Q : TriadicCube d} {q : FiniteLpExponent}
    (G : CubeVectorW1pFunction Q q) :
    MemLp (vectorW1pDivergence G) q.exponent (normalizedCubeMeasure Q) := by
  apply MeasureTheory.memLp_finsetSum
  intro i _hi
  have hmatrix := G.jacobianHilbertMemLp
  rw [MeasureTheory.memLp_piLp_iff] at hmatrix
  have hrow := hmatrix i
  rw [MeasureTheory.memLp_piLp_iff] at hrow
  simpa only [vectorW1pDivergence, Function.comp_apply, HilbertMat.ofMat,
    HilbertVec.ofVec, PiLp.toLp_apply] using hrow i

private theorem norm_jacobian_diag_le
    {d : ℕ} {Q : TriadicCube d} {q : FiniteLpExponent}
    (G : CubeVectorW1pFunction Q q) (i : Fin d) (x : Vec d) :
    ‖G.jacobian x i i‖ ≤ ‖HilbertMat.ofMat (G.jacobian x)‖ := by
  calc
    ‖G.jacobian x i i‖ ≤
        ‖(HilbertMat.ofMat (G.jacobian x) : HilbertMat d).ofLp i‖ := by
      simpa only [HilbertMat.ofMat, HilbertVec.ofVec, PiLp.toLp_apply] using
        PiLp.norm_apply_le
          ((HilbertMat.ofMat (G.jacobian x) : HilbertMat d).ofLp i) i
    _ ≤ ‖HilbertMat.ofMat (G.jacobian x)‖ :=
      PiLp.norm_apply_le (HilbertMat.ofMat (G.jacobian x) : HilbertMat d) i

private theorem eLpNorm_vectorW1pDivergence_le_dimension_mul_jacobian
    {d : ℕ} {Q : TriadicCube d} {q : FiniteLpExponent}
    (G : CubeVectorW1pFunction Q q) :
    eLpNorm (vectorW1pDivergence G) q.exponent (normalizedCubeMeasure Q) ≤
      d * eLpNorm (fun x ↦ HilbertMat.ofMat (G.jacobian x)) q.exponent
        (normalizedCubeMeasure Q) := by
  have hdiag : ∀ i : Fin d,
      MemLp (fun x ↦ G.jacobian x i i) q.exponent
        (normalizedCubeMeasure Q) := by
    intro i
    have hmatrix := G.jacobianHilbertMemLp
    rw [MeasureTheory.memLp_piLp_iff] at hmatrix
    have hrow := hmatrix i
    rw [MeasureTheory.memLp_piLp_iff] at hrow
    simpa only [Function.comp_apply, HilbertMat.ofMat, HilbertVec.ofVec,
      PiLp.toLp_apply] using hrow i
  have hdiag_le : ∀ i : Fin d,
      eLpNorm (fun x ↦ G.jacobian x i i) q.exponent
          (normalizedCubeMeasure Q) ≤
        eLpNorm (fun x ↦ HilbertMat.ofMat (G.jacobian x)) q.exponent
          (normalizedCubeMeasure Q) := by
    intro i
    apply MeasureTheory.eLpNorm_mono_ae
    exact Filter.Eventually.of_forall fun x ↦ norm_jacobian_diag_le G i x
  calc
    eLpNorm (vectorW1pDivergence G) q.exponent (normalizedCubeMeasure Q) =
        eLpNorm (∑ i : Fin d, fun x ↦ G.jacobian x i i) q.exponent
          (normalizedCubeMeasure Q) := by
      apply congrArg (fun f : Vec d → ℝ ↦
        eLpNorm f q.exponent (normalizedCubeMeasure Q))
      funext x
      simp only [vectorW1pDivergence, Finset.sum_apply]
    _ ≤ ∑ i : Fin d, eLpNorm (fun x ↦ G.jacobian x i i) q.exponent
          (normalizedCubeMeasure Q) := by
      exact MeasureTheory.eLpNorm_sum_le
        (fun i _hi ↦ (hdiag i).aestronglyMeasurable) q.one_lt.le
    _ ≤ ∑ _i : Fin d, eLpNorm (fun x ↦ HilbertMat.ofMat (G.jacobian x))
          q.exponent (normalizedCubeMeasure Q) :=
      Finset.sum_le_sum fun i _hi ↦ hdiag_le i
    _ = d * eLpNorm (fun x ↦ HilbertMat.ofMat (G.jacobian x)) q.exponent
          (normalizedCubeMeasure Q) := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

/-- Internal paired-witness `W^{1,q}` endpoint for the gradient of a scalar
Dirichlet divergence solution.  The paired `H¹` witness is used only to supply
the `L²` forcing and weak integration by parts required by the scalar Hessian
endpoint. -/
theorem exists_cubeVectorW1p_scalarDivergence_cz_of_paired
    (d : ℕ) [NeZero d] (q : FiniteLpExponent) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ)
      (G2 : CubeVectorH1Function (originCube d m))
      (Gq : CubeVectorW1pFunction (originCube d m) q),
      G2.toField = Gq.toField →
      (∀ (x : Vec d) (i j : Fin d), (G2.coord i).grad x j = Gq.jacobian x i j) →
      ∀ u : H10Function (openCubeSet (originCube d m)),
        CubeDirichletDivergenceProblem (originCube d m) u G2.toField →
        ∃ V : CubeVectorW1pFunction (originCube d m) q,
          V.toField = u.toH1Function.grad ∧
          eLpNorm (fun x ↦ HilbertMat.ofMat (V.jacobian x)) q.exponent
              (normalizedCubeMeasure (originCube d m)) ≤
            C * eLpNorm (fun x ↦ HilbertMat.ofMat (Gq.jacobian x)) q.exponent
              (normalizedCubeMeasure (originCube d m)) := by
  obtain ⟨C0, hC0top, hC0⟩ :=
    exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le d q
  refine ⟨C0 * d, lt_top_iff_ne_top.mpr
    (ENNReal.mul_ne_top hC0top.ne (ENNReal.natCast_ne_top d)), ?_⟩
  intro m G2 Gq hfield hjac u hdiv
  let Q : TriadicCube d := originCube d m
  have hdiv_eq : G2.divergence = vectorW1pDivergence Gq := by
    funext x
    unfold CubeVectorH1Function.divergence vectorW1pDivergence
    apply Finset.sum_congr rfl
    intro i _hi
    exact hjac x i i
  have hdivq : CubeDirichletDivergenceProblem Q u Gq.toField := by
    simpa only [Q, hfield] using hdiv
  have hpoisson : CubeDirichletWeakPoissonProblem Q u G2.divergence := by
    intro phi
    calc
      ∫ x in openCubeSet Q,
          vecDot (u.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume =
        -∫ x in openCubeSet Q,
          vecDot (Gq.toField x) (phi.toH1Function.grad x) ∂volume :=
        hdivq phi
      _ = -∫ x in openCubeSet Q,
          vecDot (G2.toField x) (phi.toH1Function.grad x) ∂volume := by
        rw [hfield]
      _ = ∫ x in openCubeSet Q, G2.divergence x * phi.toH1Function x ∂volume :=
        (G2.integral_divergence_mul_zeroTrace_eq_neg_integral_vecDot phi).symm
  have hF2 : MemLp G2.divergence 2 (normalizedCubeMeasure Q) :=
    G2.divergence_memLp_normalizedCubeMeasure
  have hFq : MemLp G2.divergence q.exponent (normalizedCubeMeasure Q) := by
    rw [hdiv_eq]
    exact vectorW1pDivergence_memLp Gq
  obtain ⟨H, hHmem, hHbound⟩ := hC0 m G2.divergence hF2 hFq u (by
    simpa only [Q] using hpoisson)
  have hrows : ∀ i : Fin d,
      MemLp (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x)) q.exponent
        (normalizedCubeMeasure Q) := by
    rw [MeasureTheory.memLp_piLp_iff] at hHmem
    intro i
    simpa only [Function.comp_apply, HilbertMat.ofMat, HilbertVec.ofVec,
      PiLp.toLp_apply] using hHmem i
  let V : CubeVectorW1pFunction Q q := CubeVectorW1pFunction.ofWeakHessian H hrows
  refine ⟨V, ?_, ?_⟩
  · simp only [V, CubeVectorW1pFunction.ofWeakHessian_toField]
  · have hdivbound :
        eLpNorm G2.divergence q.exponent (normalizedCubeMeasure Q) ≤
          d * eLpNorm (fun x ↦ HilbertMat.ofMat (Gq.jacobian x)) q.exponent
            (normalizedCubeMeasure Q) := by
      rw [hdiv_eq]
      exact eLpNorm_vectorW1pDivergence_le_dimension_mul_jacobian Gq
    calc
      eLpNorm (fun x ↦ HilbertMat.ofMat (V.jacobian x)) q.exponent
          (normalizedCubeMeasure Q) =
        eLpNorm (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x)) q.exponent
          (normalizedCubeMeasure Q) := by
        simp only [V, CubeVectorW1pFunction.ofWeakHessian_jacobian]
      _ ≤ C0 * eLpNorm G2.divergence q.exponent (normalizedCubeMeasure Q) := hHbound
      _ ≤ C0 *
          (d * eLpNorm (fun x ↦ HilbertMat.ofMat (Gq.jacobian x)) q.exponent
            (normalizedCubeMeasure Q)) := by
        gcongr
      _ = (C0 * d) * eLpNorm (fun x ↦ HilbertMat.ofMat (Gq.jacobian x)) q.exponent
          (normalizedCubeMeasure Q) := by ring

end CubeCalderonZygmund

end
end Homogenization
