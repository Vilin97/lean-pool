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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.RaisedRicci
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.RicciNorm

/-!
# Three-dimensional Ricci norm and curvature-reaction algebra

For a metric-compatible torsion-free connection in tangent dimension three,
the Ricci tensor is diagonal in the eigenbasis of the genuine
Ricci-complement curvature operator.  Parseval's identity and trace
invariance then give the exact identity

`2 |Ric|² = λ² + μ² + ν² + λ μ + λ ν + μ ν`.

This is the algebraic bridge that turns the intrinsic scalar-curvature
variation into the scalar reaction used by Hamilton--Ivey.  No coordinate
presentation or symmetrized readout is used.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff BigOperators RealInnerProductSpace

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

theorem two_mul_ricciNormSq_eq_threeDimensionalCurvatureReaction
    [IsContMDiffRiemannianBundle I 2 E TM]
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangent)
    (x : M) (hdim : Module.finrank ℝ (TM x) = 3) :
    2 * ricciNormSq (cov := cov) x =
      (threeDimensionalCurvatureLambda cov hT hmetric x hdim) ^ 2 +
        (threeDimensionalCurvatureMu cov hT hmetric x hdim) ^ 2 +
        (threeDimensionalCurvatureNu cov hT hmetric x hdim) ^ 2 +
      threeDimensionalCurvatureLambda cov hT hmetric x hdim *
        threeDimensionalCurvatureMu cov hT hmetric x hdim +
      threeDimensionalCurvatureLambda cov hT hmetric x hdim *
        threeDimensionalCurvatureNu cov hT hmetric x hdim +
      threeDimensionalCurvatureMu cov hT hmetric x hdim *
        threeDimensionalCurvatureNu cov hT hmetric x hdim := by
  let A : TM x →ₗ[ℝ] TM x :=
    (raisedRicciEndomorphism cov x).toLinearMap
  let o : OrthonormalBasis (Fin (Module.finrank ℝ (TM x))) ℝ (TM x) :=
    stdOrthonormalBasis ℝ (TM x)
  let b : OrthonormalBasis (Fin 3) ℝ (TM x) :=
    ricciComplementEigenbasis cov hT hmetric x hdim
  have hricciNorm : ricciNormSq (cov := cov) x =
      ∑ i : Fin (Module.finrank ℝ (TM x)), ‖A (o i)‖ ^ 2 := by
    rw [ricciNormSq_eq_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hparse := o.sum_sq_inner_left (A (o i))
    calc
      ∑ j : Fin (Module.finrank ℝ (TM x)),
          (ricciCurvature (cov := cov) x (o i) (o j)) ^ 2 =
          ∑ j : Fin (Module.finrank ℝ (TM x)),
            (inner ℝ (A (o i)) (o j)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [← inner_raisedRicciEndomorphism cov x (o i) (o j)]
          rfl
      _ = ‖A (o i)‖ ^ 2 := hparse
  have htrace_o := LinearMap.trace_eq_sum_inner (A.adjoint.comp A) o
  have hnorm_trace_o :
      (∑ i : Fin (Module.finrank ℝ (TM x)), ‖A (o i)‖ ^ 2) =
        LinearMap.trace ℝ (TM x) (A.adjoint.comp A) := by
    rw [htrace_o]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_comm]
    change ‖A (o i)‖ ^ 2 =
      inner ℝ (LinearMap.adjoint A (A (o i))) (o i)
    rw [LinearMap.adjoint_inner_left]
    exact (real_inner_self_eq_norm_sq _).symm
  have htrace_b := LinearMap.trace_eq_sum_inner (A.adjoint.comp A) b
  have hsum_norm_b :
      (∑ i : Fin 3, ‖A (b i)‖ ^ 2) =
        LinearMap.trace ℝ (TM x) (A.adjoint.comp A) := by
    rw [htrace_b]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_comm]
    change ‖A (b i)‖ ^ 2 =
      inner ℝ (LinearMap.adjoint A (A (b i))) (b i)
    rw [LinearMap.adjoint_inner_left]
    exact (real_inner_self_eq_norm_sq _).symm
  have hnorm_change :
      (∑ i : Fin (Module.finrank ℝ (TM x)), ‖A (o i)‖ ^ 2) =
        ∑ i : Fin 3, ‖A (b i)‖ ^ 2 := by
    rw [hnorm_trace_o, hsum_norm_b]
  have hA_eig : ∀ i : Fin 3,
      A (b i) =
        ((scalarCurvature (cov := cov) x -
          ricciComplementEigenvalues cov hT hmetric x hdim i) / 2) • b i := by
    intro i
    have hC := ricciComplementEndomorphism_apply_eigenbasis
      cov hT hmetric x hdim i
    change scalarCurvature (cov := cov) x • b i -
        (2 : ℝ) • A (b i) =
      ricciComplementEigenvalues cov hT hmetric x hdim i • b i at hC
    have hmove : scalarCurvature (cov := cov) x • b i =
        ricciComplementEigenvalues cov hT hmetric x hdim i • b i +
          (2 : ℝ) • A (b i) := (sub_eq_iff_eq_add).mp hC
    have hscaled : (2 : ℝ) • A (b i) =
        scalarCurvature (cov := cov) x • b i -
          ricciComplementEigenvalues cov hT hmetric x hdim i • b i := by
      apply (eq_sub_iff_add_eq').2
      exact hmove.symm
    have hscaled' : (2 : ℝ) • A (b i) =
        (scalarCurvature (cov := cov) x -
          ricciComplementEigenvalues cov hT hmetric x hdim i) • b i := by
      rw [sub_smul]
      exact hscaled
    have hhalf := congrArg (fun z : TM x => ((1 : ℝ) / 2) • z) hscaled'
    simpa [smul_smul, div_eq_mul_inv, mul_comm] using hhalf
  have hnorm_eig : ∀ i : Fin 3,
      ‖A (b i)‖ ^ 2 =
        ((scalarCurvature (cov := cov) x -
          ricciComplementEigenvalues cov hT hmetric x hdim i) / 2) ^ 2 := by
    intro i
    rw [hA_eig i, norm_smul]
    have hb : ‖b i‖ = 1 := by simp
    rw [hb, mul_one, Real.norm_eq_abs, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), div_pow, div_pow, sq_abs]
  have hsum := threeDimensionalCurvatureLambda_add_mu_add_nu_eq_scalarCurvature
    cov hT hmetric x hdim
  rw [hricciNorm, hnorm_change]
  simp only [Fin.sum_univ_three]
  rw [hnorm_eig 0, hnorm_eig 1, hnorm_eig 2]
  change 2 * (((scalarCurvature (cov := cov) x -
      threeDimensionalCurvatureLambda cov hT hmetric x hdim) / 2) ^ 2 +
    ((scalarCurvature (cov := cov) x -
      threeDimensionalCurvatureMu cov hT hmetric x hdim) / 2) ^ 2 +
    ((scalarCurvature (cov := cov) x -
      threeDimensionalCurvatureNu cov hT hmetric x hdim) / 2) ^ 2) = _
  rw [← hsum]
  ring

end CovariantDerivative
