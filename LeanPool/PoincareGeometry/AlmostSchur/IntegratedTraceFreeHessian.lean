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

public import LeanPool.PoincareGeometry.AlmostSchur.IntegratedRawBochner

/-!
# Integrated trace-free Hessian decomposition

This is the exact integrated form of the pointwise orthogonal splitting.  It
is stated for any regular metric-compatible torsion-free tangent connection,
so the final almost-Schur argument can specialize it to the constructed
Levi--Civita connection.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [Nonempty M] [LindelofSpace M] [T2Space M] [CompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The trace-free Hessian energy is integrable under the same hypotheses as
the integrated Bochner identity. -/
theorem integrable_traceFreeHessianNormSq
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f)
    (hdim : Module.finrank ℝ E ≠ 0) :
    Integrable (traceFreeHessianNormSq cov f) (riemannianVolume (I := I)) := by
  have hH := integrable_hessianNormSq cov hm ht hf
  have hL := integrable_laplacian_sq cov hf
  have heq : traceFreeHessianNormSq cov f = fun x =>
      hessianNormSq cov f x -
        (laplacian cov f x) ^ 2 / Module.finrank ℝ E := by
    funext x
    exact traceFreeHessianNormSq_eq cov f x hdim
  rw [heq]
  exact hH.sub (hL.div_const _)

/-- Exact integrated trace-free decomposition, arranged without division.
This is the identity `d H₀ = d H - L` used in the final algebra. -/
theorem finrank_mul_integral_traceFreeHessianNormSq
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f)
    (hdim : Module.finrank ℝ E ≠ 0) :
    (Module.finrank ℝ E : ℝ) *
        (∫ x, traceFreeHessianNormSq cov f x ∂riemannianVolume (I := I)) =
      (Module.finrank ℝ E : ℝ) *
          (∫ x, hessianNormSq cov f x ∂riemannianVolume (I := I)) -
        ∫ x, (laplacian cov f x) ^ 2 ∂riemannianVolume (I := I) := by
  have hn : (Module.finrank ℝ E : ℝ) ≠ 0 := by exact_mod_cast hdim
  have hH := integrable_hessianNormSq cov hm ht hf
  have hL := integrable_laplacian_sq cov hf
  have hT := integrable_traceFreeHessianNormSq cov hm ht hf hdim
  have heq :
      (∫ x, traceFreeHessianNormSq cov f x ∂riemannianVolume (I := I)) =
        (∫ x, hessianNormSq cov f x ∂riemannianVolume (I := I)) -
          (∫ x, (laplacian cov f x) ^ 2 ∂riemannianVolume (I := I)) /
            Module.finrank ℝ E := by
    rw [← integral_div]
    rw [← integral_sub hH (hL.div_const _)]
    apply integral_congr_ae
    filter_upwards [] with x
    exact traceFreeHessianNormSq_eq cov f x hdim
  rw [heq]
  field_simp

end AlmostSchur
