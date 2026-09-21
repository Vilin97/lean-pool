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

public import LeanPool.PoincareGeometry.AlmostSchur.RawBochnerFlux
public import LeanPool.PoincareGeometry.AlmostSchur.GlobalGreen

/-! # Integrated Bochner identity for the actual raw curvature contraction

The flux has proved C¹ regularity. Each separated integrand is proved
integrable before integration is distributed. The measure is the constructed
Riemannian volume. Identification with a bundled Ricci tensor, and selection
of a genuine Levi–Civita connection, are separate geometric obligations.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set MeasureTheory
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
local notation "TM" => (TangentSpace I : M → Type _)

/-- Squaring a C¹ tangent endomorphism section preserves C¹ regularity.
This is proved in actual bundle coordinates using conjugation. -/
theorem contMDiff_endomorphism_sq (A : Π y, TM y →L[ℝ] TM y)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (A y))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y ((A y).comp (A y))) := by
  intro x
  apply (contMDiffAt_hom_bundle _).mpr
  refine ⟨contMDiffAt_id, ?_⟩
  have hc := ((contMDiffAt_hom_bundle _).mp (hA x)).2
  apply (hc.clm_comp hc).congr_of_eventuallyEq
  let e := trivializationAt E TM x
  filter_upwards [e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E TM x)] with y hy
  rw [ContinuousLinearMap.inCoordinates_eq hy hy,
    ContinuousLinearMap.inCoordinates_eq hy hy]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

/-- The genuine squared Hessian norm is C¹ for the C³ data used by the flux
identity; no tensor-norm regularity premise is assumed. -/
theorem contMDiff_hessianNormSq (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f) :
    ContMDiff I 𝓘(ℝ, ℝ) 1 (hessianNormSq cov f) := by
  have hG := contMDiff_gradient (I := I) 2 hf
  have hA := contMDiffOn_univ.mp
    ((CovariantDerivative.ContMDiffCovariantDerivative.contMDiff
      (cov := cov) (k := 1)).contMDiff hG.contMDiffOn)
  have hs := contMDiff_trace_endomorphism 1 _ (contMDiff_endomorphism_sq _ hA)
  have he : (fun x ↦ LinearMap.trace ℝ (TM x)
      ((cov (gradient (I := I) f) x).comp (cov (gradient (I := I) f) x)).toLinearMap) =
      hessianNormSq cov f := by
    funext x
    exact trace_gradientDerivative_sq cov hm ht (hf.of_le (by norm_num)) x
  rwa [he] at hs

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]

/-- Continuity of the actual raw curvature contraction follows from the
proved flux identity and genuine regularity of its other terms. -/
theorem continuous_rawRicciGradient (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f) :
    Continuous (rawRicciGradient cov f) := by
  have he : rawRicciGradient cov f = fun x ↦ (laplacian cov f x) ^ 2 -
      hessianNormSq cov f x - divergence cov (bochnerFlux cov f) x := by
    funext x
    have h := divergence_bochnerFlux cov hm ht hf x
    linarith
  rw [he]
  exact (((contMDiff_laplacian cov hf).continuous.pow 2).sub
    (contMDiff_hessianNormSq cov hm ht hf).continuous).sub
    (continuous_divergence cov hm ht _ (contMDiff_bochnerFlux cov hf))

variable [Nonempty M] [LindelofSpace M] [T2Space M] [CompactSpace M]

local instance integratedRawBochnerContinuousMetric :
    IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

local instance integratedRawBochnerFiniteMeasure :
    IsFiniteMeasure (riemannianVolume (I := I) (M := M)) :=
  ⟨(riemannianVolume_finite_positive (I := I)).2⟩

/-- The actual squared Laplacian is integrable on the compact manifold. -/
theorem integrable_laplacian_sq (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f) :
    Integrable (fun x ↦ (laplacian cov f x) ^ 2) (riemannianVolume (I := I)) :=
  ((contMDiff_laplacian cov hf).continuous.pow 2).integrable_of_hasCompactSupport
    isClosed_closure.isCompact

/-- The actual Hessian norm is integrable before distributing its integral. -/
theorem integrable_hessianNormSq (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f) :
    Integrable (hessianNormSq cov f) (riemannianVolume (I := I)) :=
  (contMDiff_hessianNormSq cov hm ht hf).continuous.integrable_of_hasCompactSupport
    isClosed_closure.isCompact

/-- The actual raw curvature contraction is integrable, not merely a formal
term in a totalized Bochner integral. -/
theorem integrable_rawRicciGradient (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f) :
    Integrable (rawRicciGradient cov f) (riemannianVolume (I := I)) :=
  (continuous_rawRicciGradient cov hm ht hf).integrable_of_hasCompactSupport
    isClosed_closure.isCompact

/-- Global Green applies to the actual C¹ Bochner flux. -/
theorem integral_divergence_bochnerFlux_eq_zero (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f) :
    (∫ x, divergence cov (bochnerFlux cov f) x ∂riemannianVolume (I := I)) = 0 := by
  have h := integral_mul_divergence cov hm ht (fun _ ↦ (1 : ℝ))
    (bochnerFlux cov f) contMDiff_const (contMDiff_bochnerFlux cov hf)
  simpa only [one_mul, mvfderiv_const, zero_apply,
    integral_zero, neg_zero] using h

/-- Integrated Bochner identity for the actual raw gradient contraction and
the constructed Riemannian volume. This does not yet identify bundled Ricci. -/
theorem integratedRawBochner (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f) :
    (∫ x, hessianNormSq cov f x ∂riemannianVolume (I := I)) +
      (∫ x, rawRicciGradient cov f x ∂riemannianVolume (I := I)) =
      ∫ x, (laplacian cov f x) ^ 2 ∂riemannianVolume (I := I) := by
  have hL := integrable_laplacian_sq cov hf
  have hH := integrable_hessianNormSq cov hm ht hf
  have hR := integrable_rawRicciGradient cov hm ht hf
  have h := integral_divergence_bochnerFlux_eq_zero cov hm ht hf
  simp_rw [divergence_bochnerFlux cov hm ht hf] at h
  change (∫ x, ((fun y ↦ (laplacian cov f y) ^ 2) - hessianNormSq cov f) x -
    rawRicciGradient cov f x ∂riemannianVolume (I := I)) = 0 at h
  rw [integral_sub (hL.sub hH) hR] at h
  simp only [Pi.sub_apply] at h
  rw [integral_sub hL hH] at h
  linarith

end AlmostSchur
