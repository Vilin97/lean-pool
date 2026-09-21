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

public import LeanPool.PoincareGeometry.AlmostSchur.ContractedBianchiActual
public import LeanPool.PoincareGeometry.AlmostSchur.GlobalEnergy
public import LeanPool.PoincareGeometry.AlmostSchur.IntegratedTraceFreeHessian
public import LeanPool.PoincareGeometry.AlmostSchur.AlmostSchurAlgebra

/-! # Integrated actual contracted-Bianchi pairing

All integration by parts uses the proved global Green theorem for the
constructed Riemannian volume. A classical Poisson solution is an explicit
input, not an asserted consequence of weak solvability.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set MeasureTheory
open scoped Manifold ContDiff Topology BigOperators
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 3 E (TangentSpace I : M → Type _)]
local notation "TM" => (TangentSpace I : M → Type _)
local notation "LC" => (leviCivitaConnection (I := I) (M := M))
local instance pairingFiniteDimensional (x : M) : FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x

/-- The Ricci flux raises the first slot of Ricci paired against w.
The adjoint keeps the slot convention explicit without assuming symmetry. -/
def ricciPairingFlux (w : Π x, TM x) (x : M) : TM x :=
  (ricciRaisedEndomorphism LC x).adjoint (w x)

theorem inner_ricciPairingFlux (w : Π x, TM x) (x : M) (v : TM x) :
    inner ℝ v (ricciPairingFlux w x) = (LC).ricciCurvatureAlmostSchur x v (w x) := by
  rw [ricciPairingFlux, ContinuousLinearMap.adjoint_inner_right,
    inner_ricciRaisedEndomorphism]

/-- The flux is genuinely C¹, proved by local metric-dual reconstruction. -/
theorem contMDiff_ricciPairingFlux (w : Π x, TM x)
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% w)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% (ricciPairingFlux w)) := by
  intro x
  let b := Module.finBasis ℝ E
  let e := trivializationAt E TM x
  have hx := mem_baseSet_trivializationAt E TM x
  apply contMDiffAt_section_of_inner_localFrame b x x (mem_chart_source H x)
  intro j
  have he : (fun y ↦ inner ℝ (ricciPairingFlux w y) (e.localFrame b j y)) =
      fun y ↦ (LC).ricciCurvatureAlmostSchur y (e.localFrame b j y) (w y) := by
    funext y
    rw [real_inner_comm, inner_ricciPairingFlux]
  change ContMDiffAt I 𝓘(ℝ, ℝ) 1
    (fun y ↦ inner ℝ (ricciPairingFlux w y) (e.localFrame b j y)) x
  rw [he]
  exact contMDiffAt_ricciCurvature_apply_one LC leviCivitaConnection_metricCompatible
    leviCivitaConnection_torsion (contMDiffAt_localFrame_of_mem 3 e b j hx) (hw x)

/-- The pointwise flux rule contains the actual scalar differential and the
Hilbert--Schmidt Ricci/derivative pairing, with the factor 2 fixed by Bianchi. -/
theorem two_mul_divergence_ricciPairingFlux (w : Π x, TM x)
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% w)) (x : M) :
    2 * divergence LC (ricciPairingFlux w) x =
      mvfderiv I (LC).scalarCurvatureAlmostSchur x (w x) +
        2 * hilbertSchmidtInner (ricciRaisedEndomorphism LC x) (LC w x) := by
  let o := stdOrthonormalBasis ℝ (TM x)
  let e := trivializationAt E TM x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E TM x
  let b := o.toBasis.map (e.linearEquivAt (R := ℝ) x hx)
  let f := e.localFrame b
  have hf i : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% (f i)) x :=
    contMDiffAt_localFrame_of_mem 3 e b i hx
  have hfo i : f i x = o i := localFrame_map_orthonormalBasis x e hx o i
  have hflux := (contMDiff_ricciPairingFlux w hw x).mdifferentiableAt (by norm_num)
  have hterm i :
      inner ℝ (o i) (LC (ricciPairingFlux w) x (o i)) =
        ricciDirectionalDerivative LC (f i) (f i) w x +
          inner ℝ (ricciRaisedEndomorphism LC x (o i)) (LC w x (o i)) := by
    have hd := CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq
      leviCivitaConnection_metricCompatible (f i)
      ((hf i).mdifferentiableAt (by norm_num)) hflux
    simp only [inner_ricciPairingFlux] at hd
    simp only [ricciDirectionalDerivative, hfo, inner_ricciRaisedEndomorphism]
    simp only [hfo] at hd
    linarith
  have hb := leviCivita_contractedBianchi_actual x o w hw
  change mvfderiv I (LC).scalarCurvatureAlmostSchur x (w x) =
    2 * ∑ i, ricciDirectionalDerivative LC (f i) (f i) w x at hb
  rw [divergence, LinearMap.trace_eq_sum_inner _ o,
    hilbertSchmidtInner_eq_sum_inner _ _ o]
  change 2 * (∑ i, inner ℝ (o i) (LC (ricciPairingFlux w) x (o i))) =
    mvfderiv I (LC).scalarCurvatureAlmostSchur x (w x) +
      2 * ∑ i, inner ℝ (ricciRaisedEndomorphism LC x (o i)) (LC w x (o i))
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, hb]
  ring

/-- Removing both traces subtracts precisely the product of traces divided
by the dimension. This is the Hilbert--Schmidt pairing, not the operator norm. -/
theorem hilbertSchmidtInner_traceFree_parts
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (A B : V →L[ℝ] V)
    (hdim : Module.finrank ℝ V ≠ 0) :
    hilbertSchmidtInner (traceFree A) (traceFree B) =
      hilbertSchmidtInner A B -
        LinearMap.trace ℝ V A.toLinearMap / Module.finrank ℝ V *
          LinearMap.trace ℝ V B.toLinearMap := by
  let o := stdOrthonormalBasis ℝ V
  rw [hilbertSchmidtInner_traceFree_traceFree A B hdim,
    hilbertSchmidtInner_eq_sum_inner _ _ o, hilbertSchmidtInner_eq_sum_inner A B o]
  simp only [traceFree, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
    inner_sub_left, real_inner_smul_left, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [LinearMap.trace_eq_sum_inner B.toLinearMap o]
  rfl

local instance pairingMetricZero : IsContMDiffRiemannianBundle I (↑(0 : ℕ)) E TM :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)
local instance pairingMetricThree : IsContMDiffRiemannianBundle I (↑(3 : ℕ)) E TM :=
  IsContMDiffRiemannianBundle.of_le (n := 3) (by norm_num)
local instance pairingContinuousMetric : IsContinuousRiemannianBundle E TM :=
  continuousRiemannianBundle_of_contMDiff (I := I)

/-- Continuity of the genuine scalar differential paired with a C³ field. -/
theorem continuous_scalarDerivative_pairing (w : Π x, TM x)
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% w)) :
    Continuous (fun x ↦ mvfderiv I (LC).scalarCurvatureAlmostSchur x (w x)) := by
  have hR : ContMDiff I 𝓘(ℝ, ℝ) 1 (LC).scalarCurvatureAlmostSchur :=
    fun x ↦ contMDiffAt_scalarCurvature_one LC leviCivitaConnection_metricCompatible
      leviCivitaConnection_torsion x
  simpa only [inner_gradient] using
    (Continuous.inner_bundle (F := E) (E := TM)
      (contMDiff_gradient (I := I) 0 hR).continuous hw.continuous)

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [Nonempty M] [LindelofSpace M] [CompactSpace M]

local instance pairingFiniteMeasure : IsFiniteMeasure (riemannianVolume (I := I) (M := M)) :=
  ⟨(riemannianVolume_finite_positive (I := I)).2⟩

/-- Integrability is derived from the actual flux identity and continuity,
before the integrated identity separates any integrals. -/
theorem integrable_ricciDerivative_hilbertSchmidt (w : Π x, TM x)
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% w)) :
    Integrable (fun x ↦ hilbertSchmidtInner (ricciRaisedEndomorphism LC x) (LC w x))
      (riemannianVolume (I := I)) := by
  have he : (fun x ↦ hilbertSchmidtInner (ricciRaisedEndomorphism LC x) (LC w x)) =
      fun x ↦ divergence LC (ricciPairingFlux w) x -
        mvfderiv I (LC).scalarCurvatureAlmostSchur x (w x) / 2 := by
    funext x
    linarith [two_mul_divergence_ricciPairingFlux w hw x]
  rw [he]
  exact ((continuous_divergence LC leviCivitaConnection_metricCompatible
    leviCivitaConnection_torsion _ (contMDiff_ricciPairingFlux w hw)).sub
    ((continuous_scalarDerivative_pairing w hw).div_const 2)).integrable_of_hasCompactSupport
      isClosed_closure.isCompact

/-- Global contracted Bianchi paired with a C³ field, proved by Green on
the C¹ Ricci flux. The negative sign is from the divergence convention. -/
theorem integrated_contractedBianchi_field (w : Π x, TM x)
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% w)) :
    (∫ x, mvfderiv I (LC).scalarCurvatureAlmostSchur x (w x) ∂riemannianVolume (I := I)) =
      -2 * ∫ x, hilbertSchmidtInner (ricciRaisedEndomorphism LC x) (LC w x)
        ∂riemannianVolume (I := I) := by
  have hzero := integral_mul_divergence LC leviCivitaConnection_metricCompatible
    leviCivitaConnection_torsion (fun _ ↦ (1 : ℝ)) (ricciPairingFlux w)
    contMDiff_const (contMDiff_ricciPairingFlux w hw)
  simp only [one_mul, mvfderiv_const, zero_apply, integral_zero, neg_zero] at hzero
  have hD := (continuous_scalarDerivative_pairing w hw).integrable_of_hasCompactSupport
    (μ := riemannianVolume (I := I)) isClosed_closure.isCompact
  have hP := integrable_ricciDerivative_hilbertSchmidt w hw
  have hi := integral_congr_ae (μ := riemannianVolume (I := I))
    (Filter.Eventually.of_forall (two_mul_divergence_ricciPairingFlux w hw))
  rw [integral_const_mul, integral_add hD (hP.const_mul 2), integral_const_mul, hzero] at hi
  linarith

/-- The intrinsic trace-free Ricci/Hessian integrand used in the final algebra. -/
def contractedBianchiPairingIntegrand (f : M → ℝ) (x : M) : ℝ :=
  hilbertSchmidtInner (traceFree (ricciRaisedEndomorphism LC x))
    (traceFree (LC (gradient (I := I) f) x))

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [Nonempty M] [LindelofSpace M] [CompactSpace M] in
/-- The pointwise trace subtraction has the exact coefficient Scal/d. -/
theorem contractedBianchiPairingIntegrand_eq (f : M → ℝ)
    (hdim : Module.finrank ℝ E ≠ 0) (x : M) :
    contractedBianchiPairingIntegrand (I := I) f x =
      hilbertSchmidtInner (ricciRaisedEndomorphism LC x) (LC (gradient (I := I) f) x) -
        (LC).scalarCurvatureAlmostSchur x / Module.finrank ℝ E * laplacian LC f x := by
  have hrank := VectorBundle.finrank_eq ℝ E TM x
  have hn : Module.finrank ℝ (TM x) ≠ 0 := by rwa [hrank]
  rw [contractedBianchiPairingIntegrand, hilbertSchmidtInner_traceFree_parts _ _ hn,
    ← scalarCurvature_eq_trace_ricciRaisedEndomorphism, hrank]
  rfl

/-- The actual trace-free pairing is integrable; this is not an added analytic
premise on the final identity. C⁴ suffices for all uses of contracted Bianchi. -/
theorem integrable_contractedBianchiPairingIntegrand {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 4 f) (hdim : Module.finrank ℝ E ≠ 0) :
    Integrable (contractedBianchiPairingIntegrand (I := I) f) (riemannianVolume (I := I)) := by
  have hG : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% (gradient (I := I) f)) :=
    contMDiff_gradient 3 hf
  have hR : ContMDiff I 𝓘(ℝ, ℝ) 1 (LC).scalarCurvatureAlmostSchur :=
    fun x ↦ contMDiffAt_scalarCurvature_one LC leviCivitaConnection_metricCompatible
      leviCivitaConnection_torsion x
  have hL := continuous_laplacian LC leviCivitaConnection_metricCompatible
    leviCivitaConnection_torsion f (hf.of_le (by norm_num))
  have hprod := ((hR.continuous.div_const (Module.finrank ℝ E : ℝ)).mul hL).integrable_of_hasCompactSupport
    (μ := riemannianVolume (I := I)) isClosed_closure.isCompact
  have he := funext (contractedBianchiPairingIntegrand_eq (I := I) f hdim)
  rw [he]
  exact (integrable_ricciDerivative_hilbertSchmidt _ hG).sub hprod

/-- Before trace subtraction, global Green and actual contracted Bianchi give
the scalar variance as twice the full Ricci/Hessian pairing.

The Poisson equation uses Δ = div grad and forces the centered scalar field
to have zero integral; no separate mean assumption or integration bridge is used. -/
theorem scalar_variance_eq_two_mul_ricciHessian_of_poisson
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 4 f) (r : ℝ)
    (hpoisson : ∀ x, laplacian LC f x = (LC).scalarCurvatureAlmostSchur x - r) :
    (∫ x, ((LC).scalarCurvatureAlmostSchur x - r) ^ 2 ∂riemannianVolume (I := I)) =
      2 * ∫ x, hilbertSchmidtInner (ricciRaisedEndomorphism LC x)
        (LC (gradient (I := I) f) x) ∂riemannianVolume (I := I) := by
  have hR : ContMDiff I 𝓘(ℝ, ℝ) 1 (LC).scalarCurvatureAlmostSchur :=
    fun x ↦ contMDiffAt_scalarCurvature_one LC leviCivitaConnection_metricCompatible
      leviCivitaConnection_torsion x
  have hG : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% (gradient (I := I) f)) :=
    contMDiff_gradient 3 hf
  have hgreen := integral_mul_divergence LC leviCivitaConnection_metricCompatible
    leviCivitaConnection_torsion (fun x ↦ (LC).scalarCurvatureAlmostSchur x - r)
    (gradient (I := I) f) (hR.sub contMDiff_const) (hG.of_le (by norm_num))
  have hd x : mvfderiv I (fun y ↦ (LC).scalarCurvatureAlmostSchur y - r) x =
      mvfderiv I (LC).scalarCurvatureAlmostSchur x := by
    rw [mvfderiv_fun_sub ((hR x).mdifferentiableAt (by norm_num))
      mdifferentiableAt_const, mvfderiv_const, sub_zero]
  simp only [divergence_gradient, hpoisson, ← sq, hd] at hgreen
  rw [integrated_contractedBianchi_field _ hG] at hgreen
  linarith

/-- Exact contracted-Bianchi identity for the almost-Schur algebra:
(d - 2) A = 2 d P, where A is scalar variance and P is the integral of the
trace-free Ricci/Hessian Hilbert--Schmidt pairing. Every integration step and
integrability premise is proved from the compact geometry and C⁴ solution. -/
theorem contractedBianchi_pairing_of_poisson
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 4 f) (r : ℝ)
    (hpoisson : ∀ x, laplacian LC f x = (LC).scalarCurvatureAlmostSchur x - r)
    (hdim : Module.finrank ℝ E ≠ 0) :
    ((Module.finrank ℝ E : ℝ) - 2) *
        (∫ x, ((LC).scalarCurvatureAlmostSchur x - r) ^ 2 ∂riemannianVolume (I := I)) =
      2 * (Module.finrank ℝ E : ℝ) *
        (∫ x, contractedBianchiPairingIntegrand (I := I) f x ∂riemannianVolume (I := I)) := by
  have hR : ContMDiff I 𝓘(ℝ, ℝ) 1 (LC).scalarCurvatureAlmostSchur :=
    fun x ↦ contMDiffAt_scalarCurvature_one LC leviCivitaConnection_metricCompatible
      leviCivitaConnection_torsion x
  have hc : Continuous (fun x ↦ (LC).scalarCurvatureAlmostSchur x - r) :=
    hR.continuous.sub continuous_const
  have hi := hc.integrable_of_hasCompactSupport (μ := riemannianVolume (I := I))
    isClosed_closure.isCompact
  have hisq : Integrable (fun x ↦ ((LC).scalarCurvatureAlmostSchur x - r) ^ 2)
      (riemannianVolume (I := I)) :=
    (hc.pow 2).integrable_of_hasCompactSupport isClosed_closure.isCompact
  have hmean : (∫ x, (LC).scalarCurvatureAlmostSchur x - r ∂riemannianVolume (I := I)) = 0 := by
    simpa only [hpoisson] using integral_laplacian_eq_zero LC
      leviCivitaConnection_metricCompatible leviCivitaConnection_torsion f
      (hf.of_le (by norm_num))
  have hprod : (∫ x, (LC).scalarCurvatureAlmostSchur x * laplacian LC f x
      ∂riemannianVolume (I := I)) =
      ∫ x, ((LC).scalarCurvatureAlmostSchur x - r) ^ 2 ∂riemannianVolume (I := I) := by
    have he : (fun x ↦ (LC).scalarCurvatureAlmostSchur x * laplacian LC f x) =
        fun x ↦ ((LC).scalarCurvatureAlmostSchur x - r) ^ 2 + r * ((LC).scalarCurvatureAlmostSchur x - r) := by
      funext x
      rw [hpoisson]
      ring
    rw [he, integral_add hisq (hi.const_mul r), integral_const_mul, hmean, mul_zero, add_zero]
  have hG : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% (gradient (I := I) f)) :=
    contMDiff_gradient 3 hf
  have hH := integrable_ricciDerivative_hilbertSchmidt _ hG
  have hL := continuous_laplacian LC leviCivitaConnection_metricCompatible
    leviCivitaConnection_torsion f (hf.of_le (by norm_num))
  have hQ : Integrable (fun x ↦ ((LC).scalarCurvatureAlmostSchur x * laplacian LC f x) /
      (Module.finrank ℝ E : ℝ)) (riemannianVolume (I := I)) :=
    ((hR.continuous.mul hL).div_const (Module.finrank ℝ E : ℝ)).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  have hp : (∫ x, contractedBianchiPairingIntegrand (I := I) f x
      ∂riemannianVolume (I := I)) =
      (∫ x, hilbertSchmidtInner (ricciRaisedEndomorphism LC x)
        (LC (gradient (I := I) f) x) ∂riemannianVolume (I := I)) -
      (∫ x, ((LC).scalarCurvatureAlmostSchur x - r) ^ 2 ∂riemannianVolume (I := I)) /
        (Module.finrank ℝ E : ℝ) := by
    have he : contractedBianchiPairingIntegrand (I := I) f = fun x ↦
        hilbertSchmidtInner (ricciRaisedEndomorphism LC x) (LC (gradient (I := I) f) x) -
          ((LC).scalarCurvatureAlmostSchur x * laplacian LC f x) / (Module.finrank ℝ E : ℝ) := by
      funext x
      rw [contractedBianchiPairingIntegrand_eq f hdim]
      ring
    rw [he, integral_sub hH hQ, integral_div, hprod]
  have ha := scalar_variance_eq_two_mul_ricciHessian_of_poisson hf r hpoisson
  have hn : (Module.finrank ℝ E : ℝ) ≠ 0 := by exact_mod_cast hdim
  rw [hp, ha]
  field_simp

/-- Smooth mean-zero Poisson input for the eventual global existence theorem.
The normalization is recorded explicitly; the pairing core itself is stronger
and does not need it, since adding a constant to f does not affect the identity. -/
theorem contractedBianchi_pairing_of_smooth_meanZero_poisson
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (_hmean : (∫ x, f x ∂riemannianVolume (I := I)) = 0) (r : ℝ)
    (hpoisson : ∀ x, laplacian LC f x = (LC).scalarCurvatureAlmostSchur x - r)
    (hdim : Module.finrank ℝ E ≠ 0) :
    ((Module.finrank ℝ E : ℝ) - 2) *
        (∫ x, ((LC).scalarCurvatureAlmostSchur x - r) ^ 2 ∂riemannianVolume (I := I)) =
      2 * (Module.finrank ℝ E : ℝ) *
        (∫ x, contractedBianchiPairingIntegrand (I := I) f x ∂riemannianVolume (I := I)) :=
  contractedBianchi_pairing_of_poisson
    (hf.of_le (WithTop.coe_le_coe.2 (le_top : (4 : ℕ∞) ≤ ⊤))) r hpoisson hdim

omit [IsContMDiffRiemannianBundle I 3 E TM] in
/-- The same classical Poisson input identifies the trace-free Hessian
decomposition's Laplacian energy with the very same scalar variance A. -/
theorem poisson_traceFreeHessian_identity
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 4 f) (r : ℝ)
    (hpoisson : ∀ x, laplacian LC f x = (LC).scalarCurvatureAlmostSchur x - r)
    (hdim : Module.finrank ℝ E ≠ 0) :
    (Module.finrank ℝ E : ℝ) *
        (∫ x, traceFreeHessianNormSq LC f x ∂riemannianVolume (I := I)) =
      (Module.finrank ℝ E : ℝ) *
          (∫ x, hessianNormSq LC f x ∂riemannianVolume (I := I)) -
        ∫ x, ((LC).scalarCurvatureAlmostSchur x - r) ^ 2 ∂riemannianVolume (I := I) := by
  simpa only [hpoisson] using finrank_mul_integral_traceFreeHessianNormSq LC
    leviCivitaConnection_metricCompatible leviCivitaConnection_torsion
    (hf.of_le (by norm_num : (3 : ℕ∞ω) ≤ 4)) hdim

end AlmostSchur
