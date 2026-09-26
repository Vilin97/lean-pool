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

public import LeanPool.PoincareGeometry.AlmostSchur.ContractedBianchiPairing
public import LeanPool.PoincareGeometry.AlmostSchur.SmoothWeakPoisson
public import LeanPool.PoincareGeometry.AlmostSchur.NonnegativeRicciBochner
public import LeanPool.PoincareGeometry.AlmostSchur.AlmostSchurTheorem
public import LeanPool.PoincareGeometry.AlmostSchur.L2BilinearIntegral

/-! # The finite-dimensional almost-Schur assembly

This file contains the final geometric estimate once a classical Poisson
representative is available.  The regularity and integrability of the
trace-free Ricci energy are proved in the varying tangent bundle; no fixed
fiber or unproved tensor norm is used.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set MeasureTheory
open scoped Manifold ContDiff Topology BigOperators
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 3 E (TangentSpace I : M → Type _)]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
  [Nonempty M] [LindelofSpace M] [CompactSpace M] [PreconnectedSpace M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "LC" => (leviCivitaConnection (I := I) (M := M))

local instance boundMetricZero : IsContMDiffRiemannianBundle I (↑(0 : ℕ)) E TM :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)
local instance boundContinuousMetric : IsContinuousRiemannianBundle E TM :=
  continuousRiemannianBundle_of_contMDiff (I := I)
local instance boundFiniteMeasure : IsFiniteMeasure (riemannianVolume (I := I) (M := M)) :=
  ⟨(riemannianVolume_finite_positive (I := I)).2⟩
local instance boundFiberFiniteDimensional (x : M) : FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x

local instance boundManifoldMinThree : IsManifold I (minSmoothness ℝ 3) M :=
  IsManifold.of_le (n := ∞) (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)
local instance boundManifoldTwoAddOne : IsManifold I ((2 : ℕ∞) + 1) M :=
  IsManifold.of_le (n := ∞) (by exact_mod_cast (le_top : (2 + 1 : ℕ∞) ≤ ⊤))

private theorem ricciCurvature_symm_LC (x : M) (u v : TM x) :
    (leviCivitaConnection (I := I) (M := M)).ricciCurvatureAlmostSchur x u v =
      (leviCivitaConnection (I := I) (M := M)).ricciCurvatureAlmostSchur x v u := by
  exact CovariantDerivative.ricciCurvature_symm_of_metricCompatibleTangent_of_torsion_eq_zeroAlmostSchur
    (cov := leviCivitaConnection (I := I) (M := M))
    leviCivitaConnection_torsion
    (tangentMetricCompatible_to_curvatureVendor
      (leviCivitaConnection (I := I) (M := M))
      leviCivitaConnection_metricCompatible) x u v

theorem ricciRaised_isSelfAdjoint (x : M) :
    IsSelfAdjoint (ricciRaisedEndomorphism LC x) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  calc
    inner ℝ (ricciRaisedEndomorphism LC x u) v =
        (leviCivitaConnection (I := I) (M := M)).ricciCurvatureAlmostSchur x u v :=
      inner_ricciRaisedEndomorphism LC x u v
    _ = (leviCivitaConnection (I := I) (M := M)).ricciCurvatureAlmostSchur x v u :=
      ricciCurvature_symm_LC x u v
    _ = inner ℝ (ricciRaisedEndomorphism LC x v) u :=
      (inner_ricciRaisedEndomorphism LC x v u).symm
  rw [real_inner_comm]
  rfl

theorem contMDiffAt_traceFree_endomorphism_one
    (A : Π y, TM y →L[ℝ] TM y)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (A y))) (x : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (traceFree (A y))) x := by
  let b := Module.finBasis ℝ E
  let e := trivializationAt E TM x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E TM x
  have htr : ContMDiff I 𝓘(ℝ, ℝ) 1
      (fun y ↦ LinearMap.trace ℝ (TM y) (A y).toLinearMap) :=
    contMDiff_trace_endomorphism 1 A hA
  apply contMDiffAt_endomorphism_of_localFrame 1 _ x b
  intro i
  have hAi := hA x |>.clm_bundle_apply
    (contMDiffAt_localFrame_of_mem 1 e b i hx)
  have hFi : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1 (T% (e.localFrame b i)) x :=
    contMDiffAt_localFrame_of_mem 1 e b i hx
  have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) 1
      (fun y ↦ LinearMap.trace ℝ (TM y) (A y).toLinearMap /
        (Module.finrank ℝ E : ℝ)) x :=
    (htr x).div_const _
  have hscalar' : ContMDiffAt I 𝓘(ℝ, ℝ) 1
      (fun y ↦ LinearMap.trace ℝ (TM y) (A y).toLinearMap /
        (Module.finrank ℝ (TM y) : ℝ)) x := by
    apply hscalar.congr_of_eventuallyEq
    filter_upwards [] with y
    rw [VectorBundle.finrank_eq ℝ E TM y]
  have hsmul := hscalar'.smul_section hFi
  apply (hAi.sub_section hsmul).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  congr 1

theorem contMDiff_traceFree_ricci_one :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y
        (traceFree (ricciRaisedEndomorphism LC y))) := by
  intro x
  apply contMDiffAt_traceFree_endomorphism_one
  · intro y
    exact contMDiffAt_ricciRaisedEndomorphism_one LC
      leviCivitaConnection_metricCompatible leviCivitaConnection_torsion y

theorem traceFree_ricci_isSelfAdjoint (x : M) :
    IsSelfAdjoint (traceFree (ricciRaisedEndomorphism LC x)) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  change star (ricciRaisedEndomorphism LC x -
    ((LinearMap.trace ℝ (TM x)) (ricciRaisedEndomorphism LC x).toLinearMap /
      (Module.finrank ℝ (TM x) : ℝ)) • ContinuousLinearMap.id ℝ (TM x)) = _
  rw [star_sub, StarModule.star_smul]
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_id,
    TrivialStar.star_trivial]
  rw [ContinuousLinearMap.isSelfAdjoint_iff'.mp
    (ricciRaised_isSelfAdjoint (I := I) (M := M) x)]
  rfl

theorem hilbertSchmidtSq_traceFree_ricci_eq_trace_comp (x : M) :
    hilbertSchmidtSq (traceFree (ricciRaisedEndomorphism LC x)) =
      LinearMap.trace ℝ (TM x)
        ((traceFree (ricciRaisedEndomorphism LC x)).comp
          (traceFree (ricciRaisedEndomorphism LC x))).toLinearMap := by
  unfold hilbertSchmidtSq
  rw [(ContinuousLinearMap.isSelfAdjoint_iff'.mp
    (traceFree_ricci_isSelfAdjoint x))]

theorem contMDiff_traceFreeRicciNormSq_one :
    ContMDiff I 𝓘(ℝ, ℝ) 1 (fun x ↦ hilbertSchmidtSq
      (traceFree (ricciRaisedEndomorphism LC x))) := by
  let A : Π y, TM y →L[ℝ] TM y := fun y ↦ traceFree (ricciRaisedEndomorphism LC y)
  have hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (A y)) := by
    simpa [A] using contMDiff_traceFree_ricci_one (I := I) (M := M)
  have hA2 := contMDiff_endomorphism_sq A hA
  have ht := contMDiff_trace_endomorphism 1 _ hA2
  have hc : ContMDiff I 𝓘(ℝ, ℝ) 1
      (fun x ↦ hilbertSchmidtSq (A x)) := by
    rw [show (fun x ↦ hilbertSchmidtSq (A x)) =
      (fun x ↦ LinearMap.trace ℝ (TM x) ((A x).comp (A x)).toLinearMap) by
        funext x; exact hilbertSchmidtSq_traceFree_ricci_eq_trace_comp (I := I) x]
    exact ht
  simpa [A] using hc

theorem integrable_traceFreeRicciNormSq :
    Integrable (fun x ↦ hilbertSchmidtSq
      (traceFree (ricciRaisedEndomorphism LC x)))
      (riemannianVolume (I := I)) := by
  have hc := (contMDiff_traceFreeRicciNormSq_one (I := I) (M := M)).continuous
  exact hc.integrable_of_hasCompactSupport isClosed_closure.isCompact

theorem contMDiff_traceFreeHessianNormSq_one
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f)
    (hdim : Module.finrank ℝ E ≠ 0) :
    ContMDiff I 𝓘(ℝ, ℝ) 1 (traceFreeHessianNormSq LC f) := by
  have hH := contMDiff_hessianNormSq LC
    leviCivitaConnection_metricCompatible leviCivitaConnection_torsion hf
  have hL := contMDiff_laplacian LC hf
  have hsub : traceFreeHessianNormSq LC f = fun x ↦
      hessianNormSq LC f x - (laplacian LC f x) ^ 2 /
        (Module.finrank ℝ E : ℝ) := by
    funext x
    have hr := VectorBundle.finrank_eq ℝ E TM x
    simpa only [traceFreeHessianNormSq_eq, hr] using
      (traceFreeHessianNormSq_eq LC f x hdim)
  rw [hsub]
  exact hH.sub ((hL.pow 2).div_const _)

private theorem integrable_traceFreeHessianNormSq_of_C3
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 3 f)
    (hdim : Module.finrank ℝ E ≠ 0) :
    Integrable (traceFreeHessianNormSq LC f) (riemannianVolume (I := I)) := by
  have hc := (contMDiff_traceFreeHessianNormSq_one hf hdim).continuous
  exact hc.integrable_of_hasCompactSupport isClosed_closure.isCompact

theorem traceFree_pairing_cauchy
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 4 f)
    (hdim : Module.finrank ℝ E ≠ 0) :
    (∫ x, contractedBianchiPairingIntegrand (I := I) f x
      ∂riemannianVolume (I := I)) ^ 2 ≤
      (∫ x, hilbertSchmidtSq (traceFree (ricciRaisedEndomorphism LC x))
        ∂riemannianVolume (I := I)) *
      (∫ x, traceFreeHessianNormSq LC f x
        ∂riemannianVolume (I := I)) := by
  let μ := riemannianVolume (I := I) (M := M)
  let Bf : M → ℝ := fun x ↦ hilbertSchmidtSq
    (traceFree (ricciRaisedEndomorphism LC x))
  let Hf : M → ℝ := traceFreeHessianNormSq LC f
  let Pf : M → ℝ := contractedBianchiPairingIntegrand (I := I) f
  have hBint : Integrable Bf μ := by
    simpa [Bf, μ] using integrable_traceFreeRicciNormSq (I := I) (M := M)
  have hHint : Integrable Hf μ := by
    simpa [Hf, μ] using integrable_traceFreeHessianNormSq_of_C3
      (I := I) (M := M) (hf.of_le (by norm_num)) hdim
  have hPint : Integrable Pf μ := by
    simpa [Pf, μ] using integrable_contractedBianchiPairingIntegrand
      (I := I) (M := M) hf hdim
  have hBcont : Continuous Bf := by
    simpa [Bf] using
      (contMDiff_traceFreeRicciNormSq_one (I := I) (M := M)).continuous
  have hHcont : Continuous Hf := by
    simpa [Hf] using
      (contMDiff_traceFreeHessianNormSq_one (I := I) (M := M)
        (hf.of_le (by norm_num)) hdim).continuous
  have hBnonneg : ∀ x, 0 ≤ Bf x := by
    intro x
    exact hilbertSchmidtSq_nonneg _
  have hHnonneg : ∀ x, 0 ≤ Hf x := by
    intro x
    exact hilbertSchmidtSq_nonneg _
  let bfun : M → ℝ := fun x ↦ Real.sqrt (Bf x)
  let hfun : M → ℝ := fun x ↦ Real.sqrt (Hf x)
  have hb_sq : (fun x ↦ bfun x ^ 2) = Bf := by
    funext x
    exact Real.sq_sqrt (hBnonneg x)
  have hh_sq : (fun x ↦ hfun x ^ 2) = Hf := by
    funext x
    exact Real.sq_sqrt (hHnonneg x)
  have hbLp : MemLp bfun 2 μ := by
    apply (memLp_two_iff_integrable_sq (hBcont.sqrt.aestronglyMeasurable)).2
    rw [hb_sq]
    exact hBint
  have hhLp : MemLp hfun 2 μ := by
    apply (memLp_two_iff_integrable_sq (hHcont.sqrt.aestronglyMeasurable)).2
    rw [hh_sq]
    exact hHint
  have hprod : Integrable (fun x ↦ bfun x * hfun x) μ :=
    hbLp.integrable_mul hhLp
  have hpoint : ∀ x, |Pf x| ≤ bfun x * hfun x := by
    intro x
    apply abs_le_of_sq_le_sq
    · have hc := hilbertSchmidtInner_sq_le
        (traceFree (ricciRaisedEndomorphism LC x))
        (traceFree (LC (gradient (I := I) f) x))
      calc
        Pf x ^ 2 = hilbertSchmidtInner
            (traceFree (ricciRaisedEndomorphism LC x))
            (traceFree (LC (gradient (I := I) f) x)) ^ 2 := rfl
        _ ≤ hilbertSchmidtSq (traceFree (ricciRaisedEndomorphism LC x)) *
            hilbertSchmidtSq (traceFree (LC (gradient (I := I) f) x)) := hc
        _ = (bfun x * hfun x) ^ 2 := by
          change Bf x * Hf x = (Real.sqrt (Bf x) * Real.sqrt (Hf x)) ^ 2
          rw [mul_pow, Real.sq_sqrt (hBnonneg x), Real.sq_sqrt (hHnonneg x)]
    · exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have habs : |∫ x, Pf x ∂μ| ≤ ∫ x, bfun x * hfun x ∂μ := by
    calc
      |∫ x, Pf x ∂μ| ≤ ∫ x, |Pf x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, bfun x * hfun x ∂μ :=
        integral_mono_ae hPint.abs hprod (Filter.Eventually.of_forall hpoint)
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) (f := bfun) (g := hfun) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun x ↦ Real.sqrt_nonneg _))
    (Filter.Eventually.of_forall (fun x ↦ Real.sqrt_nonneg _))
    (by simpa using hbLp) (by simpa using hhLp)
  have hrootB : (∫ x, bfun x ^ (2 : ℝ) ∂μ) = ∫ x, Bf x ∂μ := by
    rw [show (fun x ↦ bfun x ^ (2 : ℝ)) = (fun x ↦ bfun x ^ 2) by
      funext x; exact Real.rpow_natCast _ _]
    exact congrArg (fun g ↦ ∫ x, g x ∂μ) hb_sq
  have hrootH : (∫ x, hfun x ^ (2 : ℝ) ∂μ) = ∫ x, Hf x ∂μ := by
    rw [show (fun x ↦ hfun x ^ (2 : ℝ)) = (fun x ↦ hfun x ^ 2) by
      funext x; exact Real.rpow_natCast _ _]
    exact congrArg (fun g ↦ ∫ x, g x ∂μ) hh_sq
  have hholder' : |∫ x, Pf x ∂μ| ≤
      (∫ x, Bf x ∂μ) ^ (1 / (2 : ℝ)) *
        (∫ x, Hf x ∂μ) ^ (1 / (2 : ℝ)) := by
    rw [hrootB, hrootH] at hholder
    exact habs.trans hholder
  have hBint_nonneg : 0 ≤ ∫ x, Bf x ∂μ := integral_nonneg hBnonneg
  have hHint_nonneg : 0 ≤ ∫ x, Hf x ∂μ := integral_nonneg hHnonneg
  have hsquareB : ((∫ x, Bf x ∂μ) ^ (1 / (2 : ℝ))) ^ 2 =
      ∫ x, Bf x ∂μ := by
    have h := (Real.rpow_mul hBint_nonneg (1 / (2 : ℝ)) (2 : ℝ)).symm
    norm_num at h
    simpa only [Real.rpow_natCast] using h
  have hsquareH : ((∫ x, Hf x ∂μ) ^ (1 / (2 : ℝ))) ^ 2 =
      ∫ x, Hf x ∂μ := by
    have h := (Real.rpow_mul hHint_nonneg (1 / (2 : ℝ)) (2 : ℝ)).symm
    norm_num at h
    simpa only [Real.rpow_natCast] using h
  have hRnonneg : 0 ≤
      (∫ x, Bf x ∂μ) ^ (1 / (2 : ℝ)) *
        (∫ x, Hf x ∂μ) ^ (1 / (2 : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg hBint_nonneg _)
      (Real.rpow_nonneg hHint_nonneg _)
  have hsq : (∫ x, Pf x ∂μ) ^ 2 ≤
      ((∫ x, Bf x ∂μ) ^ (1 / (2 : ℝ)) *
        (∫ x, Hf x ∂μ) ^ (1 / (2 : ℝ))) ^ 2 := by
    apply (sq_le_sq).2
    simpa only [abs_of_nonneg hRnonneg] using hholder'
  rw [mul_pow, hsquareB, hsquareH] at hsq
  simpa [Bf, Hf, Pf, μ] using hsq

theorem almostSchur_bound_of_classical_poisson
    (hRic : ∀ (x : M) (v : TM x),
      0 ≤ (leviCivitaConnection (I := I) (M := M)).ricciCurvatureAlmostSchur x v v)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 4 f) (r : ℝ)
    (hpoisson : ∀ x, laplacian (leviCivitaConnection (I := I) (M := M)) f x =
      (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x - r)
    (hd : 2 < (Module.finrank ℝ E : ℝ)) :
    (∫ x, ((leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x - r) ^ 2
      ∂riemannianVolume (I := I)) ≤
      (4 * (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) - 1) /
        ((Module.finrank ℝ E : ℝ) - 2) ^ 2) *
        (∫ x, hilbertSchmidtSq
          (traceFree (ricciRaisedEndomorphism LC x))
          ∂riemannianVolume (I := I)) := by
  have hdim : Module.finrank ℝ E ≠ 0 := by
    have hnat : 0 < Module.finrank ℝ E := by
      exact_mod_cast (show (0 : ℝ) < (Module.finrank ℝ E : ℝ) by linarith)
    exact Nat.ne_of_gt hnat
  let A : ℝ := ∫ x, ((leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x - r) ^ 2
    ∂riemannianVolume (I := I)
  let B : ℝ := ∫ x, hilbertSchmidtSq
    (traceFree (ricciRaisedEndomorphism (leviCivitaConnection (I := I) (M := M)) x))
    ∂riemannianVolume (I := I)
  let Henergy : ℝ := ∫ x, traceFreeHessianNormSq
    (leviCivitaConnection (I := I) (M := M)) f x
    ∂riemannianVolume (I := I)
  let Hess : ℝ := ∫ x, hessianNormSq
    (leviCivitaConnection (I := I) (M := M)) f x
    ∂riemannianVolume (I := I)
  let Ric : ℝ := ∫ x, (leviCivitaConnection (I := I) (M := M)).ricciCurvatureAlmostSchur x
    (gradient (I := I) f x) (gradient (I := I) f x)
    ∂riemannianVolume (I := I)
  let P : ℝ := ∫ x, contractedBianchiPairingIntegrand (I := I) f x
    ∂riemannianVolume (I := I)
  have hA : 0 ≤ A := by
    exact integral_nonneg (fun x ↦ sq_nonneg _)
  have hB : 0 ≤ B := by
    exact integral_nonneg (fun x ↦ hilbertSchmidtSq_nonneg _)
  have hcontracted : ((Module.finrank ℝ E : ℝ) - 2) * A =
      2 * (Module.finrank ℝ E : ℝ) * P := by
    simpa [A, P] using contractedBianchi_pairing_of_poisson
      (I := I) (M := M) hf r hpoisson hdim
  have hcauchy : P ^ 2 ≤ B * Henergy := by
    simpa [B, Henergy, P] using traceFree_pairing_cauchy
      (I := I) (M := M) hf hdim
  have hbochner0 := leviCivita_integratedBundledRicciBochner
    (I := I) (M := M) (f := f) (hf.of_le (by norm_num))
  have hbochner : Hess + Ric = A := by
    have hlap : (∫ x, (laplacian
        (leviCivitaConnection (I := I) (M := M)) f x) ^ 2
        ∂riemannianVolume (I := I)) = A := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hpoisson x]
    simpa [Hess, Ric, A] using hbochner0.trans hlap
  have hRic : 0 ≤ Ric := by
    exact integral_ricciGradient_nonneg (I := I) (M := M) hRic f
  have htrace : (Module.finrank ℝ E : ℝ) * Henergy =
      (Module.finrank ℝ E : ℝ) * Hess - A := by
    simpa [Henergy, Hess, A] using poisson_traceFreeHessian_identity
      (I := I) (M := M) hf r hpoisson hdim
  have hfinal := almostSchur_from_identities (d := (Module.finrank ℝ E : ℝ))
    (A := A) (B := B) (Hess := Hess) (Ric := Ric) (H := Henergy) (P := P)
    hd hA hB hRic hcontracted hcauchy hbochner htrace
  simpa [A, B] using hfinal

theorem almostSchur_bound_of_smooth_meanZero_poisson
    (hRic : ∀ (x : M) (v : TM x),
      0 ≤ (leviCivitaConnection (I := I) (M := M)).ricciCurvatureAlmostSchur x v v)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (_hmean : (∫ x, f x ∂riemannianVolume (I := I)) = 0) (r : ℝ)
    (hpoisson : ∀ x, laplacian (leviCivitaConnection (I := I) (M := M)) f x =
      (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x - r)
    (hd : 2 < (Module.finrank ℝ E : ℝ)) :
    (∫ x, ((leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x - r) ^ 2
      ∂riemannianVolume (I := I)) ≤
      (4 * (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) - 1) /
        ((Module.finrank ℝ E : ℝ) - 2) ^ 2) *
        (∫ x, hilbertSchmidtSq
          (traceFree (ricciRaisedEndomorphism LC x))
          ∂riemannianVolume (I := I)) :=
  almostSchur_bound_of_classical_poisson hRic
    (hf.of_le (by
      exact WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))) r
    hpoisson hd

noncomputable def centeredScalarCurvature : M → ℝ :=
  fun x ↦ (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x -
    riemannianMean (I := I)
      (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur

theorem memLp_centeredScalarCurvature :
    MemLp (centeredScalarCurvature (I := I) (M := M)) 2
      (riemannianVolume (I := I) (M := M)) := by
  have hS : ContMDiff I 𝓘(ℝ, ℝ) 1
      (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur :=
    fun x ↦ contMDiffAt_scalarCurvature_one
      (leviCivitaConnection (I := I) (M := M))
      leviCivitaConnection_metricCompatible leviCivitaConnection_torsion x
  have hc : Continuous (centeredScalarCurvature (I := I) (M := M)) :=
    (hS.continuous.sub continuous_const)
  exact hc.memLp_of_hasCompactSupport isClosed_closure.isCompact

theorem almostSchur_bound_of_local_smooth_representatives
    {ι : Type*} [Countable ι]
    (hRic : ∀ (x : M) (v : TM x),
      0 ≤ (leviCivitaConnection (I := I) (M := M)).ricciCurvatureAlmostSchur x v v)
    (U : ι → Set M) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (q : ι → M → ℝ)
    (hq : ∀ i, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (q i) (U i))
    (hqa : ∀ i, q i =ᵐ[(riemannianVolume (I := I)).restrict (U i)]
      energyCompletionToL2 (weakPoissonSolution
        (MemLp.toLp (centeredScalarCurvature (I := I) (M := M))
          (memLp_centeredScalarCurvature (I := I) (M := M))))) :
    2 < (Module.finrank ℝ E : ℝ) →
    (∫ x, ((leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x -
      riemannianMean (I := I)
        (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur) ^ 2
      ∂riemannianVolume (I := I)) ≤
      (4 * (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) - 1) /
        ((Module.finrank ℝ E : ℝ) - 2) ^ 2) *
        (∫ x, hilbertSchmidtSq
          (traceFree (ricciRaisedEndomorphism LC x))
          ∂riemannianVolume (I := I)) := by
  intro hd
  let S : M → ℝ := (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur
  let r : ℝ := riemannianMean (I := I) S
  let F : M → ℝ := fun x ↦ S x - r
  have hS : ContMDiff I 𝓘(ℝ, ℝ) 1 S := by
    intro x
    simpa [S] using (contMDiffAt_scalarCurvature_one LC
      leviCivitaConnection_metricCompatible leviCivitaConnection_torsion x)
  have hF : Continuous F := by
    exact (hS.continuous.sub continuous_const)
  have hmem : MemLp F 2 (riemannianVolume (I := I)) :=
    hF.memLp_of_hasCompactSupport isClosed_closure.isCompact
  let h : Lp ℝ 2 (riemannianVolume (I := I)) := MemLp.toLp F hmem
  have hh : (∫ x, h x ∂riemannianVolume (I := I)) = 0 := by
    rw [integral_congr_ae hmem.coeFn_toLp]
    exact integral_sub_riemannianMean S hS
  have hFh : F =ᵐ[riemannianVolume (I := I)] h := hmem.coeFn_toLp.symm
  have hqa' : ∀ i, q i =ᵐ[(riemannianVolume (I := I)).restrict (U i)]
      energyCompletionToL2 (weakPoissonSolution h) := by
    intro i
    have hsame : h =
        MemLp.toLp (centeredScalarCurvature (I := I) (M := M))
          (memLp_centeredScalarCurvature (I := I) (M := M)) := by
      change MemLp.toLp F hmem = _
      exact MemLp.toLp_congr hmem
        (memLp_centeredScalarCurvature (I := I) (M := M)) (by
          filter_upwards [] with x
          rfl)
    rw [hsame]
    exact hqa i
  obtain ⟨g, hg, _, _, hlap⟩ := exists_classical_weakPoisson_of_local_representatives
    (I := I) (M := M) LC leviCivitaConnection_metricCompatible
    leviCivitaConnection_torsion h hh F hF hFh U hU hcover q hq hqa'
  have hSg : ContMDiff I 𝓘(ℝ, ℝ) 4 g := hg.of_le (by
    exact WithTop.coe_le_coe.mpr
      (show (4 : ENat) ≤ (⊤ : ENat) from le_top))
  have hlap' : ∀ x, laplacian LC g x =
      (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x - r := by
    intro x
    simpa [S, r, F] using congrFun hlap x
  simpa [S, r, F] using almostSchur_bound_of_classical_poisson
    (I := I) (M := M) hRic hSg r hlap' hd

end AlmostSchur
