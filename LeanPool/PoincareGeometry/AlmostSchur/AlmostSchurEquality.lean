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

public import LeanPool.PoincareGeometry.AlmostSchur.AlmostSchurFinal
import LeanPool.PoincareGeometry.AlmostSchur.AlmostSchurAlgebra
import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

/-! # Almost Schur Equality -/

@[expose] public noncomputable section
open Bundle FiberBundle Set MeasureTheory Filter Metric
open scoped Manifold ContDiff Topology BigOperators

namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M]
  [Nonempty M] [LindelofSpace M] [T2Space M] [CompactSpace M]
  [PreconnectedSpace M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "LC" => leviCivitaConnection (I := I) (M := M)

local instance testMeasurableSpaceE : MeasurableSpace E := borel E
local instance testBorelSpaceE : BorelSpace E := ⟨rfl⟩
local instance testOpensMeasurableSpaceE : OpensMeasurableSpace E := by infer_instance
local instance testMeasurableAddE : MeasurableAdd E := by infer_instance
local instance testMetricZero : IsContMDiffRiemannianBundle I (↑(0 : ℕ)) E TM :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)
local instance testContinuousMetric : IsContinuousRiemannianBundle E TM :=
  continuousRiemannianBundle_of_contMDiff (I := I)
local instance testMetricTwo : IsContMDiffRiemannianBundle I (↑(2 : ℕ)) E TM :=
  IsContMDiffRiemannianBundle.of_le (n := ∞) (by
    exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
local instance testMetricThree : IsContMDiffRiemannianBundle I (↑(3 : ℕ)) E TM :=
  IsContMDiffRiemannianBundle.of_le (n := ∞) (by
    exact WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))
local instance testFiberFiniteDimensional (x : M) : FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x
local instance testFiniteMeasure : IsFiniteMeasure (riemannianVolume (I := I) (M := M)) :=
  ⟨(riemannianVolume_finite_positive (I := I)).2⟩
local instance testOpenPosMeasure :
    (riemannianVolume (I := I) (M := M)).IsOpenPosMeasure :=
  ⟨fun _ hs hne => ne_of_gt (riemannianVolume_open_pos (I := I) hs hne)⟩

theorem test_hasDerivAt_comp_local_curve
    {q : M → ℝ} {v : Π x : M, TM x} {γ : ℝ → M} {t : ℝ}
    (hq : ContMDiffAt I 𝓘(ℝ, ℝ) 1 q (γ t))
    (hγ : IsMIntegralCurveAt γ v t) :
    HasDerivAt (q ∘ γ) (mvfderiv I q (γ t) (v (γ t))) t := by
  have hcomp := hq.mdifferentiableAt (by norm_num) |>.hasMFDerivAt.comp t
    hγ.hasMFDerivAt
  have hcomp' := hasMFDerivAt_iff_hasFDerivAt.mp hcomp
  let R : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) t :=
    ContinuousLinearMap.mk
      { toFun := fun y => y
        map_add' := by intro y z; rfl
        map_smul' := by intro a y; rfl }
      continuous_id
  let L : TangentSpace 𝓘(ℝ, ℝ) (q (γ t)) →L[ℝ] ℝ :=
    ContinuousLinearMap.mk
      { toFun := fun y => y
        map_add' := by intro y z; rfl
        map_smul' := by intro a y; rfl }
      continuous_id
  have hsource := hcomp'.comp t (ContinuousLinearMap.hasFDerivAt R)
  have hdT := (ContinuousLinearMap.hasFDerivAt L).comp t hsource
  have hder := hdT.hasDerivAt
  have hder' : HasDerivAt (q ∘ γ)
      ((L.comp (mfderiv% q (γ t) ∘SL
        ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          ((fun x => v x) (γ t))) ∘ R) 1) t :=
    hder.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun s => by
        change q (γ s) = L (q (γ (R s)))
        rfl))
  have heq :
      (NormedSpace.fromTangentSpace (q (γ t)))
          ((mfderiv% q (γ t) ∘SL
            ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
              (v (γ t))) 1) =
        mvfderiv I q (γ t) (v (γ t)) := by
    simp [mvfderiv, NormedSpace.fromTangentSpace]
  exact hder'.congr_deriv (by
    simp [L, R]
    exact heq)

theorem test_hasDerivAt_gradient_norm_sq
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    {γ : ℝ → M} {t : ℝ}
    (hγ : IsMIntegralCurveAt γ (fun x => -gradient (I := I) f x) t) :
    HasDerivAt ((fun x => inner ℝ (gradient (I := I) f x)
      (gradient (I := I) f x)) ∘ γ)
      (mvfderiv I (fun x => inner ℝ (gradient (I := I) f x)
        (gradient (I := I) f x)) (γ t)
        ((fun x => -gradient (I := I) f x) (γ t))) t := by
  have hgrad : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (T% (gradient (I := I) f)) :=
    contMDiff_gradient 1 hf
  have hinner : ContMDiffAt I 𝓘(ℝ, ℝ)
      1 (fun x => inner ℝ (gradient (I := I) f x)
        (gradient (I := I) f x)) (γ t) :=
    @ContMDiffAt.inner_bundle E _ _ H _ I (1 : ℕ∞ω) M _ _ E _ _ TM _
      (fun y => inferInstance) (fun y => inferInstance) _ _ E _ _ H _ I M _ _ _
      (fun y => y) (gradient (I := I) f) (gradient (I := I) f) (γ t)
      (hgrad (γ t)) (hgrad (γ t))
  exact test_hasDerivAt_comp_local_curve
    (q := fun x => inner ℝ (gradient (I := I) f x)
      (gradient (I := I) f x))
    (v := fun x => -gradient (I := I) f x) (γ := γ) (t := t)
    hinner hγ

theorem test_integral_zero_continuous {f : M → ℝ}
    (hf : Continuous f) (hnonneg : ∀ x, 0 ≤ f x)
    (hfi : Integrable f (riemannianVolume (I := I) (M := M)))
    (hzero : (∫ x, f x ∂riemannianVolume (I := I)) = 0) :
    ∀ x, f x = 0 := by
  have hae := (integral_eq_zero_iff_of_nonneg hnonneg hfi).mp hzero
  have heq := MeasureTheory.Measure.eq_of_ae_eq hae hf continuous_const
  intro x
  exact congrFun heq x

theorem test_hessianRaised_eq_covariantDerivative_gradient
    {f : M → ℝ} (x : M) :
    hessianRaisedEndomorphism (I := I) f x =
      (LC (gradient (I := I) f) x) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [inner_hessianRaisedEndomorphism, hessian_apply]

theorem test_contMDiff_traceFreeHessianRaised_one
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y
        (traceFree (hessianRaisedEndomorphism (I := I) f y))) := by
  let A : Π y, TM y →L[ℝ] TM y := fun y ↦ hessianRaisedEndomorphism (I := I) f y
  have hgrad : ContMDiff I (I.prod 𝓘(ℝ, E)) 3
      (T% (gradient (I := I) f)) :=
    contMDiff_gradient 3 (hf.of_le (by
      exact WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top)))
  have hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (A y)) := by
    intro x
    have hA' := contMDiffAt_covariantDerivative_of_metric_torsion_two LC
      leviCivitaConnection_metricCompatible leviCivitaConnection_torsion
      (hgrad x)
    apply hA'.congr_of_eventuallyEq
    filter_upwards [] with y
    congr 1
    exact test_hessianRaised_eq_covariantDerivative_gradient
      (I := I) (M := M) (f := f) y
  intro x
  apply contMDiffAt_traceFree_endomorphism_one (I := I) (M := M) A
    (hA.of_le (by norm_num)) x

theorem test_hessianRaised_isSelfAdjoint
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (x : M) :
    IsSelfAdjoint (hessianRaisedEndomorphism (I := I) f x) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  calc
    inner ℝ (hessianRaisedEndomorphism (I := I) f x u) v =
        hessian LC f x u v := inner_hessianRaisedEndomorphism f x u v
    _ = hessian LC f x v u := hessian_symmetric LC
      leviCivitaConnection_metricCompatible leviCivitaConnection_torsion
      hf x u v
    _ = inner ℝ (hessianRaisedEndomorphism (I := I) f x v) u :=
      (inner_hessianRaisedEndomorphism f x v u).symm
    _ = inner ℝ u (hessianRaisedEndomorphism (I := I) f x v) :=
      real_inner_comm _ _

theorem test_traceFree_hessian_isSelfAdjoint
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (x : M) :
    IsSelfAdjoint (traceFree (hessianRaisedEndomorphism (I := I) f x)) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  change star (hessianRaisedEndomorphism (I := I) f x -
    ((LinearMap.trace ℝ (TM x))
      (hessianRaisedEndomorphism (I := I) f x).toLinearMap /
      (Module.finrank ℝ (TM x) : ℝ)) •
      ContinuousLinearMap.id ℝ (TM x)) = _
  rw [star_sub, StarModule.star_smul]
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_id,
    TrivialStar.star_trivial]
  rw [ContinuousLinearMap.isSelfAdjoint_iff'.mp
    (test_hessianRaised_isSelfAdjoint (I := I) (M := M) hf x)]
  rfl

theorem test_hilbertSchmidtSq_selfAdjoint_eq_trace_comp
    {x : M} (A : TM x →L[ℝ] TM x) (hA : IsSelfAdjoint A) :
    hilbertSchmidtSq A =
      LinearMap.trace ℝ (TM x) (A.comp A).toLinearMap := by
  unfold hilbertSchmidtSq
  rw [ContinuousLinearMap.isSelfAdjoint_iff'.mp hA]

theorem test_contMDiff_hilbertSchmidtSq_selfAdjoint
    (A : Π y, TM y →L[ℝ] TM y)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (A y)))
    (hself : ∀ y, IsSelfAdjoint (A y)) :
    ContMDiff I 𝓘(ℝ, ℝ) 1 (fun y ↦ hilbertSchmidtSq (A y)) := by
  have hA2 := contMDiff_endomorphism_sq A hA
  have ht := contMDiff_trace_endomorphism 1 _ hA2
  rw [show (fun y ↦ hilbertSchmidtSq (A y)) =
      (fun y ↦ LinearMap.trace ℝ (TM y) ((A y).comp (A y)).toLinearMap) by
        funext y
        exact test_hilbertSchmidtSq_selfAdjoint_eq_trace_comp (A y) (hself y)]
  exact ht

theorem test_scalarCurvature_nonneg
    (hRic : ∀ (x : M) (v : TM x),
      0 ≤ (leviCivitaConnection (I := I) (M := M)).ricciCurvatureAlmostSchur x v v) :
    ∀ x, 0 ≤ (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x := by
  intro x
  rw [CovariantDerivative.scalarCurvature_eq_sumAlmostSchur]
  exact Finset.sum_nonneg (fun i _ => hRic x
    ((stdOrthonormalBasis ℝ (TM x)) i))

theorem test_hessian_contraction
    {f : M → ℝ} (r μ : ℝ)
    (hpoisson : ∀ x, laplacian LC f x =
      (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x - r)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (hμ : (Module.finrank ℝ E : ℝ) - 2 ≠ 0)
    (hμval : μ = 2 * ((Module.finrank ℝ E : ℝ) - 1) /
      ((Module.finrank ℝ E : ℝ) - 2))
    (hT : ∀ x, traceFree (hessianRaisedEndomorphism (I := I) f x) =
      μ • traceFree (ricciRaisedEndomorphism LC x))
    (hRiczero : ∀ x, (leviCivitaConnection (I := I) (M := M)).ricciCurvatureAlmostSchur x
      (gradient (I := I) f x) (gradient (I := I) f x) = 0) :
    ∀ x, hessian LC f x (gradient (I := I) f x)
        (gradient (I := I) f x) =
      (-r / (Module.finrank ℝ E : ℝ) -
        (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x /
          ((Module.finrank ℝ E : ℝ) - 2)) *
        ‖gradient (I := I) f x‖ ^ 2 := by
  have hd : (Module.finrank ℝ E : ℝ) ≠ 0 := by
    linarith
  intro x
  let u := gradient (I := I) f x
  have hi := congrArg (fun A : TM x →L[ℝ] TM x => inner ℝ (A u) u)
    (hT x)
  simp only [traceFree, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
    inner_sub_left, real_inner_smul_left] at hi
  have htraceH : LinearMap.trace ℝ (TM x)
      (hessianRaisedEndomorphism (I := I) f x).toLinearMap =
      laplacian LC f x := trace_hessianRaisedEndomorphism f x
  rw [inner_hessianRaisedEndomorphism, inner_ricciRaisedEndomorphism,
    htraceH, hpoisson x,
    (scalarCurvature_eq_trace_ricciRaisedEndomorphism LC x).symm,
    real_inner_self_eq_norm_sq, hRiczero x] at hi
  rw [VectorBundle.finrank_eq ℝ E TM x] at hi
  rw [hμval] at hi
  field_simp [hd, hμ] at hi ⊢
  nlinarith [hi]

theorem test_mvfderiv_gradient_norm_sq_neg
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (x : M) :
    mvfderiv I (fun y ↦ inner ℝ (gradient (I := I) f y)
      (gradient (I := I) f y)) x
      (-gradient (I := I) f x) =
      -2 * hessian LC f x (gradient (I := I) f x)
        (gradient (I := I) f x) := by
  have hgrad : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (T% (gradient (I := I) f)) :=
    contMDiff_gradient 1 hf
  have hG : MDiffAt (T% (gradient (I := I) f)) x :=
    (hgrad x).mdifferentiableAt (by norm_num)
  have hm := CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq
    leviCivitaConnection_metricCompatible (fun y ↦ -gradient (I := I) f y)
    hG hG
  change mvfderiv I (fun y ↦ inner ℝ (gradient (I := I) f y)
      (gradient (I := I) f y)) x (-gradient (I := I) f x) = _ at hm
  rw [hessian_apply]
  rw [map_neg]
  simp only [map_neg, inner_neg_left, inner_neg_right, neg_add, neg_neg] at hm
  have hcomm : inner ℝ (gradient (I := I) f x)
      ((LC (gradient (I := I) f) x) (gradient (I := I) f x)) =
      inner ℝ ((LC (gradient (I := I) f) x) (gradient (I := I) f x))
        (gradient (I := I) f x) := real_inner_comm _ _
  linarith [hm, hcomm]

private theorem gradientNormSq_contMDiff_one {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 4 f) :
    ContMDiff I 𝓘(ℝ, ℝ) 1
      (fun x ↦ inner ℝ (gradient (I := I) f x) (gradient (I := I) f x)) := by
  have hgrad1 : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% (gradient (I := I) f)) :=
    contMDiff_gradient 1 (hf.of_le (by norm_num))
  exact @ContMDiff.inner_bundle E _ _ H _ I (1 : ℕ∞ω) M _ _ E _ _ TM _
    (fun y ↦ inferInstance) (fun y ↦ inferInstance) _ _ E _ _ H _ I M _ _ _
    (fun y ↦ y) (gradient (I := I) f) (gradient (I := I) f) hgrad1 hgrad1

private theorem gradient_eq_zero_of_hessian_contraction
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 4 f) (r : ℝ) (hr_pos : 0 < r)
    (hdim : 2 < (Module.finrank ℝ E : ℝ)) (S : M → ℝ) (hSnonneg : ∀ x, 0 ≤ S x)
    (hcontract : ∀ x, hessian LC f x (gradient (I := I) f x)
        (gradient (I := I) f x) =
      (-r / (Module.finrank ℝ E : ℝ) - S x /
        ((Module.finrank ℝ E : ℝ) - 2)) * ‖gradient (I := I) f x‖ ^ 2) :
    ∀ x, gradient (I := I) f x = 0 := by
  let F : M → ℝ := fun x ↦ inner ℝ
    (gradient (I := I) f x) (gradient (I := I) f x)
  have hgrad1 : ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% (gradient (I := I) f)) :=
    contMDiff_gradient 1 (hf.of_le (by norm_num))
  have hFmd := gradientNormSq_contMDiff_one (I := I) hf
  have hFcont : Continuous F := by
    simpa [F] using hFmd.continuous
  have hFnonneg : ∀ x, 0 ≤ F x := by
    intro x
    simpa [F, real_inner_self_eq_norm_sq] using
      sq_nonneg ‖gradient (I := I) f x‖
  obtain ⟨xmax, hxmax, hmax⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).exists_isMaxOn
      Set.univ_nonempty hFcont.continuousOn
  have hFzero : F xmax = 0 := by
    by_contra hne
    have hFpos : 0 < F xmax :=
      lt_of_le_of_ne (hFnonneg xmax) (Ne.symm hne)
    have hv : CMDiffAt 1
        (fun x ↦ (⟨x, (-gradient (I := I) f x)⟩ : TangentBundle I M)) xmax := by
      exact (hgrad1 xmax).neg_section
    obtain ⟨γ, hγ0, hγ⟩ :=
      exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
        (I := I) (M := M) (t₀ := (0 : ℝ)) (x₀ := xmax)
        (v := fun x ↦ -gradient (I := I) f x) hv
    have hFlocal : IsLocalMax F xmax := hmax.isLocalMax (by simp)
    have hFlocal' : IsLocalMax F (γ 0) := by simpa [hγ0] using hFlocal
    have hGlocal : IsLocalMax (F ∘ γ) 0 :=
      hFlocal'.comp_continuous hγ.continuousAt
    have hder := test_hasDerivAt_gradient_norm_sq
      (I := I) (M := M) (f := f) (hf.of_le (by norm_num)) hγ
    rw [hγ0, test_mvfderiv_gradient_norm_sq_neg
      (I := I) (M := M) (f := f) (hf.of_le (by norm_num)) xmax] at hder
    have hder' : HasDerivAt (F ∘ γ) (-2 * hessian LC f xmax
        (gradient (I := I) f xmax) (gradient (I := I) f xmax)) 0 := by
      simpa [F] using hder
    have hzero := hGlocal.hasDerivAt_eq_zero hder'
    have hdpos : 0 < (Module.finrank ℝ E : ℝ) := by
      linarith
    have hdminus2pos : 0 < (Module.finrank ℝ E : ℝ) - 2 := by
      linarith
    have hcoef : -r / (Module.finrank ℝ E : ℝ) -
        S xmax / ((Module.finrank ℝ E : ℝ) - 2) < 0 := by
      have hfirst : 0 < r / (Module.finrank ℝ E : ℝ) :=
        div_pos hr_pos hdpos
      have hsecond : 0 ≤ S xmax /
          ((Module.finrank ℝ E : ℝ) - 2) :=
        div_nonneg (hSnonneg xmax) (le_of_lt hdminus2pos)
      calc
        -r / (Module.finrank ℝ E : ℝ) -
            S xmax / ((Module.finrank ℝ E : ℝ) - 2) =
            -(r / (Module.finrank ℝ E : ℝ)) -
              S xmax / ((Module.finrank ℝ E : ℝ) - 2) := by ring
        _ < 0 := by linarith
    have hF_norm : ‖gradient (I := I) f xmax‖ ^ 2 = F xmax := by
      simp [F, real_inner_self_eq_norm_sq]
    rw [hcontract xmax] at hzero
    rw [hF_norm] at hzero
    have hprod : (-r / (Module.finrank ℝ E : ℝ) -
        S xmax / ((Module.finrank ℝ E : ℝ) - 2)) * F xmax = 0 := by
      nlinarith [hzero]
    have hprodneg : (-r / (Module.finrank ℝ E : ℝ) -
        S xmax / ((Module.finrank ℝ E : ℝ) - 2)) * F xmax < 0 :=
      mul_neg_of_neg_of_pos hcoef hFpos
    exact (ne_of_lt hprodneg) hprod
  have hFall : ∀ x, F x = 0 := by
    intro x
    have hxle : F x ≤ F xmax := (isMaxOn_iff.mp hmax) x (mem_univ x)
    have hxle0 : F x ≤ 0 := by simpa [hFzero] using hxle
    exact le_antisymm hxle0 (hFnonneg x)
  have hgradzero : ∀ x, gradient (I := I) f x = 0 := by
    intro x
    have hnormsq : ‖gradient (I := I) f x‖ ^ 2 = 0 := by
      simpa [F, real_inner_self_eq_norm_sq] using hFall x
    have hnorm : ‖gradient (I := I) f x‖ = 0 := by
      nlinarith [norm_nonneg (gradient (I := I) f x)]
    exact norm_eq_zero.mp hnorm
  exact hgradzero

private theorem equality_traceFreeHessian_proportional
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 4 f) (r : ℝ)
    (hdim : 2 < (Module.finrank ℝ E : ℝ)) (hdim0 : Module.finrank ℝ E ≠ 0)
    (hH : (Module.finrank ℝ E : ℝ) * (∫ x, traceFreeHessianNormSq LC f x ∂riemannianVolume (I := I)) = ((Module.finrank ℝ E : ℝ) - 1) * (∫ x, ((LC).scalarCurvatureAlmostSchur x - r) ^ 2 ∂riemannianVolume (I := I)))
    (hscale : ((Module.finrank ℝ E : ℝ) - 2) * (∫ x, contractedBianchiPairingIntegrand (I := I) f x
      ∂riemannianVolume (I := I)) = 2 * ((Module.finrank ℝ E : ℝ) - 1) * (∫ x, hilbertSchmidtSq (traceFree (ricciRaisedEndomorphism LC x))
      ∂riemannianVolume (I := I)))
    (heq : (∫ x, ((LC).scalarCurvatureAlmostSchur x - r) ^ 2 ∂riemannianVolume (I := I)) = (4 * (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) /
      ((Module.finrank ℝ E : ℝ) - 2) ^ 2) * (∫ x, hilbertSchmidtSq (traceFree (ricciRaisedEndomorphism LC x))
      ∂riemannianVolume (I := I))) :
    ∀ x, traceFree (LC (gradient (I := I) f) x) =
      (2 * ((Module.finrank ℝ E : ℝ) - 1) / ((Module.finrank ℝ E : ℝ) - 2)) •
        traceFree (ricciRaisedEndomorphism LC x) := by
  let A : ℝ := (∫ x, ((LC).scalarCurvatureAlmostSchur x - r) ^ 2 ∂riemannianVolume (I := I))
  let B : ℝ := (∫ x, hilbertSchmidtSq (traceFree (ricciRaisedEndomorphism LC x))
      ∂riemannianVolume (I := I))
  let Henergy : ℝ := (∫ x, traceFreeHessianNormSq LC f x ∂riemannianVolume (I := I))
  let P : ℝ := (∫ x, contractedBianchiPairingIntegrand (I := I) f x
      ∂riemannianVolume (I := I))
  change (Module.finrank ℝ E : ℝ) * Henergy = ((Module.finrank ℝ E : ℝ) - 1) * A at hH
  change ((Module.finrank ℝ E : ℝ) - 2) * P = 2 * ((Module.finrank ℝ E : ℝ) - 1) * B at hscale
  let μ : ℝ := 2 * ((Module.finrank ℝ E : ℝ) - 1) /
    ((Module.finrank ℝ E : ℝ) - 2)
  let R : ∀ x, TM x →L[ℝ] TM x := fun x ↦
    traceFree (ricciRaisedEndomorphism LC x)
  let T : ∀ x, TM x →L[ℝ] TM x := fun x ↦
    traceFree (LC (gradient (I := I) f) x)
  let D : M → ℝ := fun x ↦ hilbertSchmidtSq (T x - μ • R x)
  have hRsec : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (R y)) := by
    simpa [R] using contMDiff_traceFree_ricci_one
      (I := I) (M := M)
  have hgrad3 : ContMDiff I (I.prod 𝓘(ℝ, E)) 3
      (T% (gradient (I := I) f)) :=
    contMDiff_gradient 3 (hf.of_le (by norm_num))
  have hTraw : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y
        (LC (gradient (I := I) f) y)) := by
    intro x
    exact contMDiffAt_covariantDerivative_of_metric_torsion_two LC
      leviCivitaConnection_metricCompatible leviCivitaConnection_torsion
      (hgrad3 x)
  have hTsec : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (T y)) := by
    have h := contMDiffAt_traceFree_endomorphism_one
      (I := I) (M := M)
      (fun y ↦ LC (gradient (I := I) f) y) (hTraw.of_le (by norm_num))
    intro x
    simpa [T] using h x
  have hRself : ∀ x, IsSelfAdjoint (R x) := by
    intro x
    simpa [R] using traceFree_ricci_isSelfAdjoint (I := I) (M := M) x
  have hTself : ∀ x, IsSelfAdjoint (T x) := by
    intro x
    have h := test_traceFree_hessian_isSelfAdjoint
      (I := I) (M := M) (f := f) (hf.of_le (by norm_num)) x
    change IsSelfAdjoint (traceFree (LC (gradient (I := I) f) x))
    rw [← test_hessianRaised_eq_covariantDerivative_gradient
      (I := I) (M := M) (f := f) x]
    exact h
  have hμRsec : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (μ • R y)) := by
    have hc : ContMDiff I 𝓘(ℝ, ℝ) 1 (fun _ : M ↦ μ) := contMDiff_const
    simpa using hc.smul_section hRsec
  have hDsec : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (T y - μ • R y)) :=
    hTsec.sub_section hμRsec
  have hDself : ∀ x, IsSelfAdjoint (T x - μ • R x) := by
    intro x
    exact (hTself x).sub ((IsSelfAdjoint.all μ).smul (hRself x))
  have hDcont : Continuous D := by
    have h := test_contMDiff_hilbertSchmidtSq_selfAdjoint
      (I := I) (M := M) (fun y ↦ T y - μ • R y) hDsec hDself
    simpa [D] using h.continuous
  have hDnonneg : ∀ x, 0 ≤ D x := by
    intro x
    exact hilbertSchmidtSq_nonneg _
  have hT_eq : (fun x ↦ hilbertSchmidtSq (T x)) =
      traceFreeHessianNormSq LC f := by
    funext x
    simp [T, traceFreeHessianNormSq]
  have hR_eq : (fun x ↦ hilbertSchmidtSq (R x)) =
      (fun x ↦ hilbertSchmidtSq
        (traceFree (ricciRaisedEndomorphism LC x))) := by
    rfl
  have hP_eq : (fun x ↦ hilbertSchmidtInner (R x) (T x)) =
      contractedBianchiPairingIntegrand (I := I) f := by
    funext x
    rfl
  have hTint : Integrable (fun x ↦ hilbertSchmidtSq (T x))
      (riemannianVolume (I := I)) := by
    rw [hT_eq]
    exact integrable_traceFreeHessianNormSq
      (I := I) (M := M) LC leviCivitaConnection_metricCompatible
      leviCivitaConnection_torsion (hf.of_le (by norm_num)) hdim0
  have hRint : Integrable (fun x ↦ hilbertSchmidtSq (R x))
      (riemannianVolume (I := I)) := by
    rw [hR_eq]
    exact integrable_traceFreeRicciNormSq (I := I) (M := M)
  have hPint : Integrable (fun x ↦ hilbertSchmidtInner (R x) (T x))
      (riemannianVolume (I := I)) := by
    rw [hP_eq]
    exact integrable_contractedBianchiPairingIntegrand
      (I := I) (M := M) (hf.of_le (by norm_num)) hdim0
  have hD_eq : D = fun x ↦ hilbertSchmidtSq (T x) -
      2 * μ * hilbertSchmidtInner (R x) (T x) +
      μ ^ 2 * hilbertSchmidtSq (R x) := by
    funext x
    simpa [D] using hilbertSchmidtSq_sub_smul (T x) (R x) μ
  have hDint : Integrable D (riemannianVolume (I := I)) := by
    rw [hD_eq]
    exact (hTint.sub (hPint.const_mul (2 * μ))).add
      (hRint.const_mul (μ ^ 2))
  have hDzero : (∫ x, D x ∂riemannianVolume (I := I)) = 0 := by
    have hformula : (∫ x, D x ∂riemannianVolume (I := I)) =
        Henergy - 2 * μ * P + μ ^ 2 * B := by
      rw [hD_eq]
      change (∫ x, (hilbertSchmidtSq (T x) -
        2 * μ * hilbertSchmidtInner (R x) (T x) +
        μ ^ 2 * hilbertSchmidtSq (R x))
        ∂riemannianVolume (I := I)) = _
      calc
        (∫ x, (hilbertSchmidtSq (T x) -
            2 * μ * hilbertSchmidtInner (R x) (T x) +
            μ ^ 2 * hilbertSchmidtSq (R x))
            ∂riemannianVolume (I := I)) =
            (∫ x, hilbertSchmidtSq (T x) -
              2 * μ * hilbertSchmidtInner (R x) (T x)
              ∂riemannianVolume (I := I)) +
            (∫ x, μ ^ 2 * hilbertSchmidtSq (R x)
              ∂riemannianVolume (I := I)) := by
          exact integral_add (hTint.sub (hPint.const_mul (2 * μ)))
            (hRint.const_mul (μ ^ 2))
        _ = ((∫ x, hilbertSchmidtSq (T x)
              ∂riemannianVolume (I := I)) -
            (∫ x, 2 * μ * hilbertSchmidtInner (R x) (T x)
              ∂riemannianVolume (I := I))) +
            (∫ x, μ ^ 2 * hilbertSchmidtSq (R x)
              ∂riemannianVolume (I := I)) := by
          rw [integral_sub hTint (hPint.const_mul (2 * μ))]
        _ = Henergy - 2 * μ * P + μ ^ 2 * B := by
          rw [integral_const_mul, integral_const_mul, hT_eq, hP_eq, hR_eq]
    rw [hformula]
    dsimp [μ]
    have heqAB : A =
        (4 * (Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) - 1) /
          ((Module.finrank ℝ E : ℝ) - 2) ^ 2) * B := by
      simpa [A, B] using heq
    field_simp [show (Module.finrank ℝ E : ℝ) - 2 ≠ 0 by linarith] at hH hscale heqAB ⊢
    apply mul_left_cancel₀ (show (Module.finrank ℝ E : ℝ) ≠ 0 by linarith)
    linear_combination
      ((Module.finrank ℝ E : ℝ) - 2) ^ 2 * hH +
        ((Module.finrank ℝ E : ℝ) - 1) * heqAB -
        4 * (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) * hscale
  have hDpoint := test_integral_zero_continuous
    (I := I) (M := M) hDcont hDnonneg hDint hDzero
  have hTmuR : ∀ x, T x = μ • R x := by
    intro x
    exact sub_eq_zero.mp ((hilbertSchmidtSq_eq_zero_iff _).mp (hDpoint x))
  exact hTmuR

theorem test_classical_equality_forward
    (hRic_nonneg : ∀ (x : M) (v : TM x),
      0 ≤ (leviCivitaConnection (I := I) (M := M)).ricciCurvatureAlmostSchur x v v)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 4 f) (r : ℝ)
    (hpoisson : ∀ x, laplacian LC f x =
      (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x - r)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (heq :
      (∫ x, ((leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x - r) ^ 2
        ∂riemannianVolume (I := I)) =
      (4 * (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) - 1) /
        ((Module.finrank ℝ E : ℝ) - 2) ^ 2) *
        (∫ x, hilbertSchmidtSq
          (traceFree (ricciRaisedEndomorphism LC x))
          ∂riemannianVolume (I := I))) :
    ∀ x, traceFree (ricciRaisedEndomorphism LC x) = 0 := by
  have hdim0 : Module.finrank ℝ E ≠ 0 := by
    have : 0 < Module.finrank ℝ E := by
      exact_mod_cast (show (0 : ℝ) < (Module.finrank ℝ E : ℝ) by linarith)
    exact Nat.ne_of_gt this
  let A : ℝ := ∫ x, ((leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x - r) ^ 2
    ∂riemannianVolume (I := I)
  let B : ℝ := ∫ x, hilbertSchmidtSq
    (traceFree (ricciRaisedEndomorphism LC x)) ∂riemannianVolume (I := I)
  let Henergy : ℝ := ∫ x, traceFreeHessianNormSq LC f x
    ∂riemannianVolume (I := I)
  let Hess : ℝ := ∫ x, hessianNormSq LC f x
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
      (I := I) (M := M) hf r hpoisson hdim0
  have hcauchy : P ^ 2 ≤ B * Henergy := by
    simpa [B, Henergy, P] using traceFree_pairing_cauchy
      (I := I) (M := M) hf hdim0
  have hbochner0 := leviCivita_integratedBundledRicciBochner
    (I := I) (M := M) (f := f) (hf.of_le (by norm_num))
  have hbochner : Hess + Ric = A := by
    have hlap : (∫ x, (laplacian LC f x) ^ 2
        ∂riemannianVolume (I := I)) = A := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hpoisson x]
    simpa [Hess, Ric, A] using hbochner0.trans hlap
  have hRic : 0 ≤ Ric := by
    exact integral_ricciGradient_nonneg (I := I) (M := M) hRic_nonneg f
  have htrace : (Module.finrank ℝ E : ℝ) * Henergy =
      (Module.finrank ℝ E : ℝ) * Hess - A := by
    simpa [Henergy, Hess, A] using poisson_traceFreeHessian_identity
      (I := I) (M := M) hf r hpoisson hdim0
  have hdata := almostSchur_equality_data (d := (Module.finrank ℝ E : ℝ))
    (A := A) (B := B) (Hess := Hess) (Ric := Ric) (H := Henergy) (P := P)
    hdim hA hB hRic hcontracted hcauchy hbochner htrace (by simpa [A, B] using heq)
  rcases hdata with hBzero | ⟨hApos, hBpos, hH, hRiczero, hP_sq, hscale⟩
  · have hBcont : Continuous (fun x ↦ hilbertSchmidtSq
        (traceFree (ricciRaisedEndomorphism LC x))) := by
      simpa using (contMDiff_traceFreeRicciNormSq_one
        (I := I) (M := M)).continuous
    have hBint : Integrable (fun x ↦ hilbertSchmidtSq
        (traceFree (ricciRaisedEndomorphism LC x)))
        (riemannianVolume (I := I)) :=
      integrable_traceFreeRicciNormSq (I := I) (M := M)
    have hBpoint := test_integral_zero_continuous
      (I := I) (M := M) hBcont
      (fun x ↦ hilbertSchmidtSq_nonneg _) hBint (by simpa [B] using hBzero)
    intro x
    exact (hilbertSchmidtSq_eq_zero_iff _).mp (hBpoint x)
  · let μ : ℝ := 2 * ((Module.finrank ℝ E : ℝ) - 1) /
      ((Module.finrank ℝ E : ℝ) - 2)
    let R : ∀ x, TM x →L[ℝ] TM x := fun x ↦
      traceFree (ricciRaisedEndomorphism LC x)
    let T : ∀ x, TM x →L[ℝ] TM x := fun x ↦
      traceFree (LC (gradient (I := I) f) x)
    have hTmuR : ∀ x, T x = μ • R x :=
      equality_traceFreeHessian_proportional (I := I) hf r hdim hdim0 hH hscale heq
    have hgrad3 : ContMDiff I (I.prod 𝓘(ℝ, E)) 3
        (T% (gradient (I := I) f)) :=
      contMDiff_gradient 3 (hf.of_le (by norm_num))
    let hRicfun : M → ℝ := fun x ↦
      (leviCivitaConnection (I := I) (M := M)).ricciCurvatureAlmostSchur x
        (gradient (I := I) f x) (gradient (I := I) f x)
    have hRiccont : Continuous hRicfun := by
      dsimp only [hRicfun]
      apply continuous_iff_continuousAt.2
      intro x
      exact (contMDiffAt_ricciCurvature_apply_one LC
        leviCivitaConnection_metricCompatible leviCivitaConnection_torsion
        (hgrad3 x) (hgrad3 x)).continuousAt
    have hRicint' : Integrable hRicfun
        (riemannianVolume (I := I)) :=
      hRiccont.integrable_of_hasCompactSupport isClosed_closure.isCompact
    have hRicpoint : ∀ x, hRicfun x = 0 := by
      apply test_integral_zero_continuous (I := I) (M := M) hRiccont
        (by
          intro x
          simpa only [hRicfun] using
            hRic_nonneg x (gradient (I := I) f x)) hRicint'
      simpa only [hRicfun, Ric] using hRiczero
    have hTfinal : ∀ x, traceFree (hessianRaisedEndomorphism (I := I) f x) =
        μ • traceFree (ricciRaisedEndomorphism LC x) := by
      intro x
      change traceFree (hessianRaisedEndomorphism (I := I) f x) =
        μ • traceFree (ricciRaisedEndomorphism LC x)
      rw [test_hessianRaised_eq_covariantDerivative_gradient
        (I := I) (M := M) (f := f) x]
      exact hTmuR x
    let S : M → ℝ := fun x ↦
      (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x
    have hSnonneg : ∀ x, 0 ≤ S x := by
      intro x
      simpa [S] using test_scalarCurvature_nonneg
        (I := I) (M := M) hRic_nonneg x
    have hScont : Continuous S := by
      dsimp only [S]
      apply continuous_iff_continuousAt.2
      intro x
      exact (contMDiffAt_scalarCurvature_one LC
        leviCivitaConnection_metricCompatible leviCivitaConnection_torsion x).continuousAt
    have hcontract : ∀ x, hessian LC f x (gradient (I := I) f x)
        (gradient (I := I) f x) =
      (-r / (Module.finrank ℝ E : ℝ) - S x /
        ((Module.finrank ℝ E : ℝ) - 2)) *
        ‖gradient (I := I) f x‖ ^ 2 := by
      intro x
      have h := test_hessian_contraction (I := I) (M := M) (f := f) r μ
        hpoisson hdim (by linarith) (by rfl) hTfinal
        (by intro y; simpa [hRicfun] using hRicpoint y)
      simpa [S] using h x
    have hSint : Integrable S (riemannianVolume (I := I)) :=
      hScont.integrable_of_hasCompactSupport isClosed_closure.isCompact
    have hvolpos : 0 <
        (riemannianVolume (I := I) (M := M) Set.univ).toReal := by
      have hvol := riemannianVolume_finite_positive (I := I) (M := M)
      exact ENNReal.toReal_pos hvol.1.ne' (ne_of_lt hvol.2)
    have hS_integral :
        (∫ x, S x ∂riemannianVolume (I := I)) =
          r * (riemannianVolume (I := I) (M := M) Set.univ).toReal := by
      have hdiff :
          (∫ x, S x - r ∂riemannianVolume (I := I)) = 0 := by
        calc
          (∫ x, S x - r ∂riemannianVolume (I := I)) =
              ∫ x, laplacian LC f x ∂riemannianVolume (I := I) := by
            apply integral_congr_ae
            filter_upwards [] with x
            simpa [S] using (hpoisson x).symm
          _ = 0 := integral_laplacian_eq_zero LC
            leviCivitaConnection_metricCompatible leviCivitaConnection_torsion f
            (hf.of_le (by norm_num))
      rw [integral_sub hSint (integrable_const _), integral_const] at hdiff
      simp only [smul_eq_mul, Measure.real] at hdiff
      nlinarith [hdiff]
    have hr_nonneg : 0 ≤ r := by
      have hI : 0 ≤ ∫ x, S x ∂riemannianVolume (I := I) :=
        integral_nonneg hSnonneg
      rw [hS_integral] at hI
      by_contra hr
      have hrneg : r < 0 := lt_of_not_ge hr
      have hprod : r *
          (riemannianVolume (I := I) (M := M) Set.univ).toReal < 0 :=
        mul_neg_of_neg_of_pos hrneg hvolpos
      linarith
    have hr_pos : 0 < r := by
      by_contra hr
      have hrzero : r = 0 := le_antisymm (le_of_not_gt hr) hr_nonneg
      have hSzero_int : (∫ x, S x ∂riemannianVolume (I := I)) = 0 := by
        rw [hS_integral, hrzero]
        simp
      have hSzero : ∀ x, S x = 0 := test_integral_zero_continuous
        (I := I) (M := M) hScont hSnonneg hSint hSzero_int
      have hAzero : A = 0 := by
        dsimp only [A]
        calc
          (∫ x, ((leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x - r) ^ 2
              ∂riemannianVolume (I := I)) =
              (∫ x, (0 : ℝ) ∂riemannianVolume (I := I)) := by
            apply integral_congr_ae
            filter_upwards [] with x
            have hsx : (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x = 0 := by
              simpa [S] using hSzero x
            rw [hrzero, hsx]
            norm_num
          _ = 0 := by simp
      linarith [hApos, hAzero]
    have hgradzero := gradient_eq_zero_of_hessian_contraction
      (I := I) hf r hr_pos hdim S hSnonneg hcontract
    have hgradfunzero : gradient (I := I) f = 0 := by
      funext x
      exact hgradzero x
    have hLCzero : LC (gradient (I := I) f) = 0 := by
      rw [hgradfunzero]
      simp
    have hμne : μ ≠ 0 := by
      dsimp [μ]
      apply div_ne_zero
      · nlinarith
      · linarith
    have hRzero : ∀ x, R x = 0 := by
      intro x
      have hTzero : T x = 0 := by
        dsimp [T]
        rw [hLCzero]
        simp [traceFree]
      have hμRzero : μ • R x = 0 := by
        calc
          μ • R x = T x := (hTmuR x).symm
          _ = 0 := hTzero
      exact (smul_eq_zero.mp hμRzero).resolve_left hμne
    have hBzero : B = 0 := by
      dsimp only [B]
      calc
        (∫ x, hilbertSchmidtSq
            (traceFree (ricciRaisedEndomorphism LC x))
            ∂riemannianVolume (I := I)) =
            (∫ x, (0 : ℝ) ∂riemannianVolume (I := I)) := by
          apply integral_congr_ae
          filter_upwards [] with x
          have hx : hilbertSchmidtSq
              (traceFree (ricciRaisedEndomorphism LC x)) = 0 := by
            calc
              hilbertSchmidtSq
                  (traceFree (ricciRaisedEndomorphism LC x)) =
                  hilbertSchmidtSq (R x) := by rfl
              _ = hilbertSchmidtSq 0 := by rw [hRzero x]
              _ = 0 := (hilbertSchmidtSq_eq_zero_iff _).2 rfl
          exact hx
        _ = 0 := by simp
    exfalso
    linarith [hBpos, hBzero]


/-! ## Equality: exposing the classical representative -/

theorem exists_classical_weakPoisson_of_smooth_coordinate_forcing
    (hcoord : ∀ c : M, ContDiffOn ℝ ∞
      (fun z => matrixDensity
          (coordinateMetric (I := I) (stdOrthonormalBasis ℝ E).toBasis c z) *
        centeredScalarCurvature (I := I) (M := M)
          ((extChartAt I c).symm z)) (extChartAt I c).target) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧
      (∫ x, g x ∂riemannianVolume (I := I)) = 0 ∧
      ∀ x, laplacian LC g x =
        (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x -
          riemannianMean (I := I)
            (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur := by
  let b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E :=
    stdOrthonormalBasis ℝ E
  let u : M → ℝ := centeredScalarCurvature (I := I) (M := M)
  let hmem : MemLp u 2 (riemannianVolume (I := I) (M := M)) := by
    simpa [u] using
      (memLp_centeredScalarCurvature (I := I) (M := M))
  let f : Lp ℝ 2 (riemannianVolume (I := I) (M := M)) :=
    MemLp.toLp u hmem
  have hscalar : ContMDiff I 𝓘(ℝ, ℝ) 1
      (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur := by
    intro x
    exact contMDiffAt_scalarCurvature_one
      (leviCivitaConnection (I := I) (M := M))
      leviCivitaConnection_metricCompatible leviCivitaConnection_torsion x
  have hf : (∫ x, f x ∂riemannianVolume (I := I) (M := M)) = 0 := by
    rw [integral_congr_ae hmem.coeFn_toLp]
    simpa [u, centeredScalarCurvature] using
      integral_sub_riemannianMean
        ((leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur)
        hscalar
  have huf : u =ᵐ[riemannianVolume (I := I) (M := M)] (f : M → ℝ) :=
    hmem.coeFn_toLp.symm
  have hlocal : ∀ c : M, ∃ V : Set M, IsOpen V ∧ c ∈ V ∧
      ∃ q : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ q V ∧
        q =ᵐ[(riemannianVolume (I := I) (M := M)).restrict V]
          energyCompletionToL2 (weakPoissonSolution f) := by
    intro c
    exact exists_local_smooth_weakPoisson_representative
      (I := I) (M := M) b c f hf u huf (by
        simpa [b, u] using hcoord c)
  choose V hVopen hcV q hq hqa using hlocal
  have hVcover : (Set.univ : Set M) ⊆ ⋃ c : M, V c := by
    intro x _
    exact mem_iUnion.2 ⟨x, hcV x⟩
  obtain ⟨t, ht⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).elim_finite_subcover
      V hVopen hVcover
  let ι : Type _ := (t : Set M)
  let U : ι → Set M := fun i => V i.1
  let Q : ι → M → ℝ := fun i => q i.1
  have hU : ∀ i, IsOpen (U i) := by
    intro i
    exact hVopen i.1
  have hQ : ∀ i, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (Q i) (U i) := by
    intro i
    exact hq i.1
  have hUcover : ∀ x, ∃ i : ι, x ∈ U i := by
    intro x
    have hx : x ∈ ⋃ c ∈ t, V c := ht (mem_univ x)
    rcases mem_iUnion₂.1 hx with ⟨c, hct, hxc⟩
    exact ⟨⟨c, hct⟩, hxc⟩
  have hQae : ∀ i, Q i =ᵐ[
      (riemannianVolume (I := I) (M := M)).restrict (U i)]
      energyCompletionToL2 (weakPoissonSolution
        (MemLp.toLp
          (centeredScalarCurvature (I := I) (M := M))
          (memLp_centeredScalarCurvature (I := I) (M := M)))) := by
    intro i
    have hsame : f =
        MemLp.toLp
          (centeredScalarCurvature (I := I) (M := M))
          (memLp_centeredScalarCurvature (I := I) (M := M)) := by
      change MemLp.toLp u hmem = _
      exact MemLp.toLp_congr hmem
        (memLp_centeredScalarCurvature (I := I) (M := M)) (by
          filter_upwards [] with x
          rfl)
    rw [← hsame]
    exact hqa i.1
  let S : M → ℝ :=
    (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur
  let r : ℝ := riemannianMean (I := I) S
  let F : M → ℝ := fun x ↦ S x - r
  have hF : Continuous F := by
    have hS : Continuous S := hscalar.continuous
    exact hS.sub continuous_const
  have hFu : F = u := by
    funext x
    simp [F, S, r, u, centeredScalarCurvature]
  have hFh : F =ᵐ[riemannianVolume (I := I)] (f : M → ℝ) := by
    rw [hFu]
    exact hmem.coeFn_toLp.symm
  obtain ⟨g, hg, hge, hgm, hglap⟩ :=
    exists_classical_weakPoisson_of_local_representatives
      (I := I) (M := M) LC leviCivitaConnection_metricCompatible
      leviCivitaConnection_torsion f hf F hF hFh U hU hUcover Q hQ hQae
  refine ⟨g, hg, hgm, ?_⟩
  intro x
  simpa [S, r, F] using congrFun hglap x

/-! ## Sharp equality and rigidity -/

theorem almostSchur_equality_iff
    (hRic_nonneg : ∀ (x : M) (v : TM x),
      0 ≤ (leviCivitaConnection (I := I) (M := M)).ricciCurvatureAlmostSchur x v v)
    (hd : 2 < (Module.finrank ℝ E : ℝ)) :
    ((∫ x, ((leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x -
      riemannianMean (I := I)
        (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur) ^ 2
      ∂riemannianVolume (I := I)) =
      (4 * (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) - 1) /
        ((Module.finrank ℝ E : ℝ) - 2) ^ 2) *
        (∫ x, hilbertSchmidtSq
          (traceFree (ricciRaisedEndomorphism LC x))
          ∂riemannianVolume (I := I))) ↔
      ∀ x, traceFree (ricciRaisedEndomorphism LC x) = 0 := by
  constructor
  · intro heq
    obtain ⟨g, hg, _hmean, hpoisson⟩ :=
      exists_classical_weakPoisson_of_smooth_coordinate_forcing
        (I := I) (M := M)
        (fun c => smooth_coordinate_forcing (I := I) (M := M) c)
    apply test_classical_equality_forward (I := I) (M := M) hRic_nonneg
      (hg.of_le (by
        exact WithTop.coe_le_coe.mpr
          (show (4 : ℕ∞) ≤ ⊤ from le_top)))
      (riemannianMean (I := I)
        (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur) hpoisson hd
    exact heq
  · intro hRzero
    have hbound := almostSchur_bound_complete
      (I := I) (M := M) hRic_nonneg hd
    have hBzero : (∫ x, hilbertSchmidtSq
        (traceFree (ricciRaisedEndomorphism LC x))
        ∂riemannianVolume (I := I)) = 0 := by
      calc
        (∫ x, hilbertSchmidtSq
            (traceFree (ricciRaisedEndomorphism LC x))
            ∂riemannianVolume (I := I)) =
            (∫ x, (0 : ℝ) ∂riemannianVolume (I := I)) := by
          apply integral_congr_ae
          filter_upwards [] with x
          calc
            hilbertSchmidtSq
                (traceFree (ricciRaisedEndomorphism LC x)) =
                hilbertSchmidtSq 0 := by rw [hRzero x]
            _ = 0 := (hilbertSchmidtSq_eq_zero_iff _).2 rfl
        _ = 0 := by simp
    have hAnonneg : 0 ≤
        ∫ x, ((leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x -
          riemannianMean (I := I)
            (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur) ^ 2
          ∂riemannianVolume (I := I) := by
      exact integral_nonneg (fun x ↦ sq_nonneg _)
    rw [hBzero, mul_zero] at hbound
    have hA : (∫ x, ((leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur x -
        riemannianMean (I := I)
          (leviCivitaConnection (I := I) (M := M)).scalarCurvatureAlmostSchur) ^ 2
        ∂riemannianVolume (I := I)) = 0 := le_antisymm hbound hAnonneg
    rw [hA, hBzero]
    simp

end AlmostSchur
