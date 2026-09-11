/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryHelmholtzField
public import LeanPool.NavierStokesAndEuler.Euler.SolutionDefinitions
public import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicDecomposition
import LeanPool.NavierStokesAndEuler.Euler.MeanWeakHarmonicScaling
import Mathlib.Algebra.Order.Star.Real
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothField
public import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalSpace
import LeanPool.NavierStokesAndEuler.Euler.ClassicalBridge
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Prod
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothLimit
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import LeanPool.NavierStokesAndEuler.Euler.MeanWeakCurl
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# The Comparator solution satisfies the weak projected Euler equation

The test family is the dense family of compact smooth solenoidal fields.
Only pointwise identification of the supplied smooth `L²` fields with the
Comparator velocity is assumed; no time regularity of those fields is used.
-/

section

/-!
# The Euler equation tested against compact vector fields

Differentiation under the compact spatial integral uses joint smoothness on
positive times. It does not assume an `L²` time derivative or any pressure
decay.
-/

section

/-! Pressure cancellation against compactly supported solenoidal vector tests.

The scalar pressure needs only ordinary smoothness. In particular, neither
the pressure nor its gradient is assumed to be globally square integrable.
-/

@[expose] public section

noncomputable section

namespace EulerComparatorPressure

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerVectorCalculus
  EulerMeanSolenoidal EulerMeanPressure
open scoped ContDiff

/-- Integration by parts with compact support on the vector test, rather than
on the scalar potential. -/
theorem compact_vector_gradient_integration_by_parts (φ : Space → Space)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (p : Space → ℝ) (hp : ContDiff ℝ ∞ p) :
    (∫ x, ⟪φ x, gradient p x⟫_ℝ) = -∫ x, p x * divergence φ x := by
  let φi (i : Fin 3) (x : Space) := φ x i
  have hφi (i : Fin 3) : ContDiff ℝ ∞ (φi i) :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hφ
  have hci (i : Fin 3) : HasCompactSupport (φi i) :=
    hc.comp_left (g := fun v : Space => v i) rfl
  have hi₁ (i : Fin 3) : Integrable (fun x => partialDerivative p i x * φi i x) :=
    ((contDiff_partialDerivative p hp i).continuous.mul
      (hφi i).continuous).integrable_of_hasCompactSupport (hci i).mul_left
  have hi₂ (i : Fin 3) : Integrable (fun x => p x * partialDerivative (φi i) i x) :=
    (hp.continuous.mul (contDiff_partialDerivative _ (hφi i)
        i).continuous).integrable_of_hasCompactSupport
        ((hci i).fderiv_apply ℝ (EuclideanSpace.single i 1)).mul_left
  have hibp (i : Fin 3) : (∫ x, partialDerivative p i x * φi i x) =
      -∫ x, p x * partialDerivative (φi i) i x :=
    scalar_test_ibp p (φi i) hp (hφi i) (hci i) i
  have hinner (x : Space) : ⟪φ x, gradient p x⟫_ℝ =
      ∑ i : Fin 3, partialDerivative p i x * φi i x := by
    rw [real_inner_comm, inner_gradient_left]
    have hre : ∑ i : Fin 3, φ x i • (EuclideanSpace.single i 1 : Space) = φ x := by
      simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (φ x)
    calc
      fderiv ℝ p x (φ x) =
          fderiv ℝ p x (∑ i : Fin 3, φ x i • EuclideanSpace.single i 1) :=
        congrArg (fderiv ℝ p x) hre.symm
      _ = ∑ i : Fin 3, partialDerivative p i x * φi i x := by
        simp only [map_sum, map_smul, smul_eq_mul, partialDerivative, φi, mul_comm]
  have hdiv (x : Space) : p x * divergence φ x =
      ∑ i : Fin 3, p x * partialDerivative (φi i) i x := by
    rw [divergence_eq_coordinate_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact (fderiv_coordinate φ x ((hφ.differentiable (by simp)).differentiableAt)
      i (EuclideanSpace.single i 1)).symm
  simp_rw [hinner, hdiv]
  rw [integral_finsetSum _ (fun i _ => hi₁ i),
    integral_finsetSum _ (fun i _ => hi₂ i)]
  simp only [hibp, Finset.sum_neg_distrib]

/-- An arbitrary smooth scalar pressure cancels against a compact smooth
divergence-free vector test. -/
theorem compact_solenoidal_pressure_pairing_zero (φ : Space → Space)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hdiv : ∀ x, divergence φ x = 0)
    (p : Space → ℝ) (hp : ContDiff ℝ ∞ p) :
    (∫ x, ⟪φ x, gradient p x⟫_ℝ) = 0 := by
  rw [compact_vector_gradient_integration_by_parts φ hφ hc p hp]
  simp only [hdiv, mul_zero, integral_zero, neg_zero]

end EulerComparatorPressure

end
end

end

@[expose] public section

noncomputable section

open Set Filter MeasureTheory EulerSmoothLimit
open scoped ContDiff Topology

namespace Euler.EulerExistenceAndSmoothnessR3

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

variable {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
  (h : EulerExistenceAndSmoothnessR3 u₀ v p)

include h

/-- The pointwise Euler equation differentiates every compactly supported
continuous vector test pairing. Pressure is retained in this first identity. -/
theorem velocity_test_pairing_hasDerivAt
    (φ : ℝ³ → ℝ³) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (t₀ : ℝ) (ht₀ : 0 < t₀) :
    HasDerivAt (fun t : ℝ => ∫ x : ℝ³, inner ℝ (φ x) (v x t))
      (∫ x : ℝ³, inner ℝ (φ x)
        (-fderiv ℝ (v · t₀) x (v x t₀) - gradient (p · t₀) x)) t₀ := by
  let u : ℝ × ℝ³ → ℝ³ := fun z => v z.2 z.1
  let Ω : Set (ℝ × ℝ³) := Ioi 0 ×ˢ univ
  have hΩ : IsOpen Ω := isOpen_Ioi.prod isOpen_univ
  have hu : ContDiffOn ℝ ∞ u Ω :=
    h.velocity_smooth.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
      (fun z hz => ⟨mem_univ _, (show 0 < z.1 from hz.1).le⟩)
  let C : ℝ → ℝ³ → ℝ³ := fun r x => fderiv ℝ u (r, x) (1, 0)
  have hC : ContinuousOn (Function.uncurry C) Ω :=
    (hu.continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply continuousOn_const
  have hderiv (r : ℝ) (hr : 0 < r) (x : ℝ³) :
      HasDerivAt (fun s => v x s) (C r x) r := by
    have hud := (hu.differentiableOn (by simp) (r, x) ⟨hr, mem_univ x⟩).differentiableAt
      (hΩ.mem_nhds ⟨hr, mem_univ x⟩)
    simpa only [u, C, Function.comp_def, id_eq] using hud.hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).prodMk (hasDerivAt_const r x))
  let J : Set ℝ := Icc (t₀ / 2) (t₀ + 1)
  have hJ : J ∈ 𝓝 t₀ := Icc_mem_nhds (by linarith) (by linarith)
  have hJpos : ∀ r ∈ J, 0 < r := by intro r hr; dsimp [J] at hr; linarith [hr.1]
  let F : ℝ → ℝ³ → ℝ := fun r x => inner ℝ (φ x) (v x r)
  let G : ℝ → ℝ³ → ℝ := fun r x => inner ℝ (φ x) (C r x)
  have hG : ContinuousOn (Function.uncurry G) (J ×ˢ tsupport φ) := by
    apply (hφ.comp continuous_snd).continuousOn.inner
    exact hC.mono (fun z hz => ⟨hJpos z.1 hz.1, mem_univ _⟩)
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hφc).exists_bound_of_continuousOn hG
  have hFcont (r : ℝ) (hr : 0 < r) : Continuous (F r) :=
    hφ.inner (h.velocity_contDiff r hr.le).continuous
  have hGcont : Continuous (G t₀) := by
    apply hφ.inner
    exact hC.comp_continuous (continuous_const.prodMk continuous_id)
      (fun x => ⟨ht₀, mem_univ x⟩)
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (tsupport φ)) (F := F) (F' := G)
    (bound := fun _ => M) hJ
    (by
      filter_upwards [Ioi_mem_nhds ht₀] with r hr
      exact (hFcont r hr).aestronglyMeasurable)
    ((hFcont t₀ ht₀).continuousOn.integrableOn_compact hφc)
    hGcont.aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem hφc.measurableSet] with x hx
      intro r hr
      exact hM (r, x) ⟨hr, hx⟩)
    (integrableOn_const hφc.measure_ne_top)
    (Eventually.of_forall (fun x r hr => by
      simpa only [F, G, inner_zero_left, add_zero] using
        (hasDerivAt_const r (φ x)).inner ℝ (hderiv r (hJpos r hr) x)))
  have hFwhole : (fun r => ∫ x in tsupport φ, F r x) = fun r => ∫ x, F r x := by
    funext r
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp only [F, image_eq_zero_of_notMem_tsupport hx, inner_zero_left]
  have hGwhole : (∫ x in tsupport φ, G t₀ x) = ∫ x, G t₀ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp only [G, image_eq_zero_of_notMem_tsupport hx, inner_zero_left]
  have hCeq (x : ℝ³) : C t₀ x =
      -fderiv ℝ (v · t₀) x (v x t₀) - gradient (p · t₀) x :=
    (hderiv t₀ ht₀ x).unique (h.pointwise_euler x t₀ ht₀)
  have hd := hdiff.2
  rw [hFwhole, hGwhole] at hd
  simpa only [F, G, hCeq] using hd

/-- Pressure disappears from the test-pairing derivative when the compact
smooth vector test is divergence-free. -/
theorem velocity_solenoidal_test_pairing_hasDerivAt
    (φ : ℝ³ → ℝ³) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hdiv : ∀ x, EulerSmoothLimit.divergence φ x = 0)
    (t₀ : ℝ) (ht₀ : 0 < t₀) :
    HasDerivAt (fun t : ℝ => ∫ x : ℝ³, inner ℝ (φ x) (v x t))
      (-(∫ x : ℝ³, inner ℝ (φ x) (fderiv ℝ (v · t₀) x (v x t₀)))) t₀ := by
  have hv := h.velocity_contDiff t₀ ht₀.le
  have hp := h.pressure_contDiff t₀ ht₀.le
  have hi (b : ℝ³ → ℝ³) (hb : Continuous b) :
      Integrable (fun x => inner ℝ (φ x) (b x)) := by
    apply (hφ.continuous.inner hb).integrable_of_hasCompactSupport
    exact HasCompactSupport.intro hφc (fun x hx => by
      simp only [image_eq_zero_of_notMem_tsupport hx, inner_zero_left])
  have ha := hi (fun x => fderiv ℝ (v · t₀) x (v x t₀))
    ((hv.fderiv_right (m := ∞) (by simp)).continuous.clm_apply hv.continuous)
  have hg := hi (gradient (p · t₀)) (EulerMeanSolenoidal.contDiff_gradient hp).continuous
  have hc := EulerComparatorPressure.compact_solenoidal_pressure_pairing_zero
    φ hφ hφc hdiv (p · t₀) hp
  have heq : (∫ x : ℝ³, inner ℝ (φ x)
      (-fderiv ℝ (v · t₀) x (v x t₀) - gradient (p · t₀) x)) =
      -(∫ x : ℝ³, inner ℝ (φ x) (fderiv ℝ (v · t₀) x (v x t₀))) := by
    simp only [inner_sub_right, inner_neg_right]
    have han : Integrable (fun x => -inner ℝ (φ x)
        (fderiv ℝ (v · t₀) x (v x t₀))) := by
      simpa only [neg_one_mul] using ha.const_mul (-1)
    rw [integral_sub han hg, integral_neg, hc, sub_zero]
  have hd := h.velocity_test_pairing_hasDerivAt φ hφ.continuous hφc t₀ ht₀
  rwa [heq] at hd

end Euler.EulerExistenceAndSmoothnessR3

namespace Euler.ComparatorBridge

open EulerLpTranslation EulerMeanSolenoidal

/-- Replacing the Comparator velocity by any pointwise equal smooth `L²`
representatives preserves the tested time equation, including its clamped
interval parameterization. No time regularity of the representatives is assumed. -/
theorem comparator_clamped_compact_pairing_hasDerivAt
    {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
    (h : EulerExistenceAndSmoothnessR3 u₀ v p) {T : ℝ} (hT : 0 < T)
    (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ s, (A s).field = (v · s))
    (g : L2) (φ : Space → Space)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφdiv : ∀ x, EulerSmoothLimit.divergence φ x = 0)
    (hg : (g : Space → Space) =ᵐ[volume] φ)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => inner ℝ g (A (projIcc 0 T hT.le r)).toLp)
      (-(∫ x, inner ℝ (φ x) (fderiv ℝ (v · t) x (v x t)))) t := by
  have hd := h.velocity_solenoidal_test_pairing_hasDerivAt φ hφ hφc hφdiv t ht.1
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
  rw [projIcc_of_mem hT.le ⟨hr.1.le, hr.2.le⟩, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg, (A ⟨r, hr.1.le, hr.2.le⟩).toLp_ae] with x hgx hAx
  rw [hgx, hAx, hA]

end Euler.ComparatorBridge

end
end

end

section

/-!
# Compact smooth solenoidal tests determine ordinary L² solenoidal fields

The curl-curl identity reduces the orthogonal complement of compact smooth
curls inside the solenoidal space to globally weakly harmonic L² fields.
-/

@[expose] public section

noncomputable section

namespace Euler.ComparatorBridge

open Set MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit EulerVectorCalculus
  EulerMeanSolenoidal EulerMeanGradientTest EulerMeanVectorIdentities EulerMeanHarmonic
  EulerMeanCurlIntegration EulerMeanBoundary
open scoped ContDiff Topology
open Filter

/-- A distributionally harmonic vector field on all of ℝ³ vanishes if it lies in L². -/
theorem weakHarmonicOn_univ_eq_zero (u : EulerMeanSolenoidal.L2)
    (hu : WeakHarmonicOn Set.univ u) : u = 0 := by
  have hball (n : ℕ) : WeakHarmonicOn
      (Metric.ball (0 : Space) ((n + 1 : ℕ) : ℝ)) u := by
    intro φ hc hs _
    exact hu φ hc hs (Set.subset_univ _)
  have hall : ∀ᵐ x ∂volume, ∀ n : ℕ,
      x ∈ Metric.closedBall (0 : Space) (((n + 1 : ℕ) : ℝ) / 4) →
      ‖u x‖ ^ 2 ≤
        (harmonicQuarterBallConstant * (((n + 1 : ℕ) : ℝ) ^ 3)⁻¹) * ‖u‖ ^ 2 :=
    ae_all_iff.mpr (fun n => weakHarmonic_pointwise_scaled u
      ((n + 1 : ℕ) : ℝ) (by positivity) (hball n))
  have hrad : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun n : ℕ =>
      (harmonicQuarterBallConstant * (((n + 1 : ℕ) : ℝ) ^ 3)⁻¹) * ‖u‖ ^ 2)
      atTop (𝓝 0) := by
    have hi := (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)).comp
      ((tendsto_pow_atTop (by decide : (3 : ℕ) ≠ 0)).comp hrad)
    simpa using (hi.const_mul harmonicQuarterBallConstant).mul_const (‖u‖ ^ 2)
  apply Lp.ext
  filter_upwards [hall, Lp.coeFn_zero Space 2 volume] with x hx hz
  rw [hz]
  have hlarge : ∀ᶠ n : ℕ in atTop, 4 * ‖x‖ ≤ ((n + 1 : ℕ) : ℝ) :=
    hrad.eventually (eventually_ge_atTop (4 * ‖x‖))
  have hzero : ‖u x‖ ^ 2 ≤ 0 := ge_of_tendsto hlim (hlarge.mono (fun n hn =>
    hx n (by simpa only [Metric.mem_closedBall, dist_zero_right] using
      (show ‖x‖ ≤ ((n + 1 : ℕ) : ℝ) / 4 by linarith))))
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hzero (sq_nonneg _)))

/-- Taking the L² class of a compact smooth curl is a linear operation. -/
def compactCurlMap : Test →ₗ[ℝ] L2 where
  toFun f := testValue (curlTest f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [testValue_ae (curlTest (f + g)),
      testValue_ae (curlTest f), testValue_ae (curlTest g),
      Lp.coeFn_add (testValue (curlTest f)) (testValue (curlTest g))]
      with x hfg hf hg ha
    rw [hfg, ha]
    simp only [Pi.add_apply, hf, hg]
    exact congrFun (vectorCurl_add (f : Space → Space) (g : Space → Space)
      (f.smooth.differentiable (by simp)) (g.smooth.differentiable (by simp))) x
  map_smul' c f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [testValue_ae (curlTest (c • f)), testValue_ae (curlTest f),
      Lp.coeFn_smul c (testValue (curlTest f))] with x hcf hf hs
    rw [hcf, hs]
    simp only [Pi.smul_apply, hf]
    exact congrFun (vectorCurl_smul c (f : Space → Space)
      (f.smooth.differentiable (by simp))) x

/-- L² classes of curls of genuine compactly supported smooth vector fields. -/
def compactCurlGenerators : Set L2 :=
  Set.range (fun f : Test => testValue (curlTest f))

/-- The closed linear space generated by compactly supported smooth curls. -/
def compactCurlSpace : Submodule ℝ L2 :=
  (Submodule.span ℝ compactCurlGenerators).topologicalClosure

theorem compactCurlSpace_closed : IsClosed (compactCurlSpace : Set L2) :=
  (Submodule.span ℝ compactCurlGenerators).isClosed_topologicalClosure

instance : CompleteSpace compactCurlSpace := compactCurlSpace_closed.completeSpace_coe

theorem compactCurl_mem_solenoidal (f : Test) :
    testValue (curlTest f) ∈ solenoidalSpace :=
  curl_mem_solenoidal _ ((contDiff_piLp 2).mp f.smooth) (test_memLp (curlTest f))

theorem compactCurl_mem (f : Test) : testValue (curlTest f) ∈ compactCurlSpace :=
  (Submodule.span ℝ compactCurlGenerators).le_topologicalClosure
    (Submodule.subset_span ⟨f, rfl⟩)

theorem compactCurlSpace_le_solenoidal : compactCurlSpace ≤ solenoidalSpace := by
  apply (Submodule.span ℝ compactCurlGenerators).topologicalClosure_minimal
    _ gradientSpace.isClosed_orthogonal
  apply Submodule.span_le.mpr
  rintro _ ⟨f, rfl⟩
  exact compactCurl_mem_solenoidal f

/-- A solenoidal field annihilating compact smooth curls is weakly harmonic. -/
theorem weakHarmonicOn_univ_of_compactCurl_pairing_zero
    (u : L2) (hu : u ∈ solenoidalSpace)
    (htest : ∀ f : Test, ⟪u, testValue (curlTest f)⟫_ℝ = 0) :
    WeakHarmonicOn Set.univ u := by
  intro φ hc hs _
  let f : Test := ⟨φ, hs, hc⟩
  have h := solenoidal_curlcurl_pairing u hu f
  rw [htest (curlTest f)] at h
  have hz : ⟪u, testValue (laplacianTest f)⟫_ℝ = 0 := by linarith
  exact (l2_test_pairing u (laplacianTest f)).symm.trans hz

/-- Compact smooth curls span the entire solenoidal Hilbert space densely. -/
theorem compactCurlSpace_eq_solenoidal : compactCurlSpace = solenoidalSpace := by
  have hbot : compactCurlSpace.orthogonal ⊓ solenoidalSpace = ⊥ := by
    apply eq_bot_iff.mpr
    intro u hu
    change u = 0
    apply weakHarmonicOn_univ_eq_zero u
    apply weakHarmonicOn_univ_of_compactCurl_pairing_zero u hu.2
    intro f
    rw [real_inner_comm]
    exact hu.1 _ (compactCurl_mem f)
  simpa only [hbot, sup_bot_eq] using
    (Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection compactCurlSpace_le_solenoidal)

/-- Linearity makes the closure of the generator set itself the full solenoidal space. -/
theorem closure_compactCurlGenerators :
    closure compactCurlGenerators = (solenoidalSpace : Set L2) := by
  have hspan : Submodule.span ℝ compactCurlGenerators = compactCurlMap.range := by
    change Submodule.span ℝ (compactCurlMap.range : Set L2) = compactCurlMap.range
    exact Submodule.span_eq _
  calc
    closure compactCurlGenerators = (compactCurlSpace : Set L2) := by
      rw [compactCurlSpace, hspan, Submodule.topologicalClosure_coe]
      rfl
    _ = (solenoidalSpace : Set L2) := by rw [compactCurlSpace_eq_solenoidal]

/-- Compact smooth curl classes regarded as a subset of the solenoidal Hilbert space. -/
def compactSolenoidalTests : Set solenoidalSpace :=
  {u | (u : L2) ∈ compactCurlGenerators}

/-- Every member is represented by an actual compact smooth divergence-free field. -/
theorem compactSolenoidalTests_representation (u : solenoidalSpace)
    (hu : u ∈ compactSolenoidalTests) :
    ∃ φ : Space → Space, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      (∀ x, divergence φ x = 0) ∧ ((u : L2) : Space → Space) =ᵐ[volume] φ := by
  obtain ⟨f, hf⟩ := hu
  refine ⟨(curlTest f : Space → Space), (curlTest f).smooth, (curlTest f).compact,
    divergence_curl _ ((contDiff_piLp 2).mp f.smooth), ?_⟩
  rw [← hf]
  exact testValue_ae (curlTest f)

/-- A bundled compact smooth solenoidal test has the prescribed L² class. -/
theorem compactSolenoidalTests_testValue (u : solenoidalSpace)
    (hu : u ∈ compactSolenoidalTests) :
    ∃ f : Test, (∀ x, divergence (f : Space → Space) x = 0) ∧
      testValue f = (u : L2) := by
  obtain ⟨f, hf⟩ := hu
  exact ⟨curlTest f, divergence_curl _ ((contDiff_piLp 2).mp f.smooth), hf⟩

/-- The compact test fields form a dense subset of the actual solenoidal L² space. -/
theorem compactSolenoidalTests_dense : Dense compactSolenoidalTests := by
  apply Subtype.dense_iff.mpr
  change (solenoidalSpace : Set L2) ⊆
    closure (Subtype.val '' {u : solenoidalSpace | (u : L2) ∈ compactCurlGenerators})
  have himage : Subtype.val ''
      {u : solenoidalSpace | (u : L2) ∈ compactCurlGenerators} = compactCurlGenerators := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hx
      have hxS : x ∈ solenoidalSpace := by
        change x ∈ (solenoidalSpace : Set L2)
        rw [← closure_compactCurlGenerators]
        exact subset_closure hx
      exact ⟨⟨x, hxS⟩, hx, rfl⟩
  rw [himage, closure_compactCurlGenerators]

/-- Pairings against compact smooth solenoidal tests determine a solenoidal field. -/
theorem solenoidal_eq_zero_of_compact_test_pairing_zero
    (u : L2) (hu : u ∈ solenoidalSpace)
    (htest : ∀ f : Test, (∀ x, divergence (f : Space → Space) x = 0) →
      ⟪u, testValue f⟫_ℝ = 0) : u = 0 := by
  apply weakHarmonicOn_univ_eq_zero u
  apply weakHarmonicOn_univ_of_compactCurl_pairing_zero u hu
  intro f
  exact htest (curlTest f) (divergence_curl _ ((contDiff_piLp 2).mp f.smooth))

end Euler.ComparatorBridge

end
end

end

section

/-!
# Pairing the projected Euler right-hand side

A solenoidal `L²` test field removes the Helmholtz projection from the
Euler right-hand side. For a smooth divergence-free test field, this gives
the ordinary spatial integral against advection. Compactly supported smooth
tests automatically satisfy the required `L²` assumption.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerOrdinarySobolev
  EulerVectorCalculus
open scoped ContDiff

namespace EulerCompactProjectedPairing

/-- The Helmholtz projection can be removed in a solenoidal pairing. -/
theorem inner_solenoidalProjection (φ b : L2) (hφ : φ ∈ solenoidalSpace) :
    ⟪φ, solenoidalProjection b⟫_ℝ = ⟪φ, b⟫_ℝ := by
  have hz := pressure_pairing_zero (sub_solenoidalProjection_mem_gradient b) hφ
  rw [real_inner_comm, inner_sub_right] at hz
  exact (sub_eq_zero.mp hz).symm

/-- A solenoidal test sees precisely negative advection in the projected
Euler right-hand side. -/
theorem inner_projectedRhs (φ : L2) (hφ : φ ∈ solenoidalSpace)
    (A : SmoothL2Field Space) :
    ⟪φ, (projectedRhs A).toLp⟫_ℝ = -⟪φ, (advectionField A A).toLp⟫_ℝ := by
  rw [projectedRhs_toLp, inner_neg_right, inner_solenoidalProjection _ _ hφ]

/-- Integral form of the projected pairing for an arbitrary solenoidal
`L²` representative. -/
theorem inner_projectedRhs_eq_integral (φ : Space → Space)
    (hLp : MemLp φ 2 (volume : Measure Space))
    (hφ : hLp.toLp φ ∈ solenoidalSpace) (A : SmoothL2Field Space) :
    ⟪hLp.toLp φ, (projectedRhs A).toLp⟫_ℝ =
      -∫ x, ⟪φ x, fderiv ℝ A.field x (A.field x)⟫_ℝ := by
  rw [inner_projectedRhs _ hφ, MeasureTheory.L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [hLp.coeFn_toLp, (advectionField A A).toLp_ae] with x hφx hAx
  rw [hφx, hAx, advectionField_field]

/-- Smooth divergence-free `L²` tests remove the pressure projection. -/
theorem smooth_inner_projectedRhs_eq_integral (φ : Space → Space)
    (hs : ContDiff ℝ ∞ φ) (hLp : MemLp φ 2 (volume : Measure Space))
    (hdiv : ∀ x, divergence φ x = 0) (A : SmoothL2Field Space) :
    ⟪hLp.toLp φ, (projectedRhs A).toLp⟫_ℝ =
      -∫ x, ⟪φ x, fderiv ℝ A.field x (A.field x)⟫_ℝ :=
  inner_projectedRhs_eq_integral φ hLp (smooth_mem_solenoidal φ hs hLp hdiv) A

/-- In particular, every compactly supported smooth divergence-free test
has the projected Euler pairing required by the Comparator bridge. -/
theorem compact_inner_projectedRhs_eq_integral (φ : Space → Space)
    (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hdiv : ∀ x, divergence φ x = 0) (A : SmoothL2Field Space) :
    ⟪(hs.continuous.memLp_of_hasCompactSupport hc).toLp φ,
        (projectedRhs A).toLp⟫_ℝ =
      -∫ x, ⟪φ x, fderiv ℝ A.field x (A.field x)⟫_ℝ :=
  smooth_inner_projectedRhs_eq_integral φ hs
    (hs.continuous.memLp_of_hasCompactSupport hc) hdiv A

end EulerCompactProjectedPairing

end
end

end

@[expose] public section

noncomputable section

open Set Filter MeasureTheory InnerProductSpace EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerOrdinarySobolev
open scoped ContDiff Topology

namespace Euler.ComparatorBridge

private theorem inner_smoothField_eq_integral
    (g : L2) (φ : Space → Space) (hg : (g : Space → Space) =ᵐ[volume] φ)
    (A : SmoothL2Field Space) :
    inner ℝ g A.toLp = ∫ x, inner ℝ (φ x) (A.field x) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg, A.toLp_ae] with x hgx hAx
  rw [hgx, hAx]

/-- An arbitrary compact smooth solenoidal representative has the clamped
weak projected derivative used by the Sobolev time-upgrade theorem. -/
theorem comparator_compact_rep_pairing_hasDerivAt
    {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
    (h : EulerExistenceAndSmoothnessR3 u₀ v p) {T : ℝ} (hT : 0 < T)
    (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ s, (A s).field = (v · s))
    (g : solenoidalSpace) (φ : Space → Space)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφdiv : ∀ x, EulerSmoothLimit.divergence φ x = 0)
    (hg : ((g : L2) : Space → Space) =ᵐ[volume] φ)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => inner ℝ (g : L2) (A (projIcc 0 T hT.le r)).toLp)
      (inner ℝ (g : L2) (projectedRhs (A ⟨t, ht.1.le, ht.2.le⟩)).toLp) t := by
  have hd := comparator_clamped_compact_pairing_hasDerivAt h hT A hA
    (g : L2) φ hφ hφc hφdiv hg t ht
  have hR : -(∫ x, inner ℝ (φ x) (fderiv ℝ (v · t) x (v x t))) =
      inner ℝ (g : L2) (projectedRhs (A ⟨t, ht.1.le, ht.2.le⟩)).toLp := by
    rw [EulerCompactProjectedPairing.inner_projectedRhs _ g.property,
      inner_smoothField_eq_integral _ φ hg]
    simp only [advectionField_field, hA]
  rwa [hR] at hd

/-- The exact weak projected derivative on the dense compact solenoidal
test family. This is derived from the Comparator Euler equation itself. -/
theorem comparator_projected_pairing_hasDerivAt
    {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
    (h : EulerExistenceAndSmoothnessR3 u₀ v p) {T : ℝ} (hT : 0 < T)
    (A : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ s, (A s).field = (v · s))
    (g : solenoidalSpace) (hg : g ∈ compactSolenoidalTests)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => inner ℝ (g : L2) (A (projIcc 0 T hT.le r)).toLp)
      (inner ℝ (g : L2) (projectedRhs (A ⟨t, ht.1.le, ht.2.le⟩)).toLp) t := by
  obtain ⟨φ, hφ, hφc, hφdiv, hgrep⟩ := compactSolenoidalTests_representation g hg
  exact comparator_compact_rep_pairing_hasDerivAt h hT A hA g φ
    hφ hφc hφdiv hgrep t ht

end Euler.ComparatorBridge
