/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.WeakTimeContinuity
public import LeanPool.NavierStokesAndEuler.Euler.CurlTimeDerivative
public import LeanPool.NavierStokesAndEuler.Euler.CompactPressurePairing
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothField
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

/-!
# The Euler equation tested against compact vector fields

Differentiation under the compact spatial integral uses joint smoothness on
positive times. It does not assume an `L²` time derivative or any pressure
decay.
-/

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
