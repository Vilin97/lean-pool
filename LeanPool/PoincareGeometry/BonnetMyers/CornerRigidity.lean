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

import LeanPool.PoincareGeometry.BonnetMyers.DistanceRegularity
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# One-sided derivative rigidity at a minimizing corner

The normal-coordinate first variation formula is combined here with a
right-sided exact-distance identity.  Equality in Cauchy--Schwarz then forces
the outgoing tangent to have the same direction as the terminal radial
tangent.  This is the analytic core of corner elimination.
-/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace BonnetMyersEntry

/-- If `a`, `c`, and `d` lie in that order on an exact metric segment, and a
curve from `c` to `d` realizes the expected prefix and suffix distances, then
distance from `a` grows linearly along that curve. -/
theorem distance_along_exact_metric_tail
    {X : Type*} [PseudoMetricSpace X]
    {a c d : X} {beta : ℝ → X} {C : ℝ}
    (hbeta0 : beta 0 = c) (hbeta1 : beta 1 = d)
    (hchain : dist a d = dist a c + dist c d)
    (hcd : dist c d = C)
    (hsub : ∀ s ∈ Ioo (0 : ℝ) 1,
      dist c (beta s) = C * s ∧ dist (beta s) d = C * (1 - s)) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      dist a (beta s) = dist a c + C * s := by
  intro s hs
  rcases eq_or_lt_of_le hs.1 with rfl | hs0
  · simp [hbeta0]
  rcases eq_or_lt_of_le hs.2 with rfl | hs1
  · rw [hbeta1, hchain, hcd]
    ring
  have hparts := hsub s ⟨hs0, hs1⟩
  have hupp : dist a (beta s) ≤ dist a c + C * s := by
    calc
      dist a (beta s) ≤ dist a c + dist c (beta s) := dist_triangle _ _ _
      _ = dist a c + C * s := by rw [hparts.1]
  have hlow : dist a c + C * s ≤ dist a (beta s) := by
    have htri : dist a d ≤ dist a (beta s) + dist (beta s) d :=
      dist_triangle _ _ _
    rw [hchain, hcd, hparts.2] at htri
    linarith
  exact le_antisymm hupp hlow

/-- Positive aligned vectors become equal after normalization by their
respective norms. -/
theorem inv_smul_eq_inv_smul_of_norm_smul_eq
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {v w : Y} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hv : ‖v‖ = a) (hw : ‖w‖ = b)
    (halign : ‖w‖ • v = ‖v‖ • w) :
    a⁻¹ • v = b⁻¹ • w := by
  rw [hv, hw] at halign
  calc
    a⁻¹ • v = ((a * b)⁻¹ * b) • v := by
      congr 1
      field_simp
    _ = (a * b)⁻¹ • (b • v) := by rw [smul_smul]
    _ = (a * b)⁻¹ • (a • w) := congrArg (fun q ↦ (a * b)⁻¹ • q) halign
    _ = ((a * b)⁻¹ * a) • w := by rw [smul_smul]
    _ = b⁻¹ • w := by
      congr 1
      field_simp

/-- Two ordinary derivatives agree if their functions agree on a right
neighbourhood, including at the base point. -/
theorem deriv_eq_of_eventuallyEq_right
    {f g : ℝ → ℝ} {a b x : ℝ}
    (hf : HasDerivAt f a x) (hg : HasDerivAt g b x)
    (heq : f =ᶠ[𝓝[Ici x] x] g) (heqx : f x = g x) : a = b := by
  have hf' : HasDerivWithinAt f a (Ici x) x := hf.hasDerivWithinAt
  have hg' : HasDerivWithinAt g b (Ici x) x := hg.hasDerivWithinAt
  have hfg : HasDerivWithinAt g a (Ici x) x :=
    hf'.congr_of_eventuallyEq heq.symm heqx.symm
  exact UniqueDiffWithinAt.eq_deriv (Ici x) (uniqueDiffWithinAt_Ici x) hfg hg'

/-- If two differentiable real functions agree at zero and the first is at
most the second on a right neighbourhood, then their derivatives have the
same order. -/
theorem deriv_le_of_eventually_le_right
    {f g : ℝ → ℝ} {a b : ℝ}
    (hf : HasDerivAt f a 0) (hg : HasDerivAt g b 0)
    (hle : f ≤ᶠ[𝓝[Ici (0 : ℝ)] 0] g) (hzero : f 0 = g 0) : a ≤ b := by
  apply sub_nonneg.mp
  apply ge_of_tendsto (hg.sub hf).tendsto_slope_zero_right
  have hle' : f ≤ᶠ[𝓝[>] (0 : ℝ)] g :=
    hle.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)
  filter_upwards [hle', self_mem_nhdsWithin] with t hfg ht
  simp only [zero_add, smul_eq_mul, Pi.sub_apply, hzero, sub_self, sub_zero]
  exact mul_nonneg (inv_nonneg.mpr ht.le) (sub_nonneg.mpr hfg)

/-- A differentiable upper support by half squared distance forces equality
in Cauchy--Schwarz, hence positive alignment of the incoming and outgoing
tangent vectors. -/
theorem sameDirection_of_energy_firstVariation_right
    {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (e : E → ℝ) (D : E →L[ℝ] ℝ) (c : ℝ → E)
    (K : E →L[ℝ] Y) (y ξ : E) (T : Y)
    (he : HasFDerivAt e D y) (hc : HasDerivAt c ξ 0) (hc0 : c 0 = y)
    (hformula : D ξ = inner ℝ T (K ξ))
    (hsupport : (fun s : ℝ ↦
      (1 / 2 : ℝ) * (‖T‖ + s * ‖K ξ‖) ^ 2) ≤ᶠ[𝓝[Ici (0 : ℝ)] 0]
        (fun s ↦ e (c s)))
    (heq : e y = (1 / 2 : ℝ) * ‖T‖ ^ 2) :
    ‖K ξ‖ • T = ‖T‖ • K ξ := by
  have hec : HasDerivAt (fun s ↦ e (c s)) (D ξ) 0 := by
    change HasDerivAt (e ∘ c) (D ξ) 0
    have he' : HasFDerivAt e D (c 0) := by simpa only [hc0] using he
    exact he'.comp_hasDerivAt 0 hc
  have hbase : HasDerivAt (fun s : ℝ ↦ ‖T‖ + s * ‖K ξ‖) ‖K ξ‖ 0 := by
    simpa only [zero_mul, add_zero, one_mul] using
      (hasDerivAt_id' (0 : ℝ)).mul_const ‖K ξ‖ |>.const_add ‖T‖
  have hlower : HasDerivAt (fun s : ℝ ↦
      (1 / 2 : ℝ) * (‖T‖ + s * ‖K ξ‖) ^ 2)
      (‖T‖ * ‖K ξ‖) 0 := by
    have hraw := (hbase.mul hbase).const_mul (1 / 2 : ℝ)
    have hraw' : HasDerivAt (fun s : ℝ ↦
        (1 / 2 : ℝ) * (‖T‖ + s * ‖K ξ‖) ^ 2)
        ((1 / 2 : ℝ) *
          (‖K ξ‖ * (‖T‖ + 0 * ‖K ξ‖) +
            (‖T‖ + 0 * ‖K ξ‖) * ‖K ξ‖)) 0 := by
      simpa only [pow_two, Pi.mul_apply] using hraw
    exact hraw'.congr_deriv (by ring)
  have hzero : (1 / 2 : ℝ) * (‖T‖ + (0 : ℝ) * ‖K ξ‖) ^ 2 =
      e (c 0) := by rw [hc0, heq]; ring
  have hslope : ‖T‖ * ‖K ξ‖ ≤ D ξ :=
    deriv_le_of_eventually_le_right hlower hec hsupport hzero
  have hcauchy : inner ℝ T (K ξ) ≤ ‖T‖ * ‖K ξ‖ := real_inner_le_norm _ _
  have hinner : inner ℝ T (K ξ) = ‖T‖ * ‖K ξ‖ := by
    rw [hformula] at hslope
    exact le_antisymm hcauchy hslope
  exact inner_eq_norm_mul_iff_real.mp hinner

/-- If distance grows at the full outgoing speed and its differential is the
normalized pairing with the incoming radial tangent, then the incoming and
outgoing tangent vectors have the same direction. -/
theorem sameDirection_of_distance_firstVariation_right
    {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (d : E → ℝ) (D : E →L[ℝ] ℝ) (c : ℝ → E)
    (K : E →L[ℝ] Y) (y ξ : E) (T : Y)
    (hd : HasFDerivAt d D y) (hc : HasDerivAt c ξ 0) (hc0 : c 0 = y)
    (hformula : D ξ = inner ℝ T (K ξ) / ‖T‖) (hT : T ≠ 0)
    (heq : (fun s ↦ d (c s)) =ᶠ[𝓝[Ici (0 : ℝ)] 0]
      (fun s ↦ d y + s * ‖K ξ‖)) :
    ‖K ξ‖ • T = ‖T‖ • K ξ := by
  have hdc : HasDerivAt (fun s ↦ d (c s)) (D ξ) 0 := by
    change HasDerivAt (d ∘ c) (D ξ) 0
    have hd' : HasFDerivAt d D (c 0) := by simpa only [hc0] using hd
    exact hd'.comp_hasDerivAt 0 hc
  have hline : HasDerivAt
      (fun s : ℝ ↦ d y + s * ‖K ξ‖) ‖K ξ‖ 0 := by
    simpa only [id_eq, one_mul] using
      (hasDerivAt_id' (0 : ℝ)).mul_const ‖K ξ‖ |>.const_add (d y)
  have hslope : D ξ = ‖K ξ‖ :=
    deriv_eq_of_eventuallyEq_right hdc hline heq (by simp [hc0])
  have hinner : inner ℝ T (K ξ) = ‖T‖ * ‖K ξ‖ := by
    have hdiv : inner ℝ T (K ξ) / ‖T‖ = ‖K ξ‖ :=
      hformula.symm.trans hslope
    simpa [mul_comm] using (div_eq_iff (norm_ne_zero_iff.mpr hT)).mp hdiv
  exact inner_eq_norm_mul_iff_real.mp hinner

/-- If distance decreases at the full speed of a right-sided curve, the
curve tangent is opposite to the terminal radial tangent. -/
theorem oppositeDirection_of_distance_firstVariation_right
    {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (d : E → ℝ) (D : E →L[ℝ] ℝ) (c : ℝ → E)
    (K : E →L[ℝ] Y) (y ξ : E) (T : Y)
    (hd : HasFDerivAt d D y) (hc : HasDerivAt c ξ 0) (hc0 : c 0 = y)
    (hformula : D ξ = inner ℝ T (K ξ) / ‖T‖) (hT : T ≠ 0)
    (heq : (fun s ↦ d (c s)) =ᶠ[𝓝[Ici (0 : ℝ)] 0]
      (fun s ↦ d y - s * ‖K ξ‖)) :
    ‖K ξ‖ • T = -(‖T‖ • K ξ) := by
  have hdc : HasDerivAt (fun s ↦ d (c s)) (D ξ) 0 := by
    change HasDerivAt (d ∘ c) (D ξ) 0
    have hd' : HasFDerivAt d D (c 0) := by simpa only [hc0] using hd
    exact hd'.comp_hasDerivAt 0 hc
  have hline : HasDerivAt
      (fun s : ℝ ↦ d y - s * ‖K ξ‖) (-‖K ξ‖) 0 := by
    simpa using
      ((hasDerivAt_id' (0 : ℝ)).mul_const ‖K ξ‖).const_sub (d y)
  have hslope : D ξ = -‖K ξ‖ :=
    deriv_eq_of_eventuallyEq_right hdc hline heq (by simp [hc0])
  have hinner : inner ℝ T (K ξ) = -(‖T‖ * ‖K ξ‖) := by
    have hdiv : inner ℝ T (K ξ) / ‖T‖ = -‖K ξ‖ :=
      hformula.symm.trans hslope
    have hm := (div_eq_iff (norm_ne_zero_iff.mpr hT)).mp hdiv
    nlinarith
  have hinnerNeg : inner ℝ T (-K ξ) = ‖T‖ * ‖-K ξ‖ := by
    rw [inner_neg_right, hinner, norm_neg]
    ring
  have halign := inner_eq_norm_mul_iff_real.mp hinnerNeg
  simpa only [norm_neg, smul_neg] using halign

namespace CurveConnection

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Reading a differentiable manifold curve in any extended chart containing
its base point produces an ordinary coordinate derivative, and the chart's
coordinate frame sends that derivative back to the original tangent vector. -/
theorem exists_chart_hasDerivAt_coordinateFrameCombination_eq
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (γ : ℝ → M) {t : ℝ} {v : TM (γ t)}
    (hγ : HasMFDerivAt (𝓘(ℝ, ℝ)) I γ t (timeTangentMap (I := I) t v))
    (hsource : γ t ∈ (extChartAt I x₀).source) :
    ∃ ξ : E,
      HasDerivAt (fun s ↦ extChartAt I x₀ (γ s)) ξ t ∧
      LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := x₀) b ξ (γ t) = v := by
  have hsource' : γ t ∈ (chartAt H x₀).source := by
    rwa [← extChartAt_source (I := I) x₀]
  have hchart := hasMFDerivAt_extChartAt (I := I) hsource'
  have hcomp := hchart.comp t hγ
  have hdiff : DifferentiableAt ℝ (fun s ↦ extChartAt I x₀ (γ s)) t :=
    hcomp.mdifferentiableAt.differentiableAt
  let ξ : E := deriv (fun s ↦ extChartAt I x₀ (γ s)) t
  have hderiv : HasDerivAt (fun s ↦ extChartAt I x₀ (γ s)) ξ t :=
    hdiff.hasDerivAt
  refine ⟨ξ, hderiv, ?_⟩
  have htarget : extChartAt I x₀ (γ t) ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hsource
  have hinv := hasMFDerivAt_inverseChartCurve_of_hasDerivAt
    (I := I) (M := M) x₀ b (fun s ↦ extChartAt I x₀ (γ s)) htarget hderiv
  have hstay : γ ⁻¹' (extChartAt I x₀).source ∈ 𝓝 t :=
    hγ.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := I) x₀).mem_nhds hsource)
  have heq : ((extChartAt I x₀).symm ∘ fun s ↦ extChartAt I x₀ (γ s)) =ᶠ[𝓝 t] γ := by
    filter_upwards [hstay] with s hs
    exact (extChartAt I x₀).left_inv hs
  have hinv' := hinv.congr_of_eventuallyEq heq.symm
  have hmaps := hasMFDerivAt_unique hinv' hγ
  rw [(extChartAt I x₀).left_inv hsource] at hmaps
  exact timeTangentMap_injective (I := I) t hmaps

end CurveConnection

end BonnetMyersEntry
