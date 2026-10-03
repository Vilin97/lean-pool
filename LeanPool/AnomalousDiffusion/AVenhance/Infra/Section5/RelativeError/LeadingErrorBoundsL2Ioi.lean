/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorBoundsL2

/-! # `L²((0,1)×𝕋²)` bookkeeping with regularity only on the open half space

`LeadingErrorBoundsL2` integrates functions continuous on `[0,∞) × ℝ²` over the time cell.  The
field `∇HTilde_m` is only known to be continuous on `(0,∞) × ℝ²` (at `t = 0` it sees the arbitrary
negative-time extension of `T`), so here the dominating function is split as `B + |∇HTilde_m|`
    with `B`
continuous on `[0,∞) × ℝ²` and the `∇HTilde_m` part only continuous on the open half space.  If the
    error field is
square integrable then so is `∇HTilde_m`; if it is not, the Bochner integral defining its norm
    vanishes. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance

theorem abs_apply_le_sqrt_vecNormSq (v : Vec 2) (i : Fin 2) :
    |v i| ≤ Real.sqrt (vecNormSq v) := by
  apply Real.abs_le_sqrt
  simp only [vecNormSq, vecDot, Fin.sum_univ_two]
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

theorem continuousOn_sqrt_vecNormSq {s : Set (ℝ × Vec 2)} {V : ℝ × Vec 2 → Vec 2}
    (h : ∀ i, ContinuousOn (fun p => V p i) s) :
    ContinuousOn (fun p => Real.sqrt (vecNormSq (V p))) s := by
  refine ContinuousOn.sqrt ?_
  simp only [vecNormSq, vecDot, Fin.sum_univ_two]
  exact ((h 0).mul (h 0)).add ((h 1).mul (h 1))

theorem integral_sqrt_vecNormSq_sq (V : ℝ → Vec 2 → Vec 2) :
    ∫ p in timeCube, Real.sqrt (vecNormSq (V p.1 p.2)) ^ 2 = spaceTimeGradNormSq V := by
  unfold spaceTimeGradNormSq
  congr 1
  funext p
  exact Real.sq_sqrt (vecNormSq_nonneg_of_vec2 _)

/-- Functions continuous on the open half space are a.e. strongly measurable on the time cell. -/
theorem aestronglyMeasurable_timeCube_of_continuousOn_Ioi {f : ℝ × Vec 2 → ℝ}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ) ×ˢ Set.univ)) :
    AEStronglyMeasurable f (volume.restrict timeCube) := by
  have h := hf.aestronglyMeasurable (μ := volume)
    (measurableSet_Ioi.prod MeasurableSet.univ)
  refine h.mono_measure (Measure.restrict_mono ?_ le_rfl)
  exact Set.prod_mono (Set.Ioo_subset_Ioi_self) (Set.subset_univ _)

theorem LeadingErrorBoundsL2Ioi.vecNormSq_embed' (a : ℝ) : vecNormSq (![a, 0] : Vec 2) = a ^ 2 := by
  simp [vecNormSq, vecDot, Fin.sum_univ_two, sq]

theorem LeadingErrorBoundsL2Ioi.embed_add' (a b : ℝ) : (![a, 0] : Vec 2) + ![b, 0] = ![a + b, 0]
    := by
  ext i
  fin_cases i <;> simp

/-- Scalar `L²` triangle inequality on the time cell for square-integrable functions. -/
theorem sqrt_setIntegral_sq_add_le_of_integrable {f g : ℝ × Vec 2 → ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict timeCube))
    (hgm : AEStronglyMeasurable g (volume.restrict timeCube))
    (hf : Integrable (fun p => f p ^ 2) (volume.restrict timeCube))
    (hg : Integrable (fun p => g p ^ 2) (volume.restrict timeCube)) :
    Real.sqrt (∫ p in timeCube, (f p + g p) ^ 2) ≤
      Real.sqrt (∫ p in timeCube, f p ^ 2) + Real.sqrt (∫ p in timeCube, g p ^ 2) := by
  have hfg : Integrable (fun p => f p * g p) (volume.restrict timeCube) := by
    refine Integrable.mono' (hf.add hg) (hfm.mul hgm) (Filter.Eventually.of_forall fun p => ?_)
    have h1 := two_mul_le_add_sq |f p| |g p|
    have h2 : |f p * g p| = |f p| * |g p| := abs_mul _ _
    rw [Real.norm_eq_abs, h2]
    simp only [Pi.add_apply, sq_abs] at h1 ⊢
    nlinarith [sq_nonneg (f p), sq_nonneg (g p), abs_nonneg (f p), abs_nonneg (g p)]
  have key := relative_vector_integral_L2_add (μ := volume.restrict timeCube)
    (f := fun p => (![f p, 0] : Vec 2)) (g := fun p => (![g p, 0] : Vec 2))
    (by simpa only [LeadingErrorBoundsL2Ioi.vecNormSq_embed'] using hf)
    (by simpa only [LeadingErrorBoundsL2Ioi.vecNormSq_embed'] using hg)
    (by
      refine hfg.congr (Filter.Eventually.of_forall fun p => ?_)
      simp [vecDot, Fin.sum_univ_two])
  simpa only [LeadingErrorBoundsL2Ioi.embed_add', LeadingErrorBoundsL2Ioi.vecNormSq_embed'] using
      key

/-- `L²` triangle inequality for a weighted sum of three functions continuous on the closed
half space. -/
theorem sqrt_setIntegral_sq_three_le {f₁ f₂ f₃ : ℝ × Vec 2 → ℝ} {c₁ c₂ c₃ : ℝ}
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (h₁ : ContinuousOn f₁ (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (h₂ : ContinuousOn f₂ (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (h₃ : ContinuousOn f₃ (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    Real.sqrt (∫ p in timeCube, (c₁ * f₁ p + c₂ * f₂ p + c₃ * f₃ p) ^ 2) ≤
      c₁ * Real.sqrt (∫ p in timeCube, f₁ p ^ 2) + c₂ * Real.sqrt (∫ p in timeCube, f₂ p ^ 2) +
        c₃ * Real.sqrt (∫ p in timeCube, f₃ p ^ 2) := by
  have k₁ : ContinuousOn (fun p => c₁ * f₁ p) (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    continuousOn_const.mul h₁
  have k₂ : ContinuousOn (fun p => c₂ * f₂ p) (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    continuousOn_const.mul h₂
  have k₃ : ContinuousOn (fun p => c₃ * f₃ p) (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    continuousOn_const.mul h₃
  have a2 := sqrt_setIntegral_sq_add_le (k₁.add k₂) k₃
  have a3 := sqrt_setIntegral_sq_add_le k₁ k₂
  simp only [Pi.add_apply] at a2 a3
  rw [sqrt_setIntegral_sq_const_mul hc₁, sqrt_setIntegral_sq_const_mul hc₂] at a3
  rw [sqrt_setIntegral_sq_const_mul hc₃] at a2
  linarith

/-- If `F - G` is componentwise dominated by `B`, continuous on the closed half space, and every
component of `G` is continuous on the open half space, then
`‖F‖_{L²} ≤ 2 (‖B‖_{L²} + ‖G‖_{L²})`. -/
theorem sqrt_spaceTimeGradNormSq_le_of_sub_component_le {F G : ℝ → Vec 2 → Vec 2}
    {B : ℝ × Vec 2 → ℝ} (hB : ContinuousOn B (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hG : ∀ i, ContinuousOn (fun p : ℝ × Vec 2 => G p.1 p.2 i) (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    (hF : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ x : Vec 2, ∀ i : Fin 2, |F t x i - G t x i| ≤ B (t, x)) :
    Real.sqrt (spaceTimeGradNormSq F) ≤
      2 * (Real.sqrt (∫ p in timeCube, B p ^ 2) + Real.sqrt (spaceTimeGradNormSq G)) := by
  have hIoi : Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2)) ⊆ Set.Ici (0 : ℝ) ×ˢ Set.univ :=
    Set.prod_mono Set.Ioi_subset_Ici_self le_rfl
  have hBo : ContinuousOn B (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := hB.mono hIoi
  have hB2 : Integrable (fun p => B p ^ 2) (volume.restrict timeCube) :=
    integrable_timeCube_of_continuousOn (hB.pow 2)
  by_cases hIF : Integrable (fun p : ℝ × Vec 2 => vecNormSq (F p.1 p.2)) (volume.restrict timeCube)
  swap
  · have h0 : spaceTimeGradNormSq F = 0 := by
      unfold spaceTimeGradNormSq
      exact integral_undef hIF
    rw [h0, Real.sqrt_zero]
    positivity
  set gn : ℝ × Vec 2 → ℝ := fun p => Real.sqrt (vecNormSq (G p.1 p.2)) with hgn
  have hgnc : ContinuousOn gn (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := continuousOn_sqrt_vecNormSq hG
  have hgnm : AEStronglyMeasurable gn (volume.restrict timeCube) :=
    aestronglyMeasurable_timeCube_of_continuousOn_Ioi hgnc
  have hBm : AEStronglyMeasurable B (volume.restrict timeCube) :=
    aestronglyMeasurable_timeCube_of_continuousOn_Ioi hBo
  -- `‖G‖²` is integrable on the time cell
  have hgn2 : Integrable (fun p => gn p ^ 2) (volume.restrict timeCube) := by
    have hdom : Integrable (fun p : ℝ × Vec 2 => 2 * vecNormSq (F p.1 p.2) + 4 * B p ^ 2)
        (volume.restrict timeCube) := (hIF.const_mul 2).add (hB2.const_mul 4)
    refine Integrable.mono' hdom (hgnm.pow 2) ?_
    rw [ae_restrict_iff' measurableSet_timeCube]
    refine Filter.Eventually.of_forall fun p hp => ?_
    have hcomp : ∀ i : Fin 2, G p.1 p.2 i * G p.1 p.2 i ≤
        2 * (F p.1 p.2 i * F p.1 p.2 i) + 2 * B p ^ 2 := by
      intro i
      have h1 := hF p.1 hp.1 p.2 i
      have h2 : |G p.1 p.2 i| ≤ |F p.1 p.2 i| + B p := by
        have := abs_sub_abs_le_abs_sub (G p.1 p.2 i) (F p.1 p.2 i)
        rw [abs_sub_comm] at this
        have h1' : |F p.1 p.2 i - G p.1 p.2 i| ≤ B p := h1
        linarith
      have h3 : 0 ≤ B p := (abs_nonneg _).trans h1
      have h4 : |G p.1 p.2 i| ^ 2 ≤ (|F p.1 p.2 i| + B p) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h2 2
      rw [sq_abs] at h4
      rw [← sq, ← sq]
      nlinarith [sq_abs (F p.1 p.2 i), sq_nonneg (|F p.1 p.2 i| - B p)]
    have hsq : gn p ^ 2 = vecNormSq (G p.1 p.2) := Real.sq_sqrt (vecNormSq_nonneg_of_vec2 _)
    rw [Real.norm_of_nonneg (sq_nonneg _), hsq]
    have := hcomp 0
    have := hcomp 1
    simp only [vecNormSq, vecDot, Fin.sum_univ_two]
    nlinarith
  -- the dominating function `B + ‖G‖`
  have hD2 : Integrable (fun p => (B p + gn p) ^ 2) (volume.restrict timeCube) := by
    refine Integrable.mono' ((hB2.const_mul 2).add (hgn2.const_mul 2)) ((hBm.add hgnm).pow 2) ?_
    refine Filter.Eventually.of_forall fun p => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (B p - gn p)]
  have hint : Integrable (fun p : ℝ × Vec 2 => (2 * (B p + gn p)) ^ 2) (volume.restrict timeCube)
      := by
    refine (hD2.const_mul 4).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only
    ring
  have hle : spaceTimeGradNormSq F ≤ ∫ p in timeCube, (2 * (B p + gn p)) ^ 2 := by
    unfold spaceTimeGradNormSq
    refine integral_mono_of_nonneg ?_ hint ?_
    · exact Filter.Eventually.of_forall fun p => vecNormSq_nonneg_of_vec2 _
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_timeCube]
      refine Filter.Eventually.of_forall fun p hp => ?_
      have hc : ∀ i : Fin 2, |F p.1 p.2 i| ≤ B p + gn p := by
        intro i
        have h1 := hF p.1 hp.1 p.2 i
        have h2 := abs_apply_le_sqrt_vecNormSq (G p.1 p.2) i
        have h3 : |F p.1 p.2 i| ≤ |F p.1 p.2 i - G p.1 p.2 i| + |G p.1 p.2 i| := by
          calc |F p.1 p.2 i| = |(F p.1 p.2 i - G p.1 p.2 i) + G p.1 p.2 i| := by ring_nf
            _ ≤ _ := abs_add_le _ _
        have h1' : |F p.1 p.2 i - G p.1 p.2 i| ≤ B p := h1
        have h2' : |G p.1 p.2 i| ≤ gn p := h2
        linarith
      have h0' := abs_le.mp (hc 0)
      have h1' := abs_le.mp (hc 1)
      simp only [vecNormSq, vecDot, Fin.sum_univ_two]
      nlinarith [h0'.1, h0'.2, h1'.1, h1'.2]
  have htri := sqrt_setIntegral_sq_add_le_of_integrable hBm hgnm hB2 hgn2
  rw [integral_sqrt_vecNormSq_sq G] at htri
  calc Real.sqrt (spaceTimeGradNormSq F)
      ≤ Real.sqrt (∫ p in timeCube, (2 * (B p + gn p)) ^ 2) := Real.sqrt_le_sqrt hle
    _ = 2 * Real.sqrt (∫ p in timeCube, (B p + gn p) ^ 2) :=
        sqrt_setIntegral_sq_const_mul (by norm_num) (fun p => B p + gn p)
    _ ≤ _ := mul_le_mul_of_nonneg_left htri (by norm_num)

end AVenhance.Infra.Section5.RelativeError
