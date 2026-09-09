/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanVariationalInverse
public import LeanPool.NavierStokesAndEuler.Euler.TimeH1OperatorProduct

@[expose] public section

/-!
# Genuine H¹ label displacements and mean variational tests

The mean Hilbert model uses derivatives of the physical displacement.  A C¹
inverse deformation converts its terminal primitive to an actual H¹ solenoidal
label path, with a constructed Bochner L² derivative.  Conversely, each genuine
solenoidal terminal primitive yields an admissible physical test through F.
-/

noncomputable section


namespace EulerMeanVariationalInverse

open MeasureTheory Set Filter InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerTimeH1OperatorProduct
  EulerMeanSolenoidal EulerVolterraConvolution
open scoped Topology

variable (T : ℝ) (hT : 0 ≤ T)
  (FInv FInv' : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))

/-- The actual L² time derivative of the label path `FInv η`. -/
def labelDerivative : meanDerivatives T hT FInv →L[ℝ] TimeLp T L2 :=
  (productDerivative T hT FInv FInv').comp (meanDerivatives T hT FInv).subtypeL

/-- The real representative of the label displacement. -/
def labelPath (u : meanDerivatives T hT FInv) : ℝ → L2 :=
  productPrimitive T hT FInv (u : TimeLp T L2)

/-- The label path takes values in the actual ordinary solenoidal space. -/
theorem labelPath_solenoidal (u : meanDerivatives T hT FInv) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) T) : labelPath T hT FInv u t ∈ solenoidalSpace := by
  change FInv (projIcc 0 T hT t) (realPrimitive T (u : TimeLp T L2) t) ∈ solenoidalSpace
  simpa only [projIcc_of_mem hT ht, terminalPrimitive_apply] using u.property ⟨t, ht⟩

variable (hFInv : ∀ t : Icc (0 : ℝ) T,
  HasDerivWithinAt (extendPath T hT FInv) (FInv' t) (Icc (0 : ℝ) T) t)

include hFInv in
/-- The actual label displacement is absolutely continuous. -/
theorem labelPath_absolutelyContinuous (u : meanDerivatives T hT FInv) :
    AbsolutelyContinuousOnInterval (labelPath T hT FInv u) 0 T :=
  productPrimitive_absolutelyContinuous T hT FInv FInv' hFInv (u : TimeLp T L2)

include hFInv in
/-- Its L² derivative is obtained from the literal product rule. -/
theorem labelPath_hasDerivAt_ae (u : meanDerivatives T hT FInv) :
    ∀ᵐ t ∂timeMeasure T,
      HasDerivAt (labelPath T hT FInv u) (labelDerivative T hT FInv FInv' u t) t :=
  productPrimitive_hasDerivAt_ae T hT FInv FInv' hFInv (u : TimeLp T L2)

include hFInv in
/-- Integration recovers the actual H¹ label path from that derivative. -/
theorem labelPath_eq_realPrimitive (u : meanDerivatives T hT FInv) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) T) :
    labelPath T hT FInv u t = realPrimitive T (labelDerivative T hT FInv FInv' u) t :=
  productPrimitive_eq_realPrimitive T hT FInv FInv' hFInv (u : TimeLp T L2) t ht

include hFInv in
/-- Differentiating a path in the closed solenoidal subspace preserves its
constraint almost everywhere; this is an actual L² membership statement. -/
theorem labelDerivative_solenoidal_ae (u : meanDerivatives T hT FInv) :
    ∀ᵐ t ∂timeMeasure T, labelDerivative T hT FInv FInv' u t ∈ solenoidalSpace := by
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Ioo (0 : ℝ) T := by
    change ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), t ∈ Ioo (0 : ℝ) T
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hmem, labelPath_hasDerivAt_ae T hT FInv FInv' hFInv u] with t ht hd
  have hp := solenoidalProjection.hasFDerivAt.comp_hasDerivAt t hd
  have heq : labelPath T hT FInv u =ᶠ[𝓝 t]
      fun s => solenoidalProjection (labelPath T hT FInv u s) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact (solenoidalSpace.starProjection_eq_self_iff.mpr
      (labelPath_solenoidal T hT FInv u s hs)).symm
  exact solenoidalSpace.starProjection_eq_self_iff.mp
    ((hp.congr_of_eventuallyEq heq).unique hd)

/-- The norm comparison required by the source H¹ model follows from the
actual coefficient bounds and the sharp terminal Poincaré bound. -/
theorem labelDerivative_norm_le (u : meanDerivatives T hT FInv) :
    ‖labelDerivative T hT FInv FInv' u‖ ≤
      (‖FInv'‖ * Real.sqrt (T^2/2) + ‖FInv‖) * ‖u‖ :=
  productDerivative_norm_le T hT FInv FInv' (u : TimeLp T L2)

/-- Squaring the genuine derivative comparison gives the source energy control. -/
theorem labelDerivative_norm_sq_le (u : meanDerivatives T hT FInv) :
    ‖labelDerivative T hT FInv FInv' u‖^2 ≤
      (‖FInv'‖ * Real.sqrt (T^2/2) + ‖FInv‖)^2 * ‖u‖^2 := by
  calc
    _ ≤ ((‖FInv'‖ * Real.sqrt (T^2/2) + ‖FInv‖) * ‖u‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (labelDerivative_norm_le T hT FInv FInv' u) 2
    _ = _ := mul_pow _ _ _

variable (F F' : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))

/-- Restrict the physical deformation to actual solenoidal label fields. -/
def solenoidalFrame : C(Icc (0 : ℝ) T, solenoidalSpace →L[ℝ] L2) :=
  ⟨fun t => (F t).comp solenoidalSpace.subtypeL,
    F.continuous.clm_comp continuous_const⟩

/-- Differentiating the restricted frame is literal bounded-map composition. -/
theorem solenoidalFrame_hasDerivWithinAt
    (hF : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F' t) (Icc (0 : ℝ) T) t) :
    ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT (solenoidalFrame T F))
        (solenoidalFrame T F' t) (Icc (0 : ℝ) T) t := by
  intro t
  have h := (hF t).clm_comp
    (hasDerivWithinAt_const (t : ℝ) (Icc (0 : ℝ) T) solenoidalSpace.subtypeL)
  change HasDerivWithinAt (fun s => (extendPath T hT F s).comp solenoidalSpace.subtypeL)
    ((F' t).comp solenoidalSpace.subtypeL) (Icc (0 : ℝ) T) t
  simpa only [ContinuousLinearMap.comp_zero, add_zero] using h

variable (hF : ∀ t : Icc (0 : ℝ) T,
  HasDerivWithinAt (extendPath T hT F) (F' t) (Icc (0 : ℝ) T) t)
  (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (F t x) = x)

include hF hInv in
/-- Every solenoidal terminal H¹ path supplies an admissible physical test. -/
theorem productDerivative_mem_mean (v : TimeLp T solenoidalSpace) :
    productDerivative T hT (solenoidalFrame T F) (solenoidalFrame T F') v ∈
      meanDerivatives T hT FInv := by
  intro t
  rw [terminalPrimitive_productDerivative T hT (solenoidalFrame T F)
    (solenoidalFrame T F') (solenoidalFrame_hasDerivWithinAt T hT F F' hF) v t]
  change FInv t (F t ((terminalPrimitive T hT v t : solenoidalSpace) : L2)) ∈ solenoidalSpace
  rw [hInv]
  exact (terminalPrimitive T hT v t).property

/-- A genuine bounded map from solenoidal label derivatives to admissible mean tests. -/
def meanTestMap : TimeLp T solenoidalSpace →L[ℝ] meanDerivatives T hT FInv :=
  (productDerivative T hT (solenoidalFrame T F) (solenoidalFrame T F')).codRestrict
    (meanDerivatives T hT FInv) (productDerivative_mem_mean T hT FInv F F' hF hInv)

/-- The test derivative is the actual product-rule L² field. -/
@[simp] theorem meanTestMap_coe (v : TimeLp T solenoidalSpace) :
    (meanTestMap T hT FInv F F' hF hInv v : TimeLp T L2) =
      productDerivative T hT (solenoidalFrame T F) (solenoidalFrame T F') v := rfl

/-- Its displacement primitive is the actual physical test `F b`. -/
theorem meanTestMap_primitive (v : TimeLp T solenoidalSpace) :
    meanPrimitive T hT FInv (meanTestMap T hT FInv F F' hF hInv v) =
      timeMultiplier T hT (solenoidalFrame T F) (primitiveTimeLp T hT v) :=
  primitiveTimeLp_productDerivative T hT (solenoidalFrame T F) (solenoidalFrame T F')
    (solenoidalFrame_hasDerivWithinAt T hT F F' hF) v

/-- The initial trace of the physical test is exactly `F(0) b(0)`. -/
theorem meanTestMap_trace (v : TimeLp T solenoidalSpace) :
    meanTrace T hT FInv (meanTestMap T hT FInv F F' hF hInv v) =
      F ⟨0, le_rfl, hT⟩ ((initialTrace T hT v : solenoidalSpace) : L2) :=
  initialTrace_productDerivative T hT (solenoidalFrame T F) (solenoidalFrame T F')
    (solenoidalFrame_hasDerivWithinAt T hT F F' hF) v

/-- Therefore zero-endpoint label tests remove both actual initial boundary terms. -/
theorem meanTestMap_trace_zero (v : TimeLp T solenoidalSpace) (hv : initialTrace T hT v = 0) :
    meanTrace T hT FInv (meanTestMap T hT FInv F F' hF hInv v) = 0 := by
  rw [meanTestMap_trace T hT FInv F F' hF hInv v, hv]
  exact map_zero _

end EulerMeanVariationalInverse
