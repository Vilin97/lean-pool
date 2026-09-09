/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodicUniqueness
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.CompactTimeIntegral
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ScalarEnergyBound
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.CompactForceBound

@[expose] public section

/-!
# Energy of compactly supported fields on Euclidean three-space

All integrals in this module are the standard Lebesgue volume integrals on
`ProblemStatement.Space`. Compact support supplies integrability; no finite
replacement measure or convention about nonintegrable functions is used.
-/


noncomputable section

open Set Filter MeasureTheory Function
open scoped Topology BigOperators ContDiff InnerProductSpace

namespace NavierStokesR3.CompactEnergy

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

private theorem infty_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  simpa only [ENat.coe_top_add_one] using (le_rfl : (∞ : WithTop ℕ∞) ≤ ∞)

theorem compact_inner_left {f g : Space → Space} (hf : HasCompactSupport f) :
    HasCompactSupport (fun x => ⟪f x, g x⟫_ℝ) := by
  apply hf.mono
  intro x hx
  contrapose! hx
  simp only [mem_support, not_not] at hx ⊢
  rw [hx, inner_zero_left]

theorem compact_norm_sq {f : Space → Space} (hf : HasCompactSupport f) :
    HasCompactSupport (fun x => ‖f x‖ ^ 2) := by
  exact hf.comp_left (g := fun v : Space => ‖v‖ ^ 2) (by simp)

theorem integrable_norm_sq {f : Space → Space} (hf : Continuous f)
    (hcf : HasCompactSupport f) : Integrable (fun x => ‖f x‖ ^ 2) :=
  (hf.norm.pow 2).integrable_of_hasCompactSupport (compact_norm_sq hcf)

theorem compact_component {f : Space → Space} (hf : HasCompactSupport f) (i : Fin 3) :
    HasCompactSupport (fun x => f x i) :=
  hf.comp_left (g := fun v : Space => v i) rfl

theorem integrable_inner_left {f g : Space → Space} (hf : Continuous f)
    (hg : Continuous g) (hcf : HasCompactSupport f) :
    Integrable (fun x => ⟪f x, g x⟫_ℝ) :=
  (hf.inner hg).integrable_of_hasCompactSupport (compact_inner_left hcf)

theorem compact_partial {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Space → V} (hf : HasCompactSupport f) (i : Fin 3) :
    HasCompactSupport (spatialPartial i f) :=
  hf.fderiv_apply ℝ (coordinateVector i)

theorem integral_partial_eq_zero {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) (i : Fin 3) :
    (∫ x, spatialPartial i f x) = 0 := by
  have hi : Integrable (spatialPartial i f) :=
    (spatial_partial_contDiff hf i).continuous.integrable_of_hasCompactSupport
    (compact_partial hcf i)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := fun _ : Space => (1 : ℝ)) (g := f) (v := coordinateVector i)
    (by simp)
    (by simpa only [spatialPartial, one_mul] using! hi)
    (by simpa only [one_mul] using hf.continuous.integrable_of_hasCompactSupport hcf)
    (fun x _ => differentiableAt_const (1 : ℝ)) (fun x _ => hf.differentiable (by simp) x)
  simpa [spatialPartial] using h

theorem integral_mul_partial {f g : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hcf : HasCompactSupport f) (i : Fin 3) :
    (∫ x, f x * spatialPartial i g x) =
      -(∫ x, g x * spatialPartial i f x) := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := f) (g := g) (v := coordinateVector i)
    (((spatial_partial_contDiff hf i).continuous.mul hg.continuous).integrable_of_hasCompactSupport
      (compact_partial hcf i).mul_right)
    ((hf.continuous.mul (spatial_partial_contDiff hg i).continuous).integrable_of_hasCompactSupport
      hcf.mul_right)
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hcf.mul_right)
    (fun x _ => hf.differentiable (by simp) x) (fun x _ => hg.differentiable (by simp) x)
  simpa only [spatialPartial, mul_comm] using h

/-- Integration against a compactly supported vector field transfers a
directional derivative to its divergence. -/
theorem integral_fderiv_apply {f : Space → ℝ} {v : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v) (hcv : HasCompactSupport v) :
    (∫ x, fderiv ℝ f x (v x)) =
      -(∫ x, f x * ∑ i : Fin 3, spatialPartial i v x i) := by
  have hleft : (fun x => fderiv ℝ f x (v x)) =
      (fun x => ∑ i : Fin 3, v x i * spatialPartial i f x) := by
    funext x
    exact fderiv_apply_eq_sum f x (v x)
  have hright : (fun x => f x * ∑ i : Fin 3, spatialPartial i v x i) =
      (fun x => ∑ i : Fin 3, f x * spatialPartial i v x i) := by
    funext x
    exact Finset.mul_sum _ _ _
  have hIl (i : Fin 3) : Integrable (fun x => v x i * spatialPartial i f x) :=
    ((component_contDiff hv i).continuous.mul (spatial_partial_contDiff hf
      i).continuous).integrable_of_hasCompactSupport
      (compact_component hcv i).mul_right
  have hIr (i : Fin 3) : Integrable (fun x => f x * spatialPartial i v x i) :=
    (hf.continuous.mul (component_contDiff (spatial_partial_contDiff hv i)
      i).continuous).integrable_of_hasCompactSupport
      (compact_component (compact_partial hcv i) i).mul_left
  rw [hleft, hright, integral_finsetSum _ (fun i _ => hIl i),
    integral_finsetSum _ (fun i _ => hIr i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := integral_mul_partial (component_contDiff hv i) hf (compact_component hcv i) i
  simpa only [spatialPartial, fderiv_component hv] using h

theorem integral_fderiv_apply_zero {f : Space → ℝ} {v : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v) (hcv : HasCompactSupport v)
    (hdiv : ∀ x, (∑ i : Fin 3, spatialPartial i v x i) = 0) :
    (∫ x, fderiv ℝ f x (v x)) = 0 := by
  rw [integral_fderiv_apply hf hv hcv]
  simp only [hdiv, mul_zero, integral_zero, neg_zero]

/-- Divergence-free transport contributes zero to the whole-space energy. -/
theorem integral_transport_energy_zero {w v : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hv : ContDiff ℝ ∞ v) (hcv : HasCompactSupport v)
    (hdiv : ∀ x, (∑ i : Fin 3, spatialPartial i v x i) = 0) :
    (∫ x, ⟪w x, fderiv ℝ w x (v x)⟫_ℝ) = 0 := by
  have h := integral_fderiv_apply_zero (hw.norm_sq ℝ) hv hcv hdiv
  have hfun : (fun x => fderiv ℝ (fun y => ‖w y‖ ^ 2) x (v x)) =
      (fun x => 2 * ⟪w x, fderiv ℝ w x (v x)⟫_ℝ) := by
    funext x
    exact fderiv_normsq hw x (v x)
  rw [hfun, integral_const_mul] at h
  linarith

theorem integral_inner_partial {f g : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hcf : HasCompactSupport f) (i : Fin 3) :
    (∫ x, ⟪f x, spatialPartial i g x⟫_ℝ) =
      -(∫ x, ⟪spatialPartial i f x, g x⟫_ℝ) := by
  have h := integral_partial_eq_zero (hf.inner ℝ hg) (compact_inner_left hcf) i
  have hfun : spatialPartial i (fun x => ⟪f x, g x⟫_ℝ) =
      (fun x => ⟪f x, spatialPartial i g x⟫_ℝ + ⟪spatialPartial i f x, g x⟫_ℝ) := by
    funext x
    exact fderiv_inner hf hg x (coordinateVector i)
  rw [hfun] at h
  dsimp only [spatialPartial] at h ⊢
  rw [integral_add (integrable_inner_left hf.continuous
      (spatial_partial_contDiff hg i).continuous hcf)
    (integrable_inner_left (spatial_partial_contDiff hf i).continuous hg.continuous
      (compact_partial hcf i))] at h
  exact eq_neg_of_add_eq_zero_left h

theorem integral_laplacian_energy {u : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hcu : HasCompactSupport (fun x : Space => u (t, x))) :
    (∫ x, ⟪u (t, x), spatialLaplacian u t x⟫_ℝ) =
      -(∑ i : Fin 3, ∫ x, ‖spatialPartial i (fun y => u (t, y)) x‖ ^ 2) := by
  have hsum : (∫ x, ⟪u (t, x), spatialLaplacian u t x⟫_ℝ) =
      ∑ i : Fin 3, ∫ x, ⟪u (t, x),
        spatialPartial i (spatialPartial i (fun y => u (t, y))) x⟫_ℝ := by
    simp only [spatialLaplacian, inner_sum]
    exact integral_finsetSum _ (fun i _ => integrable_inner_left hu.continuous
      (spatial_partial_contDiff (spatial_partial_contDiff hu i) i).continuous hcu)
  rw [hsum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [spatialPartial, real_inner_self_eq_norm_sq] using!
    integral_inner_partial hu (spatial_partial_contDiff hu i) hcu i

/-- The pressure need not have compact support: the compact velocity already
makes every integration-by-parts product integrable. -/
theorem integral_pressure_energy_zero {u : VelocityField} {p : PressureField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hcu : HasCompactSupport (fun x : Space => u (t, x)))
    (hdiv : ∀ x, spatialDivergence u t x = 0) :
    (∫ x, ⟪u (t, x), pressureGradient p t x⟫_ℝ) = 0 := by
  have hfun : (fun x => ⟪u (t, x), pressureGradient p t x⟫_ℝ) =
      (fun x => fderiv ℝ (fun y => p (t, y)) x (u (t, x))) := by
    funext x
    exact inner_pressureGradient p t x (u (t, x))
  rw [hfun]
  exact integral_fderiv_apply_zero hp hu hcu hdiv

/-- The full squared spatial L2 norm with ordinary Euclidean volume. -/
def l2Sq (u : VelocityField) (t : ℝ) : ℝ := ∫ x : Space, ‖u (t, x)‖ ^ 2

def energyRate (u : VelocityField) (t : ℝ) : ℝ :=
  ∫ x : Space, 2 * ⟪u (t, x), temporalDerivative u t x⟫_ℝ

def dissipation (u : VelocityField) (t : ℝ) : ℝ :=
  ∑ i : Fin 3, ∫ x : Space, ‖spatialPartial i (fun y => u (t, y)) x‖ ^ 2

theorem dissipation_nonneg (u : VelocityField) (t : ℝ) : 0 ≤ dissipation u t :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

/-- The exact forced Navier--Stokes energy balance on all of Euclidean space. -/
theorem energy_balance {u f : VelocityField} {p : PressureField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hf : Continuous (fun x : Space => f (t, x)))
    (hcu : HasCompactSupport (fun x : Space => u (t, x)))
    (hdiv : ∀ x, spatialDivergence u t x = 0)
    (hNS : ∀ x, navierStokesResidual u p t x = f (t, x)) :
    energyRate u t = -2 * dissipation u t + 2 * ∫ x, ⟪u (t, x), f (t, x)⟫_ℝ := by
  have hL := (hu.inner ℝ (spatialLaplacian_contDiff hu)).continuous
  have hN := (hu.inner ℝ ((hu.fderiv_right infty_add_one_le).clm_apply hu)).continuous
  have hP := (hu.inner ℝ (pressureGradient_contDiff hp)).continuous
  have hF : Continuous (fun x : Space => ⟪u (t, x), f (t, x)⟫_ℝ) := hu.continuous.inner hf
  have hiL : Integrable (fun x => ⟪u (t, x), spatialLaplacian u t x⟫_ℝ) :=
    hL.integrable_of_hasCompactSupport (compact_inner_left hcu)
  have hiN : Integrable (fun x => ⟪u (t, x), advection u t x⟫_ℝ) :=
    hN.integrable_of_hasCompactSupport (compact_inner_left hcu)
  have hiP : Integrable (fun x => ⟪u (t, x), pressureGradient p t x⟫_ℝ) :=
    hP.integrable_of_hasCompactSupport (compact_inner_left hcu)
  have hiF : Integrable (fun x => ⟪u (t, x), f (t, x)⟫_ℝ) :=
    hF.integrable_of_hasCompactSupport (compact_inner_left hcu)
  have hiLN : Integrable (fun x => ⟪u (t, x), spatialLaplacian u t x⟫_ℝ -
      ⟪u (t, x), advection u t x⟫_ℝ) := hiL.sub hiN
  have hiLNP : Integrable (fun x => ⟪u (t, x), spatialLaplacian u t x⟫_ℝ -
      ⟪u (t, x), advection u t x⟫_ℝ - ⟪u (t, x), pressureGradient p t x⟫_ℝ) := hiLN.sub hiP
  have hEq : (fun x => ⟪u (t, x), temporalDerivative u t x⟫_ℝ) =
      (fun x => ⟪u (t, x), spatialLaplacian u t x⟫_ℝ -
        ⟪u (t, x), advection u t x⟫_ℝ - ⟪u (t, x), pressureGradient p t x⟫_ℝ +
        ⟪u (t, x), f (t, x)⟫_ℝ) := by
    funext x
    have heq : temporalDerivative u t x =
        spatialLaplacian u t x - advection u t x - pressureGradient p t x + f (t, x) := by
      have h := hNS x
      unfold navierStokesResidual at h
      rw [← h]
      abel
    rw [heq]
    simp only [inner_add_right, inner_sub_right]
  unfold energyRate
  rw [integral_const_mul, hEq,
    integral_add hiLNP hiF,
    integral_sub hiLN hiP, integral_sub hiL hiN,
    integral_laplacian_energy hu hcu,
    integral_pressure_energy_zero hu hp hcu hdiv]
  have htransport := integral_transport_energy_zero hu hu hcu hdiv
  change (∫ x, ⟪u (t, x), advection u t x⟫_ℝ) = 0 at htransport
  rw [htransport]
  simp only [sub_zero, dissipation]
  ring

/-- Young's inequality controls the forcing by the two actual squared L2
norms. All terms are integrable before the integral is compared. -/
theorem energy_rate_le {u f : VelocityField} {p : PressureField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hf : Continuous (fun x : Space => f (t, x)))
    (hcu : HasCompactSupport (fun x : Space => u (t, x)))
    (hfi : Integrable (fun x : Space => ‖f (t, x)‖ ^ 2))
    (hdiv : ∀ x, spatialDivergence u t x = 0)
    (hNS : ∀ x, navierStokesResidual u p t x = f (t, x)) :
    energyRate u t ≤ l2Sq u t + l2Sq f t := by
  have hui := integrable_norm_sq hu.continuous hcu
  have hip := integrable_inner_left hu.continuous hf hcu
  have hsum : Integrable (fun x : Space => ‖u (t, x)‖ ^ 2 + ‖f (t, x)‖ ^ 2) := hui.add hfi
  have hpoint (x : Space) :
      2 * ⟪u (t, x), f (t, x)⟫_ℝ ≤ ‖u (t, x)‖ ^ 2 + ‖f (t, x)‖ ^ 2 := by
    have hinner := (le_abs_self ⟪u (t, x), f (t, x)⟫_ℝ).trans
      (abs_real_inner_le_norm (u (t, x)) (f (t, x)))
    nlinarith [sq_nonneg (‖u (t, x)‖ - ‖f (t, x)‖)]
  have hforce : 2 * (∫ x, ⟪u (t, x), f (t, x)⟫_ℝ) ≤ l2Sq u t + l2Sq f t := by
    rw [← integral_const_mul]
    unfold l2Sq
    rw [← integral_add hui hfi]
    exact integral_mono (hip.const_mul 2) hsum hpoint
  rw [energy_balance hu hp hf hcu hdiv hNS]
  have hd := dissipation_nonneg u t
  linarith

theorem slice_compact {u : VelocityField} {K : Set Space}
    (hK : IsCompact K) {t : ℝ} (hsupp : tsupport (fun x => u (t, x)) ⊆ K) :
    HasCompactSupport (fun x => u (t, x)) :=
  hK.of_isClosed_subset (isClosed_tsupport _) hsupp

theorem zero_outside {u : VelocityField} {K : Set Space} {t : ℝ}
    (hsupp : tsupport (fun x => u (t, x)) ⊆ K) {x : Space} (hx : x ∉ K) :
    u (t, x) = 0 :=
  image_eq_zero_of_notMem_tsupport (f := fun y => u (t, y)) (fun h => hx (hsupp h))

theorem l2Sq_continuousOn {a b : ℝ} {u : VelocityField} {K : Set Space}
    (hK : IsCompact K) (hu : ContDiffOn ℝ ∞ u (slab a b))
    (hsupp : ∀ t ∈ Icc a b, tsupport (fun x => u (t, x)) ⊆ K) :
    ContinuousOn (l2Sq u) (Icc a b) := by
  have hF : ContinuousOn (fun z : SpaceTime => ‖u z‖ ^ 2) (Icc a b ×ˢ univ) :=
    (hu.norm_sq ℝ).continuousOn
  apply CompactTimeIntegral.continuousOn_integral hK hF
  intro t ht x hx
  rw [zero_outside (hsupp t ht) hx]
  simp

/-- Differentiation under the ordinary whole-space energy integral follows
from joint smoothness and fixed compact spatial support. -/
theorem energy_hasDerivAt {a b t : ℝ} {u : VelocityField} {K : Set Space}
    (hK : IsCompact K) (hu : ContDiffOn ℝ ∞ u (slab a b))
    (hsupp : ∀ r ∈ Icc a b, tsupport (fun x => u (r, x)) ⊆ K)
    (ht : t ∈ Ioo a b) : HasDerivAt (l2Sq u) (energyRate u t) t := by
  have hF : ContDiffOn ℝ 1 (fun z : SpaceTime => ‖u z‖ ^ 2) (Icc a b ×ˢ univ) :=
    (hu.norm_sq ℝ).of_le (nat_le_infty 1)
  refine CompactTimeIntegral.hasDerivAt_integral_of_contDiffOn_of_hasDerivAt hK hF ?_ ht ?_
  · intro r hr x hx
    rw [zero_outside (hsupp r hr) hx]
    simp
  · intro x
    exact energy_density_derivative (time_differentiable_at_interior hu ht x)

theorem integrable_dissipation_terms {u : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hcu : HasCompactSupport (fun x : Space => u (t, x))) (i : Fin 3) :
    Integrable (fun x : Space => ‖spatialPartial i (fun y => u (t, y)) x‖ ^ 2) :=
  integrable_norm_sq (spatial_partial_contDiff hu i).continuous (compact_partial hcu i)

/-- The exact energy identity, with the derivative justified and all spatial
integrals taken against ordinary Lebesgue volume on R³. -/
theorem hasDerivAt_energy_balance {a b t : ℝ} {u f : VelocityField}
    {p : PressureField} {K : Set Space}
    (hK : IsCompact K) (hu : ContDiffOn ℝ ∞ u (slab a b))
    (hp : ContDiffOn ℝ ∞ p (slab a b))
    (hf : Continuous (fun x : Space => f (t, x)))
    (hsupp : ∀ r ∈ Icc a b, tsupport (fun x => u (r, x)) ⊆ K)
    (ht : t ∈ Ioo a b)
    (hdiv : ∀ x, spatialDivergence u t x = 0)
    (hNS : ∀ x, navierStokesResidual u p t x = f (t, x)) :
    HasDerivAt (l2Sq u)
      (-2 * dissipation u t + 2 * ∫ x, ⟪u (t, x), f (t, x)⟫_ℝ) t := by
  have h := energy_hasDerivAt hK hu hsupp ht
  rw [energy_balance (spatial_smooth hu ⟨ht.1.le, ht.2.le⟩)
    (spatial_smooth hp ⟨ht.1.le, ht.2.le⟩) hf
    (slice_compact hK (hsupp t ⟨ht.1.le, ht.2.le⟩)) hdiv hNS] at h
  exact h

/-- A smooth compact force yields one uniform bound for the kinetic energy
before time one. The proof includes square integrability at every time, then
uses the PDE-derived energy inequality and a scalar integrating factor. -/
theorem uniform_finite_energy {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hK : IsCompact K)
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    (hp : ContDiffOn ℝ ∞ p preSingularDomain)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x => u (t, x)) ⊆ K)
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    (hinitial : ∀ x : Space, u (0, x) = 0)
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, spatialDivergence u t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, navierStokesResidual u p t x = f (t, x)) :
    ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u := by
  obtain ⟨C, hC, hforce⟩ := CompactForceBound.exists_uniform_l2sq_bound hf.continuous hcf
  refine ⟨(1 / 2 : ℝ) * (C * Real.exp 1),
    mul_nonneg (by norm_num) (mul_nonneg hC (Real.exp_pos _).le), ?_⟩
  intro t ht
  have hsub : slab 0 t ⊆ preSingularDomain := by
    intro z hz
    exact ⟨⟨hz.1.1, lt_of_le_of_lt hz.1.2 ht.2⟩, hz.2⟩
  have huT := hu.mono hsub
  have hpT := hp.mono hsub
  have hsuppT : ∀ r ∈ Icc (0 : ℝ) t, tsupport (fun x => u (r, x)) ⊆ K := by
    intro r hr
    exact hsupp r ⟨hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hzero : l2Sq u 0 = 0 := by simp [l2Sq, hinitial]
  have hbound : l2Sq u t ≤ C * Real.exp 1 := by
    apply ScalarEnergyBound.forced_gronwall_uniform ht.1 ht.2.le hC
      (l2Sq_continuousOn hK huT hsuppT) hzero
      (fun r hr => energy_hasDerivAt hK huT hsuppT hr) _ t ⟨ht.1, le_rfl⟩
    intro r hr
    have hrT : r ∈ Icc (0 : ℝ) t := ⟨hr.1.le, hr.2.le⟩
    have hr1 : r ∈ Ioo (0 : ℝ) 1 := ⟨hr.1, hr.2.trans ht.2⟩
    have hrf := hforce r ⟨hr.1.le, hr1.2.le⟩
    have hrate := energy_rate_le (spatial_smooth huT hrT) (spatial_smooth hpT hrT)
      (hf.continuous.comp (continuous_const.prodMk continuous_id))
      (slice_compact hK (hsuppT r hrT)) hrf.1 (hdiv r hr1) (hNS r hr1)
    exact hrate.trans (add_le_add_right hrf.2 _)
  refine ⟨integrable_norm_sq (spatial_smooth huT ⟨ht.1, le_rfl⟩).continuous
    (slice_compact hK (hsupp t ht)), ?_⟩
  exact mul_le_mul_of_nonneg_left hbound (by norm_num)

end NavierStokesR3.CompactEnergy
