/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Calculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.TimeEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.PeriodicCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.SigmaMat
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsZ2Periodic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceGrad
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.UnitCube
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.L2NormSq

/-!
# Periodic integration by parts against a Lipschitz periodic function

The classical periodic integration by parts is available for `C¹` factors. Here one factor is only
differentiable with a bounded (measurable) partial derivative; the line integration by parts then
still holds because the derivative is interval integrable.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization

namespace AVenhance.Infra.Section5.RelativeError

local instance periodicFiniteUnitCube : IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  unfold AVenhance.unitCube
  rw [Measure.restrict_apply_univ, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

/-- The two endpoints of a coordinate insertion line differ by an integer shift. -/
theorem ForcedEnergyPeriodic.insertNth_one_eq_shift (i : Fin 2) (z : Vec 1) :
    (i.insertNth 1 z : Vec 2) =
      (i.insertNth 0 z : Vec 2) + AVenhance.latticeShift (fun j => if j = i then 1 else 0) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [AVenhance.latticeShift, Fin.insertNth_apply_same]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
    simp [AVenhance.latticeShift, Fin.insertNth_apply_succAbove, hji]

theorem ForcedEnergyPeriodic.periodic_insertNth_endpoints (i : Fin 2) (z : Vec 1) {f : Vec 2 → ℝ}
    (hf : AVenhance.IsZ2Periodic f) : f (i.insertNth 1 z) = f (i.insertNth 0 z) := by
  rw [ForcedEnergyPeriodic.insertNth_one_eq_shift]
  exact hf _ _

/-- A partial derivative of a differentiable function is measurable. -/
theorem measurable_spaceGrad_component (ξ : Vec 2 → ℝ) (i : Fin 2) :
    Measurable (fun x => AVenhance.spaceGrad ξ x i) :=
  (measurable_fderiv ℝ ξ).apply_continuousLinearMap (Homogenization.basisVec i)

/-- A continuous function is integrable on the unit cube. -/
theorem continuous_integrableOn_unitCube {f : Vec 2 → ℝ} (hf : Continuous f) :
    IntegrableOn f AVenhance.unitCube :=
  (hf.continuousOn.integrableOn_compact
    (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)).mono_set (by
      intro x hx
      simp only [AVenhance.unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx
      simp only [Set.mem_pi, Set.mem_univ, true_implies]
      exact fun j => ⟨(hx j).1.le, (hx j).2.le⟩)

/-- A bounded measurable factor times a continuous factor is integrable on the unit cube. -/
theorem integrableOn_unitCube_mul_continuous {a c : Vec 2 → ℝ} (ha : Measurable a) {C : ℝ}
    (hC : ∀ x, |a x| ≤ C) (hc : Continuous c) :
    IntegrableOn (fun x => a x * c x) AVenhance.unitCube := by
  have := (continuous_integrableOn_unitCube hc).mul_bdd (c := C) ha.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hC x)
  exact this.congr (ae_of_all _ fun x => mul_comm _ _)

/-- Periodic integration by parts in one coordinate, with a merely differentiable factor with
bounded partial derivative. -/
theorem integral_cell_coord_ibp_differentiable (i : Fin 2) {ξ g : Vec 2 → ℝ}
    (hξ : Differentiable ℝ ξ) (hξp : AVenhance.IsZ2Periodic ξ)
    (hξb : ∃ C : ℝ, ∀ x, |AVenhance.spaceGrad ξ x i| ≤ C)
    (hg : ContDiff ℝ 1 g) (hgp : AVenhance.IsZ2Periodic g) :
    ∫ x in AVenhance.unitCube, ξ x * AVenhance.spaceGrad g x i =
      -∫ x in AVenhance.unitCube, AVenhance.spaceGrad ξ x i * g x := by
  obtain ⟨C, hC⟩ := hξb
  have hgradg : Continuous (fun x => AVenhance.spaceGrad g x i) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hmeasξ' := measurable_spaceGrad_component ξ i
  have hint1 : IntegrableOn (fun x => ξ x * AVenhance.spaceGrad g x i) AVenhance.unitCube := by
    have hc : Continuous (fun x => ξ x * AVenhance.spaceGrad g x i) :=
      hξ.continuous.mul hgradg
    exact (hc.continuousOn.integrableOn_compact
      (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)).mono_set (by
        intro x hx
        simp only [AVenhance.unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx
        simp only [Set.mem_pi, Set.mem_univ, true_implies]
        exact fun j => ⟨(hx j).1.le, (hx j).2.le⟩)
  have hint2 : IntegrableOn (fun x => AVenhance.spaceGrad ξ x i * g x) AVenhance.unitCube := by
    have hgint : IntegrableOn g AVenhance.unitCube :=
      (hg.continuous.continuousOn.integrableOn_compact
        (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)).mono_set (by
        intro x hx
        simp only [AVenhance.unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx
        simp only [Set.mem_pi, Set.mem_univ, true_implies]
        exact fun j => ⟨(hx j).1.le, (hx j).2.le⟩)
    have := hgint.mul_bdd (c := C) hmeasξ'.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hC x)
    exact this.congr (ae_of_all _ fun x => mul_comm _ _)
  rw [← AVenhance.Infra.Torus.integral_unitCell_eq_unitCube,
    ← AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
  have hint1' : IntegrableOn (fun x => ξ x * AVenhance.spaceGrad g x i)
      (AVenhance.Infra.Torus.unitCell 2) :=
    hint1.congr_set_ae AVenhance.Infra.Torus.unitCell_ae_eq_unitCube
  have hint2' : IntegrableOn (fun x => AVenhance.spaceGrad ξ x i * g x)
      (AVenhance.Infra.Torus.unitCell 2) :=
    hint2.congr_set_ae AVenhance.Infra.Torus.unitCell_ae_eq_unitCube
  rw [AVenhance.Infra.Torus.integral_unitCell_peel_coord i hint1',
    AVenhance.Infra.Torus.integral_unitCell_peel_coord i hint2', ← integral_neg]
  refine setIntegral_congr_fun (AVenhance.Infra.Torus.measurableSet_unitCell 1) fun z _ => ?_
  let u : ℝ → ℝ := fun t => ξ (i.insertNth t z)
  let v : ℝ → ℝ := fun t => g (i.insertNth t z)
  let u' : ℝ → ℝ := fun t => AVenhance.spaceGrad ξ (i.insertNth t z) i
  let v' : ℝ → ℝ := fun t => AVenhance.spaceGrad g (i.insertNth t z) i
  have hu : ∀ t, HasDerivAt u (u' t) t := fun t =>
    (hξ (i.insertNth t z)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_insertNth i z t)
  have hv : ∀ t, HasDerivAt v (v' t) t := fun t =>
    ((hg.differentiable (by simp)) (i.insertNth t z)).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_insertNth i z t)
  have hline : Continuous (fun t : ℝ => (i.insertNth t z : Vec 2)) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_insertNth i z t).continuousAt
  have hv'c : Continuous v' := hgradg.comp hline
  have hu'm : Measurable u' := hmeasξ'.comp hline.measurable
  have hu'int : IntervalIntegrable u' volume 0 1 := by
    rw [intervalIntegrable_iff]
    refine Measure.integrableOn_of_bounded (M := C) ?_ hu'm.aestronglyMeasurable
      (ae_of_all _ fun t => by simpa [Real.norm_eq_abs, u'] using hC (i.insertNth t z))
    simp
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 1) (fun x _ => hu x) (fun x _ => hv x) hu'int
    (hv'c.intervalIntegrable 0 1)
  have hendF : u 1 = u 0 := ForcedEnergyPeriodic.periodic_insertNth_endpoints i z hξp
  have hendG : v 1 = v 0 := ForcedEnergyPeriodic.periodic_insertNth_endpoints i z hgp
  rw [hendF, hendG, sub_self, zero_sub] at hIBP
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  simpa [u, v, u', v', intervalIntegral.integral_of_le h01] using hIBP

/-- Mixed partial derivatives of a `C²` function commute. -/
theorem spaceGrad_mixed_symm {θ : Vec 2 → ℝ} (hθ : ContDiff ℝ 2 θ) (x : Vec 2) (i j : Fin 2) :
    AVenhance.spaceGrad (fun y => AVenhance.spaceGrad θ y j) x i =
      AVenhance.spaceGrad (fun y => AVenhance.spaceGrad θ y i) x j := by
  have hd1 : Differentiable ℝ (fderiv ℝ θ) :=
    (hθ.fderiv_right (m := 1) (by norm_num)).differentiable (by simp)
  have hform (a b : Fin 2) : AVenhance.spaceGrad (fun y => AVenhance.spaceGrad θ y b) x a =
      fderiv ℝ (fderiv ℝ θ) x (Homogenization.basisVec a) (Homogenization.basisVec b) := by
    unfold AVenhance.spaceGrad
    have := fderiv_clm_apply (c := fderiv ℝ θ) (u := fun _ : Vec 2 => Homogenization.basisVec b)
      (x := x) (hd1 x) (differentiableAt_const _)
    change (fderiv ℝ (fun y => (fderiv ℝ θ y) (Homogenization.basisVec b)) x)
      (Homogenization.basisVec a) = _
    rw [this]
    simp [fderiv_fun_const]
  rw [hform, hform]
  exact ((hθ.contDiffAt (x := x)).isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
    ) _ _

theorem spaceGrad_component_continuous' {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f) (j : Fin 2) :
    Continuous (fun x => AVenhance.spaceGrad f x j) :=
  (hf.continuous_fderiv (by simp)).clm_apply continuous_const

/-- The coordinates of `σ a`. -/
theorem sigmaMat_mulVec_apply_zero (a : Vec 2) : AVenhance.sigmaMat.mulVec a 0 = -a 1 := by
  simp [AVenhance.sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem sigmaMat_mulVec_apply_one (a : Vec 2) : AVenhance.sigmaMat.mulVec a 1 = a 0 := by
  simp [AVenhance.sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Product rule for coordinate derivatives. -/
theorem spaceGrad_mul_apply {ψ k : Vec 2 → ℝ} (hψ : Differentiable ℝ ψ)
    (hk : Differentiable ℝ k) (x : Vec 2) (i : Fin 2) :
    AVenhance.spaceGrad (fun y => ψ y * k y) x i =
      AVenhance.spaceGrad ψ x i * k x + ψ x * AVenhance.spaceGrad k x i := by
  unfold AVenhance.spaceGrad
  rw [fderiv_fun_mul (hψ x) (hk x)]
  simp
  ring

theorem spaceGrad_contDiff_component {θ : Vec 2 → ℝ} {n : ℕ} (hθ : ContDiff ℝ (n + 1 : ℕ) θ)
    (j : Fin 2) : ContDiff ℝ n (fun x => AVenhance.spaceGrad θ x j) := by
  change ContDiff ℝ n (fun x => fderiv ℝ θ x (Homogenization.basisVec j))
  exact (hθ.fderiv_right (by simp)).clm_apply contDiff_const

/-- Skew cancellation: the flux `ξ σ ∇θ` represents the transport `σ∇ξ·∇θ` against any periodic
test, for periodic `C²` functions `θ` and a merely Lipschitz periodic `ξ`. -/
theorem skew_flux_cell_identity {ξ θ ψ : Vec 2 → ℝ}
    (hξ : Differentiable ℝ ξ) (hξp : AVenhance.IsZ2Periodic ξ)
    (hξb : ∀ i : Fin 2, ∃ C : ℝ, ∀ x, |AVenhance.spaceGrad ξ x i| ≤ C)
    (hθ : ContDiff ℝ 2 θ) (hθp : AVenhance.IsZ2Periodic θ)
    (hψ : ContDiff ℝ 1 ψ) (hψp : AVenhance.IsZ2Periodic ψ) :
    ∫ x in AVenhance.unitCube,
        Homogenization.vecDot (AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad ξ x))
          (AVenhance.spaceGrad θ x) * ψ x =
      ∫ x in AVenhance.unitCube, ξ x *
        Homogenization.vecDot (AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad θ x))
          (AVenhance.spaceGrad ψ x) := by
  have hθ1 : ContDiff ℝ 1 θ := hθ.of_le (by norm_num)
  have hgradθ (j : Fin 2) : ContDiff ℝ 1 (fun x => AVenhance.spaceGrad θ x j) :=
    spaceGrad_contDiff_component (n := 1) (by simpa using hθ) j
  have hgradθp (j : Fin 2) : AVenhance.IsZ2Periodic (fun x => AVenhance.spaceGrad θ x j) :=
    AVenhance.Infra.Classical.periodic_spaceGrad_component hθp j
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hθd (j : Fin 2) : Differentiable ℝ (fun x => AVenhance.spaceGrad θ x j) :=
    (hgradθ j).differentiable (by simp)
  have hVcont (j : Fin 2) : ContDiff ℝ 1 (fun x => ψ x * AVenhance.spaceGrad θ x j) :=
    hψ.mul (hgradθ j)
  have hVper (j : Fin 2) : AVenhance.IsZ2Periodic (fun x => ψ x * AVenhance.spaceGrad θ x j) := by
    intro n x
    simp only [hψp n x, hgradθp j n x]
  have h0 := integral_cell_coord_ibp_differentiable 0 hξ hξp (hξb 0)
    (hVcont 1) (hVper 1)
  have h1 := integral_cell_coord_ibp_differentiable 1 hξ hξp (hξb 1)
    (hVcont 0) (hVper 0)
  -- expand derivatives of the products
  have hd0 (x : Vec 2) : AVenhance.spaceGrad (fun y => ψ y * AVenhance.spaceGrad θ y 1) x 0 =
      AVenhance.spaceGrad ψ x 0 * AVenhance.spaceGrad θ x 1 +
        ψ x * AVenhance.spaceGrad (fun y => AVenhance.spaceGrad θ y 1) x 0 :=
    spaceGrad_mul_apply hψd (hθd 1) x 0
  have hd1 (x : Vec 2) : AVenhance.spaceGrad (fun y => ψ y * AVenhance.spaceGrad θ y 0) x 1 =
      AVenhance.spaceGrad ψ x 1 * AVenhance.spaceGrad θ x 0 +
        ψ x * AVenhance.spaceGrad (fun y => AVenhance.spaceGrad θ y 0) x 1 :=
    spaceGrad_mul_apply hψd (hθd 0) x 1
  have hsym (x : Vec 2) : AVenhance.spaceGrad (fun y => AVenhance.spaceGrad θ y 1) x 0 =
      AVenhance.spaceGrad (fun y => AVenhance.spaceGrad θ y 0) x 1 :=
    spaceGrad_mixed_symm hθ x 0 1
  -- integrability of the pieces
  have hmeas (i : Fin 2) := measurable_spaceGrad_component ξ i
  have hI0 : IntegrableOn (fun x => AVenhance.spaceGrad ξ x 0 *
      (ψ x * AVenhance.spaceGrad θ x 1)) AVenhance.unitCube := by
    obtain ⟨C, hC⟩ := hξb 0
    exact integrableOn_unitCube_mul_continuous (hmeas 0) hC (hVcont 1).continuous
  have hI1 : IntegrableOn (fun x => AVenhance.spaceGrad ξ x 1 *
      (ψ x * AVenhance.spaceGrad θ x 0)) AVenhance.unitCube := by
    obtain ⟨C, hC⟩ := hξb 1
    exact integrableOn_unitCube_mul_continuous (hmeas 1) hC (hVcont 0).continuous
  have hψgrad (j : Fin 2) : Continuous (fun x => AVenhance.spaceGrad ψ x j) :=
    spaceGrad_component_continuous' hψ j
  have hθ2grad (a b : Fin 2) : Continuous
      (fun x => AVenhance.spaceGrad (fun y => AVenhance.spaceGrad θ y b) x a) :=
    spaceGrad_component_continuous' (hgradθ b) a
  have hJ0 : IntegrableOn (fun x => ξ x * AVenhance.spaceGrad
      (fun y => ψ y * AVenhance.spaceGrad θ y 1) x 0) AVenhance.unitCube :=
    continuous_integrableOn_unitCube (hξ.continuous.mul (spaceGrad_component_continuous'
      (hVcont 1) 0))
  have hJ1 : IntegrableOn (fun x => ξ x * AVenhance.spaceGrad
      (fun y => ψ y * AVenhance.spaceGrad θ y 0) x 1) AVenhance.unitCube :=
    continuous_integrableOn_unitCube (hξ.continuous.mul (spaceGrad_component_continuous'
      (hVcont 0) 1))
  have hL : (fun x => Homogenization.vecDot (AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad ξ x))
          (AVenhance.spaceGrad θ x) * ψ x) =
      fun x => AVenhance.spaceGrad ξ x 0 * (ψ x * AVenhance.spaceGrad θ x 1) -
        AVenhance.spaceGrad ξ x 1 * (ψ x * AVenhance.spaceGrad θ x 0) := by
    funext x
    simp only [Homogenization.vecDot, Fin.sum_univ_two, sigmaMat_mulVec_apply_zero,
      sigmaMat_mulVec_apply_one]
    ring
  have hR : (fun x => ξ x * Homogenization.vecDot
        (AVenhance.sigmaMat.mulVec (AVenhance.spaceGrad θ x)) (AVenhance.spaceGrad ψ x)) =
      fun x => ξ x * AVenhance.spaceGrad (fun y => ψ y * AVenhance.spaceGrad θ y 0) x 1 -
        ξ x * AVenhance.spaceGrad (fun y => ψ y * AVenhance.spaceGrad θ y 1) x 0 := by
    funext x
    rw [hd0 x, hd1 x, hsym x]
    simp only [Homogenization.vecDot, Fin.sum_univ_two, sigmaMat_mulVec_apply_zero,
      sigmaMat_mulVec_apply_one]
    ring
  rw [hL, hR, integral_sub hI0 hI1, integral_sub hJ1 hJ0, h0, h1]
  ring

end AVenhance.Infra.Section5.RelativeError

end
