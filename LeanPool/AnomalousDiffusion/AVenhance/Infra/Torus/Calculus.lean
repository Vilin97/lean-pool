/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Slicing
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import LeanPool.AnomalousDiffusion.Homogenization.Sobolev.CubeEmbedding.FaceReflectionLines

/-! Smooth periodic integration by parts on half-open fundamental cells. -/

@[expose] public section

noncomputable section

open MeasureTheory Set intervalIntegral
open Homogenization

namespace AVenhance.Infra.Torus

/-- The classical coordinate derivative, evaluated in the unit coordinate direction. -/
noncomputable def coordDeriv {d : ℕ} (i : Fin d) (f : Vec d → ℂ) (x : Vec d) : ℂ :=
  fderiv ℝ f x (basisVec i)

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def Calculus.closedUnitCell (d : ℕ) : Set (Vec d) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

theorem Calculus.isCompact_closedUnitCell (d : ℕ) : IsCompact (Calculus.closedUnitCell d) := by
  simpa [Calculus.closedUnitCell] using
    (isCompact_univ_pi fun _ : Fin d => isCompact_Icc)

theorem Calculus.unitCell_subset_closedUnitCell (d : ℕ) :
    unitCell d ⊆ Calculus.closedUnitCell d := by
  intro x hx
  simp only [unitCell, unitCellAt, Set.mem_ofPred_eq, zero_add] at hx
  simp only [Calculus.closedUnitCell, Set.mem_pi, mem_univ, forall_true_left]
  intro i
  exact ⟨le_of_lt (hx i).1, (hx i).2⟩

theorem Calculus.continuous_integrableOn_unitCell {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] {f : Vec d → E} (hf : Continuous f) : IntegrableOn f (unitCell d) := by
  exact (hf.continuousOn.integrableOn_compact (Calculus.isCompact_closedUnitCell d)).mono_set
    (Calculus.unitCell_subset_closedUnitCell d)

/-- The two endpoints of a coordinate insertion line differ by an integer shift. -/
theorem Calculus.insertNth_one_eq_integerTranslate {n : ℕ} (i : Fin (n + 1))
    (z : Vec n) :
    i.insertNth 1 z = i.insertNth 0 z +
      intVector (fun j => if j = i then (1 : ℤ) else 0) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [intVector, Fin.insertNth_apply_same]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
    simp [intVector, Fin.insertNth_apply_succAbove, hji]

theorem Calculus.periodic_insertNth_endpoints {n : ℕ} (i : Fin (n + 1))
    (z : Vec n) {f : Vec (n + 1) → ℂ} (hf : IsZdPeriodic f) :
    f (i.insertNth 1 z) = f (i.insertNth 0 z) := by
  simpa [Calculus.insertNth_one_eq_integerTranslate] using
    hf (fun j => if j = i then (1 : ℤ) else 0) (i.insertNth 0 z)

theorem Calculus.hasDerivAt_comp_insertNth_complex {n : ℕ}
    {f : Vec (n + 1) → ℂ} (hf : Differentiable ℝ f)
    (i : Fin (n + 1)) (z : Vec n) (t : ℝ) :
    HasDerivAt (fun s => f (i.insertNth s z))
      (coordDeriv i f (i.insertNth t z)) t := by
  exact (hf (i.insertNth t z)).hasFDerivAt.comp_hasDerivAt t
    (Homogenization.hasDerivAt_insertNth i z t)

theorem Calculus.line_integral_ibp {n : ℕ} (i : Fin (n + 1))
    {f g : Vec (n + 1) → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hpf : IsZdPeriodic f) (hpg : IsZdPeriodic g) (z : Vec n) :
    (∫ t in Set.Ioc (0 : ℝ) 1,
        f (i.insertNth t z) * coordDeriv i g (i.insertNth t z)) =
      -∫ t in Set.Ioc (0 : ℝ) 1,
        coordDeriv i f (i.insertNth t z) * g (i.insertNth t z) := by
  let u : ℝ → ℂ := fun t => f (i.insertNth t z)
  let v : ℝ → ℂ := fun t => g (i.insertNth t z)
  let u' : ℝ → ℂ := fun t => coordDeriv i f (i.insertNth t z)
  let v' : ℝ → ℂ := fun t => coordDeriv i g (i.insertNth t z)
  have hdF : Differentiable ℝ f := hf.differentiable (by simp)
  have hdG : Differentiable ℝ g := hg.differentiable (by simp)
  have hu : ∀ t, HasDerivAt u (u' t) t := fun t =>
    Calculus.hasDerivAt_comp_insertNth_complex hdF i z t
  have hv : ∀ t, HasDerivAt v (v' t) t := fun t =>
    Calculus.hasDerivAt_comp_insertNth_complex hdG i z t
  have hline : Continuous (fun t : ℝ => (i.insertNth t z : Vec (n + 1))) :=
    continuous_iff_continuousAt.2 fun t =>
      (Homogenization.hasDerivAt_insertNth i z t).continuousAt
  have hu'c : Continuous u' := by
    change Continuous (fun t => coordDeriv i f (i.insertNth t z))
    exact ((hf.continuous_fderiv (by simp)).comp hline).clm_apply continuous_const
  have hv'c : Continuous v' := by
    change Continuous (fun t => coordDeriv i g (i.insertNth t z))
    exact ((hg.continuous_fderiv (by simp)).comp hline).clm_apply continuous_const
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 1)
    (fun x _ => hu x) (fun x _ => hv x)
    (hu'c.intervalIntegrable 0 1) (hv'c.intervalIntegrable 0 1)
  have hendF : u 1 = u 0 := by
    exact Calculus.periodic_insertNth_endpoints i z hpf
  have hendG : v 1 = v 0 := by
    exact Calculus.periodic_insertNth_endpoints i z hpg
  rw [hendF, hendG] at hIBP
  simpa [u, v, u', v', intervalIntegral.integral_of_le h01] using hIBP

/-- Smooth periodic integration by parts on the `ℤ^d` unit cell. -/
theorem integral_unitCell_coord_ibp {n : ℕ} (i : Fin (n + 1))
    {f g : Vec (n + 1) → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hpf : IsZdPeriodic f) (hpg : IsZdPeriodic g) :
    (∫ x in unitCell (n + 1), f x * coordDeriv i g x) =
      -∫ x in unitCell (n + 1), coordDeriv i f x * g x := by
  have hDf : Continuous (fun x => coordDeriv i f x) := by
    exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDg : Continuous (fun x => coordDeriv i g x) := by
    exact (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfg : IntegrableOn (fun x => f x * coordDeriv i g x) (unitCell (n + 1)) :=
    Calculus.continuous_integrableOn_unitCell (hf.continuous.mul hDg)
  have hgf : IntegrableOn (fun x => coordDeriv i f x * g x) (unitCell (n + 1)) :=
    Calculus.continuous_integrableOn_unitCell (hDf.mul hg.continuous)
  rw [integral_unitCell_peel_coord i hfg, integral_unitCell_peel_coord i hgf]
  rw [← MeasureTheory.integral_neg]
  apply setIntegral_congr_ae (measurableSet_unitCell n)
  filter_upwards with z _hz
  exact Calculus.line_integral_ibp i hf hg hpf hpg z

/-- Vanishing of the integral of any coordinate derivative of a smooth periodic
complex-valued function over its unit cell. -/
theorem integral_unitCell_coord_deriv_eq_zero {n : ℕ} (i : Fin (n + 1))
    {f : Vec (n + 1) → ℂ} (hf : ContDiff ℝ 1 f) (hpf : IsZdPeriodic f) :
    ∫ x in unitCell (n + 1), coordDeriv i f x = 0 := by
  have hone : ContDiff ℝ 1 (fun _ : Vec (n + 1) => (1 : ℂ)) := contDiff_const
  have hperOne : IsZdPeriodic (fun _ : Vec (n + 1) => (1 : ℂ)) := by
    intro k x
    rfl
  have h := integral_unitCell_coord_ibp i hone hf hperOne hpf
  simpa [coordDeriv] using h

end AVenhance.Infra.Torus
