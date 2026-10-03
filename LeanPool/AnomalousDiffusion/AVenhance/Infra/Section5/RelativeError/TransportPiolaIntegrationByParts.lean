/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.PeriodicCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.TimeEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Basic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceGrad

/-! # RelativeError: periodic integration by parts for the Piola vector -/

@[expose] public section

noncomputable section

open Homogenization
open MeasureTheory
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance
open AVenhance.Infra.Classical
open AVenhance.Infra.Torus

/-- Periodic integration by parts transfers divergence from a smooth vector
field to a smooth scalar function on the unit cell. -/
theorem integral_unitCell_scalar_mul_vecDiv
    {f : Vec 2 → ℝ} {W : Vec 2 → Vec 2}
    (hf : ContDiff ℝ 1 f) (hW : ContDiff ℝ 1 W)
    (hfp : IsZ2Periodic f)
    (hWp : ∀ i : Fin 2, IsZ2Periodic (fun x => W x i)) :
    (∫ x in unitCell 2, f x * vecDiv W x) =
      -∫ x in unitCell 2, vecDot (spaceGrad f x) (W x) := by
  have hgradFCont (i : Fin 2) : Continuous (fun x => spaceGrad f x i) := by
    change Continuous (fun x => fderiv ℝ f x (basisVec i))
    exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hWCont (i : Fin 2) : Continuous (fun x => W x i) :=
    (contDiff_pi.1 hW i).continuous
  have hsumLeft :
      (∫ x in unitCell 2, f x * vecDiv W x) =
        ∑ i : Fin 2, ∫ x in unitCell 2,
          f x * spaceGrad (fun y => W y i) x i := by
    calc
      _ = ∫ x in unitCell 2, ∑ i : Fin 2,
          f x * spaceGrad (fun y => W y i) x i := by
        apply setIntegral_congr_fun (measurableSet_unitCell 2)
        intro x hx
        simp only [vecDiv, Fin.sum_univ_two]
        ring
      _ = _ := integral_finsetSum Finset.univ
        (μ := (volume : Measure (Vec 2)).restrict (unitCell 2))
        (f := fun i x => f x * spaceGrad (fun y => W y i) x i)
        (by
          intro i hi
          apply continuous_integrableOn_unitCell
          exact hf.continuous.mul (by
            change Continuous (fun x => fderiv ℝ (fun y => W y i) x (basisVec i))
            exact ((contDiff_pi.1 hW i).continuous_fderiv (by norm_num)).clm_apply
              continuous_const))
  have hparts (i : Fin 2) :
      (∫ x in unitCell 2,
        f x * spaceGrad (fun y => W y i) x i) =
      -∫ x in unitCell 2, spaceGrad f x i * W x i :=
    integral_unitCell_coord_ibp_real i hf (contDiff_pi.1 hW i)
      hfp (hWp i)
  have hsumRight :
      (∫ x in unitCell 2, vecDot (spaceGrad f x) (W x)) =
        ∑ i : Fin 2, ∫ x in unitCell 2,
          spaceGrad f x i * W x i := by
    change (∫ x in unitCell 2, ∑ i : Fin 2,
        spaceGrad f x i * W x i) = _
    exact integral_finsetSum Finset.univ
      (μ := (volume : Measure (Vec 2)).restrict (unitCell 2))
      (f := fun i x => spaceGrad f x i * W x i)
      (by
        intro i hi
        apply continuous_integrableOn_unitCell
        exact (hgradFCont i).mul (hWCont i))
  calc
    (∫ x in unitCell 2, f x * vecDiv W x) =
        ∑ i : Fin 2, ∫ x in unitCell 2,
          f x * spaceGrad (fun y => W y i) x i := hsumLeft
    _ = -∑ i : Fin 2, ∫ x in unitCell 2,
          spaceGrad f x i * W x i := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      exact hparts i
    _ = -∫ x in unitCell 2, vecDot (spaceGrad f x) (W x) := by
      rw [hsumRight]

end AVenhance.Infra.Section5.RelativeError

end
