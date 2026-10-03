/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesTruncatedMatrix

/-! # Iterates Matrix Integral Sum

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance

/-- Exact transpose reversal of a scalar matrix pairing. -/
theorem iterate_matrix_pairing_transpose (a b : Vec 2)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    vecDot a (Q.transpose.mulVec b) = vecDot b (Q.mulVec a) := by
  simp only [vecDot, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two]
  ring

/-- Continuous fields on the actual compact torus cell are integrable. -/
theorem iterate_unitCube_integrable_of_continuous {f : Vec 2 → ℝ} (hf : Continuous f) :
    IntegrableOn f unitCube := by
  have hc : IsCompact (Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  apply (hf.continuousOn.integrableOn_compact hc).mono_set
  intro x hx
  change (∀ i ∈ Set.univ, x i ∈ Set.Ioo (0 : ℝ) 1) at hx
  change ∀ i ∈ Set.univ, x i ∈ Set.Icc (0 : ℝ) 1
  exact fun i hi => ⟨(hx i hi).1.le, (hx i hi).2.le⟩

/-- Finite matrix pairings commute with integration under componentwise
integrability; coefficients retain their original order. -/
theorem iterate_matrix_pairing_integral_eq_sum {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {a b : X → Vec 2} {Q : X → Matrix (Fin 2) (Fin 2) ℝ}
    (hi : ∀ j k, Integrable (fun z => Q z j k * a z j * b z k) μ) :
    (∫ z, vecDot (a z) ((Q z).mulVec (b z)) ∂μ) =
      ∑ j : Fin 2, ∑ k : Fin 2, ∫ z, Q z j k * a z j * b z k ∂μ := by
  have he : (fun z => vecDot (a z) ((Q z).mulVec (b z))) =
      (fun z => ∑ j : Fin 2, ∑ k : Fin 2, Q z j k * a z j * b z k) := by
    funext z
    simp only [vecDot, Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he, integral_finsetSum Finset.univ (fun j _ =>
    integrable_finsetSum Finset.univ (fun k _ => hi j k))]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_finsetSum Finset.univ (fun k _ => hi j k)

end AVenhance.Infra.Section4
