/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMatrixIntegralSum

/-! # Iterates Matrix Primitive Assembly

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance

/-- Finite-dimensional assembly of independently proved component primitive
identities. This lemma performs only linearity of integrals and finite sums. -/
theorem iterate_matrix_primitive_component_assembly
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}
    {a b ma mb : X → Vec 2} {C Q : X → Matrix (Fin 2) (Fin 2) ℝ}
    {as bs : Y → Vec 2} {Qs : Y → Matrix (Fin 2) (Fin 2) ℝ}
    (hc : ∀ j k, Integrable (fun z => C z j k * a z j * b z k) μ)
    (hbd : ∀ j k, Integrable (fun x => Qs x j k * as x j * bs x k) ν)
    (hp : ∀ j k, Integrable (fun z => Q z j k * a z j * mb z k) μ)
    (hu : ∀ j k, Integrable (fun z => Q z j k * ma z j * b z k) μ)
    (hcomponent : ∀ j k,
      (∫ z, C z j k * a z j * b z k ∂μ) =
        (∫ x, Qs x j k * as x j * bs x k ∂ν) -
        (∫ z, Q z j k * a z j * mb z k ∂μ) -
        (∫ z, Q z j k * ma z j * b z k ∂μ)) :
    (∫ z, vecDot (a z) ((C z).mulVec (b z)) ∂μ) =
      (∫ x, vecDot (as x) ((Qs x).mulVec (bs x)) ∂ν) -
      (∫ z, vecDot (a z) ((Q z).mulVec (mb z)) ∂μ) -
      (∫ z, vecDot (ma z) ((Q z).mulVec (b z)) ∂μ) := by
  rw [iterate_matrix_pairing_integral_eq_sum hc,
    iterate_matrix_pairing_integral_eq_sum hbd,
    iterate_matrix_pairing_integral_eq_sum hp,
    iterate_matrix_pairing_integral_eq_sum hu]
  simp_rw [hcomponent, Finset.sum_sub_distrib]

end AVenhance.Infra.Section4
