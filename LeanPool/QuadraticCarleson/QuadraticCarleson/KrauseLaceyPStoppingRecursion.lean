/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyStoppingRecursion
import LeanPool.QuadraticCarleson.QuadraticCarleson.FiniteModulationKernelComparison

/-!
# Stopping recursion with a separate `L^p` monitor

The sparse pairing is tested against `g`, while the stopping family must
control the local average of `‖g‖^p`. This file separates those two roles.
The children are selected using the compactly supported monitor
`x ↦ ‖g x‖^p`, whereas the exact recursive pairing still contains the
original test function `g`.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyPStoppingRecursion

open KrauseLaceyStoppingExtraction KrauseLaceyStoppingRecursion


/-- The nonnegative compactly supported monitor whose `L¹` averages are the
unnormalized `p`-mass averages of `g`. -/
noncomputable def pStoppingMonitor (g : L0Infinity) (p : ℝ) (hp : 0 < p) : L0Infinity where
  toFun := fun x ↦ ((‖g x‖ ^ p : ℝ) : ℂ)
  measurable_toFun := Complex.measurable_ofReal.comp
    ((Real.continuous_rpow_const hp.le).measurable.comp g.measurable_toFun.norm)
  bounded_toFun := by
    obtain ⟨C, hC⟩ := g.bounded_toFun
    let D : ℝ := max C 0
    have hD : 0 ≤ D := le_max_right C 0
    have hbound (x : ℝ) : ‖g x‖ ≤ D := (hC x).trans (le_max_left C 0)
    refine ⟨D ^ p, fun x ↦ ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_rpow (norm_nonneg _) (hbound x) hp.le
  hasCompactSupport_toFun := by
    exact g.hasCompactSupport_toFun.comp_left
      (g := fun z : ℂ ↦ ((‖z‖ ^ p : ℝ) : ℂ)) (by simp [hp.ne'])

@[simp] theorem pStoppingMonitor_apply (g : L0Infinity) (p : ℝ) (hp : 0 < p) (x : ℝ) :
    pStoppingMonitor g p hp x = ((‖g x‖ ^ p : ℝ) : ℂ) := rfl

theorem norm_pStoppingMonitor (g : L0Infinity) (p : ℝ) (hp : 0 < p) (x : ℝ) :
    ‖pStoppingMonitor g p hp x‖ = ‖g x‖ ^ p := by
  rw [pStoppingMonitor_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]

theorem intervalL1Average_pStoppingMonitor
    (g : L0Infinity) (p : ℝ) (hp : 0 < p) (I : RealInterval) :
    intervalL1Average (pStoppingMonitor g p hp) I =
      I.length⁻¹ * ∫ x in I.carrier, ‖g x‖ ^ p := by
  simp only [intervalL1Average, norm_pStoppingMonitor]

/-- Equivalently, the monitor's `L¹` average is the `p`th power of the
usual local `L^p` average. -/
theorem intervalL1Average_pStoppingMonitor_eq_localAverage_rpow
    (g : L0Infinity) (p : ℝ) (hp : 0 < p) (I : RealInterval) :
    intervalL1Average (pStoppingMonitor g p hp) I =
      localAverage p g I ^ p := by
  rw [intervalL1Average_pStoppingMonitor, localAverage,
    ← Real.rpow_mul (mul_nonneg (inv_nonneg.mpr I.length_pos.le)
      (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _)),
    one_div_mul_cancel hp.ne', Real.rpow_one]

/-- On the collection surviving the monitor stopping step, the exact local
`p`-mass bound needed by the interpolation argument is automatic. -/
theorem goodCollection_pMass_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (g : L0Infinity)
    {p : ℝ} (hp : 0 < p) {I₀ J : RealInterval}
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (hJ : J ∈ goodCollection S f (pStoppingMonitor g p hp) I₀) :
    (∫ x in J.carrier, ‖g x‖ ^ p) ≤
      (10 * intervalL1Average (pStoppingMonitor g p hp) I₀) * J.length := by
  have hgood := (goodCollection_averages_le hsub hJ).2
  have hmass : intervalL1Average (pStoppingMonitor g p hp) J * J.length =
      ∫ x in J.carrier, ‖g x‖ ^ p := by
    rw [intervalL1Average_mul_length]
    simp only [norm_pStoppingMonitor]
  rw [← hmass]
  exact mul_le_mul_of_nonneg_right hgood J.length_pos.le

/-- The exact pointwise recursion when the family is stopped by an auxiliary
monitor rather than by the pairing test function. -/
theorem localizedTailMaximal_le_monitorGood_add_children
    (ell₀ : ℤ) (scale : RealInterval → ℤ) {S : Finset RealInterval}
    (f monitor : ℝ → ℂ) (I : RealInterval)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (x : ℝ) :
    localizedTailMaximal ell₀ scale S f x ≤
      localizedTailMaximal ell₀ scale (goodCollection S f monitor I) f x +
        ∑ K ∈ stoppingChildren S f monitor I,
          localizedTailMaximal ell₀ scale (childCollection S K) f x :=
  localizedTailMaximal_le_good_add_children ell₀ scale f monitor I hlam x

/-- The bilinear recursion pairs the operator with the original `g`; only
the interval selection uses the independent monitor. -/
theorem localizedTailMaximal_pairing_le_monitorGood_add_children
    (ell₀ : ℤ) (scale : RealInterval → ℤ) {S : Finset RealInterval}
    {f g monitor : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g)
    (I : RealInterval)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier) :
    (∫⁻ x, localizedTailMaximal ell₀ scale S f x * ‖g x‖ₑ) ≤
      (∫⁻ x, localizedTailMaximal ell₀ scale
        (goodCollection S f monitor I) f x * ‖g x‖ₑ) +
        ∑ K ∈ stoppingChildren S f monitor I,
          ∫⁻ x, localizedTailMaximal ell₀ scale
            (childCollection S K) f x * ‖g x‖ₑ := by
  calc
    _ ≤ ∫⁻ x, (localizedTailMaximal ell₀ scale
          (goodCollection S f monitor I) f x +
        ∑ K ∈ stoppingChildren S f monitor I,
          localizedTailMaximal ell₀ scale (childCollection S K) f x) * ‖g x‖ₑ :=
      lintegral_mono fun x ↦ mul_le_mul'
        (localizedTailMaximal_le_monitorGood_add_children ell₀ scale f monitor I hlam x)
        le_rfl
    _ = _ := by
      simp_rw [add_mul, Finset.sum_mul]
      have hgood : Measurable (fun x ↦ localizedTailMaximal ell₀ scale
          (goodCollection S f monitor I) f x * ‖g x‖ₑ) :=
        (measurable_localizedTailMaximal ell₀ scale
          (goodCollection S f monitor I) hf).mul hg.enorm
      rw [lintegral_add_left hgood]
      congr 1
      apply lintegral_finsetSum
      intro K hK
      exact (measurable_localizedTailMaximal ell₀ scale
        (childCollection S K) hf).mul hg.enorm

/-- One complete stopping step using `‖g‖^p` for selection and the original
`g` for the bilinear pairing. -/
theorem finite_localized_p_stopping_step
    (ell₀ : ℤ) (scale : RealInterval → ℤ) (S : Finset RealInterval)
    {f : ℝ → ℂ} (g : L0Infinity) {p : ℝ} (hp : 0 < p)
    (hf : Measurable f) (hfi : Integrable f) (I₀ : RealInterval)
    (hsub : ∀ J ∈ S, J.carrier ⊆ I₀.carrier)
    (hscale : ∀ J ∈ S, J.length = (2 : ℝ) ^ (scale J + 2))
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier) :
    IsSparse (1 / 4) (↑(stoppingStepFamily S f (pStoppingMonitor g p hp) I₀) :
      Set RealInterval) ∧
      (∀ J ∈ goodCollection S f (pStoppingMonitor g p hp) I₀,
        intervalL1Average f J ≤ 10 * intervalL1Average f I₀ ∧
          (∫ x in J.carrier, ‖g x‖ ^ p) ≤
            (10 * intervalL1Average (pStoppingMonitor g p hp) I₀) * J.length) ∧
      (∀ K ∈ stoppingChildren S f (pStoppingMonitor g p hp) I₀, ∀ x,
        x ∉ K.carrier →
          localizedTailMaximal ell₀ scale (childCollection S K) f x = 0) ∧
      (∫⁻ x, localizedTailMaximal ell₀ scale S f x * ‖g x‖ₑ) ≤
        (∫⁻ x, localizedTailMaximal ell₀ scale
          (goodCollection S f (pStoppingMonitor g p hp) I₀) f x * ‖g x‖ₑ) +
          ∑ K ∈ stoppingChildren S f (pStoppingMonitor g p hp) I₀,
            ∫⁻ x, localizedTailMaximal ell₀ scale
              (childCollection S K) f x * ‖g x‖ₑ := by
  classical
  let monitor := pStoppingMonitor g p hp
  have hmi : Integrable monitor := monitor.integrable
  refine ⟨root_insert_stoppingChildren_isSparse f monitor I₀ hfi hmi hlam, ?_, ?_, ?_⟩
  · intro J hJ
    exact ⟨(goodCollection_averages_le hsub hJ).1,
      goodCollection_pMass_le g hp hsub hJ⟩
  · intro K hK x hx
    apply localizedTailMaximal_eq_zero_of_notMem ell₀ scale (childCollection S K) f K
      (fun J hJ ↦ hscale J (Finset.mem_filter.mp hJ).1)
      (fun J hJ ↦ (Finset.mem_filter.mp hJ).2) hx
  · exact localizedTailMaximal_pairing_le_monitorGood_add_children
      ell₀ scale hf g.measurable_toFun I₀ hlam


end KrauseLaceyPStoppingRecursion
end QuadraticCarleson
