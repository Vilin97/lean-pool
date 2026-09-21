/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
public import Mathlib.Analysis.Normed.Group.Bounded
public import LeanPool.PoincareGeometry.RellichKondrachov.MeasureTheory.Function.LpSpace.Restrict

/-! # Bounded measurable scalar multipliers on L² -/

@[expose] public noncomputable section
open MeasureTheory Filter
namespace AlmostSchur

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Bounded measurable multiplication preserves square integrability. -/
theorem memLp_bounded_mul (a : α → ℝ) (ha : AEStronglyMeasurable a μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) (u : Lp ℝ 2 μ) :
    MemLp (fun x => a x * u x) 2 μ := by
  apply (Lp.memLp u).of_le_mul (c := C) (ha.mul (Lp.aestronglyMeasurable u))
  filter_upwards [hb] with x hx
  simpa only [Pi.mul_apply, norm_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg (u x))

/-- The actual product as a bounded linear L² operator. -/
def boundedL2Multiplier (a : α → ℝ) (ha : AEStronglyMeasurable a μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun u => (memLp_bounded_mul a ha C hb u).toLp _
      map_add' := by
        intro u w
        change (memLp_bounded_mul a ha C hb (u + w)).toLp _ =
          (memLp_bounded_mul a ha C hb u).toLp _ + (memLp_bounded_mul a ha C hb w).toLp _
        apply Lp.ext
        filter_upwards [(memLp_bounded_mul a ha C hb (u + w)).coeFn_toLp,
          (memLp_bounded_mul a ha C hb u).coeFn_toLp,
          (memLp_bounded_mul a ha C hb w).coeFn_toLp,
          Lp.coeFn_add u w,
          Lp.coeFn_add ((memLp_bounded_mul a ha C hb u).toLp _)
            ((memLp_bounded_mul a ha C hb w).toLp _)] with x hx hu hw hs ht
        refine hx.trans ?_
        rw [ht]
        change a x * (u + w) x = _ + _
        rw [hu, hw, hs]
        exact mul_add _ _ _
      map_smul' := by
        intro r u
        apply Lp.ext
        filter_upwards [(memLp_bounded_mul a ha C hb (r • u)).coeFn_toLp,
          (memLp_bounded_mul a ha C hb u).coeFn_toLp, Lp.coeFn_smul r u,
          Lp.coeFn_smul r ((memLp_bounded_mul a ha C hb u).toLp _)] with x hx hu hs ht
        simp [hx, ht, hu, hs, mul_left_comm] }
    C (by
      intro u
      change ‖(memLp_bounded_mul a ha C hb u).toLp _‖ ≤ C * ‖u‖
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(memLp_bounded_mul a ha C hb u).coeFn_toLp, hb] with x hx hb
      rw [hx, norm_mul]
      exact mul_le_mul_of_nonneg_right hb (norm_nonneg _))

/-- The bounded operator retains the actual multiplication representative. -/
theorem boundedL2Multiplier_ae_eq (a : α → ℝ) (ha : AEStronglyMeasurable a μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) (u : Lp ℝ 2 μ) :
    boundedL2Multiplier a ha C hb u =ᵐ[μ] (fun x => a x * u x) :=
  (memLp_bounded_mul a ha C hb u).coeFn_toLp

/-- Multiplication by a compact cutoff followed by extension from a measurable
set has the expected global representative whenever the cutoff is supported there. -/
theorem exists_cutoffL2Extension [TopologicalSpace α] [BorelSpace α]
    (a : α → ℝ) (ha : Continuous a) (hc : HasCompactSupport a)
    {K : Set α} (hK : MeasurableSet K) (hs : tsupport a ⊆ K) :
    ∃ S : Lp ℝ 2 (μ.restrict K) →L[ℝ] Lp ℝ 2 μ,
      ∀ (u : Lp ℝ 2 (μ.restrict K)) (f : α → ℝ), u =ᵐ[μ.restrict K] f →
        S u =ᵐ[μ] (fun x => a x * f x) := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous ha
  let A := boundedL2Multiplier (μ := μ) a ha.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  let Z := (Lp.extendByZeroₗᵢ (μ := μ) (E := ℝ) (p := 2) hK).toContinuousLinearMap
  refine ⟨A.comp Z, ?_⟩
  intro u f hf
  have hf' := (ae_restrict_iff' hK).mp hf
  filter_upwards [boundedL2Multiplier_ae_eq a ha.aestronglyMeasurable C
    (Filter.Eventually.of_forall hC) (Z u), Lp.extendByZeroₗᵢ_ae_eq hK u, hf']
    with x hx hz hf
  change A (Z u) x = _
  rw [hx]
  change a x * ((Lp.extendByZeroₗᵢ hK) u) x = _
  rw [hz]
  by_cases hk : x ∈ K
  · simp [hk, hf hk]
  · have hz : a x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hk (hs h))
    simp [hk, hz]

end AlmostSchur
