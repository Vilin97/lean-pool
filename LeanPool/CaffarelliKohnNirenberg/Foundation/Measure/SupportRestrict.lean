/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Support Restrict

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set
open CKN.Foundation.Parabolic
open scoped ENNReal


noncomputable section

namespace CKN.Foundation.Measure

/-- If a function is almost everywhere strongly measurable with respect to the
restricted measure `volume.restrict s` and its support is contained in the
measurable set `s`, then it is almost everywhere strongly measurable with
respect to the ambient `volume`. -/
theorem aestronglyMeasurable_of_restrict_of_support
    {h : Vec3 → ℝ} {s : Set Vec3} (hs : MeasurableSet s)
    (hmeas : AEStronglyMeasurable h (volume.restrict s))
    (hsupp : Function.support h ⊆ s) :
    AEStronglyMeasurable h volume := by
  have h1 : AEMeasurable (s.indicator h) volume :=
    (aemeasurable_indicator_iff hs).2 hmeas.aemeasurable
  have heq : s.indicator h = h := by
    funext y
    by_cases hy : y ∈ s
    · simp [Set.indicator_of_mem hy]
    · have hz : h y = 0 := by
        by_contra hne
        exact hy (hsupp hne)
      simp [Set.indicator_of_notMem hy, hz]
  rw [heq] at h1
  exact h1.aestronglyMeasurable

/-- If a function is `MemLp` on the restricted measure `volume.restrict s` and its
support is contained in the measurable set `s`, then it is `MemLp` on the
ambient `volume`. -/
theorem memLp_volume_of_memLp_restrict_of_support
    {h : Vec3 → ℝ} {s : Set Vec3} {p : ℝ≥0∞}
    (hmeas : AEStronglyMeasurable h volume) (hsupp : Function.support h ⊆ s)
    (hh : MemLp h p (volume.restrict s)) :
    MemLp h p volume := by
  rw [memLp_iff] at hh ⊢
  rwa [eLpNorm_restrict_eq_of_support_subset hmeas hsupp] at hh

/-- A continuous compactly supported multiplier localizes an integrable function. -/
theorem integrable_mul_of_tsupport_subset {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {μ : Measure α} {s : Set α} {f g : α → ℝ}
    (hf : IntegrableOn f s μ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupport : tsupport g ⊆ s) : Integrable (fun x => f x * g x) μ := by
  obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg
  have hmul : IntegrableOn (fun x => f x * g x) s μ :=
    hf.mul_bdd hg.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC x)
  exact hmul.integrable_of_forall_notMem_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (f := g) (fun h => hx (hsupport h)), mul_zero])

end CKN.Foundation.Measure
