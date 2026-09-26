/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTRieszSelection
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientSymmetricGeometry
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics

/-! # Time and space restrictions of measurable Riesz sources

A source restricted to a measurable spatial ball and time window has globally
integrable slices almost everywhere when the original slices are integrable
on that window. Its completed Riesz representative is selected on all times.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Step4

/-- Restriction to a product window turns restricted almost-everywhere slice
integrability into a statement on the entire time axis. -/
theorem memLp_product_indicator_slices
    {F : Vec3 × ℝ → ℝ} {B : Set Vec3} {J : Set ℝ}
    (hB : MeasurableSet B) (hJ : MeasurableSet J)
    (hF : ∀ᵐ s ∂volume.restrict J,
      MemLp (fun y => F (y, s)) (ENNReal.ofReal (6 / 5 : ℝ)) volume) :
    ∀ᵐ s ∂volume, MemLp (fun y => (B ×ˢ J).indicator F (y, s))
      (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
  filter_upwards [(ae_restrict_iff' hJ).mp hF] with s hs
  by_cases hsj : s ∈ J
  · have heq : (fun y => (B ×ˢ J).indicator F (y, s)) =
        B.indicator (fun y => F (y, s)) := by
      funext y
      by_cases hy : y ∈ B <;> simp only [Set.indicator, mem_prod, hy, hsj, and_self, false_and,
        ↓reduceIte]
    rw [heq]
    exact (hs hsj).indicator hB
  · have heq : (fun y => (B ×ˢ J).indicator F (y, s)) = fun _ => 0 := by
      funext y
      exact Set.indicator_of_notMem (fun h => hsj h.2) F
    rw [heq]
    exact MemLp.zero

/-- The completed Riesz operator of a ball-and-time restricted source admits
one jointly measurable representative over the whole time axis. -/
theorem exists_measurable_riesz_extension_field_on_window (j i : Fin 3)
    {F : Vec3 × ℝ → ℝ} {x : Vec3} {r : ℝ} (hr : 0 < r)
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hF : AEMeasurable ((vec3Ball x r ×ˢ J).indicator F) volume)
    (hFs : ∀ᵐ s ∂volume.restrict J,
      MemLp (fun y => F (y, s)) (ENNReal.ofReal (6 / 5 : ℝ)) volume) :
    ∃ T : Vec3 × ℝ → ℝ, Measurable T ∧
      ∀ᵐ s ∂volume, (fun y => T (y, s)) =ᵐ[volume]
        rieszSecondGradientExtensionOperator
          (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i)
          (fun y => (vec3Ball x r ×ˢ J).indicator F (y, s)) := by
  apply exists_measurable_riesz_extension_field_of_aemeasurable j i hF
    (CKN.Foundation.Parabolic.isCompact_closure_vec3Ball hr)
  · intro y s hy
    exact Set.indicator_of_notMem (fun h => hy (subset_closure h.1)) F
  · exact memLp_product_indicator_slices (isOpen_vec3Ball _ _).measurableSet hJ hFs

end CKN.Core.Step4
