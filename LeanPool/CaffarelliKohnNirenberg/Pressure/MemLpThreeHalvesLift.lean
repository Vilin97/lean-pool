/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionSWSBasic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SupportRestrict

/-!
# Mem Lp Three Halves Lift

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory CKN.Foundation.Parabolic

namespace CKN

/-- A function in `L^{3/2}` of a finite-measure ball, with topological support
contained in that ball, is in `L^{3/2}` of the whole space. -/
theorem memLp_three_halves_of_restrict_of_tsupport_subset {g : Vec3 → ℝ} {B : Set Vec3}
    [IsFiniteMeasure (volume.restrict B)]
    (hB : MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict B))
    (hBsupport : tsupport g ⊆ B) :
    MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
  have hsupport : Function.support g ⊆ B :=
    (subset_tsupport (f := g)).trans hBsupport
  have hgint : Integrable g volume :=
    decomposition_full_of_on_sws (hB.integrable (by norm_num)) hBsupport
  exact CKN.Foundation.Measure.memLp_volume_of_memLp_restrict_of_support
    hgint.aestronglyMeasurable hsupport hB

end CKN
