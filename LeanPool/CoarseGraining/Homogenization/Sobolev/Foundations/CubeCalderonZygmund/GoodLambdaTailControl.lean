/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.OneStoppingBallTail

/-! # Good Lambda Tail Control -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory Set

/-!
# The control measure for the one-ball good-`λ` estimate

The local stopping-ball estimate has two lower-level weighted tails on its
right-hand side.  This file packages precisely their sum as a measure.  The
evaluation lemmas below are deliberately stated on measurable sets, which is
what the Vitali assembly consumes; no measurability is hidden in the
definition of the restricted measures.
-/

/-- The two lower-level square-weighted tails which control a stopping ball. -/
def oneStoppingBallTailControl
    {d : ℕ} {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    (f : Vec d → F) (g : Vec d → G) (eps level : ℝ) : Measure (Vec d) :=
  (sqWeightedMeasure f volume).restrict {x | level / 2 < ‖f x‖} +
    ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) •
      (sqWeightedMeasure g volume).restrict {x | eps * level / 2 < ‖g x‖}

/-- Evaluation of the one-ball control measure on a measurable set.  The
intersection order agrees exactly with the lower tails in
`sqWeightedMeasure_oneStoppingBall_le`. -/
theorem oneStoppingBallTailControl_apply
    {d : ℕ} {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    (f : Vec d → F) (g : Vec d → G) (eps level : ℝ) {B : Set (Vec d)}
    (hB : MeasurableSet B) :
    oneStoppingBallTailControl f g eps level B =
      sqWeightedMeasure f volume ({x | level / 2 < ‖f x‖} ∩ B) +
        ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
          sqWeightedMeasure g volume
            ({x | eps * level / 2 < ‖g x‖} ∩ B) := by
  rw [oneStoppingBallTailControl, Measure.add_apply,
    Measure.restrict_apply hB, Measure.smul_apply, Measure.restrict_apply hB]
  simp only [smul_eq_mul, Set.inter_comm]

/-- The ambient-set specialization of `oneStoppingBallTailControl_apply`. -/
theorem oneStoppingBallTailControl_apply_ambient
    {d : ℕ} {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    (f : Vec d → F) (g : Vec d → G) (eps level : ℝ) {U : Set (Vec d)}
    (hU : MeasurableSet U) :
    oneStoppingBallTailControl f g eps level U =
      sqWeightedMeasure f volume ({x | level / 2 < ‖f x‖} ∩ U) +
        ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
          sqWeightedMeasure g volume
            ({x | eps * level / 2 < ‖g x‖} ∩ U) :=
  oneStoppingBallTailControl_apply f g eps level hU

/-- The first lower-tail set is volume-null-measurable when the field is
almost-everywhere strongly measurable. -/
theorem nullMeasurableSet_oneStoppingBall_f_tail
    {d : ℕ} {F : Type*} [NormedAddCommGroup F]
    (f : Vec d → F) (level : ℝ) (hf : AEStronglyMeasurable f volume) :
    NullMeasurableSet {x | level / 2 < ‖f x‖} volume := by
  simpa using aestronglyMeasurable_const.nullMeasurableSet_lt hf.norm

/-- The scaled second lower-tail set is volume-null-measurable when the field
is almost-everywhere strongly measurable. -/
theorem nullMeasurableSet_oneStoppingBall_g_tail
    {d : ℕ} {G : Type*} [NormedAddCommGroup G]
    (g : Vec d → G) (eps level : ℝ) (hg : AEStronglyMeasurable g volume) :
    NullMeasurableSet {x | eps * level / 2 < ‖g x‖} volume := by
  simpa using aestronglyMeasurable_const.nullMeasurableSet_lt hg.norm

end CubeCalderonZygmund

end

end Homogenization
