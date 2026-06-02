/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.RectHomotopy.HomotopyDef

/-!
# Segment differentiability for the homotopy

Proves that each segment of `fdBoundaryToPolygonHomotopy`
is differentiable in t.
-/

open Complex Set Metric Filter Topology

namespace RectHomotopyProof

/-- Segment 1 formula (t < 1) is differentiable in t. -/
lemma fdBoundaryToPolygonHomotopy_seg1_differentiable (t _s : ℝ) :
    DifferentiableAt ℝ (fun t' : ℝ => (1/2 : ℂ) +
        (HHeight - (↑t' : ℂ) * (HHeight - Real.sqrt 3 / 2)) *
          I) t := by
  apply DifferentiableAt.add
  · exact differentiableAt_const _
  · apply DifferentiableAt.mul_const
    apply DifferentiableAt.sub
    · exact differentiableAt_const _
    · apply DifferentiableAt.mul
      · exact Complex.ofRealCLM.differentiableAt
      · exact differentiableAt_const _

/-- Segment 4 formula (3 < t ≤ 4) is differentiable in t. -/
lemma fdBoundaryToPolygonHomotopy_seg4_differentiable (t _s : ℝ) :
    DifferentiableAt ℝ (fun t' : ℝ => (-1/2 : ℂ) +
        (Real.sqrt 3 / 2 + ((↑t' : ℂ) - 3) *
            (HHeight - Real.sqrt 3 / 2)) *
          I) t := by
  apply DifferentiableAt.add
  · exact differentiableAt_const _
  · apply DifferentiableAt.mul_const
    apply DifferentiableAt.add
    · exact differentiableAt_const _
    · apply DifferentiableAt.mul
      · apply DifferentiableAt.sub
        · exact Complex.ofRealCLM.differentiableAt
        · exact differentiableAt_const _
      · exact differentiableAt_const _

/-- Segment 5 formula (t > 4) is differentiable in t. -/
lemma fdBoundaryToPolygonHomotopy_seg5_differentiable (t _s : ℝ) :
    DifferentiableAt ℝ (fun t' : ℝ => ((↑t' : ℂ) - 9/2) + HHeight * I) t := by
  apply DifferentiableAt.add
  · apply DifferentiableAt.sub
    · exact Complex.ofRealCLM.differentiableAt
    · exact differentiableAt_const _
  · exact differentiableAt_const _

/-- Segment 2 formula (1 < t ≤ 2) is differentiable in t. -/
lemma fdBoundaryToPolygonHomotopy_seg2_differentiable (t s : ℝ) :
    DifferentiableAt ℝ (fun t' : ℝ =>
      let arc_point :=
        Complex.exp ((Real.pi / 3 +
            (t' - 1) * (Real.pi / 2 -
                Real.pi / 3)) * I)
      let chord_point :=
        chordSegment rho' iPoint (t' - 1)
      (1 - s) • arc_point +
        s • chord_point) t := by
  simp only [chordSegment]
  refine DifferentiableAt.add ?_ ?_
  · have h_exp :
        DifferentiableAt ℝ (fun t' : ℝ =>
          Complex.exp ((Real.pi / 3 +
              (t' - 1) * (Real.pi / 2 -
                  Real.pi / 3)) * I)) t := by
      apply DifferentiableAt.cexp
      apply DifferentiableAt.mul_const
      refine DifferentiableAt.add (differentiableAt_const _) ?_
      refine DifferentiableAt.mul ?_ (differentiableAt_const _)
      convert
        Complex.ofRealCLM.differentiableAt.comp
          t (DifferentiableAt.sub
            differentiableAt_id (differentiableAt_const 1)) using 1
      funext y
      simp only [Function.comp_apply]
      exact (Complex.ofReal_sub y 1).symm
    exact h_exp.const_smul (1 - s)
  · have h_chord :
        DifferentiableAt ℝ (fun t' : ℝ => (1 - (t' - 1)) • rho' +
            (t' - 1) • iPoint) t := by
      have eq_mul : ∀ t' : ℝ, (1 - (t' - 1)) • rho' +
            (t' - 1) • iPoint =
          (↑(1 - (t' - 1)) : ℂ) * rho' + (↑(t' - 1) : ℂ) * iPoint :=
        fun _ => rfl
      simp only [eq_mul]
      refine DifferentiableAt.add ?_ ?_
      · have h1 : DifferentiableAt ℝ (fun t' : ℝ =>
              (↑(1 - (t' - 1)) : ℂ)) t :=
          Complex.ofRealCLM.differentiableAt.comp
            t (DifferentiableAt.sub (differentiableAt_const _)
              (DifferentiableAt.sub
                differentiableAt_id (differentiableAt_const _)))
        exact DifferentiableAt.mul h1 (differentiableAt_const _)
      · have h2 : DifferentiableAt ℝ (fun t' : ℝ =>
              (↑(t' - 1) : ℂ)) t :=
          Complex.ofRealCLM.differentiableAt.comp
            t (DifferentiableAt.sub
              differentiableAt_id (differentiableAt_const _))
        exact DifferentiableAt.mul h2 (differentiableAt_const _)
    exact h_chord.const_smul s

/-- Segment 3 formula (2 < t ≤ 3) is differentiable in t. -/
lemma fdBoundaryToPolygonHomotopy_seg3_differentiable (t s : ℝ) :
    DifferentiableAt ℝ (fun t' : ℝ =>
      let arc_point :=
        Complex.exp ((Real.pi / 2 +
            (t' - 2) * (2 * Real.pi / 3 -
                Real.pi / 2)) * I)
      let chord_point :=
        chordSegment iPoint rho (t' - 2)
      (1 - s) • arc_point +
        s • chord_point) t := by
  simp only [chordSegment]
  refine DifferentiableAt.add ?_ ?_
  · have h_exp :
        DifferentiableAt ℝ (fun t' : ℝ =>
          Complex.exp ((Real.pi / 2 +
              (t' - 2) * (2 * Real.pi / 3 -
                  Real.pi / 2)) * I)) t := by
      apply DifferentiableAt.cexp
      apply DifferentiableAt.mul_const
      refine DifferentiableAt.add (differentiableAt_const _) ?_
      refine DifferentiableAt.mul ?_ (differentiableAt_const _)
      convert
        Complex.ofRealCLM.differentiableAt.comp
          t (DifferentiableAt.sub
            differentiableAt_id (differentiableAt_const 2)) using 1
      funext y
      simp only [Function.comp_apply]
      exact (Complex.ofReal_sub y 2).symm
    exact h_exp.const_smul (1 - s)
  · have h_chord :
        DifferentiableAt ℝ (fun t' : ℝ => (1 - (t' - 2)) • iPoint +
            (t' - 2) • rho) t := by
      have eq_mul : ∀ t' : ℝ, (1 - (t' - 2)) • iPoint +
            (t' - 2) • rho =
          (↑(1 - (t' - 2)) : ℂ) * iPoint + (↑(t' - 2) : ℂ) * rho :=
        fun _ => rfl
      simp only [eq_mul]
      refine DifferentiableAt.add ?_ ?_
      · have h1 : DifferentiableAt ℝ (fun t' : ℝ =>
              (↑(1 - (t' - 2)) : ℂ)) t :=
          Complex.ofRealCLM.differentiableAt.comp
            t (DifferentiableAt.sub (differentiableAt_const _)
              (DifferentiableAt.sub
                differentiableAt_id (differentiableAt_const _)))
        exact DifferentiableAt.mul h1 (differentiableAt_const _)
      · have h2 : DifferentiableAt ℝ (fun t' : ℝ =>
              (↑(t' - 2) : ℂ)) t :=
          Complex.ofRealCLM.differentiableAt.comp
            t (DifferentiableAt.sub
              differentiableAt_id (differentiableAt_const _))
        exact DifferentiableAt.mul h2 (differentiableAt_const _)
    exact h_chord.const_smul s

end RectHomotopyProof
