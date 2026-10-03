/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.JetSeparation
public import LeanPool.BooleanMultiplication.N4.BooleanIdentities

/-!
# Algebraic feedback-state lemmas

The feedback state has quadratic target space
`S = ⟨E₀,E₁,E₆,r₁⟩`.  The only relation among its six pair wedges is
`E₀ ∧ E₁ = 0`.  We prove this from the five coordinate rows displayed in
the manuscript and derive the zero-wedge structure needed by the low--low
second-feedback exclusion.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Coordinates in the basis consisting of the first, second, last, and evaluation-at-one
targets. -/
abbrev FeedbackCoord := Fin 4 → F₂

/-- Represent feedback coordinates in the target coefficient space. -/
@[expose] def feedbackCoeffRep (q : FeedbackCoord) : TargetCoeff :=
  q 0 • targetBasis 0 + q 1 • targetBasis 1 +
    q 2 • targetBasis 6 + q 3 • rOneCoeff

/-- A two-by-two minor of the two feedback coordinate vectors. -/
def feedbackMinor (q c : FeedbackCoord) (i j : Fin 4) : F₂ :=
  q i * c j + q j * c i

private theorem feedback_wedge_row0 (q c : FeedbackCoord) :
    wedgeTwo (targetTwo (feedbackCoeffRep q))
      (targetTwo (feedbackCoeffRep c)) 0 1 4 5 =
      feedbackMinor q c 0 3 := by
  simp [wedgeTwo, targetTwo, feedbackCoeffRep, feedbackMinor, targetBasis, Pi.basisFun]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2]

private theorem feedback_wedge_row1 (q c : FeedbackCoord) :
    wedgeTwo (targetTwo (feedbackCoeffRep q))
      (targetTwo (feedbackCoeffRep c)) 0 1 4 6 =
      feedbackMinor q c 0 3 + feedbackMinor q c 1 3 := by
  simp [wedgeTwo, targetTwo, feedbackCoeffRep, feedbackMinor, targetBasis, Pi.basisFun]
  ring_nf
  simp [N3Certificate.four_eq_zero_f2]

private theorem feedback_wedge_row2 (q c : FeedbackCoord) :
    wedgeTwo (targetTwo (feedbackCoeffRep q))
      (targetTwo (feedbackCoeffRep c)) 0 3 4 7 =
      feedbackMinor q c 0 2 + feedbackMinor q c 0 3 +
        feedbackMinor q c 2 3 := by
  simp [wedgeTwo, targetTwo, feedbackCoeffRep, feedbackMinor, targetBasis, Pi.basisFun]
  ring_nf
  simp [N3Certificate.four_eq_zero_f2]

private theorem feedback_wedge_row3 (q c : FeedbackCoord) :
    wedgeTwo (targetTwo (feedbackCoeffRep q))
      (targetTwo (feedbackCoeffRep c)) 0 3 5 7 =
      feedbackMinor q c 1 2 + feedbackMinor q c 1 3 +
        feedbackMinor q c 2 3 := by
  simp [wedgeTwo, targetTwo, feedbackCoeffRep, feedbackMinor, targetBasis, Pi.basisFun]
  ring_nf
  simp [N3Certificate.four_eq_zero_f2]

private theorem feedback_wedge_row4 (q c : FeedbackCoord) :
    wedgeTwo (targetTwo (feedbackCoeffRep q))
      (targetTwo (feedbackCoeffRep c)) 0 3 6 7 =
      feedbackMinor q c 2 3 := by
  simp [wedgeTwo, targetTwo, feedbackCoeffRep, feedbackMinor, targetBasis, Pi.basisFun]
  ring_nf
  simp [N3Certificate.four_eq_zero_f2]

theorem feedback_wedge_relations {q c : FeedbackCoord}
    (h : wedgeTwo (targetTwo (feedbackCoeffRep q))
      (targetTwo (feedbackCoeffRep c)) = 0) :
    feedbackMinor q c 0 2 = 0 ∧
    feedbackMinor q c 0 3 = 0 ∧
    feedbackMinor q c 1 2 = 0 ∧
    feedbackMinor q c 1 3 = 0 ∧
    feedbackMinor q c 2 3 = 0 := by
  have r0 := congrFun (congrFun (congrFun (congrFun h 0) 1) 4) 5
  have r1 := congrFun (congrFun (congrFun (congrFun h 0) 1) 4) 6
  have r2 := congrFun (congrFun (congrFun (congrFun h 0) 3) 4) 7
  have r3 := congrFun (congrFun (congrFun (congrFun h 0) 3) 5) 7
  have r4 := congrFun (congrFun (congrFun (congrFun h 0) 3) 6) 7
  rw [feedback_wedge_row0] at r0
  rw [feedback_wedge_row1] at r1
  rw [feedback_wedge_row2] at r2
  rw [feedback_wedge_row3] at r3
  rw [feedback_wedge_row4] at r4
  simp only [Pi.zero_apply] at r0 r1 r2 r3 r4
  have h03 : feedbackMinor q c 0 3 = 0 := r0
  have h13 : feedbackMinor q c 1 3 = 0 := by
    rw [h03, zero_add] at r1
    exact r1
  have h23 : feedbackMinor q c 2 3 = 0 := r4
  have h12 : feedbackMinor q c 1 2 = 0 := by
    rw [h13, h23, add_zero, add_zero] at r3
    exact r3
  have h02 : feedbackMinor q c 0 2 = 0 := by
    rw [h03, h23, add_zero, add_zero] at r2
    exact r2
  exact ⟨h02, h03, h12, h13, h23⟩

/-- The feedback vector lies in the plane of the first two target coefficients. -/
@[expose]
def InFirstJetPlane (q : FeedbackCoord) : Prop := q 2 = 0 ∧ q 3 = 0

theorem feedback_dependent_or_firstJetPlane {q c : FeedbackCoord}
    (h02 : feedbackMinor q c 0 2 = 0)
    (h03 : feedbackMinor q c 0 3 = 0)
    (h12 : feedbackMinor q c 1 2 = 0)
    (h13 : feedbackMinor q c 1 3 = 0)
    (h23 : feedbackMinor q c 2 3 = 0) :
    q = 0 ∨ c = 0 ∨ q = c ∨
      (InFirstJetPlane q ∧ InFirstJetPlane c) := by
  by_cases h01 : feedbackMinor q c 0 1 = 0
  · change q 0 * c 1 + q 1 * c 0 = 0 at h01
    change q 0 * c 2 + q 2 * c 0 = 0 at h02
    change q 0 * c 3 + q 3 * c 0 = 0 at h03
    change q 1 * c 2 + q 2 * c 1 = 0 at h12
    change q 1 * c 3 + q 3 * c 1 = 0 at h13
    change q 2 * c 3 + q 3 * c 2 = 0 at h23
    have hall : ∀ i j, q i * c j + q j * c i = 0 := by
      intro i j
      fin_cases i <;> fin_cases j
      · exact CharTwo.add_self_eq_zero _
      · exact h01
      · exact h02
      · exact h03
      · rw [add_comm]
        exact h01
      · exact CharTwo.add_self_eq_zero _
      · exact h12
      · exact h13
      · rw [add_comm]
        exact h02
      · rw [add_comm]
        exact h12
      · exact CharTwo.add_self_eq_zero _
      · exact h23
      · rw [add_comm]
        exact h03
      · rw [add_comm]
        exact h13
      · rw [add_comm]
        exact h23
      · exact CharTwo.add_self_eq_zero _
    rcases dependent_of_vectorWedge_zero q c hall with hq | hc | hqc
    · exact Or.inl hq
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr (Or.inl hqc))
  · have h01one : feedbackMinor q c 0 1 = 1 :=
      (f2_eq_zero_or_one _).resolve_left h01
    have q2identity :
        q 2 * feedbackMinor q c 0 1 =
          q 0 * feedbackMinor q c 1 2 +
            q 1 * feedbackMinor q c 0 2 := by
      simp [feedbackMinor]
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    have c2identity :
        c 2 * feedbackMinor q c 0 1 =
          c 0 * feedbackMinor q c 1 2 +
            c 1 * feedbackMinor q c 0 2 := by
      simp [feedbackMinor]
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    have q3identity :
        q 3 * feedbackMinor q c 0 1 =
          q 0 * feedbackMinor q c 1 3 +
            q 1 * feedbackMinor q c 0 3 := by
      simp [feedbackMinor]
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    have c3identity :
        c 3 * feedbackMinor q c 0 1 =
          c 0 * feedbackMinor q c 1 3 +
            c 1 * feedbackMinor q c 0 3 := by
      simp [feedbackMinor]
      ring_nf
      simp [N3Certificate.two_eq_zero_f2]
    have hq2 : q 2 = 0 := by
      rw [h01one, h12, h02] at q2identity
      simpa using q2identity
    have hc2 : c 2 = 0 := by
      rw [h01one, h12, h02] at c2identity
      simpa using c2identity
    have hq3 : q 3 = 0 := by
      rw [h01one, h13, h03] at q3identity
      simpa using q3identity
    have hc3 : c 3 = 0 := by
      rw [h01one, h13, h03] at c3identity
      simpa using c3identity
    exact Or.inr (Or.inr (Or.inr ⟨⟨hq2, hq3⟩, ⟨hc2, hc3⟩⟩))

/-- Zero-wedge structure in `S`: either the two directions are dependent,
or both lie in `⟨E₀,E₁⟩`. -/
theorem feedback_zero_wedge_structure {q c : FeedbackCoord}
    (h : wedgeTwo (targetTwo (feedbackCoeffRep q))
      (targetTwo (feedbackCoeffRep c)) = 0) :
    q = 0 ∨ c = 0 ∨ q = c ∨
      (InFirstJetPlane q ∧ InFirstJetPlane c) := by
  rcases feedback_wedge_relations h with ⟨h02, h03, h12, h13, h23⟩
  exact feedback_dependent_or_firstJetPlane h02 h03 h12 h13 h23

/-- Row-wise form used by the ANF quartic bridge.  These are precisely the
five displayed rows of the manuscript's zero-wedge matrix. -/
theorem feedback_zero_wedge_structure_of_rows {q c : FeedbackCoord}
    (h0 : wedgeTwo (targetTwo (feedbackCoeffRep q))
      (targetTwo (feedbackCoeffRep c)) 0 1 4 5 = 0)
    (h1 : wedgeTwo (targetTwo (feedbackCoeffRep q))
      (targetTwo (feedbackCoeffRep c)) 0 1 4 6 = 0)
    (h2 : wedgeTwo (targetTwo (feedbackCoeffRep q))
      (targetTwo (feedbackCoeffRep c)) 0 3 4 7 = 0)
    (h3 : wedgeTwo (targetTwo (feedbackCoeffRep q))
      (targetTwo (feedbackCoeffRep c)) 0 3 5 7 = 0)
    (h4 : wedgeTwo (targetTwo (feedbackCoeffRep q))
      (targetTwo (feedbackCoeffRep c)) 0 3 6 7 = 0) :
    q = 0 ∨ c = 0 ∨ q = c ∨
      (InFirstJetPlane q ∧ InFirstJetPlane c) := by
  rw [feedback_wedge_row0] at h0
  rw [feedback_wedge_row1] at h1
  rw [feedback_wedge_row2] at h2
  rw [feedback_wedge_row3] at h3
  rw [feedback_wedge_row4] at h4
  have h03 : feedbackMinor q c 0 3 = 0 := h0
  have h13 : feedbackMinor q c 1 3 = 0 := by
    rw [h03, zero_add] at h1
    exact h1
  have h23 : feedbackMinor q c 2 3 = 0 := h4
  have h12 : feedbackMinor q c 1 2 = 0 := by
    rw [h13, h23, add_zero, add_zero] at h3
    exact h3
  have h02 : feedbackMinor q c 0 2 = 0 := by
    rw [h03, h23, add_zero, add_zero] at h2
    exact h2
  exact feedback_dependent_or_firstJetPlane h02 h03 h12 h13 h23

/-- The second-jet coefficient vector with its two lower-order parameters. -/
@[expose]
def secondJetFeedbackCoeff (α β : F₂) : TargetCoeff :=
  targetBasis 2 + α • targetBasis 1 + β • targetBasis 0

private theorem secondJet_feedback_row0 (α β : F₂) (q : FeedbackCoord) :
    wedgeTwo (targetTwo (secondJetFeedbackCoeff α β))
      (targetTwo (feedbackCoeffRep q)) 0 1 4 5 =
      q 0 + (1 + β) * q 3 := by
  simp [wedgeTwo, targetTwo, secondJetFeedbackCoeff, feedbackCoeffRep, targetBasis,
    Pi.basisFun]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

private theorem secondJet_feedback_row1 (α β : F₂) (q : FeedbackCoord) :
    wedgeTwo (targetTwo (secondJetFeedbackCoeff α β))
      (targetTwo (feedbackCoeffRep q)) 0 1 4 6 =
      q 1 + (1 + α + β) * q 3 := by
  simp [wedgeTwo, targetTwo, secondJetFeedbackCoeff, feedbackCoeffRep, targetBasis,
    Pi.basisFun]
  ring_nf

private theorem secondJet_feedback_row2 (α β : F₂) (q : FeedbackCoord) :
    wedgeTwo (targetTwo (secondJetFeedbackCoeff α β))
      (targetTwo (feedbackCoeffRep q)) 0 1 6 7 = q 3 := by
  simp [wedgeTwo, targetTwo, secondJetFeedbackCoeff, feedbackCoeffRep, targetBasis,
    Pi.basisFun]

private theorem secondJet_feedback_row3 (α β : F₂) (q : FeedbackCoord) :
    wedgeTwo (targetTwo (secondJetFeedbackCoeff α β))
      (targetTwo (feedbackCoeffRep q)) 0 3 6 7 = q 2 + q 3 := by
  simp [wedgeTwo, targetTwo, secondJetFeedbackCoeff, feedbackCoeffRep, targetBasis,
    Pi.basisFun]

/-- Wedge by any second-jet representative is injective on the feedback
state `S`. -/
theorem secondJet_wedge_feedback_injective (α β : F₂) (q : FeedbackCoord)
    (h : wedgeTwo (targetTwo (secondJetFeedbackCoeff α β))
      (targetTwo (feedbackCoeffRep q)) = 0) : q = 0 := by
  have r0 := congrFun (congrFun (congrFun (congrFun h 0) 1) 4) 5
  have r1 := congrFun (congrFun (congrFun (congrFun h 0) 1) 4) 6
  have r2 := congrFun (congrFun (congrFun (congrFun h 0) 1) 6) 7
  have r3 := congrFun (congrFun (congrFun (congrFun h 0) 3) 6) 7
  rw [secondJet_feedback_row0] at r0
  rw [secondJet_feedback_row1] at r1
  rw [secondJet_feedback_row2] at r2
  rw [secondJet_feedback_row3] at r3
  simp only [Pi.zero_apply] at r0 r1 r2 r3
  have h3 : q 3 = 0 := r2
  rw [h3, mul_zero, add_zero] at r0 r1
  rw [h3, add_zero] at r3
  funext i
  fin_cases i
  · exact r0
  · exact r1
  · exact r3
  · exact h3

/-- Four-row version of second-jet injectivity, matching the explicit minor
in the manuscript. -/
theorem secondJet_wedge_feedback_injective_of_rows
    (α β : F₂) (q : FeedbackCoord)
    (h0 : wedgeTwo (targetTwo (secondJetFeedbackCoeff α β))
      (targetTwo (feedbackCoeffRep q)) 0 1 4 5 = 0)
    (h1 : wedgeTwo (targetTwo (secondJetFeedbackCoeff α β))
      (targetTwo (feedbackCoeffRep q)) 0 1 4 6 = 0)
    (h2 : wedgeTwo (targetTwo (secondJetFeedbackCoeff α β))
      (targetTwo (feedbackCoeffRep q)) 0 1 6 7 = 0)
    (h3 : wedgeTwo (targetTwo (secondJetFeedbackCoeff α β))
      (targetTwo (feedbackCoeffRep q)) 0 3 6 7 = 0) : q = 0 := by
  rw [secondJet_feedback_row0] at h0
  rw [secondJet_feedback_row1] at h1
  rw [secondJet_feedback_row2] at h2
  rw [secondJet_feedback_row3] at h3
  have hq3 : q 3 = 0 := h2
  rw [hq3, mul_zero, add_zero] at h0 h1
  rw [hq3, add_zero] at h3
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h3
  · exact hq3

theorem secondJetFeedback_not_rankOne (α β : F₂) :
    ¬ HankelRankLEOne (secondJetFeedbackCoeff α β) := by
  intro h
  have hm := h (0 : Fin 4) 2 2 0
  simp [hankelMatrix, secondJetFeedbackCoeff, targetBasis, Pi.basisFun] at hm

/-- The alternating rank of a second-jet representative is at least four;
equivalently, wedging it with a vector is injective. -/
theorem secondJet_vector_wedge_injective (α β : F₂) (u : LinearForm)
    (h : vectorWedgeTwo u (targetTwo (secondJetFeedbackCoeff α β)) = 0) :
    u = 0 := by
  by_contra hu
  have hN : vectorWedgeTwoN u (targetTwo (secondJetFeedbackCoeff α β)) = 0 := by
    funext i j k
    have hij := congrFun (congrFun (congrFun h i) j) k
    simpa [vectorWedgeTwoN, vectorWedgeTwo] using hij
  rcases decomposable_of_vectorWedgeTwoN_zero u
    (targetTwo (secondJetFeedbackCoeff α β)) hu hN with ⟨v, hv⟩
  have hv' : targetTwo (secondJetFeedbackCoeff α β) = vectorWedge u v := by
    funext i j
    have hij := congrFun (congrFun hv i) j
    simpa [vectorWedgeN, vectorWedge] using hij
  have hdec : IsDecomposableTarget (secondJetFeedbackCoeff α β) := by
    refine ⟨u, v, ?_, ?_, ?_⟩
    · intro i j
      rw [← hv']
      exact targetTwo_sameA _ i j
    · intro i j
      rw [← hv']
      exact targetTwo_sameB _ i j
    · intro i j
      rw [crossPart, ← hv']
      exact (targetTwo_cross _ i j).symm
  exact secondJetFeedback_not_rankOne α β (decomposableTarget_rankOne hdec)

end

end N4
end UnrestrictedBooleanMul
