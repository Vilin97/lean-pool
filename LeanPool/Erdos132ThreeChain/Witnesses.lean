/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos132ThreeChain.Statement
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Witnesses and the determinant form of the five-point obstruction

Two things are recorded here.

First, the four-point catalogue is not vacuous: `rhombus_chain_config` and
`centroid_chain_config` exhibit the two planar patterns of the chain-quadruple theorem — the
rhombus made of two equilateral triangles glued along an edge (five short edges and one long
one) and the equilateral triangle together with its centroid (three short edges and three long
ones).  Both have all six squared distances inside the adjacent pair `{1, 3}`.

Second, `symDet4_chain_five` records the determinant form of the five-point obstruction.  The
doubled anchored Gram matrix of the only assignment that survives the four-point catalogue has
determinant `-27 * r ^ 4`, whereas `symDet4_dotp_eq_zero` shows that the Gram matrix of four
plane vectors is singular.  `no_four_on_circle` proves the same obstruction in the
equivalent sum-of-squares form, which avoids having to enumerate principal minors at all.
-/

namespace Erdos132ThreeChain

/-- The determinant of the symmetric `4 × 4` matrix with diagonal `d₁ d₂ d₃ d₄` and
off-diagonal entries `eᵢⱼ`. -/
def symDet4 (d₁ d₂ d₃ d₄ e₁₂ e₁₃ e₁₄ e₂₃ e₂₄ e₃₄ : ℝ) : ℝ :=
  d₁ * d₂ * d₃ * d₄ - d₁ * d₂ * e₃₄ ^ 2 - d₁ * d₃ * e₂₄ ^ 2 - d₁ * d₄ * e₂₃ ^ 2
    + 2 * d₁ * e₂₃ * e₂₄ * e₃₄ - d₂ * d₃ * e₁₄ ^ 2 - d₂ * d₄ * e₁₃ ^ 2
    + 2 * d₂ * e₁₃ * e₁₄ * e₃₄ - d₃ * d₄ * e₁₂ ^ 2 + 2 * d₃ * e₁₂ * e₁₄ * e₂₄
    + 2 * d₄ * e₁₂ * e₁₃ * e₂₃ + e₁₂ ^ 2 * e₃₄ ^ 2 - 2 * e₁₂ * e₁₃ * e₂₄ * e₃₄
    - 2 * e₁₂ * e₁₄ * e₂₃ * e₃₄ + e₁₃ ^ 2 * e₂₄ ^ 2 - 2 * e₁₃ * e₁₄ * e₂₃ * e₂₄
    + e₁₄ ^ 2 * e₂₃ ^ 2

/-- The Gram matrix of four vectors of the plane is singular. -/
theorem symDet4_dotp_eq_zero (o p q r s : Point) :
    symDet4 (dotp o p p) (dotp o q q) (dotp o r r) (dotp o s s) (dotp o p q) (dotp o p r)
      (dotp o p s) (dotp o q r) (dotp o q s) (dotp o r s) = 0 := by
  simp only [symDet4, dotp]; ring

/-- The doubled anchored Gram determinant of the only five-point assignment that survives the
four-point catalogue — a triangle of `3 * r` edges together with seven `r` edges — equals
`-27 * r ^ 4`. -/
theorem symDet4_chain_five (r : ℝ) :
    symDet4 (2 * r) (2 * r) (2 * r) (2 * r) r r r (-r) (-r) (-r) = -27 * r ^ 4 := by
  simp only [symDet4]; ring

theorem symDet4_chain_five_ne_zero {r : ℝ} (hr : 0 < r) :
    symDet4 (2 * r) (2 * r) (2 * r) (2 * r) r r r (-r) (-r) (-r) ≠ 0 := by
  rw [symDet4_chain_five]
  have : (0 : ℝ) < r ^ 4 := by positivity
  linarith

/-- The rhombus of two equilateral triangles glued along an edge: five squared distances equal
`1` and one equals `3`.  This is the first pattern of the four-point catalogue, and it witnesses
that the hypotheses of `four_chain_adjacent` are satisfiable. -/
theorem rhombus_chain_config :
    ∃ A B C D : Point, A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
      sqDist A B = 1 ∧ sqDist A C = 1 ∧ sqDist A D = 1 ∧ sqDist B C = 1 ∧ sqDist B D = 1 ∧
      sqDist C D = 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨(-(1 / 2), 0), (1 / 2, 0), (0, Real.sqrt 3 / 2), (0, -(Real.sqrt 3 / 2)), ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [sqDist, Prod.mk.injEq, ne_eq, not_and] <;> intros <;> nlinarith [h3, hpos]

/-- The equilateral triangle together with its centroid: three squared distances equal `1` and
three equal `3`.  This is the second pattern of the four-point catalogue. -/
theorem centroid_chain_config :
    ∃ A B C D : Point, A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
      sqDist A B = 1 ∧ sqDist A C = 1 ∧ sqDist A D = 1 ∧ sqDist B C = 3 ∧ sqDist B D = 3 ∧
      sqDist C D = 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨(0, 0), (1, 0), (-(1 / 2), Real.sqrt 3 / 2), (-(1 / 2), -(Real.sqrt 3 / 2)), ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [sqDist, Prod.mk.injEq, ne_eq, not_and] <;> intros <;> nlinarith [h3, hpos]


/-- The rhombus witnesses that the definitions in the headline theorem are not vacuous: it is a
four-point set whose squared diameter is `3` and whose set of non-diameter squared distances is
exactly the one-term geometric 3-chain `{1}`.  Thus `IsSqDiameter`, `nonDiameterSqDists` and
`chain` do realise the configuration that `threeChain_support_empty` forbids for `n ≥ 13`. -/
theorem rhombus_nonDiameter_support :
    ∃ X : Finset Point, X.card = 4 ∧ IsSqDiameter X 3 ∧ nonDiameterSqDists X 3 = chain 1 1 := by
  classical
  obtain ⟨A, B, C, D, hAB, hAC, hAD, hBC, hBD, hCD, dAB, dAC, dAD, dBC, dBD, dCD⟩ :=
    rhombus_chain_config
  have eBA : sqDist B A = 1 := by rw [sqDist_comm B A]; exact dAB
  have eCA : sqDist C A = 1 := by rw [sqDist_comm C A]; exact dAC
  have eDA : sqDist D A = 1 := by rw [sqDist_comm D A]; exact dAD
  have eCB : sqDist C B = 1 := by rw [sqDist_comm C B]; exact dBC
  have eDB : sqDist D B = 1 := by rw [sqDist_comm D B]; exact dBD
  have eDC : sqDist D C = 3 := by rw [sqDist_comm D C]; exact dCD
  have hmem : ∀ p ∈ ({A, B, C, D} : Finset Point), p = A ∨ p = B ∨ p = C ∨ p = D := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    tauto
  have hvals : ∀ p ∈ ({A, B, C, D} : Finset Point), ∀ q ∈ ({A, B, C, D} : Finset Point),
      sqDist p q = 0 ∨ sqDist p q = 1 ∨ sqDist p q = 3 := by
    intro p hp q hq
    rcases hmem p hp with rfl | rfl | rfl | rfl <;>
      rcases hmem q hq with rfl | rfl | rfl | rfl <;>
      first
        | exact Or.inl (sqDist_self _)
        | exact Or.inr (Or.inl (by assumption))
        | exact Or.inr (Or.inr (by assumption))
  refine ⟨{A, B, C, D}, ?_, ⟨⟨C, by simp, D, by simp, hCD, dCD⟩, ?_⟩, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hAB, hAC, hAD]),
      Finset.card_insert_of_notMem (by simp [hBC, hBD]),
      Finset.card_insert_of_notMem (by simp [hCD]), Finset.card_singleton]
  · intro p hp q hq
    rcases hvals p hp q hq with h | h | h <;> rw [h] <;> norm_num
  · ext x
    constructor
    · rintro ⟨p, hp, q, hq, hpq, rfl, hne⟩
      rcases hvals p hp q hq with h | h | h
      · exact absurd (sqDist_eq_zero_iff.mp h) hpq
      · exact ⟨0, by norm_num, by rw [h]; norm_num⟩
      · exact absurd h hne
    · rintro ⟨j, hj, rfl⟩
      have hj0 : j = 0 := by omega
      subst hj0
      exact ⟨A, by simp, B, by simp, hAB, by rw [dAB]; norm_num, by norm_num⟩


/-- Five points of the plane whose squared distances are `1`, `3` and `4`: the rhombus of two
glued equilateral triangles together with the reflection of one vertex.  Its squared diameter is
`4`, realised once, and both `1` and `3` occur as non-diameter squared distances. -/
theorem chainTwo_config :
    ∃ A B C E F : Point,
      A ≠ B ∧ A ≠ C ∧ A ≠ E ∧ A ≠ F ∧ B ≠ C ∧ B ≠ E ∧ B ≠ F ∧ C ≠ E ∧ C ≠ F ∧ E ≠ F ∧
      sqDist A B = 1 ∧ sqDist A C = 1 ∧ sqDist A E = 1 ∧ sqDist A F = 3 ∧ sqDist B C = 3 ∧
      sqDist B E = 1 ∧ sqDist B F = 4 ∧ sqDist C E = 1 ∧ sqDist C F = 1 ∧ sqDist E F = 1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨(0, 0), (1, 0), (-(1 / 2), Real.sqrt 3 / 2), (1 / 2, Real.sqrt 3 / 2),
    (0, Real.sqrt 3), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩ <;>
    simp only [sqDist, Prod.mk.injEq, ne_eq, not_and] <;> intros <;> nlinarith [h3, hpos]

/-- **A witness at chain length two.**  There is a five-point set of the plane whose squared
diameter is `4` and whose set of non-diameter squared distances is exactly the two-term
geometric 3-chain `chain 1 2 = {1, 3}`.  Thus the configuration that
`nonDiameterSqDists_ne_chain` forbids once `n ≥ 13` is realisable at `n = 5` with `h = 2`, so
the headline is not vacuous in its own `h ≥ 2` regime. -/
theorem chainTwo_nonDiameter_support :
    ∃ X : Finset Point, X.card = 5 ∧ IsSqDiameter X 4 ∧ nonDiameterSqDists X 4 = chain 1 2 := by
  classical
  obtain ⟨A, B, C, E, F, hAB, hAC, hAE, hAF, hBC, hBE, hBF, hCE, hCF, hEF,
    dAB, dAC, dAE, dAF, dBC, dBE, dBF, dCE, dCF, dEF⟩ := chainTwo_config
  have eBA : sqDist B A = 1 := by rw [sqDist_comm B A]; exact dAB
  have eCA : sqDist C A = 1 := by rw [sqDist_comm C A]; exact dAC
  have eEA : sqDist E A = 1 := by rw [sqDist_comm E A]; exact dAE
  have eFA : sqDist F A = 3 := by rw [sqDist_comm F A]; exact dAF
  have eCB : sqDist C B = 3 := by rw [sqDist_comm C B]; exact dBC
  have eEB : sqDist E B = 1 := by rw [sqDist_comm E B]; exact dBE
  have eFB : sqDist F B = 4 := by rw [sqDist_comm F B]; exact dBF
  have eEC : sqDist E C = 1 := by rw [sqDist_comm E C]; exact dCE
  have eFC : sqDist F C = 1 := by rw [sqDist_comm F C]; exact dCF
  have eFE : sqDist F E = 1 := by rw [sqDist_comm F E]; exact dEF
  have hmem : ∀ p ∈ ({A, B, C, E, F} : Finset Point), p = A ∨ p = B ∨ p = C ∨ p = E ∨ p = F := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    tauto
  have hvals : ∀ p ∈ ({A, B, C, E, F} : Finset Point), ∀ q ∈ ({A, B, C, E, F} : Finset Point),
      sqDist p q = 0 ∨ sqDist p q = 1 ∨ sqDist p q = 3 ∨ sqDist p q = 4 := by
    intro p hp q hq
    rcases hmem p hp with rfl | rfl | rfl | rfl | rfl <;>
      rcases hmem q hq with rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact Or.inl (sqDist_self _)
        | exact Or.inr (Or.inl (by assumption))
        | exact Or.inr (Or.inr (Or.inl (by assumption)))
        | exact Or.inr (Or.inr (Or.inr (by assumption)))
  refine ⟨{A, B, C, E, F}, ?_, ⟨⟨B, by simp, F, by simp, hBF, dBF⟩, ?_⟩, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hAB, hAC, hAE, hAF]),
      Finset.card_insert_of_notMem (by simp [hBC, hBE, hBF]),
      Finset.card_insert_of_notMem (by simp [hCE, hCF]),
      Finset.card_insert_of_notMem (by simp [hEF]), Finset.card_singleton]
  · intro p hp q hq
    rcases hvals p hp q hq with h | h | h | h <;> rw [h] <;> norm_num
  · ext x
    constructor
    · rintro ⟨p, hp, q, hq, hpq, rfl, hne⟩
      rcases hvals p hp q hq with h | h | h | h
      · exact absurd (sqDist_eq_zero_iff.mp h) hpq
      · exact ⟨0, by norm_num, by rw [h]; norm_num⟩
      · exact ⟨1, by norm_num, by rw [h]; norm_num⟩
      · exact absurd h hne
    · rintro ⟨j, hj, rfl⟩
      have hj2 : j = 0 ∨ j = 1 := by omega
      rcases hj2 with rfl | rfl
      · exact ⟨A, by simp, B, by simp, hAB, by rw [dAB]; norm_num, by norm_num⟩
      · exact ⟨A, by simp, F, by simp, hAF, by rw [dAF]; norm_num, by norm_num⟩

end Erdos132ThreeChain
