/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffTransmission

/-!
# The first transmission row for a same-strand one-off marking

This begins the formalization of Lemmas 4.23--4.25 for the marking consisting
of the left endpoint and the penultimate point of one strand.  The endpoint
reflection firing rewrites subtraction of the penultimate chip into banana
normal form.  At the divisor `g • rightEndpoint`, the resulting four ranks
give `rankDelta = 1`, hence the base transmission row `tau 0 = 0`.
-/

namespace Bananas

open Utilities

/-- The zero divisor is a semibreak divisor. -/
theorem isSemibreak_zero {g : ℕ} (B : Banana g) :
    IsSemibreak B 0 := by
  let chips : ∀ gamma : Fin (g + 1), Option (Fin (B.length gamma - 1)) :=
    fun _ => none
  refine ⟨chips, ?_⟩
  funext z
  rcases z with core | ⟨gamma, offset⟩
  · rfl
  · simp [semibreakDivisor, chips]

/-- Endpoint reflection, rewritten in the form used after subtracting the
penultimate mark from a right-endpoint multiple:
`cR-v_(alpha,n-1) ~ -L+(c-1)R+v_(alpha,1)`. -/
theorem oneOff_sub_penultimate_linearEquiv_normalForm
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (c : ℕ) (hLength : 1 < B.length alpha) :
    linearEquiv B.graph
      ((c : ℤ) • oneChip (rightEndpoint B) -
        oneChip (strandVertex B alpha
          ⟨B.length alpha - 1, by omega⟩))
      (bananaNormalForm B (-1) ((c : ℤ) - 1)
        (oneChip (strandVertex B alpha ⟨1, by omega⟩))) := by
  let one : B.PathPosition alpha := ⟨1, by omega⟩
  have hReflect := endpoint_sum_linearEquiv_strand_reflection B alpha one
  have hMirror : strandMirror B alpha one =
      (⟨B.length alpha - 1, by omega⟩ : B.PathPosition alpha) := by
    apply Fin.ext
    simp [one, strandMirror]
  rw [hMirror] at hReflect
  unfold linearEquiv at hReflect ⊢
  convert hReflect using 1
  ext z
  simp only [bananaNormalForm, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  dsimp [one]
  ring

/-- The corresponding reflection firing after also subtracting the left
mark. -/
theorem oneOff_sub_both_marks_linearEquiv_normalForm
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (c : ℕ) (hLength : 1 < B.length alpha) :
    linearEquiv B.graph
      ((c : ℤ) • oneChip (rightEndpoint B) -
        oneChip (leftEndpoint B) -
        oneChip (strandVertex B alpha
          ⟨B.length alpha - 1, by omega⟩))
      (bananaNormalForm B (-2) ((c : ℤ) - 1)
        (oneChip (strandVertex B alpha ⟨1, by omega⟩))) := by
  let one : B.PathPosition alpha := ⟨1, by omega⟩
  have hReflect := endpoint_sum_linearEquiv_strand_reflection B alpha one
  have hMirror : strandMirror B alpha one =
      (⟨B.length alpha - 1, by omega⟩ : B.PathPosition alpha) := by
    apply Fin.ext
    simp [one, strandMirror]
  rw [hMirror] at hReflect
  unfold linearEquiv at hReflect ⊢
  convert hReflect using 1
  ext z
  simp only [bananaNormalForm, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  dsimp [one]
  ring

/-- The rank-difference calculation behind the base row of paper
Lemma 4.23.  It is stated for every positive right-endpoint coefficient up to
the genus; the paper application is `c=g`. -/
theorem rankDelta_oneOff_rightEndpoint_nsmul_eq_one
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (c : ℕ) (hc : 0 < c) (hcg : c ≤ g)
    (hLength : 1 < B.length alpha) :
    rankDelta
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      (c • oneChip (rightEndpoint B)) = 1 := by
  let one : B.PathPosition alpha := ⟨1, by omega⟩
  let E : CFDiv B.graph := oneChip (strandVertex B alpha one)
  have hOne : B.IsInteriorPosition alpha one := by
    change 0 < (1 : ℕ) ∧ 1 < B.length alpha
    exact ⟨by omega, hLength⟩
  have hE : IsSemibreak B E := by
    exact isSemibreak_one_strand_chip B alpha one hOne
  have hZero : IsSemibreak B (0 : CFDiv B.graph) := isSemibreak_zero B
  have hdegE : deg E = 1 := by simp [E, deg_one_chip]
  have hDDef : bananaNormalForm B 0 (c : ℤ) 0 =
      c • oneChip (rightEndpoint B) := by
    unfold bananaNormalForm
    ext z
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, zero_mul,
      zero_add, smul_eq_mul]
    rw [nsmul_eq_mul]
    ring
  have hDUDef : bananaNormalForm B (-1) (c : ℤ) 0 =
      c • oneChip (rightEndpoint B) - oneChip (leftEndpoint B) := by
    unfold bananaNormalForm
    ext z
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul]
    rw [nsmul_eq_mul]
    ring
  have hRankDForm := rank_bananaNormalForm B 0 (c : ℤ) 0 hZero
    (by omega) (by omega) (by simp; exact_mod_cast hcg)
  have hRankD : rank B.graph (c • oneChip (rightEndpoint B)) = 0 := by
    rw [← hDDef]
    rw [hRankDForm]
    simp
    omega
  have hRankDUForm := rank_bananaNormalForm B (-1) (c : ℤ) 0 hZero
    (by omega) (by omega) (by simp; exact_mod_cast hcg)
  have hRankDU : rank B.graph
      (c • oneChip (rightEndpoint B) - oneChip (leftEndpoint B)) = -1 := by
    rw [← hDUDef]
    rw [hRankDUForm]
    simp
    omega
  have hShiftV := oneOff_sub_penultimate_linearEquiv_normalForm
    B alpha c hLength
  have hRankDVForm := rank_bananaNormalForm B (-1) ((c : ℤ) - 1) E hE
    (by omega) (by omega) (by
      rw [hdegE]
      omega)
  have hRankDV : rank B.graph
      ((c : ℤ) • oneChip (rightEndpoint B) -
        oneChip (strandVertex B alpha
          ⟨B.length alpha - 1, by omega⟩)) = -1 := by
    rw [rank_eq_of_linear_equiv B.graph hShiftV, hRankDVForm]
    rw [hdegE]
    simp
    omega
  have hShiftBoth := oneOff_sub_both_marks_linearEquiv_normalForm
    B alpha c hLength
  have hRankBothForm := (rank_bananaNormalForm_neg_iff B
    (-2) ((c : ℤ) - 1) E hE (by omega)
      (by rw [hdegE]; omega)).2 (by omega)
  have hRankBoth : rank B.graph
      ((c : ℤ) • oneChip (rightEndpoint B) -
        oneChip (leftEndpoint B) -
        oneChip (strandVertex B alpha
          ⟨B.length alpha - 1, by omega⟩)) = -1 := by
    rw [rank_eq_of_linear_equiv B.graph hShiftBoth]
    exact hRankBothForm
  unfold rankDelta
  change rank B.graph (c • oneChip (rightEndpoint B)) -
      rank B.graph (c • oneChip (rightEndpoint B) - oneChip (leftEndpoint B)) -
      rank B.graph (c • oneChip (rightEndpoint B) -
        oneChip (strandVertex B alpha
          ⟨B.length alpha - 1, by omega⟩)) +
      rank B.graph (c • oneChip (rightEndpoint B) -
        oneChip (leftEndpoint B) -
        oneChip (strandVertex B alpha
          ⟨B.length alpha - 1, by omega⟩)) = 1
  rw [hRankD, hRankDU]
  have hCast : (c : ℤ) • oneChip (rightEndpoint B) =
      c • oneChip (rightEndpoint B) := by
    ext z
    simp
  rw [hCast] at hRankDV hRankBoth
  rw [hRankDV, hRankBoth]
  norm_num
/-- The first concrete transmission row of Lemma 4.23: for
`D=g·rightEndpoint`, the same-strand one-off permutation satisfies
`tau(0)=0`. -/
theorem transmission_oneOff_zero
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (tau : ℤ → ℤ) (hg : 0 < g) (hLength : 1 < B.length alpha)
    (hTau : IsTransmissionPermutation
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      (g • oneChip (rightEndpoint B)) tau) :
    tau 0 = 0 := by
  apply transmission_value_of_rankDelta_eq_one hTau
  have hzero : (g • oneChip (rightEndpoint B) : CFDiv B.graph) +
        (0 : ℤ) • oneChip (leftEndpoint B) -
        (0 : ℤ) • oneChip (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩) =
      g • oneChip (rightEndpoint B) := by simp
  convert! rankDelta_oneOff_rightEndpoint_nsmul_eq_one B alpha g hg le_rfl hLength using 1
  congr 1

end Bananas
