/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.QuarticOrbits

/-!
# Quartic separation for every pair of rational-place supports

There are only three unordered pairs of rational places.  The first pair is
certified in `QuarticCoordinates`; the packed rows below certify the other
two.  This lets the low--low proof select a nonzero `2 × 2` coefficient
minor directly, without formalizing a separate `PGL₂(F₂)` action.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Packed separating covectors for the rational places at zero and infinity. -/
def quarticZeroInfinitySeparators (i : Fin 144) : Nat :=
  #[0x0000200,0x0000200,0x0100000,0x0200000,0x0100000,0x0200000,0x0100000,0x0200000,0x0200000,
    0x0000200,0x0000200,0x0100000,0x0080000,0x0100000,0x0100000,0x0100000,0x0080000,0x0100000,
    0x0000200,0x0000200,0x0020000,0x0010000,0x0020000,0x0020000,0x0020000,0x0010000,0x0020000,
    0x0000200,0x0000200,0x8100000,0x4080000,0x8100000,0x8100000,0x8100000,0x4080000,0x8100000,
    0x0000010,0x0000010,0x0100000,0x0200000,0x0100000,0x0200000,0x0100000,0x0200000,0x0200000,
    0x0000010,0x0000010,0x0100000,0x0080000,0x0100000,0x0100000,0x0100000,0x0080000,0x0100000,
    0x0000010,0x0000010,0x0020000,0x0010000,0x0020000,0x0020000,0x0020000,0x0010000,0x0020000,
    0x0000010,0x0000010,0x8100000,0x4080000,0x8100000,0x8100000,0x8100000,0x4080000,0x8100000,
    0x0000200,0x0000200,0x0100000,0x0200000,0x0100000,0x0200000,0x0100000,0x0200000,0x0200000,
    0x0000200,0x0000200,0x0100000,0x0080000,0x0100000,0x0100000,0x0100000,0x0080000,0x0100000,
    0x0000200,0x0000200,0x0020000,0x0010000,0x0020000,0x0020000,0x0020000,0x0010000,0x0020000,
    0x0000200,0x0000200,0x8100000,0x4080000,0x8100000,0x8100000,0x8100000,0x4080000,0x8100000,
    0x0400010,0x0400010,0x0100000,0x0200000,0x0100000,0x0200000,0x0100000,0x0200000,0x0200000,
    0x0400010,0x0400010,0x0100000,0x0080000,0x0100000,0x0100000,0x0100000,0x0080000,0x0100000,
    0x0400010,0x0400010,0x0020000,0x0010000,0x0020000,0x0020000,0x0020000,0x0010000,0x0020000,
    0x0400010,0x0400010,0x8100000,0x4080000,0x8100000,0x8100000,0x8100000,0x4080000,0x8100000
    ][i.val]'i.isLt

/-- Packed separating covectors for the rational places at one and infinity. -/
def quarticOneInfinitySeparators (i : Fin 144) : Nat :=
  #[0x0000200,0x0000200,0x0100000,0x0200000,0x0100000,0x0200000,0x0100000,0x0200000,0x0200000,
    0x0000200,0x0000200,0x0100000,0x0080000,0x0100000,0x0100000,0x0100000,0x0080000,0x0100000,
    0x0000200,0x0000200,0x0020000,0x0010000,0x0020000,0x0020000,0x0020000,0x0010000,0x0020000,
    0x0000200,0x0000200,0x8100000,0x4080000,0x8100000,0x8100000,0x8100000,0x4080000,0x8100000,
    0x0001200,0x0001200,0x0300000,0x0300000,0x0300000,0x0280000,0x0300000,0x0300000,0x0280000,
    0x0000a00,0x0000a00,0x0180000,0x0180000,0x0180000,0x0180000,0x0140000,0x0180000,0x0180000,
    0x0001200,0x0001200,0x0030000,0x0030000,0x0030000,0x0030000,0x0028000,0x0030000,0x0030000,
    0x0000a00,0x0000a00,0xe180000,0xe180000,0xe180000,0xe180000,0x9940000,0xe180000,0xe180000,
    0x0040200,0x0040200,0x0220000,0x0220000,0x0220000,0x0110000,0x0220000,0x0220000,0x0110000,
    0x0040200,0x0040200,0x0110000,0x0110000,0x0110000,0x0110000,0x0088000,0x0110000,0x0110000,
    0x0004200,0x0004200,0x0021000,0x0021000,0x0021000,0x0021000,0x0010800,0x0021000,0x0021000,
    0x1040200,0x1040200,0x8110000,0x8110000,0x8110000,0x8110000,0x4088000,0x8110000,0x8110000,
    0x1001200,0x1001200,0x8300000,0x8300000,0x8300000,0x4280000,0x8300000,0x8300000,0x4280000,
    0x0800a00,0x0800a00,0x2180000,0x2180000,0x2180000,0x2180000,0x0940000,0x2180000,0x2180000,
    0x1001200,0x1001200,0x8030000,0x8030000,0x8030000,0x8030000,0x4028000,0x8030000,0x8030000,
    0x0800a00,0x0800a00,0xc180000,0xc180000,0xc180000,0xc180000,0x9140000,0xc180000,0xc180000
    ][i.val]'i.isLt

/-- The two remaining support-pair tables, stored as bounded blocks. -/
def quarticOtherPairSeparatorTable (i : Fin 288) : Nat :=
  if h : i.val < 144 then quarticZeroInfinitySeparators ⟨i.val, h⟩
  else quarticOneInfinitySeparators ⟨i.val - 144, by omega⟩

/-- Pair zero is `(P₁,P₀)`, pair one `(P₀,P∞)`, and pair two
`(P₁,P∞)`. -/
@[expose]
def quarticSupportPair : Fin 3 → Fin 3 × Fin 3 :=
  ![(1, 0), (0, 2), (1, 2)]

/-- A vector in the two-input support of a chosen rational place. -/
@[expose] def quarticSupportVector (theta : Fin 3) (a b : F₂) : LinearForm :=
  a • placeA theta + b • placeB theta

/-- Select a packed separating covector for one of the three rational-place pairs. -/
def quarticPairSeparatorRow (pair : Fin 3) (index : Fin 144) : Nat :=
  if pair = 0 then quarticLowLowSeparatorTable index
  else if pair = 1 then
    quarticOtherPairSeparatorTable ⟨index.val, index.isLt.trans (by decide)⟩
  else
    quarticOtherPairSeparatorTable
      ⟨144 + index.val, Nat.add_lt_add_left index.isLt 144⟩

/-- Extract a coefficient of the covector separating a target from a support pair. -/
def quarticPairSeparatorBit (pair : Fin 3) (a b c d : F₂)
    (i : Fin 9) (k : Fin 28) : F₂ :=
  if Nat.testBit
      (quarticPairSeparatorRow pair (quarticSeparatorIndex a b c d i)) k.val
    then 1 else 0

/-- The separating linear functional for a rational-place pair and its support parameters. -/
def quarticPairSeparatorLinear (pair : Fin 3) (a b c d : F₂)
    (i : Fin 9) : TwoForm →ₗ[F₂] F₂ :=
  ∑ k : Fin 28, quarticPairSeparatorBit pair a b c d i k •
    twoFormCoordinate (upperPair k).1 (upperPair k).2

theorem quarticPairSeparator_target_check :
    ∀ (pair : Fin 3) (a b c d : F₂) (i : Fin 9),
      quarticPairSeparatorLinear pair a b c d i
        (targetTwo (outsideRankTwoWord i)) = 1 := by
  decide +kernel

/- Each finite check is kernel-reduced one rational-place pair at a time.
The original all-three-pairs reduction exceeded a 4-GiB Lean heap on 4.33.1.
Separate declarations bound the reduction cache without changing statements,
using native evaluation, or introducing axioms. -/
private theorem quarticPairSeparator_first_basis_check_0 :
    ∀ (a b c d : F₂) (i : Fin 9) (j : Fin 8),
      quarticPairSeparatorLinear 0 a b c d i
        (vectorWedge
          (quarticSupportVector (quarticSupportPair 0).1 a b)
          (coordinateLinear j)) = 0 := by
  intro a b c d i j
  exact quarticSeparator_pone_basis_check a b c d i j

private theorem quarticPairSeparator_first_basis_check_1 :
    ∀ (a b c d : F₂) (i : Fin 9) (j : Fin 8),
      quarticPairSeparatorLinear 1 a b c d i
        (vectorWedge
          (quarticSupportVector (quarticSupportPair 1).1 a b)
          (coordinateLinear j)) = 0 := by
  decide +kernel

private theorem quarticPairSeparator_first_basis_check_2 :
    ∀ (a b c d : F₂) (i : Fin 9) (j : Fin 8),
      quarticPairSeparatorLinear 2 a b c d i
        (vectorWedge
          (quarticSupportVector (quarticSupportPair 2).1 a b)
          (coordinateLinear j)) = 0 := by
  decide +kernel

theorem quarticPairSeparator_first_basis_check :
    ∀ (pair : Fin 3) (a b c d : F₂) (i : Fin 9) (j : Fin 8),
      quarticPairSeparatorLinear pair a b c d i
        (vectorWedge
          (quarticSupportVector (quarticSupportPair pair).1 a b)
          (coordinateLinear j)) = 0 := by
  intro pair
  fin_cases pair
  · exact quarticPairSeparator_first_basis_check_0
  · exact quarticPairSeparator_first_basis_check_1
  · exact quarticPairSeparator_first_basis_check_2

private theorem quarticPairSeparator_second_basis_check_0 :
    ∀ (a b c d : F₂) (i : Fin 9) (j : Fin 8),
      quarticPairSeparatorLinear 0 a b c d i
        (vectorWedge
          (quarticSupportVector (quarticSupportPair 0).2 c d)
          (coordinateLinear j)) = 0 := by
  intro a b c d i j
  exact quarticSeparator_pzero_basis_check a b c d i j

private theorem quarticPairSeparator_second_basis_check_1 :
    ∀ (a b c d : F₂) (i : Fin 9) (j : Fin 8),
      quarticPairSeparatorLinear 1 a b c d i
        (vectorWedge
          (quarticSupportVector (quarticSupportPair 1).2 c d)
          (coordinateLinear j)) = 0 := by
  decide +kernel

private theorem quarticPairSeparator_second_basis_check_2 :
    ∀ (a b c d : F₂) (i : Fin 9) (j : Fin 8),
      quarticPairSeparatorLinear 2 a b c d i
        (vectorWedge
          (quarticSupportVector (quarticSupportPair 2).2 c d)
          (coordinateLinear j)) = 0 := by
  decide +kernel

theorem quarticPairSeparator_second_basis_check :
    ∀ (pair : Fin 3) (a b c d : F₂) (i : Fin 9) (j : Fin 8),
      quarticPairSeparatorLinear pair a b c d i
        (vectorWedge
          (quarticSupportVector (quarticSupportPair pair).2 c d)
          (coordinateLinear j)) = 0 := by
  intro pair
  fin_cases pair
  · exact quarticPairSeparator_second_basis_check_0
  · exact quarticPairSeparator_second_basis_check_1
  · exact quarticPairSeparator_second_basis_check_2
theorem quarticPairSeparator_first (pair : Fin 3) (a b c d : F₂)
    (i : Fin 9) (z : LinearForm) :
    quarticPairSeparatorLinear pair a b c d i
      (vectorWedge
        (quarticSupportVector (quarticSupportPair pair).1 a b) z) = 0 := by
  change quarticPairSeparatorLinear pair a b c d i
    (vectorWedgeBilinear
      (quarticSupportVector (quarticSupportPair pair).1 a b) z) = 0
  rw [linear_eq_sum_coordinate z]
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro j _
  change z j • quarticPairSeparatorLinear pair a b c d i
    (vectorWedge
      (quarticSupportVector (quarticSupportPair pair).1 a b)
      (coordinateLinear j)) = 0
  rw [quarticPairSeparator_first_basis_check]
  simp

theorem quarticPairSeparator_second (pair : Fin 3) (a b c d : F₂)
    (i : Fin 9) (z : LinearForm) :
    quarticPairSeparatorLinear pair a b c d i
      (vectorWedge
        (quarticSupportVector (quarticSupportPair pair).2 c d) z) = 0 := by
  change quarticPairSeparatorLinear pair a b c d i
    (vectorWedgeBilinear
      (quarticSupportVector (quarticSupportPair pair).2 c d) z) = 0
  rw [linear_eq_sum_coordinate z]
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro j _
  change z j • quarticPairSeparatorLinear pair a b c d i
    (vectorWedge
      (quarticSupportVector (quarticSupportPair pair).2 c d)
      (coordinateLinear j)) = 0
  rw [quarticPairSeparator_second_basis_check]
  simp

theorem outsideRankTwo_not_supportPair_wedges
    (pair : Fin 3) (a b c d : F₂) (i : Fin 9) (z w : LinearForm) :
    targetTwo (outsideRankTwoWord i) ≠
      vectorWedge
          (quarticSupportVector (quarticSupportPair pair).1 a b) z +
        vectorWedge
          (quarticSupportVector (quarticSupportPair pair).2 c d) w := by
  intro h
  have he := congrArg (quarticPairSeparatorLinear pair a b c d i) h
  rw [quarticPairSeparator_target_check] at he
  rw [map_add, quarticPairSeparator_first,
    quarticPairSeparator_second] at he
  exact one_ne_zero he

theorem target_eq_rational_add_supportPair_is_rational
    (t : TargetCoeff) (gamma : Fin 3 → F₂)
    (pair : Fin 3) (a b c d : F₂) (z w : LinearForm)
    (h : targetTwo t = rationalTwo gamma +
      vectorWedge
          (quarticSupportVector (quarticSupportPair pair).1 a b) z +
        vectorWedge
          (quarticSupportVector (quarticSupportPair pair).2 c d) w) :
    IsRationalCoeff t := by
  let delta : TargetCoeff := t + rationalCoeffRep gamma
  have hdelta : targetTwo delta =
      vectorWedge
          (quarticSupportVector (quarticSupportPair pair).1 a b) z +
        vectorWedge
          (quarticSupportVector (quarticSupportPair pair).2 c d) w := by
    rw [show targetTwo delta = targetTwo t +
      targetTwo (rationalCoeffRep gamma) by
        exact targetTwoLinear.map_add _ _]
    rw [targetTwo_rationalCoeffRep, h]
    funext i j
    simp only [Pi.add_apply]
    ring_nf
    simp [N3Certificate.two_eq_zero_f2]
  have hdeltaRank : HankelRankLETwo delta := by
    exact target_sum_two_decomposable_rankTwo hdelta
  have hdeltaRat : IsRationalCoeff delta := by
    by_contra hnot
    have hne : delta ≠ 0 := by
      intro hz
      apply hnot
      rw [hz]
      exact ⟨0, 0, 0, by simp⟩
    rcases (outside_rankTwo_classification delta).mp
        ⟨hdeltaRank, hne, hnot⟩ with ⟨i, hi⟩
    have hdelta' := hdelta
    rw [hi] at hdelta'
    exact outsideRankTwo_not_supportPair_wedges
      pair a b c d i z w hdelta'
  rcases (IsRationalCoeff_iff delta).mp hdeltaRat with ⟨eta, heta⟩
  apply (IsRationalCoeff_iff t).mpr
  refine ⟨eta + gamma, ?_⟩
  rw [rationalCoeffRep_add, ← heta]
  dsimp [delta]
  funext i
  simp only [Pi.add_apply]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

end

end N4
end UnrestrictedBooleanMul
