/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.Cubic

/-!
# Three-term tail geometry at a rational anchor

After wedging by the zero-place form `a₀ ∧ b₀`, only the six tail variables
remain.  This file gives that quotient its own small coordinate model.  The
rank-one classification is proved from minors, so the annihilator argument
does not enumerate the 128 target words or build a large exterior basis.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- The five product coefficient coordinates of the three-term tail. -/
abbrev TailCoeff := Fin 5 → F₂
/-- The six linear input coordinates of the three-term tail. -/
abbrev TailLinear := Fin 6 → F₂
/-- Two-index coordinate arrays for exterior forms on the six tail inputs. -/
abbrev TailTwo := Fin 6 → Fin 6 → F₂

/-- Coordinate of a coefficient of the first tail polynomial. -/
def tailACoord (i : Fin 3) : Fin 6 := ⟨i.val, by omega⟩
/-- Coordinate of a coefficient of the second tail polynomial. -/
def tailBCoord (i : Fin 3) : Fin 6 := ⟨3 + i.val, by omega⟩

/-- The three-by-three Hankel matrix of the five tail coefficients. -/
def tailHankelMatrix (c : TailCoeff) : Matrix (Fin 3) (Fin 3) F₂ :=
  fun i j => c ⟨i.val + j.val, by omega⟩

/-- Every two-by-two minor of the tail Hankel matrix vanishes. -/
def TailHankelRankLEOne (c : TailCoeff) : Prop :=
  ∀ i k j l : Fin 3,
    tailHankelMatrix c i j * tailHankelMatrix c k l =
      tailHankelMatrix c i l * tailHankelMatrix c k j

/-- The tail coefficient vector for evaluation at zero. -/
def tailZeroCoeff : TailCoeff := ![1, 0, 0, 0, 0]
/-- The tail coefficient vector for evaluation at one. -/
def tailOneCoeff : TailCoeff := ![1, 1, 1, 1, 1]
/-- The tail coefficient vector for evaluation at infinity. -/
def tailInfinityCoeff : TailCoeff := ![0, 0, 0, 0, 1]

private theorem tail_rankOne_minor {c : TailCoeff} (h : TailHankelRankLEOne c)
    (i k j l : Fin 3) :
    c ⟨i.val + j.val, by omega⟩ * c ⟨k.val + l.val, by omega⟩ =
      c ⟨i.val + l.val, by omega⟩ * c ⟨k.val + j.val, by omega⟩ := by
  simpa [TailHankelRankLEOne, tailHankelMatrix] using h i k j l

/-- The nonzero rank-one `3 × 3` Hankel tails are the three rational
places. -/
theorem tail_rankOne_classification {c : TailCoeff}
    (h : TailHankelRankLEOne c) (hc : c ≠ 0) :
    c = tailZeroCoeff ∨ c = tailOneCoeff ∨ c = tailInfinityCoeff := by
  rcases f2_eq_zero_or_one (c 0) with hc0 | hc0
  · have hc1 : c 1 = 0 := by
      have hm := tail_rankOne_minor h (0 : Fin 3) 1 1 0
      simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.one_mod, zero_add,
        Fin.mk_one, add_zero, N3Certificate.mul_self_f2, Fin.zero_eta, hc0, Nat.reduceAdd,
        Fin.reduceFinMk, zero_mul] at hm
      exact hm
    have hc2 : c 2 = 0 := by
      have hm := tail_rankOne_minor h (0 : Fin 3) 2 2 0
      simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.mod_succ, zero_add,
        Fin.reduceFinMk, add_zero, N3Certificate.mul_self_f2, Fin.zero_eta, hc0,
        Nat.reduceAdd, zero_mul] at hm
      exact hm
    have hc3 : c 3 = 0 := by
      have hm := tail_rankOne_minor h (1 : Fin 3) 2 2 1
      simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.one_mod, Nat.mod_succ, Nat.reduceAdd,
        Fin.reduceFinMk, N3Certificate.mul_self_f2, hc2, zero_mul] at hm
      exact hm
    have hc4 : c 4 = 1 := by
      rcases f2_eq_zero_or_one (c 4) with hc4 | hc4
      · exfalso
        apply hc
        funext i
        fin_cases i <;> assumption
      · exact hc4
    exact Or.inr (Or.inr (by
      funext i
      fin_cases i <;>
        simp [tailInfinityCoeff, hc0, hc1, hc2, hc3, hc4]))
  · have hc2 : c 2 = c 1 := by
      have hm := tail_rankOne_minor h (0 : Fin 3) 1 0 1
      simpa [hc0, N3Certificate.mul_self_f2] using hm
    have hc3 : c 3 = c 1 := by
      have hm := tail_rankOne_minor h (0 : Fin 3) 1 0 2
      simpa [hc0, hc2, N3Certificate.mul_self_f2] using hm
    have hc4 : c 4 = c 1 := by
      have hm := tail_rankOne_minor h (0 : Fin 3) 2 0 2
      simpa [hc0, hc2, N3Certificate.mul_self_f2] using hm
    rcases f2_eq_zero_or_one (c 1) with hc1 | hc1
    · exact Or.inl (by
        funext i
        fin_cases i <;>
          simp [tailZeroCoeff, hc0, hc1, hc2, hc3, hc4])
    · exact Or.inr (Or.inl (by
        funext i
        fin_cases i <;>
          simp [tailOneCoeff, hc0, hc1, hc2, hc3, hc4]))

/-- The alternating two-form whose mixed block is the tail Hankel matrix. -/
def tailTargetTwo (c : TailCoeff) : TailTwo := fun i j =>
  if hi : i.val < 3 then
    if hj : 3 ≤ j.val then
      c ⟨i.val + (j.val - 3), by omega⟩
    else 0
  else if hj : j.val < 3 then
    c ⟨j.val + (i.val - 3), by omega⟩
  else 0

/-- Restrict a tail linear form to the first polynomial input. -/
def tailAPart (u : TailLinear) : Fin 3 → F₂ := fun i => u (tailACoord i)
/-- Restrict a tail linear form to the second polynomial input. -/
def tailBPart (u : TailLinear) : Fin 3 → F₂ := fun i => u (tailBCoord i)

/-- The tail target is a mixed exterior product with both same-input blocks zero. -/
def IsDecomposableTailTarget (c : TailCoeff) : Prop :=
  ∃ u v : TailLinear,
    (∀ i j : Fin 3,
      vectorWedgeN u v (tailACoord i) (tailACoord j) = 0) ∧
    (∀ i j : Fin 3,
      vectorWedgeN u v (tailBCoord i) (tailBCoord j) = 0) ∧
    (∀ i j : Fin 3,
      c ⟨i.val + j.val, by omega⟩ =
        vectorWedgeN u v (tailACoord i) (tailBCoord j))

theorem decomposableTailTarget_rankOne {c : TailCoeff}
    (h : IsDecomposableTailTarget c) : TailHankelRankLEOne c := by
  rcases h with ⟨u, v, hAA, _hBB, hcross⟩
  have hApart : ∀ i j : Fin 3,
      tailAPart u i * tailAPart v j +
        tailAPart u j * tailAPart v i = 0 := by
    intro i j
    simpa [tailAPart, vectorWedgeN] using hAA i j
  rcases dependent_of_vectorWedge_zero (tailAPart u) (tailAPart v) hApart with
    hu | hv | huv
  · intro i k j l
    simp only [tailHankelMatrix]
    rw [hcross i j, hcross k l, hcross i l, hcross k j]
    have hui : u (tailACoord i) = 0 := congrFun hu i
    have huk : u (tailACoord k) = 0 := congrFun hu k
    simp [vectorWedgeN, hui, huk]
    ring
  · intro i k j l
    simp only [tailHankelMatrix]
    rw [hcross i j, hcross k l, hcross i l, hcross k j]
    have hvi : v (tailACoord i) = 0 := congrFun hv i
    have hvk : v (tailACoord k) = 0 := congrFun hv k
    simp [vectorWedgeN, hvi, hvk]
    ring
  · intro i k j l
    simp only [tailHankelMatrix]
    rw [hcross i j, hcross k l, hcross i l, hcross k j]
    have hui : u (tailACoord i) = v (tailACoord i) := congrFun huv i
    have huk : u (tailACoord k) = v (tailACoord k) := congrFun huv k
    simp only [vectorWedgeN, hui, huk]
    ring

theorem decomposableTailTarget_classification {c : TailCoeff}
    (h : IsDecomposableTailTarget c) (hc : c ≠ 0) :
    c = tailZeroCoeff ∨ c = tailOneCoeff ∨ c = tailInfinityCoeff :=
  tail_rankOne_classification (decomposableTailTarget_rankOne h) hc

/-- Quotient coordinates obtained by deleting the anchor variables `a₀,b₀`. -/
def tailEmbed : Fin 6 → Fin 8 := ![1, 2, 3, 5, 6, 7]

/-- Restrict an eight-variable linear form to the six tail inputs. -/
def tailVectorOf (M : LinearForm) : TailLinear := fun i => M (tailEmbed i)

/-- Drop the first two coefficients of a four-term product target. -/
def tailCoeffOf (c : TargetCoeff) : TailCoeff :=
  fun i => c ⟨i.val + 2, by omega⟩

theorem tailTargetOf_apply (c : TargetCoeff) (i j : Fin 6) :
    targetTwo c (tailEmbed i) (tailEmbed j) =
      tailTargetTwo (tailCoeffOf c) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [targetTwo, tailTargetTwo, tailCoeffOf, tailEmbed]

private theorem zeroPlace_anchor :
    zeroPlaceTwo (aCoord 0) (bCoord 0) = 1 := by
  simp [zeroPlaceTwo, vectorWedge, aLinear, bLinear, aCoord, bCoord, Pi.basisFun]

private theorem zeroPlace_a_tail (i : Fin 6) :
    zeroPlaceTwo (aCoord 0) (tailEmbed i) = 0 := by
  fin_cases i <;>
    simp [zeroPlaceTwo, vectorWedge, aLinear, bLinear, aCoord, bCoord, tailEmbed, Pi.basisFun]

private theorem zeroPlace_b_tail (i : Fin 6) :
    zeroPlaceTwo (bCoord 0) (tailEmbed i) = 0 := by
  fin_cases i <;>
    simp [zeroPlaceTwo, vectorWedge, aLinear, bLinear, aCoord, bCoord, tailEmbed, Pi.basisFun]

private theorem zeroPlace_tail_a (i : Fin 6) :
    zeroPlaceTwo (tailEmbed i) (aCoord 0) = 0 := by
  fin_cases i <;>
    simp [zeroPlaceTwo, vectorWedge, aLinear, bLinear, aCoord, bCoord, tailEmbed, Pi.basisFun]

private theorem zeroPlace_tail_b (i : Fin 6) :
    zeroPlaceTwo (tailEmbed i) (bCoord 0) = 0 := by
  fin_cases i <;>
    simp [zeroPlaceTwo, vectorWedge, aLinear, bLinear, aCoord, bCoord, tailEmbed, Pi.basisFun]

private theorem zeroPlace_tail_tail (i j : Fin 6) :
    zeroPlaceTwo (tailEmbed i) (tailEmbed j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [zeroPlaceTwo, vectorWedge, aLinear, bLinear, aCoord, bCoord, tailEmbed, Pi.basisFun]

private theorem zeroPlace_wedge_target_anchor_tail (c : TargetCoeff)
    (i j : Fin 6) :
    wedgeTwo zeroPlaceTwo (targetTwo c)
      (aCoord 0) (bCoord 0) (tailEmbed i) (tailEmbed j) =
      targetTwo c (tailEmbed i) (tailEmbed j) := by
  simp [wedgeTwo, zeroPlace_anchor, zeroPlace_a_tail, zeroPlace_b_tail, zeroPlace_tail_tail]

private theorem zeroPlace_wedge_target_missing_a (c : TargetCoeff)
    (i j k : Fin 6) :
    wedgeTwo zeroPlaceTwo (targetTwo c)
      (bCoord 0) (tailEmbed i) (tailEmbed j) (tailEmbed k) = 0 := by
  simp [wedgeTwo, zeroPlace_b_tail, zeroPlace_tail_tail]

private theorem zeroPlace_wedge_target_missing_b (c : TargetCoeff)
    (i j k : Fin 6) :
    wedgeTwo zeroPlaceTwo (targetTwo c)
      (aCoord 0) (tailEmbed i) (tailEmbed j) (tailEmbed k) = 0 := by
  simp [wedgeTwo, zeroPlace_a_tail, zeroPlace_tail_tail]

/-- The five-form annihilator equation descends to the three-form equation
on the six-dimensional tail quotient. -/
theorem anchoredAnnihilator_tailEquation (M : LinearForm) (c : TargetCoeff)
    (hc : c ∈ targetAnnihilator
      (vectorWedgeTwo M (rationalPlaceTwo 0))) :
    vectorWedgeTwoN (tailVectorOf M)
      (tailTargetTwo (tailCoeffOf c)) = 0 := by
  rw [mem_targetAnnihilator_iff, rationalPlaceTwo_zero_eq] at hc
  funext i j k
  have heval := congrFun (congrFun (congrFun (congrFun (congrFun hc
    (aCoord 0)) (bCoord 0)) (tailEmbed i)) (tailEmbed j)) (tailEmbed k)
  rw [wedgeThreeTwo_vectorWedgeTwo] at heval
  simp only [vectorWedgeFour, Pi.zero_apply, zeroPlace_wedge_target_missing_a,
    zeroPlace_wedge_target_missing_b, zeroPlace_wedge_target_anchor_tail, mul_zero, zero_add
    ] at heval
  change tailVectorOf M i * tailTargetTwo (tailCoeffOf c) j k +
      tailVectorOf M j * tailTargetTwo (tailCoeffOf c) i k +
      tailVectorOf M k * tailTargetTwo (tailCoeffOf c) i j = 0
  simpa only [tailVectorOf, tailTargetOf_apply] using heval

theorem tailVector_ne_zero_of_anchored_ne_zero (M : LinearForm)
    (hM : vectorWedgeTwo M (rationalPlaceTwo 0) ≠ 0) :
    tailVectorOf M ≠ 0 := by
  intro htail
  have h1 : M 1 = 0 := congrFun htail 0
  have h2 : M 2 = 0 := congrFun htail 1
  have h3 : M 3 = 0 := congrFun htail 2
  have h5 : M 5 = 0 := congrFun htail 3
  have h6 : M 6 = 0 := congrFun htail 4
  have h7 : M 7 = 0 := congrFun htail 5
  have hdecomp :
      M = M 0 • aLinear 0 + M 4 • bLinear 0 := by
    funext i
    fin_cases i <;>
      simp [aLinear, bLinear, aCoord, bCoord, Pi.basisFun, h1, h2, h3, h5, h6, h7]
  apply hM
  rw [rationalPlaceTwo_zero_eq, hdecomp, vectorWedgeTwo_add_left,
    vectorWedgeTwo_smul_left, vectorWedgeTwo_smul_left, zeroPlaceTwo,
    vectorWedgeTwo_repeated_left, vectorWedgeTwo_repeated_right]
  simp

theorem tailTarget_decomposable_of_annihilates
    (u : TailLinear) (c : TailCoeff) (hu : u ≠ 0)
    (h : vectorWedgeTwoN u (tailTargetTwo c) = 0) :
    IsDecomposableTailTarget c := by
  rcases decomposable_of_vectorWedgeTwoN_zero u (tailTargetTwo c) hu h with
    ⟨v, hv⟩
  refine ⟨u, v, ?_, ?_, ?_⟩
  · intro i j
    rw [← hv]
    fin_cases i <;> fin_cases j <;>
      simp [tailTargetTwo, tailACoord]
  · intro i j
    rw [← hv]
    fin_cases i <;> fin_cases j <;>
      simp [tailTargetTwo, tailBCoord]
  · intro i j
    rw [← hv]
    fin_cases i <;> fin_cases j <;>
      simp [tailTargetTwo, tailACoord, tailBCoord]

/-- Exterior core of the tail-place table: after quotienting by the two
baseline annihilators, the only possible nonzero annihilator directions are
the three rank-one three-term places. -/
theorem anchored_annihilator_tail_classification (M : LinearForm)
    (hM : vectorWedgeTwo M (rationalPlaceTwo 0) ≠ 0)
    (c : TargetCoeff)
    (hc : c ∈ targetAnnihilator
      (vectorWedgeTwo M (rationalPlaceTwo 0))) :
    tailCoeffOf c = 0 ∨
      tailCoeffOf c = tailZeroCoeff ∨
      tailCoeffOf c = tailOneCoeff ∨
      tailCoeffOf c = tailInfinityCoeff := by
  let d := tailCoeffOf c
  by_cases hd : d = 0
  · exact Or.inl hd
  · have hu := tailVector_ne_zero_of_anchored_ne_zero M hM
    have heq := anchoredAnnihilator_tailEquation M c hc
    have hdec : IsDecomposableTailTarget d :=
      tailTarget_decomposable_of_annihilates (tailVectorOf M) d hu heq
    rcases decomposableTailTarget_classification hdec hd with h0 | h1 | hinf
    · exact Or.inr (Or.inl h0)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr hinf))

/-- Evaluation at zero on the first tail polynomial. -/
def tailZeroA : TailLinear := ![1, 0, 0, 0, 0, 0]
/-- Evaluation at zero on the second tail polynomial. -/
def tailZeroB : TailLinear := ![0, 0, 0, 1, 0, 0]
/-- Evaluation at infinity on the first tail polynomial. -/
def tailInfinityA : TailLinear := ![0, 0, 1, 0, 0, 0]
/-- Evaluation at infinity on the second tail polynomial. -/
def tailInfinityB : TailLinear := ![0, 0, 0, 0, 0, 1]
/-- Evaluation at one on the first tail polynomial. -/
def tailOneA : TailLinear := ![1, 1, 1, 0, 0, 0]
/-- Evaluation at one on the second tail polynomial. -/
def tailOneB : TailLinear := ![0, 0, 0, 1, 1, 1]

/-- Membership in the span of two specified tail linear forms. -/
def InTailPlane (u a b : TailLinear) : Prop :=
  ∃ α β : F₂, u = α • a + β • b

@[simp] theorem tailTargetTwo_zero_place :
    tailTargetTwo tailZeroCoeff = vectorWedgeN tailZeroA tailZeroB := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [tailTargetTwo, tailZeroCoeff, vectorWedgeN, tailZeroA, tailZeroB]

@[simp] theorem tailTargetTwo_infinity_place :
    tailTargetTwo tailInfinityCoeff =
      vectorWedgeN tailInfinityA tailInfinityB := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [tailTargetTwo, tailInfinityCoeff, vectorWedgeN, tailInfinityA, tailInfinityB]

@[simp] theorem tailTargetTwo_one_place :
    tailTargetTwo tailOneCoeff = vectorWedgeN tailOneA tailOneB := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [tailTargetTwo, tailOneCoeff, vectorWedgeN, tailOneA, tailOneB]

theorem tailVector_mem_zeroPlane_of_wedge (u : TailLinear)
    (h : vectorWedgeTwoN u (tailTargetTwo tailZeroCoeff) = 0) :
    InTailPlane u tailZeroA tailZeroB := by
  have h1 := congrFun (congrFun (congrFun h 1) 0) 3
  have h2 := congrFun (congrFun (congrFun h 2) 0) 3
  have h4 := congrFun (congrFun (congrFun h 4) 0) 3
  have h5 := congrFun (congrFun (congrFun h 5) 0) 3
  simp [vectorWedgeTwoN, tailTargetTwo, tailZeroCoeff] at h1 h2 h4 h5
  refine ⟨u 0, u 3, ?_⟩
  funext i
  fin_cases i <;>
    simp [tailZeroA, tailZeroB, h1, h2, h4, h5]

theorem tailVector_mem_infinityPlane_of_wedge (u : TailLinear)
    (h : vectorWedgeTwoN u (tailTargetTwo tailInfinityCoeff) = 0) :
    InTailPlane u tailInfinityA tailInfinityB := by
  have h0 := congrFun (congrFun (congrFun h 0) 2) 5
  have h1 := congrFun (congrFun (congrFun h 1) 2) 5
  have h3 := congrFun (congrFun (congrFun h 3) 2) 5
  have h4 := congrFun (congrFun (congrFun h 4) 2) 5
  simp [vectorWedgeTwoN, tailTargetTwo, tailInfinityCoeff] at h0 h1 h3 h4
  refine ⟨u 2, u 5, ?_⟩
  funext i
  fin_cases i <;>
    simp [tailInfinityA, tailInfinityB, h0, h1, h3, h4]

private theorem eq_of_add_eq_zero {x y : F₂} (h : x + y = 0) : x = y := by
  apply sub_eq_zero.mp
  rw [CharTwo.sub_eq_add]
  exact h

theorem tailVector_mem_onePlane_of_wedge (u : TailLinear)
    (h : vectorWedgeTwoN u (tailTargetTwo tailOneCoeff) = 0) :
    InTailPlane u tailOneA tailOneB := by
  have ha01 := congrFun (congrFun (congrFun h 0) 1) 3
  have ha02 := congrFun (congrFun (congrFun h 0) 2) 3
  have hb01 := congrFun (congrFun (congrFun h 0) 3) 4
  have hb02 := congrFun (congrFun (congrFun h 0) 3) 5
  simp only [vectorWedgeTwoN, Fin.isValue, tailTargetTwo, Fin.coe_ofNat_eq_mod, Nat.one_mod,
    Nat.one_lt_ofNat, ↓reduceDIte, Nat.reduceMod, Std.le_refl, tailOneCoeff, tsub_self,
    add_zero, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, mul_one, Nat.zero_mod,
    Nat.ofNat_pos, Fin.zero_eta, Nat.not_ofNat_le_one, mul_zero, Pi.zero_apply,
    Nat.lt_add_one, Fin.reduceFinMk, Matrix.cons_val, Nat.reduceLeDiff, lt_self_iff_false,
    Nat.reduceLT, Nat.reduceSub, zero_add, Nat.mod_succ] at ha01 ha02 hb01 hb02
  have ha1 : u 1 = u 0 := (eq_of_add_eq_zero ha01).symm
  have ha2 : u 2 = u 0 := (eq_of_add_eq_zero ha02).symm
  have hb1 : u 4 = u 3 := (eq_of_add_eq_zero hb01).symm
  have hb2 : u 5 = u 3 := (eq_of_add_eq_zero hb02).symm
  refine ⟨u 0, u 3, ?_⟩
  funext i
  fin_cases i <;>
    simp [tailOneA, tailOneB, ha1, ha2, hb1, hb2]

/-- Full tail-place incidence table, stated in quotient coordinates. -/
theorem anchored_annihilator_tail_table (M : LinearForm)
    (hM : vectorWedgeTwo M (rationalPlaceTwo 0) ≠ 0)
    (c : TargetCoeff)
    (hc : c ∈ targetAnnihilator
      (vectorWedgeTwo M (rationalPlaceTwo 0))) :
    tailCoeffOf c = 0 ∨
      (tailCoeffOf c = tailZeroCoeff ∧
        InTailPlane (tailVectorOf M) tailZeroA tailZeroB) ∨
      (tailCoeffOf c = tailOneCoeff ∧
        InTailPlane (tailVectorOf M) tailOneA tailOneB) ∨
      (tailCoeffOf c = tailInfinityCoeff ∧
        InTailPlane (tailVectorOf M) tailInfinityA tailInfinityB) := by
  have heq := anchoredAnnihilator_tailEquation M c hc
  rcases anchored_annihilator_tail_classification M hM c hc with
    hzero | hzeroPlace | hone | hinfinity
  · exact Or.inl hzero
  · have heq0 : vectorWedgeTwoN (tailVectorOf M)
        (tailTargetTwo tailZeroCoeff) = 0 := by
      simpa [hzeroPlace] using heq
    exact Or.inr (Or.inl ⟨hzeroPlace,
      tailVector_mem_zeroPlane_of_wedge (tailVectorOf M) heq0⟩)
  · have heq1 : vectorWedgeTwoN (tailVectorOf M)
        (tailTargetTwo tailOneCoeff) = 0 := by
      simpa [hone] using heq
    exact Or.inr (Or.inr (Or.inl ⟨hone,
      tailVector_mem_onePlane_of_wedge (tailVectorOf M) heq1⟩))
  · have heqinf : vectorWedgeTwoN (tailVectorOf M)
        (tailTargetTwo tailInfinityCoeff) = 0 := by
      simpa [hinfinity] using heq
    exact Or.inr (Or.inr (Or.inr ⟨hinfinity,
      tailVector_mem_infinityPlane_of_wedge (tailVectorOf M) heqinf⟩))

end

end N4
end UnrestrictedBooleanMul
