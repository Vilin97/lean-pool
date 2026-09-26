/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.ParameterizedBound
public import Mathlib.Tactic

/-!
# Enlarging the degree data in Corvaja--Zannier Proposition 2

The actual coordinate degrees of a plane curve can be strictly smaller than
the public bidegree bounds used by the final theorem.  The degree alternative
in Proposition 2 is not itself monotone in those bounds.  Nevertheless, once
the gcd quantity satisfies its trivial bound by the first actual degree, an
actual degree alternative implies the numerical alternative for every larger
pair of degrees: its Euler term already dominates the first degree.

This is the exact numerical bridge needed between a Proposition 2 proof at
the curve's actual degrees and the public min/max degree convention.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

/-- Proposition 2 remains valid after enlarging both degrees and the Euler
budget, provided the gcd quantity has the trivial bound by the first original
degree.

The old degree alternative cannot in general be transported to the larger
degrees.  In that case both parameters are positive, and
`2 * k <= h * k + h + k - 1`; hence the new Euler term (whose Euler budget is
positive) is at least `k`, and therefore at least the gcd quantity. -/
theorem propositionTwoNumericalAlternatives_mono_degreeBounds
    (a b A B p chi Chi : ℕ) (G : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (haA : a ≤ A) (hbB : b ≤ B)
    (hchi : chi ≤ Chi) (hChi : 0 < Chi)
    (hG : G ≤ (a : ℝ))
    (hactual : PropositionTwoNumericalAlternatives a b p chi G) :
    PropositionTwoNumericalAlternatives A B p Chi G := by
  intro h k hadmissible
  have hadmissibleActual :
      PropositionTwoParametersAreAdmissible a b p h k := by
    refine ⟨hadmissible.1, ?_⟩
    have hweighted : a * h + b * k ≤ A * h + B * k :=
      Nat.add_le_add (Nat.mul_le_mul_right h haA)
        (Nat.mul_le_mul_right k hbB)
    exact hweighted.trans_lt hadmissible.2
  rcases hactual h k hadmissibleActual with hdegree | hbound
  · right
    let n : ℕ := h * k + h + k
    have hkPos : 0 < k := lt_of_lt_of_le ha hdegree.1
    have hhPos : 0 < h := lt_of_lt_of_le hb hdegree.2
    have hnSub : 2 * k ≤ n - 1 := by
      obtain ⟨h', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hhPos.ne'
      simp only [n, Nat.succ_mul, Nat.succ_eq_add_one]
      omega
    have hnSubReal : (2 * k : ℝ) ≤ (n : ℝ) - 1 := by
      have hnOne : 1 ≤ n := by dsimp only [n]; omega
      have hnSubCast : ((2 * k : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
        exact_mod_cast hnSub
      rw [Nat.cast_sub hnOne] at hnSubCast
      norm_num at hnSubCast ⊢
      exact hnSubCast
    have hkEulerHalf : (k : ℝ) ≤ ((n : ℝ) - 1) / 2 := by
      linarith
    have hEulerHalfNonneg : 0 ≤ ((n : ℝ) - 1) / 2 :=
      (Nat.cast_nonneg k).trans hkEulerHalf
    have hChiReal : (1 : ℝ) ≤ (Chi : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hChi.ne')
    have hkEuler :
        (k : ℝ) ≤ (((n : ℝ) - 1) / 2) * (Chi : ℝ) := by
      calc
        (k : ℝ) ≤ ((n : ℝ) - 1) / 2 := hkEulerHalf
        _ = (((n : ℝ) - 1) / 2) * 1 := by ring
        _ ≤ (((n : ℝ) - 1) / 2) * (Chi : ℝ) :=
          mul_le_mul_of_nonneg_left hChiReal hEulerHalfNonneg
    have hGa : G ≤ (k : ℝ) :=
      hG.trans (by exact_mod_cast hdegree.1)
    have hnPosReal : 0 < (n : ℝ) := by
      exact_mod_cast hadmissible.1
    have hfirstNonneg :
        0 ≤ (((h + 2 * k : ℕ) : ℝ) / (n : ℝ)) * (A : ℝ) :=
      mul_nonneg (div_nonneg (Nat.cast_nonneg _) hnPosReal.le)
        (Nat.cast_nonneg _)
    have hsecondNonneg :
        0 ≤ ((k : ℝ) / (n : ℝ)) * (B : ℝ) :=
      mul_nonneg (div_nonneg (Nat.cast_nonneg _) hnPosReal.le)
        (Nat.cast_nonneg _)
    calc
      G ≤ (k : ℝ) := hGa
      _ ≤ (((n : ℝ) - 1) / 2) * (Chi : ℝ) := hkEuler
      _ ≤
          (((h + 2 * k : ℕ) : ℝ) / (n : ℝ)) * (A : ℝ) +
            ((k : ℝ) / (n : ℝ)) * (B : ℝ) +
              (((n : ℝ) - 1) / 2) * (Chi : ℝ) := by
        linarith
      _ =
          (((h + 2 * k : ℕ) : ℝ) /
              ((h * k + h + k : ℕ) : ℝ)) * (A : ℝ) +
            ((k : ℝ) / ((h * k + h + k : ℕ) : ℝ)) * (B : ℝ) +
              ((((h * k + h + k : ℕ) : ℝ) - 1) / 2) *
                (Chi : ℝ) := by
        rfl
  · right
    let n : ℕ := h * k + h + k
    have hnPosReal : 0 < (n : ℝ) := by
      exact_mod_cast hadmissible.1
    have hfirstCoefficient :
        0 ≤ ((h + 2 * k : ℕ) : ℝ) / (n : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) hnPosReal.le
    have hsecondCoefficient : 0 ≤ (k : ℝ) / (n : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) hnPosReal.le
    have hnOne : 1 ≤ n := by
      exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hadmissible.1)
    have hthirdCoefficient : 0 ≤ ((n : ℝ) - 1) / 2 := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnOne
      positivity
    have haReal : (a : ℝ) ≤ (A : ℝ) := by exact_mod_cast haA
    have hbReal : (b : ℝ) ≤ (B : ℝ) := by exact_mod_cast hbB
    have hchiReal : (chi : ℝ) ≤ (Chi : ℝ) := by exact_mod_cast hchi
    have hfirst := mul_le_mul_of_nonneg_left haReal hfirstCoefficient
    have hsecond := mul_le_mul_of_nonneg_left hbReal hsecondCoefficient
    have hthird := mul_le_mul_of_nonneg_left hchiReal hthirdCoefficient
    calc
      G ≤
          (((h + 2 * k : ℕ) : ℝ) /
              ((h * k + h + k : ℕ) : ℝ)) * (a : ℝ) +
            ((k : ℝ) / ((h * k + h + k : ℕ) : ℝ)) * (b : ℝ) +
              ((((h * k + h + k : ℕ) : ℝ) - 1) / 2) *
                (chi : ℝ) := hbound
      _ ≤
          (((h + 2 * k : ℕ) : ℝ) / (n : ℝ)) * (A : ℝ) +
            ((k : ℝ) / (n : ℝ)) * (B : ℝ) +
              (((n : ℝ) - 1) / 2) * (Chi : ℝ) := by
        dsimp only [n] at hfirst hsecond hthird ⊢
        linarith
      _ =
          (((h + 2 * k : ℕ) : ℝ) /
              ((h * k + h + k : ℕ) : ℝ)) * (A : ℝ) +
            ((k : ℝ) / ((h * k + h + k : ℕ) : ℝ)) * (B : ℝ) +
              ((((h * k + h + k : ℕ) : ℝ) - 1) / 2) *
                (Chi : ℝ) := by
        rfl

/-- Convert an auxiliary degree alternative on a finite image curve into the
numerical alternative at the source-curve heights.

Here `a` and `b` are the two image-curve degrees, `A` is the first source
height, and `d` is the source-to-image degree.  In the intended application
`A = d * a`.  The hypothesis `d ≤ Chi` is the precise extra input needed to
absorb the image degree alternative into the source Euler term.  Merely knowing
`a ≤ A` is not enough.

The hypothesis `hauxiliary` deliberately keeps the numerical branch already
at the source degrees `A`, `B`: this is the shape produced by the canonical
Wronskian sum, whose divisor degrees are computed on the source curve. -/
theorem propositionTwoNumericalAlternatives_of_scaledAuxiliaryDegreeAlternative
    (a b d A B p Chi : ℕ) (G : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hA : A ≤ d * a) (hdChi : d ≤ Chi)
    (hG : G ≤ (A : ℝ))
    (hauxiliary : ∀ h k : ℕ,
      PropositionTwoParametersAreAdmissible A B p h k →
        (a ≤ k ∧ b ≤ h) ∨
          G ≤
            (((h + 2 * k : ℕ) : ℝ) /
                ((h * k + h + k : ℕ) : ℝ)) * (A : ℝ) +
              ((k : ℝ) / ((h * k + h + k : ℕ) : ℝ)) * (B : ℝ) +
                ((((h * k + h + k : ℕ) : ℝ) - 1) / 2) *
                  (Chi : ℝ)) :
    PropositionTwoNumericalAlternatives A B p Chi G := by
  intro h k hadmissible
  rcases hauxiliary h k hadmissible with hdegree | hbound
  · right
    let n : ℕ := h * k + h + k
    have hkPos : 0 < k := lt_of_lt_of_le ha hdegree.1
    have hhPos : 0 < h := lt_of_lt_of_le hb hdegree.2
    have hnSub : 2 * k ≤ n - 1 := by
      obtain ⟨h', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hhPos.ne'
      simp only [n, Nat.succ_mul, Nat.succ_eq_add_one]
      omega
    have hnOne : 1 ≤ n := by dsimp only [n]; omega
    have hnSubReal : (2 * k : ℝ) ≤ (n : ℝ) - 1 := by
      have hnSubCast : ((2 * k : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
        exact_mod_cast hnSub
      rw [Nat.cast_sub hnOne] at hnSubCast
      norm_num at hnSubCast ⊢
      exact hnSubCast
    have hkEulerHalf : (k : ℝ) ≤ ((n : ℝ) - 1) / 2 := by
      linarith
    have hEulerHalfNonneg : 0 ≤ ((n : ℝ) - 1) / 2 :=
      (Nat.cast_nonneg k).trans hkEulerHalf
    have hdChiReal : (d : ℝ) ≤ (Chi : ℝ) := by exact_mod_cast hdChi
    have hkEuler : (d : ℝ) * (k : ℝ) ≤
        (((n : ℝ) - 1) / 2) * (Chi : ℝ) := by
      calc
        (d : ℝ) * (k : ℝ) ≤ (Chi : ℝ) * (k : ℝ) :=
          mul_le_mul_of_nonneg_right hdChiReal (Nat.cast_nonneg _)
        _ = (k : ℝ) * (Chi : ℝ) := by ring
        _ ≤ (((n : ℝ) - 1) / 2) * (Chi : ℝ) :=
          mul_le_mul_of_nonneg_right hkEulerHalf (Nat.cast_nonneg _)
    have hAk : A ≤ d * k :=
      hA.trans (Nat.mul_le_mul_left d hdegree.1)
    have hGdk : G ≤ (d : ℝ) * (k : ℝ) := by
      calc
        G ≤ (A : ℝ) := hG
        _ ≤ ((d * k : ℕ) : ℝ) := by exact_mod_cast hAk
        _ = (d : ℝ) * (k : ℝ) := by norm_num
    have hnPosReal : 0 < (n : ℝ) := by exact_mod_cast hadmissible.1
    have hfirstNonneg :
        0 ≤ (((h + 2 * k : ℕ) : ℝ) / (n : ℝ)) * (A : ℝ) :=
      mul_nonneg (div_nonneg (Nat.cast_nonneg _) hnPosReal.le)
        (Nat.cast_nonneg _)
    have hsecondNonneg :
        0 ≤ ((k : ℝ) / (n : ℝ)) * (B : ℝ) :=
      mul_nonneg (div_nonneg (Nat.cast_nonneg _) hnPosReal.le)
        (Nat.cast_nonneg _)
    calc
      G ≤ (d : ℝ) * (k : ℝ) := hGdk
      _ ≤ (((n : ℝ) - 1) / 2) * (Chi : ℝ) := hkEuler
      _ ≤
          (((h + 2 * k : ℕ) : ℝ) / (n : ℝ)) * (A : ℝ) +
            ((k : ℝ) / (n : ℝ)) * (B : ℝ) +
              (((n : ℝ) - 1) / 2) * (Chi : ℝ) := by
        linarith
      _ =
          (((h + 2 * k : ℕ) : ℝ) /
              ((h * k + h + k : ℕ) : ℝ)) * (A : ℝ) +
            ((k : ℝ) / ((h * k + h + k : ℕ) : ℝ)) * (B : ℝ) +
              ((((h * k + h + k : ℕ) : ℝ) - 1) / 2) *
                (Chi : ℝ) := by
        rfl
  · exact Or.inr hbound

end

end BGS.CorvajaZannier
