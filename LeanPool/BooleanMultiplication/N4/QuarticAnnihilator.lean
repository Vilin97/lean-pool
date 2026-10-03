/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.QuarticSeedUsing

/-!
# Rational quartic annihilators in the Hankel target

Nine fixed exterior coordinates classify the target two-forms annihilated by
a nonzero rational direction.  The certificate ranges over only the seven
nonzero rational coefficient vectors and 128 Hankel words.  It is an
algebraic coordinate check, not a circuit or truth-table enumeration.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- The unit coefficient vector for one rational place. -/
@[expose] def rationalSingleton (theta : Fin 3) : Fin 3 → F₂ :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]] theta

/-- A first-jet target at a rational place, optionally translated by the place itself. -/
@[expose] def rationalTangentAt (theta : Fin 3) (eps : F₂) : TargetCoeff :=
  match theta with
  | ⟨0, _⟩ => ![eps, 1, 0, 0, 0, 0, 0]
  | ⟨1, _⟩ =>
      ![eps, 1 + eps, eps, 1 + eps, eps, 1 + eps, eps]
  | ⟨2, _⟩ => ![0, 0, 0, 0, 0, 1, eps]

/-- A compact set of quartic coordinates sufficient for the rational
annihilator classification. -/
@[expose]
def quarticAnnihilatorCoord :
    Fin 9 → Fin 8 × Fin 8 × Fin 8 × Fin 8 :=
  ![(0,1,4,5), (0,3,5,7), (0,1,4,6),
    (0,3,4,7), (0,3,6,7), (0,1,4,7),
    (1,3,6,7), (0,2,4,7), (2,3,6,7)]

/-- Extract a designated quartic-annihilator coordinate of a wedge of two two-forms. -/
def quarticAnnihilatorProbe (q r : TwoForm) (k : Fin 9) : F₂ :=
  let ijkl := quarticAnnihilatorCoord k
  wedgeTwo q r ijkl.1 ijkl.2.1 ijkl.2.2.1 ijkl.2.2.2

/-- Packed `9 × (7·3)` bilinear coefficient matrix for the probe. -/
def quarticAnnihilatorTable : Fin 9 → Nat :=
  ![0x0000c2, 0x082430, 0x000692,
    0x0c0006, 0x090580, 0x003412,
    0x092c00, 0x018482, 0x086000]

/-- The scalar bilinear formula for a quartic-annihilator probe on target coordinates. -/
@[expose] def quarticAnnihilatorCoeffProbe
    (c : TargetCoeff) (delta : Fin 3 → F₂) (k : Fin 9) : F₂ :=
  match k with
  | ⟨0, _⟩ => c 0 * delta 1 + c 2 * delta 0 + c 2 * delta 1
  | ⟨1, _⟩ => c 1 * delta 1 + c 1 * delta 2 + c 3 * delta 1 +
      c 4 * delta 1 + c 6 * delta 1
  | ⟨2, _⟩ => c 0 * delta 1 + c 1 * delta 1 + c 2 * delta 1 +
      c 3 * delta 0 + c 3 * delta 1
  | ⟨3, _⟩ => c 0 * delta 1 + c 0 * delta 2 +
      c 6 * delta 0 + c 6 * delta 1
  | ⟨4, _⟩ => c 2 * delta 1 + c 2 * delta 2 + c 3 * delta 1 +
      c 5 * delta 1 + c 6 * delta 1
  | ⟨5, _⟩ => c 0 * delta 1 + c 1 * delta 1 + c 3 * delta 1 +
      c 4 * delta 0 + c 4 * delta 1
  | ⟨6, _⟩ => c 3 * delta 1 + c 3 * delta 2 + c 4 * delta 1 +
      c 5 * delta 1 + c 6 * delta 1
  | ⟨7, _⟩ => c 0 * delta 1 + c 2 * delta 1 + c 3 * delta 1 +
      c 5 * delta 0 + c 5 * delta 1
  | ⟨8, _⟩ => c 4 * delta 1 + c 4 * delta 2 + c 6 * delta 1

/-- Every designated quartic-annihilator coefficient vanishes. -/
@[expose]
def VanishesOnQuarticAnnihilatorProbe
    (c : TargetCoeff) (delta : Fin 3 → F₂) : Prop :=
  ∀ k : Fin 9, quarticAnnihilatorCoeffProbe c delta k = 0

instance (c : TargetCoeff) (delta : Fin 3 → F₂) :
    Decidable (VanishesOnQuarticAnnihilatorProbe c delta) := by
  unfold VanishesOnQuarticAnnihilatorProbe
  infer_instance

theorem quarticAnnihilatorCoeffProbe_eq
    (c : TargetCoeff) (delta : Fin 3 → F₂) (k : Fin 9) :
    quarticAnnihilatorCoeffProbe c delta k =
      quarticAnnihilatorProbe (targetTwo c) (rationalTwo delta) k := by
  fin_cases k <;>
    simp [quarticAnnihilatorCoeffProbe, quarticAnnihilatorProbe, quarticAnnihilatorCoord,
      wedgeTwo, targetTwo, rationalTwo, rationalPlaceTwo, vectorWedge, placeA, placeB,
      Fin.sum_univ_succ] <;>
    ring_nf <;>
    simp [N3Certificate.two_eq_zero_f2]

/-- The rational-place coefficient vectors paired with the six tangent targets. -/
@[expose]
def rationalAnnihilatorDelta : Fin 6 → (Fin 3 → F₂) :=
  ![![1, 0, 0], ![1, 0, 0],
    ![0, 1, 0], ![0, 1, 0],
    ![0, 0, 1], ![0, 0, 1]]

/-- Packed finite form of the rational target-annihilator certificate. -/
theorem rational_target_annihilator_pair_classification :
    ∀ (delta : Fin 3 → F₂) (c : TargetCoeff),
      delta ≠ 0 →
      ¬ IsRationalCoeff c →
      VanishesOnQuarticAnnihilatorProbe c delta →
      ∃ i : Fin 6,
        delta = rationalAnnihilatorDelta i ∧ c = tangentWord i := by
  decide +kernel

/-- A nonrational Hankel target annihilated by a nonzero rational two-form is
a first tangent at one of the three singleton rational places. -/
theorem rational_target_annihilator_classification
    (delta : Fin 3 → F₂) (c : TargetCoeff)
    (hdelta : delta ≠ 0) (hc : ¬ IsRationalCoeff c)
    (hprobe : VanishesOnQuarticAnnihilatorProbe c delta) :
    ∃ (theta : Fin 3) (eps : F₂),
      delta = rationalSingleton theta ∧
      c = rationalTangentAt theta eps := by
  rcases rational_target_annihilator_pair_classification
    delta c hdelta hc hprobe with ⟨i, hdeltaPair, hcPair⟩
  fin_cases i
  · exact ⟨0, 0, by simpa [rationalSingleton, rationalAnnihilatorDelta] using hdeltaPair,
      by simpa [rationalTangentAt, tangentWord, outsideRankTwoWord] using hcPair⟩
  · exact ⟨0, 1, by simpa [rationalSingleton, rationalAnnihilatorDelta] using hdeltaPair,
      by simpa [rationalTangentAt, tangentWord, outsideRankTwoWord] using hcPair⟩
  · exact ⟨1, 0, by simpa [rationalSingleton, rationalAnnihilatorDelta] using hdeltaPair,
      by simpa [rationalTangentAt, tangentWord, outsideRankTwoWord] using hcPair⟩
  · exact ⟨1, 1, by simpa [rationalSingleton, rationalAnnihilatorDelta] using hdeltaPair,
      by
        rw [hcPair]
        funext j
        fin_cases j <;> decide⟩
  · exact ⟨2, 0, by simpa [rationalSingleton, rationalAnnihilatorDelta] using hdeltaPair,
      by simpa [rationalTangentAt, tangentWord, outsideRankTwoWord] using hcPair⟩
  · exact ⟨2, 1, by simpa [rationalSingleton, rationalAnnihilatorDelta] using hdeltaPair,
      by simpa [rationalTangentAt, tangentWord, outsideRankTwoWord] using hcPair⟩

theorem vanishesOnQuarticAnnihilatorProbe_of_wedge_zero
    {c : TargetCoeff} {delta : Fin 3 → F₂}
    (h : wedgeTwo (targetTwo c) (rationalTwo delta) = 0) :
    VanishesOnQuarticAnnihilatorProbe c delta := by
  intro k
  have hk := congrFun (congrFun (congrFun (congrFun h
    (quarticAnnihilatorCoord k).1)
    (quarticAnnihilatorCoord k).2.1)
    (quarticAnnihilatorCoord k).2.2.1)
    (quarticAnnihilatorCoord k).2.2.2
  rw [quarticAnnihilatorCoeffProbe_eq]
  simpa [quarticAnnihilatorProbe] using hk

end

end N4
end UnrestrictedBooleanMul
