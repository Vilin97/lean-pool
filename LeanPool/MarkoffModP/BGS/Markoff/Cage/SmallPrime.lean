/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Cage.PowerCover

/-!
# The small prime in the cage estimate

The geometric cage proof starts at `p = 7`.  The target interface also asks
for `p = 5`; this file handles that one finite field by a transparent ambient
cardinality bound, not by applying an inapplicable irreducibility statement.
-/

@[expose] public section

namespace BGS.Markoff

noncomputable section

local instance cageSmallPrime_factPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private def cageRangeCoordinatesAtFive
    (axis other : NormalizedCoordinateAxis) (xi eta : ZMod 5) (d : ℕ) :
    cageMiddleWitnessPowerRangeSolutions 5 axis other xi eta d →
      Fin 7 → ZMod 5 := fun z i =>
  match i with
  | 0 => z.1.1.1.1.u1
  | 1 => z.1.1.1.1.u2
  | 2 => z.1.1.1.1.u3
  | 3 => z.1.1.1.2.u1
  | 4 => z.1.1.1.2.u2
  | 5 => z.1.1.1.2.u3
  | 6 => z.1.2.1

private lemma cageRangeCoordinatesAtFive_injective
    (axis other : NormalizedCoordinateAxis) (xi eta : ZMod 5) (d : ℕ) :
    Function.Injective (cageRangeCoordinatesAtFive axis other xi eta d) := by
  intro z w h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext <;> apply NormalizedPoint.ext
    · simpa [cageRangeCoordinatesAtFive] using congrFun h (0 : Fin 7)
    · simpa [cageRangeCoordinatesAtFive] using congrFun h (1 : Fin 7)
    · simpa [cageRangeCoordinatesAtFive] using congrFun h (2 : Fin 7)
    · simpa [cageRangeCoordinatesAtFive] using congrFun h (3 : Fin 7)
    · simpa [cageRangeCoordinatesAtFive] using congrFun h (4 : Fin 7)
    · simpa [cageRangeCoordinatesAtFive] using congrFun h (5 : Fin 7)
  · apply Subtype.ext
    apply Units.ext
    simpa [cageRangeCoordinatesAtFive] using congrFun h (6 : Fin 7)

/-- Every witness-bearing power-range set over `ZMod 5` has at most `5^7`
elements. -/
lemma natCard_cageMiddleWitnessPowerRangeSolutions_five_le
    (axis other : NormalizedCoordinateAxis) (xi eta : ZMod 5) (d : ℕ) :
    Nat.card (cageMiddleWitnessPowerRangeSolutions 5 axis other xi eta d) ≤
      78125 := by
  calc
    Nat.card (cageMiddleWitnessPowerRangeSolutions 5 axis other xi eta d) ≤
        Nat.card (Fin 7 → ZMod 5) :=
      Nat.card_le_card_of_injective
        (cageRangeCoordinatesAtFive axis other xi eta d)
        (cageRangeCoordinatesAtFive_injective axis other xi eta d)
    _ = 78125 := by
      rw [Nat.card_fun]
      norm_num [Nat.card_fin, Nat.card_zmod]

/-- A coarse uniform estimate at `p=5`.  Multiplicity one is sufficient for
this isolated finite case. -/
lemma cageWitnessPointEstimate_five :
    ∀ (axis other : NormalizedCoordinateAxis) (xi eta : ZMod 5),
      IsSplitMaximalTrace 5 xi → IsSplitMaximalTrace 5 eta →
      ∃ multiplicity : ℕ, 0 < multiplicity ∧
        ∀ d : ℕ, d ∣ Nat.card (ZMod 5)ˣ → 0 < d →
          |(Nat.card (cageMiddleWitnessPowerRangeSolutions
              5 axis other xi eta d) : ℝ) -
                (multiplicity : ℝ) * (5 : ℝ) / d| ≤
            (100000 : ℝ) * Real.sqrt 5 := by
  intro axis other xi eta _ _
  refine ⟨1, by norm_num, ?_⟩
  intro d _ hd
  have hcardNat :=
    natCard_cageMiddleWitnessPowerRangeSolutions_five_le axis other xi eta d
  have hcardReal :
      (Nat.card (cageMiddleWitnessPowerRangeSolutions
        5 axis other xi eta d) : ℝ) ≤ 78125 := by
    exact_mod_cast hcardNat
  have hdReal : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 5 := by
    have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    have hnonnegative := Real.sqrt_nonneg 5
    nlinarith
  norm_num only [Nat.cast_one, one_mul]
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdivNonnegative : (0 : ℝ) ≤ 5 / d :=
    div_nonneg (by norm_num) hdReal.le
  have hdivLe : (5 : ℝ) / d ≤ 5 := by
    apply (div_le_iff₀ hdReal).mpr
    nlinarith
  apply abs_le.mpr
  constructor <;> nlinarith

end

end BGS.Markoff
