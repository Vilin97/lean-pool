/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Core.Action

/-!
# Divisibility of Markoff orbit cardinalities

This file formalizes Daniel E. Martin's elementary proof of the Markoff-graph corollary of
Chen's theorem.  Piecewise Penner weights sum to one at every punctured Markoff point, while the
weight in coordinate `i` pairs to one across the `i`-th Vieta involution.  Reindexing a finite
Vieta-invariant set by those involutions then forces its cardinality to vanish in the ground
field.  Over `ZMod p`, this says that `p` divides the cardinality.

The result is stated only for `3 < p`.  This is the range used in Martin's proof and is necessary:
at `p = 3` the eight points with all coordinates in `{1, -1}` form one Vieta component.
-/

@[expose] public section

namespace BGS.Markoff

universe u

/-- Martin's piecewise Penner weights in the original Markoff coordinates. -/
noncomputable def pennerWeights {F : Type u} [Field F] (x : Point F) : Point F := by
  classical
  exact if hx1 : x.x1 = 0 then
      ⟨0, 1 / 2, 1 / 2⟩
    else if hx2 : x.x2 = 0 then
      ⟨1 / 2, 0, 1 / 2⟩
    else if hx3 : x.x3 = 0 then
      ⟨1 / 2, 1 / 2, 0⟩
    else
      ⟨x.x1 / (3 * x.x2 * x.x3),
        x.x2 / (3 * x.x1 * x.x3),
        x.x3 / (3 * x.x1 * x.x2)⟩

/-- Penner weights restricted to the punctured Markoff surface. -/
noncomputable def puncturedPennerWeights {F : Type u} [Field F]
    (x : PuncturedMarkoffSurface F) : Point F :=
  pennerWeights x.1.1

private theorem half_add_half_eq_one {F : Type u} [Field F] (htwo : (2 : F) ≠ 0) :
    (1 / 2 : F) + 1 / 2 = 1 := by
  field_simp
  ring

private theorem first_ne_zero_of_second_eq_zero
    {F : Type u} [Field F] (x : PuncturedMarkoffSurface F)
    (hx2 : x.1.1.x2 = 0) : x.1.1.x1 ≠ 0 := by
  intro hx1
  have hx3 : x.1.1.x3 = 0 := by
    have hmark := x.1.2
    simp [IsMarkoff, markoffPolynomial, hx1, hx2] at hmark
    exact hmark
  apply x.2
  apply Subtype.ext
  ext <;> simp [surfaceOrigin, origin, hx1, hx2, hx3]

private theorem first_ne_zero_of_third_eq_zero
    {F : Type u} [Field F] (x : PuncturedMarkoffSurface F)
    (hx3 : x.1.1.x3 = 0) : x.1.1.x1 ≠ 0 := by
  intro hx1
  have hx2 : x.1.1.x2 = 0 := by
    have hmark := x.1.2
    simp [IsMarkoff, markoffPolynomial, hx1, hx3] at hmark
    exact hmark
  apply x.2
  apply Subtype.ext
  ext <;> simp [surfaceOrigin, origin, hx1, hx2, hx3]

private theorem second_ne_zero_of_first_eq_zero
    {F : Type u} [Field F] (x : PuncturedMarkoffSurface F)
    (hx1 : x.1.1.x1 = 0) : x.1.1.x2 ≠ 0 := by
  intro hx2
  have hx3 : x.1.1.x3 = 0 := by
    have hmark := x.1.2
    simp [IsMarkoff, markoffPolynomial, hx1, hx2] at hmark
    exact hmark
  apply x.2
  apply Subtype.ext
  ext <;> simp [surfaceOrigin, origin, hx1, hx2, hx3]

private theorem second_ne_zero_of_third_eq_zero
    {F : Type u} [Field F] (x : PuncturedMarkoffSurface F)
    (hx3 : x.1.1.x3 = 0) : x.1.1.x2 ≠ 0 := by
  intro hx2
  have hx1 : x.1.1.x1 = 0 := by
    have hmark := x.1.2
    simp [IsMarkoff, markoffPolynomial, hx2, hx3] at hmark
    exact hmark
  apply x.2
  apply Subtype.ext
  ext <;> simp [surfaceOrigin, origin, hx1, hx2, hx3]

private theorem third_ne_zero_of_first_eq_zero
    {F : Type u} [Field F] (x : PuncturedMarkoffSurface F)
    (hx1 : x.1.1.x1 = 0) : x.1.1.x3 ≠ 0 := by
  intro hx3
  have hx2 : x.1.1.x2 = 0 := by
    have hmark := x.1.2
    simp [IsMarkoff, markoffPolynomial, hx1, hx3] at hmark
    exact hmark
  apply x.2
  apply Subtype.ext
  ext <;> simp [surfaceOrigin, origin, hx1, hx2, hx3]

private theorem third_ne_zero_of_second_eq_zero
    {F : Type u} [Field F] (x : PuncturedMarkoffSurface F)
    (hx2 : x.1.1.x2 = 0) : x.1.1.x3 ≠ 0 := by
  intro hx3
  have hx1 : x.1.1.x1 = 0 := by
    have hmark := x.1.2
    simp [IsMarkoff, markoffPolynomial, hx2, hx3] at hmark
    exact hmark
  apply x.2
  apply Subtype.ext
  ext <;> simp [surfaceOrigin, origin, hx1, hx2, hx3]

private theorem pennerWeights_first_of_second_third_ne_zero
    {F : Type u} [Field F] (x : Point F) (hx2 : x.x2 ≠ 0) (hx3 : x.x3 ≠ 0) :
    (pennerWeights x).x1 = x.x1 / (3 * x.x2 * x.x3) := by
  by_cases hx1 : x.x1 = 0
  · simp [pennerWeights, hx1]
  · simp [pennerWeights, hx1, hx2, hx3]

private theorem pennerWeights_second_of_first_third_ne_zero
    {F : Type u} [Field F] (x : Point F) (hx1 : x.x1 ≠ 0) (hx3 : x.x3 ≠ 0) :
    (pennerWeights x).x2 = x.x2 / (3 * x.x1 * x.x3) := by
  by_cases hx2 : x.x2 = 0
  · simp [pennerWeights, hx1, hx2]
  · simp [pennerWeights, hx1, hx2, hx3]

private theorem pennerWeights_third_of_first_second_ne_zero
    {F : Type u} [Field F] (x : Point F) (hx1 : x.x1 ≠ 0) (hx2 : x.x2 ≠ 0) :
    (pennerWeights x).x3 = x.x3 / (3 * x.x1 * x.x2) := by
  by_cases hx3 : x.x3 = 0
  · simp [pennerWeights, hx1, hx2, hx3]
  · simp [pennerWeights, hx1, hx2, hx3]

/-- The three Penner weights at a punctured Markoff point sum to one. -/
theorem puncturedPennerWeights_sum_eq_one
    {F : Type u} [Field F] (htwo : (2 : F) ≠ 0) (hthree : (3 : F) ≠ 0)
    (x : PuncturedMarkoffSurface F) :
    (puncturedPennerWeights x).x1 + (puncturedPennerWeights x).x2 +
        (puncturedPennerWeights x).x3 = 1 := by
  by_cases hx1 : x.1.1.x1 = 0
  · simpa [puncturedPennerWeights, pennerWeights, hx1] using half_add_half_eq_one htwo
  by_cases hx2 : x.1.1.x2 = 0
  · simpa [puncturedPennerWeights, pennerWeights, hx1, hx2] using half_add_half_eq_one htwo
  by_cases hx3 : x.1.1.x3 = 0
  · simpa [puncturedPennerWeights, pennerWeights, hx1, hx2, hx3] using
      half_add_half_eq_one htwo
  have hmark := x.1.2
  change x.1.1.x1 ^ 2 + x.1.1.x2 ^ 2 + x.1.1.x3 ^ 2 -
      3 * x.1.1.x1 * x.1.1.x2 * x.1.1.x3 = 0 at hmark
  rw [sub_eq_zero] at hmark
  simp only [puncturedPennerWeights, pennerWeights, hx1, hx2, hx3, ↓reduceDIte]
  calc
    x.1.1.x1 / (3 * x.1.1.x2 * x.1.1.x3) +
          x.1.1.x2 / (3 * x.1.1.x1 * x.1.1.x3) +
          x.1.1.x3 / (3 * x.1.1.x1 * x.1.1.x2) =
        (x.1.1.x1 ^ 2 + x.1.1.x2 ^ 2 + x.1.1.x3 ^ 2) /
          (3 * x.1.1.x1 * x.1.1.x2 * x.1.1.x3) := by
            field_simp [hx1, hx2, hx3, hthree]
    _ = 1 := by rw [hmark]; field_simp [hx1, hx2, hx3, hthree]

/-- The first Penner weight pairs to one across the first Vieta involution. -/
theorem puncturedPennerWeight_first_add_vieta1_eq_one
    {F : Type u} [Field F] (htwo : (2 : F) ≠ 0) (hthree : (3 : F) ≠ 0)
    (x : PuncturedMarkoffSurface F) :
    (puncturedPennerWeights x).x1 +
        (puncturedPennerWeights (vieta1PuncturedPerm F x)).x1 = 1 := by
  change (pennerWeights x.1.1).x1 + (pennerWeights (vieta1 x.1.1)).x1 = 1
  by_cases hx2 : x.1.1.x2 = 0
  · have hx1 := first_ne_zero_of_second_eq_zero x hx2
    simpa [pennerWeights, vieta1, hx1, hx2] using half_add_half_eq_one htwo
  by_cases hx3 : x.1.1.x3 = 0
  · have hx1 := first_ne_zero_of_third_eq_zero x hx3
    simpa [pennerWeights, vieta1, hx1, hx2, hx3] using half_add_half_eq_one htwo
  rw [pennerWeights_first_of_second_third_ne_zero x.1.1 hx2 hx3]
  rw [pennerWeights_first_of_second_third_ne_zero (vieta1 x.1.1) (by simpa [vieta1])
    (by simpa [vieta1])]
  simp only [vieta1]
  field_simp [hx2, hx3, hthree]
  ring

/-- The second Penner weight pairs to one across the second Vieta involution. -/
theorem puncturedPennerWeight_second_add_vieta2_eq_one
    {F : Type u} [Field F] (htwo : (2 : F) ≠ 0) (hthree : (3 : F) ≠ 0)
    (x : PuncturedMarkoffSurface F) :
    (puncturedPennerWeights x).x2 +
        (puncturedPennerWeights (vieta2PuncturedPerm F x)).x2 = 1 := by
  change (pennerWeights x.1.1).x2 + (pennerWeights (vieta2 x.1.1)).x2 = 1
  by_cases hx1 : x.1.1.x1 = 0
  · have hx2 := second_ne_zero_of_first_eq_zero x hx1
    simpa [pennerWeights, vieta2, hx1, hx2] using half_add_half_eq_one htwo
  by_cases hx3 : x.1.1.x3 = 0
  · have hx2 := second_ne_zero_of_third_eq_zero x hx3
    simpa [pennerWeights, vieta2, hx1, hx2, hx3] using half_add_half_eq_one htwo
  rw [pennerWeights_second_of_first_third_ne_zero x.1.1 hx1 hx3]
  rw [pennerWeights_second_of_first_third_ne_zero (vieta2 x.1.1) (by simpa [vieta2])
    (by simpa [vieta2])]
  simp only [vieta2]
  field_simp [hx1, hx3, hthree]
  ring

/-- The third Penner weight pairs to one across the third Vieta involution. -/
theorem puncturedPennerWeight_third_add_vieta3_eq_one
    {F : Type u} [Field F] (htwo : (2 : F) ≠ 0) (hthree : (3 : F) ≠ 0)
    (x : PuncturedMarkoffSurface F) :
    (puncturedPennerWeights x).x3 +
        (puncturedPennerWeights (vieta3PuncturedPerm F x)).x3 = 1 := by
  change (pennerWeights x.1.1).x3 + (pennerWeights (vieta3 x.1.1)).x3 = 1
  by_cases hx1 : x.1.1.x1 = 0
  · have hx3 := third_ne_zero_of_first_eq_zero x hx1
    simpa [pennerWeights, vieta3, hx1, hx3] using half_add_half_eq_one htwo
  by_cases hx2 : x.1.1.x2 = 0
  · have hx3 := third_ne_zero_of_second_eq_zero x hx2
    simpa [pennerWeights, vieta3, hx1, hx2, hx3] using half_add_half_eq_one htwo
  rw [pennerWeights_third_of_first_second_ne_zero x.1.1 hx1 hx2]
  rw [pennerWeights_third_of_first_second_ne_zero (vieta3 x.1.1) (by simpa [vieta3])
    (by simpa [vieta3])]
  simp only [vieta3]
  field_simp [hx1, hx2, hthree]
  ring

/-- A finite punctured Markoff set invariant under all three Vieta involutions has cardinality
zero in the ground field. -/
theorem card_cast_eq_zero_of_vieta_invariant
    {F : Type u} [Field F] (htwo : (2 : F) ≠ 0) (hthree : (3 : F) ≠ 0)
    (C : Finset (PuncturedMarkoffSurface F))
    (hC1 : ∀ x, vieta1PuncturedPerm F x ∈ C ↔ x ∈ C)
    (hC2 : ∀ x, vieta2PuncturedPerm F x ∈ C ↔ x ∈ C)
    (hC3 : ∀ x, vieta3PuncturedPerm F x ∈ C ↔ x ∈ C) :
    (C.card : F) = 0 := by
  classical
  have hreindex1 :
      (∑ x : C, (puncturedPennerWeights (vieta1PuncturedPerm F x.1)).x1) =
        ∑ x : C, (puncturedPennerWeights x.1).x1 := by
    simpa [Equiv.Perm.subtypePerm_apply] using
      (Equiv.sum_comp ((vieta1PuncturedPerm F).subtypePerm hC1)
        (fun x : C ↦ (puncturedPennerWeights x.1).x1))
  have hreindex2 :
      (∑ x : C, (puncturedPennerWeights (vieta2PuncturedPerm F x.1)).x2) =
        ∑ x : C, (puncturedPennerWeights x.1).x2 := by
    simpa [Equiv.Perm.subtypePerm_apply] using
      (Equiv.sum_comp ((vieta2PuncturedPerm F).subtypePerm hC2)
        (fun x : C ↦ (puncturedPennerWeights x.1).x2))
  have hreindex3 :
      (∑ x : C, (puncturedPennerWeights (vieta3PuncturedPerm F x.1)).x3) =
        ∑ x : C, (puncturedPennerWeights x.1).x3 := by
    simpa [Equiv.Perm.subtypePerm_apply] using
      (Equiv.sum_comp ((vieta3PuncturedPerm F).subtypePerm hC3)
        (fun x : C ↦ (puncturedPennerWeights x.1).x3))
  have hsum1 :
      (2 : F) * (∑ x : C, (puncturedPennerWeights x.1).x1) = C.card := by
    calc
      (2 : F) * (∑ x : C, (puncturedPennerWeights x.1).x1) =
          (∑ x : C, (puncturedPennerWeights x.1).x1) +
            ∑ x : C, (puncturedPennerWeights x.1).x1 := by ring
      _ = (∑ x : C, (puncturedPennerWeights x.1).x1) +
            ∑ x : C, (puncturedPennerWeights (vieta1PuncturedPerm F x.1)).x1 := by
              rw [hreindex1]
      _ = ∑ x : C, ((puncturedPennerWeights x.1).x1 +
            (puncturedPennerWeights (vieta1PuncturedPerm F x.1)).x1) := by
              rw [Finset.sum_add_distrib]
      _ = ∑ _x : C, (1 : F) := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact puncturedPennerWeight_first_add_vieta1_eq_one htwo hthree x.1
      _ = C.card := by simp
  have hsum2 :
      (2 : F) * (∑ x : C, (puncturedPennerWeights x.1).x2) = C.card := by
    calc
      (2 : F) * (∑ x : C, (puncturedPennerWeights x.1).x2) =
          (∑ x : C, (puncturedPennerWeights x.1).x2) +
            ∑ x : C, (puncturedPennerWeights x.1).x2 := by ring
      _ = (∑ x : C, (puncturedPennerWeights x.1).x2) +
            ∑ x : C, (puncturedPennerWeights (vieta2PuncturedPerm F x.1)).x2 := by
              rw [hreindex2]
      _ = ∑ x : C, ((puncturedPennerWeights x.1).x2 +
            (puncturedPennerWeights (vieta2PuncturedPerm F x.1)).x2) := by
              rw [Finset.sum_add_distrib]
      _ = ∑ _x : C, (1 : F) := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact puncturedPennerWeight_second_add_vieta2_eq_one htwo hthree x.1
      _ = C.card := by simp
  have hsum3 :
      (2 : F) * (∑ x : C, (puncturedPennerWeights x.1).x3) = C.card := by
    calc
      (2 : F) * (∑ x : C, (puncturedPennerWeights x.1).x3) =
          (∑ x : C, (puncturedPennerWeights x.1).x3) +
            ∑ x : C, (puncturedPennerWeights x.1).x3 := by ring
      _ = (∑ x : C, (puncturedPennerWeights x.1).x3) +
            ∑ x : C, (puncturedPennerWeights (vieta3PuncturedPerm F x.1)).x3 := by
              rw [hreindex3]
      _ = ∑ x : C, ((puncturedPennerWeights x.1).x3 +
            (puncturedPennerWeights (vieta3PuncturedPerm F x.1)).x3) := by
              rw [Finset.sum_add_distrib]
      _ = ∑ _x : C, (1 : F) := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact puncturedPennerWeight_third_add_vieta3_eq_one htwo hthree x.1
      _ = C.card := by simp
  have htotal :
      (∑ x : C, (puncturedPennerWeights x.1).x1) +
          (∑ x : C, (puncturedPennerWeights x.1).x2) +
          (∑ x : C, (puncturedPennerWeights x.1).x3) = C.card := by
    calc
      (∑ x : C, (puncturedPennerWeights x.1).x1) +
            (∑ x : C, (puncturedPennerWeights x.1).x2) +
            (∑ x : C, (puncturedPennerWeights x.1).x3) =
          ∑ x : C, ((puncturedPennerWeights x.1).x1 +
            (puncturedPennerWeights x.1).x2 + (puncturedPennerWeights x.1).x3) := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = ∑ _x : C, (1 : F) := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact puncturedPennerWeights_sum_eq_one htwo hthree x.1
      _ = C.card := by simp
  linear_combination 2 * htotal - hsum1 - hsum2 - hsum3

/-- Every `Gamma` orbit on the punctured Markoff surface over `ZMod p` has cardinality divisible
by `p` once `3 < p`. -/
theorem prime_dvd_puncturedGammaOrbit_ncard
    (p : ℕ) [Fact p.Prime] (hpThree : 3 < p)
    (x : PuncturedMarkoffSurface (ZMod p)) :
    p ∣ (puncturedGammaOrbit x).ncard := by
  classical
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hpDvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hpDvd
  have hthree : (3 : ZMod p) ≠ 0 := by
    intro hzero
    have hpDvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hzero
    exact (Nat.not_dvd_of_pos_of_lt (by omega) hpThree) hpDvd
  let S := puncturedGammaOrbit x
  have hS : S.Finite := Set.toFinite S
  let C : Finset (PuncturedMarkoffSurface (ZMod p)) := hS.toFinset
  have hC1 : ∀ y, vieta1PuncturedPerm (ZMod p) y ∈ C ↔ y ∈ C := by
    intro y
    simp only [C, Set.Finite.mem_toFinset]
    constructor
    · intro hy
      exact samePuncturedComponent_trans hy
        (samePuncturedComponent_symm (samePuncturedComponent_vieta1 y))
    · intro hy
      exact samePuncturedComponent_trans hy (samePuncturedComponent_vieta1 y)
  have hC2 : ∀ y, vieta2PuncturedPerm (ZMod p) y ∈ C ↔ y ∈ C := by
    intro y
    simp only [C, Set.Finite.mem_toFinset]
    constructor
    · intro hy
      exact samePuncturedComponent_trans hy
        (samePuncturedComponent_symm (samePuncturedComponent_vieta2 y))
    · intro hy
      exact samePuncturedComponent_trans hy (samePuncturedComponent_vieta2 y)
  have hC3 : ∀ y, vieta3PuncturedPerm (ZMod p) y ∈ C ↔ y ∈ C := by
    intro y
    simp only [C, Set.Finite.mem_toFinset]
    constructor
    · intro hy
      exact samePuncturedComponent_trans hy
        (samePuncturedComponent_symm (samePuncturedComponent_vieta3 y))
    · intro hy
      exact samePuncturedComponent_trans hy (samePuncturedComponent_vieta3 y)
  have hzero : (C.card : ZMod p) = 0 :=
    card_cast_eq_zero_of_vieta_invariant htwo hthree C hC1 hC2 hC3
  change p ∣ S.ncard
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [Set.ncard_eq_toFinset_card S hS]
  simpa [C] using hzero

end BGS.Markoff
