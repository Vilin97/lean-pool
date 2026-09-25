/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Cage.HasseWeilAssumption
public import LeanPool.MarkoffModP.BGS.Markoff.Endgame.LargeOrderToMaximal

/-!
# Connectivity of the selected split cage
-/

@[expose] public section

namespace BGS.Markoff

noncomputable section

/-- Membership in the selected split cage core. -/
def IsInSplitCage (p : ℕ) [Fact p.Prime]
    (x : NormalizedMarkoffSurface (ZMod p)) : Prop :=
  ∃ axis : NormalizedCoordinateAxis,
    IsSplitMaximalTrace p (normalizedCoordinateAt axis x.1)

theorem mem_normalizedFiberAt_coordinate
    {R : Type*} [CommRing R] (axis : NormalizedCoordinateAxis)
    (x : NormalizedMarkoffSurface R) :
    x.1 ∈ normalizedFiberAt axis (normalizedCoordinateAt axis x.1) := by
  cases axis <;> exact ⟨x.property, rfl⟩

theorem isNormalizedMarkoff_of_mem_normalizedFiberAt
    {R : Type*} [CommRing R] {axis : NormalizedCoordinateAxis} {t : R}
    {x : NormalizedPoint R} (hx : x ∈ normalizedFiberAt axis t) :
    IsNormalizedMarkoff x := by
  cases axis <;> exact hx.1

/-- On a split-maximal first-coordinate fiber, the normalized rotation is transitive. -/
theorem sameNormalizedComponent_of_mem_splitMaximal_firstFiber
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)] (hpSeven : 7 ≤ p)
    (t : ZMod p) (hmax : IsSplitMaximalTrace p t)
    (x y : ↥(normalizedFiber1 t)) :
    SameNormalizedComponent
      (⟨x.1, x.property.1⟩ : NormalizedMarkoffSurface (ZMod p))
      (⟨y.1, y.property.1⟩ : NormalizedMarkoffSurface (ZMod p)) := by
  have ht0 : t ≠ 0 := by
    intro htZero
    subst t
    have hle := rotationOrder_zero_le_four p
    rw [IsSplitMaximalTrace] at hmax
    rw [hmax] at hle
    omega
  have ht : t ^ 2 ≠ 4 := by
    intro htParabolic
    have htCases : t = 2 ∨ t = -2 := by
      apply (sq_eq_sq_iff_eq_or_eq_neg).mp
      calc
        t ^ 2 = 4 := htParabolic
        _ = (2 : ZMod p) ^ 2 := by norm_num
    rw [IsSplitMaximalTrace] at hmax
    rcases htCases with rfl | rfl
    · rw [rotationOrder_two] at hmax
      omega
    · rw [rotationOrder_neg_two p (by omega)] at hmax
      omega
  rcases exists_split_or_quadraticNormOneTrace p (by omega) t ht with
      ⟨w, htrace, hw⟩ | ⟨w, htrace, hw⟩
  · have htrace0 : splitTorusTrace w ≠ 0 := by simpa [htrace] using ht0
    let xw : ↥(normalizedFiber1 (splitTorusTrace w)) :=
      ⟨x.1, x.property.1, by simpa [htrace] using x.property.2⟩
    let yw : ↥(normalizedFiber1 (splitTorusTrace w)) :=
      ⟨y.1, y.property.1, by simpa [htrace] using y.property.2⟩
    let sx := (splitFiberEquiv w hw htrace0).symm xw
    let sy := (splitFiberEquiv w hw htrace0).symm yw
    have hx : splitFiberPoint w sx = (x : NormalizedPoint (ZMod p)) :=
      congrArg Subtype.val ((splitFiberEquiv w hw htrace0).apply_symm_apply xw)
    have hy : splitFiberPoint w sy = (y : NormalizedPoint (ZMod p)) :=
      congrArg Subtype.val ((splitFiberEquiv w hw htrace0).apply_symm_apply yw)
    have horder : orderOf w = Nat.card (ZMod p)ˣ := by
      have hrotation : rotationOrder t = orderOf w := by
        rw [← htrace, rotationOrder_splitTorusTrace w hw]
      have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
        rw [Nat.card_units, Nat.card_zmod]
      calc
        orderOf w = rotationOrder t := hrotation.symm
        _ = p - 1 := hmax
        _ = Nat.card (ZMod p)ˣ := hcard.symm
    have htop : Subgroup.zpowers w = ⊤ := by
      apply (Subgroup.card_eq_iff_eq_top (H := Subgroup.zpowers w)).mp
      rw [Nat.card_zpowers, horder]
    have hmem : sx⁻¹ * sy ∈ Submonoid.powers w := by
      apply mem_powers_iff_mem_zpowers.mpr
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (sx⁻¹ * sy) w).mp hmem
    have hiterate : (normalizedRotate1^[n]) (x : NormalizedPoint (ZMod p)) = y := by
      rw [← hx, iterate_normalizedRotate1_splitFiberPoint, hn]
      simpa [mul_assoc] using hy
    let xs : NormalizedMarkoffSurface (ZMod p) := ⟨x.1, x.property.1⟩
    let ys : NormalizedMarkoffSurface (ZMod p) := ⟨y.1, y.property.1⟩
    have hsurface : (normalizedRotate1Surface^[n]) xs = ys := by
      apply Subtype.ext
      rw [coe_iterate_normalizedRotate1Surface]
      exact hiterate
    change SameNormalizedComponent xs ys
    rw [← hsurface]
    exact sameNormalizedComponent_iterate_normalizedRotate1Surface xs n
  · have hrotation : rotationOrder t = orderOf w := by
      rw [← htrace, rotationOrder_quadraticNormOneTrace p w hw]
    have horder : orderOf w = p - 1 := by
      rw [← hmax]
      exact hrotation.symm
    have hdvd := orderOf_dvd_natCard w
    rw [quadraticNormOneTorus_natCard, horder] at hdvd
    have hdvdTwo : p - 1 ∣ 2 := by
      have hsub := Nat.dvd_sub hdvd (dvd_refl (p - 1))
      have heq : (p + 1) - (p - 1) = 2 := by omega
      rw [heq] at hsub
      exact hsub
    have hle : p - 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvdTwo
    omega

/-- Any two normalized surface points in the same split-maximal fiber, on any coordinate axis,
lie in the same Markoff component. -/
theorem sameNormalizedComponent_of_mem_same_splitMaximalFiber
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)] (hpSeven : 7 ≤ p)
    (axis : NormalizedCoordinateAxis) (t : ZMod p) (hmax : IsSplitMaximalTrace p t)
    (x y : NormalizedMarkoffSurface (ZMod p))
    (hx : x.1 ∈ normalizedFiberAt axis t)
    (hy : y.1 ∈ normalizedFiberAt axis t) :
    SameNormalizedComponent x y := by
  rcases axis with _ | _ | _
  · let xf : ↥(normalizedFiber1 t) := ⟨x.1, hx⟩
    let yf : ↥(normalizedFiber1 t) := ⟨y.1, hy⟩
    exact sameNormalizedComponent_of_mem_splitMaximal_firstFiber
      p hpSeven t hmax xf yf
  · let x' := normalizedSwap12Surface x
    let y' := normalizedSwap12Surface y
    have hxComp : SameNormalizedComponent x x' := sameNormalizedComponent_swap12Surface x
    have hyComp : SameNormalizedComponent y y' := sameNormalizedComponent_swap12Surface y
    let xf : ↥(normalizedFiber1 t) := ⟨x'.1, x'.property, by
      simpa [x', normalizedSwap12, coe_normalizedSwap12Surface] using hx.2⟩
    let yf : ↥(normalizedFiber1 t) := ⟨y'.1, y'.property, by
      simpa [y', normalizedSwap12, coe_normalizedSwap12Surface] using hy.2⟩
    have hmiddle : SameNormalizedComponent x' y' :=
      sameNormalizedComponent_of_mem_splitMaximal_firstFiber
        p hpSeven t hmax xf yf
    exact sameNormalizedComponent_trans hxComp
      (sameNormalizedComponent_trans hmiddle (sameNormalizedComponent_symm hyComp))
  · let x23 := normalizedSwap23Surface x
    let y23 := normalizedSwap23Surface y
    let x' := normalizedSwap12Surface x23
    let y' := normalizedSwap12Surface y23
    have hx23 : SameNormalizedComponent x x23 := sameNormalizedComponent_swap23Surface x
    have hy23 : SameNormalizedComponent y y23 := sameNormalizedComponent_swap23Surface y
    have hx12 : SameNormalizedComponent x23 x' := sameNormalizedComponent_swap12Surface x23
    have hy12 : SameNormalizedComponent y23 y' := sameNormalizedComponent_swap12Surface y23
    let xf : ↥(normalizedFiber1 t) := ⟨x'.1, x'.property, by
      simpa [x', x23, normalizedSwap12, normalizedSwap23,
        coe_normalizedSwap12Surface, coe_normalizedSwap23Surface] using hx.2⟩
    let yf : ↥(normalizedFiber1 t) := ⟨y'.1, y'.property, by
      simpa [y', y23, normalizedSwap12, normalizedSwap23,
        coe_normalizedSwap12Surface, coe_normalizedSwap23Surface] using hy.2⟩
    have hmiddle : SameNormalizedComponent x' y' :=
      sameNormalizedComponent_of_mem_splitMaximal_firstFiber
        p hpSeven t hmax xf yf
    exact sameNormalizedComponent_trans
      (sameNormalizedComponent_trans hx23 hx12)
      (sameNormalizedComponent_trans hmiddle
        (sameNormalizedComponent_trans
          (sameNormalizedComponent_symm hy12) (sameNormalizedComponent_symm hy23)))

private theorem three_ne_zero_zmod_of_prime_ne_three
    (p : ℕ) [Fact p.Prime] (hpThree : p ≠ 3) : (3 : ZMod p) ≠ 0 := by
  intro hzero
  have hpDvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hzero
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hpDvd with hpOne | hpEq
  · exact (Fact.out : p.Prime).ne_one hpOne
  · exact hpThree hpEq

/-- The selected split cage is connected for all sufficiently large primes, relative only to
the explicit cage Hasse--Weil count assumption. -/
theorem exists_threshold_splitCage_connected
    (coefficient : ℕ) (hHasse : CageWitnessPointEstimate coefficient) :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] → ∀ hpThree : p ≠ 3,
      letI : Invertible (3 : ZMod p) :=
        invertibleOfNonzero (three_ne_zero_zmod_of_prime_ne_three p hpThree)
      ∀ x y : NormalizedMarkoffSurface (ZMod p),
        IsInSplitCage p x → IsInSplitCage p y → SameNormalizedComponent x y := by
  obtain ⟨bridgeThreshold, hbridge⟩ :=
    exists_threshold_splitMaximalFiberBridge coefficient hHasse
  refine ⟨max bridgeThreshold 7, ?_⟩
  intro p hp _ hpThree
  let : Invertible (3 : ZMod p) :=
    invertibleOfNonzero (three_ne_zero_zmod_of_prime_ne_three p hpThree)
  intro x y hxCage hyCage
  rcases hxCage with ⟨axis, hxi⟩
  rcases hyCage with ⟨other, heta⟩
  let xi := normalizedCoordinateAt axis x.1
  let eta := normalizedCoordinateAt other y.1
  obtain ⟨middle, z, hmiddleAxis, hmiddleOther, hzMax, hxMeet, hyMeet⟩ :=
    hbridge p ((le_max_left bridgeThreshold 7).trans hp)
      axis other xi eta hxi heta
  rcases hxMeet with ⟨px, hpxAxis, hpxMiddle⟩
  rcases hyMeet with ⟨py, hpyOther, hpyMiddle⟩
  let pxs : NormalizedMarkoffSurface (ZMod p) :=
    ⟨px, isNormalizedMarkoff_of_mem_normalizedFiberAt hpxAxis⟩
  let pys : NormalizedMarkoffSurface (ZMod p) :=
    ⟨py, isNormalizedMarkoff_of_mem_normalizedFiberAt hpyOther⟩
  have hxFiber : x.1 ∈ normalizedFiberAt axis xi := by
    exact mem_normalizedFiberAt_coordinate axis x
  have hyFiber : y.1 ∈ normalizedFiberAt other eta := by
    exact mem_normalizedFiberAt_coordinate other y
  have hxpx : SameNormalizedComponent x pxs :=
    sameNormalizedComponent_of_mem_same_splitMaximalFiber
      p ((le_max_right bridgeThreshold 7).trans hp) axis xi hxi x pxs
      hxFiber hpxAxis
  have hpxpy : SameNormalizedComponent pxs pys :=
    sameNormalizedComponent_of_mem_same_splitMaximalFiber
      p ((le_max_right bridgeThreshold 7).trans hp) middle z hzMax pxs pys
      hpxMiddle hpyMiddle
  have hypy : SameNormalizedComponent y pys :=
    sameNormalizedComponent_of_mem_same_splitMaximalFiber
      p ((le_max_right bridgeThreshold 7).trans hp) other eta heta y pys
      hyFiber hpyOther
  exact sameNormalizedComponent_trans hxpx
    (sameNormalizedComponent_trans hpxpy (sameNormalizedComponent_symm hypy))

/-- The completed endgame lands in the selected split cage core. -/
theorem exists_threshold_largeOrder_to_splitCage
    (splitCoefficient : ℕ)
    (hSplitWeil : WeightedSplitTraceWeilBoundAssumption splitCoefficient)
    (nonsplitCoefficient : ℕ)
    (hNonsplitWeil : SeededNonsplitTraceWeilBoundAssumption nonsplitCoefficient)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] → ∀ hpThree : p ≠ 3,
      letI : Invertible (3 : ZMod p) :=
        invertibleOfNonzero (three_ne_zero_zmod_of_prime_ne_three p hpThree)
      ∀ x : NormalizedMarkoffSurface (ZMod p),
        ((p : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤ rotationOrder x.1.u1 ∨
          (p : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤ rotationOrder x.1.u2 ∨
          (p : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤ rotationOrder x.1.u3) →
        ∃ y : NormalizedMarkoffSurface (ZMod p),
          SameNormalizedComponent x y ∧ IsInSplitCage p y := by
  obtain ⟨threshold, hendgame⟩ :=
    exists_threshold_sameComponent_maximalRotation_of_some_largeCoordinate
      splitCoefficient hSplitWeil nonsplitCoefficient hNonsplitWeil hδ
  refine ⟨threshold, ?_⟩
  intro p hp _ hpThree
  let : Invertible (3 : ZMod p) :=
    invertibleOfNonzero (three_ne_zero_zmod_of_prime_ne_three p hpThree)
  intro x hlarge
  obtain ⟨y, hxy, hyOrder⟩ := hendgame p hp hpThree x hlarge
  refine ⟨y, hxy, .second, ?_⟩
  exact hyOrder

end

end BGS.Markoff
