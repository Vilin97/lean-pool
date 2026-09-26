/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Endgame.PrimitiveOrbitWiring
public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.Diagonalization
public import LeanPool.MarkoffModP.BGS.Markoff.Core.ParabolicFibers

/-!
# The parabolic branch of the endgame

The two parabolic fibers are affine lines.  Their explicit rotation formulas make the second
coordinate run through the whole base field, so in particular through the trace of a generator
of the split torus.
-/

@[expose] public section

namespace BGS.Markoff

noncomputable section

private theorem exists_fullOrderBaseUnit (p : ℕ) [Fact p.Prime] :
    ∃ u : (ZMod p)ˣ, orderOf u = Nat.card (ZMod p)ˣ := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  exact ⟨u, orderOf_eq_card_of_forall_mem_zpowers hu⟩

private theorem two_ne_zero_zmod_of_prime_ne_two
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro hzero
  have hpDvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
  have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpDvd
  exact hpTwo (Nat.le_antisymm hpLe (Fact.out : p.Prime).two_le)

/-- Every point of the trace-`2` fiber reaches a primitive split trace in its second
coordinate. -/
theorem exists_iterate_parabolicTwoPoint_with_primitive_secondTrace
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (x : ↥(normalizedFiber1 (2 : ZMod p))) :
    ∃ n : ℕ, ∃ u : (ZMod p)ˣ,
      ((normalizedRotate1^[n]) (x : NormalizedPoint (ZMod p))).u2 =
          splitTorusTrace u ∧
        orderOf u = Nat.card (ZMod p)ˣ := by
  have htwo := two_ne_zero_zmod_of_prime_ne_two p hpTwo
  let i : ZMod p := (x.1.u3 - x.1.u2) / 2
  have hi : i ^ 2 = -1 := by
    have hsurface :
        IsNormalizedMarkoff
          (⟨(2 : ZMod p), x.1.u2, x.1.u3⟩ : NormalizedPoint (ZMod p)) := by
      simpa [← x.property.2] using x.property.1
    have hsquare := (isNormalizedMarkoff_at_two_iff x.1.u2 x.1.u3).mp hsurface
    dsimp [i]
    field_simp [htwo]
    linear_combination hsquare
  have hx : (x : NormalizedPoint (ZMod p)) = parabolicLineAtTwo i x.1.u2 := by
    ext
    · exact x.property.2
    · rfl
    · dsimp [parabolicLineAtTwo, i]
      field_simp [htwo]
      ring
  have hi0 : i ≠ 0 := by
    intro hzero
    rw [hzero] at hi
    norm_num at hi
  have hstep : (2 : ZMod p) * i ≠ 0 := mul_ne_zero htwo hi0
  obtain ⟨u, huOrder⟩ := exists_fullOrderBaseUnit p
  let a : ZMod p := (splitTorusTrace u - x.1.u2) / (2 * i)
  let n : ℕ := a.val
  have hn : (n : ZMod p) = a := by
    exact ZMod.natCast_zmod_val a
  refine ⟨n, u, ?_, huOrder⟩
  rw [hx, iterate_normalizedRotate1_parabolicLineAtTwo]
  change x.1.u2 + (n : ZMod p) * (2 * i) = splitTorusTrace u
  rw [hn]
  dsimp [a]
  field_simp [hstep]
  ring

/-- Every point of the trace-`-2` fiber reaches a primitive split trace in its second
coordinate. -/
theorem exists_iterate_parabolicNegTwoPoint_with_primitive_secondTrace
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (x : ↥(normalizedFiber1 (-2 : ZMod p))) :
    ∃ n : ℕ, ∃ u : (ZMod p)ˣ,
      ((normalizedRotate1^[n]) (x : NormalizedPoint (ZMod p))).u2 =
          splitTorusTrace u ∧
        orderOf u = Nat.card (ZMod p)ˣ := by
  have htwo := two_ne_zero_zmod_of_prime_ne_two p hpTwo
  let i : ZMod p := (x.1.u3 + x.1.u2) / 2
  have hi : i ^ 2 = -1 := by
    have hsurface :
        IsNormalizedMarkoff
          (⟨(-2 : ZMod p), x.1.u2, x.1.u3⟩ : NormalizedPoint (ZMod p)) := by
      simpa [← x.property.2] using x.property.1
    have hsquare := (isNormalizedMarkoff_at_neg_two_iff x.1.u2 x.1.u3).mp hsurface
    dsimp [i]
    field_simp [htwo]
    linear_combination hsquare
  have hx : (x : NormalizedPoint (ZMod p)) = parabolicLineAtNegTwo i x.1.u2 := by
    ext
    · exact x.property.2
    · rfl
    · dsimp [parabolicLineAtNegTwo, i]
      field_simp [htwo]
      ring
  have hi0 : i ≠ 0 := by
    intro hzero
    rw [hzero] at hi
    norm_num at hi
  have hfour : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]
    exact mul_ne_zero htwo htwo
  have hstep : (4 : ZMod p) * i ≠ 0 := mul_ne_zero hfour hi0
  obtain ⟨u, huOrder⟩ := exists_fullOrderBaseUnit p
  let a : ZMod p := (x.1.u2 - splitTorusTrace u) / (4 * i)
  let k : ℕ := a.val
  have hk : (k : ZMod p) = a := ZMod.natCast_zmod_val a
  refine ⟨2 * k, u, ?_, huOrder⟩
  rw [hx, iterate_two_mul_normalizedRotate1_parabolicLineAtNegTwo]
  change x.1.u2 - (k : ZMod p) * (4 * i) = splitTorusTrace u
  rw [hk]
  dsimp [a]
  field_simp [hstep]
  ring

/-- Unified parabolic branch. -/
theorem exists_iterate_parabolicPoint_with_primitive_secondTrace
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (t : ZMod p) (ht : t ^ 2 = 4) (x : ↥(normalizedFiber1 t)) :
    ∃ n : ℕ, ∃ u : (ZMod p)ˣ,
      ((normalizedRotate1^[n]) (x : NormalizedPoint (ZMod p))).u2 =
          splitTorusTrace u ∧
        orderOf u = Nat.card (ZMod p)ˣ := by
  have htCases : t = 2 ∨ t = -2 := by
    apply (sq_eq_sq_iff_eq_or_eq_neg).mp
    calc
      t ^ 2 = 4 := ht
      _ = (2 : ZMod p) ^ 2 := by norm_num
  rcases htCases with rfl | rfl
  · exact exists_iterate_parabolicTwoPoint_with_primitive_secondTrace p hpTwo x
  · exact exists_iterate_parabolicNegTwoPoint_with_primitive_secondTrace p hpTwo x

/-- For primes at least five, the primitive trace reached in the parabolic branch has maximal
split rotation order `p - 1`. -/
theorem exists_iterate_parabolicPoint_with_maximal_secondRotation
    (p : ℕ) [Fact p.Prime] (hpFive : 5 ≤ p)
    (t : ZMod p) (ht : t ^ 2 = 4) (x : ↥(normalizedFiber1 t)) :
    ∃ n : ℕ,
      rotationOrder
          (((normalizedRotate1^[n])
            (x : NormalizedPoint (ZMod p))).u2) = p - 1 := by
  obtain ⟨n, u, hcoordinate, huOrder⟩ :=
    exists_iterate_parabolicPoint_with_primitive_secondTrace p (by omega) t ht x
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_units, Nat.card_zmod]
  have huSq : (u : ZMod p) ^ 2 ≠ 1 := by
    intro huPower
    have huDvd : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one <| by
      apply Units.ext
      exact huPower
    have huLe : orderOf u ≤ 2 := Nat.le_of_dvd (by norm_num) huDvd
    rw [huOrder, hcard] at huLe
    omega
  refine ⟨n, ?_⟩
  rw [hcoordinate, rotationOrder_splitTorusTrace u huSq, huOrder, hcard]

/-- Full first-coordinate form of Proposition 10, including semisimple, parabolic, and the
trace-zero exclusion. -/
theorem exists_threshold_point_with_maximal_secondRotation
    (splitCoefficient : ℕ)
    (hSplitWeil : WeightedSplitTraceWeilBoundAssumption splitCoefficient)
    (nonsplitCoefficient : ℕ)
    (hNonsplitWeil : SeededNonsplitTraceWeilBoundAssumption nonsplitCoefficient)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ threshold : ℕ, ∀ p : ℕ, threshold ≤ p → [Fact p.Prime] →
      ∀ (t : ZMod p) (x : ↥(normalizedFiber1 t)),
        (p : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤ rotationOrder t →
        ∃ n : ℕ,
          rotationOrder
              (((normalizedRotate1^[n])
                (x : NormalizedPoint (ZMod p))).u2) = p - 1 := by
  obtain ⟨semisimpleThreshold, hSemisimple⟩ :=
    exists_threshold_nonparabolicPoint_with_maximal_secondRotation
      splitCoefficient hSplitWeil nonsplitCoefficient hNonsplitWeil hδ
  have hexponent : (0 : ℝ) < (1 : ℝ) / 2 + δ := by linarith
  have hZeroAbsorb :
      ∀ᶠ p : ℕ in Filter.atTop,
        4 < (p : ℝ) ^ ((1 : ℝ) / 2 + δ) := by
    simpa using
      (eventually_const_mul_rpow_lt_rpow
        (C := (4 : ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ) / 2 + δ) hexponent)
  obtain ⟨zeroThreshold, hZeroThreshold⟩ := Filter.eventually_atTop.mp hZeroAbsorb
  refine ⟨max (max semisimpleThreshold zeroThreshold) 5, ?_⟩
  intro p hp _ t x hlarge
  have hpSemisimple : semisimpleThreshold ≤ p :=
    (le_max_left semisimpleThreshold zeroThreshold).trans
      ((le_max_left (max semisimpleThreshold zeroThreshold) 5).trans hp)
  have hpZero : zeroThreshold ≤ p :=
    (le_max_right semisimpleThreshold zeroThreshold).trans
      ((le_max_left (max semisimpleThreshold zeroThreshold) 5).trans hp)
  by_cases htParabolic : t ^ 2 = 4
  · exact exists_iterate_parabolicPoint_with_maximal_secondRotation
      p (by omega) t htParabolic x
  · have ht0 : t ≠ 0 := by
      intro htZero
      subst t
      have horderSmall := rotationOrder_zero_le_four p
      have hlargeLe : (p : ℝ) ^ ((1 : ℝ) / 2 + δ) ≤ 4 :=
        hlarge.trans (by exact_mod_cast horderSmall)
      exact (not_lt_of_ge hlargeLe) (hZeroThreshold p hpZero)
    exact hSemisimple p hpSemisimple t htParabolic ht0 x hlarge

end

end BGS.Markoff
