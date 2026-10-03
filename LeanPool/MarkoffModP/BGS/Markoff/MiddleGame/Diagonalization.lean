/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.OrderEscape

/-!
# Diagonalizing an arbitrary nonzero nonparabolic Markoff fiber

This module closes the algebraic interface required by the weighted middle-game order escape.
Every normalized Markoff point whose fixed coordinate is nonzero and nonparabolic becomes an
explicit `splitFiberPoint w s` after scalar extension to the canonical quadratic field.

The trace-zero fiber is excluded explicitly.  Its conic is singular and the existing
`splitFiberEquiv` / `quadraticNormFiberEquiv` APIs correctly require nonzero trace; no false torus
parametrization is introduced for that branch.
-/

@[expose] public section

namespace BGS.Markoff

/-- The singular trace-zero rotation has order at most four.  This keeps the trace-zero fiber
outside every middle-game range whose current order is greater than four, without pretending
that its singular conic is a torus. -/
theorem rotationOrder_zero_le_four
    (p : ℕ) [Fact p.Prime] : rotationOrder (0 : ZMod p) ≤ 4 := by
  rw [rotationOrder]
  apply orderOf_le_of_pow_eq_one (by norm_num)
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change (rho (0 : ZMod p) ^ 4) i j = (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rhoSL, rho, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Scalar extension carries the explicit split fiber parametrization to the corresponding
parametrization over the quadratic field. -/
theorem algebraMapNormalizedPoint_splitFiberPoint
    (p : ℕ) [Fact p.Prime] (w s : (ZMod p)ˣ) :
    algebraMapNormalizedPoint p (splitFiberPoint w s) =
      splitFiberPoint
        (Units.map (algebraMap (ZMod p) (quadraticFiniteField p)).toMonoidHom w)
        (Units.map (algebraMap (ZMod p) (quadraticFiniteField p)).toMonoidHom s) := by
  let phi := algebraMap (ZMod p) (quadraticFiniteField p)
  let mapUnit : (ZMod p)ˣ →* (quadraticFiniteField p)ˣ := Units.map phi.toMonoidHom
  have htrace : phi (splitTorusTrace w) = splitTorusTrace (mapUnit w) := by
    rw [splitTorusTrace, splitTorusTrace, map_add]
    rfl
  have hproduct : phi (splitFiberProduct w) = splitFiberProduct (mapUnit w) := by
    rw [splitFiberProduct, splitFiberProduct, map_div₀, map_sub, map_pow, map_ofNat, htrace]
  ext
  · exact htrace
  · change phi ((s : ZMod p) + splitFiberProduct w * ((s⁻¹ : (ZMod p)ˣ) : ZMod p)) = _
    rw [map_add, map_mul, hproduct]
    rfl
  · change phi ((s : ZMod p) * (w : ZMod p) +
        splitFiberProduct w * ((s⁻¹ : (ZMod p)ˣ) : ZMod p) *
          ((w⁻¹ : (ZMod p)ˣ) : ZMod p)) = _
    rw [map_add, map_mul, map_mul, map_mul, hproduct]
    rfl

/-- Every normalized nonzero nonparabolic fiber point admits the diagonalized scalar-extension
presentation consumed by `exists_iterate_with_larger_secondRotationOrder_of_diagonalizedFiber`. -/
theorem exists_diagonalizedFiberPoint_of_nonzero_nonparabolic
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (x : NormalizedPoint (ZMod p)) (hx : IsNormalizedMarkoff x)
    (hnonzero : x.u1 ≠ 0) (hnonparabolic : x.u1 ^ 2 ≠ 4) :
    ∃ w s : (quadraticFiniteField p)ˣ,
      (w : quadraticFiniteField p) ^ 2 ≠ 1 ∧
        algebraMapNormalizedPoint p x = splitFiberPoint w s := by
  rcases exists_split_or_quadraticNormOneTrace p hpTwo x.u1 hnonparabolic with
    ⟨w, htrace, hw⟩ | ⟨w, htrace, hw⟩
  · let xp : ↑(normalizedFiber1 (splitTorusTrace w)) :=
      ⟨x, hx, htrace.symm⟩
    have htraceNonzero : splitTorusTrace w ≠ 0 := by
      rw [htrace]
      exact hnonzero
    let s : (ZMod p)ˣ := (splitFiberEquiv w hw htraceNonzero).symm xp
    have hsPoint : splitFiberPoint w s = x :=
      congrArg Subtype.val ((splitFiberEquiv w hw htraceNonzero).apply_symm_apply xp)
    let embedding : (ZMod p)ˣ →* (quadraticFiniteField p)ˣ :=
      Units.map (algebraMap (ZMod p) (quadraticFiniteField p)).toMonoidHom
    let extensionW : (quadraticFiniteField p)ˣ := embedding w
    let extensionS : (quadraticFiniteField p)ˣ := embedding s
    have hExtensionW : (extensionW : quadraticFiniteField p) ^ 2 ≠ 1 := by
      intro hpower
      apply hw
      apply (algebraMap (ZMod p) (quadraticFiniteField p)).injective
      rw [map_pow, map_one]
      exact hpower
    refine ⟨extensionW, extensionS, hExtensionW, ?_⟩
    calc
      algebraMapNormalizedPoint p x =
          algebraMapNormalizedPoint p (splitFiberPoint w s) := by rw [hsPoint]
      _ = splitFiberPoint extensionW extensionS := by
        exact algebraMapNormalizedPoint_splitFiberPoint p w s
  · let xp : ↑(normalizedFiber1 x.u1) := ⟨x, hx, rfl⟩
    let s := (quadraticNormFiberEquiv p x.u1 hnonparabolic hnonzero w htrace hw).symm xp
    have hsPoint : quadraticNormFiberPoint p x.u1 hnonparabolic hnonzero w s = x :=
      congrArg Subtype.val
        ((quadraticNormFiberEquiv p x.u1 hnonparabolic hnonzero w htrace hw).apply_symm_apply xp)
    refine ⟨(w : (quadraticFiniteField p)ˣ), s.1, hw, ?_⟩
    calc
      algebraMapNormalizedPoint p x =
          algebraMapNormalizedPoint p
            (quadraticNormFiberPoint p x.u1 hnonparabolic hnonzero w s) := by rw [hsPoint]
      _ = splitFiberPoint (w : (quadraticFiniteField p)ˣ) s.1 :=
        algebraMap_quadraticNormFiberPoint p x.u1 hnonparabolic hnonzero w htrace s

/-- Complete nonzero nonparabolic middle-game order escape.  All algebraic and combinatorial
wiring is discharged internally.  The only deep hypothesis is the weighted Corvaja--Zannier
estimate, stated uniformly for whichever split or norm-one diagonalization the point has. -/
theorem exists_iterate_with_larger_secondRotationOrder_of_nonzero_nonparabolic
    (p : ℕ) [Fact p.Prime] [Fintype (quadraticFiniteField p)] (hpTwo : p ≠ 2)
    (delta : ℝ) (hdelta : delta ≤ (1 : ℝ) / 2)
    (x : NormalizedPoint (ZMod p)) (hx : IsNormalizedMarkoff x)
    (hnonzero : x.u1 ≠ 0) (hnonparabolic : x.u1 ^ 2 ≠ 4)
    (hbelowEndgame :
      (rotationOrder x.u1 : ℝ) < (p : ℝ) ^ ((1 : ℝ) / 2 + delta))
    (hcube :
      (corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card)) ^ 3 <
        rotationOrder x.u1)
    (hlinear :
      corvajaZannierCorollaryTwoSafeCoefficient *
        ((p - 1).divisors.card + (p + 1).divisors.card) *
          rotationOrder x.u1 < p)
    (hCZ :
      ∀ (w s : (quadraticFiniteField p)ˣ),
        (w : quadraticFiniteField p) ^ 2 ≠ 1 →
        algebraMapNormalizedPoint p x = splitFiberPoint w s →
        (s : quadraticFiniteField p) *
            (splitFiberProduct w * ((s⁻¹ : (quadraticFiniteField p)ˣ) :
              quadraticFiniteField p)) ≠ 1 →
        ∀ d ∈ middleGameCandidateOrders p (rotationOrder x.u1),
          ((weightedTraceEquationSolutions
            (s : quadraticFiniteField p)
            (splitFiberProduct w * ((s⁻¹ : (quadraticFiniteField p)ˣ) :
              quadraticFiniteField p))
            (Subgroup.zpowers w) (middleGameRightSubgroup p d)).card : ℝ) ≤
            corvajaZannierTraceUpperBound p (rotationOrder x.u1)
              (Nat.card (middleGameRightSubgroup p d))) :
    ∃ n : ℕ,
      rotationOrder x.u1 < rotationOrder ((normalizedRotate1^[n]) x).u2 := by
  obtain ⟨w, s, hw, hpoint⟩ :=
    exists_diagonalizedFiberPoint_of_nonzero_nonparabolic
      p hpTwo x hx hnonzero hnonparabolic
  exact exists_iterate_with_larger_secondRotationOrder_of_diagonalizedFiber
    p hpTwo delta hdelta x w s hw hpoint hbelowEndgame hcube hlinear
      (hCZ w s hw hpoint)

end BGS.Markoff
