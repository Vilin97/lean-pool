/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.CorvajaZannierGeometry

/-!
# The weighted trace curve is not a subtorus translate

This module proves the non-specialness condition needed by the
Corvaja--Zannier torsion-point bound.  The proof uses the two deck involutions
of the weighted trace curve and keeps all degenerate parameters explicit.
-/

@[expose] public section

namespace BGS.Markoff

section CharacterPowers

variable {F : Type*} [Field F] [Infinite F]

/-- No fixed nonzero integer power is identically one on the units of an
infinite field. -/
private theorem exists_unit_zpow_ne_one (n : ℤ) (hn : n ≠ 0) :
    ∃ u : Fˣ, u ^ n ≠ 1 := by
  by_contra h
  push Not at h
  let m := n.natAbs
  let q : Polynomial F := Polynomial.X ^ m - 1
  have hm : m ≠ 0 := Int.natAbs_ne_zero.mpr hn
  have hqDegree : q.natDegree = m := by
    simpa [q] using (Polynomial.natDegree_X_pow_sub_C (R := F) (n := m) (r := 1))
  have hq : q ≠ 0 := by
    intro hzero
    have : q.natDegree = 0 := by simp [hzero]
    omega
  have hXq : Polynomial.X * q ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hq
  apply hXq
  apply Polynomial.zero_of_eval_zero
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · let u : Fˣ := Units.mk0 x hx
    have hu : u ^ m = 1 := pow_natAbs_eq_one.mpr (h u)
    have hxpow : x ^ m = 1 := by
      have := congrArg (fun v : Fˣ ↦ (v : F)) hu
      simpa [u] using this
    simp [q, hxpow]

end CharacterPowers

section CurveProjections

variable {F : Type*} [Field F] [IsAlgClosed F]

/-- Every right torus coordinate occurs on a nondegenerate weighted trace
curve.  The other coordinate is obtained from its quadratic equation. -/
private theorem exists_weightedTraceCurve_point_over_right
    (alpha beta : F) (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) (k : Fˣ) :
    ∃ h : Fˣ,
      weightedSplitTorusTrace alpha beta h = splitTorusTrace k := by
  let trace := splitTorusTrace k
  let q : Polynomial F :=
    Polynomial.C alpha * Polynomial.X ^ 2 -
      Polynomial.C trace * Polynomial.X + Polynomial.C beta
  have hqDegree : q.natDegree = 2 := by
    rw [show q = Polynomial.C alpha * Polynomial.X ^ 2 +
        Polynomial.C (-trace) * Polynomial.X + Polynomial.C beta by
      simp only [q, Polynomial.C_neg]
      ring]
    exact Polynomial.natDegree_quadratic halpha
  have hq : q ≠ 0 := by
    intro hzero
    have : q.natDegree = 0 := by simp [hzero]
    omega
  have hqDegreeBot : q.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hq, hqDegree]
    norm_num
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root q hqDegreeBot
  have hxzero : x ≠ 0 := by
    intro hzero
    subst x
    simp [Polynomial.IsRoot.def, q, hbeta] at hx
  refine ⟨Units.mk0 x hxzero, ?_⟩
  change alpha * x + beta * x⁻¹ = trace
  have hxeq : alpha * x ^ 2 - trace * x + beta = 0 := by
    simpa [Polynomial.IsRoot.def, q] using hx
  field_simp [hxzero]
  linear_combination hxeq

/-- Every left torus coordinate occurs on the weighted trace curve. -/
private theorem exists_weightedTraceCurve_point_over_left
    (alpha beta : F) (h : Fˣ) :
    ∃ k : Fˣ,
      weightedSplitTorusTrace alpha beta h = splitTorusTrace k := by
  let trace := weightedSplitTorusTrace alpha beta h
  let q : Polynomial F :=
    Polynomial.X ^ 2 - Polynomial.C trace * Polynomial.X + 1
  have hqDegree : q.natDegree = 2 := by
    rw [show q = Polynomial.C (1 : F) * Polynomial.X ^ 2 +
        Polynomial.C (-trace) * Polynomial.X + Polynomial.C 1 by
      simp only [q, Polynomial.C_neg, Polynomial.C_1]
      ring]
    exact Polynomial.natDegree_quadratic one_ne_zero
  have hq : q ≠ 0 := by
    intro hzero
    have : q.natDegree = 0 := by simp [hzero]
    omega
  have hqDegreeBot : q.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hq, hqDegree]
    norm_num
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root q hqDegreeBot
  have hxzero : x ≠ 0 := by
    intro hzero
    subst x
    simp [Polynomial.IsRoot.def, q] at hx
  refine ⟨Units.mk0 x hxzero, ?_⟩
  change trace = x + x⁻¹
  have hxeq : x ^ 2 - trace * x + 1 = 0 := by
    simpa [Polynomial.IsRoot.def, q] using hx
  field_simp [hxzero]
  linear_combination -hxeq

end CurveProjections

section DeckInvolutions

variable {F : Type*} [Field F]

private theorem splitTorusTrace_inv (k : Fˣ) :
    splitTorusTrace k⁻¹ = splitTorusTrace k := by
  simp only [splitTorusTrace, Units.val_inv_eq_inv_val, inv_inv]
  exact add_comm _ _

/-- The second deck involution exchanges the two roots of the quadratic in
the weighted coordinate. -/
private theorem weightedSplitTorusTrace_deck_involution
    (alpha beta : F) (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) (h : Fˣ) :
    let q : Fˣ := Units.mk0 (beta / alpha) (div_ne_zero hbeta halpha)
    weightedSplitTorusTrace alpha beta (q * h⁻¹) =
      weightedSplitTorusTrace alpha beta h := by
  dsimp
  simp only [weightedSplitTorusTrace, Units.val_mul, Units.val_inv_eq_inv_val,
    Units.val_mk0, div_eq_mul_inv]
  field_simp [halpha, hbeta, Units.ne_zero h]
  ring

end DeckInvolutions

section NonSubtorus

variable {K : Type*} [Field K]

/-- If both weights are nonzero, the complete weighted trace curve is not a
character fiber in the two-dimensional torus.  No characteristic restriction
is needed.

This deliberately does not assume `alpha * beta ≠ 1`.  When the product is
one the curve is reducible into two subtorus translates, but no single
character is constant on their union.  Thus this proposition is the correct
non-specialness condition only when paired with the separate absolute
irreducibility hypothesis, exactly as it is in
`WeightedTraceCurveIsCorvajaZannierAdmissible`. -/
theorem weightedTraceCurve_notSubtorusTranslate_of_weights_ne_zero
    (alpha beta : K) (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) :
    WeightedTraceCurveNotSubtorusTranslate alpha beta := by
  let alphaL : AlgebraicClosure K := algebraMap K (AlgebraicClosure K) alpha
  let betaL : AlgebraicClosure K := algebraMap K (AlgebraicClosure K) beta
  have halphaL : alphaL ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap K (AlgebraicClosure K))
      (algebraMap K (AlgebraicClosure K)).injective).mpr halpha
  have hbetaL : betaL ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap K (AlgebraicClosure K))
      (algebraMap K (AlgebraicClosure K)).injective).mpr hbeta
  intro a b hab c
  by_contra hvaries
  push Not at hvaries
  have haUniversal : ∀ k : (AlgebraicClosure K)ˣ, k ^ (2 * a) = 1 := by
    intro k
    obtain ⟨h, hcurve⟩ :=
      exists_weightedTraceCurve_point_over_right alphaL betaL halphaL hbetaL k
    have hcurveInv :
        weightedSplitTorusTrace alphaL betaL h = splitTorusTrace k⁻¹ := by
      rw [splitTorusTrace_inv]
      exact hcurve
    have hvalue := hvaries k h hcurve
    have hvalueInv := hvaries k⁻¹ h hcurveInv
    have hpower : k ^ a = (k⁻¹) ^ a := by
      exact mul_right_cancel (hvalue.trans hvalueInv.symm)
    have hpowerInv : k ^ a = (k ^ a)⁻¹ := by
      simpa only [inv_zpow] using hpower
    have hsquare : k ^ a * k ^ a = 1 := eq_inv_iff_mul_eq_one.mp hpowerInv
    calc
      k ^ (2 * a) = k ^ (a + a) := by (congr 1; ring)
      _ = k ^ a * k ^ a := zpow_add k a a
      _ = 1 := hsquare
  have ha : a = 0 := by
    by_contra ha
    have htwoa : 2 * a ≠ 0 := mul_ne_zero (by norm_num) ha
    obtain ⟨k, hk⟩ := exists_unit_zpow_ne_one (F := AlgebraicClosure K) (2 * a) htwoa
    exact hk (haUniversal k)
  have hbUniversal : ∀ h : (AlgebraicClosure K)ˣ, h ^ (2 * b) = 1 := by
    let q : (AlgebraicClosure K)ˣ :=
      Units.mk0 (betaL / alphaL) (div_ne_zero hbetaL halphaL)
    have hconstant : ∀ h : (AlgebraicClosure K)ˣ, h ^ (2 * b) = q ^ b := by
      intro h
      obtain ⟨k, hcurve⟩ := exists_weightedTraceCurve_point_over_left alphaL betaL h
      have hcurveDeck :
          weightedSplitTorusTrace alphaL betaL (q * h⁻¹) = splitTorusTrace k := by
        rw [weightedSplitTorusTrace_deck_involution alphaL betaL halphaL hbetaL]
        exact hcurve
      have hvalue := hvaries k h hcurve
      have hvalueDeck := hvaries k (q * h⁻¹) hcurveDeck
      have hpower : h ^ b = (q * h⁻¹) ^ b := by
        exact mul_left_cancel (hvalue.trans hvalueDeck.symm)
      have hpowerExpanded : h ^ b = q ^ b * (h ^ b)⁻¹ := by
        simpa only [mul_zpow, inv_zpow] using hpower
      have hsquare : h ^ b * h ^ b = q ^ b := by
        calc
          h ^ b * h ^ b = (q ^ b * (h ^ b)⁻¹) * h ^ b := by
            exact congrArg (fun z ↦ z * h ^ b) hpowerExpanded
          _ = q ^ b := by simp
      calc
        h ^ (2 * b) = h ^ (b + b) := by (congr 1; ring)
        _ = h ^ b * h ^ b := zpow_add h b b
        _ = q ^ b := hsquare
    have hq : q ^ b = 1 := by
      have hone := hconstant (1 : (AlgebraicClosure K)ˣ)
      simpa using hone.symm
    intro h
    exact (hconstant h).trans hq
  have hb : b = 0 := by
    by_contra hb
    have htwob : 2 * b ≠ 0 := mul_ne_zero (by norm_num) hb
    obtain ⟨h, hh⟩ := exists_unit_zpow_ne_one
      (F := AlgebraicClosure K) (2 * b) htwob
    exact hh (hbUniversal h)
  exact hab.elim (fun hne ↦ hne ha) (fun hne ↦ hne hb)

/-- Once absolute irreducibility is supplied, all remaining geometric
admissibility conditions are discharged by the explicit parameter
hypotheses. -/
theorem weightedTraceCurve_isCorvajaZannierAdmissible_of_absoluteIrreducible
    (alpha beta : K) (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hnondegenerate : alpha * beta ≠ 1)
    (hirreducible : WeightedTraceCurveAbsolutelyIrreducible alpha beta) :
    WeightedTraceCurveIsCorvajaZannierAdmissible alpha beta := by
  exact ⟨halpha, hbeta, hnondegenerate, hirreducible,
    weightedTraceCurve_notSubtorusTranslate_of_weights_ne_zero alpha beta halpha hbeta⟩

end NonSubtorus

end BGS.Markoff
