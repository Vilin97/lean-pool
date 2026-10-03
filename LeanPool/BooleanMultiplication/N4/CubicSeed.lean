/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.QuarticExclusion

/-!
# The normalized seed is genuinely cubic

Quartic exclusion says that the rational quadratic parts of the two seed
factors are dependent.  Expanding the three possible dependencies in the
Boolean ANF algebra bounds the product by degree three.  The independent
high-part argument then makes its cubic projection nonzero.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

theorem DegreeLE.add {m d : Nat} {p q : ANF m}
    (hp : DegreeLE d p) (hq : DegreeLE d q) : DegreeLE d (p + q) := by
  intro s hs
  simp [hp s hs, hq s hs]

theorem representedLowFactor_degreeLE_two
    (a : F₂) (ell : LinearForm) (alpha : Fin 3 → F₂) :
    DegreeLE 2 (representedLowFactor a ell alpha) := by
  apply DegreeLE.add
  · exact (degreeLE_one_affineANF a ell).mono (by omega)
  · exact degreeLE_two_rationalANF alpha

private theorem dependent_low_product_degreeLE_three
    (a b : F₂) (ell m : LinearForm) (alpha beta : Fin 3 → F₂)
    (hprobe : quarticWedgeProbe (rationalTwo alpha) (rationalTwo beta) = 0) :
    DegreeLE 3
      (representedLowFactor a ell alpha *
        representedLowFactor b m beta) := by
  rcases rational_probe_zero_dependent alpha beta hprobe with
    halpha | hbeta | hab
  · subst alpha
    have hleft : representedLowFactor a ell 0 = affineANF a ell := by
      rw [representedLowFactor, rationalANF_zero, add_zero]
    rw [hleft]
    exact (degreeLE_one_affineANF a ell).mul
      (representedLowFactor_degreeLE_two b m beta)
  · subst beta
    have hright : representedLowFactor b m 0 = affineANF b m := by
      rw [representedLowFactor, rationalANF_zero, add_zero]
    rw [hright]
    exact (representedLowFactor_degreeLE_two a ell alpha).mul
      (degreeLE_one_affineANF b m)
  · subst beta
    let A := affineANF a ell
    let B := affineANF b m
    let Q := rationalANF alpha
    have hA : DegreeLE 1 A := degreeLE_one_affineANF a ell
    have hB : DegreeLE 1 B := degreeLE_one_affineANF b m
    have hQ : DegreeLE 2 Q := degreeLE_two_rationalANF alpha
    have hAB : DegreeLE 3 (A * B) :=
      (hA.mul hB).mono (by omega)
    have hAQ : DegreeLE 3 (A * Q) := hA.mul hQ
    have hQB : DegreeLE 3 (Q * B) := hQ.mul hB
    have hQ' : DegreeLE 3 Q := hQ.mono (by omega)
    have hexpand :
        representedLowFactor a ell alpha *
            representedLowFactor b m alpha =
          A * B + A * Q + Q * B + Q := by
      simp only [representedLowFactor, A, B, Q, add_mul, mul_add, anf_mul_self]
      ac_rfl
    rw [hexpand]
    exact ((hAB.add hAQ).add hQB).add hQ'

/-- Quartic exclusion upgrades the normalized seed to degree at most three. -/
theorem NormalizedEight.seed_degreeLE_three
    {C : Circuit 8 8} (h : NormalizedEight C) :
    DegreeLE 3 (C.gate 3) := by
  rcases h.seedFactorData with
    ⟨leftAffine, rightAffine, leftCoeff, rightCoeff,
      hleftAffine, hrightAffine, hleft, hright, hgate⟩
  rcases exists_affineANF_of_mem hleftAffine with
    ⟨leftConst, leftLinear, hleftRep⟩
  rcases exists_affineANF_of_mem hrightAffine with
    ⟨rightConst, rightLinear, hrightRep⟩
  have hprobe :
      quarticWedgeProbe (rationalTwo leftCoeff) (rationalTwo rightCoeff) = 0 := by
    have hz := h.seed_quarticProbe_eq_zero
    rw [hgate, hleftRep, hrightRep] at hz
    change quarticProbeANF
      ((affineANF leftConst leftLinear + rationalANF leftCoeff) *
        (affineANF rightConst rightLinear + rationalANF rightCoeff)) = 0 at hz
    rw [lowProduct_quarticProjection] at hz
    exact hz
  rw [hgate, hleftRep, hrightRep]
  exact dependent_low_product_degreeLE_three leftConst rightConst
    leftLinear rightLinear leftCoeff rightCoeff hprobe

/-- The cubic homogeneous projection of the normalized seed is nonzero. -/
theorem NormalizedEight.seed_cubicProjection_ne_zero
    {C : Circuit 8 8} (h : NormalizedEight C) :
    anfThreeProjection (C.gate 3) ≠ 0 := by
  intro hcubic
  rcases normalized_seed_high h with ⟨⟨s⟩, hsHigh, hsCoeff⟩
  change 3 ≤ s.card at hsHigh
  have hsLE := h.seed_degreeLE_three
  have hsCard : s.card = 3 := by
    have hsAtMost : s.card ≤ 3 := by
      by_contra hs
      have hz := hsLE ⟨s⟩ (by
        change 3 < s.card
        omega)
      exact hsCoeff hz
    omega
  rcases Finset.card_eq_three.mp hsCard with
    ⟨i, j, k, hij, hik, hjk, hs⟩
  subst s
  have hcoord := congrFun (congrFun (congrFun hcubic i) j) k
  simp only [anfThreeProjection, Fin.isValue, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.mem_insert, hij, Finset.mem_singleton, hik, or_self, not_false_eq_true,
    Finset.card_insert_of_notMem, hjk, Finset.card_singleton, Nat.reduceAdd, ↓reduceIte,
    Pi.zero_apply] at hcoord
  exact hsCoeff hcoord

/-- The exact manuscript predicate: the normalized seed has nonzero cubic
high part and no monomial above degree three. -/
theorem NormalizedEight.cubicSeedState
    {C : Circuit 8 8} (h : NormalizedEight C) : CubicSeedState C := by
  exact ⟨normalized_seed_high h, h.seed_degreeLE_three⟩

end

end N4
end UnrestrictedBooleanMul
