/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Opening.FiniteOrbit
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Transporting the characteristic-zero opening through an algebraic closure

The archimedean argument is proved over `ℂ`, while the paper formulates the opening over an
algebraic closure of `ℚ`.  This file records the missing functorial step.  A field embedding sends
normalized Markoff points coordinatewise and intertwines the five generators.  Closure induction
on `Gamma` then shows that a finite orbit over the source field has finite image orbit over `ℂ`.
-/

namespace BGS.Markoff

universe u v

/-- Apply a ring homomorphism coordinatewise to a normalized trace point. -/
def NormalizedPoint.map {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (x : NormalizedPoint R) : NormalizedPoint S :=
  ⟨f x.u1, f x.u2, f x.u3⟩

@[simp]
theorem NormalizedPoint.map_u1 {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (x : NormalizedPoint R) : (x.map f).u1 = f x.u1 :=
  rfl

@[simp]
theorem NormalizedPoint.map_u2 {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (x : NormalizedPoint R) : (x.map f).u2 = f x.u2 :=
  rfl

@[simp]
theorem NormalizedPoint.map_u3 {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (x : NormalizedPoint R) : (x.map f).u3 = f x.u3 :=
  rfl

@[simp]
theorem NormalizedPoint.map_origin {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) : (normalizedOrigin : NormalizedPoint R).map f = normalizedOrigin := by
  ext <;> simp [NormalizedPoint.map, normalizedOrigin]

@[simp]
theorem normalizedPolynomial_map {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (x : NormalizedPoint R) :
    normalizedPolynomial (x.map f) = f (normalizedPolynomial x) := by
  simp [normalizedPolynomial, NormalizedPoint.map]

/-- A ring homomorphism sends the normalized Markoff surface to the normalized Markoff surface. -/
def normalizedSurfaceMap {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (x : NormalizedMarkoffSurface R) : NormalizedMarkoffSurface S :=
  ⟨x.1.map f, by
    change normalizedPolynomial (x.1.map f) = 0
    rw [normalizedPolynomial_map, x.property, map_zero]⟩

@[simp]
theorem coe_normalizedSurfaceMap {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (x : NormalizedMarkoffSurface R) :
    (normalizedSurfaceMap f x).1 = x.1.map f :=
  rfl

theorem normalizedSurfaceMap_injective {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (normalizedSurfaceMap f) := by
  intro x y hxy
  apply Subtype.ext
  apply NormalizedPoint.ext
  · exact hf (congrArg NormalizedPoint.u1 (congrArg Subtype.val hxy))
  · exact hf (congrArg NormalizedPoint.u2 (congrArg Subtype.val hxy))
  · exact hf (congrArg NormalizedPoint.u3 (congrArg Subtype.val hxy))

private def normalizedVieta1Surface {R : Type u} [CommRing R]
    (x : NormalizedMarkoffSurface R) : NormalizedMarkoffSurface R :=
  ⟨normalizedVieta1 x.1, (isNormalizedMarkoff_vieta1 x.1).2 x.property⟩

private def normalizedVieta2Surface {R : Type u} [CommRing R]
    (x : NormalizedMarkoffSurface R) : NormalizedMarkoffSurface R :=
  ⟨normalizedVieta2 x.1, (isNormalizedMarkoff_vieta2 x.1).2 x.property⟩

private def normalizedVieta3Surface {R : Type u} [CommRing R]
    (x : NormalizedMarkoffSurface R) : NormalizedMarkoffSurface R :=
  ⟨normalizedVieta3 x.1, (isNormalizedMarkoff_vieta3 x.1).2 x.property⟩

private theorem gammaVieta1_smul_normalizedSurface
    {R : Type u} [CommRing R] [Invertible (3 : R)] (x : NormalizedMarkoffSurface R) :
    gammaVieta1 R • x = normalizedVieta1Surface x := by
  rw [normalizedGamma_smul_eq_perm, normalizedGammaPerm_apply]
  rw [show (gammaVieta1 R : Equiv.Perm (MarkoffSurface R))
      ((normalizationSurfaceEquiv R).symm x) =
        vieta1SurfacePerm R ((normalizationSurfaceEquiv R).symm x) by
    exact gammaVieta1_smul_surface ((normalizationSurfaceEquiv R).symm x)]
  apply Subtype.ext
  change toNormalized (vieta1 ((normalizationSurfaceEquiv R).symm x : Point R)) =
    normalizedVieta1 x
  rw [toNormalized_vieta1]
  rw [show toNormalized ((normalizationSurfaceEquiv R).symm x : Point R) = x by
    exact congrArg Subtype.val ((normalizationSurfaceEquiv R).apply_symm_apply x)]

private theorem gammaVieta2_smul_normalizedSurface
    {R : Type u} [CommRing R] [Invertible (3 : R)] (x : NormalizedMarkoffSurface R) :
    gammaVieta2 R • x = normalizedVieta2Surface x := by
  rw [normalizedGamma_smul_eq_perm, normalizedGammaPerm_apply]
  rw [show (gammaVieta2 R : Equiv.Perm (MarkoffSurface R))
      ((normalizationSurfaceEquiv R).symm x) =
        vieta2SurfacePerm R ((normalizationSurfaceEquiv R).symm x) by
    exact gammaVieta2_smul_surface ((normalizationSurfaceEquiv R).symm x)]
  apply Subtype.ext
  change toNormalized (vieta2 ((normalizationSurfaceEquiv R).symm x : Point R)) =
    normalizedVieta2 x
  rw [toNormalized_vieta2]
  rw [show toNormalized ((normalizationSurfaceEquiv R).symm x : Point R) = x by
    exact congrArg Subtype.val ((normalizationSurfaceEquiv R).apply_symm_apply x)]

private theorem gammaVieta3_smul_normalizedSurface
    {R : Type u} [CommRing R] [Invertible (3 : R)] (x : NormalizedMarkoffSurface R) :
    gammaVieta3 R • x = normalizedVieta3Surface x := by
  rw [normalizedGamma_smul_eq_perm, normalizedGammaPerm_apply]
  rw [show (gammaVieta3 R : Equiv.Perm (MarkoffSurface R))
      ((normalizationSurfaceEquiv R).symm x) =
        vieta3SurfacePerm R ((normalizationSurfaceEquiv R).symm x) by
    exact gammaVieta3_smul_surface ((normalizationSurfaceEquiv R).symm x)]
  apply Subtype.ext
  change toNormalized (vieta3 ((normalizationSurfaceEquiv R).symm x : Point R)) =
    normalizedVieta3 x
  rw [toNormalized_vieta3]
  rw [show toNormalized ((normalizationSurfaceEquiv R).symm x : Point R) = x by
    exact congrArg Subtype.val ((normalizationSurfaceEquiv R).apply_symm_apply x)]

private theorem normalizedSurfaceMap_vieta1 {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S) (x : NormalizedMarkoffSurface R) :
    normalizedSurfaceMap f (normalizedVieta1Surface x) =
      normalizedVieta1Surface (normalizedSurfaceMap f x) := by
  apply Subtype.ext
  ext <;> simp [normalizedSurfaceMap, NormalizedPoint.map, normalizedVieta1Surface,
    normalizedVieta1]

private theorem normalizedSurfaceMap_vieta2 {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S) (x : NormalizedMarkoffSurface R) :
    normalizedSurfaceMap f (normalizedVieta2Surface x) =
      normalizedVieta2Surface (normalizedSurfaceMap f x) := by
  apply Subtype.ext
  ext <;> simp [normalizedSurfaceMap, NormalizedPoint.map, normalizedVieta2Surface,
    normalizedVieta2]

private theorem normalizedSurfaceMap_vieta3 {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S) (x : NormalizedMarkoffSurface R) :
    normalizedSurfaceMap f (normalizedVieta3Surface x) =
      normalizedVieta3Surface (normalizedSurfaceMap f x) := by
  apply Subtype.ext
  ext <;> simp [normalizedSurfaceMap, NormalizedPoint.map, normalizedVieta3Surface,
    normalizedVieta3]

private theorem normalizedSurfaceMap_swap12 {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S) (x : NormalizedMarkoffSurface R) :
    normalizedSurfaceMap f (normalizedSwap12Surface x) =
      normalizedSwap12Surface (normalizedSurfaceMap f x) := by
  apply Subtype.ext
  ext <;> simp [normalizedSurfaceMap, NormalizedPoint.map, normalizedSwap12Surface,
    normalizedSwap12]

private theorem normalizedSurfaceMap_swap23 {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (f : R →+* S) (x : NormalizedMarkoffSurface R) :
    normalizedSurfaceMap f (normalizedSwap23Surface x) =
      normalizedSwap23Surface (normalizedSurfaceMap f x) := by
  apply Subtype.ext
  ext <;> simp [normalizedSurfaceMap, NormalizedPoint.map, normalizedSwap23Surface,
    normalizedSwap23]

/-- Every normalized `Gamma` word over the target field has a source-field word with the same
action after applying a field embedding. -/
theorem exists_normalizedGamma_lift_along_fieldHom
    {K : Type u} {L : Type v} [Field K] [Field L]
    [Invertible (3 : K)] [Invertible (3 : L)] (f : K →+* L) (g : Gamma L) :
    ∃ h : Gamma K, ∀ x : NormalizedMarkoffSurface K,
      normalizedSurfaceMap f (h • x) = g • normalizedSurfaceMap f x := by
  let motive : ∀ q : Equiv.Perm (MarkoffSurface L), q ∈ Subgroup.closure (gammaGenerators L) → Prop :=
    fun q hq ↦ ∃ h : Gamma K, ∀ x : NormalizedMarkoffSurface K,
      normalizedSurfaceMap f (h • x) =
        (⟨q, hq⟩ : Gamma L) • normalizedSurfaceMap f x
  apply Subgroup.closure_induction (p := motive)
  · intro q hq
    simp only [gammaGenerators, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · refine ⟨gammaVieta1 K, fun x ↦ ?_⟩
      change normalizedSurfaceMap f (gammaVieta1 K • x) =
        gammaVieta1 L • normalizedSurfaceMap f x
      rw [gammaVieta1_smul_normalizedSurface, gammaVieta1_smul_normalizedSurface]
      exact normalizedSurfaceMap_vieta1 f x
    · refine ⟨gammaVieta2 K, fun x ↦ ?_⟩
      change normalizedSurfaceMap f (gammaVieta2 K • x) =
        gammaVieta2 L • normalizedSurfaceMap f x
      rw [gammaVieta2_smul_normalizedSurface, gammaVieta2_smul_normalizedSurface]
      exact normalizedSurfaceMap_vieta2 f x
    · refine ⟨gammaVieta3 K, fun x ↦ ?_⟩
      change normalizedSurfaceMap f (gammaVieta3 K • x) =
        gammaVieta3 L • normalizedSurfaceMap f x
      rw [gammaVieta3_smul_normalizedSurface, gammaVieta3_smul_normalizedSurface]
      exact normalizedSurfaceMap_vieta3 f x
    · refine ⟨gammaSwap12 K, fun x ↦ ?_⟩
      change normalizedSurfaceMap f (gammaSwap12 K • x) =
        gammaSwap12 L • normalizedSurfaceMap f x
      rw [gammaSwap12_smul_normalizedSurface, gammaSwap12_smul_normalizedSurface]
      exact normalizedSurfaceMap_swap12 f x
    · refine ⟨gammaSwap23 K, fun x ↦ ?_⟩
      change normalizedSurfaceMap f (gammaSwap23 K • x) =
        gammaSwap23 L • normalizedSurfaceMap f x
      rw [gammaSwap23_smul_normalizedSurface, gammaSwap23_smul_normalizedSurface]
      exact normalizedSurfaceMap_swap23 f x
  · refine ⟨1, fun x ↦ ?_⟩
    simp
  · intro q r hq hr hqLift hrLift
    obtain ⟨qK, hqK⟩ := hqLift
    obtain ⟨rK, hrK⟩ := hrLift
    refine ⟨qK * rK, fun x ↦ ?_⟩
    change normalizedSurfaceMap f ((qK * rK) • x) =
      ((⟨q, hq⟩ : Gamma L) * (⟨r, hr⟩ : Gamma L)) • normalizedSurfaceMap f x
    rw [mul_smul, mul_smul, hqK, hrK]
  · intro q hq hqLift
    obtain ⟨qK, hqK⟩ := hqLift
    refine ⟨qK⁻¹, fun x ↦ ?_⟩
    have h := congrArg (fun y ↦ (⟨q, hq⟩ : Gamma L)⁻¹ • y) (hqK (qK⁻¹ • x))
    simpa [mul_smul] using h.symm

/-- The target-field orbit of the mapped point is contained in the image of the source orbit. -/
theorem normalizedGammaOrbit_map_subset
    {K : Type u} {L : Type v} [Field K] [Field L]
    [Invertible (3 : K)] [Invertible (3 : L)] (f : K →+* L)
    (x : NormalizedMarkoffSurface K) :
    normalizedGammaOrbit (normalizedSurfaceMap f x) ⊆
      normalizedSurfaceMap f '' normalizedGammaOrbit x := by
  intro y hy
  change y ∈ MulAction.orbit (Gamma L) (normalizedSurfaceMap f x) at hy
  rw [MulAction.mem_orbit_iff] at hy
  obtain ⟨g, rfl⟩ := hy
  obtain ⟨h, hh⟩ := exists_normalizedGamma_lift_along_fieldHom f g
  refine ⟨h • x, (MulAction.mem_orbit_iff).2 ⟨h, rfl⟩, hh x⟩

/-- A finite normalized orbit stays finite after applying a field embedding. -/
theorem finite_normalizedGammaOrbit_map
    {K : Type u} {L : Type v} [Field K] [Field L]
    [Invertible (3 : K)] [Invertible (3 : L)] (f : K →+* L)
    (x : NormalizedMarkoffSurface K) (hfinite : (normalizedGammaOrbit x).Finite) :
    (normalizedGammaOrbit (normalizedSurfaceMap f x)).Finite :=
  (hfinite.image (normalizedSurfaceMap f)).subset (normalizedGammaOrbit_map_subset f x)

/-- The complex opening theorem descends along any field embedding into `ℂ`. -/
theorem normalizedGammaOrbit_infinite_of_ne_origin_of_complexEmbedding
    {K : Type u} [Field K] [Invertible (3 : K)] (f : K →+* ℂ)
    (x : NormalizedMarkoffSurface K) (hx : x.1 ≠ normalizedOrigin) :
    (normalizedGammaOrbit x).Infinite := by
  intro hfinite
  have hmapNe : (normalizedSurfaceMap f x).1 ≠ normalizedOrigin := by
    intro hzero
    apply hx
    apply NormalizedPoint.ext
    · apply f.injective
      simpa [normalizedSurfaceMap, NormalizedPoint.map, normalizedOrigin] using
        congrArg NormalizedPoint.u1 hzero
    · apply f.injective
      simpa [normalizedSurfaceMap, NormalizedPoint.map, normalizedOrigin] using
        congrArg NormalizedPoint.u2 hzero
    · apply f.injective
      simpa [normalizedSurfaceMap, NormalizedPoint.map, normalizedOrigin] using
        congrArg NormalizedPoint.u3 hzero
  exact complex_normalizedGammaOrbit_infinite_of_ne_origin (normalizedSurfaceMap f x) hmapNe
    (finite_normalizedGammaOrbit_map f x hfinite)

/-- A chosen embedding of the canonical algebraic closure of `ℚ` into `ℂ`. -/
noncomputable def algebraicClosureRatComplexEmbedding : AlgebraicClosure ℚ →+* ℂ :=
  letI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.isAlgebraic ℚ
  (IsAlgClosed.lift (R := ℚ) (S := AlgebraicClosure ℚ) (M := ℂ)).toRingHom

/-- The published characteristic-zero opening: every nonzero normalized Markoff point over the
canonical algebraic closure of `ℚ` has infinite `Gamma`-orbit. -/
theorem algebraicClosureRat_normalizedGammaOrbit_infinite_of_ne_origin
    (x : NormalizedMarkoffSurface (AlgebraicClosure ℚ))
    (hx : x.1 ≠ normalizedOrigin) :
    (normalizedGammaOrbit x).Infinite :=
  normalizedGammaOrbit_infinite_of_ne_origin_of_complexEmbedding
    algebraicClosureRatComplexEmbedding x hx

end BGS.Markoff
