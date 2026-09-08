/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.RareDistanceFields.PolynomialSpecialization
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Planar sets over purely transcendental fields

See the project entry module for the exact coordinate restrictions and source roles.
For any real embedding of the fraction field of Q[variables], all finite planar
configurations admit rational realizations of exactly the same distance-equality
pattern. Common denominators are cleared before polynomial specialization.
This proves both rare-distance assertions in this regime. Nontrivial algebraic
extensions of the rational function field are not included.
-/

namespace LeanPool.RareDistanceFields.PureTranscendental

noncomputable section

open Classical in
/-- The rational function field in the specified family of variables over the rationals. -/
abbrev Functions (σ : Type*) := FractionRing (MvPolynomial σ ℚ)

variable {σ : Type*}

open Classical in
/-- Algebraically independent parameters supply the required real field embedding. -/
def embedding (t : σ → ℝ) (ht : AlgebraicIndependent ℚ t) : Functions σ →ₐ[ℚ] ℝ :=
  (IsFractionRing.lift
    (g := (MvPolynomial.aeval t : MvPolynomial σ ℚ →ₐ[ℚ] ℝ).toRingHom) ht).toRatAlgHom

open Classical in
theorem embedding_variables (t : σ → ℝ) (ht : AlgebraicIndependent ℚ t) (i : σ) :
    embedding t ht (algebraMap (MvPolynomial σ ℚ) (Functions σ) (MvPolynomial.X i)) = t i := by
  change (IsFractionRing.lift
    (g := (MvPolynomial.aeval t : MvPolynomial σ ℚ →ₐ[ℚ] ℝ).toRingHom) ht)
    (algebraMap (MvPolynomial σ ℚ) (Functions σ) (MvPolynomial.X i)) = t i
  exact (IsFractionRing.lift_algebraMap
    (g := (MvPolynomial.aeval t : MvPolynomial σ ℚ →ₐ[ℚ] ℝ).toRingHom)
    ht (MvPolynomial.X i)).trans (MvPolynomial.aeval_X t i)

open Classical in
theorem real_embedding_exists : Nonempty (Functions Empty →ₐ[ℚ] ℝ) :=
  ⟨embedding Empty.elim algebraicIndependent_empty_type⟩

variable {V : Type*} [Fintype V]

open Classical in
/-- The planar point obtained from a pair of rational functions under a real embedding. -/
def point (f : Functions σ →ₐ[ℚ] ℝ) (x : V → Functions σ × Functions σ) (a : V) : ℂ :=
  ⟨f (x a).1, f (x a).2⟩

omit [Fintype V] in
open Classical in
theorem exists_rational_pattern [Finite V] (f : Functions σ →ₐ[ℚ] ℝ)
    (x : V → Functions σ × Functions σ) :
    ∃ y : V → ℚ × ℚ, DistancePattern.SamePattern y (point f x) := by
  let := Fintype.ofFinite V
  classical
  let R := MvPolynomial σ ℚ
  let K := Functions σ
  let g : R →ₐ[ℚ] ℝ := (f.toRingHom.comp (algebraMap R K)).toRatAlgHom
  have hg : Function.Injective g :=
    f.injective.comp (IsFractionRing.injective R K)
  let t : σ → ℝ := fun i => g (MvPolynomial.X i)
  have hgt : g = MvPolynomial.aeval t := MvPolynomial.aeval_unique g
  have ht : AlgebraicIndependent ℚ t := by
    change Function.Injective (MvPolynomial.aeval t)
    rwa [← hgt]
  let coordinates : V × Bool → K := fun e => if e.2 then (x e.1).1 else (x e.1).2
  obtain ⟨B, hB⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) coordinates
  have hc (a : V) : ∃ p q : R,
      algebraMap R K p = algebraMap R K (B : R) * (x a).1 ∧
      algebraMap R K q = algebraMap R K (B : R) * (x a).2 := by
    obtain ⟨p, hp⟩ := hB (a, true)
    obtain ⟨q, hq⟩ := hB (a, false)
    exact ⟨p, q, by simpa [coordinates, Algebra.smul_def] using hp,
      by simpa [coordinates, Algebra.smul_def] using hq⟩
  choose p q hp hq using hc
  let P : PolynomialSpecialization.Coordinates σ V := fun a => (p a, q a)
  let d : ℝ := g B
  have hBne : (B : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp B.property
  have hd : d ≠ 0 := by
    intro hz
    apply hBne
    apply hg
    simpa [d] using hz
  have hpoint (a : V) : PolynomialSpecialization.realPoint P t a =
      (d : ℂ) * point f x a := by
    have hpa := congrArg f (hp a)
    have hqa := congrArg f (hq a)
    have hpa' : g (p a) = d * f (x a).1 := by simpa [g, d] using hpa
    have hqa' : g (q a) = d * f (x a).2 := by simpa [g, d] using hqa
    apply Complex.ext
    · simpa [PolynomialSpecialization.realPoint, P, point, ← hgt] using hpa'
    · simpa [PolynomialSpecialization.realPoint, P, point, ← hgt] using hqa'
  have hscale (a b : V) :
      dist (PolynomialSpecialization.realPoint P t a)
        (PolynomialSpecialization.realPoint P t b) =
        |d| * dist (point f x a) (point f x b) := by
    rw [hpoint, hpoint]
    simp [Complex.dist_eq, ← mul_sub, Complex.norm_real]
  obtain ⟨u, hu⟩ := PolynomialSpecialization.exists_rational_pattern P t ht
  refine ⟨PolynomialSpecialization.rationalPoint P u, ?_⟩
  intro a b c e
  rw [hu a b c e, hscale, hscale]
  exact ⟨mul_left_cancel₀ (abs_ne_zero.mpr hd), congrArg (fun z : ℝ => |d| * z)⟩

open Classical in
theorem card_le_pow_rare (f : Functions σ →ₐ[ℚ] ℝ)
    (x : V → Functions σ × Functions σ) (hx : Function.Injective (point f x)) :
    Fintype.card V ≤ 2 ^ (DistancePattern.rareDistances (point f x)).card := by
  obtain ⟨y, hy⟩ := exists_rational_pattern f x
  exact DistancePattern.card_le_pow_rare y (point f x) hx hy

open Classical in
theorem two_rare_distances (f : Functions σ →ₐ[ℚ] ℝ)
    (x : V → Functions σ × Functions σ) (hx : Function.Injective (point f x))
    (hn : 3 ≤ Fintype.card V) :
    ∃ d ∈ DistancePattern.rareDistances (point f x),
      ∃ e ∈ DistancePattern.rareDistances (point f x), d ≠ e := by
  obtain ⟨y, hy⟩ := exists_rational_pattern f x
  exact DistancePattern.two_rare_distances y (point f x) hx hy hn

open Classical in
theorem uniform_divergence (k : ℕ) : ∃ N : ℕ, ∀ {σ V : Type*} [Fintype V]
    (f : Functions σ →ₐ[ℚ] ℝ) (x : V → Functions σ × Functions σ),
    Function.Injective (point f x) → N ≤ Fintype.card V →
      k ≤ (DistancePattern.rareDistances (point f x)).card := by
  refine ⟨2 ^ k, ?_⟩
  intro σ V inst f x hx hn
  have h := card_le_pow_rare f x hx
  by_contra hr
  have hp : 2 ^ (DistancePattern.rareDistances (point f x)).card < 2 ^ k :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  omega

end
end LeanPool.RareDistanceFields.PureTranscendental
