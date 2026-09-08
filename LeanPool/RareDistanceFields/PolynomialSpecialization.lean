/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.RareDistanceFields.DistancePattern
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-!
# Exact specialization of polynomial coordinate families

See the project entry module for the exact coordinate restrictions and source roles.
Rational polynomials evaluated at algebraically independent real parameters
admit a rational specialization preserving every equality and inequality of
distance labels (equality versus disequality, not numerical order). Thus both
rare-distance assertions follow with n <= 2^r for this coordinate regime.
Algebraic dependence of the parameters is not covered.
-/

namespace LeanPool.RareDistanceFields.PolynomialSpecialization

noncomputable section

variable {σ : Type*}

open Classical in
/-- A finite family of rational polynomials has an evaluation separating its members. -/
theorem exists_injective_eval (S : Finset (MvPolynomial σ ℚ)) :
    ∃ u : σ → ℚ, Set.InjOn (MvPolynomial.eval u) S := by
  classical
  let D := S.offDiag
  let P : MvPolynomial σ ℚ := ∏ e ∈ D, (e.1 - e.2)
  have hP : P ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro e he
    exact sub_ne_zero.mpr (Finset.mem_offDiag.mp he).2.2
  have he : ∃ u : σ → ℚ, (MvPolynomial.eval u) P ≠ 0 := by
    by_contra h
    push Not at h
    apply hP
    apply MvPolynomial.funext
    intro u
    simpa using h u
  obtain ⟨u, hu⟩ := he
  refine ⟨u, ?_⟩
  intro p hp q hq hpq
  by_contra hne
  have hmem : (p, q) ∈ D := Finset.mem_offDiag.mpr ⟨hp, hq, hne⟩
  have hh : ∀ e ∈ D, (MvPolynomial.eval u) (e.1 - e.2) ≠ 0 := by
    have hz := hu
    dsimp [P] at hz
    rw [map_prod] at hz
    exact Finset.prod_ne_zero_iff.mp hz
  apply hh (p, q) hmem
  simpa using sub_eq_zero.mpr hpq

variable {V : Type*} [Fintype V]

open Classical in
/-- Two rational multivariate polynomials for every configuration label. -/
abbrev Coordinates (σ V : Type*) := V → MvPolynomial σ ℚ × MvPolynomial σ ℚ

open Classical in
/-- The polynomial expression for the squared distance of two labeled points. -/
def sqPolynomial (P : Coordinates σ V) (a b : V) : MvPolynomial σ ℚ :=
  ((P a).1 - (P b).1) ^ 2 + ((P a).2 - (P b).2) ^ 2

open Classical in
/-- The complex point obtained by evaluating the coordinate polynomials over the reals. -/
def realPoint (P : Coordinates σ V) (t : σ → ℝ) (a : V) : ℂ :=
  ⟨(MvPolynomial.aeval t) (P a).1, (MvPolynomial.aeval t) (P a).2⟩

open Classical in
/-- The rational point obtained by evaluating the coordinate polynomials over the rationals. -/
def rationalPoint (P : Coordinates σ V) (u : σ → ℚ) (a : V) : ℚ × ℚ :=
  ⟨(MvPolynomial.eval u) (P a).1, (MvPolynomial.eval u) (P a).2⟩

omit [Fintype V] in
open Classical in
theorem real_dist_sq (P : Coordinates σ V) (t : σ → ℝ) (a b : V) :
    dist (realPoint P t a) (realPoint P t b) ^ 2 = (MvPolynomial.aeval t) (sqPolynomial P a b) := by
  rw [Complex.dist_eq, ← Complex.normSq_eq_norm_sq]
  simp [realPoint, sqPolynomial, Complex.normSq_apply, pow_two]

omit [Fintype V] in
open Classical in
theorem rational_sqDist (P : Coordinates σ V) (u : σ → ℚ) (a b : V) :
    RationalPlane.sqDist (rationalPoint P u a) (rationalPoint P u b) =
      (MvPolynomial.eval u) (sqPolynomial P a b) := by
  simp [RationalPlane.sqDist, rationalPoint, sqPolynomial]

omit [Fintype V] in
open Classical in
/-- A genuine rational realization of the original whole distance-equality pattern. -/
theorem exists_rational_pattern [Finite V] (P : Coordinates σ V) (t : σ → ℝ)
    (ht : AlgebraicIndependent ℚ t) :
    ∃ u : σ → ℚ, DistancePattern.SamePattern (rationalPoint P u) (realPoint P t) := by
  let := Fintype.ofFinite V
  let S := (Finset.univ : Finset (V × V)).image fun e => sqPolynomial P e.1 e.2
  obtain ⟨u, hu⟩ := exists_injective_eval S
  refine ⟨u, ?_⟩
  have hmem (a b : V) : sqPolynomial P a b ∈ S := Finset.mem_image.mpr ⟨(a, b), by simp, rfl⟩
  intro a b c d
  rw [rational_sqDist, rational_sqDist]
  constructor
  · intro h
    have he := hu (hmem a b) (hmem c d) h
    have hh := congrArg (MvPolynomial.aeval t) he
    rw [← real_dist_sq, ← real_dist_sq] at hh
    nlinarith [dist_nonneg (x := realPoint P t a) (y := realPoint P t b),
      dist_nonneg (x := realPoint P t c) (y := realPoint P t d)]
  · intro h
    have hh := congrArg (fun r : ℝ => r ^ 2) h
    rw [real_dist_sq, real_dist_sq] at hh
    exact congrArg (MvPolynomial.eval u) (ht hh)

open Classical in
theorem card_le_pow_rare (P : Coordinates σ V) (t : σ → ℝ)
    (ht : AlgebraicIndependent ℚ t) (hx : Function.Injective (realPoint P t)) :
    Fintype.card V ≤ 2 ^ (DistancePattern.rareDistances (realPoint P t)).card := by
  obtain ⟨u, hu⟩ := exists_rational_pattern P t ht
  exact DistancePattern.card_le_pow_rare (rationalPoint P u) (realPoint P t) hx hu

open Classical in
theorem two_rare_distances (P : Coordinates σ V) (t : σ → ℝ)
    (ht : AlgebraicIndependent ℚ t) (hx : Function.Injective (realPoint P t))
    (hn : 3 ≤ Fintype.card V) :
    ∃ d ∈ DistancePattern.rareDistances (realPoint P t),
      ∃ e ∈ DistancePattern.rareDistances (realPoint P t), d ≠ e := by
  obtain ⟨u, hu⟩ := exists_rational_pattern P t ht
  exact DistancePattern.two_rare_distances (rationalPoint P u) (realPoint P t) hx hu hn

open Classical in
theorem uniform_divergence (k : ℕ) : ∃ N : ℕ, ∀ {σ V : Type*} [Fintype V] (P : Coordinates σ V)
    (t : σ → ℝ),
    AlgebraicIndependent ℚ t → Function.Injective (realPoint P t) →
    N ≤ Fintype.card V → k ≤ (DistancePattern.rareDistances (realPoint P t)).card := by
  refine ⟨2 ^ k, ?_⟩
  intro σ V inst P t ht hx hn
  have h := card_le_pow_rare P t ht hx
  by_contra hr
  have hp : 2 ^ (DistancePattern.rareDistances (realPoint P t)).card < 2 ^ k :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  omega

end
end LeanPool.RareDistanceFields.PolynomialSpecialization
