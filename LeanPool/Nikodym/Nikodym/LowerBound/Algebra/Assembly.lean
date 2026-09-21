/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.DegreeUpper
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Degree
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.ProperCut
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Transfer

/-!
# The algebraic interface, unconditionally

This file assembles the commutative-algebra backend (`docs/algebra_backend_design.md`) into the
structure `Nikodym.LowerBound.AlgebraInterface K d` for every field `K` and every `d`:

* over an infinite field, the two-sided Hilbert bounds of A08-core (`exists_hilbert_bounds`)
  feed the polynomial arguments of A04′ (`Algebra/Degree.lean`), giving the degree facts
  `degreeFacts` and the uniform Hilbert upper bound `hilbert_le_degree_mul_choose_of_infinite`
  (A08);
* the degree facts feed the affine proper cut B03 (`proper_cut_of_infinite`);
* the base-change assembly TR7 (`algebraInterface_of_infinite`) transports A08, B03 and J02 from
  `RatFunc K` back to `K`.

The main result is `Nikodym.LowerBound.algebraInterface K d`.
-/

namespace Nikodym.LowerBound

variable {K : Type*} [Field K] {d : ℕ}

/-- The lower bound of `exists_hilbert_bounds` (a sum over the `i` with `e i ≤ t`) in the eventual
form used by `Algebra/Degree.lean`: for `t ≥ ∑ i, e i` every `i` qualifies. -/
theorem eventually_sum_choose_le_hilbert {I : Ideal (MvPolynomial (Fin d) K)} {Δ : ℕ}
    {e : Fin Δ → ℕ}
    (hlow : ∀ t, ∑ i ∈ Finset.univ.filter (fun i ↦ e i ≤ t),
      (t - e i + quotDim I).choose (quotDim I) ≤ hilbert I t) :
    ∀ᶠ t : ℕ in Filter.atTop,
      ∑ i, (t - e i + quotDim I).choose (quotDim I) ≤ hilbert I t := by
  filter_upwards [Filter.eventually_ge_atTop (∑ i, e i)] with t ht
  have h : Finset.univ.filter (fun i ↦ e i ≤ t) = (Finset.univ : Finset (Fin Δ)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans ht
  simpa [h] using hlow t

section Infinite

variable [Infinite K]

/-- Blueprint A04′ over an infinite field: `natDegree (affineHilbertPoly I) = quotDim I` for a
prime `I`. -/
theorem natDegree_affineHilbertPoly_of_infinite (I : Ideal (MvPolynomial (Fin d) K))
    [I.IsPrime] : (affineHilbertPoly I).natDegree = quotDim I := by
  obtain ⟨Δ, e, hΔ, hlow, hup⟩ := exists_hilbert_bounds I
  exact natDegree_affineHilbertPoly_of_eventually_bounds hΔ (eventually_sum_choose_le_hilbert hlow)
    (Filter.Eventually.of_forall hup)

/-- Blueprint A04′ over an infinite field: the leading coefficient of the affine Hilbert
polynomial of a prime `I` is `degree I / (quotDim I)!`. -/
theorem leadingCoeff_affineHilbertPoly_of_infinite (I : Ideal (MvPolynomial (Fin d) K))
    [I.IsPrime] :
    (affineHilbertPoly I).leadingCoeff = (degree I : ℚ) / (quotDim I).factorial := by
  obtain ⟨Δ, e, hΔ, hlow, hup⟩ := exists_hilbert_bounds I
  exact leadingCoeff_affineHilbertPoly_of_eventually_bounds hΔ
    (eventually_sum_choose_le_hilbert hlow) (Filter.Eventually.of_forall hup)

/-- Blueprint A04′ over an infinite field: a prime has positive degree. -/
theorem degree_pos_of_infinite (I : Ideal (MvPolynomial (Fin d) K)) [I.IsPrime] :
    0 < degree I := by
  obtain ⟨Δ, e, hΔ, hlow, hup⟩ := exists_hilbert_bounds I
  exact degree_pos_of_eventually_bounds hΔ (eventually_sum_choose_le_hilbert hlow)
    (Filter.Eventually.of_forall hup)

/-- Blueprint A08 over an infinite field: **the uniform Hilbert upper bound**
`hilbert I t ≤ degree I * (t + quotDim I).choose (quotDim I)` for a prime `I`. -/
theorem hilbert_le_degree_mul_choose_of_infinite (I : Ideal (MvPolynomial (Fin d) K))
    [I.IsPrime] (t : ℕ) : hilbert I t ≤ degree I * (t + quotDim I).choose (quotDim I) := by
  obtain ⟨Δ, e, hΔ, hlow, hup⟩ := exists_hilbert_bounds I
  exact hilbert_le_degree_mul_choose_of_eventually_bounds hΔ
    (eventually_sum_choose_le_hilbert hlow) hup t

variable (K d) in
/-- The A04′ facts bundled for B03. -/
theorem degreeFacts : DegreeFacts K d where
  natDegree_affineHilbertPoly I hI := by
    have := hI
    exact natDegree_affineHilbertPoly_of_infinite I
  leadingCoeff_affineHilbertPoly I hI := by
    have := hI
    exact leadingCoeff_affineHilbertPoly_of_infinite I
  degree_pos I hI := by
    have := hI
    exact degree_pos_of_infinite I

end Infinite

variable (K d) in
/-- **The algebraic interface holds over every field** (blueprint nodes A08, J02, B03 via TR7). -/
theorem algebraInterface : AlgebraInterface K d :=
  algebraInterface_of_infinite
    (fun I hI t ↦ by
      have := hI
      exact hilbert_le_degree_mul_choose_of_infinite I t)
    (fun I hI hk g T hg hT hne ↦ by
      have := hI
      exact proper_cut_of_infinite (degreeFacts (RatFunc K) d) I hk g T hg hT hne)

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
