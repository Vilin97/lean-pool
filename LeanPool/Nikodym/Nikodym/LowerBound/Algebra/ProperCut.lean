/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.ComponentDegree
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Homogenization
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.HilbertPolynomial

/-!
# The affine proper cut

This file implements blueprint node **B03** of the algebra backend: cutting a prime
`I ⊆ P := MvPolynomial (Fin d) K` of quotient dimension `k ≥ 2` by a polynomial `g ∉ I` of total
degree at most `T` with `I + (g) ≠ P` produces the minimal primes `J` over `I + (g)`, all of
positive degree, with `∑_J deg J ≤ T · deg I`.

## The `DegreeFacts` hypothesis

The proof uses three facts about the affine Hilbert polynomial of a prime ideal over an infinite
field, supplied by node **A04′** (`Algebra/Degree.lean`): `natDegree (affineHilbertPoly I) =
quotDim I`, `leadingCoeff (affineHilbertPoly I) = degree I / (quotDim I)!` and `0 < degree I`.
They are bundled here as the `Prop`-valued structure `DegreeFacts K d`, and the main theorem
`proper_cut_of_infinite` is proved conditionally on a term of this structure; node A04′ discharges
it.

## Main declarations

* `Nikodym.LowerBound.DegreeFacts K d`: the A04′ facts as a hypothesis.
* `Nikodym.LowerBound.coeff_quotDim_affineHilbertPoly`: the coefficient of `X ^ quotDim I` in the
  affine Hilbert polynomial of a prime `I` is `degree I / (quotDim I)!`.
* `Nikodym.LowerBound.one_le_totalDegree_of_sup_ne_top`: a polynomial `g ∉ I` with `I + (g) ≠ P`
  has positive total degree.
* `Nikodym.LowerBound.proper_cut_of_infinite`: the main theorem (B03) over an infinite field.

## Route

With `k := quotDim I = n + 1`, homogenize: `Q₀ := homogenization I` is a homogeneous prime of
`P̂ := MvPolynomial (Fin (d + 1)) K` with `quotDim Q₀ = n + 2` (A05), `G := homogenizeTo e g`
(`e := totalDegree g ≥ 1`) is a form of degree `e` not in `Q₀`, and for every minimal prime `J`
over `I + (g)` the homogenization `homogenization J` is a homogeneous prime of quotient dimension
`n + 1` containing `Q₀ ⊔ (G)`. Node B02 (`sum_coeff_le_of_components`) applied with
`p₀ := affineHilbertPoly I` and `p Q := affineHilbertPoly (Q.map dehom)` (so `p (homogenization J)
= affineHilbertPoly J`, via `map_dehom_homogenization` and `homHilbert_homogenization`) gives
`∑_J deg J / n! ≤ e · (n + 1) · deg I / (n + 1)!`, i.e. `∑_J deg J ≤ e · deg I ≤ T · deg I`.
-/

namespace Nikodym.LowerBound

open MvPolynomial Polynomial Filter

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K] {d : ℕ}

/-- The facts about `affineHilbertPoly` of primes supplied by node A04′ (over an infinite
field): the affine Hilbert polynomial of a prime `I` has degree `quotDim I`, leading coefficient
`degree I / (quotDim I)!`, and `degree I` is positive. -/
structure DegreeFacts (K : Type*) [Field K] (d : ℕ) : Prop where
  /-- Blueprint A04′: `natDegree (affineHilbertPoly I) = quotDim I` for a prime `I`. -/
  natDegree_affineHilbertPoly : ∀ (I : Ideal (MvPolynomial (Fin d) K)), I.IsPrime →
    (affineHilbertPoly I).natDegree = quotDim I
  /-- Blueprint A04′: `leadingCoeff (affineHilbertPoly I) = degree I / (quotDim I)!` for a prime
  `I`. -/
  leadingCoeff_affineHilbertPoly : ∀ (I : Ideal (MvPolynomial (Fin d) K)), I.IsPrime →
    (affineHilbertPoly I).leadingCoeff = (degree I : ℚ) / (quotDim I).factorial
  /-- Blueprint A04′: `0 < degree I` for a prime `I`. -/
  degree_pos : ∀ (I : Ideal (MvPolynomial (Fin d) K)), I.IsPrime → 0 < degree I

/-- Blueprint B03: the coefficient of `X ^ quotDim I` in the affine Hilbert polynomial of a prime
`I` is `degree I / (quotDim I)!` (given the A04′ facts). -/
theorem coeff_quotDim_affineHilbertPoly (hF : DegreeFacts K d)
    (I : Ideal (MvPolynomial (Fin d) K)) [I.IsPrime] :
    (affineHilbertPoly I).coeff (quotDim I) = (degree I : ℚ) / (quotDim I).factorial := by
  have h := hF.natDegree_affineHilbertPoly I ‹_›
  calc (affineHilbertPoly I).coeff (quotDim I)
      = (affineHilbertPoly I).coeff (affineHilbertPoly I).natDegree := by rw [h]
    _ = (affineHilbertPoly I).leadingCoeff := coeff_natDegree
    _ = (degree I : ℚ) / (quotDim I).factorial := hF.leadingCoeff_affineHilbertPoly I ‹_›

/-- Blueprint B03: a polynomial `g ∉ I` with `I + (g) ≠ P` has positive total degree (a nonzero
constant is a unit). -/
theorem one_le_totalDegree_of_sup_ne_top {I : Ideal (MvPolynomial (Fin d) K)}
    {g : MvPolynomial (Fin d) K} (hg : g ∉ I) (hne : I ⊔ Ideal.span {g} ≠ ⊤) :
    1 ≤ g.totalDegree := by
  by_contra h
  have h0 : g.totalDegree = 0 := by omega
  have hgC : g = MvPolynomial.C (g.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp h0
  have hc : g.coeff 0 ≠ 0 := by
    intro hc
    rw [hc, MvPolynomial.C_0] at hgC
    exact hg (hgC ▸ I.zero_mem)
  refine hne (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
    ?_)
  rw [hgC]
  exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C

-- The hypothesis `hne` is part of the blueprint contract (it forces `1 ≤ totalDegree g`, see
-- `one_le_totalDegree_of_sup_ne_top`) but is not needed: B02 does not require `1 ≤ e`.

open scoped Classical in
/-- Blueprint B03 (**affine proper cut**, over an infinite field, conditional on the A04′ facts
`hF : DegreeFacts K d`). For a prime `I` of quotient dimension `≥ 2` and `g ∉ I` of total degree
`≤ T` with `I + (g) ≠ P`, every minimal prime over `I + (g)` has positive degree, and the sum of
their degrees is at most `T · degree I`. -/
theorem proper_cut_of_infinite [Infinite K] (hF : DegreeFacts K d)
    (I : Ideal (MvPolynomial (Fin d) K)) [I.IsPrime] (hk : 2 ≤ quotDim I)
    (g : MvPolynomial (Fin d) K) (T : ℕ) (hg : g ∉ I) (hT : g.totalDegree ≤ T)
    (hne : I ⊔ Ideal.span {g} ≠ ⊤) :
    (∀ J ∈ (I ⊔ Ideal.span {g}).minimalPrimes, 0 < degree J) ∧
    ∑ J ∈ (finite_minimalPrimes_sup K I g).toFinset, degree J ≤ T * degree I := by
  refine ⟨fun J hJ ↦ hF.degree_pos J hJ.1.1, ?_⟩
  set S := (finite_minimalPrimes_sup K I g).toFinset
  have hmem : ∀ J, J ∈ S ↔ J ∈ (I ⊔ Ideal.span {g}).minimalPrimes := fun J ↦
    Set.Finite.mem_toFinset _
  -- the dimension `k = n + 1` with `n ≥ 1`
  obtain ⟨n, hn⟩ : ∃ n, quotDim I = n + 1 := ⟨quotDim I - 1, by omega⟩
  have hn1 : 1 ≤ n := by omega
  have hdimJ : ∀ J ∈ S, quotDim J = n := fun J hJ ↦ by
    have := quotDim_add_one_of_mem_minimalPrimes_sup hg ((hmem J).mp hJ)
    omega
  -- the homogenized data
  set e := g.totalDegree
  set G := homogenizeTo e g with hG
  have hGh : G.IsHomogeneous e := isHomogeneous_homogenizeTo le_rfl
  have hGQ : G ∉ homogenization I := by
    rw [hG, homogenizeTo_mem_homogenization_iff le_rfl]
    exact hg
  have hdim₀ : quotDim (homogenization I) = n + 2 := by rw [quotDim_homogenization, hn]
  have hp₀ : ∀ᶠ t : ℕ in atTop,
      (homHilbert (homogenization I) t : ℚ) = (affineHilbertPoly I).eval (t : ℚ) := by
    simpa only [homHilbert_homogenization] using hilbert_eventually_eq_affineHilbertPoly I
  have hd₀ : (affineHilbertPoly I).natDegree ≤ n + 1 := by
    rw [hF.natDegree_affineHilbertPoly I ‹_›, hn]
  have h𝒬 : ∀ Q ∈ S.image homogenization, Q.IsPrime ∧
      Q.IsHomogeneous (homogeneousSubmodule (Fin (d + 1)) K) ∧ quotDim Q = n + 1 ∧
      homogenization I ⊔ Ideal.span {G} ≤ Q := by
    intro Q hQ
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hQ
    have hJ' := (hmem J).mp hJ
    haveI : J.IsPrime := hJ'.1.1
    refine ⟨inferInstance, homogenization_isHomogeneous J, ?_, ?_⟩
    · rw [quotDim_homogenization, hdimJ J hJ]
    · refine sup_le (homogenization_mono (le_sup_left.trans hJ'.1.2)) ?_
      rw [Ideal.span_singleton_le_iff_mem, hG, homogenizeTo_mem_homogenization_iff le_rfl]
      exact hJ'.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
  have hp : ∀ Q ∈ S.image homogenization, ∀ᶠ t : ℕ in atTop,
      (homHilbert Q t : ℚ) = (affineHilbertPoly (Q.map dehom)).eval (t : ℚ) := by
    intro Q hQ
    obtain ⟨J, _, rfl⟩ := Finset.mem_image.mp hQ
    rw [map_dehom_homogenization]
    simpa only [homHilbert_homogenization] using hilbert_eventually_eq_affineHilbertPoly J
  have hd : ∀ Q ∈ S.image homogenization, (affineHilbertPoly (Q.map dehom)).natDegree ≤ n := by
    intro Q hQ
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hQ
    rw [map_dehom_homogenization, hF.natDegree_affineHilbertPoly J ((hmem J).mp hJ).1.1,
      hdimJ J hJ]
  -- apply B02
  have key := sum_coeff_le_of_components hn1 (homogenization_isHomogeneous I) hdim₀ hGh hGQ
    (S.image homogenization) h𝒬 hp₀ hd₀ (p := fun Q ↦ affineHilbertPoly (Q.map dehom)) hp hd
  rw [Finset.sum_image fun _ _ _ _ h ↦ homogenization_injective h] at key
  -- identify both sides
  have hL : ∑ J ∈ S, (affineHilbertPoly ((homogenization J).map dehom)).coeff n =
      (∑ J ∈ S, (degree J : ℚ)) / (n.factorial : ℚ) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun J hJ ↦ ?_
    haveI : J.IsPrime := ((hmem J).mp hJ).1.1
    rw [map_dehom_homogenization, ← hdimJ J hJ, coeff_quotDim_affineHilbertPoly hF J]
  have hR : (affineHilbertPoly I).coeff (n + 1) = (degree I : ℚ) / ((n + 1).factorial : ℚ) := by
    rw [← hn, coeff_quotDim_affineHilbertPoly hF I]
  rw [hL, hR, Nat.factorial_succ] at key
  -- clear denominators
  have hnf : (0 : ℚ) < n.factorial := by positivity
  have h1 : (∑ J ∈ S, (degree J : ℚ)) ≤ e * degree I := by
    rw [div_le_iff₀ hnf] at key
    have hfac : ((n + 1) * n.factorial : ℕ) = ((n : ℚ) + 1) * (n.factorial : ℚ) := by
      push_cast; ring
    have h2 : (e : ℚ) * ((n : ℚ) + 1) * ((degree I : ℚ) / (((n : ℚ) + 1) * (n.factorial : ℚ))) *
        (n.factorial : ℚ) = e * degree I := by
      field_simp
    rwa [hfac, h2] at key
  have h2 : ∑ J ∈ S, degree J ≤ e * degree I := by exact_mod_cast h1
  exact h2.trans (Nat.mul_le_mul_right _ hT)

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
