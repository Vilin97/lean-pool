/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import LeanPool.Nivat.Algebra.Action
public import LeanPool.Nivat.Core.Patterns
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Ring

/-
Upstream: https://github.com/boonsuan/nivat
Commit: 84fe839635bdebb7d5e80c209b4f578a0c767fcf
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Boon Suan Ho

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# An annihilator from low pattern complexity

The finite-range form of Lemma 3.2 (`lem:ann-exists`) is proved by affine
dependence among the occurring patterns. `exists_affine_annihilator` gives a nonzero filter
with constant output, and `exists_nonzero_annihilator` multiplies it by a nonzero difference.

The `windowPolynomial` linear map identifies finite coefficient vectors with
Laurent polynomials supported in the window. Its injectivity, support, action,
and reconstruction lemmas also supply the finite-dimensional pairing used in
Theorem 2.2 (`thm:descent`).
-/

public section

namespace Nivat.Algebra

/-- Auxiliary construction for Lemma 3.2 (`lem:ann-exists`): identify a coefficient vector on a
finite window with its supported Laurent polynomial. -/
@[expose] noncomputable def windowPolynomial (D : Finset Lattice) (a : D → ℚ) : Laurent :=
  ∑ z : D, AddMonoidAlgebra.single z.1 (a z)

/-- Auxiliary construction for Lemma 3.2 (`lem:ann-exists`): the supported polynomial recovers each
input coefficient on the window. -/
theorem windowPolynomial_coeff (D : Finset Lattice) (a : D → ℚ) (z : D) :
    (windowPolynomial D a).coeff z.1 = a z := by
  classical
  simp [windowPolynomial, AddMonoidAlgebra.coeff_sum, Finsupp.single_apply]

/-- Auxiliary construction for Lemma 3.2 (`lem:ann-exists`): the coefficient-vector identification
is injective. -/
theorem windowPolynomial_injective (D : Finset Lattice) :
    Function.Injective (windowPolynomial D) := by
  intro a b hab
  funext z
  simpa only [windowPolynomial_coeff] using congrArg (fun f : Laurent => f.coeff z.1) hab

/-- Auxiliary construction for Lemma 3.2 (`lem:ann-exists`): the polynomial associated with a window
vector is supported inside that window. -/
theorem windowPolynomial_support (D : Finset Lattice) (a : D → ℚ) :
    (windowPolynomial D a).coeff.support ⊆ D := by
  classical
  intro z hz
  by_contra hzD
  have hzero : (windowPolynomial D a).coeff z = 0 := by
    simp [windowPolynomial, AddMonoidAlgebra.coeff_sum,
      show ∀ w : D, w.1 ≠ z from fun w hw => hzD (hw ▸ w.2)]
  exact (Finsupp.mem_support_iff.mp hz) hzero

/-- Auxiliary construction for Lemma 3.2 (`lem:ann-exists`): the associated Laurent action is the
coefficient pairing with a translated restriction. -/
theorem act_windowPolynomial (D : Finset Lattice) (a : D → ℚ)
    (c : Configuration ℚ) (u : Lattice) :
    act (windowPolynomial D a) c u = ∑ z : D, a z * c (u + z.1) := by
  simp [windowPolynomial, act, map_sum, actionHom, AddMonoidAlgebra.lift_single,
    shiftRepresentation, shiftLinear, shift, Finset.sum_apply]

/-- Auxiliary construction for Lemma 3.2 (`lem:ann-exists`): restriction of a supported polynomial
followed by reconstruction returns that polynomial. -/
theorem windowPolynomial_reconstruct (D : Finset Lattice) (f : Laurent)
    (hf : f.coeff.support ⊆ D) : windowPolynomial D (fun z => f.coeff z.1) = f := by
  classical
  ext z
  by_cases hz : z ∈ D
  · exact windowPolynomial_coeff D _ ⟨z, hz⟩
  · rw [Finsupp.notMem_support_iff.mp (fun h => hz (windowPolynomial_support D _ h)),
      Finsupp.notMem_support_iff.mp (fun h => hz (hf h))]

/-- Auxiliary construction for Lemma 3.2 (`lem:ann-exists`): the supported-polynomial identification
as a rational linear map. -/
@[expose] noncomputable def windowPolynomialLinear (D : Finset Lattice) :
    (D → ℚ) →ₗ[ℚ] Laurent where
  toFun := windowPolynomial D
  map_add' a b := by
    classical
    simp [windowPolynomial, AddMonoidAlgebra.single_add, Finset.sum_add_distrib]
  map_smul' a b := by
    classical
    simp [windowPolynomial, Finset.smul_sum, AddMonoidAlgebra.smul_single]

/-- Auxiliary construction for Lemma 3.2 (`lem:ann-exists`): affine dependence among the occurring
patterns gives a nonzero supported filter with constant output. -/
theorem exists_affine_annihilator (c : Configuration ℚ) (hc : FiniteRange c)
    (D : Finset Lattice) (hlow : complexity c D ≤ D.card) :
    ∃ g : Laurent, g ≠ 0 ∧ g.coeff.support ⊆ D ∧
      ∃ κ : ℚ, act g c = fun _ => κ := by
  classical
  let : Fintype (patterns c D) := (patterns_finite hc D).fintype
  let F : (Option D → ℚ) →ₗ[ℚ] (patterns c D → ℚ) :=
    { toFun := fun a p => a none + ∑ z : D, a (some z) * p.1 z
      map_add' := by
        intro a b
        funext p
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
        ring
      map_smul' := by
        intro a b
        funext p
        simp [Finset.mul_sum, mul_add, mul_assoc] }
  have hdim : Module.finrank ℚ (patterns c D → ℚ) < Module.finrank ℚ (Option D → ℚ) := by
    have hcard : Fintype.card (patterns c D) = complexity c D := by
      simp only [complexity, Set.ncard_eq_toFinset_card', Set.toFinset_card]
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_option, Fintype.card_coe, hcard]
    omega
  have hker : LinearMap.ker F ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨a, ha, hane⟩ := (LinearMap.ker F).ne_bot_iff.mp hker
  have hrel (u : Lattice) : a none + ∑ z : D, a (some z) * c (z.1 + u) = 0 := by
    exact congrFun (LinearMap.mem_ker.mp ha) ⟨patternAt c D u, ⟨u, rfl⟩⟩
  let b : D → ℚ := fun z => a (some z)
  have hb : b ≠ 0 := by
    intro hz
    have hnone : a none = 0 := by
      have h := hrel 0
      have hz' : ∀ z : D, a (some z) = 0 := congrFun hz
      simpa only [hz', zero_mul, Finset.sum_const_zero, add_zero] using h
    apply hane
    funext z
    cases z with
    | none => exact hnone
    | some z => exact congrFun hz z
  refine ⟨windowPolynomial D b, ?_, windowPolynomial_support D b, -a none, ?_⟩
  · intro hg
    apply hb
    apply windowPolynomial_injective D
    simpa [windowPolynomial] using hg
  · funext u
    rw [act_windowPolynomial]
    have h := hrel u
    change (∑ z : D, a (some z) * c (u + z.1)) = -a none
    have hsum : (∑ z : D, a (some z) * c (u + z.1)) =
        ∑ z : D, a (some z) * c (z.1 + u) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [add_comm u z.1]
    rw [hsum]
    exact eq_neg_of_add_eq_zero_right h

/-- Lemma 3.2 (`lem:ann-exists`): low complexity gives a nonzero Laurent annihilator. A nonzero
difference polynomial annihilates the constant output of the affine relation. -/
theorem exists_nonzero_annihilator (c : Configuration ℚ) (hc : FiniteRange c)
    (D : Finset Lattice) (hlow : complexity c D ≤ D.card) :
    ∃ f : Laurent, f ≠ 0 ∧ act f c = 0 := by
  obtain ⟨g, hg, _, κ, hconst⟩ := exists_affine_annihilator c hc D hlow
  let h : Lattice := (1, 0)
  have hh : h ≠ 0 := by decide
  refine ⟨(monomial h - 1) * g, mul_ne_zero (monomial_sub_one_ne_zero hh) hg, ?_⟩
  rw [act_mul, hconst, act_difference]
  funext z
  simp [difference_apply]

end Nivat.Algebra
