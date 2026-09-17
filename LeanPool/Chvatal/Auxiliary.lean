/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvátal formalization contributors
-/
module

public import LeanPool.Chvatal.Fourier
public import LeanPool.Chvatal.Bessel
public import LeanPool.Chvatal.Family
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

import Mathlib.Tactic.Ring

/-
Upstream: https://github.com/boonsuan/chvatal
Commit: c19ed3aaac9e42d446f963a862d39d8a09eddbf9
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Chvatal formalization contributors

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
# Auxiliary monomials

The Boolean monomials in Section 3.1 of the paper are represented as indicators
of principal upper sets. This file proves their exact Fourier expansion (9),
all four assertions of Lemma 3.1, and the orthonormal auxiliary families of
Corollary 3.2. The independence proof uses subset induction and needs no
arbitrary ordering of the monomials.
-/

@[expose] public section

namespace Chvatal

open Finset
open scoped symmDiff

variable {ι : Type*} [DecidableEq ι]

/-- The Boolean monomial `M_S` of Section 3.1, equal to `1` exactly on supersets of `S`. -/
def monomial (S x : Finset ι) : ℝ := if S ⊆ x then 1 else 0

/-- The physical support calculation immediately preceding Lemma 3.1. -/
@[simp] theorem monomial_ne_zero_iff (S x : Finset ι) :
    monomial S x ≠ 0 ↔ S ⊆ x := by
  simp [monomial]

/-- Each monomial is one at its own index, the diagonal entry in the triangular
independence argument of Lemma 3.1(iii). -/
@[simp] theorem monomial_self (S : Finset ι) : monomial S S = 1 := by
  simp [monomial]

variable [Fintype ι]

/-- Evaluating a zero linear combination at successive subsets forces every
coefficient to vanish. This is the triangular argument in Lemma 3.1(iii). -/
theorem monomial_coefficients_eq_zero (c : Finset ι → ℝ)
    (h : ∑ S, c S • monomial S = 0) : ∀ S, c S = 0 := by
  intro S
  induction S using Finset.strongInductionOn
  rename_i S ih
  have heval := congrFun h S
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at heval
  have hsum : ∑ T : Finset ι, c T * monomial T S = c S := by
      rw [Finset.sum_eq_single S]
      · simp
      · intro T _ hTS
        by_cases hsub : T ⊆ S
        · rw [ih T (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hTS⟩)]
          simp
        · simp [monomial, hsub]
      · simp
  exact hsum.symm.trans heval

omit [Fintype ι] in
/-- Lemma 3.1(iii): the entire Boolean monomial family is linearly independent.
Consequently every family obtained by restricting the index set is independent. -/
theorem linearIndependent_monomial [Finite ι] :
    LinearIndependent ℝ (monomial (ι := ι)) := by
  let _ := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  exact monomial_coefficients_eq_zero

omit [Fintype ι] in
/-- Lemma 3.1(iii) for any specified subfamily of monomials. -/
theorem linearIndependent_monomial_subfamily [Finite ι] (A : Set (Finset ι)) :
    LinearIndependent ℝ (fun S : A => monomial S.1) :=
  linearIndependent_monomial.comp Subtype.val Subtype.val_injective

omit [Fintype ι] in
/-- A monomial is unchanged when a coordinate outside its index is toggled.
This gives its Fourier support in the discussion preceding Lemma 3.1. -/
theorem monomial_toggle {S : Finset ι} {i : ι} (hi : i ∉ S) (x : Finset ι) :
    monomial S (x ∆ {i}) = monomial S x := by
  have hsub : S ⊆ x ∆ {i} ↔ S ⊆ x := by
    constructor <;> intro h j hj
    · have hji : j ≠ i := fun heq => hi (heq ▸ hj)
      simpa [Finset.mem_symmDiff, hji] using h hj
    · have hji : j ≠ i := fun heq => hi (heq ▸ hj)
      simpa [Finset.mem_symmDiff, hji] using h hj
  simp [monomial, hsub]

/-- The Fourier support inclusion for monomials preceding Lemma 3.1:
only subsets of the monomial's index can have a nonzero coefficient. -/
theorem fourier_monomial_eq_zero {S T : Finset ι} (hTS : ¬T ⊆ S) :
    fourier (monomial S) T = 0 := by
  obtain ⟨i, hiT, hiS⟩ := Finset.not_subset.mp hTS
  exact fourier_eq_zero_of_invariant _ hiT (monomial_toggle hiS)

/-- Multiplication by the full Walsh character, used to construct the second
auxiliary family in Lemma 3.1. It is a linear involution. -/
noncomputable def fullWalshMultiplier : (Finset ι → ℝ) ≃ₗ[ℝ] (Finset ι → ℝ) where
  toFun f x := f x * walsh Finset.univ x
  invFun f x := f x * walsh Finset.univ x
  left_inv f := by
    funext x
    change (f x * walsh Finset.univ x) * walsh Finset.univ x = f x
    rw [mul_assoc, ← pow_two, walsh_sq, mul_one]
  right_inv f := by
    funext x
    change (f x * walsh Finset.univ x) * walsh Finset.univ x = f x
    rw [mul_assoc, ← pow_two, walsh_sq, mul_one]
  map_add' f g := by ext x; simp only [Pi.add_apply]; ring
  map_smul' c f := by ext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The functions `χ_[n] M_S` in the second auxiliary family of Lemma 3.1. -/
noncomputable def twistedMonomial (S : Finset ι) : Finset ι → ℝ :=
  fullWalshMultiplier (monomial S)

/-- Coordinate description of the twisted monomials of Lemma 3.1. -/
@[simp] theorem twistedMonomial_apply (S x : Finset ι) :
    twistedMonomial S x = monomial S x * walsh Finset.univ x := rfl

/-- Lemma 3.1(iii) for the second family: the full character is an invertible
multiplier, so independence of the monomials is preserved. -/
theorem linearIndependent_twistedMonomial :
    LinearIndependent ℝ (twistedMonomial (ι := ι)) :=
  linearIndependent_monomial.map' fullWalshMultiplier.toLinearMap
    (LinearMap.ker_eq_bot.mpr fullWalshMultiplier.injective)

/-- Fourier support of the second family in Lemma 3.1: a nonzero coefficient
must contain the complement of the monomial's index. -/
theorem fourier_twistedMonomial_eq_zero {S T : Finset ι} (hST : ¬Sᶜ ⊆ T) :
    fourier (twistedMonomial S) T = 0 := by
  have hTS : ¬Tᶜ ⊆ S := by
    intro h
    exact hST (by simpa using compl_le_compl h)
  change fourier (fun x => monomial S x * walsh Finset.univ x) T = 0
  rw [fourier_mul_walsh]
  have hcomp : T ∆ Finset.univ = Tᶜ := by
    ext i
    simp [Finset.mem_symmDiff]
  rw [hcomp]
  exact fourier_monomial_eq_zero hTS

omit [Fintype ι] in
/-- Lemma 3.1(i), physical support: increasing families contain the entire
support of every monomial indexed by one of their members. -/
theorem monomial_eq_zero_of_not_mem {F : Family ι} (hF : F.IsIncreasing)
    {S : Finset ι} (hS : S ∈ F) {x : Finset ι} (hx : x ∉ F) :
    monomial S x = 0 := by
  have hsub : ¬S ⊆ x := fun h => hx (hF h hS)
  simp [monomial, hsub]

/-- Lemma 3.1(i), Fourier support: a monomial whose index lies outside an
increasing family has zero Fourier coefficients on that family. -/
theorem fourier_monomial_eq_zero_of_mem {G : Family ι} (hG : G.IsIncreasing)
    {S T : Finset ι} (hS : S ∉ G) (hT : T ∈ G) :
    fourier (monomial S) T = 0 :=
  fourier_monomial_eq_zero (fun hTS => hS (hG hTS hT))

/-- Lemma 3.1(ii), physical support of the twisted monomials. -/
theorem twistedMonomial_eq_zero_of_not_mem {F : Family ι} (hF : F.IsIncreasing)
    {S : Finset ι} (hS : S ∈ F) {x : Finset ι} (hx : x ∉ F) :
    twistedMonomial S x = 0 := by
  simp [monomial_eq_zero_of_not_mem hF hS hx]

/-- Lemma 3.1(ii), Fourier support of the twisted monomials: when the complement
of the index belongs to an increasing family, all coefficients outside it vanish. -/
theorem fourier_twistedMonomial_eq_zero_of_not_mem {G : Family ι}
    (hG : G.IsIncreasing) {S T : Finset ι} (hS : Sᶜ ∈ G) (hT : T ∉ G) :
    fourier (twistedMonomial S) T = 0 :=
  fourier_twistedMonomial_eq_zero (fun hST => hT (hG hST hS))

omit [Fintype ι] in
/-- The multiplicative recursion for the Boolean monomials in Section 3.1. -/
theorem monomial_insert (i : ι) (S x : Finset ι) :
    monomial (insert i S) x = if i ∈ x then monomial S x else 0 := by
  simp only [monomial, Finset.insert_subset_iff]
  split_ifs <;> simp_all

omit [Fintype ι] in
/-- Equation (9), multiplied by `2^|S|`: the finite Walsh expansion of a
Boolean monomial. This proof follows the coordinate product expansion. -/
theorem monomial_expansion_scaled (S x : Finset ι) :
    (∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * walsh T x) =
      (2 : ℝ) ^ S.card * monomial S x := by
  induction S using Finset.induction_on with
  | empty => simp [monomial]
  | @insert i S hi ih =>
    rw [Finset.sum_powerset_insert hi]
    have hsum :
        (∑ T ∈ S.powerset, (-1 : ℝ) ^ (insert i T).card * walsh (insert i T) x) =
          -(if i ∈ x then (-1 : ℝ) else 1) *
            (∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * walsh T x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      have hiT : i ∉ T := fun h => hi ((Finset.mem_powerset.mp hT) h)
      rw [Finset.card_insert_of_notMem hiT, walsh_insert hiT, pow_succ]
      ring
    rw [hsum, ih, Finset.card_insert_of_notMem hi, pow_succ, monomial_insert]
    by_cases hix : i ∈ x <;> simp [hix]
    ring

omit [Fintype ι] in
/-- Equation (9): the normalized Fourier–Walsh expansion of `M_S`. -/
theorem monomial_expansion (S x : Finset ι) :
    monomial S x = ((2 : ℝ) ^ S.card)⁻¹ *
      ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * walsh T x := by
  rw [monomial_expansion_scaled]
  simp

/-- Scalar linearity of the Fourier transform, used when preserving support
under the Gram–Schmidt process in Corollary 3.2. -/
theorem fourier_smul_function (c : ℝ) (f : Finset ι → ℝ) (S : Finset ι) :
    fourier (c • f) S = c * fourier f S := by
  simp only [fourier, Pi.smul_apply, smul_eq_mul, mul_assoc, cubeMean_mul_left]

/-- The functions satisfying both support restrictions of Corollary 3.2 form a
linear subspace: physical support lies in `F`, and Fourier support lies in `K`. -/
def supportSubspace (F K : Family ι) : Submodule ℝ (Finset ι → ℝ) where
  carrier := {f | (∀ x, x ∉ F → f x = 0) ∧ (∀ S, S ∉ K → fourier f S = 0)}
  zero_mem' := by
    constructor
    · intro x _; rfl
    · intro S _; simp [fourier, cubeMean]
  add_mem' := by
    intro f g hf hg
    constructor
    · intro x hx; simp [hf.1 x hx, hg.1 x hx]
    · intro S hS
      change fourier (fun x => f x + g x) S = 0
      rw [fourier_add, hf.2 S hS, hg.2 S hS, add_zero]
  smul_mem' := by
    intro c f hf
    constructor
    · intro x hx; simp [hf.1 x hx]
    · intro S hS; rw [fourier_smul_function, hf.2 S hS, mul_zero]

/-- Expanded membership criterion for the support-preserving subspace used in
Corollary 3.2. -/
@[simp] theorem mem_supportSubspace (F K : Family ι) (f : Finset ι → ℝ) :
    f ∈ supportSubspace F K ↔
      (∀ x, x ∉ F → f x = 0) ∧ (∀ S, S ∉ K → fourier f S = 0) := Iff.rfl

omit [DecidableEq ι] in
/-- The probability inner product of Theorem 2.1 is the cube expectation used in
all Fourier identities in Section 2. -/
theorem uniformInner_eq_cubeMean (f g : Finset ι → ℝ) :
    uniformInner f g = cubeMean (fun x => f x * g x) := rfl

/-- Lemma 3.1(iv): disjoint Fourier supports imply orthogonality by Parseval. -/
theorem uniformInner_eq_zero_of_fourier_support (G : Family ι)
    {f g : Finset ι → ℝ} (hf : ∀ S, S ∈ G → fourier f S = 0)
    (hg : ∀ S, S ∉ G → fourier g S = 0) : uniformInner f g = 0 := by
  rw [uniformInner_eq_cubeMean, parseval_inner]
  apply Finset.sum_eq_zero
  intro S _
  by_cases hS : S ∈ G
  · rw [hf S hS, zero_mul]
  · rw [hg S hS, mul_zero]

omit [DecidableEq ι] in
/-- Symmetry of the real probability inner product, used for the two mixed
orders in the combined orthonormal family of Corollary 3.2. -/
theorem uniformInner_comm (f g : Finset ι → ℝ) : uniformInner f g = uniformInner g f := by
  simp only [uniformInner, mul_comm]

/-- Lemma 3.1(iv) for the particular two monomial families in the paper. -/
theorem monomial_twistedMonomial_orthogonal {G : Family ι} (hG : G.IsIncreasing)
    {S T : Finset ι} (hS : S ∉ G) (hT : Tᶜ ∈ G) :
    uniformInner (monomial S) (twistedMonomial T) = 0 :=
  uniformInner_eq_zero_of_fourier_support G
    (fun _ h => fourier_monomial_eq_zero_of_mem hG hS h)
    (fun _ h => fourier_twistedMonomial_eq_zero_of_not_mem hG hT h)

/-- Corollary 3.2: orthonormal auxiliary families with the paper's exact index
sets and both required support conditions. The sum type joins the two families
into a single orthonormal system, including when either index set is empty. -/
theorem auxiliary_orthonormal_system (F G : Family ι)
    (hF : F.IsIncreasing) (hG : G.IsIncreasing) :
    ∃ (u : ↥(F \ G) → Finset ι → ℝ) (v : ↥(F \ G.dual) → Finset ι → ℝ),
      UniformOrthonormal (Sum.elim u v) ∧
      (∀ i, u i ∈ supportSubspace F Gᶜ) ∧
      (∀ i, v i ∈ supportSubspace F G) := by
  classical
  have hmono : ∀ i : ↥(F \ G), monomial i.1 ∈ supportSubspace F Gᶜ := by
    intro i
    constructor
    · intro x hx
      exact monomial_eq_zero_of_not_mem hF (Finset.mem_sdiff.mp i.2).1 hx
    · intro S hS
      exact fourier_monomial_eq_zero_of_mem hG (Finset.mem_sdiff.mp i.2).2
        (by simpa using hS)
  have htwist : ∀ i : ↥(F \ G.dual), twistedMonomial i.1 ∈ supportSubspace F G := by
    intro i
    constructor
    · intro x hx
      exact twistedMonomial_eq_zero_of_not_mem hF (Finset.mem_sdiff.mp i.2).1 hx
    · intro S hS
      apply fourier_twistedMonomial_eq_zero_of_not_mem hG _ hS
      simpa only [Family.mem_dual, not_not] using (Finset.mem_sdiff.mp i.2).2
  obtain ⟨u, hu, humem⟩ := exists_uniformOrthonormal_in_submodule
    (supportSubspace F Gᶜ) (fun i : ↥(F \ G) => monomial i.1)
      (linearIndependent_monomial.comp Subtype.val Subtype.val_injective) hmono
  obtain ⟨v, hv, hvmem⟩ := exists_uniformOrthonormal_in_submodule
    (supportSubspace F G) (fun i : ↥(F \ G.dual) => twistedMonomial i.1)
      (linearIndependent_twistedMonomial.comp Subtype.val Subtype.val_injective) htwist
  have huv (i j) : uniformInner (u i) (v j) = 0 := by
    apply uniformInner_eq_zero_of_fourier_support G
    · intro S hS
      exact (humem i).2 S (by simpa using hS)
    · exact (hvmem j).2
  refine ⟨u, v, ?_, humem, hvmem⟩
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      by_cases hij : i = j <;> simpa [hij] using hu i j
    | inr j => simpa using huv i j
  | inr i =>
    cases j with
    | inl j => simpa [uniformInner_comm] using huv j i
    | inr j =>
      by_cases hij : i = j <;> simpa [hij] using hv i j

/-- The exact coefficient formula from equation (9). In particular, every subset
of `S` occurs with a nonzero Fourier coefficient. -/
theorem fourier_monomial (S T : Finset ι) :
    fourier (monomial S) T =
      if T ⊆ S then ((2 : ℝ) ^ S.card)⁻¹ * (-1 : ℝ) ^ T.card else 0 := by
  unfold fourier
  simp_rw [monomial_expansion S]
  simp_rw [mul_assoc, Finset.sum_mul, mul_assoc]
  rw [cubeMean_mul_left, cubeMean_sum]
  simp_rw [cubeMean_mul_left, walsh_orthogonality]
  by_cases hTS : T ⊆ S <;> simp [hTS, mul_ite]

/-- The exact Fourier support calculation for the first family preceding Lemma 3.1. -/
theorem fourier_monomial_ne_zero_iff (S T : Finset ι) :
    fourier (monomial S) T ≠ 0 ↔ T ⊆ S := by
  rw [fourier_monomial]
  split_ifs with h <;> simp [h]

/-- The exact coefficients of the second auxiliary family, obtained by
complementing Fourier indices as in the discussion preceding Lemma 3.1. -/
theorem fourier_twistedMonomial (S T : Finset ι) :
    fourier (twistedMonomial S) T =
      if Sᶜ ⊆ T then ((2 : ℝ) ^ S.card)⁻¹ * (-1 : ℝ) ^ Tᶜ.card else 0 := by
  change fourier (fun x => monomial S x * walsh Finset.univ x) T = _
  rw [fourier_mul_walsh]
  have hcomp : T ∆ Finset.univ = Tᶜ := by ext i; simp [Finset.mem_symmDiff]
  rw [hcomp, fourier_monomial]
  have hsub : Tᶜ ⊆ S ↔ Sᶜ ⊆ T := by
    constructor <;> intro h <;> simpa using compl_le_compl h
  simp only [hsub]

/-- The exact Fourier support calculation for the second family preceding
Lemma 3.1: its support is the upper interval above the complementary index. -/
theorem fourier_twistedMonomial_ne_zero_iff (S T : Finset ι) :
    fourier (twistedMonomial S) T ≠ 0 ↔ Sᶜ ⊆ T := by
  rw [fourier_twistedMonomial]
  split_ifs with h <;> simp [h]

omit [Fintype ι] in
/-- The physical support equality for monomials stated before Lemma 3.1. -/
theorem support_monomial (S : Finset ι) :
    Function.support (monomial S) = {x | S ⊆ x} := by
  ext x; simp [Function.mem_support]

/-- The Fourier support equality for monomials stated before Lemma 3.1. -/
theorem support_fourier_monomial (S : Finset ι) :
    Function.support (fourier (monomial S)) = {T | T ⊆ S} := by
  ext T; simp [Function.mem_support, fourier_monomial_ne_zero_iff]

/-- Multiplication by the full character does not change physical support,
as stated before Lemma 3.1. -/
theorem support_twistedMonomial (S : Finset ι) :
    Function.support (twistedMonomial S) = {x | S ⊆ x} := by
  ext x
  have hw : walsh Finset.univ x ≠ 0 := by
    intro h
    have hsq := walsh_sq Finset.univ x
    simp [h] at hsq
  simp [Function.mem_support, hw]

/-- The Fourier support equality for twisted monomials stated before Lemma 3.1. -/
theorem support_fourier_twistedMonomial (S : Finset ι) :
    Function.support (fourier (twistedMonomial S)) = {T | Sᶜ ⊆ T} := by
  ext T; simp [Function.mem_support, fourier_twistedMonomial_ne_zero_iff]

end Chvatal
