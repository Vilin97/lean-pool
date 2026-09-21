/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import LeanPool.EuclideanJordan.EuclideanJordan.Block


/-!
# The Faraut–Korányi block pattern, forced by three constraints

`EuclideanJordan/Block.lean` characterises the rank-two block `J₁(p+q)`. This file does the
    frame-level
analogue, but as a **constraint on eigenvalue patterns** rather than as an assembled direct
sum — which is both what is provable here and what the FK block structure actually *is*.

Let `p` be an orthogonal idempotent family and `x ≠ 0` a joint eigenvector,
`pᵢ ∘ x = μᵢ • x`, lying in `J₁(∑ pᵢ)`. Three facts:

* `sum_eigen_eq_one` — **`∑ μᵢ = 1`**;
* `eigen_pattern_mem` — **each `μᵢ ∈ {0, 1/2, 1}`** (the trichotomy, applied at each `pᵢ`);
* `eigen_pattern_card_le_two` — **at most two `μᵢ` are nonzero**, since every nonzero one is
  at least `1/2` and they sum to `1`.

Together these force the Faraut–Korányi pattern: **either exactly one `μᵢ` is `1` — the
diagonal block `J_ii` — or exactly two are `1/2` — the coherence block `J_ij`.** The
arithmetic is immediate from the three: zero nonzero entries give sum `0 ≠ 1`; one gives a
single entry equal to `1`, so it is `1` and not `1/2`; two give `a + b = 1` with
`a, b ∈ {1/2, 1}`, whose only solution is `1/2 + 1/2`.

★ **That packaged statement is deliberately NOT a theorem here.** Formalising it means
extracting the elements of a `Finset` of cardinality `≤ 2` and case-splitting, which is
bookkeeping with no mathematical content, and stating it without proving it is exactly the
defect this arc spent four audit rounds removing. The three constraints are proved; the
one-line consequence is written out above so a reader can check it rather than trust it.

★ **What is still not built:** the assembled direct sum `J = ⊕_{i ≤ j} J_{ij}`. These
constraints say what the summands can be, not that every element decomposes into them.
-/

namespace EuclideanJordan

open Finset

section Pattern

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]
  [IsScalarTower ℝ J J]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → J} {x : J} {mu : ι → ℝ}

omit [IsCommJordan J] [IsScalarTower ℝ J J] [DecidableEq ι] in
/-- **The eigenvalue pattern of a joint eigenvector in the block sums to 1.** -/
theorem sum_eigen_eq_one (hx : x ≠ 0) (hs : (∑ i, p i) * x = x)
    (hmu : ∀ i, p i * x = mu i • x) : ∑ i, mu i = 1 := by
  have hexp : (∑ i, p i) * x = (∑ i, mu i) • x := by
    rw [Finset.sum_mul, Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => hmu i
  have hcalc : (∑ i, mu i) • x = x := by rw [← hexp, hs]
  have hz : ((∑ i, mu i) - 1) • x = 0 := by rw [sub_smul, hcalc, one_smul, sub_self]
  rcases smul_eq_zero.mp hz with h | h
  · linarith [sub_eq_zero.mp h]
  · exact absurd h hx

omit [Fintype ι] [DecidableEq ι] in
/-- **Each entry of the pattern is `0`, `1/2` or `1`.** -/
theorem eigen_pattern_mem (hp : IsOrthIdemFamily p) (hx : x ≠ 0)
    (hmu : ∀ i, p i * x = mu i • x) (i : ι) : mu i = 0 ∨ mu i = (2 : ℝ)⁻¹ ∨ mu i = 1 :=
  eigenvalue_trichotomy (hp.idem i) hx (hmu i)

omit [DecidableEq ι] in
/-- **At most two frame idempotents see a given joint eigenvector.** -/
theorem eigen_pattern_card_le_two (hp : IsOrthIdemFamily p) (hx : x ≠ 0)
    (hs : (∑ i, p i) * x = x) (hmu : ∀ i, p i * x = mu i • x) :
    ({i | mu i ≠ 0} : Finset ι).card ≤ 2 := by
  classical
  set S : Finset ι := {i | mu i ≠ 0} with hSdef
  have hlb : ∀ i ∈ S, (2 : ℝ)⁻¹ ≤ mu i := by
    intro i hi
    have hne : mu i ≠ 0 := by simpa [hSdef] using hi
    rcases eigen_pattern_mem hp hx hmu i with h | h | h
    · exact absurd h hne
    · rw [h]
    · rw [h]; norm_num
  have hsumS : ∑ i ∈ S, mu i = 1 := by
    have hsub : ∑ i ∈ S, mu i = ∑ i, mu i := by
      refine Finset.sum_subset (Finset.subset_univ S) ?_
      intro i _ hi
      simpa [hSdef] using hi
    rw [hsub, sum_eigen_eq_one hx hs hmu]
  have hcard : (S.card : ℝ) * (2 : ℝ)⁻¹ ≤ ∑ i ∈ S, mu i := by
    have h1 : ∑ _i ∈ S, (2 : ℝ)⁻¹ ≤ ∑ i ∈ S, mu i := Finset.sum_le_sum hlb
    simpa [Finset.sum_const, nsmul_eq_mul] using h1
  rw [hsumS] at hcard
  have : (S.card : ℝ) ≤ 2 := by linarith
  exact_mod_cast this

end Pattern

end EuclideanJordan
