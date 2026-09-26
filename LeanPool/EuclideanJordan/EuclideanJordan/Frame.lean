/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import LeanPool.EuclideanJordan.EuclideanJordan.Orthogonal
public import Mathlib.Algebra.BigOperators.Ring.Finset



/-!
# Orthogonal idempotent families, and three Faraut–Korányi facts

Three Faraut–Korányi facts about a Jordan frame, each of which a coalescence argument would
otherwise have to carry as a hypothesis:

| content | derived here as |
| --- | --- |
| scalar-on-`range q` and `J₂(q)` operator-commute | `opCommute_scalarOn_frame` |
| `V_{ij} ⊆ J₂(pᵢ + pⱼ)` | `mem_J2_of_half_half` |
| `rᵢ = rⱼ ⟹ a(r)` is scalar on `range(pᵢ + pⱼ)` | `diagFamily_scalarOn` |

**All three are theorems rather than hypotheses**, given `EuclideanJordan/PeirceMul.lean`.

★ **But not all three are theorems of the same depth, and the first draft of this paragraph
claimed they were** ("all three are theorems of the Jordan identity"). Only
`opCommute_scalarOn_frame` uses the Jordan identity — through `EuclideanJordan/PeirceMul.lean`. The
other two do not use it at all: `mem_J2_of_half_half` is `1/2 + 1/2 = 1`, and
`diagFamily_scalarOn` is a `Finset` split. Their `omit` lines say so, and a reader should
take the FK content of this file to be **one** theorem plus two pieces of bookkeeping that
become available once the frame equations exist. The bookkeeping still has to be done; it
is just not where the difficulty is.

## The hypotheses, stated exactly

Nothing below is stated over a structure that bundles a frame. Each theorem takes as explicit
hypotheses exactly the frame equations it uses:

* `p i * p i = p i` and `p i * p j = 0` for `i ≠ j` — bundled as `IsOrthIdemFamily`;
* where a diagonal element is involved, that it is presented as `∑ k, f k • p k`.

★★ **A consumer that carries its Jordan product as a bundled bilinear map cannot apply these
lemmas without a bridge, and the reason is a typeclass diamond rather than a missing
theorem.** This layer uses the *typeclass* `Mul J` from `NonUnitalNonAssocCommRing` together
with Mathlib's `IsCommJordan`. A structure carrying the product as
`jordan : J →ₗ[ℝ] J →ₗ[ℝ] J` over `[NormedAddCommGroup J] [InnerProductSpace ℝ J]`, with
operator-commutation defined through that map, supplies a *different* `AddCommGroup J` from
the one under `NonUnitalNonAssocCommRing`. With both in scope `Module ℝ J` fails to synthesise
at `peirceOne`'s use site: it is an `AddCommGroup` diamond, not a gap in the mathematics.
`EuclideanJordan/Bridge.lean` resolves it by building the ring on the *ambient* additive group,
so only one `AddCommGroup` is ever in play. Concrete carriers are unaffected —
`EuclideanJordan/Witness.lean` uses both worlds on `HermitianMat`, where the two are the same
    instance.

★ **Completeness (`∑ p i = e`) is not assumed anywhere in this file.** None of the three
facts needs it; it is what the *spectral* theorem produces and what the rank argument
consumes. Keeping it out makes visible which results are independent of the spectral theorem.
-/

@[expose] public section

namespace EuclideanJordan

open Finset

section Family

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A family of pairwise-orthogonal idempotents. Completeness is deliberately *not* part of
this definition — see the module docstring. -/
structure IsOrthIdemFamily (p : ι → J) : Prop where
  /-- Each member is idempotent. -/
  idem : ∀ i, p i * p i = p i
  /-- Distinct members are orthogonal. -/
  orth : ∀ i j, i ≠ j → p i * p j = 0

namespace IsOrthIdemFamily

variable {p : ι → J}

omit [IsCommJordan J] [Module ℝ J] [Fintype ι] [DecidableEq ι] in
/-- **A sum over any subset of an orthogonal idempotent family is an idempotent.** In
particular `p i + p j` is, which is the rank-two block the results below run on. -/
theorem sum_idem (hp : IsOrthIdemFamily p) (s : Finset ι) :
    (∑ i ∈ s, p i) * (∑ i ∈ s, p i) = ∑ i ∈ s, p i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j hj hne => hp.orth i j (Ne.symm hne)) (fun h => absurd hi h)]
  exact hp.idem i

omit [IsCommJordan J] [Module ℝ J] [Fintype ι] [DecidableEq ι] in
/-- A member outside a subset is orthogonal to that subset's sum. -/
theorem sum_mul_of_notMem (hp : IsOrthIdemFamily p) {s : Finset ι} {k : ι} (hk : k ∉ s) :
    (∑ i ∈ s, p i) * p k = 0 := by
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun i hi => hp.orth i k ?_
  rintro rfl
  exact hk hi

end IsOrthIdemFamily

end Family

section Fields

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]
  [IsScalarTower ℝ J J]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → J}

omit [IsCommJordan J] [IsScalarTower ℝ J J] [Fintype ι] [DecidableEq ι] in
/-- **The block containment, derived.** An element halved by `p i` and by `p j` —
that is, an element of the coherence block `V_{ij}` — lies in `J₂(p i + p j)`.

The proof is that `1/2 + 1/2 = 1`; the content is entirely in the *definition* of `V_{ij}`
as a joint half-eigenspace, which is what the Peirce theory of `EuclideanJordan/Peirce.lean`
    licenses. -/
theorem mem_J2_of_half_half {i j : ι} {x : J} (hi : p i * x = (2 : ℝ)⁻¹ • x)
    (hj : p j * x = (2 : ℝ)⁻¹ • x) : (p i + p j) * x = x := by
  rw [add_mul, hi, hj]
  module

omit [IsCommJordan J] [Module ℝ J] [IsScalarTower ℝ J J] [Fintype ι] [DecidableEq ι] in
/-- The complement of a rank-two block annihilates it: `(p i + p j) ∘ p k = 0` for
`k ∉ {i, j}`. -/
theorem pair_mul_of_ne (hp : IsOrthIdemFamily p) {i j k : ι} (hki : k ≠ i) (hkj : k ≠ j) :
    (p i + p j) * p k = 0 := by
  rw [add_mul, hp.orth i k (Ne.symm hki), hp.orth j k (Ne.symm hkj), add_zero]

omit [IsCommJordan J] in
/-- The off-block part of a diagonal family is annihilated by the block. -/
theorem pair_mul_offblock (hp : IsOrthIdemFamily p) (f : ι → ℝ) (i j : ι) :
    (p i + p j) * (∑ k ∈ univ \ {i, j}, f k • p k) = 0 := by
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' := Finset.mem_sdiff.mp hk
  have hki : k ≠ i := fun h => hk'.2 (by simp [h])
  have hkj : k ≠ j := fun h => hk'.2 (by simp [h])
  rw [mul_smul_comm', pair_mul_of_ne hp hki hkj, smul_zero]

omit [IsCommJordan J] [IsScalarTower ℝ J J] in
/-- **The scalar-on-a-block decomposition, derived.** When two coordinates of `f` agree, the
diagonal family `∑ f k • p k` is *scalar on the range of* `p i + p j`: it splits as
`f i • (p i + p j)` plus a part the block annihilates.

The decomposition is exhibited rather than assumed. -/
theorem diagFamily_scalarOn (f : ι → ℝ) {i j : ι} (hij : i ≠ j) (h : f i = f j) :
    ∑ k, f k • p k = f i • (p i + p j) + ∑ k ∈ univ \ {i, j}, f k • p k := by
  have hsd := Finset.sum_sdiff (f := fun k => f k • p k) (Finset.subset_univ ({i, j} : Finset ι))
  rw [← hsd, Finset.sum_pair hij, ← h, ← smul_add]
  abel

omit [IsCommJordan J] [IsScalarTower ℝ J J] in
/-- The `i = j` case of `diagFamily_scalarOn`, for a consumer whose scalar-on-a-block
hypothesis carries no `i ≠ j` side condition. -/
theorem diagFamily_scalarOn_self (f : ι → ℝ) (i : ι) :
    ∑ k, f k • p k = (f i / 2) • (p i + p i) + ∑ k ∈ univ \ {i}, f k • p k := by
  have hsd := Finset.sum_sdiff (f := fun k => f k • p k) (Finset.subset_univ ({i} : Finset ι))
  rw [← hsd, Finset.sum_singleton]
  have : (f i / 2) • (p i + p i) = f i • p i := by module
  rw [this]
  abel

omit [DecidableEq ι] in
/-- **The operator-commutation fact, derived.** For a
rank-two block `q = p i + p j` of an orthogonal idempotent family, a diagonal family with
`f i = f j` operator-commutes with every element of `J₂(q)`. -/
theorem opCommute_scalarOn_frame (hp : IsOrthIdemFamily p) (f : ι → ℝ) {i j : ι} (hij : i ≠ j)
    (h : f i = f j) {b : J} (hb : (p i + p j) * b = b) (w : J) :
    (∑ k, f k • p k) * (b * w) = b * ((∑ k, f k • p k) * w) := by
  classical
  exact
    opCommute_scalarOn (add_idem_of_orthogonal (hp.idem i) (hp.idem j) (hp.orth i j hij))
        (diagFamily_scalarOn f hij h) (pair_mul_offblock hp f i j) hb w

end Fields

end EuclideanJordan
