/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.ExampleB
import LeanPool.DomainTheory.Neighborhood.Theorem111

/-!
# Exercise 1.13 (Scott 1981, PRG-19, §1) — the infinite binary system `B`,
revisited

Scott: "Verify all the assertions made about the system `B` … Draw a picture …
which includes nodes
for all `σ ∈ Σ*` … and where the total elements lie. (The picture … has to have
limit nodes all
along the top.)"

The "assertions about `B`" are exactly the content of `ExampleB.lean`:

* `ExampleB.B` is a neighbourhood system (`ExampleB.nestedOrDisjoint`);
* `ExampleB.sigmaElt`/`sigmaElt_bot` realize Scott's `σx` and `σ⊥` with `σx ∈
|B|`;
* `ExampleB.sigmaBot_le_iff` is "`σ₀⊥ ⊑ σ₁⊥ iff σ₀` initial segment of `σ₁`";
* `ExampleB.mem_iff_exists_sigmaBot` is "`x = ⋃ₙ σₙ⊥`".

This file supplies the **limit nodes**: for an infinite path `p : ℕ → Bool` we
build the element
`branch p ∈ |B|` as the ascending union (Theorem 1.11(ii)) of the finite
approximations
`σₙ⊥ = (p↾n)⊥`, show every finite approximation approximates it
(`branchSeq_le_branch`), and prove it
is a **total** (maximal) element (`branch_isTotal`). These are the nodes "along
the top".

Constructive except `branch_isTotal`'s use of `B`'s structure (still `[propext,
Quot.sound]`).
-/

namespace Domain.Neighborhood.Exercise113

open Domain.Neighborhood NeighborhoodSystem ExampleB

/-- The length-`n` initial segment `p ↾ n = ⟨p 0, …, p (n-1)⟩` of an infinite path
`p`. -/
def prefixSeq (p : ℕ → Bool) : ℕ → Str
  | 0 => []
  | (n + 1) => prefixSeq p n ++ [p n]

@[simp] theorem prefixSeq_length (p : ℕ → Bool) (n : ℕ) : (prefixSeq p n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [prefixSeq, ih]

theorem prefixSeq_prefix_succ (p : ℕ → Bool) (n : ℕ) :
    prefixSeq p n <+: prefixSeq p (n + 1) := ⟨[p n], rfl⟩

theorem prefixSeq_mono (p : ℕ → Bool) {n m : ℕ} (h : n ≤ m) :
    prefixSeq p n <+: prefixSeq p m := by
  induction m, h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ k _ ih => exact ih.trans (prefixSeq_prefix_succ p k)

/-- The finite approximations `σₙ⊥ = (p ↾ n)⊥` along the path `p`. -/
def branchSeq (p : ℕ → Bool) (n : ℕ) : B.Element := sigmaBot (prefixSeq p n)

theorem branchSeq_mono (p : ℕ → Bool) : Monotone (branchSeq p) := by
  intro n m h
  exact (sigmaBot_le_iff (prefixSeq p n) (prefixSeq p m)).mpr (prefixSeq_mono p h)

/-- **The limit/total element of an infinite path** `p`: the ascending union `⋃ₙ
(p ↾ n)⊥`
(Theorem 1.11(ii)). These are the "limit nodes all along the top" of Scott's
picture. -/
def branch (p : ℕ → Bool) : B.Element := B.iUnion (branchSeq p) (branchSeq_mono p)

/-- `cone σ ∈ branch p` iff `σ` is an initial segment of some `p ↾ n`, i.e. `σ`
lies on the path. -/
theorem branch_mem_iff (p : ℕ → Bool) {σ : Str} :
    (branch p).mem (cone σ) ↔ ∃ n, σ <+: prefixSeq p n := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (B.mem_iUnion (branchSeq p) (branchSeq_mono p)).mp h
    exact ⟨n, cone_subset_cone.mp hn.2⟩
  · rintro ⟨n, hn⟩
    exact (B.mem_iUnion (branchSeq p) (branchSeq_mono p)).mpr
      ⟨n, memB_cone σ, cone_subset_cone.mpr hn⟩

/-- Every finite approximation `(p ↾ n)⊥` approximates the limit element `branch
p`. -/
theorem branchSeq_le_branch (p : ℕ → Bool) (n : ℕ) : branchSeq p n ≤ branch p :=
  B.le_iUnion (branchSeq p) (branchSeq_mono p) n

/-- Two neighbourhoods present in a common element of `|B|` have comparable
generating prefixes
(their cones cannot be disjoint, since the intersection is a nonempty cone). -/
theorem prefix_comparable_of_mem {σ τ : Str} (y : B.Element)
    (hσ : y.mem (cone σ)) (hτ : y.mem (cone τ)) : σ <+: τ ∨ τ <+: σ := by
  have hi : y.mem (cone σ ∩ cone τ) := y.inter_mem hσ hτ
  obtain ⟨ρ, hρ⟩ := y.sub hi
  rcases cone_trichotomy σ τ with h | h | h
  · exact Or.inr (cone_subset_cone.mp h)
  · exact Or.inl (cone_subset_cone.mp h)
  · exfalso
    have hmem : ρ ∈ cone ρ := mem_cone.mpr List.prefix_rfl
    rw [← hρ, h] at hmem
    simp at hmem

/-- **Exercise 1.13 (total elements).** Each infinite path `p` gives a *total*
(maximal) element
`branch p`: any `y` it approximates approximates it back. (These maximal elements
are exactly the
limit nodes along the top of the binary-tree picture.) -/
theorem branch_isTotal (p : ℕ → Bool) : B.IsTotal (branch p) := by
  intro y hy X hX
  obtain ⟨σ, rfl⟩ := y.sub hX
  have hk : y.mem (cone (prefixSeq p σ.length)) :=
    hy _ ((branch_mem_iff p).mpr ⟨σ.length, List.prefix_rfl⟩)
  rcases prefix_comparable_of_mem y hX hk with h | h
  · exact (branch_mem_iff p).mpr ⟨σ.length, h⟩
  · have hlen : (prefixSeq p σ.length).length = σ.length := prefixSeq_length p σ.length
    have hσ : prefixSeq p σ.length = σ := h.eq_of_length hlen
    exact (branch_mem_iff p).mpr ⟨σ.length, by rw [hσ]⟩

end Domain.Neighborhood.Exercise113
