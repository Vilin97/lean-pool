/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Exercise513
import Mathlib.Data.List.Basic

/-!
# Exercise 5.14 (Scott 1981, PRG-19, Lecture V) — the graph model `Pω`

> Using the pairing function of Exercise 5.13, code finite sequences by
> `[n₀, …, n_k] = num(n₀, [n₁, …, n_k])` and define
>
>   `fun(u)(x) = {m ∣ ∃ n₀ … n_{k-1} ∈ x, [n₀+1, …, n_{k-1}+1, 0, m] ∈ u}`,
>   `graph(f)  = {[n₀+1, …, n_{k-1}+1, 0, m] ∣ m ∈ f({n₀, …, n_{k-1}})}`.
>
> Show `fun ∘ graph = λf.f` (for continuous `f`) and `graph ∘ fun ⊇ λx.x`.

Following Exercises 4.17 and 5.13, the power-set domain `Pω` is modelled by the
complete lattice
`(Set ℕ, ⊆)`.

## The coding

The decisive device is the **tag**
`tag [n₀, …, n_{k-1}] m = [n₀+1, …, n_{k-1}+1, 0, m] = num(n₀+1, … num(n_{k-1}+1,
num(0, m))…)`,
defined by

  `tag [] m = num 0 m`,   `tag (n :: ns) m = num (n+1) (tag ns m)`.

It is a **bijection** `(List ℕ) × ℕ ≃ ℕ`: injectivity (`tag_injective`) is an
induction using
`num_injective`, and surjectivity (`tag_surjective`) is strong induction on the
value, decreasing
because `num (n+1) b > b` (`num_succ_left_gt`) — the head's first coordinate is
either `0` (stop,
emit `m`) or `≥ 1` (peel one entry and recurse on a strictly smaller code).

## The maps

With `entries ns = {n ∣ n ∈ ns}` the finite set of entries of a list:

* `Fun u x   = {m ∣ ∃ ns, (∀ n ∈ ns, n ∈ x) ∧ tag ns m ∈ u}`,
* `Graph f   = {c ∣ ∃ ns m, c = tag ns m ∧ m ∈ f (entries ns)}`.

`fun ∘ graph = id` holds only for **continuous** maps, captured by
`IsApprox f := Monotone f ∧ (finite approximation)`. We prove:

* `Fun_Graph` : `Fun (Graph f) x = f x` for `IsApprox f` — the reflexive equation
`fun ∘ graph = λf.f`;
* `id_le_Graph_Fun` : `u ⊆ Graph (Fun u)` — the inclusion `graph ∘ fun ⊇ λx.x`
(genuinely `⊇`, since
  reorderings/duplications of a list with the same `entries` give other codes in
  `Graph (Fun u)`);
* `Fun_isApprox` : every `Fun u` is itself `IsApprox`, so `fun` lands in the
continuous maps.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Domain.Neighborhood.Exercise514

open Domain.Neighborhood.Exercise513

/-! ### A strict lower bound for `num` -/

/-- `num (n+1) b` strictly exceeds its second argument: this is what makes the
decode recursion
terminate. `num (n+1) b = T(n+1+b) + b ≥ (n+b+1) + b > b`. -/
theorem num_succ_left_gt (n b : ℕ) : b < num (n + 1) b := by
  unfold num
  have e : n + 1 + b = (n + b) + 1 := by omega
  rw [e, tri_succ]
  omega

/-! ### The tag: coding `(List ℕ) × ℕ` as `ℕ` -/

/-- `tag [n₀, …, n_{k-1}] m = [n₀+1, …, n_{k-1}+1, 0, m]`, built from the pairing
function `num`. -/
def tag : List ℕ → ℕ → ℕ
  | [], m => num 0 m
  | (n :: ns), m => num (n + 1) (tag ns m)

@[simp] theorem tag_nil (m : ℕ) : tag [] m = num 0 m := rfl

@[simp] theorem tag_cons (n : ℕ) (ns : List ℕ) (m : ℕ) :
    tag (n :: ns) m = num (n + 1) (tag ns m) := rfl

/-- **The tag is one-one**, jointly in both arguments (induction on the list +
`num_injective`). -/
theorem tag_injective : ∀ {ns₁ ns₂ : List ℕ} {m₁ m₂ : ℕ},
    tag ns₁ m₁ = tag ns₂ m₂ → ns₁ = ns₂ ∧ m₁ = m₂ := by
  intro ns₁
  induction ns₁ with
  | nil =>
      intro ns₂ m₁ m₂ h
      cases ns₂ with
      | nil =>
          have hp := num_injective (show numP (0, m₁) = numP (0, m₂) from h)
          injection hp with _ hm
          exact ⟨rfl, hm⟩
      | cons n₂ ns₂' =>
          exfalso
          have hp := num_injective (show numP (0, m₁) = numP (n₂ + 1, tag ns₂' m₂) from h)
          injection hp with h1 _
          omega
  | cons n₁ ns₁' ih =>
      intro ns₂ m₁ m₂ h
      cases ns₂ with
      | nil =>
          exfalso
          have hp := num_injective (show numP (n₁ + 1, tag ns₁' m₁) = numP (0, m₂) from h)
          injection hp with h1 _
          omega
      | cons n₂ ns₂' =>
          have hp := num_injective
            (show numP (n₁ + 1, tag ns₁' m₁) = numP (n₂ + 1, tag ns₂' m₂) from h)
          injection hp with h1 h2
          have hn : n₁ = n₂ := by omega
          obtain ⟨hns, hm⟩ := ih h2
          exact ⟨by rw [hn, hns], hm⟩

/-- **The tag is onto**: every `c : ℕ` decodes as some `tag ns m`. Strong
induction on `c`,
decreasing via `num_succ_left_gt`. -/
theorem tag_surjective (c : ℕ) : ∃ ns m, tag ns m = c := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
      obtain ⟨a, b, hab⟩ : ∃ a b, num a b = c :=
        ⟨(unnum c).1, (unnum c).2, numP_unnum c⟩
      cases a with
      | zero => exact ⟨[], b, hab⟩
      | succ k =>
          have hlt : b < c := by rw [← hab]; exact num_succ_left_gt k b
          obtain ⟨ns, m, hns⟩ := ih b hlt
          exact ⟨k :: ns, m, by rw [tag_cons, hns]; exact hab⟩

/-! ### The maps `fun` and `graph` -/

/-- The finite set of entries of a list, as a subset of `ℕ`. -/
def entries (ns : List ℕ) : Set ℕ := {n | n ∈ ns}

@[simp] theorem mem_entries {n : ℕ} {ns : List ℕ} : n ∈ entries ns ↔ n ∈ ns := Iff.rfl

/-- `fun(u)(x)` — apply the "function coded by `u`" to argument `x`. -/
def Fun (u : Set ℕ) (x : Set ℕ) : Set ℕ :=
  {m | ∃ ns, (∀ n ∈ ns, n ∈ x) ∧ tag ns m ∈ u}

/-- `graph(f)` — the code of the function `f`. -/
def Graph (f : Set ℕ → Set ℕ) : Set ℕ :=
  {c | ∃ ns m, c = tag ns m ∧ m ∈ f (entries ns)}

/-- A map `f : Pω → Pω` is *approximable* (continuous) when it is monotone and
every output is
already produced by a finite subset of the input. The finite subsets of `x` are
exactly the
`entries ns` with all entries in `x`.

Monotonicity is phrased as an explicit `⊆`-implication rather than `Monotone f`:
on `Set ℕ` the
order `≤` resolves through the `CompleteLattice` instance whose construction uses
`Classical.choice`,
so the `Monotone`-based statement would not be choice-free. The two are
definitionally equal. -/
def IsApprox (f : Set ℕ → Set ℕ) : Prop :=
  (∀ ⦃x x' : Set ℕ⦄, x ⊆ x' → f x ⊆ f x') ∧
    ∀ x m, m ∈ f x → ∃ ns, (∀ n ∈ ns, n ∈ x) ∧ m ∈ f (entries ns)

/-- **`fun ∘ graph = λf.f`** for continuous `f`: `Fun (Graph f) x = f x`. -/
theorem Fun_Graph {f : Set ℕ → Set ℕ} (hf : IsApprox f) (x : Set ℕ) :
    Fun (Graph f) x = f x := by
  apply Set.Subset.antisymm
  · intro m hm
    obtain ⟨ns, hsub, htag⟩ := hm
    obtain ⟨ns', m', heq, hmem⟩ := htag
    obtain ⟨hns, hmm⟩ := tag_injective heq
    subst hns; subst hmm
    have hsubset : entries ns ⊆ x := fun n hn => hsub n hn
    exact hf.1 hsubset hmem
  · intro m hm
    obtain ⟨ns, hsub, hmem⟩ := hf.2 x m hm
    exact ⟨ns, hsub, ns, m, rfl, hmem⟩

/-- **`graph ∘ fun ⊇ λx.x`**: `u ⊆ Graph (Fun u)`. -/
theorem id_le_Graph_Fun (u : Set ℕ) : u ⊆ Graph (Fun u) := by
  intro c hc
  obtain ⟨ns, m, hceq⟩ := tag_surjective c
  refine ⟨ns, m, hceq.symm, ?_⟩
  exact ⟨ns, fun n hn => hn, by rw [hceq]; exact hc⟩

/-- Every `Fun u` is itself approximable, so `fun` really lands in the continuous
maps. -/
theorem Fun_isApprox (u : Set ℕ) : IsApprox (Fun u) := by
  refine ⟨?_, ?_⟩
  · intro x x' hxx' m hm
    obtain ⟨ns, hsub, htag⟩ := hm
    exact ⟨ns, fun n hn => hxx' (hsub n hn), htag⟩
  · intro x m hm
    obtain ⟨ns, hsub, htag⟩ := hm
    exact ⟨ns, hsub, ns, fun n hn => hn, htag⟩

end Domain.Neighborhood.Exercise514
