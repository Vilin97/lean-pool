/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import Mathlib.Data.Set.Basic

/-!
# Lecture IV (§4) — Definition 4.5 and Theorem 4.6: models of Peano's Axioms

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19
(1981),
Lecture IV, *Fixed points and recursion*, pages 65–66.

* **Definition 4.5** — a *model for Peano's Axioms* is a structured set `⟨N, 0,
⁺⟩` (a type `N`
  with a distinguished element `0 : N` and a unary `successor` `⁺ : N → N`)
  satisfying:
  (i) `0 ≠ n⁺` for all `n`; (ii) `n⁺ = m⁺ ⟹ n = m` (the successor is injective);
  (iii) **induction**: whenever `x ⊆ N` has `0 ∈ x` and `x⁺ ⊆ x`, then `x = N`.
  We package this as `PeanoModel`, stating (iii) in the equivalent point form
  `0 ∈ s → (∀ n ∈ s, n⁺ ∈ s) → ∀ n, n ∈ s` (`x⁺ ⊆ x` is `∀ n ∈ x, n⁺ ∈ x`; `x = N`
  is
  `∀ n, n ∈ x`).

* **Theorem 4.6** — *all models of Peano's Axioms are isomorphic*
(`peano_models_isomorphic`).
  Scott's proof is an application of the **Fixed-point Theorem 4.1**: between
  models
  `⟨N,0,⁺⟩` and `⟨M,□,#⟩` he forms, on the powerset domain `P(N × M)`, the
  approximable
  operator `u ↦ {(0,□)} ∪ {(n⁺,m#) ∣ (n,m) ∈ u}` and takes its **least fixed
  point** `r`.

  We realize that least fixed point directly as the inductively generated relation
  `Graph`
  (the least set of pairs containing `(0,□)` and closed under `(n,m) ↦ (n⁺,m#)` —
  exactly the
  least fixed point of Scott's monotone operator, by Theorem 4.1). Scott's two
  facts
  (i) `0 r □` and (ii) `n r m ⟹ n⁺ r m#` are the two constructors. We then show
  `Graph` is a
  one-one correspondence: functionality + totality on the right
  (`exists_unique_right`, by
  induction 4.5(iii) using 4.5(i)/(ii) to invert the generating rules) and, by the
  symmetry of
  the construction, on the left (`exists_unique_left`). This yields the
  structure-preserving
  bijection `e : N ≃ M` with `e 0 = □` and `e (n⁺) = (e n)#`.

All of the *content* (the relation `Graph`, the uniqueness lemmas) is
**choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`); only the packaging of the bijection `N
≃ M` from the
functional-and-total relation pulls `Classical.choice`, exactly as a
Dedekind/recursion theorem
must.
-/

namespace Domain.Neighborhood

universe u v

/-- **Definition 4.5 (Scott 1981, PRG-19).** A *model for Peano's Axioms*: a type
`N` with a
distinguished element `zero` and a unary `succ`essor, satisfying

* (i)   `zero ≠ succ n` for all `n`                       (`zero_ne_succ`);
* (ii)  `succ` is injective (`n⁺ = m⁺ ⟹ n = m`)          (`succ_injective`);
* (iii) **mathematical induction**: any `s ⊆ N` with `zero ∈ s` and closed under
`succ`
        (`∀ n ∈ s, succ n ∈ s`, i.e. Scott's `x⁺ ⊆ x`) is all of `N`
        (`∀ n, n ∈ s`, i.e. Scott's `x = N`)              (`induction`). -/
structure PeanoModel (N : Type u) where
  /-- The distinguished zero `0 ∈ N`. -/
  zero : N
  /-- The unary successor `⁺ : N → N`. -/
  succ : N → N
  /-- **4.5(i)** `0 ≠ n⁺`. -/
  zero_ne_succ : ∀ n, zero ≠ succ n
  /-- **4.5(ii)** the successor is one-one. -/
  succ_injective : Function.Injective succ
  /-- **4.5(iii)** the induction principle (point form of `x⁺ ⊆ x ⟹ x = N`). -/
  induction : ∀ (s : Set N), zero ∈ s → (∀ n ∈ s, succ n ∈ s) → ∀ n, n ∈ s

namespace PeanoModel

variable {M : Type u} {N : Type v}

/-- Scott's least fixed point `r ⊆ N × M`, realized as the inductively generated
relation: the
least relation containing `(0, □)` and closed under `(n, m) ↦ (n⁺, m#)`. The two
constructors are
Scott's facts (i) `0 r □` and (ii) `n r m ⟹ n⁺ r m#`. By Theorem 4.1 this *is* the
least fixed
point of the approximable operator `u ↦ {(0,□)} ∪ {(n⁺,m#) ∣ (n,m) ∈ u}` on `P(N ×
M)`. -/
inductive Graph (P : PeanoModel M) (Q : PeanoModel N) : M → N → Prop
  | base : Graph P Q P.zero Q.zero
  | step : ∀ {m n}, Graph P Q m n → Graph P Q (P.succ m) (Q.succ n)

/-- The construction is symmetric in the two models: `Graph P Q m n` swaps to
`Graph Q P n m`.
(This is why the relation is one-one in *both* directions, as Scott notes: "the
rôles of `N` and
`M` are completely symmetric".) -/
theorem Graph.swap {P : PeanoModel M} {Q : PeanoModel N} {m : M} {n : N}
    (h : Graph P Q m n) : Graph Q P n m := by
  induction h with
  | base => exact Graph.base
  | step _ ih => exact Graph.step ih

/-- **Inversion at `0` (uses 4.5(i)).** Anything related to `0` on the left is `□`
on the right:
`0 r k ⟹ k = □`. (The other generating rule would force `0 = n⁺`, impossible by
4.5(i).) -/
theorem graph_zero_right (P : PeanoModel M) (Q : PeanoModel N) {k : N}
    (h : Graph P Q P.zero k) : k = Q.zero := by
  generalize hz : P.zero = z at h
  cases h with
  | base => rfl
  | step _ => exact absurd hz (P.zero_ne_succ _)

/-- **Inversion at a successor (uses 4.5(i)/(ii)).** Anything related to `n⁺` on
the left comes
from a relation `n r n₀` with right value a successor: `n⁺ r k ⟹ ∃ n₀, n r n₀ ∧ k
= n₀#`. -/
theorem graph_succ_right (P : PeanoModel M) (Q : PeanoModel N) {m : M} {k : N}
    (h : Graph P Q (P.succ m) k) : ∃ n, Graph P Q m n ∧ k = Q.succ n := by
  generalize hz : P.succ m = z at h
  cases h with
  | base => exact absurd hz.symm (P.zero_ne_succ _)
  | step h' =>
    rename_i m0 n0
    have hm : m = m0 := P.succ_injective hz
    subst hm
    exact ⟨n0, h', rfl⟩

/-- Each element of the left model is related by `Graph` to exactly one element of
the right
model. Proved by the induction principle 4.5(iii) on the set `{m ∣ ∃! n, m r n}`:
the base case
is the `0`-inversion `graph_zero_right`, the step case the successor-inversion
`graph_succ_right`
together with 4.5(ii). -/
theorem exists_unique_right (P : PeanoModel M) (Q : PeanoModel N) (m : M) :
    ∃! n, Graph P Q m n := by
  refine P.induction {m | ∃! n, Graph P Q m n} ?_ ?_ m
  · exact ⟨Q.zero, Graph.base, fun k hk => graph_zero_right P Q hk⟩
  · rintro m' ⟨n', hn', huniq⟩
    refine ⟨Q.succ n', Graph.step hn', fun k hk => ?_⟩
    obtain ⟨n'', hn'', rfl⟩ := graph_succ_right P Q hk
    rw [huniq n'' hn'']

/-- Dually (by `Graph.swap`), each element of the right model is related to
exactly one element of
the left model. -/
theorem exists_unique_left (P : PeanoModel M) (Q : PeanoModel N) (n : N) :
    ∃! m, Graph P Q m n := by
  obtain ⟨m, hm, huniq⟩ := exists_unique_right Q P n
  exact ⟨m, hm.swap, fun y hy => huniq y hy.swap⟩

/-- **Theorem 4.6 (Scott 1981, PRG-19).** *All models of Peano's Axioms are
isomorphic.* Between
any two models there is a bijection `e : N ≃ M` of the underlying sets that
preserves the
structure: `e 0 = □` and `e (n⁺) = (e n)#`. The bijection is the least-fixed-point
relation
`Graph`, which `exists_unique_right`/`exists_unique_left` show is a one-one
correspondence; the
two structure equations are the constructors `Graph.base`/`Graph.step`. -/
theorem peano_models_isomorphic (P : PeanoModel M) (Q : PeanoModel N) :
    ∃ e : M ≃ N, e P.zero = Q.zero ∧ ∀ m, e (P.succ m) = Q.succ (e m) := by
  classical
  refine ⟨⟨fun m => (exists_unique_right P Q m).choose,
          fun n => (exists_unique_left P Q n).choose, ?_, ?_⟩, ?_, ?_⟩
  · -- left inverse `g ∘ f = id`
    intro m
    have hf : Graph P Q m (exists_unique_right P Q m).choose :=
      (exists_unique_right P Q m).choose_spec.1
    exact ((exists_unique_left P Q _).choose_spec.2 m hf).symm
  · -- right inverse `f ∘ g = id`
    intro n
    have hg : Graph P Q (exists_unique_left P Q n).choose n :=
      (exists_unique_left P Q n).choose_spec.1
    exact ((exists_unique_right P Q _).choose_spec.2 n hg).symm
  · -- `f 0 = □`
    exact ((exists_unique_right P Q P.zero).choose_spec.2 Q.zero Graph.base).symm
  · -- `f (n⁺) = (f n)#`
    intro m
    have hf : Graph P Q m (exists_unique_right P Q m).choose :=
      (exists_unique_right P Q m).choose_spec.1
    exact ((exists_unique_right P Q (P.succ m)).choose_spec.2 _ (Graph.step hf)).symm

end PeanoModel

end Domain.Neighborhood
