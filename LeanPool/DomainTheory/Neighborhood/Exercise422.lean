/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Exercise414
import LeanPool.DomainTheory.Neighborhood.Theorem46

/-!
# Exercise 4.22 (Scott 1981, PRG-19, Lecture IV) — carving a Peano model out of a
partial one

Suppose `N*` is a structured set `⟨N*, 0, ⁺⟩` satisfying **only** axioms (i) and
(ii) of
Definition 4.5 — i.e. `0 ≠ n⁺` (zero is not a successor) and `⁺` is injective —
but *not necessarily*
the induction axiom (iii). **Must there be a subset `N ⊆ N*` that satisfies (i),
(ii), and (iii)?**

**Yes.** Following Scott's hint, take the **least fixed point in `P(N*)`**
(Exercise 4.14 / 4.13(2),
the dual Knaster–Tarski over the complete lattice `P(N*)`) of the monotone
operator

  `g(x) = {0} ∪ x⁺ = {0} ∪ {n⁺ ∣ n ∈ x}`.

This least fixed point `nats` is the smallest subset of `N*` containing `0` and
closed under `⁺`
(`zero_mem_nats`, `succ_mem_nats`). On the subtype `N = {m // m ∈ nats}`:

* (i) `0 ≠ n⁺` and (ii) `⁺` injective are **inherited** from `N*`;
* (iii) **induction** holds *by minimality* of the least fixed point: a subset of
`N` closed under
  `0`/`⁺` pulls back to a pre-fixed point of `g` in `P(N*)`, which therefore
  contains `nats`.

So `⟨N, 0, ⁺⟩` is a genuine model of Peano's Axioms (`peanoSub`), giving
`exists_peano_submodel`.

*(For set theorists.)* The existence of such an `N*` at all is guaranteed by the
**axiom of
infinity**: the standard `⟨ℕ, 0, ⁺⟩` is one (`PeanoModel ℕ`, recorded as
`natPeano`), and indeed it
already satisfies (iii), so it is its own carved-out model.

The subset `nats` is built choice-free (`lfpSet`); the `PeanoModel` packaging of
`peanoSub` and the
existence statement live over `Classical.choice` exactly as Theorem 4.6's
bijection does.
-/

namespace Domain.Neighborhood.Exercise422

open Domain.Neighborhood Domain.Neighborhood.Exercise414

variable {M : Type*} (zero : M) (succ : M → M)

/-- Scott's operator `g(x) = {0} ∪ x⁺` on `P(N*)`, whose least fixed point is the
smallest subset
containing `0` and closed under the successor. -/
def genOp (x : Set M) : Set M := {zero} ∪ succ '' x

theorem genOp_monotone : Monotone (genOp zero succ) := by
  intro x y hxy z hz
  rcases hz with hz | ⟨a, ha, rfl⟩
  · exact Or.inl hz
  · exact Or.inr ⟨a, hxy ha, rfl⟩

/-- The carved-out subset `N ⊆ N*`: the least fixed point of `g` (Exercise
4.13(2)/4.14). -/
def nats : Set M := lfpSet (genOp zero succ)

theorem genOp_nats : genOp zero succ (nats zero succ) = nats zero succ :=
  lfpSet_isFixed (genOp zero succ) (genOp_monotone zero succ)

/-- `0 ∈ N` — directly from the `lfpSet` definition (no monotonicity needed),
keeping the
construction choice-free. -/
theorem zero_mem_nats : zero ∈ nats zero succ := by
  intro x hx
  exact hx (Or.inl rfl)

/-- `N` is closed under the successor: `n ∈ N ⟹ n⁺ ∈ N` — again directly from
`lfpSet`. -/
theorem succ_mem_nats {n : M} (hn : n ∈ nats zero succ) : succ n ∈ nats zero succ := by
  intro x hx
  exact hx (Or.inr ⟨n, hn x hx, rfl⟩)

/-- **Induction by minimality.** Any subset `s ⊆ N*` containing `0` and closed
under `⁺` contains
all of `N`. (This is the heart of axiom (iii): `s` is a pre-fixed point of `g`,
hence dominates the
least fixed point `nats`.) -/
theorem nats_induction (s : Set M) (h0 : zero ∈ s) (hsucc : ∀ n ∈ s, succ n ∈ s) :
    nats zero succ ⊆ s := by
  apply lfpSet_subset (genOp zero succ)
  rintro x (rfl | ⟨n, hn, rfl⟩)
  · exact h0
  · exact hsucc n hn

/-! ### The carved-out structure is a model of Peano's Axioms. -/

/-- The subtype `N = {m // m ∈ nats}` carrying the carved-out Peano structure. -/
abbrev Nat' : Type _ := {m : M // m ∈ nats zero succ}

/-- The zero of the subtype. -/
def subZero : Nat' zero succ := ⟨zero, zero_mem_nats zero succ⟩

/-- The successor of the subtype (well-defined by closure `succ_mem_nats`). -/
def subSucc (n : Nat' zero succ) : Nat' zero succ := ⟨succ n.1, succ_mem_nats zero succ n.2⟩

/-- **Exercise 4.22 (Scott 1981, PRG-19).** The carved-out subset `N ⊆ N*`, with
the inherited
`0` and `⁺`, is a model of **all three** Peano axioms — even though `N*` was only
assumed to satisfy
(i) and (ii). Axioms (i)/(ii) are inherited; (iii) holds by minimality of the
least fixed point. -/
def peanoSub (hzero : ∀ n, zero ≠ succ n) (hinj : Function.Injective succ) :
    PeanoModel (Nat' zero succ) where
  zero := subZero zero succ
  succ := subSucc zero succ
  zero_ne_succ n h := hzero n.1 (Subtype.ext_iff.mp h)
  succ_injective a b h := Subtype.ext (hinj (Subtype.ext_iff.mp h))
  induction s h0 hstep := by
    -- pull `s` back to a subset of `N*`, show it is closed under `0`/`⁺`, apply
    -- `nats_induction`
    intro n
    have hsub : nats zero succ ⊆
        {m | ∃ h : m ∈ nats zero succ, (⟨m, h⟩ : Nat' zero succ) ∈ s} := by
      apply nats_induction zero succ
      · exact ⟨zero_mem_nats zero succ, h0⟩
      · rintro m ⟨hmnat, hms⟩
        exact ⟨succ_mem_nats zero succ hmnat, hstep ⟨m, hmnat⟩ hms⟩
    obtain ⟨_, hns⟩ := hsub n.2
    exact hns

/-- **Exercise 4.22 (Scott 1981, PRG-19).** *Yes:* whenever `N*` satisfies (i) and
(ii), there is a
subset `N ⊆ N*` (carrying the inherited structure) satisfying (i), (ii), and
(iii). -/
theorem exists_peano_submodel (hzero : ∀ n, zero ≠ succ n) (hinj : Function.Injective succ) :
    Nonempty (PeanoModel (Nat' zero succ)) :=
  ⟨peanoSub zero succ hzero hinj⟩

/-! ### Existence of `N*` (axiom of infinity): the standard `ℕ`. -/

/-- *(For set theorists.)* The standard natural numbers `⟨ℕ, 0, ⁺⟩` form a model
of Peano's Axioms;
their existence is the **axiom of infinity**. (This witnesses that an `N*`
satisfying (i)/(ii) — in
fact all three — exists in the first place.) -/
def natPeano : PeanoModel ℕ where
  zero := 0
  succ := Nat.succ
  zero_ne_succ n := (Nat.succ_ne_zero n).symm
  succ_injective := Nat.succ_injective
  induction s h0 hstep := by
    intro n
    induction n with
    | zero => exact h0
    | succ k ih => exact hstep k ih

end Domain.Neighborhood.Exercise422
