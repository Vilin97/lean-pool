/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Exercise621

/-!
# Exercise 6.22 (Scott 1981, PRG-19, §6) — commenting on three domain equations

> **EXERCISE 6.22.** Comment on these domain equations:
> `N ≅ {{0}, {0, Λ}} ⊕ N`,
> `M ≅ {{Λ}} + M`,
> `N* ≅ N ⊕ (N ⊗ N*)`.

This is a *"comment on"* exercise, so the substantive formal content is to
recognise each equation as
an instance of the fixed-point machinery built in Exercises 6.19–6.21. Every
right-hand side is a
construct `T(X)` of the algebra `GExpr` (constants, identity, `+`, `×`, `⊕`, `⊗`),
whose constants are
**rooted** (contain `Λ`). Hence by `gExists_singleton_subsystem` (Exercise
6.21/6.20) there is a token
set `Γ` with `Γ = tok(T({Γ}))`, so `{Γ} ◁ T({Γ})` and **Theorem 6.14 applies**:
each equation has a
solution.

## What the three domains *are* (the "comment")

* `N ≅ {{0},{0,Λ}} ⊕ N`. The constant `{{0},{0,Λ}}` is the **two-point domain** (a
chain `{0} ⊏ Δ`,
  i.e. one proper point above the bottom). Folding it under the **coalesced** sum
  `⊕` — which
  *identifies* the bottoms at each stage — stacks the proper points into a single
  chain. So `N` is the
  domain of **vertical natural numbers**: a chain `⊥ ⊑ 0 ⊑ 1 ⊑ ⋯` topped by a
  limit `∞`.
* `M ≅ {{Λ}} + M`. The constant `{{Λ}}` is the **one-point domain** `𝟙` (the
terminal object). Folding
  it under the **separated** sum `+` — which keeps the two bottoms *apart*,
  offering a genuine
  stop/continue choice at each step — yields the **lazy natural numbers**: each
  `n` is a distinct
  partial element `succⁿ(stop)`, with `⊥` below every finite stage and one
  infinite element. The only
  difference from `N` is coalesced vs. separated: `⊕` collapses the choice into a
  chain, `+` keeps it
  branching.
* `N* ≅ N ⊕ (N ⊗ N*)`. With the **smash** product `⊗` (strict pairing: a pair is
`⊥` unless *both*
  coordinates are proper) and the coalesced `⊕`, this is the cons-cell equation `X
  ≅ N ⊕ (N ⊗ X)`: an
  element is either a single datum from `N` or a strict head/tail pair. So `N*` is
  the domain of
  **finite and infinite strict sequences (streams) over `N`**.

All three solutions are obtained uniformly below; the only per-equation work is
exhibiting the
constant systems `{{0},{0,Λ}}`, `{{Λ}}` and checking they are `∅`-free and rooted.
Everything is
**choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap Domain.Neighborhood.Exercise619
open Domain.Neighborhood.Example62 Domain.Neighborhood.ExampleB

namespace Exercise619

/-! ## The two constant domains -/

/-- **The two-point generator `{{0},{0,Λ}}`.** Its tokens are `Δ = {0,Λ}`, with
the one proper
neighbourhood `{0}` sitting strictly below the master `{0,Λ} = Δ`. As a domain
this is the chain
`{0} ⊏ Δ` (one point above the bottom). Here `0 = [false]` and `Λ = []`. -/
def Cnat : ScottSys where
  sys :=
    { mem := fun X => X = {([false] : Str)} ∨ X = {([false] : Str), ([] : Str)}
      master := {([false] : Str), ([] : Str)}
      master_mem := Or.inr rfl
      inter_mem := by
        have hAB : ({([false] : Str)} : Set Str) ⊆ {([false] : Str), ([] : Str)} :=
          Set.singleton_subset_iff.mpr (Set.mem_insert _ _)
        rintro X Y Z (rfl | rfl) (rfl | rfl) _ _
        · exact Or.inl (Set.inter_self _)
        · exact Or.inl (Set.inter_eq_self_of_subset_left hAB)
        · exact Or.inl (Set.inter_eq_self_of_subset_right hAB)
        · exact Or.inr (Set.inter_self _)
      sub_master := by
        simp_all }
  ne := by
    simp_all

/-- `Λ ∈ tok(Cnat)`, so `Cnat` is a rooted constant. -/
theorem nil_mem_Cnat : ([] : Str) ∈ Cnat.sys.master := Set.mem_insert_iff.mpr (Or.inr rfl)

/-- **The one-point domain `{{Λ}} = 𝟙`** (the terminal object of Scott's
category). -/
def Cone : ScottSys := singletonSys ({([] : Str)} : Set Str) ⟨[], rfl⟩

/-- `Λ ∈ tok(Cone)`. -/
theorem nil_mem_Cone : ([] : Str) ∈ Cone.sys.master := rfl

/-! ## The three domain equations as `GExpr` constructs -/

/-- `T(X) = {{0},{0,Λ}} ⊕ X` — the right-hand side of `N ≅ {{0},{0,Λ}} ⊕ N`. -/
def NExpr : GExpr := .oplus (.const Cnat) .var

/-- `T(X) = {{Λ}} + X` — the right-hand side of `M ≅ {{Λ}} + M`. -/
def MExpr : GExpr := .sum (.const Cone) .var

/-- `T(X) = N ⊕ (N ⊗ X)` — the right-hand side of `N* ≅ N ⊕ (N ⊗ N*)`,
parametrised by the (rooted)
datum domain `N`. -/
def NStarExpr (N : ScottSys) : GExpr := .oplus (.const N) (.otimes (.const N) .var)

theorem NExpr_rooted : NExpr.RootedConst := ⟨nil_mem_Cnat, trivial⟩

theorem MExpr_rooted : MExpr.RootedConst := ⟨nil_mem_Cone, trivial⟩

theorem NStarExpr_rooted {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master) :
    (NStarExpr N).RootedConst := ⟨hN, hN, trivial⟩

/-! ## Each equation has a solution (`Γ = tok(T({Γ}))`, so `{Γ} ◁ T({Γ})` and 6.14
applies) -/

/-- **`N ≅ {{0},{0,Λ}} ⊕ N` has a solution.** There is `Γ` (the vertical naturals'
token set) with
`Γ = tok(NExpr({Γ}))`, so `{Γ} ◁ NExpr({Γ})` and Theorem 6.14 applies. -/
theorem N_eq_solution :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ (NExpr.obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem NExpr NExpr_rooted

/-- **`M ≅ {{Λ}} + M` has a solution** (the lazy naturals). -/
theorem M_eq_solution :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ (MExpr.obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem MExpr MExpr_rooted

/-- **`N* ≅ N ⊕ (N ⊗ N*)` has a solution** for any rooted datum domain `N` (the
strict streams over
`N`). -/
theorem NStar_eq_solution (N : ScottSys) (hN : ([] : Str) ∈ N.sys.master) :
    ∃ (Γ : Set Str) (h : Γ.Nonempty),
      (singletonSys Γ h).sys ◁ ((NStarExpr N).obj (singletonSys Γ h)).sys :=
  gExists_singleton_subsystem (NStarExpr N) (NStarExpr_rooted hN)

/-- **Chaining the equations.** The solution `N` to the first equation is itself a
rooted domain
(`Λ ∈ tok(N)`, since its token set is the fixed point `Γ₁ ∋ Λ`), so it is a
legitimate datum domain
for the third: `N*` exists *over the very `N` produced by* `N ≅ {{0},{0,Λ}} ⊕ N`. -/
theorem NStar_over_N_exists :
    ∃ N : ScottSys, ([] : Str) ∈ N.sys.master ∧
      ∃ (Γ : Set Str) (h : Γ.Nonempty),
        (singletonSys Γ h).sys ◁ ((NStarExpr N).obj (singletonSys Γ h)).sys := by
  obtain ⟨Γ₁, hnil₁, _⟩ := gExists_tok_fixedPoint NExpr NExpr_rooted
  exact ⟨singletonSys Γ₁ ⟨[], hnil₁⟩, hnil₁, NStar_eq_solution _ hnil₁⟩

end Exercise619

end Domain.Neighborhood
