/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Exercise413
import LeanPool.DomainTheory.Neighborhood.Exercise415

/-!
# Exercise 4.16 (Scott 1981, PRG-19, Lecture IV) — the *optimal* fixed point

(For fixed-point nuts.) Scott's step (1): for any *non-empty* set `S` of fixed
points of a monotone
`f : |𝒟| → |𝒟|`, the greatest lower bound `⋂S` (Exercise 1.18 `sInf`) satisfies

  `f(⋂S) ⊑ ⋂S`               (`f_sInf_le`)

— indeed `f(⋂S) ⊑ f(s) = s` for each `s ∈ S`, so `f(⋂S)` is a lower bound of `S`.
Being a pre-fixed
point, `⋂S` carries (Exercise 4.13(1)'s `monoFix`) the least fixed point
`optimalFix S` with

  `optimalFix S ⊑ ⋂S ⊑ s`   for every `s ∈ S`   (`optimalFix_le`),

so `optimalFix S` is a fixed point lying **below** every member of `S`, and it is
**consistent** with
each `s ∈ S` (their common upper bound is `s` itself, `optimalFix_consistent`).
Taking `S` to be the
set of *maximal* fixed points (which exist by Exercise 4.15) gives the fixed point
that is below all
the maximal ones, consistent with all other fixed points — Scott's "optimal" fixed
point.

The data (`optimalFix`) is **choice-free**; only the *appeal to* Exercise 4.15 for
the supply of
maximal fixed points is classical.
-/

namespace Domain.Neighborhood

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem

/-- **Exercise 4.16(1) (Scott 1981, PRG-19).** Scott's formula: for a non-empty
set `S` of fixed
points, `f(⋂S) ⊑ ⋂S`. (`f(⋂S) ⊑ f(s) = s` for each `s ∈ S`, then take the glb.) -/
theorem f_sInf_le (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) : f (V.sInf S hS) ≤ V.sInf S hS := by
  apply V.le_sInf
  intro s hsS
  calc f (V.sInf S hS) ≤ f s := hf (V.sInf_le S hS hsS)
    _ = s := hfix s hsS

/-- **Exercise 4.16 (Scott 1981, PRG-19).** The *optimal* fixed point associated
with a non-empty
set `S` of fixed points: the least fixed point sitting below `⋂S` (Exercise
4.13(1) applied to the
pre-fixed point `⋂S`). -/
def optimalFix (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element) (hS : S.Nonempty)
    (hfix : ∀ s ∈ S, f s = s) : V.Element :=
  monoFix f (f_sInf_le f hf S hS hfix)

/-- `optimalFix S` is a fixed point. -/
theorem optimalFix_isFixed (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) :
    f (optimalFix f hf S hS hfix) = optimalFix f hf S hS hfix :=
  monoFix_isFixed f hf _

/-- `optimalFix S ⊑ ⋂S`. -/
theorem optimalFix_le_sInf (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) :
    optimalFix f hf S hS hfix ≤ V.sInf S hS :=
  monoFix_le f _

/-- **Exercise 4.16 (Scott 1981, PRG-19).** `optimalFix S` lies below every member
of `S`. -/
theorem optimalFix_le (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) {s : V.Element} (hs : s ∈ S) :
    optimalFix f hf S hS hfix ≤ s :=
  le_trans (optimalFix_le_sInf f hf S hS hfix) (V.sInf_le S hS hs)

/-- **Exercise 4.16 (Scott 1981, PRG-19).** `optimalFix S` is *consistent* with
every member of `S`
(they share a common upper bound, namely `s` itself). -/
theorem optimalFix_consistent (f : V.Element → V.Element) (hf : Monotone f) (S : Set V.Element)
    (hS : S.Nonempty) (hfix : ∀ s ∈ S, f s = s) {s : V.Element} (hs : s ∈ S) :
    ∃ ub, optimalFix f hf S hS hfix ≤ ub ∧ s ≤ ub :=
  ⟨s, optimalFix_le f hf S hS hfix hs, le_refl s⟩

end NeighborhoodSystem

end Domain.Neighborhood
