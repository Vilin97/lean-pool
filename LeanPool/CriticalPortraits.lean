/-
Copyright (c) 2026 Keston Aquino-Michaels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keston Aquino-Michaels
-/
module

public import LeanPool.CriticalPortraits.CycleLemma
public import LeanPool.CriticalPortraits.Core
public import LeanPool.CriticalPortraits.Denominator
public import LeanPool.CriticalPortraits.Portraits
public import LeanPool.CriticalPortraits.Forward
public import LeanPool.CriticalPortraits.Injectivity
public import LeanPool.CriticalPortraits.Surjectivity
public import LeanPool.CriticalPortraits.Census

/-!
# Counting Critical Portraits

Source: doi:10.5281/zenodo.20737896
Authors: Keston Aquino-Michaels
Status: verified
Main declarations: `CriticalPortraits.card_portraits`, `CriticalPortraits.Cycle.cycle_lemma`
Tags: combinatorics, cycle-lemma, critical-portraits, enumeration
MSC: 05A15, 37F20
-/

@[expose] public section

/-!
# Full all-`d` proof of `census = C(N,d−1)/d` (Mathlib)

Aggregator root. Positions are `ZMod N` (`N = d*m`); `level i = i.val / m`,
`fiber i = i.val % m`. A `(d−1)`-subset is **level-canonical** iff `#{i ∈ S : level i ≤ j} ≤ j`
for all `j < d`.

Submodules:
* `CriticalPortraits.CycleLemma`  — the cycle lemma (Raney, sum = 1), sorry-free.
* `CriticalPortraits.Core`        — `level` / `fiber` / `LevelCanonical` + the count **numerator**
                              `#{(d−1)-subsets of Z_N} = C(N, d−1)`.
* `CriticalPortraits.Denominator` — the `/d` **denominator**: the free `ZMod d` rotation +
                              cycle-lemma bridge give `d · #{canonical} = C(N, d−1)`, hence
                              `#{canonical} = C(N, d−1) / d`.
* `CriticalPortraits.Portraits`   — the geometric **foundation**: `IsCriticalSet` / `Unlinked` /
                              `Portrait` / the delete-min map `T`, with the weight identity
                              `#T(P) = d − 1` proved.  Model is faithful to the verified census.
-/
