/-
Copyright (c) 2026 YnirPaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YnirPaz
-/

import LeanPool.PCFTheory.Background
import LeanPool.PCFTheory.ClubGuessing

/-!
# PCF Theory

Source: url:https://github.com/YnirPaz/PCF-Theory
Authors: YnirPaz
Status: verified
Main declarations: `Ordinal.exists_isClubGuessing_of_cof_uncountable`
Tags: set-theory, cardinal-arithmetic, club-guessing
MSC: 03E04, 03E10, 03E55
-/

/-!
## Mathematical overview

A formalization of foundational results from Shelah's Possible Cofinality (PCF)
theory, following article 14, "Cardinal Arithmetic", in the *Handbook of Set
Theory*.

The project sets up the basic theory of clubs (closed and unbounded sets) and
stationary sets below an ordinal, and uses it to prove a fundamental
*club-guessing* existence result.

## Main results

- `Ordinal.IsClub` and `Ordinal.Club`: clubs below an ordinal.
- `Ordinal.IsStationary`: stationary sets.
- `Ordinal.IsClub.sInter`, `IsClub.iInter`, `IsClub.diagInter`: intersection
  results showing that small intersections and diagonal intersections of clubs
  are again clubs.
- `Ordinal.IsClubGuessing`: definition of a club-guessing sequence.
- `Ordinal.exists_isClubGuessing_of_cof_uncountable` (Handbook theorem 2.17):
  let `Ϟ` be an ordinal and `S` a stationary subset of `Ϟ` whose elements all
  have a common uncountable cofinality `κ` with `succ κ < Ϟ.cof`. Then there
  exists a club-guessing sequence on `S`.

## Provenance

Imported from <https://github.com/YnirPaz/PCF-Theory>; ported from
Lean v4.18.0-rc1 to Lean Pool's v4.30.0-rc2.
-/
