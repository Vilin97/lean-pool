/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import LeanPool.AharoniKorman.Counterexample

/-!
# Disproof of the Aharoni-Korman Conjecture

Source: url:https://github.com/b-mehta/AharoniKorman
Authors: Bhavik Mehta
Status: verified
Main declarations: `LeanPool.AharoniKorman.aharoni_korman_false`
Tags: order-theory, combinatorics, partial-orders
MSC: 06A06, 06A07
-/

/-!
## Mathematical overview

Formalizes Hollom's disproof of the Aharoni-Korman conjecture, also known as
the fishbone conjecture. The construction defines Hollom's partial order `P_5`
on `Nat^3`, proves it has no infinite antichain, and proves that no chain can
serve as a spine meeting an antichain partition of the whole order.

The final theorem, `aharoni_korman_false`, states that the proposed dichotomy
for arbitrary partially ordered sets is false.

## Provenance

Imported from <https://github.com/b-mehta/AharoniKorman>. Upstream is
Apache-2.0 licensed and contains no `sorry`s. Ported from Lean v4.16.0-rc2 to
Lean Pool's v4.30.0-rc2.
-/
