/-
Copyright (c) 2026 Wondermonger-daydreaming. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wondermonger-daydreaming
-/
module

public import LeanPool.SemicircleCheck.ShiftTwoEquiv
public import LeanPool.SemicircleCheck.FinRotateLemmas
public import LeanPool.SemicircleCheck.RotationArithmetic
public import LeanPool.SemicircleCheck.GenusNoncrossing
public import LeanPool.SemicircleCheck.EvenCard
public import LeanPool.SemicircleCheck.CatalanRecurrence
public import LeanPool.SemicircleCheck.Census

/-!
# Genus-Zero Pairings and Catalan Numbers

Source: url:https://github.com/Wondermonger-daydreaming/semicircle-catalan
Authors: Wondermonger-daydreaming
Status: verified
Main declarations: `card_noncrossingPairing_eq_catalan`, `Pairing.genus_zero_count`
Tags: combinatorics, catalan-numbers, noncrossing-partitions
MSC: 05A15, 05A18
-/

@[expose] public section
