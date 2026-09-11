/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import LeanPool.Shannon1948Formalization.Entropy
import Mathlib.Tactic.Positivity.Finset

/-!
# Shannon Entropy Characterization

Source: doi:10.1002/j.1538-7305.1948.tb01338.x
Authors: Samuel Schlesinger
Status: verified
Main declarations: `LeanPool.Shannon1948Formalization.entropyNat_unique`
Tags: information-theory, entropy, probability
MSC: 94A17, 60C05
-/

@[expose] public section

/-!
# Shannon

Project entrypoint.
Re-exports the entropy characterization development.
-/
