/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic

/-!
# Morrey Vec Mem

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey


namespace CKN

/-- Componentwise parabolic Morrey membership used by paper label `def:parabolic-morrey`. -/
@[expose] def morreyVecMem (P τ : ℝ) (S : Set ParabolicPoint)
    (u : ParabolicPoint → Vec3) : Prop :=
  ∀ i : Fin 3,
    morreyBallNorm P τ (S.indicator (fun z => u z i)) < ∞

end CKN
