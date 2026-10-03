/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Local Box

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open Set
open CKN.Foundation.Parabolic


namespace CKN

/-- Compactly interior spatial and time subdomains used by paper label `def:sws`. -/
@[expose]
def localBox (Ω : Set Vec3) (I : Set ℝ) (Ω' : Set Vec3) (J : Set ℝ) : Prop :=
  IsOpen Ω' ∧ IsCompact (closure Ω') ∧ closure Ω' ⊆ Ω ∧
    OrdConnected J ∧ IsCompact (closure J) ∧ closure J ⊆ I

end CKN
