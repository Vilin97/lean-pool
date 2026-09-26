/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaModule

/-!
# The parity shift of a super module

Exchanging the two components of a super module and relabelling
the four action blocks accordingly again gives a super module:
the module parity is only a label, so the eight associativities
permute among themselves and no sign appears.  This is the module
underlying a twist by the odd line.
-/

@[expose] public section

namespace RS

open CategoryTheory

universe u u'

namespace SuperCommAlgebra.Mod

variable {S : SuperCommAlgebra.{u, u'}}

/-- **The parity shift** of a super module. -/
def shift (M : S.Mod) : S.Mod where
  even := M.odd
  odd := M.even
  actEE := M.actEO
  actEO := M.actEE
  actOE := M.actOO
  actOO := M.actOE
  one_act_e := M.one_act_o
  one_act_o := M.one_act_e
  assoc_eee := M.assoc_eeo
  assoc_eeo := M.assoc_eee
  assoc_eoe := M.assoc_eoo
  assoc_eoo := M.assoc_eoe
  assoc_oee := M.assoc_oeo
  assoc_oeo := M.assoc_oee
  assoc_ooe := M.assoc_ooo
  assoc_ooo := M.assoc_ooe

/-- The even component of the shift is the odd component.  This is
definitional, and is stated for use by name: as a `simp` rule it
would rewrite the type arguments of every application of the
shifted module's interface and so stop that interface firing. -/
theorem shift_even (M : S.Mod) : (shift M).even = M.odd :=
  rfl

end SuperCommAlgebra.Mod

end RS
