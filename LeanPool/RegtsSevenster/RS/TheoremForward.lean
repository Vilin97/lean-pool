/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ReindexHeart
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.EnvDelignePackage

/-!
# The Regts–Sevenster theorem, forward direction

The forward direction conditional on Deligne's theorem. The
factorial trace obstruction supplies semisimplicity and abelianness
of the envelope from the connection-rank bound, without a Schur
package. The resulting fibre functor provides the mixed model.
-/

@[expose] public section

namespace RS

open CategoryTheory

/-- **THE REGTS–SEVENSTER THEOREM, CONDITIONAL ON DELIGNE
ALONE**: the factorial trace obstruction verifies the envelope
hypotheses, and Deligne's fibre functor reconstructs a mixed
partition function. -/
theorem regts_sevenster_deligne_only
    (hDeligne : DeligneTheoremStatement.{1, 1}) :
    RegtsSevensterStatement := by
  intro R f
  obtain ⟨P⟩ := skein_delignePackage f hDeligne
  obtain ⟨k, ℓ, e, e', he'e, hee', hform, hcopair⟩ :=
    skein_std_model f P
  refine ⟨k, ℓ, hRS f P e', fun W => ?_⟩
  exact parameter_eq_mixedPartition f P e e' W
    hee' he'e hform hcopair

end RS
