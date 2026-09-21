/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.TheoremForward
import LeanPool.RegtsSevenster.RS.Classical.Interfaces.TotalDimension

/-!
# The total-dimension Regts–Sevenster theorem

The reconstructed standard model has at most `R` colours in total.
The extraction and graph-evaluation proof are those of the forward
theorem; the dimension bound comes from the polynomial commutant
estimate for the full signed colour action.
-/

namespace RS

open CategoryTheory

/-- The Regts–Sevenster theorem with `k + 2 * ℓ ≤ R`, conditional
on Deligne's theorem alone. -/
theorem regts_sevenster_total_deligne_only
    (hDeligne : DeligneTheoremStatement.{1, 1}) :
    RegtsSevensterStatementTotal := by
  intro R f
  obtain ⟨P⟩ := skein_delignePackage f hDeligne
  obtain ⟨k, ℓ, e, e', he'e, hee', hform, hcopair⟩ :=
    skein_std_model f P
  refine ⟨{
    k := k
    ℓ := ℓ
    functional := hRS f P e'
    dimension_le := ?_
    partition_eq := fun W => parameter_eq_mixedPartition
      f P e e' W hee' he'e hform hcopair
  }⟩
  exact stdModel_total_dimension_le f P
    { hom := e, inv := e', hom_inv_id := he'e, inv_hom_id := hee' }

end RS
