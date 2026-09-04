/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.ModelTheory.HanfSpectrum.VonNeumannModel
import LeanPool.InfinitaryLogic.ModelTheory.HanfSpectrum.LadderBound
import LeanPool.InfinitaryLogic.ModelTheory.MorleyHanf
/-!
# The beth ladder: sharpness of the Morley–Hanf bound

The assembly of Marker's Exercise 5.3 ladder: for every `α < ω₁` the ladder sentence has the
von Neumann model of size exactly `ℶ_{α+1}` (`VonNeumannModel.lean`) and no larger models
(`LadderBound.lean`), so through the generic bounded-spectrum endpoint each `ℶ_{α+1}` is a
strict lower bound for the global Hanf number; the successor-cofinal supremum
(`CardinalBounds.lean`) then gives `ℶ_{ω₁} ≤ Hanf(L_{ω₁ω})`. Combined with the Morley–Hanf
upper bound `Lomega1omegaHanfNumber_le_beth_omega1`:

* `Lomega1omegaHanfNumber_eq_beth_omega1` — **`Hanf(L_{ω₁ω}) = ℶ_{ω₁}`**, the exact Hanf
  number of `L_{ω₁ω}` over `Language.{0,0}`.

Reference: Marker, *Lectures on Infinitary Model Theory*, Exercise 5.3 and Theorem 5.4.
-/

namespace FirstOrder

namespace Language

open _root_.FirstOrder.Language.HanfLadder

/-- **The per-stage sharpness step**: for every `α < ω₁`, the ladder sentence has maximal
model size exactly `ℶ_{α+1}`, so `ℶ_{α+1} < Lomega1omegaHanfNumber`. -/
theorem beth_add_one_lt_Lomega1omegaHanfNumber {α : Ordinal.{0}}
    (hα : α < Ordinal.omega 1) :
    Cardinal.beth (α + 1) < Lomega1omegaHanfNumber := by
  have : Countable (Index α) := countable_index_of_lt_omega1 hα
  let := vStructure α
  refine lt_Lomega1omegaHanfNumber_of_maximal_model
    ⟨VCarrier α, inferInstance,
      realize_ladderSentence_iff.mpr (vStructure_isLadderModel α), (mk_vCarrier α).ge⟩
    (fun M instM hM => mk_le_beth_of_isLadderModel (realize_ladderSentence_iff.mp hM))

/-- The lower half of the Hanf-number computation: `ℶ_{ω₁} ≤ Lomega1omegaHanfNumber`, by the
successor-cofinal supremum over the ladder stages. -/
theorem beth_omega1_le_Lomega1omegaHanfNumber :
    Cardinal.beth (Ordinal.omega 1) ≤ Lomega1omegaHanfNumber := by
  rw [← FirstOrder.HanfLadder.iSup_beth_add_one_omega1]
  exact ciSup_le' fun α => (beth_add_one_lt_Lomega1omegaHanfNumber α.2).le

/-- **The Hanf number of `L_{ω₁ω}` is exactly `ℶ_{ω₁}`** (Morley; Marker, Theorem 5.4): the
Morley–Hanf upper bound `morley_hanf` is sharp. -/
theorem Lomega1omegaHanfNumber_eq_beth_omega1 :
    Lomega1omegaHanfNumber = Cardinal.beth (Ordinal.omega 1) :=
  le_antisymm Lomega1omegaHanfNumber_le_beth_omega1 beth_omega1_le_Lomega1omegaHanfNumber

end Language

end FirstOrder
