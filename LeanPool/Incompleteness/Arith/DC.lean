/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arith.First
import LeanPool.Incompleteness.Arith.Second
import LeanPool.Incompleteness.DC.Basic

/-! # DC -/


noncomputable section «lp_nc_section_1»

open LO.FirstOrder.DerivabilityCondition

namespace LO
namespace FirstOrder
namespace Arith

open LO.Arith LO.Arith.Formalized

variable (T : Theory ℒₒᵣ) [𝐈Sg1 wkn T]

variable (U : Theory ℒₒᵣ) [U.Delta1Definable] [ℕ ⊧ₘ* U] [𝐑₀ wkn U]

instance : Diagonalization T where
  fixpoint := fixpoint
  diag θ := diagonal θ

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.FirstOrder.Theory.standardDP : ProvabilityPredicate T U where
  prov := U.provableₐ
  spec := provableₐ_D1

instance : (Theory.standardDP T U).HBL2 := ⟨provableₐ_D2⟩
instance : (Theory.standardDP T U).HBL3 := ⟨provableₐ_D3⟩
instance : (Theory.standardDP T U).HBL := ⟨⟩
instance : (Theory.standardDP T U).GoedelSound :=
  ⟨fun h ↦ by simpa [provable₀_iff] using provableₐ_sound h⟩

end Arith
end FirstOrder
end LO

end «lp_nc_section_1»
