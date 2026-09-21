/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Summit

/-!
# Audit: Deligne's theorem and the unconditional summit

The pinned axiom checks for Deligne’s theorem and the unconditional
summit statements. Each `#guard_msgs`
fails the build if the axiom set changes, so the claim that these
depend on nothing beyond `propext`, `Classical.choice` and
`Quot.sound` is checked rather than asserted.
-/

namespace RS

/-! ### Deligne's theorem -/

/-- info: 'RS.deligne_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.braidedFibreHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.exists_splitting_simple_algebra_doubled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.exists_simple_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-! ### The summit, unconditionally -/

/-- info: 'RS.regts_sevenster' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.regts_sevenster_quant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.regts_sevenster_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.regts_sevenster_characterisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.regts_sevenster_quant_characterisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-! ### Minimum dimensions, growth and padding -/

/-- info: 'RS.minimumColourDimension_le_of_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.TotalBoundedMixedModel.dimension_eq_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.stdModel_dimension_eq_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.stdModel_connectionRank_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.MixedColourEmbedding.mixedPartition_extendColours' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.MixedFunctional.padColours_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.TotalBoundedMixedModel.even_dimension_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.TotalBoundedMixedModel.half_odd_dimension_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.regts_sevenster_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.regts_sevenster_rank_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.regts_sevenster_prescribed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

end RS
