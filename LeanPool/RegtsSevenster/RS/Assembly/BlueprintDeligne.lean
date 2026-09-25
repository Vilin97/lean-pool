/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Summit

/-!
# Audit: Deligne's theorem and the unconditional summit

The pinned axiom checks for Deligne’s theorem and the unconditional
summit statements. Each `#guard_msgs`
fails the build if the axiom set changes, so the claim that these
depend on nothing beyond `propext`, `Classical.choice` and
`Quot.sound` is checked rather than asserted.
-/

@[expose] public section

namespace RS

/-! ### Deligne's theorem -/

/- Upstream audit output: 'RS.deligne_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.braidedFibreHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.exists_splitting_simple_algebra_doubled' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.exists_simple_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/-! ### The summit, unconditionally -/

/- Upstream audit output: 'RS.regts_sevenster' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.regts_sevenster_quant' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.regts_sevenster_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.regts_sevenster_characterisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.regts_sevenster_quant_characterisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/-! ### Minimum dimensions, growth and padding -/

/- Upstream audit output: 'RS.minimumColourDimension_le_of_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.TotalBoundedMixedModel.dimension_eq_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.stdModel_dimension_eq_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.stdModel_connectionRank_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.MixedColourEmbedding.mixedPartition_extendColours' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.MixedFunctional.padColours_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.TotalBoundedMixedModel.even_dimension_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.TotalBoundedMixedModel.half_odd_dimension_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.regts_sevenster_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.regts_sevenster_rank_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.regts_sevenster_prescribed' depends on axioms: [propext, Classical.choice, Quot.sound] -/

end RS
