/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.CDVFBase

/-!
# The noetherian dichotomy: a noetherian valuation ring with an irreducible
is a DVR

([hrw-decomposition] N1 preamble, formalized.)  The valuation ring `𝒪[K]` of a
nontrivially normed ultrametric field is Bézout; if the unit ball is
noetherian it is therefore a PIR, and the existence of an irreducible element
(a uniformizer) rules out the field case.  This upgrades the standing
`(ϖ, hK₀)` hypotheses of the WP campaign to the `[IsDiscreteValuationRing 𝒪[K]]`
instance required by the Tate-algebra Nullstellensatz layer.
-/

@[expose] public section

@[expose] public section

open scoped NormedField Valued

namespace FiniteJetOver

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- **The noetherian dichotomy**: a uniformizer plus a noetherian unit ball
make the valuation ring a DVR. -/
theorem Uniformizer.isDiscreteValuationRing (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    IsDiscreteValuationRing 𝒪[K] := by
  haveI hnoeth : IsNoetherianRing 𝒪[K] :=
    isNoetherianRing_of_ringEquiv _ (unitBallEquivInteger K)
  haveI hpir : IsPrincipalIdealRing 𝒪[K] :=
    ⟨fun I => IsBezout.isPrincipal_of_FG I (IsNoetherian.noetherian I)⟩
  refine { not_a_field' := ?_ }
  intro hbot
  have hmem : ϖ.elem ∈ IsLocalRing.maximalIdeal 𝒪[K] :=
    ϖ.irreducible.not_isUnit
  rw [hbot, Ideal.mem_bot] at hmem
  exact ϖ.irreducible.ne_zero hmem

end FiniteJetOver
