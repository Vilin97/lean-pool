/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Real.RealCyclicDecomposition
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.MultiplicityModelReal

/-!
# Real Hahn--Hellinger: the existence of a real multiplicity model

Every bounded self-adjoint operator on a **separable real** Hilbert space is unitarily
equivalent, over `ℝ`, to multiplication by the (truncated) spectral coordinate on the real `L²`
space of a `TauCeti.MultiplicityDatum ℝ`.

This is the existence half of Hahn--Hellinger over `ℝ`, which Mathlib has for no scalar field.
It is assembled here from three pieces that are each proved elsewhere:

1. `exists_countable_isHilbertSum_lp_diagMeasure_real` -- the conjugation-equivariant cyclic
   decomposition of the complexification, with every cyclic vector drawn from the real copy;
2. `TauCeti.BorelCalculus.exists_hasMultiplicityModel_star` -- complex Hahn--Hellinger run so
   that the *whole chain* of unitaries is `star`-equivariant, plus the observation that a
   self-adjoint operator has real spectrum, so the resulting base measure is carried by the real
   axis;
3. `TauCeti.operatorUnitaryEquiv_retype_real_of_starOperatorUnitaryEquiv` -- the descent of a
   `star`-equivariant unitary equivalence to the fixed points of the two conjugations.

## Why the equivariance is the whole content

Descending an *arbitrary* unitary equivalence is genuinely obstructed, and not for a Lean
reason: a unitary intertwining two operators is unique only up to the commutant of either, so
nothing forces a given witness to commute with the conjugations, and a witness that does not
commute with them does not restrict to the real forms at all.  What descends is the **model**,
once every step of its construction has been made equivariant.  That is why
`TauCeti.StarOperatorUnitaryEquiv` -- which remembers its unitary -- exists, and why
`TauCeti.OperatorUnitaryEquiv`, which forgets it, cannot be used at any link of the chain.

## What is *not* claimed

Nothing here says the real datum is unique, and nothing here builds a datum whose base measure
lives on `ℝ`.  The base measure remains a `Measure ℂ`; what the construction delivers is that it
is carried by the real axis (`TauCeti.MultiplicityDatum.starFixedInvariant_iff_base_im_eq_zero`
is the reason that matters), and reality of the base is a *hypothesis* of the descent, never a
field of the datum.
-/

@[expose] public section

open MeasureTheory

namespace TauCeti
namespace DavisKahan
namespace RealSpectralRestriction

open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification

noncomputable section

universe v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {T : E →L[ℝ] E}

/-- **Every bounded self-adjoint operator on a separable real Hilbert space has a real
multiplicity model.**  This is the existence half of Hahn--Hellinger over `ℝ`.

The datum is a `TauCeti.MultiplicityDatum ℝ`, so its `operator` acts on `Lp ℝ 2` and the
equivalence is a *real* unitary equivalence; its base measure and level sets -- the entire
multiplicity content -- are those of the complex model, unchanged
(`TauCeti.MultiplicityDatum.retype_base`, `TauCeti.MultiplicityDatum.retype_level`). -/
theorem exists_hasMultiplicityModel_real [TopologicalSpace.SeparableSpace E]
    (hT : IsSelfAdjoint T) :
    ∃ D : TauCeti.MultiplicityDatum ℝ, TauCeti.OperatorUnitaryEquiv T D.operator := by
  have : TopologicalSpace.SeparableSpace (RealComplexification E) :=
    separableSpace_realComplexification (E := E)
  obtain ⟨ξ, -, -, hsum, hstar⟩ :=
    exists_countable_isHilbertSum_lp_diagMeasure_real (E := E) (T := T) hT
  obtain ⟨D, hbase, hequiv⟩ :=
    TauCeti.BorelCalculus.exists_hasMultiplicityModel_star
      (isSelfAdjoint_complexify_bounded hT).isStarNormal
      (isSelfAdjoint_complexify_bounded hT)
      (conjugation (E := E)).continuous
      (fun x y => map_add (conjugation (E := E)) x y) hsum hstar
  exact ⟨D.retype ℝ, TauCeti.operatorUnitaryEquiv_retype_real_of_starOperatorUnitaryEquiv hbase
    (fun x => ofReal x) re (fun x y => map_add (ofReal (E := E)) x y)
    (fun c x => by
      rw [coe_real_smul]
      exact map_smul (ofReal (E := E)) c x)
    (fun x => (ofReal (E := E)).norm_map x)
    (fun x => conjugation_ofReal x) (fun _ hy => ofReal_re_of_conjugation_fixed hy)
    (fun x => complexify_ofReal T x) hequiv⟩

end

end RealSpectralRestriction
end DavisKahan
end TauCeti
