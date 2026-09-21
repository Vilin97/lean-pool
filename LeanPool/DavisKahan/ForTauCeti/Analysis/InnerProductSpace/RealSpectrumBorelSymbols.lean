/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.CStarAlgebra.RealSpectrumFunctionalCalculus
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.CyclicModel

/-!
# The bounded Borel symbol algebra of a self-adjoint operator, on its real spectrum

`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/CyclicModel.lean` builds the cyclic
multiplication model out of `bddSymbols a : Submodule ℂ (spectrum ℂ a → ℂ)`, the bounded
measurable symbols of a **complex** spectral parameter.
`ForTauCeti/Analysis/CStarAlgebra/RealSpectrumFunctionalCalculus.lean` lowers the symbol
*domain* of the **continuous** calculus to `spectrum ℝ a`, keeping the codomain and the
scalars at `ℂ`.

The gap between those two is bounded-Borel versus continuous, not real versus complex:
`bddSymbols` carries an `IsBddMeasurable` predicate on a raw function, and no continuous
calculus can produce it.  This module closes that gap on the symbol side alone.  It defines
the bounded measurable symbols of a **real** spectral parameter and shows the two symbol
modules are `ℂ`-linearly isomorphic by reindexing along `realSpectrumHomeomorph`.

## Why this is only a reindexing

`realSpectrumHomeomorph ha : spectrum ℂ a ≃ₜ spectrum ℝ a` is a homeomorphism of subtypes of
`ℂ` and `ℝ`, and both carry the subspace Borel σ-algebra (`Subtype.borelSpace`).  A
homeomorphism between Borel spaces is measurable in both directions, so `Measurable` is
preserved either way; a uniform bound is preserved by any reindexing whatsoever, being a
statement about the range.  Both halves of `IsBddMeasurable` therefore transport, and the
resulting map on symbols is precomposition, hence `ℂ`-linear on the nose.

Nothing here changes `BorelCalculus/`.  The transported module sits beside it, so that the
rewrite of `cyclicIsometry` and `range_cyclicIsometry` onto a real spectral parameter is a
separate, mechanical step with its own compile budget.

## Main results

* `TauCeti.BorelCalculus.IsRealSpectrumBddMeasurable`: admissibility for the Borel calculus,
  for a symbol of a real spectral parameter.
* `TauCeti.BorelCalculus.realSpectrumBddSymbols`: those symbols as a `ℂ`-submodule, the real
  analogue of `bddSymbols`.
* `TauCeti.BorelCalculus.IsRealSpectrumBddMeasurable.comp_realSpectrumHomeomorph` and
  `TauCeti.BorelCalculus.IsBddMeasurable.comp_realSpectrumHomeomorph_symm`: admissibility is
  preserved in **both** directions across the homeomorphism.
* `TauCeti.BorelCalculus.realSpectrumBddSymbolsEquiv`: **the deliverable** — the `ℂ`-linear
  isomorphism `realSpectrumBddSymbols a ≃ₗ[ℂ] bddSymbols a`, with
  `coe_realSpectrumBddSymbolsEquiv` and `coe_realSpectrumBddSymbolsEquiv_symm` naming its two
  underlying functions.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.); written here, new for
  this library.
* Extraction class: **new**.  The predicate mirrors
  `TauCeti.BorelCalculus.IsBddMeasurable` field for field; the transport is
  `Homeomorph.measurable` in both directions plus a bound that survives reindexing.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

public section

namespace TauCeti
namespace BorelCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

section Predicate

/-- A symbol admissible for the bounded Borel calculus of a self-adjoint operator, written
with a **real** spectral parameter: measurable and bounded.

Field for field this is `TauCeti.BorelCalculus.IsBddMeasurable`; only the domain differs.
The two are not the same predicate and cannot be, since `IsBddMeasurable` is stated at
`spectrum ℂ a → ℂ` and this one at `spectrum ℝ a → ℂ`. -/
structure IsRealSpectrumBddMeasurable (f : spectrum ℝ a → ℂ) : Prop where
  /-- The symbol is measurable for the subspace Borel σ-algebra on `spectrum ℝ a`. -/
  measurable : Measurable f
  /-- The symbol is uniformly bounded, by some nonnegative constant. -/
  exists_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M

namespace IsRealSpectrumBddMeasurable

variable {f g : spectrum ℝ a → ℂ}

omit [CompleteSpace H] in
/-- Sums of admissible real-spectrum symbols are admissible. -/
theorem add (hf : IsRealSpectrumBddMeasurable f) (hg : IsRealSpectrumBddMeasurable g) :
    IsRealSpectrumBddMeasurable (fun x => f x + g x) := by
  obtain ⟨M, hM0, hM⟩ := hf.exists_bound
  obtain ⟨N, hN0, hN⟩ := hg.exists_bound
  refine ⟨hf.measurable.add hg.measurable, M + N, by positivity, fun x => ?_⟩
  exact le_trans (norm_add_le _ _) (add_le_add (hM x) (hN x))

omit [CompleteSpace H] in
/-- Scalar multiples of admissible real-spectrum symbols are admissible. -/
theorem const_smul (c : ℂ) (hf : IsRealSpectrumBddMeasurable f) :
    IsRealSpectrumBddMeasurable (fun x => c * f x) := by
  obtain ⟨M, hM0, hM⟩ := hf.exists_bound
  refine ⟨measurable_const.mul hf.measurable, ‖c‖ * M, by positivity, fun x => ?_⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg c)

end IsRealSpectrumBddMeasurable

/-- **The bounded measurable symbols of a real spectral parameter**, as a `ℂ`-submodule of
all functions on `spectrum ℝ a`.

This is the real-spectrum analogue of `TauCeti.BorelCalculus.bddSymbols`, defined the same
way: the carrier is the admissible symbols, and admissibility is closed under the module
operations. -/
def realSpectrumBddSymbols (a : H →L[ℂ] H) : Submodule ℂ (spectrum ℝ a → ℂ) where
  carrier := {f | IsRealSpectrumBddMeasurable f}
  add_mem' hf hg := hf.add hg
  zero_mem' := ⟨measurable_const, 0, le_rfl, fun _ => by simp⟩
  smul_mem' c _ hf := hf.const_smul c

omit [CompleteSpace H] in
/-- Membership in `realSpectrumBddSymbols` is exactly admissibility. -/
theorem mem_realSpectrumBddSymbols {f : spectrum ℝ a → ℂ} :
    f ∈ realSpectrumBddSymbols a ↔ IsRealSpectrumBddMeasurable f := Iff.rfl

omit [CompleteSpace H] in
/-- The admissibility proof carried by an element of `realSpectrumBddSymbols`.  Consumers
cannot unfold the submodule's carrier, so this is the accessor they use. -/
theorem isRealSpectrumBddMeasurable_coe (f : realSpectrumBddSymbols a) :
    IsRealSpectrumBddMeasurable (f : spectrum ℝ a → ℂ) := mem_realSpectrumBddSymbols.mp f.2

end Predicate

section Transport

/-- The homeomorphism of spectra is measurable: it is continuous, and both subtypes carry
the subspace Borel σ-algebra. -/
theorem measurable_realSpectrumHomeomorph (ha : IsSelfAdjoint a) :
    Measurable (realSpectrumHomeomorph ha) :=
  (realSpectrumHomeomorph ha).continuous.measurable

/-- The inverse homeomorphism of spectra is measurable, for the same reason. -/
theorem measurable_realSpectrumHomeomorph_symm (ha : IsSelfAdjoint a) :
    Measurable (realSpectrumHomeomorph ha).symm :=
  (realSpectrumHomeomorph ha).symm.continuous.measurable

/-- **Admissibility transports forward.**  Reindexing a real-spectrum symbol along
`realSpectrumHomeomorph` gives a symbol admissible for the Borel calculus as
`BorelCalculus/` states it. -/
theorem IsRealSpectrumBddMeasurable.comp_realSpectrumHomeomorph {f : spectrum ℝ a → ℂ}
    (hf : IsRealSpectrumBddMeasurable f) (ha : IsSelfAdjoint a) :
    IsBddMeasurable (f ∘ realSpectrumHomeomorph ha) := by
  obtain ⟨M, hM0, hM⟩ := hf.exists_bound
  exact ⟨hf.measurable.comp (measurable_realSpectrumHomeomorph ha), M, hM0,
    fun z => hM (realSpectrumHomeomorph ha z)⟩

/-- **Admissibility transports backward.**  Reindexing a complex-spectrum symbol along the
inverse homeomorphism gives an admissible real-spectrum symbol.  This is the direction the
refuted route could not supply, and it is available here because the transport moves the
domain and leaves the values alone. -/
theorem IsBddMeasurable.comp_realSpectrumHomeomorph_symm {g : spectrum ℂ a → ℂ}
    (hg : IsBddMeasurable g) (ha : IsSelfAdjoint a) :
    IsRealSpectrumBddMeasurable (g ∘ (realSpectrumHomeomorph ha).symm) := by
  obtain ⟨M, hM0, hM⟩ := hg.exists_bound
  exact ⟨hg.measurable.comp (measurable_realSpectrumHomeomorph_symm ha), M, hM0,
    fun x => hM ((realSpectrumHomeomorph ha).symm x)⟩

/-- Admissibility of a reindexed symbol is equivalent to admissibility of the symbol: the
two transports above are inverse to each other. -/
theorem isBddMeasurable_comp_realSpectrumHomeomorph_iff {f : spectrum ℝ a → ℂ}
    (ha : IsSelfAdjoint a) :
    IsBddMeasurable (f ∘ realSpectrumHomeomorph ha) ↔ IsRealSpectrumBddMeasurable f := by
  refine ⟨fun h => ?_, fun h => h.comp_realSpectrumHomeomorph ha⟩
  have h' := h.comp_realSpectrumHomeomorph_symm ha
  have hfun : (f ∘ realSpectrumHomeomorph ha) ∘ (realSpectrumHomeomorph ha).symm = f :=
    funext fun x => congrArg f ((realSpectrumHomeomorph ha).apply_symm_apply x)
  rwa [hfun] at h'

end Transport

section Equiv

/-- **The real-spectrum symbol algebra is the complex one, reindexed.**

Precomposition with `realSpectrumHomeomorph ha` is a `ℂ`-linear isomorphism from the bounded
measurable symbols of a real spectral parameter onto `bddSymbols a`, with precomposition
along the inverse homeomorphism as its inverse.  Linearity is definitional -- the module
operations on both sides are pointwise -- and bijectivity is the fact that the two
reindexings compose to the identity.

This is the object the cyclic multiplication model needs in order to be restated with a real
spectral parameter: every construction in `BorelCalculus/CyclicModel.lean` that consumes
`bddSymbols a` can consume `realSpectrumBddSymbols a` through this equivalence, with no
change to the Borel calculus itself. -/
noncomputable def realSpectrumBddSymbolsEquiv (ha : IsSelfAdjoint a) :
    realSpectrumBddSymbols a ≃ₗ[ℂ] bddSymbols a where
  toFun f := ⟨(f : spectrum ℝ a → ℂ) ∘ realSpectrumHomeomorph ha,
    mem_bddSymbols.mpr ((isRealSpectrumBddMeasurable_coe f).comp_realSpectrumHomeomorph ha)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun g := ⟨(g : spectrum ℂ a → ℂ) ∘ (realSpectrumHomeomorph ha).symm,
    mem_realSpectrumBddSymbols.mpr
      ((isBddMeasurable_coe g).comp_realSpectrumHomeomorph_symm ha)⟩
  left_inv f := Subtype.ext
    (funext fun x => congrArg (f : spectrum ℝ a → ℂ)
      ((realSpectrumHomeomorph ha).apply_symm_apply x))
  right_inv g := Subtype.ext
    (funext fun z => congrArg (g : spectrum ℂ a → ℂ)
      ((realSpectrumHomeomorph ha).symm_apply_apply z))

private theorem coe_realSpectrumBddSymbolsEquiv_apply_aux (ha : IsSelfAdjoint a)
    (f : realSpectrumBddSymbols a) :
    ((realSpectrumBddSymbolsEquiv ha f : bddSymbols a) : spectrum ℂ a → ℂ)
      = (f : spectrum ℝ a → ℂ) ∘ realSpectrumHomeomorph ha := rfl

/-- The isomorphism is precomposition with `realSpectrumHomeomorph`. -/
@[simp]
theorem coe_realSpectrumBddSymbolsEquiv (ha : IsSelfAdjoint a)
    (f : realSpectrumBddSymbols a) :
    ((realSpectrumBddSymbolsEquiv ha f : bddSymbols a) : spectrum ℂ a → ℂ)
      = (f : spectrum ℝ a → ℂ) ∘ realSpectrumHomeomorph ha :=
  coe_realSpectrumBddSymbolsEquiv_apply_aux ha f

private theorem coe_realSpectrumBddSymbolsEquiv_symm_aux (ha : IsSelfAdjoint a)
    (g : bddSymbols a) :
    (((realSpectrumBddSymbolsEquiv ha).symm g : realSpectrumBddSymbols a) :
        spectrum ℝ a → ℂ)
      = (g : spectrum ℂ a → ℂ) ∘ (realSpectrumHomeomorph ha).symm := rfl

/-- The inverse isomorphism is precomposition with the inverse homeomorphism. -/
@[simp]
theorem coe_realSpectrumBddSymbolsEquiv_symm (ha : IsSelfAdjoint a) (g : bddSymbols a) :
    (((realSpectrumBddSymbolsEquiv ha).symm g : realSpectrumBddSymbols a) :
        spectrum ℝ a → ℂ)
      = (g : spectrum ℂ a → ℂ) ∘ (realSpectrumHomeomorph ha).symm :=
  coe_realSpectrumBddSymbolsEquiv_symm_aux ha g

/-- The value of the isomorphism at a point: the real-spectrum symbol read at the real part
of the complex spectral point. -/
theorem realSpectrumBddSymbolsEquiv_apply_apply (ha : IsSelfAdjoint a)
    (f : realSpectrumBddSymbols a) (z : spectrum ℂ a) :
    ((realSpectrumBddSymbolsEquiv ha f : bddSymbols a) : spectrum ℂ a → ℂ) z
      = (f : spectrum ℝ a → ℂ) (realSpectrumHomeomorph ha z) := by
  rw [coe_realSpectrumBddSymbolsEquiv]
  rfl

end Equiv

end BorelCalculus
end TauCeti
