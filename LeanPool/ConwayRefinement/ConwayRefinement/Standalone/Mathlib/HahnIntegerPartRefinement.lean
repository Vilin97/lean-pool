/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.Order.Module.HahnEmbedding
public import Mathlib.RingTheory.HahnSeries.Cardinal
public import Mathlib.SetTheory.Cardinal.Regular

/-!
# Refinement over saturated exponent groups

An uncountably saturated ordered rational vector space gives four-factor refinement in the
cardinal-bounded generalised-power-series integer part with integer constant coefficients.
-/

public noncomputable section

open Cardinal

namespace ConwayRefinement.Standalone.Hahn

universe u v

variable {G : Type u} {R : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Field R]

/-- The cardinal-bounded integer part
`ℤ + {x : R((G)) | supp(x) ⊆ G^{<0} and #supp(x) < κ}`. -/
abbrev integerHahnPart (κ : Cardinal.{u}) : Set (HahnSeries G R) :=
  {x | x.cardSupp < κ ∧ x.support ⊆ Set.Iic 0 ∧ ∃ z : ℤ, (z : R) = x.coeff 0}

/-- The ordered set `G` is `κ`-saturated. -/
abbrev IsKappaSaturated (κ : Cardinal.{u}) : Prop :=
  ∀ L R : Set G, #L < κ → #R < κ →
    (∀ l ∈ L, ∀ r ∈ R, l < r) →
      ∃ x : G, (∀ l ∈ L, l < x) ∧ ∀ r ∈ R, x < r

/-- **Four-factor refinement over a saturated exponent group.** Let `κ` be regular and
uncountable, let `G` be a `κ`-saturated ordered rational vector space, and let `R` be a field of
characteristic zero. Every equality `a * b = c * d` in
`ℤ + R((G^{<0}))_κ` has four-factor refinement. -/
abbrev HahnIntegerPartRefinement
    : Prop :=
  ∀ (κ : Cardinal.{u}), ℵ₀ < κ → κ.IsRegular → IsKappaSaturated (G := G) κ →
    ∀ a b c d : HahnSeries G R,
      a ∈ integerHahnPart κ → b ∈ integerHahnPart κ →
      c ∈ integerHahnPart κ → d ∈ integerHahnPart κ → a * b = c * d →
        ∃ e f g h : HahnSeries G R,
          e ∈ integerHahnPart κ ∧ f ∈ integerHahnPart κ ∧
          g ∈ integerHahnPart κ ∧ h ∈ integerHahnPart κ ∧
            a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h

end ConwayRefinement.Standalone.Hahn

/-!
## Formal proof

Proof module: `HahnIntegerPartRefinementProof`.

* `HahnIntegerPartRefinement` → `HahnIntegerPartRefinement.proof`
-/
