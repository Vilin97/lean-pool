/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Table55

/-!
# Lecture V (§5) — Proposition 5.3 (Scott 1981, PRG-19)

The least fixed point of `λx, y. ⟨τ(x, y), σ(x, y)⟩` is the pair with coordinates

`!x. τ(x, !y. σ(x, y))`  and  `!y. σ(!x. τ(x, y), y)`.

This is **Bekić's theorem**: the least solution of the simultaneous system `x =
τ(x, y)`,
`y = σ(x, y)` is computed coordinatewise by nested least fixed points.

In this framework `τ : 𝒟₀ × 𝒟₁ → 𝒟₀` and `σ : 𝒟₀ × 𝒟₁ → 𝒟₁` are approximable, and
the pair-valued
map is `F = ⟨τ, σ⟩ = paired τ σ : 𝒟₀ × 𝒟₁ → 𝒟₀ × 𝒟₁` whose least fixed point
`F.fixElement` (Thm 4.1)
is the least solution Scott invokes in his hint. We build:

* `secFixX τ : 𝒟₁ → 𝒟₀`, the approximable map `y ↦ !x. τ(x, y)` (`fix ∘ curry(τ ∘
swap)`);
* `outerOp τ σ : 𝒟₁ → 𝒟₁`, the approximable map `y ↦ σ(!x. τ(x, y), y)`;
* `ystar = (outerOp τ σ).fixElement = !y. σ(!x. τ(x, y), y)` and
  `xstar = secFixX τ (ystar) = !x. τ(x, ystar)`.

The theorem `fixElement_paired_eq` states `F.fixElement = ⟨xstar, ystar⟩`, proved
exactly as Scott:
`⟨xstar, ystar⟩` is a fixed-point pair (so `F.fixElement ⊑ ⟨xstar, ystar⟩`), and
from the least
solution `⟨a, b⟩` one derives `!x.τ(x,b) ⊑ a`, hence `outerOp(b) ⊑ b`, hence
`ystar ⊑ b`, hence
`xstar ⊑ a`. All *data* is **choice-free**; the proof uses only the order on
`|𝒟ᵢ|` and the
universal properties of `fixElement`.
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap

/-- The section `x ↦ τ(x, y)` of `τ : 𝒟₀ × 𝒟₁ → 𝒟₀` at a fixed `y`, as an
approximable endomap of
`𝒟₀` (the curried `τ ∘ swap` applied to `y`). -/
def sectionX (τ : ApproximableMap (prod V₀ V₁) V₀) (y : V₁.Element) : ApproximableMap V₀ V₀ :=
  toApproxMap ((curry (τ.comp (swapC V₁ V₀))).toElementMap y)

theorem sectionX_apply (τ : ApproximableMap (prod V₀ V₁) V₀) (y : V₁.Element) (x : V₀.Element) :
    (sectionX τ y).toElementMap x = τ.toElementMap (pair x y) := by
  rw [sectionX, toElementMap_curry_apply, toElementMap_comp, swapC_apply]

/-- The approximable map `y ↦ !x. τ(x, y)`: `fix ∘ curry(τ ∘ swap)`. -/
def secFixX (τ : ApproximableMap (prod V₀ V₁) V₀) : ApproximableMap V₁ V₀ :=
  (fixMap V₀).comp (curry (τ.comp (swapC V₁ V₀)))

theorem secFixX_apply (τ : ApproximableMap (prod V₀ V₁) V₀) (y : V₁.Element) :
    (secFixX τ).toElementMap y = (sectionX τ y).fixElement := by
  rw [secFixX, toElementMap_comp, fixMap_toElementMap, sectionX]

/-- `!x. τ(x, y)` is a fixed point of the section: `τ(!x.τ(x,y), y) = !x.τ(x,y)`. -/
theorem secFixX_isFixed (τ : ApproximableMap (prod V₀ V₁) V₀) (y : V₁.Element) :
    τ.toElementMap (pair ((secFixX τ).toElementMap y) y) = (secFixX τ).toElementMap y := by
  rw [secFixX_apply, ← sectionX_apply, toElementMap_fixElement]

/-- The outer operator `y ↦ σ(!x. τ(x, y), y)`. -/
def outerOp (τ : ApproximableMap (prod V₀ V₁) V₀) (σ : ApproximableMap (prod V₀ V₁) V₁) :
    ApproximableMap V₁ V₁ :=
  σ.comp (paired (secFixX τ) (idMap V₁))

theorem outerOp_apply (τ : ApproximableMap (prod V₀ V₁) V₀) (σ : ApproximableMap (prod V₀ V₁) V₁)
    (y : V₁.Element) :
    (outerOp τ σ).toElementMap y = σ.toElementMap (pair ((secFixX τ).toElementMap y) y) := by
  rw [outerOp, toElementMap_comp, toElementMap_paired, toElementMap_idMap]

/-- **Proposition 5.3 (Scott 1981, PRG-19).** Bekić's theorem: the least fixed
point of
`F = ⟨τ, σ⟩` is the pair `⟨!x.τ(x, !y.σ(x,y)-coordinate), !y.σ(!x.τ(x,y), y)⟩`.
Here the second
coordinate is `ystar = (outerOp τ σ).fixElement` and the first is `xstar = secFixX
τ (ystar)`. -/
theorem fixElement_paired_eq (τ : ApproximableMap (prod V₀ V₁) V₀)
    (σ : ApproximableMap (prod V₀ V₁) V₁) :
    (paired τ σ).fixElement =
      pair ((secFixX τ).toElementMap (outerOp τ σ).fixElement) (outerOp τ σ).fixElement := by
  set ystar := (outerOp τ σ).fixElement with hystar
  set xstar := (secFixX τ).toElementMap ystar with hxstar
  -- `σ(xstar, ystar) = ystar`: `ystar` is the fixed point of `outerOp`.
  have hσ : σ.toElementMap (pair xstar ystar) = ystar := by
    have := toElementMap_fixElement (outerOp τ σ)
    rw [← hystar] at this
    rw [outerOp_apply] at this
    rw [hxstar]; exact this
  -- `τ(xstar, ystar) = xstar`: `xstar = !x.τ(x, ystar)` is a fixed point of its
  -- section.
  have hτ : τ.toElementMap (pair xstar ystar) = xstar := by
    rw [hxstar]; exact secFixX_isFixed τ ystar
  apply le_antisymm
  · -- `F.fixElement ⊑ ⟨xstar, ystar⟩`: the pair is a fixed point of `F`.
    apply fixElement_le_of_toElementMap_le
    rw [toElementMap_paired]
    rw [hτ, hσ]
  · -- `⟨xstar, ystar⟩ ⊑ F.fixElement`.
    set fp := (paired τ σ).fixElement with hfp
    set a := fp.fst with ha
    set b := fp.snd with hb
    -- `τ(a, b) = a` and `σ(a, b) = b` (decompose the fixed point of `F`).
    have hfpeq : pair (τ.toElementMap fp) (σ.toElementMap fp) = fp := by
      have := toElementMap_fixElement (paired τ σ)
      rw [← hfp, toElementMap_paired] at this
      exact this
    have hfp_pair : fp = pair a b := (pair_fst_snd fp).symm
    have hτa : τ.toElementMap (pair a b) = a := by
      have : (pair (τ.toElementMap fp) (σ.toElementMap fp)).fst = fp.fst := by rw [hfpeq]
      rw [fst_pair] at this
      rw [← hfp_pair]; rw [ha]; exact this
    have hσb : σ.toElementMap (pair a b) = b := by
      have : (pair (τ.toElementMap fp) (σ.toElementMap fp)).snd = fp.snd := by rw [hfpeq]
      rw [snd_pair] at this
      rw [← hfp_pair]; rw [hb]; exact this
    -- `!x.τ(x, b) ⊑ a` since `τ(a, b) = a`.
    have hxfix_le : (secFixX τ).toElementMap b ≤ a := by
      rw [secFixX_apply]
      apply fixElement_le_of_toElementMap_le
      rw [sectionX_apply]
      exact le_of_eq hτa
    -- `outerOp(b) = σ(!x.τ(x,b), b) ⊑ σ(a, b) = b`.
    have houter_le : (outerOp τ σ).toElementMap b ≤ b := by
      rw [outerOp_apply]
      calc σ.toElementMap (pair ((secFixX τ).toElementMap b) b)
          ≤ σ.toElementMap (pair a b) :=
            σ.toElementMap_mono (pair_le_pair_iff.mpr ⟨hxfix_le, le_refl b⟩)
        _ = b := hσb
    -- so `ystar ⊑ b`, and `xstar = !x.τ(x, ystar) ⊑ !x.τ(x, b) ⊑ a`.
    have hystar_le : ystar ≤ b := by
      rw [hystar]
      exact fixElement_le_of_toElementMap_le (outerOp τ σ) houter_le
    have hxstar_le : xstar ≤ a := by
      rw [hxstar]
      calc (secFixX τ).toElementMap ystar
          ≤ (secFixX τ).toElementMap b := (secFixX τ).toElementMap_mono hystar_le
        _ ≤ a := hxfix_le
    rw [hfp_pair]
    exact pair_le_pair_iff.mpr ⟨hxstar_le, hystar_le⟩

end ApproximableMap

end Domain.Neighborhood
