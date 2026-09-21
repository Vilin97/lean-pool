/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Presheaf

/-!
# Concrete Refinement for Rational Coverings

If a finer covering (same base, each piece inside some piece of the original)
has the separation property (jointly injective restriction maps), then so does
the original covering. This is the concrete version of Proposition A.3 of Wedhorn.

The analogous statement for **gluing** (`gluing_of_finer_rational`) is more subtle:
reducing gluing from a refinement `V` to the original `C` also requires separation
of `V`, because the witness produced from `V`'s gluing restricts correctly to the
pieces of `V` but only restricts to the pieces of `C` "up to further refinement by
`V`", and `V`-separation is needed to upgrade this.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Proposition A.3
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsHuberRing A] [HasLocLiftPowerBounded A]

/-- A rational covering has the *separation property* if the restriction
maps to the covering pieces are jointly injective. -/
def RationalCoveringData.HasSeparation (C : RationalCoveringData A) : Prop :=
  ∀ x y : presheafValue C.base,
    (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      restrictionMap C.base D (C.hsubset D hD) x =
      restrictionMap C.base D (C.hsubset D hD) y) → x = y

/-- **Refinement preserves separation (Proposition A.3 of Wedhorn).**

Given a covering `C` and a finer covering `V_covers` of the same base,
if V has separation then C has separation. Uses `restrictionMap_comp`. -/
theorem separation_of_finer_rational (C : RationalCoveringData A)
    (V_covers : Finset (RationalLocData A))
    (hV_subset : ∀ D ∈ V_covers, rationalOpen D.T D.s ⊆
      rationalOpen C.base.T C.base.s)
    (τ : { D // D ∈ V_covers } → { E // E ∈ C.covers })
    (hτ : ∀ d : { D // D ∈ V_covers },
      rationalOpen d.1.T d.1.s ⊆ rationalOpen (τ d).1.T (τ d).1.s)
    (hV_sep : ∀ x y : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ V_covers),
        restrictionMap C.base D (hV_subset D hD) x =
        restrictionMap C.base D (hV_subset D hD) y) → x = y)
    (x y : presheafValue C.base)
    (hC : ∀ (E : RationalLocData A) (hE : E ∈ C.covers),
      restrictionMap C.base E (C.hsubset E hE) x =
      restrictionMap C.base E (C.hsubset E hE) y) :
    x = y := by
  apply hV_sep
  intro D hD
  let E := (τ ⟨D, hD⟩).1
  have hE : E ∈ C.covers := (τ ⟨D, hD⟩).2
  have hDE : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s := hτ ⟨D, hD⟩
  have hcomp := restrictionMap_comp C.base E D (C.hsubset E hE) hDE
  rw [show hV_subset D hD = hDE.trans (C.hsubset E hE) from Subsingleton.elim _ _,
    ← congr_fun hcomp x, ← congr_fun hcomp y]
  exact congrArg (restrictionMap E D hDE) (hC E hE)

/-- **Refinement reduces gluing (concrete form)**.

Given a covering `C` with base `C.base` and a refinement `V_covers` (the same
base; each piece inside some piece of `C`), compatible sections on `C` can be
glued by combining:

* `hV_glue`: gluing for `V`, which produces a candidate `x : presheafValue C.base`
  whose `V`-restrictions match the restrictions of the given `fC` sections.
* `hE_sep`: for each `E ∈ C.covers`, separation on `presheafValue E` via the
  restriction maps to the `V_covers` pieces that land inside `E` (i.e. those
  `D` with `τ D = E`). This local separation is needed to upgrade "x restricts
  to `fC τ(D)` on each `D`" to "x restricts to `fC E` on each `E`".

The concrete refinement from `StandardCover.RationalCoveringData.refines_by_standard_cover`
together with separation for both `C` and each `E` (which in the full Wedhorn
setting follows from `restrictionMapHom_injective` / Wedhorn Cor 8.32) will feed
this theorem to transfer gluing from the standard-cover / Laurent-cover induction
back to an arbitrary rational covering.

**Proof sketch**. Build `fV D := restrictionMap (τ⟨D,hD⟩).1 D (hτ⟨D,hD⟩) (fC (τ⟨D,hD⟩).1 _)`
for `D ∈ V_covers`. Check `fV` is compatible on `V`-overlaps via `fC`-compatibility
and `restrictionMap_comp`. Apply `hV_glue` to get `x : presheafValue C.base`. For
each `E ∈ C.covers`, apply `hE_sep E hE` to `restrictionMap C.base E _ x` and
`fC E hE`; the equality of their further `V`-restrictions to each `D ∈ V_covers`
with `τ⟨D,_⟩ = E` follows from `restrictionMap_comp` + the `x`-gluing property. -/
theorem gluing_of_finer_rational (C : RationalCoveringData A)
    (V_covers : Finset (RationalLocData A))
    (hV_subset : ∀ D ∈ V_covers, rationalOpen D.T D.s ⊆
      rationalOpen C.base.T C.base.s)
    (τ : { D // D ∈ V_covers } → { E // E ∈ C.covers })
    (hτ : ∀ d : { D // D ∈ V_covers },
      rationalOpen d.1.T d.1.s ⊆ rationalOpen (τ d).1.T (τ d).1.s)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (hV_glue : ∀ (fV : ∀ D : { D // D ∈ V_covers }, presheafValue D.1),
      (∀ (D₁ D₂ : { D // D ∈ V_covers }) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂)) →
      ∃ x : presheafValue C.base, ∀ D : { D // D ∈ V_covers },
        restrictionMap C.base D.1 (hV_subset D.1 D.2) x = fV D)
    (hE_sep : ∀ (E : { E // E ∈ C.covers }) (a b : presheafValue E.1),
      (∀ (d : { D // D ∈ V_covers }) (hd : τ d = E),
        restrictionMap E.1 d.1 (hd ▸ hτ d) a =
          restrictionMap E.1 d.1 (hd ▸ hτ d) b) → a = b) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  -- Step 1: Build the V-indexed family fV by restricting fC along τ.
  let fV : ∀ D : { D // D ∈ V_covers }, presheafValue D.1 :=
    fun D => restrictionMap (τ D).1 D.1 (hτ D) (fC (τ D))
  -- Step 2: Check fV satisfies the V-compatibility.
  have hfV_compat : ∀ (D₁ D₂ : { D // D ∈ V_covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (fV D₁) = restrictionMap D₂.1 D₃ h₃₂ (fV D₂) := by
    intro D₁ D₂ D₃ h₃₁ h₃₂
    -- Peel each fV via restrictionMap_comp, then close with hC_compat.
    simp only [fV, ← Function.comp_apply (f := restrictionMap D₁.1 D₃ h₃₁),
      ← Function.comp_apply (f := restrictionMap D₂.1 D₃ h₃₂), restrictionMap_comp]
    exact hC_compat (τ D₁) (τ D₂) D₃ (h₃₁.trans (hτ D₁)) (h₃₂.trans (hτ D₂))
  -- Step 3: Apply hV_glue to get x.
  obtain ⟨x, hx⟩ := hV_glue fV hfV_compat
  refine ⟨x, fun E => ?_⟩
  -- Step 4: For each E ∈ C.covers, verify restrictionMap C.base E _ x = fC E
  -- via hE_sep (separation on E through the V-pieces with τ d = E).
  apply hE_sep E
  intro d hd
  -- Substitute E := τ d to align types, then collapse the LHS double-restriction
  -- via restrictionMap_comp; it then equals fV d = restrictionMap (τ d) d (fC (τ d)).
  subst hd
  rw [← Function.comp_apply (f := restrictionMap (τ d).1 d.1 (hτ d)), restrictionMap_comp]
  exact hx d

end ValuationSpectrum
