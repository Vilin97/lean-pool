/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.RepFlag

/-!
# Per-edge factoring of the out-sign product

The subtype product of odd-partner signs over outgoing participating
flags equals the edge-indexed product: each participating edge
contributes the sign of its (pairing-constant) colour exactly once,
and non-participating edges contribute 1 on both sides.
-/

@[expose] public section

namespace RS

open Finset

variable (W : ClosedFragment) (F : EdgeSubset W) {ℓ : ℕ}
  {κ : F.TransitionSystem} (o : κ.Orientation) (φ : F.OddColouring ℓ)

/-- Totalized per-flag sign contribution: the odd-partner sign for
outgoing participating flags, 1 otherwise. -/
private noncomputable def outSignFun (x : W.Flag) : ℤ :=
  if h : x ∈ F.flags then
    if o.isOut x = true then oddPartnerSign ℓ (φ.val ⟨x, h⟩) else 1
  else 1

private theorem outSignFun_of_mem {x : W.Flag} (hx : x ∈ F.flags) :
    outSignFun W F o φ x =
      if o.isOut x = true then oddPartnerSign ℓ (φ.val ⟨x, hx⟩) else 1 :=
  dite_eq_left hx

private theorem outSignFun_of_not_mem {x : W.Flag} (hx : x ∉ F.flags) :
    outSignFun W F o φ x = 1 :=
  dite_eq_right hx

/-- The subtype product over F.flags equals the full product of the
totalized function. -/
private theorem prod_subtype_eq_prod_total :
    (∏ f : {f : W.Flag // f ∈ F.flags},
      (if o.isOut f.val = true then oddPartnerSign ℓ (φ.val f) else 1)) =
    ∏ x : W.Flag, outSignFun W F o φ x := by
  have hbody : ∀ f : {f : W.Flag // f ∈ F.flags},
      (if o.isOut f.val = true then oddPartnerSign ℓ (φ.val f) else 1) =
      outSignFun W F o φ f.val :=
    fun f => (outSignFun_of_mem W F o φ f.prop).symm
  simp_rw [hbody]
  rw [prod_coe_sort]
  exact prod_subset (subset_univ _) (fun x _ hx =>
    outSignFun_of_not_mem W F o φ hx)

/-- Per-edge factor collapse: the product of the two half-slot
contributions equals the single representative contribution. -/
private theorem edge_factor (i : Fin (edgeCount W)) :
    outSignFun W F o φ
        ((starFlagEnum W).symm (Fin.castAdd (edgeCount W) i)) *
    outSignFun W F o φ
        ((starFlagEnum W).symm (Fin.natAdd (edgeCount W) i)) =
    if h : (starFlagEnum W).symm (Fin.castAdd (edgeCount W) i) ∈ F.flags
    then oddPartnerSign ℓ
      (φ.val ⟨(starFlagEnum W).symm (Fin.castAdd (edgeCount W) i), h⟩)
    else 1 := by
  set f₀ := (starFlagEnum W).symm (Fin.castAdd (edgeCount W) i)
  set f₁ := (starFlagEnum W).symm (Fin.natAdd (edgeCount W) i)
  have hpair : W.pairing f₀ = f₁ := pairing_starFlagEnum_symm W i
  by_cases hmem : f₀ ∈ F.flags
  · -- Both flags participate
    have hmem₁ : f₁ ∈ F.flags := hpair ▸ F.pairing_mem _ hmem
    have hsub : (⟨W.pairing f₀, F.pairing_mem _ hmem⟩ :
        {f // f ∈ F.flags}) = ⟨f₁, hmem₁⟩ :=
      Subtype.ext hpair
    have hφeq : φ.val ⟨f₁, hmem₁⟩ = φ.val ⟨f₀, hmem⟩ :=
      (congrArg φ.val hsub).symm.trans (φ.prop ⟨f₀, hmem⟩)
    have hflip : o.isOut f₁ = !o.isOut f₀ :=
      hpair ▸ o.pairing_flip _ hmem
    rw [outSignFun_of_mem W F o φ hmem,
      outSignFun_of_mem W F o φ hmem₁, dite_eq_left hmem]
    by_cases hb : o.isOut f₀ = true
    · -- f₀ outgoing, f₁ incoming
      have hb₁ : ¬ o.isOut f₁ = true := by
        rw [hflip, hb]; decide
      rw [ite_eq_left hb, ite_eq_right hb₁, mul_one]
    · -- f₀ incoming, f₁ outgoing
      have hb₁ : o.isOut f₁ = true := by
        have ho : o.isOut f₀ = false :=
          Bool.eq_false_iff.mpr (by simpa using hb)
        rw [hflip, ho]; rfl
      rw [ite_eq_right hb, ite_eq_left hb₁, one_mul]
      exact congrArg (oddPartnerSign ℓ) hφeq
  · -- Neither flag participates
    have hmem₁ : f₁ ∉ F.flags := hpair ▸ F.pairing_not_mem hmem
    rw [outSignFun_of_not_mem W F o φ hmem,
      outSignFun_of_not_mem W F o φ hmem₁,
      dite_eq_right hmem, mul_one]

/-- Each participating edge has exactly one outgoing flag; the
subtype product of odd-partner signs equals the edge-indexed
product. -/
theorem prod_out_sign_eq_prod_edges :
    (∏ f : {f : W.Flag // f ∈ F.flags},
      (if o.isOut f.val = true then oddPartnerSign ℓ (φ.val f) else 1)) =
    ∏ i : Fin (edgeCount W),
      (if h : (starFlagEnum W).symm (Fin.castAdd (edgeCount W) i) ∈ F.flags
       then oddPartnerSign ℓ
         (φ.val ⟨(starFlagEnum W).symm (Fin.castAdd (edgeCount W) i), h⟩)
       else 1) := by
  rw [prod_subtype_eq_prod_total W F o φ,
    ← Equiv.prod_comp (starFlagEnum W).symm (outSignFun W F o φ),
    Fin.prod_univ_add, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun i _ => edge_factor W F o φ i)

end RS
