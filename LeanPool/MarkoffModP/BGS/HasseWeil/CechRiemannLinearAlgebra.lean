/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The linear-algebra inequality in the Cech proof of Riemann's inequality

Let `A ≤ A'` and `B` be subspaces of a vector space `V`.  The canonical map

`A' / A → V / (A ⊔ B)`

has kernel canonically represented by

`(A' ⊓ B) / (A ⊓ B)`.

Rank--nullity therefore gives

`finrank (A' / A) ≤ finrank ((A' ⊓ B) / (A ⊓ B)) + finrank (V / (A ⊔ B))`.

Only the three quotient spaces occurring in this argument need to be
finite-dimensional; the ambient space `V` and the subspaces themselves may
be infinite-dimensional.  This is the abstract finite-dimensional step used
by the Cech proof of Riemann's inequality.
-/

namespace BGS.HasseWeil

open Submodule

noncomputable section

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The copy of `A` inside `A'`.  When `A ≤ A'`, this is the denominator in
the relative quotient `A' / A`. -/
abbrev relativeSubmodule (A A' : Submodule K V) : Submodule K A' :=
  A.comap A'.subtype

/-- The canonical map `A' / A → V / (A ⊔ B)` used in the Cech argument. -/
def cechRelativeQuotientMap (A A' B : Submodule K V) :
    (A' ⧸ relativeSubmodule A A') →ₗ[K] V ⧸ (A ⊔ B) :=
  (relativeSubmodule A A').mapQ (A ⊔ B) A'.subtype
    (comap_mono le_sup_left)

/-- The quotient `(A' ⊓ B) / (A ⊓ B)` maps naturally into `A' / A`. -/
def cechIntersectionQuotientMap (A A' B : Submodule K V) :
    (↥(A' ⊓ B) ⧸ (A ⊓ B).comap (A' ⊓ B).subtype) →ₗ[K]
      A' ⧸ relativeSubmodule A A' :=
  let sourceDenominator := (A ⊓ B).comap (A' ⊓ B).subtype
  let targetDenominator := relativeSubmodule A A'
  let inclusion : ↥(A' ⊓ B) →ₗ[K] A' := Submodule.inclusion inf_le_left
  sourceDenominator.liftQ (targetDenominator.mkQ.comp inclusion) <| by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    change (x : V) ∈ A
    exact hx.1

theorem cechIntersectionQuotientMap_injective (A A' B : Submodule K V) :
    Function.Injective (cechIntersectionQuotientMap A A' B) := by
  rw [← LinearMap.ker_eq_bot]
  apply Submodule.ker_liftQ_eq_bot
  intro x hx
  change (x : V) ∈ A ⊓ B
  have hxA : (x : V) ∈ A := by
    simpa [cechIntersectionQuotientMap, relativeSubmodule] using hx
  exact ⟨hxA, x.property.2⟩

private theorem comap_sup_eq_sup_comap_of_le
    (A A' B : Submodule K V) (hAA' : A ≤ A') :
    (A ⊔ B).comap A'.subtype =
      relativeSubmodule A A' ⊔ B.comap A'.subtype := by
  apply le_antisymm
  · intro x hx
    have hx' : (x : V) ∈ A' ⊓ (A ⊔ B) := ⟨x.property, hx⟩
    have hmodular : A' ⊓ (A ⊔ B) = A ⊔ (A' ⊓ B) := by
      calc
        A' ⊓ (A ⊔ B) = A' ⊓ (B ⊔ A) := by rw [sup_comm A B]
        _ = (A' ⊓ B) ⊔ A := (inf_sup_assoc_of_le B hAA').symm
        _ = A ⊔ (A' ⊓ B) := sup_comm _ _
    rw [hmodular] at hx'
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx'
    refine Submodule.mem_sup.mpr
      ⟨⟨a, hAA' ha⟩, ha, ⟨b, hb.1⟩, hb.2, ?_⟩
    exact Subtype.ext hab
  · exact sup_le (comap_mono le_sup_left) (comap_mono le_sup_right)

/-- The intersection quotient identifies exactly with the kernel of the Cech
relative quotient map. -/
theorem range_cechIntersectionQuotientMap_eq_ker
    (A A' B : Submodule K V) (hAA' : A ≤ A') :
    LinearMap.range (cechIntersectionQuotientMap A A' B) =
      LinearMap.ker (cechRelativeQuotientMap A A' B) := by
  rw [cechIntersectionQuotientMap, Submodule.range_liftQ,
    LinearMap.range_comp, Submodule.range_inclusion]
  simp only [comap_inf, comap_subtype_self, top_inf_eq]
  rw [cechRelativeQuotientMap, Submodule.ker_mapQ,
    comap_sup_eq_sup_comap_of_le A A' B hAA', Submodule.map_sup,
    Submodule.mkQ_map_self, bot_sup_eq]

/-- Rank--nullity with the Cech kernel written as the intersection quotient.
This equality is the strongest finite-dimensional form of the abstract
linear-algebra argument. -/
theorem finrank_relativeQuotient_eq_infQuotient_add_range
    (A A' B : Submodule K V) (hAA' : A ≤ A')
    [Module.Finite K (A' ⧸ relativeSubmodule A A')] :
    Module.finrank K (A' ⧸ relativeSubmodule A A') =
      Module.finrank K (↥(A' ⊓ B) ⧸ (A ⊓ B).comap (A' ⊓ B).subtype) +
        Module.finrank K (LinearMap.range (cechRelativeQuotientMap A A' B)) := by
  have hker := range_cechIntersectionQuotientMap_eq_ker A A' B hAA'
  have hinj := cechIntersectionQuotientMap_injective A A' B
  calc
    Module.finrank K (A' ⧸ relativeSubmodule A A') =
        Module.finrank K (LinearMap.range (cechRelativeQuotientMap A A' B)) +
          Module.finrank K (LinearMap.ker (cechRelativeQuotientMap A A' B)) :=
      (LinearMap.finrank_range_add_finrank_ker _).symm
    _ = Module.finrank K (LinearMap.range (cechRelativeQuotientMap A A' B)) +
          Module.finrank K
            (↥(A' ⊓ B) ⧸ (A ⊓ B).comap (A' ⊓ B).subtype) := by
      rw [← hker, LinearMap.finrank_range_of_inj hinj]
    _ = Module.finrank K
          (↥(A' ⊓ B) ⧸ (A ⊓ B).comap (A' ⊓ B).subtype) +
        Module.finrank K (LinearMap.range (cechRelativeQuotientMap A A' B)) :=
      Nat.add_comm _ _

/-- The abstract finite-dimensional inequality behind the Cech proof of
Riemann's inequality.  No finite-dimensionality hypothesis is imposed on
the ambient vector space. -/
theorem finrank_relativeQuotient_le_infQuotient_add_supQuotient
    (A A' B : Submodule K V) (hAA' : A ≤ A')
    [Module.Finite K (A' ⧸ relativeSubmodule A A')]
    [Module.Finite K (V ⧸ (A ⊔ B))] :
    Module.finrank K (A' ⧸ relativeSubmodule A A') ≤
      Module.finrank K (↥(A' ⊓ B) ⧸ (A ⊓ B).comap (A' ⊓ B).subtype) +
        Module.finrank K (V ⧸ (A ⊔ B)) := by
  rw [finrank_relativeQuotient_eq_infQuotient_add_range A A' B hAA']
  exact Nat.add_le_add_left
    (LinearMap.range (cechRelativeQuotientMap A A' B)).finrank_le _

/-- Subtractive form of
`finrank_relativeQuotient_le_infQuotient_add_supQuotient`, convenient when
the intersection quotient is the desired lower bound. -/
theorem finrank_relativeQuotient_sub_supQuotient_le_infQuotient
    (A A' B : Submodule K V) (hAA' : A ≤ A')
    [Module.Finite K (A' ⧸ relativeSubmodule A A')]
    [Module.Finite K (V ⧸ (A ⊔ B))] :
    Module.finrank K (A' ⧸ relativeSubmodule A A') -
        Module.finrank K (V ⧸ (A ⊔ B)) ≤
      Module.finrank K (↥(A' ⊓ B) ⧸ (A ⊓ B).comap (A' ⊓ B).subtype) := by
  apply Nat.sub_le_iff_le_add.mpr
  simpa [Nat.add_comm] using
    finrank_relativeQuotient_le_infQuotient_add_supQuotient A A' B hAA'

end

end BGS.HasseWeil
