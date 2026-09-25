/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.ZMod.QuotientGroup
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation
/-! Provides the public declarations in the
  `LocalClassFieldTheory.ClassFormation.ValueGroupCohomology` Lean module. -/

@[expose] public section

namespace LocalClassFieldTheory

open LocalFieldTheory

open CyclicCohomology

noncomputable section

open scoped BigOperators

universe u

open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]

/-- On the trivially acted-on value group, the finite-group norm is
multiplication by the order of the Galois group. -/
theorem galoisGroupValueGroup_tateNorm_toAdd (a : Multiplicative Int) :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    Multiplicative.toAdd
        (tateNorm (Gal(L/K)) (Multiplicative Int) a) =
      (Fintype.card (Gal(L/K)) : Int) * Multiplicative.toAdd a := by
  let := galoisGroupValueGroupMulDistribMulAction K L
  have hnorm : tateNorm (Gal(L/K)) (Multiplicative Int) a =
      a ^ Fintype.card (Gal(L/K)) := by
    simp only [tateNorm, galoisGroupValueGroupMulDistribMulAction_smul,
      Finset.prod_const, Finset.card_univ]
  simpa only [toAdd_pow, nsmul_eq_mul] using
    congrArg Multiplicative.toAdd hnorm

/-- Reduction modulo `|G|` on the fixed subgroup of the trivial value-group
module. -/
def galoisGroupValueGroupFixedToZModHom :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    fixedSubgroup (Gal(L/K)) (Multiplicative Int) →*
      Multiplicative (ZMod (Fintype.card (Gal(L/K)))) := by
  letI := galoisGroupValueGroupMulDistribMulAction K L
  exact
    { toFun := fun x => Multiplicative.ofAdd
        ((Multiplicative.toAdd (x : Multiplicative Int) : Int) :
          ZMod (Fintype.card (Gal(L/K))))
      map_one' := by simp
      map_mul' := by
        intro x y
        simp }

/-- States the theorem `galoisGroupValueGroupFixedToZModHom_surjective`. -/
theorem galoisGroupValueGroupFixedToZModHom_surjective :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    Function.Surjective (galoisGroupValueGroupFixedToZModHom K L) := by
  let := galoisGroupValueGroupMulDistribMulAction K L
  intro y
  rcases ZMod.intCast_surjective (Multiplicative.toAdd y) with ⟨z, hz⟩
  let x : fixedSubgroup (Gal(L/K)) (Multiplicative Int) :=
    ⟨Multiplicative.ofAdd z, by intro σ; rfl⟩
  refine ⟨x, ?_⟩
  rw [show galoisGroupValueGroupFixedToZModHom K L x =
      Multiplicative.ofAdd
        ((z : Int) : ZMod (Fintype.card (Gal(L/K)))) by rfl]
  exact congrArg Multiplicative.ofAdd hz

/-- The kernel of reduction modulo `|G|` is exactly the norm subgroup inside
the fixed subgroup. -/
theorem galoisGroupValueGroupFixedToZModHom_ker :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    MonoidHom.ker (galoisGroupValueGroupFixedToZModHom K L) =
      (tateNormSubgroup (Gal(L/K)) (Multiplicative Int)).subgroupOf
        (fixedSubgroup (Gal(L/K)) (Multiplicative Int)) := by
  let := galoisGroupValueGroupMulDistribMulAction K L
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have hx0 :
        ((Multiplicative.toAdd (x : Multiplicative Int) : Int) :
          ZMod (Fintype.card (Gal(L/K)))) = 0 := by
      exact congrArg Multiplicative.toAdd hx
    rcases (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hx0 with ⟨z, hz⟩
    change (x : Multiplicative Int) ∈
      tateNormSubgroup (Gal(L/K)) (Multiplicative Int)
    refine ⟨Multiplicative.ofAdd z, ?_⟩
    have htoAdd :
        Multiplicative.toAdd
            (tateNorm (Gal(L/K)) (Multiplicative Int)
              (Multiplicative.ofAdd z)) =
          Multiplicative.toAdd (x : Multiplicative Int) := by
      rw [galoisGroupValueGroup_tateNorm_toAdd]
      exact hz.symm
    exact congrArg Multiplicative.ofAdd htoAdd
  · intro hx
    change (x : Multiplicative Int) ∈
      tateNormSubgroup (Gal(L/K)) (Multiplicative Int) at hx
    rcases hx with ⟨z, hz⟩
    rw [tateNormHom_apply] at hz
    exact congrArg Multiplicative.ofAdd (by
      change
        ((Multiplicative.toAdd (x : Multiplicative Int) : Int) :
            ZMod (Fintype.card (Gal(L/K)))) = 0
      rw [← hz, galoisGroupValueGroup_tateNorm_toAdd]
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2
      exact ⟨Multiplicative.toAdd z, rfl⟩)

/-- The actual custom Tate `H⁰` of the trivial value group is `Z/|G|Z`. -/
noncomputable def galoisGroupValueGroupHerbrandH0MulEquivZMod :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    HerbrandH0 (Gal(L/K)) (Multiplicative Int) ≃*
      Multiplicative (ZMod (Fintype.card (Gal(L/K)))) := by
  letI := galoisGroupValueGroupMulDistribMulAction K L
  exact
    (HerbrandH0.equiv
      (G := Gal(L/K)) (A := Multiplicative Int)).trans
      ((QuotientGroup.quotientMulEquivOfEq
        (galoisGroupValueGroupFixedToZModHom_ker K L).symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective
          (galoisGroupValueGroupFixedToZModHom K L)
          (galoisGroupValueGroupFixedToZModHom_surjective K L)))

/-- Finiteness of value-group `H⁰`, derived from its explicit cyclic
description rather than assumed as an extra hypothesis. -/
theorem galoisGroupValueGroupHerbrandH0Finite :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    Finite (HerbrandH0 (Gal(L/K)) (Multiplicative Int)) := by
  let := galoisGroupValueGroupMulDistribMulAction K L
  exact Finite.of_equiv
    (Multiplicative (ZMod (Fintype.card (Gal(L/K)))))
    (galoisGroupValueGroupHerbrandH0MulEquivZMod K L).symm.toEquiv

/-- Value-group factor for the local class-field axiom: `#H⁰(G,ℤ)=|G|`. -/
theorem galoisGroupValueGroup_herbrandH0_card :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    letI := galoisGroupValueGroupHerbrandH0Finite K L
    Nat.card (HerbrandH0 (Gal(L/K)) (Multiplicative Int)) =
      Fintype.card (Gal(L/K)) := by
  let := galoisGroupValueGroupMulDistribMulAction K L
  rw [Nat.card_congr (galoisGroupValueGroupHerbrandH0MulEquivZMod K L).toEquiv]
  simp

/-- For a finite Galois extension, the value-group factor is the extension
degree appearing in the local class-field-axiom theorem. -/
theorem galoisGroupValueGroup_herbrandH0_card_eq_finrank [IsGalois K L] :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    letI := galoisGroupValueGroupHerbrandH0Finite K L
    Nat.card (HerbrandH0 (Gal(L/K)) (Multiplicative Int)) =
      Module.finrank K L := by
  let := galoisGroupValueGroupMulDistribMulAction K L
  rw [galoisGroupValueGroup_herbrandH0_card K L]
  exact Fintype.card_eq_nat_card.trans (IsGalois.card_aut_eq_finrank K L)

/-- The norm kernel of the trivial torsion-free value group is zero. -/
theorem galoisGroupValueGroup_normKernelSubgroup_eq_bot :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    normKernelSubgroup (Gal(L/K)) (Multiplicative Int) = ⊥ := by
  let := galoisGroupValueGroupMulDistribMulAction K L
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_bot]
    exact congrArg Multiplicative.ofAdd (by
      change Multiplicative.toAdd (x : Multiplicative Int) = 0
      have hnorm :
          (Fintype.card (Gal(L/K)) : Int) *
              Multiplicative.toAdd (x : Multiplicative Int) = 0 := by
        rw [← galoisGroupValueGroup_tateNorm_toAdd K L]
        exact congrArg Multiplicative.toAdd hx
      exact (mul_eq_zero.mp hnorm).resolve_left (by
        exact_mod_cast Fintype.card_ne_zero))
  · exact bot_le

/-- Finiteness of value-group `H⁻¹`, derived from the vanishing of its
norm kernel. -/
theorem galoisGroupValueGroupHerbrandHMinusOneFinite
    (σ : Gal(L/K)) :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    Finite
      (HerbrandHMinusOne (Gal(L/K)) (Multiplicative Int) σ) := by
  let := galoisGroupValueGroupMulDistribMulAction K L
  have : Subsingleton
      (normKernelSubgroup (Gal(L/K)) (Multiplicative Int)) := by
    rw [galoisGroupValueGroup_normKernelSubgroup_eq_bot K L]
    infer_instance
  let : Subsingleton
      (HerbrandHMinusOne (Gal(L/K)) (Multiplicative Int) σ) :=
    ⟨fun q =>
      HerbrandHMinusOne.inductionOn σ
        (motive := fun q => ∀ r, q = r) q fun x r =>
          HerbrandHMinusOne.inductionOn σ
            (motive := fun r => HerbrandHMinusOne.mk σ x = r) r fun y =>
              congrArg (fun z => HerbrandHMinusOne.mk σ z)
                (Subsingleton.elim x y)⟩
  exact Finite.of_injective
    (fun _ : HerbrandHMinusOne (Gal(L/K))
      (Multiplicative Int) σ => false)
    (fun x y _ => Subsingleton.elim x y)

/-- Value-group factor for the local class-field axiom: `H⁻¹(G,ℤ)` is trivial. -/
theorem galoisGroupValueGroup_herbrandHMinusOne_card_eq_one
    (σ : Gal(L/K)) :
    letI := galoisGroupValueGroupMulDistribMulAction K L
    letI := galoisGroupValueGroupHerbrandHMinusOneFinite K L σ
    Nat.card
      (HerbrandHMinusOne (Gal(L/K)) (Multiplicative Int) σ) = 1 := by
  let := galoisGroupValueGroupMulDistribMulAction K L
  have : Subsingleton
      (normKernelSubgroup (Gal(L/K)) (Multiplicative Int)) := by
    rw [galoisGroupValueGroup_normKernelSubgroup_eq_bot K L]
    infer_instance
  let : Subsingleton
      (HerbrandHMinusOne (Gal(L/K)) (Multiplicative Int) σ) :=
    ⟨fun q =>
      HerbrandHMinusOne.inductionOn σ
        (motive := fun q => ∀ r, q = r) q fun x r =>
          HerbrandHMinusOne.inductionOn σ
            (motive := fun r => HerbrandHMinusOne.mk σ x = r) r fun y =>
              congrArg (fun z => HerbrandHMinusOne.mk σ z)
                (Subsingleton.elim x y)⟩
  exact Nat.card_unique

end
end LocalClassFieldTheory
