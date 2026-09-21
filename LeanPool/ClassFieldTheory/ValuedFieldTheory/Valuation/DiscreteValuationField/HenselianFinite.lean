/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.AdicPower
import Mathlib.Algebra.Module.Shrink
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Nakayama

/-! # Henselian Finite -/
namespace ValuationTheory

/-!
# Finite algebra consequences of Henselian pairs

This file keeps the Nakayama and finite-module completion consequences away
from the lightweight `HenselianDVF` core.
-/

noncomputable section

universe u v

namespace DiscreteValuationField

/-- If an ideal lies in the Jacobson radical of the base ring, then its action
on any module lands in the module Jacobson radical. -/
theorem ideal_smul_top_le_module_jacobson_of_le_jacobson_bot
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {I : Ideal R} (hI : I ≤ Ideal.jacobson (⊥ : Ideal R)) :
    I • (⊤ : Submodule R M) ≤ Module.jacobson R M := by
  rw [Ideal.jacobson_bot] at hI
  exact (Submodule.smul_mono hI le_rfl).trans
    (Ring.jacobson_smul_top_le R M)

/-- The `jac` field of `HenselianRing` gives the Nakayama/module-Jacobson
component needed after applying the Henselian ideal to any module. -/
theorem ideal_smul_top_le_module_jacobson_of_henselianRing
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {I : Ideal R} [HenselianRing R I] :
    I • (⊤ : Submodule R M) ≤ Module.jacobson R M :=
  ideal_smul_top_le_module_jacobson_of_le_jacobson_bot HenselianRing.jac

/-- Algebra form of `ideal_smul_top_le_module_jacobson_of_henselianRing`: the
base Henselian ideal mapped into an algebra lies in the module Jacobson radical
after restricting scalars to the base. -/
theorem ideal_map_restrictScalars_le_module_jacobson_of_henselianRing
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {I : Ideal R} [HenselianRing R I] :
    (I.map (algebraMap R S)).restrictScalars R ≤ Module.jacobson R S := by
  simpa [Ideal.smul_top_eq_map] using
    (ideal_smul_top_le_module_jacobson_of_henselianRing
      (R := R) (M := S) (I := I))

/-- Finite algebra form of the Jacobson/Nakayama component: if an ideal lies
in the Jacobson radical of the base, then its extension to a finite algebra
lies in the Jacobson radical upstairs. -/
theorem ideal_map_le_jacobson_bot_of_le_jacobson_bot_of_moduleFinite
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] {I : Ideal R}
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R)) :
    I.map (algebraMap R S) ≤ Ideal.jacobson (⊥ : Ideal S) := by
  rw [Ideal.jacobson, le_sInf_iff]
  rintro Q ⟨-, hQmax⟩
  by_contra hle
  rw [SetLike.le_def] at hle
  push Not at hle
  rcases hle with ⟨x, hxI, hxQ⟩
  let : Q.IsMaximal := hQmax
  let : Field (S ⧸ Q) := Ideal.Quotient.field Q
  let qlin : S →ₗ[R] S ⧸ Q := (Ideal.Quotient.mkₐ R Q).toLinearMap
  have : Module.Finite R (S ⧸ Q) :=
    Module.Finite.of_surjective qlin (Ideal.Quotient.mkₐ_surjective R Q)
  have hxQideal :
      Ideal.Quotient.mk Q x ∈ I.map (algebraMap R (S ⧸ Q)) := by
    simpa [Ideal.map_map, RingHom.comp_apply] using
      Ideal.mem_map_of_mem (Ideal.Quotient.mk Q) hxI
  have hunit : IsUnit (Ideal.Quotient.mk Q x) := by
    exact isUnit_iff_ne_zero.mpr (by
      intro hzero
      exact hxQ (Ideal.Quotient.eq_zero_iff_mem.mp hzero))
  have htop :
      (⊤ : Submodule R (S ⧸ Q)) ≤
        I • (⊤ : Submodule R (S ⧸ Q)) := by
    intro y hy
    rcases hunit with ⟨u, hu⟩
    have hyideal : y ∈ I.map (algebraMap R (S ⧸ Q)) := by
      rw [← Units.mul_inv_cancel_left u y]
      exact (I.map (algebraMap R (S ⧸ Q))).mul_mem_right
        (↑u⁻¹ * y) (by simpa [hu.symm] using hxQideal)
    simpa [Ideal.smul_top_eq_map] using hyideal
  have hbot :
      (⊤ : Submodule R (S ⧸ Q)) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I
      (⊤ : Submodule R (S ⧸ Q)) Module.Finite.fg_top htop hI
  exact (top_ne_bot : (⊤ : Submodule R (S ⧸ Q)) ≠ ⊥) hbot

/-- Henselian-ring version of
`ideal_map_le_jacobson_bot_of_le_jacobson_bot_of_moduleFinite`. -/
theorem ideal_map_le_jacobson_bot_of_henselianRing_of_moduleFinite
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] {I : Ideal R} [HenselianRing R I] :
    I.map (algebraMap R S) ≤ Ideal.jacobson (⊥ : Ideal S) :=
  ideal_map_le_jacobson_bot_of_le_jacobson_bot_of_moduleFinite
    (R := R) (S := S) (I := I) HenselianRing.jac

/-- In a Noetherian finite algebra over a Henselian pair, the extended
Henselian ideal is adically Hausdorff. -/
theorem isHausdorff_map_algebraMap_of_henselianRing_of_moduleFinite
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [IsNoetherianRing S]
    {I : Ideal R} [HenselianRing R I] :
    IsHausdorff (I.map (algebraMap R S)) S :=
  IsHausdorff.of_le_jacobson
    (R := S) (M := S) (I := I.map (algebraMap R S))
    (ideal_map_le_jacobson_bot_of_henselianRing_of_moduleFinite
      (R := R) (S := S) (I := I))

/-- Pulling back an adic power submodule along a linear equivalence gives the
corresponding adic power submodule on the source. -/
theorem linearEquiv_comap_pow_smul_top
    {R M N : Type*} [CommRing R] (I : Ideal R)
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (n : ℕ) :
    ((I ^ n • ⊤ : Submodule R N).comap (e : M →ₗ[R] N)) =
      (I ^ n • ⊤ : Submodule R M) := by
  rw [Submodule.comap_equiv_eq_map_symm]
  rw [Submodule.map_smul'']
  rw [Submodule.map_top]
  simp

/-- Mapping an adic power submodule along a linear equivalence gives the
corresponding adic power submodule on the target. -/
theorem linearEquiv_map_pow_smul_top
    {R M N : Type*} [CommRing R] (I : Ideal R)
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (n : ℕ) :
    ((I ^ n • ⊤ : Submodule R M).map (e : M →ₗ[R] N)) =
      (I ^ n • ⊤ : Submodule R N) := by
  rw [Submodule.map_smul'']
  rw [Submodule.map_top]
  simp

/-- Adic Hausdorffness is preserved by linear equivalence of modules. -/
theorem isHausdorff_of_linearEquiv
    {R M N : Type*} [CommRing R] (I : Ideal R)
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N)
    [IsHausdorff I M] : IsHausdorff I N := by
  refine ⟨fun y hy => ?_⟩
  have hsymm : e.symm y = 0 := by
    apply IsHausdorff.haus (I := I) (M := M) (show IsHausdorff I M from inferInstance)
    intro n
    have hy' : e.symm y ≡ e.symm 0
        [SMOD ((I ^ n • ⊤ : Submodule R N).comap (e : M →ₗ[R] N))] := by
      have hy0 : e (e.symm y) ≡ e (e.symm 0)
          [SMOD (I ^ n • ⊤ : Submodule R N)] := by
        simpa using hy n
      exact SModEq.comap (I ^ n • ⊤ : Submodule R N) (f := (e : M →ₗ[R] N)) hy0
    simpa [linearEquiv_comap_pow_smul_top (I := I) e n] using hy'
  exact e.symm.injective (by simpa using hsymm)

/-- Adic precompleteness is preserved by linear equivalence of modules. -/
theorem isPrecomplete_of_linearEquiv
    {R M N : Type*} [CommRing R] (I : Ideal R)
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N)
    [IsPrecomplete I M] : IsPrecomplete I N := by
  refine ⟨fun f hf => ?_⟩
  have hcf :
      ∀ {m n : ℕ}, m ≤ n →
        e.symm (f m) ≡ e.symm (f n) [SMOD (I ^ m • ⊤ : Submodule R M)] := by
    intro m n hmn
    have hfn : e (e.symm (f m)) ≡ e (e.symm (f n))
        [SMOD (I ^ m • ⊤ : Submodule R N)] := by
      simpa using hf hmn
    have hcomap : e.symm (f m) ≡ e.symm (f n)
        [SMOD ((I ^ m • ⊤ : Submodule R N).comap (e : M →ₗ[R] N))] :=
      SModEq.comap (I ^ m • ⊤ : Submodule R N) (f := (e : M →ₗ[R] N)) hfn
    simpa [linearEquiv_comap_pow_smul_top (I := I) e m] using hcomap
  obtain ⟨L, hL⟩ := IsPrecomplete.prec
    (show IsPrecomplete I M from inferInstance) hcf
  refine ⟨e L, fun n => ?_⟩
  have hmap : e (e.symm (f n)) ≡ e L
      [SMOD ((I ^ n • ⊤ : Submodule R M).map (e : M →ₗ[R] N))] :=
    SModEq.map (hL n) (e : M →ₗ[R] N)
  simpa [linearEquiv_map_pow_smul_top (I := I) e n] using hmap

/-- Hausdorffness for an ideal is invariant under a linear equivalence. -/
theorem isHausdorff_linearEquiv_iff
    {R M N : Type*} [CommRing R] (I : Ideal R)
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    IsHausdorff I N ↔ IsHausdorff I M := by
  constructor
  · intro h
    let : IsHausdorff I N := h
    exact isHausdorff_of_linearEquiv I e.symm
  · intro h
    let : IsHausdorff I M := h
    exact isHausdorff_of_linearEquiv I e

/-- Precompleteness for an ideal is invariant under a linear equivalence. -/
theorem isPrecomplete_linearEquiv_iff
    {R M N : Type*} [CommRing R] (I : Ideal R)
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    IsPrecomplete I N ↔ IsPrecomplete I M := by
  constructor
  · intro h
    let : IsPrecomplete I N := h
    exact isPrecomplete_of_linearEquiv I e.symm
  · intro h
    let : IsPrecomplete I M := h
    exact isPrecomplete_of_linearEquiv I e

/-- Same-universe finite modules over a Noetherian adically complete ring are
adically complete. -/
theorem isAdicComplete_of_moduleFinite_sameUniverse
    {R M : Type u} [CommRing R] (I : Ideal R)
    [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M]
    [IsAdicComplete I R] :
    IsAdicComplete I M := by
  refine AdicCompletion.of_bijective_iff.mp ?_
  let e : M ≃ₗ[R] AdicCompletion I M :=
    (TensorProduct.lid R M).symm.trans
      ((TensorProduct.congr (AdicCompletion.ofLinearEquiv I R)
        (LinearEquiv.refl R M)).trans
        ((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M).restrictScalars R))
  have heq : (e : M →ₗ[R] AdicCompletion I M) = AdicCompletion.of I M := by
    ext x n
    simp [e]
    exact one_smul (R ⧸ (I ^ n • ⊤ : Ideal R))
      (Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R M)) x)
  have hebij : Function.Bijective (e : M → AdicCompletion I M) := e.bijective
  rw [← heq]
  exact hebij

/-- A finite module over a Noetherian adically complete ring is adically complete.

This is a universe-polymorphic wrapper around mathlib's tensor-product
finite-module completion theorem. -/
theorem isAdicComplete_of_moduleFinite
    {R : Type u} {M : Type v} [CommRing R] (I : Ideal R)
    [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M]
    [IsAdicComplete I R] :
    IsAdicComplete I M := by
  let : Small.{u} M := Module.Finite.small R M
  let : Module.Finite R (Shrink.{u} M) :=
    Module.Finite.of_surjective
      ((Shrink.linearEquiv R M).symm : M →ₗ[R] Shrink.{u} M)
      (Shrink.linearEquiv R M).symm.surjective
  have : IsAdicComplete I (Shrink.{u} M) :=
    isAdicComplete_of_moduleFinite_sameUniverse (I := I)
  exact ValuationTheory.DiscreteValuationField.isAdicComplete_of_linearEquiv
    (I := I) (Shrink.linearEquiv R M)

/-- A finite algebra over a Noetherian `I`-adically complete base is Henselian
along the ideal generated by `I`. -/
theorem henselianRing_map_algebraMap_of_moduleFinite_of_isAdicComplete
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {I : Ideal R} [IsNoetherianRing R] [Module.Finite R S]
    [IsAdicComplete I R] :
    HenselianRing S (I.map (algebraMap R S)) := by
  have hRS : IsAdicComplete I S :=
    isAdicComplete_of_moduleFinite (I := I) (M := S)
  have hmap : IsAdicComplete (I.map (algebraMap R S)) S :=
    (isAdicComplete_map_algebraMap_iff (I := I) (S := S)).2 hRS
  let : IsAdicComplete (I.map (algebraMap R S)) S := hmap
  infer_instance

namespace HenselianDVF

variable {K : Type u} [Field K]

/-- The maximal-ideal topology on a Henselian DVF valuation ring is separated.

The proof uses only the Henselian Jacobson condition together with the
Noetherian DVR structure of the valuation ring. -/
theorem isHausdorff_maximalIdeal (F : HenselianDVF.{u, v} K) :
    IsHausdorff F.maximalIdeal F.valuationSubring := by
  let : IsNoetherianRing F.valuationSubring :=
    F.toDVF.valuationSubring_isNoetherianRing
  exact
    IsHausdorff.of_le_jacobson
      (R := F.valuationSubring) (M := F.valuationSubring)
      (I := F.maximalIdeal)
      (show F.maximalIdeal ≤
          Ideal.jacobson (⊥ : Ideal F.valuationSubring) from
        HenselianRing.jac)

/-- A precomplete Henselian DVF valuation ring is adically complete at its
maximal ideal, since separatedness is automatic. -/
theorem isAdicComplete_maximalIdeal_of_isPrecomplete
    (F : HenselianDVF.{u, v} K)
    [IsPrecomplete F.maximalIdeal F.valuationSubring] :
    IsAdicComplete F.maximalIdeal F.valuationSubring where
  toIsHausdorff := F.isHausdorff_maximalIdeal
  toIsPrecomplete := inferInstance

end HenselianDVF

end DiscreteValuationField

end

end ValuationTheory
