/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule


/-!
# Kernel and cokernel equivalences for module localization

The actual localization functor preserves the two elementary constructions
needed by the successor pages.  The equivalences below are obtained from the
canonical submodule and quotient localization equivalences in Mathlib.
-/

@[expose] public section

namespace AlgebraicAnalysis.LocalizedKernelCokernelEquivalences

universe u v w

variable {R : Type u} [CommRing R]
variable {U : Type v} {V : Type w}
variable [AddCommGroup U] [AddCommGroup V]
variable [Module R U] [Module R V]

noncomputable section

variable (S : Submonoid R) (f : U →ₗ[R] V)

/-- The localization of an `R`-linear map, regarded as a map over the
localized ring. -/
noncomputable def localizedMap : LocalizedModule S U →ₗ[Localization S]
    LocalizedModule S V :=
  (LocalizedModule.map S f).extendScalarsOfIsLocalization S (Localization S)

@[simp]
theorem localizedMap_apply (x : LocalizedModule S U) :
    localizedMap S f x = LocalizedModule.map S f x :=
  rfl

/-- Localization carries an actual linear equivalence to an equivalence over
the localized ring. -/
noncomputable def localizedEquiv (e : U ≃ₗ[R] V) :
    LocalizedModule S U ≃ₗ[Localization S] LocalizedModule S V :=
  LinearEquiv.ofBijective (localizedMap S e.toLinearMap) (by
    constructor
    · simpa [localizedMap] using
        (LocalizedModule.map_injective S e.toLinearMap e.injective)
    · simpa [localizedMap] using
        (LocalizedModule.map_surjective S e.toLinearMap e.surjective))

/-- Localization commutes with kernels. -/
noncomputable def localizedKernelEquiv :
    LocalizedModule S (LinearMap.ker f) ≃ₗ[Localization S]
      LinearMap.ker (localizedMap S f) := by
  let e₁ : (LinearMap.ker f).localized' (Localization S) S
      (LocalizedModule.mkLinearMap S U) ≃ₗ[Localization S]
      LocalizedModule S (LinearMap.ker f) :=
    Submodule.localizedEquiv S (LinearMap.ker f)
  let e₂ : (LinearMap.ker f).localized' (Localization S) S
      (LocalizedModule.mkLinearMap S U) ≃ₗ[Localization S]
      LinearMap.ker (localizedMap S f) :=
    LinearEquiv.ofEq _ _
      (LinearMap.localized'_ker_eq_ker_localizedMap (Localization S) S
        (LocalizedModule.mkLinearMap S U) (LocalizedModule.mkLinearMap S V) f)
  exact e₁.symm.trans e₂

/-- Localization commutes with cokernels. -/
noncomputable def localizedCokernelEquiv :
    LocalizedModule S (V ⧸ LinearMap.range f) ≃ₗ[Localization S]
      LocalizedModule S V ⧸ LinearMap.range (localizedMap S f) := by
  let h : Submodule.localized S (LinearMap.range f) =
      LinearMap.range (localizedMap S f) := by
    have hm :
        IsLocalizedModule.map S (LocalizedModule.mkLinearMap S U)
            (LocalizedModule.mkLinearMap S V) f = LocalizedModule.map S f := by
      ext x
      induction x using LocalizedModule.induction_on with
      | _ x s =>
        rw [IsLocalizedModule.map_LocalizedModules]
        exact (LocalizedModule.map_mk S f x s).symm
    simpa [localizedMap, hm] using
      (LinearMap.localized'_range_eq_range_localizedMap
        (Localization S) S (LocalizedModule.mkLinearMap S U)
        (LocalizedModule.mkLinearMap S V) f)
  let e₁ : (LocalizedModule S V ⧸
      Submodule.localized S (LinearMap.range f)) ≃ₗ[Localization S]
      LocalizedModule S (V ⧸ LinearMap.range f) :=
    localizedQuotientEquiv S (LinearMap.range f)
  let e : LocalizedModule S V ≃ₗ[Localization S] LocalizedModule S V :=
    LinearEquiv.refl _ _
  exact e₁.symm.trans
    (Submodule.Quotient.equiv _ _ e (by simpa [e] using h))

end
end AlgebraicAnalysis.LocalizedKernelCokernelEquivalences
