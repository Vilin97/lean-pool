/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Module.BaseLocalizationModuleComparison
import LeanPool.Stafford38.AlgebraicAnalysis.Module.LocalizedKernelCokernelEquivalences
import LeanPool.Stafford38.AlgebraicAnalysis.Module.MinimalSupportKernelCokernelLengths
import LeanPool.Stafford38.AlgebraicAnalysis.Module.LocalizedMinimalSupportAvoidance
import LeanPool.Stafford38.AlgebraicAnalysis.Module.PrincipalKoszulMinimalSupportPositivity

/-!
Strict positivity of the localized principal Koszul Euler characteristic over the base ring.
-/

namespace AlgebraicAnalysis.BaseLocalizedKoszulPositivity

open scoped Pointwise
open AlgebraicAnalysis
open AlgebraicAnalysis.BaseLocalizationModuleComparison
open AlgebraicAnalysis.LocalizedKernelCokernelEquivalences
open AlgebraicAnalysis.LocalizedMinimalSupportAvoidance
open AlgebraicAnalysis.PrincipalKoszulMinimalSupportPositivity

noncomputable section

variable {R C E : Type*} [CommRing R] [CommRing C] [Algebra R C]
variable [AddCommGroup E] [Module R E] [Module C E] [IsScalarTower R C E]
variable [IsNoetherianRing R] [IsNoetherianRing C] [Module.Finite C E]

theorem localized_length_cokernel_gt_kernel
    (x : C)
    [Module.Finite R
      (LinearMap.ker ((LinearMap.lsmul C E x).restrictScalars R))]
    [Module.Finite R
      (E ⧸ LinearMap.range ((LinearMap.lsmul C E x).restrictScalars R))]
    (q : PrimeSpectrum R)
    (hqmem : q ∈ Module.support R
      (E ⧸ LinearMap.range ((LinearMap.lsmul C E x).restrictScalars R)))
    (hqmin : ∀ p ∈ Module.support R
        (E ⧸ LinearMap.range ((LinearMap.lsmul C E x).restrictScalars R)),
      p.asIdeal ≤ q.asIdeal → q.asIdeal ≤ p.asIdeal)
    (havoid : ∀ p ∈ (Module.annihilator C E).minimalPrimes, x ∉ p) :
    Module.length (Localization q.asIdeal.primeCompl)
        (LocalizedModule q.asIdeal.primeCompl
          (E ⧸ LinearMap.range ((LinearMap.lsmul C E x).restrictScalars R))) >
      Module.length (Localization q.asIdeal.primeCompl)
        (LocalizedModule q.asIdeal.primeCompl
          (LinearMap.ker ((LinearMap.lsmul C E x).restrictScalars R))) := by
  let S : Submonoid R := q.asIdeal.primeCompl
  let SC : Submonoid C := Algebra.algebraMapSubmonoid C S
  let fC : Module.End C E := LinearMap.lsmul C E x
  let fR : Module.End R E := fC.restrictScalars R
  have hfinite := localized_kernel_and_cokernel_isFiniteLength fC q hqmem hqmin
  have hcokerfinite : IsFiniteLength (Localization S)
      (LocalizedModule S (E ⧸ LinearMap.range fR)) := by
    simpa only [S, fR, fC] using hfinite.1
  have hkerfinite : IsFiniteLength (Localization S)
      (LocalizedModule S (LinearMap.ker fR)) := by
    simpa only [S, fR, fC] using hfinite.2
  let : Module (Localization S) (LocalizedModule SC E) :=
    Module.compHom _ (algebraMap (Localization S) (Localization SC))
  let : IsScalarTower (Localization S) (Localization SC)
      (LocalizedModule SC E) :=
    IsScalarTower.of_compHom (Localization S) (Localization SC)
      (LocalizedModule SC E)
  let e : LocalizedModule S E ≃ₗ[Localization S] LocalizedModule SC E :=
    localizedModuleComparison S
  let gR : Module.End (Localization S) (LocalizedModule S E) := localizedMap S fR
  let y : Localization SC := algebraMap C (Localization SC) x
  let gC : Module.End (Localization SC) (LocalizedModule SC E) :=
    LinearMap.lsmul (Localization SC) (LocalizedModule SC E) y
  have heq (z : LocalizedModule S E) : e (gR z) = gC (e z) := by
    rw [show e (gR z) = LocalizedModule.map SC fC (e z) by
      exact localizedModuleComparison_natural S fC z]
    induction e z using LocalizedModule.induction_on with
    | _ m s => simp [gC, y, fC, LocalizedModule.smul'_mk]
  let ek : LinearMap.ker gR ≃ₗ[Localization S]
      LinearMap.ker (gC.restrictScalars (Localization S)) :=
    LinearEquiv.ofBijective
      (e.toLinearMap.domRestrict (LinearMap.ker gR) |>.codRestrict
        (LinearMap.ker (gC.restrictScalars (Localization S))) (fun z => by
          exact LinearMap.mem_ker.mpr (by simpa using (heq z).symm)))
      (by
        constructor
        · intro a b hab
          exact Subtype.ext (e.injective (congrArg Subtype.val hab))
        · intro z
          refine ⟨⟨e.symm z, ?_⟩, Subtype.ext (e.apply_symm_apply z)⟩
          exact LinearMap.mem_ker.mpr (e.injective (by
            rw [heq]
            simpa using z.property)))
  have herange : Submodule.map e.toLinearMap (LinearMap.range gR) =
      LinearMap.range (gC.restrictScalars (Localization S)) := by
    ext z
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨e a, by simpa using (heq a).symm⟩
    · rintro ⟨a, rfl⟩
      refine ⟨gR (e.symm a), ⟨e.symm a, rfl⟩, ?_⟩
      simpa using heq (e.symm a)
  let ec : (LocalizedModule S E ⧸ LinearMap.range gR) ≃ₗ[Localization S]
      (LocalizedModule SC E ⧸ LinearMap.range
        (gC.restrictScalars (Localization S))) :=
    Submodule.Quotient.equiv _ _ e herange
  have hnontrivBase : Nontrivial
      (LocalizedModule S (E ⧸ LinearMap.range fR)) :=
    Module.mem_support_iff.mp (by simpa only [S, fR, fC] using hqmem)
  have hnontrivCokerR : Nontrivial
      (LocalizedModule S E ⧸ LinearMap.range gR) :=
    not_subsingleton_iff_nontrivial.mp (by
      intro hs
      let := hs
      have : Subsingleton (LocalizedModule S (E ⧸ LinearMap.range fR)) :=
        (localizedCokernelEquiv S fR).toEquiv.subsingleton_congr.mpr inferInstance
      exact not_subsingleton_iff_nontrivial.mpr hnontrivBase inferInstance)
  have hnontrivCokerC : Nontrivial
      (LocalizedModule SC E ⧸ LinearMap.range
        (gC.restrictScalars (Localization S))) :=
    not_subsingleton_iff_nontrivial.mp (by
      intro hs
      exact not_subsingleton_iff_nontrivial.mpr hnontrivCokerR
        (ec.toEquiv.subsingleton_congr.mpr hs))
  have hrange : LinearMap.range gC = y • (⊤ : Submodule (Localization SC)
      (LocalizedModule SC E)) := by
    ext z
    rw [LinearMap.mem_range, Submodule.mem_smul_pointwise_iff_exists]
    simp only [Submodule.mem_top, true_and]
    rfl
  have hnontrivQuot : Nontrivial (QuotSMulTop y (LocalizedModule SC E)) := by
    change Nontrivial (LocalizedModule SC E ⧸
      y • (⊤ : Submodule (Localization SC) (LocalizedModule SC E)))
    rw [← hrange]
    exact hnontrivCokerC
  have havoid' := localized_minimalPrime_avoids SC x havoid
  have hkbase : IsFiniteLength (Localization S) (LinearMap.ker gR) :=
    (localizedKernelEquiv S fR).isFiniteLength hkerfinite
  have hkfinite : IsFiniteLength (Localization S)
      (LinearMap.ker (gC.restrictScalars (Localization S))) :=
    ek.isFiniteLength hkbase
  have hpos := length_cokernel_gt_kernel_of_minimal_support
    (R := Localization S) (C := Localization SC) (E := LocalizedModule SC E)
    y havoid' hnontrivQuot hkfinite
  rw [← ec.length_eq, ← (localizedCokernelEquiv S fR).length_eq,
    ← ek.length_eq, ← (localizedKernelEquiv S fR).length_eq] at hpos
  simpa only [S, fR, fC] using hpos


end
end AlgebraicAnalysis.BaseLocalizedKoszulPositivity
