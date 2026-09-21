/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalTangentialSuccessors
import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalTangentialBoundaryMaps
import LeanPool.Stafford38.Stafford38.Characteristic.LocalizedKernelCokernelEquivalences
import LeanPool.Stafford38.Stafford38.Characteristic.UniformBoundaryVanishing
import LeanPool.Stafford38.Stafford38.Characteristic.TwoTermPageLength

namespace Stafford38.Characteristic.CanonicalPageEulerInequality
open Stafford38.Characteristic
open Stafford38.Characteristic.FilteredTwoTermPages
open Stafford38.Characteristic.CanonicalTangentialTotalAction
open Stafford38.Characteristic.LocalizedKernelCokernelEquivalences
open Stafford38.Characteristic.TwoTermPageLength
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylIteratedEquivalence
noncomputable section
variable (k : Type*) [Field k] [Algebra ℚ k]
variable (n N : ℕ) (d : PresentedWeyl k (n + 1))
variable (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
variable (S : Submonoid (MvPolynomial (Fin n ⊕ Fin n) k))
attribute [local instance] sourceModule targetModule
theorem canonicalPage_length_target_le_source : ∀
    (hA0 : IsFiniteLength (Localization S)
      (LocalizedModule S ((complex k n N d hd).SourceTotal 1)))
    (hC0 : IsFiniteLength (Localization S)
      (LocalizedModule S ((complex k n N d hd).TargetTotal 1))),
    Module.length (Localization S) (LocalizedModule S ((complex k n N d hd).TargetTotal 1)) ≤
      Module.length (Localization S) (LocalizedModule S ((complex k n N d hd).SourceTotal 1)) := by
  intro hA0 hC0
  let A : ℕ → Type _ := fun r => LocalizedModule S ((complex k n N d hd).SourceTotal (r+1))
  let C : ℕ → Type _ := fun r => LocalizedModule S ((complex k n N d hd).TargetTotal (r+1))
  letI : ∀ r, AddCommGroup (A r) := fun r => by dsimp only [A]; infer_instance
  letI : ∀ r, Module (Localization S) (A r) := fun r => by dsimp only [A]; infer_instance
  letI : ∀ r, AddCommGroup (C r) := fun r => by dsimp only [C]; infer_instance
  letI : ∀ r, Module (Localization S) (C r) := fun r => by dsimp only [C]; infer_instance
  let dd : ∀ r, A r →ₗ[Localization S] C r := fun r =>
    localizedMap S (tangentialDrop k n N d hd (r+1))
  have hA0' : IsFiniteLength (Localization S) (A 0) := by simpa [A] using hA0
  have hC0' : IsFiniteLength (Localization S) (C 0) := by simpa [C] using hC0
  have hs : ∀ r, A (r+1) ≃ₗ[Localization S] LinearMap.ker (dd r) := by
    intro r
    dsimp only [A, dd]
    exact (localizedEquiv
      (U := (complex k n N d hd).SourceTotal ((r + 1) + 1))
      (V := LinearMap.ker (tangentialDrop k n N d hd (r + 1))) S
      (tangentialSourceSuccEquiv k n N d hd (r+1))).trans
        (localizedKernelEquiv S (tangentialDrop k n N d hd (r+1)))
  have ht : ∀ r, C (r+1) ≃ₗ[Localization S] C r ⧸ LinearMap.range (dd r) := by
    intro r
    dsimp only [C, dd]
    exact (localizedEquiv S (tangentialTargetSuccEquiv k n N d hd (r+1))).trans
      (localizedCokernelEquiv S (tangentialDrop k n N d hd (r+1)))
  letI : IsNoetherian (Localization S)
      (LocalizedModule S ((complex k n N d hd).TargetTotal 1)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hC0).1
  obtain ⟨N', hN'⟩ := exists_uniform_subsingleton_localized S
    (fun r => tangentialBoundaryMap k n N d hd r)
    (tangentialBoundaryMap_ker_mono k n N d hd)
    (fun z => tangentialBoundaryMap_eventually_zero k n N d hd z)
    (fun r => tangentialBoundaryMap_surjective k n N d hd r)
  simpa [A, C] using twoTermPage_length_target_le_source A C hA0' hC0' dd hs ht N'
 #print axioms canonicalPage_length_target_le_source

end
end Stafford38.Characteristic.CanonicalPageEulerInequality
