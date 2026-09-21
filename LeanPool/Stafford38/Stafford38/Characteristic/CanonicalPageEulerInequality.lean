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

/-!
The localized Euler length inequality for canonical two-term pages.
-/

namespace Stafford38.Characteristic.CanonicalPageEulerInequality
open Stafford38.Characteristic
open Stafford38.Characteristic.FilteredTwoTermPages
open Stafford38.Characteristic.CanonicalTangentialTotalAction
open Stafford38.Characteristic.LocalizedKernelCokernelEquivalences
open Stafford38.Characteristic.TwoTermPageLength
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylIteratedEquivalence
noncomputable section
variable (k : Type*) [Field k]
variable (n N : ℕ) (d : PresentedWeyl k (n + 1))
variable (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
variable (S : Submonoid (MvPolynomial (Fin n ⊕ Fin n) k))
attribute [local instance] sourceModule targetModule
private def sourceSuccLocalized (r : ℕ) :
    LocalizedModule S ((complex k n N d).SourceTotal ((r + 1) + 1)) ≃ₗ[Localization S]
      LinearMap.ker (localizedMap S (tangentialDrop k n N d (r + 1))) := by
  exact (localizedEquiv
    (U := (complex k n N d).SourceTotal ((r + 1) + 1))
    (V := LinearMap.ker (tangentialDrop k n N d (r + 1))) S
    (tangentialSourceSuccEquiv k n N d (r + 1))).trans
      (localizedKernelEquiv S (tangentialDrop k n N d (r + 1)))

private def targetSuccLocalized (r : ℕ) :
    LocalizedModule S ((complex k n N d).TargetTotal ((r + 1) + 1)) ≃ₗ[Localization S]
      LocalizedModule S ((complex k n N d).TargetTotal (r + 1)) ⧸
        LinearMap.range (localizedMap S (tangentialDrop k n N d (r + 1))) := by
  exact (localizedEquiv S (tangentialTargetSuccEquiv k n N d (r + 1))).trans
    (localizedCokernelEquiv S (tangentialDrop k n N d (r + 1)))

include hd in
private theorem localized_boundary_subsingleton [Algebra ℚ k]
    (hC0 : IsFiniteLength (Localization S)
      (LocalizedModule S ((complex k n N d).TargetTotal 1))) :
    ∃ r, Subsingleton (LocalizedModule S ((complex k n N d).TargetTotal (r + 1))) := by
  let : IsNoetherian (Localization S)
      (LocalizedModule S ((complex k n N d).TargetTotal 1)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hC0).1
  exact exists_uniform_subsingleton_localized S
    (fun r => tangentialBoundaryMap k n N d r)
    (tangentialBoundaryMap_ker_mono k n N d)
    (fun z => tangentialBoundaryMap_eventually_zero k n N d hd z)
    (fun r => tangentialBoundaryMap_surjective k n N d r)

private theorem page_inequality_of_subsingleton
    (r : ℕ) (hr : Subsingleton
      (LocalizedModule S ((complex k n N d).TargetTotal (r + 1)))) : ∀
    (_hA0 : IsFiniteLength (Localization S)
      (LocalizedModule S ((complex k n N d).SourceTotal 1)))
    (_hC0 : IsFiniteLength (Localization S)
      (LocalizedModule S ((complex k n N d).TargetTotal 1))),
    Module.length (Localization S) (LocalizedModule S ((complex k n N d).TargetTotal 1)) ≤
      Module.length (Localization S) (LocalizedModule S ((complex k n N d).SourceTotal 1)) := by
  intro hA0 hC0
  have h := @twoTermPage_length_target_le_source (Localization S) _
    (fun r => LocalizedModule S ((complex k n N d).SourceTotal (r + 1)))
    (fun r => LocalizedModule S ((complex k n N d).TargetTotal (r + 1)))
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => inferInstance) (fun _ => inferInstance)
    hA0 hC0 (fun r => localizedMap S (tangentialDrop k n N d (r + 1)))
    (sourceSuccLocalized k n N d S) (targetSuccLocalized k n N d S) r hr
  exact h


include hd in
theorem canonicalPage_length_target_le_source [Algebra ℚ k] : ∀
    (_hA0 : IsFiniteLength (Localization S)
      (LocalizedModule S ((complex k n N d).SourceTotal 1)))
    (_hC0 : IsFiniteLength (Localization S)
      (LocalizedModule S ((complex k n N d).TargetTotal 1))),
    Module.length (Localization S) (LocalizedModule S ((complex k n N d).TargetTotal 1)) ≤
      Module.length (Localization S) (LocalizedModule S ((complex k n N d).SourceTotal 1)) := by
  intro hA0 hC0
  obtain ⟨r, hr⟩ := localized_boundary_subsingleton k n N d hd S hC0
  exact page_inequality_of_subsingleton k n N d S r hr hA0 hC0

end
end Stafford38.Characteristic.CanonicalPageEulerInequality
