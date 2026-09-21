/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.TransposedFilteredModuleSupport
import LeanPool.Stafford38.Stafford38.Characteristic.AssociatedGradedFinite
import LeanPool.Stafford38.Stafford38.PaperInputs

namespace Stafford38.Characteristic.CanonicalSupportAvoidanceFromCokernel

open Stafford38.Characteristic
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CharacteristicTransposedFilteredModuleSupport
open Stafford38.WeylEulerResidue
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylTranspositionFiltration

noncomputable section

universe u
variable (k : Type u) [Field k]

/-! A zero coordinate cokernel has empty support.  Transposition fixes the
coordinate variable, so the same empty-support statement excludes the
coordinate zero locus from the transposed support. -/
theorem canonical_support_avoidance_of_coordinate_cokernel_subsingleton
    (n N : ℕ) (d : PresentedWeyl k (n + 1))
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)
    (hzero : Subsingleton (QuotSMulTop
      (MvPolynomial.X (.inl (0 : Fin (n + 1))) : SymbolRing k (n + 1))
      (OrderAssociatedGradedModule k
        (canonicalRightIdeal (presentedCoordinate k n) d N)))) :
    Disjoint
      (transposedOrderAssociatedGradedSupport k
        (canonicalRightIdeal (presentedCoordinate k n) d N))
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl (0 : Fin (n + 1)))} :
          Set (SymbolRing k (n + 1)))) := by
  let R := SymbolRing k (n + 1)
  let I := canonicalRightIdeal (presentedCoordinate k n) d N
  let E := OrderAssociatedGradedModule k I
  let x : R := MvPolynomial.X (.inl (0 : Fin (n + 1)))
  let τ : R →+* R := (symbolTranspositionEquiv k).toRingEquiv.toRingHom
  let qmod := QuotSMulTop x E
  let : Subsingleton qmod := hzero
  have hqempty : Module.support R qmod = ∅ := Module.support_eq_empty
  rw [transposedOrderAssociatedGradedSupport_eq_preimage]
  apply Set.disjoint_left.2
  intro p hp haxis
  let q : PrimeSpectrum R := PrimeSpectrum.comap τ p
  have hq : q ∈ Module.support R E := hp
  have hqx : q ∈ PrimeSpectrum.zeroLocus ({x} : Set R) := by
    rw [PrimeSpectrum.mem_zeroLocus]
    intro y hy
    have hyx : y = x := by simpa using hy
    subst y
    change τ x ∈ p.asIdeal
    have hτ : τ x = x := by
      change symbolTransposition k (MvPolynomial.X (.inl (0 : Fin (n + 1)))) = _
      exact symbolTransposition_coordinate k 0
    rw [hτ]
    exact haxis (by simp [x])
  have hqmod : q ∈ Module.support R qmod := by
    rw [Module.support_quotSMulTop]
    exact ⟨hq, hqx⟩
  rw [hqempty] at hqmod
  exact hqmod

end
end Stafford38.Characteristic.CanonicalSupportAvoidanceFromCokernel
