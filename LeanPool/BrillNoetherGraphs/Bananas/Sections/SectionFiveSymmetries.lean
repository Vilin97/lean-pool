/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Sections.SectionFiveDefinitions
import LeanPool.BrillNoetherGraphs.Bananas.Sections.SectionFiveTransports

/-!
# Section 5: symmetries of transmission permutations

The two symmetry arguments are deliberately carried out at the raw
`IsTransmissionPermutation` level.  This keeps the graph relabeling and
linear-equivalence transports independent of the ASP packaging.
-/

namespace Bananas

open Utilities

private theorem isTransmissionPermutation_of_linearEquiv
    {M : TwiceMarked} {D E : CFDiv M.graph} {tau : ℤ → ℤ}
    (hDE : linear_equiv M.graph D E)
    (hTau : IsTransmissionPermutation M D tau) :
    IsTransmissionPermutation M E tau := by
  refine ⟨hTau.1, ?_⟩
  intro a b
  rw [hTau.2]
  apply rankDelta_eq_of_linearEquiv
  unfold linear_equiv at hDE ⊢
  have hDifference :
      (E + a • one_chip M.u - b • one_chip M.v) -
          (D + a • one_chip M.u - b • one_chip M.v) = E - D := by
    abel
  rw [hDifference]
  exact hDE

private theorem linearEquiv_of_sub_linearEquiv
    {G : CFGraph} {A B C : CFDiv G}
    (h : linear_equiv G (A - B) C) :
    linear_equiv G A (B + C) := by
  unfold linear_equiv at h ⊢
  have hDifference : (B + C) - A = C - (A - B) := by abel
  rw [hDifference]
  exact h

/-- Corrected Lemma 5.3(1): Riemann--Roch duality needs connectedness.
The statement ledger's unqualified version is therefore deliberately not
used: a disconnected chip-firing graph has no such duality theorem. -/
theorem sectionFive_tau_involutive_of_dual_automorphism_connected
    {M : TwiceMarked} (hconn : _root_.graph_connected M.graph)
    (phi : MarkedPointSwap M)
    {D : CFDiv M.graph} {tau : ℤ → ℤ}
    (hTau : IsTransmissionPermutation M D tau)
    (hDual : linear_equiv M.graph
      (phi.toMarkedPointAutomorphism.iso.mapDiv D)
      (transmissionDualDivisor M.u M.v D)) :
    ∀ a b : ℤ, tau b = a ↔ tau a = b := by
  have hMap : IsTransmissionPermutation (mark M.graph M.v M.u)
      (phi.toMarkedPointAutomorphism.iso.mapDiv D) tau :=
    (isTransmissionPermutation_mapDiv_of_marks_iff (M := M)
      (N := mark M.graph M.v M.u)
      phi.toMarkedPointAutomorphism.iso phi.map_u phi.map_v D tau).mpr hTau
  have hMappedDual : IsTransmissionPermutation (mark M.graph M.v M.u)
      (transmissionDualDivisor M.u M.v D) tau :=
    isTransmissionPermutation_of_linearEquiv hDual hMap
  have hDualTau : IsTransmissionPermutation (mark M.graph M.v M.u)
      (transmissionDualDivisor M.u M.v D) (rawInverse tau) := by
    exact sectionFive_dual_transmission_proof hconn M.u M.v hTau
  have hEq : tau = rawInverse tau :=
    transmissionPermutation_unique hMappedDual hDualTau
  have hInvolutive : ∀ x : ℤ, rawInverse tau (rawInverse tau x) = x := by
    intro x
    calc
      rawInverse tau (rawInverse tau x) = rawInverse tau (tau x) := by
        exact congrArg (fun f => rawInverse tau (f x)) hEq.symm
      _ = x := rawInverse_apply_apply tau hTau.1 x
  intro a b
  rw [hEq]
  constructor
  · intro h
    subst a
    exact hInvolutive b
  · intro h
    calc
      rawInverse tau b = rawInverse tau (rawInverse tau a) := by rw [h]
      _ = a := hInvolutive a

/-- Lemma 5.3(2), at the raw transmission level. -/
theorem sectionFive_tau_reflection_of_twisted_automorphism_proved
    {M : TwiceMarked} (phi : MarkedPointSwap M)
    {D : CFDiv M.graph} {tau : ℤ → ℤ} (n : ℤ)
    (hTau : IsTransmissionPermutation M D tau)
    (hTwist : linear_equiv M.graph
      (phi.toMarkedPointAutomorphism.iso.mapDiv D - D)
      (n • (one_chip M.u - one_chip M.v))) :
    ∀ a b : ℤ, tau b = a ↔ tau (n - a) = n - b := by
  have hMap : IsTransmissionPermutation (mark M.graph M.v M.u)
      (phi.toMarkedPointAutomorphism.iso.mapDiv D) tau :=
    (isTransmissionPermutation_mapDiv_of_marks_iff (M := M)
      (N := mark M.graph M.v M.u)
      phi.toMarkedPointAutomorphism.iso phi.map_u phi.map_v D tau).mpr hTau
  have hPhi : linear_equiv M.graph
      (phi.toMarkedPointAutomorphism.iso.mapDiv D)
      (D + n • (one_chip M.u - one_chip M.v)) := by
    exact linearEquiv_of_sub_linearEquiv hTwist
  have hShift : IsTransmissionPermutation (mark M.graph M.v M.u)
      (D + n • (one_chip M.u - one_chip M.v)) tau :=
    isTransmissionPermutation_of_linearEquiv hPhi hMap
  intro a b
  have hDiv :
      D + n • (one_chip M.u - one_chip M.v) + a • one_chip M.v -
          b • one_chip M.u =
        D + (n - b) • one_chip M.u - (n - a) • one_chip M.v := by
    ext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    ring
  have hRank :
      rankDelta (mark M.graph M.v M.u)
          (D + n • (one_chip M.u - one_chip M.v) + a • one_chip M.v -
            b • one_chip M.u) =
        rankDelta M (D + (n - b) • one_chip M.u -
          (n - a) • one_chip M.v) := by
    rw [rankDelta_mark_swap, hDiv]
  have hShiftValue := hShift.2 a b
  have hTauValue := hTau.2 (n - b) (n - a)
  change (if tau b = a then 1 else 0) =
      rankDelta (mark M.graph M.v M.u)
        (D + n • (one_chip M.u - one_chip M.v) + a • one_chip M.v -
          b • one_chip M.u) at hShiftValue
  constructor
  · intro h
    by_contra hNot
    rw [if_pos h, hRank] at hShiftValue
    rw [if_neg hNot] at hTauValue
    omega
  · intro h
    by_contra hNot
    rw [if_pos h] at hTauValue
    rw [if_neg hNot, hRank] at hShiftValue
    omega

end Bananas
