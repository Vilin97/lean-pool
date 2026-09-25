/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Sections.SectionFiveDefinitions
public import LeanPool.BrillNoetherGraphs.Bananas.Sections.SectionFiveTransports
public import LeanPool.BrillNoetherGraphs.Bananas.Sections.SectionFiveSymmetries
public import LeanPool.BrillNoetherGraphs.Bananas.Sections.SectionFiveInversionBound

/-!
# Section 5: symmetry statements

This is the formal statement ledger for the precise claims in Section 5 of
the twice-marked banana paper.  The qualitative ``quasi-symmetry'' discussion and
the two examples in that section deliberately have no theorem declarations.

The statements use the library's push-forward convention for
`CFGraphIso.mapDiv`.  Connectivity is explicit precisely where the
Riemann--Roch/tau-characteristic argument needs it; the paper has a global
connected-graph convention.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- Lemma 5.2(2), with the raw reflected inverse used by the current
transmission API. -/
theorem sectionFive_swap_value_iff
    {M : TwiceMarked} {D : CFDiv M.graph} {tau : ℤ → ℤ}
    (hTau : IsTransmissionPermutation M D tau) (a b : ℤ) :
    tau b = a ↔ swapTransmissionPermutation tau (-a) = -b := by
  exact sectionFive_swap_value_iff_proof hTau a b

/-- Lemma 5.2(3): canonical duality gives the inverse transmission
permutation at the exchanged marks. -/
theorem sectionFive_dual_transmission
    {G : CFGraph} (hconn : _root_.graphConnected G) (u v : G.V)
    {D : CFDiv G} {tau : ℤ → ℤ}
    (hTau : IsTransmissionPermutation (mark G u v) D tau) :
    IsTransmissionPermutation (mark G v u)
      (transmissionDualDivisor u v D) (rawInverse tau) := by
  exact sectionFive_dual_transmission_proof hconn u v hTau

/-- Lemma 5.2(4): graph isomorphisms preserve the same raw transmission
permutation while transporting both marks and the divisor. -/
theorem sectionFive_map_transmission
    {G H : CFGraph} (phi : CFGraphIso G H) (u v : G.V)
    {D : CFDiv G} {tau : ℤ → ℤ}
    (hTau : IsTransmissionPermutation (mark G u v) D tau) :
    IsTransmissionPermutation
      (mark H (phi.vertexEquiv u) (phi.vertexEquiv v))
      (phi.mapDiv D) tau := by
  exact sectionFive_map_transmission_proof phi u v hTau

/-- Lemma 5.3(1).  A mark-swapping automorphism that identifies its divisor
with the canonical dual forces the raw transmission permutation to be an
involution. -/
theorem sectionFive_tau_involutive_of_dual_automorphism
    {M : TwiceMarked} (hconn : _root_.graphConnected M.graph)
    (phi : MarkedPointSwap M)
    {D : CFDiv M.graph} {tau : ℤ → ℤ}
    (hTau : IsTransmissionPermutation M D tau)
    (hDual : linearEquiv M.graph
      (phi.toMarkedPointAutomorphism.iso.mapDiv D)
      (transmissionDualDivisor M.u M.v D)) :
    ∀ a b : ℤ, tau b = a ↔ tau a = b := by
  exact sectionFive_tau_involutive_of_dual_automorphism_connected
    hconn phi hTau hDual

/-- Lemma 5.3(2).  A mark-swapping automorphism differing from `D` by a
marked twist gives reflection symmetry about `n / 2`. -/
theorem sectionFive_tau_reflection_of_twisted_automorphism
    {M : TwiceMarked} (phi : MarkedPointSwap M)
    {D : CFDiv M.graph} {tau : ℤ → ℤ} (n : ℤ)
    (hTau : IsTransmissionPermutation M D tau)
    (hTwist : linearEquiv M.graph
      (phi.toMarkedPointAutomorphism.iso.mapDiv D - D)
      (n • (oneChip M.u - oneChip M.v))) :
    ∀ a b : ℤ, tau b = a ↔ tau (n - a) = n - b := by
  exact sectionFive_tau_reflection_of_twisted_automorphism_proved
    phi n hTau hTwist

/-- The final unlabelled proposition of Section 5.  The self-inverse
hypothesis is intentionally separate: Lemma 5.3(1) supplies it from a
marked-point automorphism. -/
theorem sectionFive_inversion_lower_bound_of_involutive_transmission
    {M : TwiceMarked} {D : CFDiv M.graph} {tau : ℤ → ℤ} {k : ℕ}
    (hk : 0 < k) (hconn : _root_.graphConnected M.graph)
    (hTau : IsTransmissionPermutation M D tau)
    (hAffine : IsKAffine k tau)
    (hInvolutive : ∀ a b : ℤ, tau b = a ↔ tau a = b) :
    sectionFiveRankDropSum M D k ≤ kInversionCount k tau := by
  exact sectionFive_inversion_lower_bound_of_involutive_transmission_connected
    hk hconn hTau hAffine hInvolutive

end Bananas
