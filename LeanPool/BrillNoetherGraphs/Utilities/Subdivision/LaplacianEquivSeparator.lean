/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.StrongSeparator
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.LaplacianEquiv
public import Mathlib.Tactic

/-!
# Transport of strong-separator certificates along a Laplacian equivalence

`LaplacianEquiv` already transports divisors, firing scripts, winnability,
rank lower bounds, connectivity and `BNExists`.  What it did *not* transport is
the one remaining ingredient of the rank-one pipeline: the finite
`StrongSeparator.ExpansionCell` data and the `StrongSeparatorCertificate`
predicate assembled from it.

This file adds exactly that.  Every field of `ExpansionCell` is phrased in
`numEdges` and `Finset` membership, which is precisely the structure a
`LaplacianEquiv` preserves, so the transport is a pure relabeling: no graph
theory is redeveloped and no new hypothesis appears.

## Why this is the load-bearing piece for the closed length orthant

A degenerate subdivision (`Utilities.Certificate.DegenerateSpec.DegSpec`) at a face of the length
orthant is `LaplacianEquiv` to the strictly positive subdivision of the
*contracted* core (`DegSpec.Contraction.laplacianEquiv`).  The separator
argument of `Certificate/SubdivisionSeparator.lean` rests on injectivity of
`Spec.pathVertex`, which genuinely fails at a face — `coreVertex` is not
injective there.  Rather than redoing that argument in a setting where it is
false, we run it on the contracted *positive* spec, where it applies verbatim,
and pull the resulting certificate back along the equivalence.
-/

@[expose] public section

namespace Utilities.Certificate
open Utilities.Certificate

open Utilities

end Utilities.Certificate

namespace Utilities.Certificate.StrongSeparator
open Utilities
open Utilities.Certificate

open Utilities.Certificate
open Utilities
open Utilities.Certificate.StrongSeparator

open Finset

universe u v

/-! ## Finset images along an equivalence -/

section EquivImage
variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

theorem mem_image_equiv_apply (f : α ≃ β) (S : Finset α) (x : α) :
    f x ∈ S.image f ↔ x ∈ S := by
  constructor
  · intro h
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp h
    rwa [f.injective hzx] at hz
  · intro h
    exact Finset.mem_image_of_mem f h

theorem mem_image_equiv (f : α ≃ β) (S : Finset α) (y : β) :
    y ∈ S.image f ↔ f.symm y ∈ S := by
  rw [← mem_image_equiv_apply f S (f.symm y), Equiv.apply_symm_apply]

theorem mem_image_equiv_symm (f : α ≃ β) (T : Finset β) (x : α) :
    x ∈ T.image f.symm ↔ f x ∈ T := by
  constructor
  · intro h
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp h
    rw [← hzx, Equiv.apply_symm_apply]
    exact hz
  · intro h
    exact Finset.mem_image.mpr ⟨f x, h, f.symm_apply_apply x⟩

theorem image_equiv_symm_image (f : α ≃ β) (T : Finset β) :
    (T.image f.symm).image f = T := by
  ext y
  constructor
  · intro h
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp h
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx
    rwa [← hxy, ← hzx, Equiv.apply_symm_apply]
  · intro h
    exact Finset.mem_image.mpr
      ⟨f.symm y, Finset.mem_image.mpr ⟨y, h, rfl⟩, f.apply_symm_apply y⟩

theorem image_equiv_univ [Fintype α] [Fintype β] (f : α ≃ β) :
    (Finset.univ : Finset α).image f = Finset.univ := by
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
  exact ⟨f.symm y, f.apply_symm_apply y⟩

theorem image_equiv_symm_ne_univ [Fintype α] [Fintype β] (f : α ≃ β)
    {T : Finset β} (h : T ≠ Finset.univ) :
    T.image f.symm ≠ Finset.univ := by
  intro hEq
  apply h
  rw [← image_equiv_symm_image f T, hEq, image_equiv_univ]

end EquivImage

/-! ## The elementary quantities transport -/

variable {G : CFGraph.{u}} {H : CFGraph.{v}}

/-- `LaplacianEquiv.symm` reading, with the equivalence written on the target
side.  Stated separately so `rw` finds it without unfolding `symm`. -/
theorem num_edges_toEquiv_symm (φ : LaplacianEquiv G H) (x y : H.V) :
    numEdges G (φ.toEquiv.symm x) (φ.toEquiv.symm y) = numEdges H x y :=
  φ.symm.num_edges_eq x y

theorem intoMultiplicity_image (φ : LaplacianEquiv G H) (C : Finset G.V)
    (v : G.V) :
    intoMultiplicity H (C.image φ.toEquiv) (φ.toEquiv v) =
      intoMultiplicity G C v := by
  classical
  unfold intoMultiplicity
  rw [Finset.sum_image (fun a _ b _ h => φ.toEquiv.injective h)]
  exact Finset.sum_congr rfl fun x _ => by rw [φ.num_edges_eq]

theorem isBoundary_image (φ : LaplacianEquiv G H) (C : Finset G.V) (v : G.V) :
    IsBoundary H (C.image φ.toEquiv) (φ.toEquiv v) ↔ IsBoundary G C v := by
  constructor
  · rintro ⟨y, hy, hpos⟩
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    refine ⟨x, hx, ?_⟩
    rw [← φ.num_edges_eq v x, hxy]
    exact hpos
  · rintro ⟨x, hx, hpos⟩
    exact ⟨φ.toEquiv x, Finset.mem_image_of_mem _ hx,
      by rw [φ.num_edges_eq]; exact hpos⟩

/-! ## Transport of an expansion cell -/

/-- Relabel a complementary cell along a Laplacian equivalence.  Every field is
a `numEdges`/membership statement, so nothing but the labels changes. -/
def ExpansionCell.map (φ : LaplacianEquiv G H) {R : Finset G.V}
    (cell : ExpansionCell G R) : ExpansionCell H (R.image φ.toEquiv) where
  carrier := cell.carrier.image φ.toEquiv
  nonempty := cell.nonempty.image _
  disjoint := by
    rw [Finset.disjoint_left]
    intro y hy hyR
    rw [mem_image_equiv] at hy hyR
    exact (Finset.disjoint_left.mp cell.disjoint) hy hyR
  anchor := φ.toEquiv cell.anchor
  anchor_mem := Finset.mem_image_of_mem _ cell.anchor_mem
  anchor_boundary := (isBoundary_image φ _ _).mpr cell.anchor_boundary
  closed := by
    intro x y hx hy hxy
    rw [mem_image_equiv] at hx hy ⊢
    refine cell.closed hx hy ?_
    rw [num_edges_toEquiv_symm]
    exact hxy
  oneEdge := by
    intro y hy
    rw [mem_image_equiv] at hy
    have hy' : y = φ.toEquiv (φ.toEquiv.symm y) :=
      (φ.toEquiv.apply_symm_apply y).symm
    rw [hy', intoMultiplicity_image]
    exact cell.oneEdge hy
  pathCut := by
    intro t htR htBoundary A hAnchorA htNotA
    rw [mem_image_equiv] at htR
    have htEq : φ.toEquiv (φ.toEquiv.symm t) = t := φ.toEquiv.apply_symm_apply t
    have htB : IsBoundary G cell.carrier (φ.toEquiv.symm t) := by
      rw [← isBoundary_image φ, htEq]
      exact htBoundary
    have hmemA : ∀ x : G.V, x ∈ A.image φ.toEquiv.symm ↔ φ.toEquiv x ∈ A :=
      fun x => mem_image_equiv_symm φ.toEquiv A x
    have hAnchor : cell.anchor ∈ A.image φ.toEquiv.symm :=
      (hmemA cell.anchor).mpr hAnchorA
    have htNot : φ.toEquiv.symm t ∉ A.image φ.toEquiv.symm := by
      intro hmem
      exact htNotA (htEq ▸ (hmemA _).mp hmem)
    rcases cell.pathCut htR htB (A.image φ.toEquiv.symm) hAnchor htNot with
      hIncoming | hOutgoing
    · obtain ⟨x, hxCarrier, hxNotA, y, hyA, hxy⟩ := hIncoming
      refine Or.inl ⟨φ.toEquiv x, Finset.mem_image_of_mem _ hxCarrier, ?_,
        φ.toEquiv y, (hmemA y).mp hyA, ?_⟩
      · intro hmem
        exact hxNotA ((hmemA x).mpr hmem)
      · rw [φ.num_edges_eq]
        exact hxy
    · obtain ⟨x, hxCarrier, hxA, y, hyNotA, hxy⟩ := hOutgoing
      refine Or.inr ⟨φ.toEquiv x, Finset.mem_image_of_mem _ hxCarrier,
        (hmemA x).mp hxA, φ.toEquiv y, ?_, ?_⟩
      · intro hmem
        exact hyNotA ((hmemA y).mpr hmem)
      · rw [φ.num_edges_eq]
        exact hxy

/-! ## Transport of the certificate -/

/-- **The missing transport.**  A strong-separator certificate for `S` in `G`
is a strong-separator certificate for the relabeled set in `H`. -/
theorem strongSeparatorCertificate_image (φ : LaplacianEquiv G H)
    {S : Finset G.V} (hSeparator : StrongSeparatorCertificate G S) :
    StrongSeparatorCertificate H (S.image φ.toEquiv) := by
  classical
  intro R hS hNonempty hProper
  have hPulledSub : S ⊆ R.image φ.toEquiv.symm := by
    intro s hs
    rw [mem_image_equiv_symm]
    exact hS (Finset.mem_image_of_mem _ hs)
  have hPulledNonempty : (R.image φ.toEquiv.symm).Nonempty :=
    hNonempty.image _
  have hPulledProper : R.image φ.toEquiv.symm ≠ Finset.univ :=
    image_equiv_symm_ne_univ φ.toEquiv hProper
  obtain ⟨cell⟩ := hSeparator _ hPulledSub hPulledNonempty hPulledProper
  have hImage : (R.image φ.toEquiv.symm).image φ.toEquiv = R :=
    image_equiv_symm_image φ.toEquiv R
  exact ⟨hImage ▸ cell.map φ⟩

/-- The form used at a call site, where the relabeled separator has already
been identified with a set named on the target side. -/
theorem strongSeparatorCertificate_of_image (φ : LaplacianEquiv G H)
    {S : Finset G.V} {T : Finset H.V}
    (hT : S.image φ.toEquiv = T)
    (hSeparator : StrongSeparatorCertificate G S) :
    StrongSeparatorCertificate H T :=
  hT ▸ strongSeparatorCertificate_image φ hSeparator

end Utilities.Certificate.StrongSeparator

namespace Utilities.Certificate
open Utilities.Certificate
open Utilities

end Utilities.Certificate
