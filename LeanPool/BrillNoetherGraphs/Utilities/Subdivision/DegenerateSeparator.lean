/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.LaplacianEquivSeparator
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionSeparator
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionConnectivity
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateRankOne

/-!
# The strong separator and connectivity on the CLOSED length orthant

`Certificate/DegenerateRankOne.lean` ends at
`bnExists_of_validClosed_of_strongSeparator`, which still *assumes* graph
connectivity and a strong-separator certificate for the contracted core
classes.  On the open orthant those two hypotheses are discharged uniformly by
`SubdivisionSeparator.coreVertices_strongSeparatorCertificate` and
`SubdivisionConnectivity.graph_connected_of_coreConnected`, and the resulting
convenience wrapper is `bnExists_on_subdivision_of_valid`.  This file supplies
the closed-orthant analogue.

## The route, and why not the other one

The separator argument of `Certificate/SubdivisionSeparator.lean` rests on
`Spec.pathVertex_injective`.  That is **false at a face**: when a slot
collapses, `tail = head` and `coreVertex` stops being injective, so a naive
port of those 954 lines to `DegSpec` would be porting an argument to a setting
where its central lemma fails.

Instead we exploit the fact already proved in `Certificate/DegenerateSpec.lean`:
a `DegSpec` with a contraction datum is `LaplacianEquiv` to the **strictly
positive** `Spec` on the contracted core, where the existing machinery applies
unchanged.  `Certificate/LaplacianEquivSeparator.lean` transports an
`ExpansionCell` and a `StrongSeparatorCertificate` along a `LaplacianEquiv`;
here we pull both the separator and connectivity back through
`DegSpec.Contraction.laplacianEquiv`.

So `SubdivisionSeparator` is used, not reproved, and it is used only where its
hypotheses hold.

## No contraction datum has to be supplied

`DegSpec.canonicalContraction` builds the contracted target from the `DegSpec`
itself: its vertices are the `rep`-classes and its slots are the surviving
ones.  Consequently the wrapper below takes no target, no vertex map and no
slot map — only the same core-connectivity check
`ExplicitPotential.Core.Connected` (decided by `connectedCheck`) that the open
orthant already uses, stated on the **uncontracted** core.

## Hazard respected

Nothing here indexes anything by `Fin n` through `coreVertex`.  The separator
is the image `Finset` `degenerateCoreVertices d`, which is exactly the set of
`rep`-classes; `degenerateCoreVertices_eq_image` proves it is the relabeled
`coreVertices` of the contracted target without ever asserting injectivity.
-/

-- `Certificate` is a structure inside a namespace already ending in `Certificate`;
-- renaming either would ripple through every consumer.  Lean v4.33 added
-- `linter.dupNamespace`, which flags exactly this shape.
namespace Utilities.Certificate.DegenerateSpec.DegSpec
open Utilities.Certificate

open Utilities

open Finset ExplicitPotential

variable {n p : ℕ} (d : DegSpec n p)

/-! ## The canonical contraction target -/

/-- The surviving slots of a degenerate spec. -/
abbrev PositiveSlot := {e : Fin p // 0 < d.length e}

theorem class_nonempty : Nonempty d.Class :=
  ⟨⟨d.rep ⟨0, d.core_nonempty⟩, d.rep_idem _⟩⟩

/-- Number of contracted core classes. -/
def classCard : ℕ := Fintype.card d.Class

/-- Number of surviving slots. -/
def slotCard : ℕ := Fintype.card d.PositiveSlot

/-- An indexing of the contracted classes.  Any bijection will do; the
statements below never depend on the choice. -/
noncomputable def classIndex : d.Class ≃ Fin d.classCard :=
  Fintype.equivFin d.Class

/-- An indexing of the surviving slots. -/
noncomputable def slotIndex : d.PositiveSlot ≃ Fin d.slotCard :=
  Fintype.equivFin d.PositiveSlot

theorem classCard_pos : 0 < d.classCard :=
  Fintype.card_pos_iff.mpr d.class_nonempty

/-- The contracted core: one vertex per `rep`-class, one slot per surviving
slot, endpoints taken `rep`-wise. -/
noncomputable def contractedCore : ExplicitPotential.Core d.classCard d.slotCard where
  tail := fun e' =>
    d.classIndex ⟨d.rep (d.core.tail (d.slotIndex.symm e').val), d.rep_idem _⟩
  head := fun e' =>
    d.classIndex ⟨d.rep (d.core.head (d.slotIndex.symm e').val), d.rep_idem _⟩

/-- **The canonical contraction target.**  A genuinely positive
`SubdivisionGraph.Spec`, so every lemma of the open-orthant layer applies to
it verbatim. -/
noncomputable def contractedSpec :
    SubdivisionGraph.Spec d.classCard d.slotCard where
  core := d.contractedCore
  length := fun e' => d.length (d.slotIndex.symm e').val
  core_nonempty := d.classCard_pos
  core_loopless := by
    intro e' hEq
    refine d.rep_loopless (d.slotIndex.symm e').val
      (d.slotIndex.symm e').property ?_
    exact congrArg Subtype.val (d.classIndex.injective hEq)
  length_pos := fun e' => (d.slotIndex.symm e').property

/-- The `DegSpec` is a contraction onto its canonical target.  This is the
datum a row would otherwise have to produce by hand. -/
noncomputable def canonicalContraction : Contraction d d.contractedSpec where
  vtx := fun v' => (d.classIndex.symm v').val
  vtx_rep := fun v' => (d.classIndex.symm v').property
  vtx_inj := by
    intro a b h
    exact d.classIndex.symm.injective (Subtype.ext h)
  vtx_surj := by
    intro v
    exact ⟨d.classIndex ⟨d.rep v, d.rep_idem v⟩, by
      rw [Equiv.symm_apply_apply]⟩
  slot := fun e' => (d.slotIndex.symm e').val
  slot_inj := by
    intro a b h
    exact d.slotIndex.symm.injective (Subtype.ext h)
  slot_surj := by
    intro e he
    exact ⟨d.slotIndex ⟨e, he⟩, by rw [Equiv.symm_apply_apply]⟩
  length_eq := fun _ => rfl
  tail_eq := by
    intro e'
    show (d.classIndex.symm (d.classIndex ⟨_, _⟩)).val = _
    rw [Equiv.symm_apply_apply]
  head_eq := by
    intro e'
    show (d.classIndex.symm (d.classIndex ⟨_, _⟩)).val = _
    rw [Equiv.symm_apply_apply]

/-! ## Separator and connectivity through a contraction -/

namespace Contraction

variable {n' p' : ℕ} {d : DegSpec n p} {target : SubdivisionGraph.Spec n' p'}

/-- The relabeled core vertices of the contracted target are exactly the
contracted core classes.  Injectivity of `coreVertex` is never used: the
statement is an equality of images. -/
theorem degenerateCoreVertices_eq_image (c : Contraction d target) :
    (ExplicitPotential.Certificate.coreVertices target).image c.vertexEquiv
      = ExplicitPotential.Certificate.degenerateCoreVertices d := by
  classical
  ext y
  simp only [ExplicitPotential.Certificate.coreVertices,
    ExplicitPotential.Certificate.degenerateCoreVertices]
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    obtain ⟨v', _, hv'⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨c.vtx v', Finset.mem_univ _, ?_⟩
    rw [← hxy, ← hv', c.vertexEquiv_coreVertex]
  · intro hy
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hy
    obtain ⟨v', hv'⟩ := c.vtx_surj v
    refine Finset.mem_image.mpr ⟨target.coreVertex v',
      Finset.mem_image.mpr ⟨v', Finset.mem_univ _, rfl⟩, ?_⟩
    rw [c.vertexEquiv_coreVertex, hv', ← hv]
    exact (d.coreVertex_eq_iff (d.rep v) v).mpr (d.rep_idem v)

/-- **The separator, on the closed orthant.**  Pulled back from the contracted
positive target, where `SubdivisionSeparator` applies unchanged. -/
theorem strongSeparatorCertificate (c : Contraction d target) :
    StrongSeparator.StrongSeparatorCertificate d.graph
      (ExplicitPotential.Certificate.degenerateCoreVertices d) :=
  StrongSeparator.strongSeparatorCertificate_of_image c.laplacianEquiv
    c.degenerateCoreVertices_eq_image
    (SubdivisionGraph.Spec.coreVertices_strongSeparatorCertificate target)

/-- Cut connectedness passes from the uncontracted core to the contracted one.
A cut of the target pulls back to a `rep`-saturated cut of the core; a core
slot crossing it cannot be collapsed, so it is the image of a target slot. -/
theorem target_core_connected (c : Contraction d target)
    (hCore : d.core.Connected) :
    target.core.Connected := by
  classical
  intro S' hSplit
  set S : Finset (Fin n) :=
    Finset.univ.filter (fun v => ∃ v' ∈ S', c.vtx v' = d.rep v) with hS
  have hmem : ∀ v : Fin n, v ∈ S ↔ ∃ v' ∈ S', c.vtx v' = d.rep v := by
    intro v
    simp [hS]
  have hRepMem : ∀ v : Fin n, d.rep v ∈ S ↔ v ∈ S := by
    intro v
    rw [hmem, hmem, d.rep_idem]
  have hmemVtx : ∀ v' : Fin n', c.vtx v' ∈ S ↔ v' ∈ S' := by
    intro v'
    rw [hmem]
    constructor
    · rintro ⟨w', hw', hEq⟩
      have hvtx : c.vtx w' = c.vtx v' := by rw [hEq, c.vtx_rep v']
      rw [← c.vtx_inj hvtx]
      exact hw'
    · intro h
      exact ⟨v', h, (c.vtx_rep v').symm⟩
  obtain ⟨v', w', hv', hw'⟩ := hSplit
  have hSplitS : ∃ v w : Fin n, v ∈ S ∧ w ∉ S :=
    ⟨c.vtx v', c.vtx w', (hmemVtx v').mpr hv',
      fun h => hw' ((hmemVtx w').mp h)⟩
  obtain ⟨e, he⟩ := hCore S hSplitS
  have hne : d.rep (d.core.tail e) ≠ d.rep (d.core.head e) := by
    intro hEq
    have hiff : d.core.tail e ∈ S ↔ d.core.head e ∈ S := by
      rw [← hRepMem (d.core.tail e), ← hRepMem (d.core.head e), hEq]
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 (hiff.mp h1)
    · exact h2 (hiff.mpr h1)
  have hpos : 0 < d.length e := by
    rcases Nat.eq_zero_or_pos (d.length e) with hz | hz
    · exact absurd (d.rep_zero e hz) hne
    · exact hz
  obtain ⟨e', he'⟩ := c.slot_surj e hpos
  refine ⟨e', ?_⟩
  have hT : target.core.tail e' ∈ S' ↔ d.core.tail e ∈ S := by
    rw [← hmemVtx, c.tail_eq e', he', hRepMem]
  have hH : target.core.head e' ∈ S' ↔ d.core.head e ∈ S := by
    rw [← hmemVtx, c.head_eq e', he', hRepMem]
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨hT.mpr h1, fun hx => h2 (hH.mp hx)⟩
  · exact Or.inr ⟨hH.mpr h1, fun hx => h2 (hT.mp hx)⟩

/-- **Connectivity, on the closed orthant.**  The finite trust boundary is the
same `Core.Connected` cut certificate the open orthant uses, on the
uncontracted core. -/
theorem graph_connected (c : Contraction d target)
    (hCore : d.core.Connected) : graph_connected d.graph :=
  c.laplacianEquiv.graphConnected
    (target.graph_connected_of_coreConnected (c.target_core_connected hCore))

end Contraction

/-! ## Uniform statements, with no contraction datum supplied -/

/-- **The strong separator for any degenerate spec.**  No hypothesis at all:
exactly as on the open orthant, where
`coreVertices_strongSeparatorCertificate` is also hypothesis-free. -/
theorem strongSeparatorCertificate :
    StrongSeparator.StrongSeparatorCertificate d.graph
      (ExplicitPotential.Certificate.degenerateCoreVertices d) :=
  d.canonicalContraction.strongSeparatorCertificate

/-- **Connectivity for any degenerate spec** from the finite core cut
certificate on the uncontracted core. -/
theorem graph_connected_of_coreConnected (hCore : d.core.Connected) :
    graph_connected d.graph :=
  d.canonicalContraction.graph_connected hCore

/-- The contracted core classes determine rank one on a closed subdivision.

This is the closed-orthant counterpart of
`SubdivisionGraph.Spec.rank_ge_one_of_reachesCoreVertices`.  Once a divisor
reaches every named core class, the canonical contraction transports the
ordinary strong-separator theorem from the positive contracted subdivision,
so no separate calculation is needed at subdivision-interior vertices. -/
theorem rank_ge_one_of_reaches_coreVertices
    (hCore : d.core.Connected) (D : CFDiv d.graph)
    (hReaches : ∀ v : Fin n,
      StrongSeparator.Reaches d.graph D (d.coreVertex v)) :
    rank d.graph D ≥ 1 := by
  apply StrongSeparator.rank_ge_one_of_strongSeparatorCertificate
    (d.graph_connected_of_coreConnected hCore)
    (ExplicitPotential.Certificate.degenerateCoreVertices_nonempty d)
    d.strongSeparatorCertificate
  intro vertex hVertex
  obtain ⟨v, _hv, rfl⟩ := Finset.mem_image.mp hVertex
  exact hReaches v

end Utilities.Certificate.DegenerateSpec.DegSpec

/-! ## The convenience wrapper a row calls -/

namespace Utilities.Certificate.ExplicitPotential.Certificate
open Utilities
open Utilities.Certificate
open Utilities.Certificate.DegenerateSpec

open Utilities.Certificate
open Utilities
open Finset ExplicitPotential
variable {n p : ℕ} (d : DegSpec n p)
variable {n' p' : ℕ} {d : DegSpec n p} {target : SubdivisionGraph.Spec n' p'}
open Utilities.Certificate.ExplicitPotential
open Utilities.Certificate.ExplicitPotential.Certificate

variable {m n p : ℕ}

section Face

variable (certificate : Certificate m n p) (point : Fin m → ℤ)
  (core_nonempty : 0 < n) (rep : Fin n → Fin n)
  (rep_idem : ∀ v : Fin n, rep (rep v) = rep v)
  (rep_zero : ∀ edge : Fin p, certificate.segmentNat point edge = 0 →
    rep (certificate.core.tail edge) = rep (certificate.core.head edge))
  (rep_loopless : ∀ edge : Fin p, 0 < certificate.segmentNat point edge →
    rep (certificate.core.tail edge) ≠ rep (certificate.core.head edge))
  (forest : (Finset.univ.image rep).card
    + (Finset.univ.filter
        (fun edge : Fin p => certificate.segmentNat point edge = 0)).card = n)

/-- **The closed-orthant analogue of `bnExists_on_subdivision_of_valid`.**

A checked closed-orthant record, at one integral length point together with the
face datum `rep`, proves rank-one existence on the contracted subdivision with
*no* separately supplied separator hypothesis and *no* contraction target: both
are discharged uniformly, the first through
`DegSpec.strongSeparatorCertificate` and the second through
`DegSpec.canonicalContraction`.

The remaining hypotheses are exactly the two the open orthant also needs
(`ValidClosed` in place of `Valid`, and `FormsHold`), the finite core
connectivity check on the **uncontracted** core, and the one genuinely new
face obligation `RepInvariant` — which is free on the interior
(`repInvariant_evaluatedPotential_of_pos`) and discharged from a chain of
collapsed slots at a face
(`repInvariant_evaluatedPotential_of_zeroReach`). -/
theorem bnExists_on_degenerate_subdivision_of_validClosed
    (degree : ℤ) (hValid : certificate.ValidClosed degree)
    (hCone : FormsHold certificate.cone point)
    (hInv : ∀ anchor : Fin n,
      (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
        rep_loopless forest).RepInvariant
          (certificate.evaluatedPotential anchor point))
    (hCoreConnected : certificate.core.Connected) :
    BNExists
      (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
        rep_loopless forest).graph 1 degree := by
  apply certificate.bnExists_of_validClosed_of_strongSeparator point
    core_nonempty rep rep_idem rep_zero rep_loopless forest degree hValid hCone
    hInv
  · exact Utilities.Certificate.DegenerateSpec.DegSpec.graph_connected_of_coreConnected _ hCoreConnected
  · exact Utilities.Certificate.DegenerateSpec.DegSpec.strongSeparatorCertificate _

/-- The census-facing form: the `RepInvariant` obligation is replaced by the
collapsed-slot reachability witness a contraction census already produces.
Every hypothesis is then either a Boolean check on the certificate
(`checkClosed`, `connectedCheck`), a cone membership, or census output. -/
theorem bnExists_on_degenerate_subdivision_of_validClosed_of_zeroReach
    (degree : ℤ) (hValid : certificate.ValidClosed degree)
    (hCone : FormsHold certificate.cone point)
    (hReach : ∀ v : Fin n, certificate.ZeroReach point v (rep v))
    (hCoreConnected : certificate.core.Connected) :
    BNExists
      (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
        rep_loopless forest).graph 1 degree :=
  certificate.bnExists_on_degenerate_subdivision_of_validClosed point
    core_nonempty rep rep_idem rep_zero rep_loopless forest degree hValid hCone
    (fun anchor =>
      certificate.repInvariant_evaluatedPotential_of_zeroReach point
        core_nonempty rep rep_idem rep_zero rep_loopless forest hValid hCone
        anchor hReach)
    hCoreConnected

/-- On the interior of the length orthant the face datum is trivial and the
statement is the existing one: this is the compatibility check that the closed
layer does not weaken anything. -/
theorem bnExists_on_degenerate_subdivision_of_validClosed_of_pos
    (degree : ℤ) (hValid : certificate.ValidClosed degree)
    (hCone : FormsHold certificate.cone point)
    (hpos : ∀ edge : Fin p, 0 < certificate.segmentNat point edge)
    (hCoreConnected : certificate.core.Connected) :
    BNExists
      (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
        rep_loopless forest).graph 1 degree :=
  certificate.bnExists_on_degenerate_subdivision_of_validClosed point
    core_nonempty rep rep_idem rep_zero rep_loopless forest degree hValid hCone
    (fun anchor =>
      certificate.repInvariant_evaluatedPotential_of_pos point core_nonempty rep
        rep_idem rep_zero rep_loopless forest hpos anchor)
    hCoreConnected

end Face

/-! ## The closed wrapper subsumes the open one

Nothing above weakens the existing statement: on the open orthant the closed
wrapper *proves* `bnExists_on_subdivision_of_valid`'s conclusion, about the
very same `subdivisionSpec`.  The only difference in the hypotheses is that
connectivity is asked for as the finite core cut certificate rather than as
`graph_connected` of the built graph — which is how the open orthant obtains
it anyway, through `graph_connected_of_coreConnected`. -/

/-- At a strictly positive point the degenerate spec's `toSpec` *is*
`subdivisionSpec`: the two structures have the same core and the same lengths,
and their remaining fields are proofs. -/
theorem toSpec_degenerateSpec_eq_subdivisionSpec
    (certificate : Certificate m n p) (point : Fin m → ℤ)
    (core_nonempty : 0 < n) (rep : Fin n → Fin n)
    (rep_idem rep_zero rep_loopless forest)
    {degree : ℤ} (hValid : certificate.Valid degree)
    (hCone : FormsHold certificate.cone point)
    (hpos : ∀ edge : Fin p,
      0 < (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
        rep_loopless forest).length edge) :
    (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
        rep_loopless forest).toSpec hpos
      = certificate.subdivisionSpec point core_nonempty hValid hCone := rfl

/-- **The open-orthant conclusion, re-derived through the closed layer.**

`rep = id` is a legal face datum at a strictly positive point (`forest` holds
because there are no vanishing slots), the `RepInvariant` obligation is free,
and `DegSpec.bnExists_toSpec_iff` carries the conclusion back to the ordinary
`subdivisionSpec`.  So the closed-orthant route is a strict extension of the
open one, not an alternative to it. -/
theorem bnExists_on_subdivision_of_valid_via_closed
    (certificate : Certificate m n p) (point : Fin m → ℤ)
    (core_nonempty : 0 < n) (degree : ℤ)
    (hValid : certificate.Valid degree)
    (hCone : FormsHold certificate.cone point)
    (hCoreConnected : certificate.core.Connected) :
    BNExists
      (certificate.subdivisionSpec point core_nonempty hValid hCone).graph
      1 degree := by
  classical
  have hpos : ∀ edge : Fin p, 0 < certificate.segmentNat point edge :=
    certificate.segmentNat_positive hValid point hCone
  have hrepZero : ∀ edge : Fin p, certificate.segmentNat point edge = 0 →
      id (certificate.core.tail edge) = id (certificate.core.head edge) := by
    intro edge hzero
    exact absurd hzero (by have := hpos edge; omega)
  have hrepLoopless : ∀ edge : Fin p, 0 < certificate.segmentNat point edge →
      id (certificate.core.tail edge) ≠ id (certificate.core.head edge) :=
    fun edge _ => hValid.1 edge
  have hforest : (Finset.univ.image (id : Fin n → Fin n)).card
      + (Finset.univ.filter
          (fun edge : Fin p => certificate.segmentNat point edge = 0)).card = n := by
    have hImage : (Finset.univ.image (id : Fin n → Fin n)) = Finset.univ := by
      simp
    have hFilter : (Finset.univ.filter
        (fun edge : Fin p => certificate.segmentNat point edge = 0)) = ∅ := by
      apply Finset.filter_false_of_mem
      intro edge _
      have := hpos edge
      omega
    rw [hImage, hFilter]
    simp
  have hDegenerate :=
    certificate.bnExists_on_degenerate_subdivision_of_validClosed_of_pos point
      core_nonempty id (fun _ => rfl) hrepZero hrepLoopless hforest degree
      (certificate.valid_toValidClosed hValid) hCone hpos hCoreConnected
  have hTransported :=
    ((certificate.degenerateSpec point core_nonempty id (fun _ => rfl) hrepZero
      hrepLoopless hforest).bnExists_toSpec_iff hpos 1 degree).mpr hDegenerate
  rwa [certificate.toSpec_degenerateSpec_eq_subdivisionSpec point core_nonempty
    id (fun _ => rfl) hrepZero hrepLoopless hforest hValid hCone hpos]
    at hTransported

end Utilities.Certificate.ExplicitPotential.Certificate

namespace Utilities.Certificate
open Utilities.Certificate
open Utilities
open Finset ExplicitPotential

end Utilities.Certificate
