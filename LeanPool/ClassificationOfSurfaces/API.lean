/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.CellComplexQuotient
import LeanPool.ClassificationOfSurfaces.CanonicalCoordinates
import LeanPool.ClassificationOfSurfaces.CanonicalGeneratorMaps
import LeanPool.ClassificationOfSurfaces.CanonicalPairings
import LeanPool.ClassificationOfSurfaces.CanonicalWords
import LeanPool.ClassificationOfSurfaces.EvalStatement
import LeanPool.ClassificationOfSurfaces.Examples
import LeanPool.ClassificationOfSurfaces.FiniteCyclicCanonical
import LeanPool.ClassificationOfSurfaces.FiniteCyclicCanonicalRealization
import LeanPool.ClassificationOfSurfaces.FiniteCyclicCancellation
import LeanPool.ClassificationOfSurfaces.FiniteCyclicCrosscap
import LeanPool.ClassificationOfSurfaces.FiniteCyclicDerivedRewrites
import LeanPool.ClassificationOfSurfaces.FiniteCyclicDyck
import LeanPool.ClassificationOfSurfaces.FiniteCyclicFaceMerge
import LeanPool.ClassificationOfSurfaces.FiniteCyclicMoveRealization
import LeanPool.ClassificationOfSurfaces.FiniteCyclicMoves
import LeanPool.ClassificationOfSurfaces.FiniteCyclicNormalization
import LeanPool.ClassificationOfSurfaces.FiniteCyclicNormalizationResult
import LeanPool.ClassificationOfSurfaces.FiniteCyclicP1
import LeanPool.ClassificationOfSurfaces.FiniteCyclicP1Realization
import LeanPool.ClassificationOfSurfaces.FiniteCyclicP2
import LeanPool.ClassificationOfSurfaces.FiniteCyclicP2DegenerateRealization
import LeanPool.ClassificationOfSurfaces.FiniteCyclicP2Realization
import LeanPool.ClassificationOfSurfaces.FiniteCyclicPresentation
import LeanPool.ClassificationOfSurfaces.FiniteCyclicRealization
import LeanPool.ClassificationOfSurfaces.FiniteCyclicReduction
import LeanPool.ClassificationOfSurfaces.FiniteCyclicSignedRealization
import LeanPool.ClassificationOfSurfaces.FiniteCyclicSphereRealization
import LeanPool.ClassificationOfSurfaces.FiniteCyclicTerminalNormalization
import LeanPool.ClassificationOfSurfaces.FiniteCyclicTriangulation
import LeanPool.ClassificationOfSurfaces.FiniteCyclicUnorientedRealization
import LeanPool.ClassificationOfSurfaces.FiniteCyclicWordReduction
import LeanPool.ClassificationOfSurfaces.GeometricTriangulationRealization
import LeanPool.ClassificationOfSurfaces.LeanEval.RepresentativeSanity
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicGraphApproximation
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicGraphPL
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicFaceBoundary
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicFaceExtension
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicFaceFilling
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicFaceModel
import LeanPool.ClassificationOfSurfaces.Moise.IntrinsicFineSubdivision
import LeanPool.ClassificationOfSurfaces.Moise.FrontierGlue
import LeanPool.ClassificationOfSurfaces.Moise.PlaneCycle
import LeanPool.ClassificationOfSurfaces.PolygonalQuotient
import LeanPool.ClassificationOfSurfaces.PolygonCellRadial
import LeanPool.ClassificationOfSurfaces.RepresentativeCarrier
import LeanPool.ClassificationOfSurfaces.SignedPresentation
import LeanPool.ClassificationOfSurfaces.SphereCarrierGeometry
import LeanPool.ClassificationOfSurfaces.SphereHemisphere
import LeanPool.ClassificationOfSurfaces.SphereQuotientHomeomorph
import LeanPool.ClassificationOfSurfaces.StrongVertexStar
import LeanPool.ClassificationOfSurfaces.TriangleCell

/-!
# Public API map

This file is the preferred first Lean file to read. It re-exports the completed proof and
documents its main interfaces.

## Eval input

* `EvalSurface`
* `ChartBoundaryInvariant`
* `chartBoundaryInvariant_of_invarianceOfDomain`
* `evalSurface`
* `eval_surface_hypotheses`
* the typeclass hypothesis block used by `classification_of_surfaces`

## Moise--Radó triangulation route

* `GeometricTriangulation` and `GeometricRealization` (`Moise/GeometricTriangulation.lean`)
* `TriangleFamily.FaceAdjacentAtVertex`, `TriangleFamily.IsStrongVertexStarConnected`, and
  the strong-to-legacy and strong-to-dual connectivity bridges
  (`Moise/GeometricTriangulation.lean`)
* `PlaneComplex`, `IsPLOn`, `IsPLOnSet` (`Moise/PlaneComplex.lean`)
* `IntrinsicTwoComplex`, its faithful `Subdivision`, `IsPLMap`, and `PLHomeomorph`
  (`Moise/IntrinsicComplex.lean`)
* intrinsic one-skeleton polygonal replacement, exact finite edge complexes, and embedding
  (`Moise/IntrinsicGraphApproximation.lean`, `Moise/IntrinsicGraphPL.lean`)
* standard plane models, exact polygonal face-boundary cycles, certified relative PL fillings,
  and faithful arbitrarily fine midpoint subdivisions (`Moise/IntrinsicFaceModel.lean`,
  `Moise/IntrinsicFaceBoundary.lean`, `Moise/IntrinsicFaceExtension.lean`,
  `Moise/IntrinsicFaceFilling.lean`, `Moise/IntrinsicCellwiseExtension.lean`,
  `Moise/IntrinsicFineSubdivision.lean`)
* strongly positive frontier controls and continuous vanishing-error gluing
  (`Moise/FrontierGlue.lean`)
* `PolygonalCircle`, `polygonal_jordan`, the crossing `index` (`Moise/PolygonalJordan.lean`)
* `closedRegion_is_polyhedron`, `polygonal_schoenflies_rel` (`Moise/PolygonalSchoenflies.lean`)
* `pl_approximation_two_manifold` (`Moise/PLApproximation.lean`)
* `JoinedByBrokenLine` (`Moise/BrokenLine.lean`)
* `MoiseChart`, `MoiseChart.BoundaryFaithful`, `exists_moiseChart_core_mem_nhds`
  (`Moise/ChartExtraction.lean`)
* `PartialTriangulation`, `RadoInvariant`, `moise_finite_chart_cover`,
  `moise_induction_step`, `moise_triangulation_of_boundaries`
  (`Moise/ChartInduction.lean`)
* `nonempty_geometricTriangulation_iff_explicit`, `moise_triangulation`, and
  `moise_triangulation_explicit` (`Moise/GeometricTriangulation.lean`, `Triangulation.lean`)
* anchors and countermodels: `Moise/Anchors.lean`, `Moise/Countermodels.lean`

The triangulation route uses the faithful geometric and intrinsic-complex APIs above. Superseded
experimental APIs are not part of the public surface; git history remains available for historical
implementations.

## Shared triangulation and cell-complex boundary

* `OrientedEdge`
* `FiniteSurfaceTriangulation` (ledgered; fed by the `GeometricTriangulation` bridge)
* `compact_eval_surface_finitely_triangulable`
* `FiniteSurfaceTriangulation.toCellComplex`
* `FiniteSurfaceTriangulation.toFiniteCyclicPresentation`
* `FiniteSurfaceTriangulation.toFiniteCyclicPresentation_isSurfaceValid`
* `FiniteSurfaceTriangulation.toFiniteCyclicPresentation_isConnected`
* `compactEvalSurfaceFiniteCyclicPresentation`
* `compact_eval_surface_has_valid_connected_finiteCyclicPresentation`
* `GeometricTriangulation.polygonalRealizationHomeomorph`
* `GeometricTriangulation.polygonalRealization_homeomorphic_of_surface`
* `compact_eval_surface_polygonalRealization_certificates`
* `compact_eval_surface_polygonalRealization_homeomorphic_surface`

The cell-complex adapter preserves the certified triangle-boundary incidence. The faithful
finite-cyclic handoff enumerates that incidence directly and identifies its polygonal quotient
with the geometric triangulation.

## Shared finite surface cell complexes

* `SurfaceCellComplex`
* `SurfaceCellComplex.BoundaryOccurrence`
* `SurfaceCellComplex.IsBoundaryDart`
* `SurfaceCellComplex.IsSurfaceValid`
* `SurfaceCellComplex.FaceAdjacent`
* `SurfaceCellComplex.IsConnected`
* `SurfaceCellComplex.SignedDart`
* `SurfaceCellComplex.oneFacePresentation`
* `SurfaceCellComplex.EdgeOrbit`
* `SurfaceCellComplex.edgeOrbit`
* `SurfaceCellComplex.signedDartEquiv`
* `SurfaceCellComplex.finSignedDartEquiv`
* `SurfaceCellComplex.normalizedBoundary`

`SurfaceCellComplex` contains only finite incidence data. Its topology is the faithful
occurrence-indexed `PolygonalRealization` described below.

## Finite cyclic presentation layer

* `FiniteCyclicPresentation`
* `FiniteCyclicPresentation.inverseWord`
* `FiniteCyclicPresentation.OrientedFace`
* `FiniteCyclicPresentation.orientedBoundary`
* `FiniteCyclicPresentation.edgeMultiplicity`
* `FiniteCyclicPresentation.IsSurfaceValid`
* `FiniteCyclicPresentation.FaceAdjacent`
* `FiniteCyclicPresentation.IsConnected`
* `FiniteCyclicPresentation.emptyWordSphere`
* `FiniteCyclicPresentation.twoMonogonSphere`
* `FiniteCyclicPresentation.IsEmptyWordSphere`
* `FiniteCyclicPresentation.IsGallierValid`
* `FiniteCyclicPresentation.EdgeRelabeling`
* `FiniteCyclicPresentation.EdgeRelabeling.dartEquiv`
* `FiniteCyclicPresentation.PresentationIso`
* `FiniteCyclicPresentation.PresentationIso.isSurfaceValid_iff`
* `FiniteCyclicPresentation.PresentationIso.isConnected_iff`
* `FiniteCyclicPresentation.BoundaryOccurrence`
* `FiniteCyclicPresentation.BoundaryPairing`
* `FiniteCyclicPresentation.PolygonalRealization`
* `FiniteCyclicPresentation.RealizationEquivData`
* `FiniteCyclicPresentation.PolygonallyEquivalent`
* `FiniteCyclicPresentation.ofOneFaceWord`
* `FiniteCyclicPresentation.ofOneFaceWord_isSurfaceValid`
* `FiniteCyclicPresentation.ofOneFaceWord_isConnected`
* `FiniteCyclicPresentation.SubdivisionStep`
* `FiniteCyclicPresentation.Subdivides`
* `FiniteCyclicPresentation.HasCommonSubdivision`
* `FiniteCyclicPresentation.MoveEquivalent`
* `FiniteCyclicPresentation.HasCommonSubdivision.polygonallyEquivalent`
* `FiniteCyclicPresentation.SignedPresentationIso.preHomeomorph`
* `FiniteCyclicPresentation.SignedPresentationIso.realizationHomeomorph`
* `FiniteCyclicPresentation.SignedPresentationIso.polygonallyEquivalent`
* `PolygonCell.radialHomeomorph`
* `PolygonCell.radialHomeomorph_ofCircle`
* `GeometricTriangulation.toFiniteCyclicPresentation`
* `GeometricTriangulation.toFiniteCyclicPresentation_valid_and_connected`
* `FiniteCyclicPresentation.SignedPresentationIso`
* `FiniteCyclicPresentation.SignedPresentationIso.ofPresentationIso`
* `FiniteCyclicPresentation.SignedPresentationIso.orientedFaceEquiv`
* `FiniteCyclicPresentation.SignedPresentationIso.orientedBoundary_rotated`
* `FiniteCyclicPresentation.SignedPresentationIso.isSurfaceValid_iff`
* `FiniteCyclicPresentation.SignedPresentationIso.isConnected_iff`
* `FiniteCyclicPresentation.SignedPresentationIso.isGallierValid_iff`
* `FiniteCyclicPresentation.P1.expandDart`
* `FiniteCyclicPresentation.P1.expandWord`
* `FiniteCyclicPresentation.P1.contractWord`
* `FiniteCyclicPresentation.P1.expandDart_flip`
* `FiniteCyclicPresentation.P1.expandWord_inverseWord`
* `FiniteCyclicPresentation.P1.expandWord_isRotated_iff`
* `FiniteCyclicPresentation.P1.expand`
* `FiniteCyclicPresentation.P1.expand_isSurfaceValid`
* `FiniteCyclicPresentation.P1.expand_isConnected`
* `FiniteCyclicPresentation.P1.expand_isGallierValid`
* `FiniteCyclicPresentation.P1Subdivision`
* `FiniteCyclicPresentation.P1Subdivision.isGallierValid`
* `FiniteCyclicPresentation.P1Subdivision.preservesPolygonalRealization`
* `FiniteCyclicPresentation.P2Cut`
* `FiniteCyclicPresentation.P2Cut.canonical`
* `FiniteCyclicPresentation.P2Cut.IsNondegenerate`
* `FiniteCyclicPresentation.P2Cut.swap`
* `FiniteCyclicPresentation.P2Cut.flip`
* `FiniteCyclicPresentation.P2.split`
* `FiniteCyclicPresentation.P2.split_orientedBoundary_selected`
* `FiniteCyclicPresentation.P2.split_orientedBoundary_right`
* `FiniteCyclicPresentation.P2.edgeMultiplicity_split_castSucc`
* `FiniteCyclicPresentation.P2.edgeMultiplicity_split_freshEdge`
* `FiniteCyclicPresentation.P2.split_isSurfaceValid`
* `FiniteCyclicPresentation.P2.split_isConnected`
* `FiniteCyclicPresentation.P2.split_isGallierValid`
* `FiniteCyclicPresentation.P2.split_emptyWordSphere`
* `FiniteCyclicPresentation.P2Subdivision`
* `FiniteCyclicPresentation.P2Subdivision.isGallierValid`
* `FiniteCyclicPresentation.P2Subdivision.preservesPolygonalRealization`
* `FiniteCyclicPresentation.subdivisionStep_preservesPolygonalRealization`
* `FiniteCyclicPresentation.Subdivides.toPolygonallyEquivalent`
* `FiniteCyclicPresentation.HasCommonSubdivision.toPolygonallyEquivalent`
* `FiniteCyclicPresentation.Dyck.hasCommonSubdivision`
* `FiniteCyclicPresentation.Dyck.polygonallyEquivalent`
* `FiniteCyclicPresentation.UnorientedPresentationIso`
* `FiniteCyclicPresentation.UnorientedPresentationIso.realizationHomeomorph`
* `FiniteCyclicPresentation.Crosscap.polygonallyEquivalent`
* `FiniteCyclicPresentation.ValidPresentation`
* `FiniteCyclicPresentation.NormalizationStep`
* `FiniteCyclicPresentation.NormalizationEquivalent`
* `FiniteCyclicPresentation.NormalizationEquivalent.ofSubdivides`
* `FiniteCyclicPresentation.NormalizationEquivalent.polygonallyEquivalent`
* `FiniteCyclicPresentation.P1.contractionNormalizationEquivalent`
* `FiniteCyclicPresentation.P2.mergeNormalizationEquivalent`
* `FiniteCyclicPresentation.P2.oneSidedMergeNormalizationEquivalent`
* `FiniteCyclicPresentation.P2.oneSidedPolygonallyEquivalent`
* `FiniteCyclicPresentation.Dyck.normalizationEquivalent`
* `FiniteCyclicPresentation.Crosscap.normalizationEquivalent`
* `FiniteCyclicPresentation.Dyck.negativeNormalizationEquivalent`
* `FiniteCyclicPresentation.Crosscap.negativeNormalizationEquivalent`
* `FiniteCyclicPresentation.Crosscap.adjacentNormalizationEquivalent`
* `FiniteCyclicPresentation.Handle.normalizationEquivalent`
* `FiniteCyclicPresentation.HandleToCrosscaps.normalizationEquivalent`
* `FiniteCyclicPresentation.LoopGrouping.normalizationEquivalent`
* `FiniteCyclicPresentation.Cancellation.normalizationEquivalent`
* `FiniteCyclicPresentation.Cancellation.Context.normalizationEquivalent`
* `FiniteCyclicPresentation.FaceMerge.normalizationEquivalent`
* `FiniteCyclicPresentation.FaceMerge.ContextMerge.normalizationEquivalent`
* `FiniteCyclicPresentation.canonicalValidPresentation`
* `FiniteCyclicPresentation.NormalizationResult`
* `FiniteCyclicPresentation.NormalizationResult.polygonallyEquivalent`
* `FiniteCyclicPresentation.NormalizationResult.realizationHomeomorph`
* `FiniteCyclicPresentation.normalizeConnectedToCanonical`
* `FiniteCyclicPresentation.exists_admissible_normalForm_polygonallyEquivalent`
* `FiniteCyclicPresentation.Reduction.exists_distinct_faceAdjacent`
* `FiniteCyclicPresentation.Reduction.exists_oppositelyDisplayedAdjacentFaces`
* `FiniteCyclicPresentation.Reduction.mergeNormalizationEquivalent`
* `FiniteCyclicPresentation.Reduction.mergeTarget_faces_length`

This packed layer retains only finite signed face words. A signed presentation isomorphism may
relabel faces, rotate individual face boundaries, and independently reverse the chosen
orientation of every renamed edge. Reversal bits compose by exclusive-or. Validity, edge
multiplicities, and connectivity are invariant under these operations. Each stored face also has
two non-mutating oriented views: the negative view reverses the word and flips every dart, and
signed presentation isomorphisms transport either view up to cyclic rotation. The original
orientation-preserving `PresentationIso` embeds into this general layer.

The Gallier--Xu normalization recursion is complete at this interface. Every valid connected
finite-cyclic presentation reaches the single existing `NormalForm.canonicalPresentation` for an
Eval-admissible normal form, through a `NormalizationEquivalent` chain and hence a
`PolygonallyEquivalent` proof. The terminal argument orders boundary blocks, converts handles to
crosscaps exactly when a crosscap is present, normalizes edge orientations, and positionally
relabels the result to the existing canonical words.

Gallier--Xu's exceptional one-face, zero-edge, empty-boundary sphere is represented explicitly by
`emptyWordSphere`, without weakening ordinary `IsSurfaceValid`. `IsGallierValid` adds exactly its
signed-isomorphism class as a disjunct. The P2-expanded `twoMonogonSphere`, with boundaries `d`
and `d⁻¹`, satisfies ordinary validity and connectivity.

`P1.expand` implements Gallier--Xu's global edge subdivision exactly: the canonical positive
occurrence becomes `b c`, while its negative occurrence becomes `c⁻¹ b⁻¹`. Contraction is a
left inverse and expansion preserves and reflects cyclic rotation. Face positions are unchanged,
and both subdivided edges inherit the old edge multiplicity. The construction conditionally
preserves ordinary validity, connectivity, and `IsGallierValid`; these hypotheses are not
bundled into the syntactic `P1Subdivision` relation. The positive orientation is canonical, while
the relation's signed target isomorphism supports renamed and reoriented target edges.
The finite cyclic quotient adapter realizes those face words directly as a disjoint union of
standard polygonal disks modulo occurrence-level side pairings.

`P2.split` implements Gallier--Xu's cyclic oriented face-cut formula. Its raw cut pieces may be
empty so the same construction expresses the exceptional empty-word-sphere conversion.
The selected child has displayed boundary `left d`, the appended child has displayed boundary
`d⁻¹ right`, and both are stored in the cut's chosen traversal orientation. Flipping the cut
reverses its selected traversal and swaps its two pieces. The fresh edge has multiplicity two,
old edge multiplicities are preserved, and validity, connectivity, and Gallier validity survive. The
exceptional empty-word sphere presentation splits definitionally to the
`twoMonogonSphere` presentation. `P2Subdivision` is the corresponding syntactic relation for
nondegenerate ordinary face cuts, together with that exceptional sphere conversion, up to signed
presentation isomorphism of the target.

The generic Gallier--Xu Dyck rewrite
`a U V a⁻¹ X ~ b V U b⁻¹ X` is now an explicit common-subdivision theorem. Its two P2 splits
are related by a signed isomorphism exchanging the retained distinguished edge with the fresh
cutting edge. Consequently the rewrite preserves faithful polygonal realizations for ordinary-valid
source and target presentations.

Gallier--Xu's cross-cap rewrite `a X a Y ~ b b Y⁻¹ X` reverses one child face before
the second P2 merge. `UnorientedPresentationIso` records that independent face-traversal choice
explicitly, and realizes it by cyclic disk rotations and reflections. Because the current
`IsSurfaceValid` face-uniqueness clause is intentionally stated for stored orientations, this
broader comparison takes ordinary-validity proofs for both endpoints rather than claiming to
transport validity automatically.

`NormalizationEquivalent` is the stable chain API over validity-bundled presentations. Its
primitive steps are common subdivisions, unoriented comparisons in either direction, and the
proved one-sided-degenerate P2 comparison; every chain produces a faithful
polygonal-realization homeomorphism. Both generic pseudo-rewrites are available as nodes in this
closure. The derived-chain layer also exposes the opposite-orientation Dyck and crosscap rules,
the full three-Dyck handle extraction, the four-rewrite conversion of a handle plus a crosscap
into three crosscaps, and the loop-grouping specialization; all intermediate validity witnesses
are constructed internally. Exact inverse-pair cancellation and two-face merging are available
both as isolated word rules and in multi-face contexts with untouched faces. Their transported
forms isolate arbitrary edge naming, face order, traversal orientation, and cyclic starting
points behind signed presentation isomorphisms.
Validity-safe marked merging now gives a total face-count recursion from every connected valid
presentation to one face. A second well-founded recursion cancels all cyclic adjacent inverse
pairs—including the retained merge markers—and lands either at the exact canonical sphere node
or at a pair-reduced valid one-face word.

## Polygonal quotient foundation

* `PolygonCell`
* `PolygonCell.side`
* `PolygonCell.iUnion_range_side`
* `PolygonGluing.PreRealization`
* `PolygonGluing.Side`
* `PolygonGluing.Identification`
* `PolygonGluing.setoid`
* `PolygonGluing.Realization`
* `PolygonGluing.realizationCongr`
* `FiniteCyclicPresentation.edgeMultiplicity_eq_card_edgeOccurrences`
* `FiniteCyclicPresentation.IsSurfaceValid.exists_unique_partner`
* `FiniteCyclicPresentation.IsSurfaceValid.exists_identification_source`
* `FiniteCyclicPresentation.polygonalMk_pairing_eq`
* `SurfaceCellComplex.BoundaryOccurrence`
* `SurfaceCellComplex.BoundaryPairing`
* `SurfaceCellComplex.OccurrencePairingValid`
* `SurfaceCellComplex.wordEdgeOccurrences`
* `SurfaceCellComplex.oneFacePresentation_isSurfaceValid`
* `SurfaceCellComplex.oneFacePresentation_occurrencePairingValid`
* `SurfaceCellComplex.PolygonalRealization`
* `SurfaceCellComplex.mem_polygonalIdentifications_iff_exists_occurrences`
* `SurfaceCellComplex.oneFaceOccurrence`
* `SurfaceCellComplex.oneFace_mem_polygonalIdentifications_iff`
* `Complex.ClosedUnitDisc.bdyPtOfReal_add_int`
* `SurfaceCellComplex.not_isBoundaryDart_of_occurs_at_ne`
* `SurfaceCellComplex.swapIdentification`
* `SurfaceCellComplex.swapIdentification_mem_polygonalIdentifications`
* `SurfaceCellComplex.oppositeDirectionIdentification_mem_of_get_pos_neg`
* `quotEqvGenHomeomorph`
* `eqvGenQuotientCongrRaw`
* `eqvGen_map_of_generator_to_eqvGen`
* `eqvGen_iff_of_generator_maps`
* `eqvGenQuotientCongrRawOfGeneratorMaps`
* `PolygonCell.closedUnitDiscHomeomorph`
* `PolygonCell.closedUnitDiscHomeomorph_side`
* `PolygonGluing.oneFacePreRealizationHomeomorph`
* `PolygonGluing.oneFacePreRealizationHomeomorph_sidePoint`
* `PolygonCell.conjHomeomorph`
* `PolygonCell.conj_side_symm_monogon`
* `PolygonCell.hemisphereHeight`
* `PolygonCell.upperHemisphere`
* `PolygonCell.lowerHemisphere`
* `PolygonCell.upperHemisphere_side_eq_lowerHemisphere_side_symm`
* `PolygonCell.sphereDiskPoint`
* `SurfaceCellComplex.oneFacePolygonalPreRealizationHomeomorph`
* `SurfaceCellComplex.oneFacePolygonalPreRealizationHomeomorph_sidePoint`
* `SurfaceCellComplex.sphereBoundaryOccurrence_eq`
* `SurfaceCellComplex.mem_sphere_polygonalIdentifications_iff`
* `SurfaceCellComplex.spherePreMap`
* `SurfaceCellComplex.spherePreMap_eq_of_generator`
* `SurfaceCellComplex.spherePreMap_eq_iff_gluingRel`
* `SurfaceCellComplex.sphereQuotientMap`
* `SurfaceCellComplex.spherePolygonalRealizationHomeomorph`

This generic layer supports disk cells with any number of marked sides and generated side
identifications. The additive cell-complex adapter now maps boundary occurrences to polygon sides
and, given incidence validity plus nonempty face boundaries, generates all compatible internal
pairings. Edge-orbit counts and inverse-invariance of boundary status are derived from
`IsSurfaceValid`, not repeated as adapter assumptions. The standard one-face examples have
incidence- and occurrence-validity witnesses, including the corrected length-six annulus word.
The representative-carrier bridge identifies each indexed disk, and hence every one-face
pre-realization, with the exact vendored closed unit disk. It
records the side-coordinate formula, integral-period boundary invariance, and closure-aware
quotient congruence from the polygonal generated setoid to a raw relation quotient. The one-face
membership theorem characterizes compatible ordered pairings by two distinct boundary-word
positions with the required status and dart equalities. Forward canonical block positions and
exhaustive raw-pairing classifications for both canonical families are complete. Exact carrier
coordinates, including
the reversed boundary index, send all five canonical pairing families into the corresponding
trusted equivalence closures. Exhaustive forward maps and constructor-by-constructor reverse maps
therefore identify both generated relations, and the carrier descends to homeomorphisms from the
canonical polygonal realizations to the exact trusted Eval quotients.
For the sphere branch, the compatible upper/lower hemisphere map descends from the two monogons;
its kernel is exactly the generated side-gluing relation, and compact-to-Hausdorff upgrades the
resulting bijection to a homeomorphism with `SphereRepresentative`.

## Gallier-Xu tail

* `NormalForm.OrientableEdge`
* `NormalForm.NonOrientableEdge`
* `NormalForm.orientableBoundaryWord`
* `NormalForm.nonOrientableBoundaryWord`
* `NormalForm.orientableHandlePosition`
* `NormalForm.orientableBoundaryPosition`
* `NormalForm.nonOrientableCrosscapPosition`
* `NormalForm.nonOrientableBoundaryPosition`
* `NormalForm.orientableBoundaryWord_length`
* `NormalForm.nonOrientableBoundaryWord_length`
* `NormalForm.orientableBoundaryWord_edge_occurrences`
* `NormalForm.nonOrientableBoundaryWord_edge_occurrences`
* `NormalForm.canonicalPresentation`
* `NormalForm.canonicalPresentation_isSurfaceValid`
* `NormalForm.canonicalPresentation_isConnected`
* `NormalForm.canonicalPresentation_isGallierValid`
* `FiniteCyclicPresentation.ofOneFaceWordRealizationHomeomorph`
* `NormalForm.canonicalSphereRealizationHomeomorph`
* `NormalForm.canonicalOrientableRealizationHomeomorph`
* `NormalForm.canonicalNonOrientableRealizationHomeomorph`
* `NormalForm.orientableCellComplex_isSurfaceValid`
* `NormalForm.nonOrientableCellComplex_isSurfaceValid`
* `NormalForm.orientableCellComplex_isConnected`
* `NormalForm.nonOrientableCellComplex_isConnected`
* `NormalForm.orientableCellComplex_occurrencePairingValid`
* `NormalForm.nonOrientableCellComplex_occurrencePairingValid`
* `NormalForm.nonOrientableCrosscapIdentification`
* `NormalForm.nonOrientableCrosscapIdentificationReverse`
* `NormalForm.nonOrientableBoundaryIdentification`
* `NormalForm.nonOrientableBoundaryIdentificationReverse`
* `NormalForm.mem_nonOrientable_polygonalIdentifications_iff`
* `NormalForm.orientableHandleAIdentification`
* `NormalForm.orientableHandleAIdentificationReverse`
* `NormalForm.orientableHandleBIdentification`
* `NormalForm.orientableHandleBIdentificationReverse`
* `NormalForm.orientableBoundaryIdentification`
* `NormalForm.orientableBoundaryIdentificationReverse`
* `NormalForm.mem_orientable_polygonalIdentifications_iff`
* `NormalForm.orientableOccurrencePoint`
* `NormalForm.nonOrientableOccurrencePoint`
* `NormalForm.orientableCarrier_occurrencePoint`
* `NormalForm.nonOrientableCarrier_occurrencePoint`
* `NormalForm.orientableBoundary_trustedSource_eq_carrier_c_neg`
* `NormalForm.orientableBoundary_trustedTarget_eq_carrier_c_pos`
* `NormalForm.nonOrientableBoundary_trustedSource_eq_carrier_c_neg`
* `NormalForm.nonOrientableBoundary_trustedTarget_eq_carrier_c_pos`
* `NormalForm.orientableCarrier_handle_a_eqvGen`
* `NormalForm.orientableCarrier_handle_b_eqvGen`
* `NormalForm.orientableCarrier_boundary_c_eqvGen`
* `NormalForm.nonOrientableCarrier_crosscap_a_eqvGen`
* `NormalForm.nonOrientableCarrier_boundary_c_eqvGen`
* `NormalForm.orientableGenerator_to_eqvGen`
* `NormalForm.nonOrientableGenerator_to_eqvGen`
* `NormalForm.orientableRel_to_polygonEqvGen`
* `NormalForm.nonOrientableRel_to_polygonEqvGen`
* `NormalForm.orientablePolygonalRealizationHomeomorph`
* `NormalForm.nonOrientablePolygonalRealizationHomeomorph`
* `NormalForm.orientableCellComplex`
* `NormalForm.nonOrientableCellComplex`
* `NormalForm.canonicalCellComplex`
* `NormalForm.IsEvalAdmissible`
* `FiniteCyclicPresentation.hasEvalRepresentative`

The canonical word families match the exact commutator, crosscap, and boundary-block patterns in
the vendored relations. Their lengths, edge multiplicities, incidence validity, connectivity, and
Eval-admissible occurrence pairings are certified combinatorially. Forward
block-position maps and exact `List.get` lemmas locate every signed entry of each named handle,
crosscap, and boundary block. Polygonal identifications in both families are classified
exhaustively as the two directed forms of the expected handle, crosscap, or boundary-seam
pairings, with singleton free-boundary darts excluded. Exact coordinate theorems transport every
explicit pairing family into the trusted closures; boundary blocks use `Fin.rev` and integral
periodicity to reconcile the benchmark's negative angles. The exhaustive classifications package
those facts for arbitrary polygon generators, while the trusted relation constructors map back to
named polygon pairings.
The resulting bidirectional closure comparisons descend to homeomorphisms with `Quot
(OrientableRel p n)` and `Quot (NonOrientableRel p n)`.

The public classification theorem uses the faithful replacement route: it normalizes finite cyclic
presentations, proves their polygonal realizations match the vendored quotient relations, and
transports that result across the geometric-triangulation realization bridge. The combinatorial
normalization layer does not mention manifold chart machinery.

## Eval representatives and final theorem

* `Complex.ClosedUnitDisc`, `OrientableRel`, and `NonOrientableRel`
  (`LeanEval/ChallengeDeps.lean`, vendored verbatim from Lean-Eval)
* `Complex.ClosedUnitDisc.norm_bdyPtOfReal`
* `orientableQuotRadius` and `nonOrientableQuotRadius`
* `not_subsingleton_orientableQuot` and `not_subsingleton_nonOrientableQuot`
  (`LeanEval/RepresentativeSanity.lean`, project-owned consequences)
* `SphereRepresentative` and `NormalForm` (project-owned abbreviations and indices)
* `classification_of_surfaces`
* `topological_classification_of_surfaces`

The final theorem is a short assembly proof from a geometric triangulation, through a
finite cyclic presentation and Gallier-Xu normalization, to separately certified polygonal
realization homeomorphisms for the vendored quotients. The C0 `ChartBoundaryInvariant` interface
is discharged unconditionally by planar no-retraction, Brouwer's fixed-point theorem, and
invariance of domain. `LeanEval/SpecAudit.lean` checks that the current public theorem's conclusion
is the exact published Lean-Eval type over the vendored disc relations.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

end ClassificationOfSurfaces
end Topology
end LeanEval
