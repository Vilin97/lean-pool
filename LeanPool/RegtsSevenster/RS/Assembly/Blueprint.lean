/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps
public import LeanPool.RegtsSevenster.RS.Common.YoungDiagrams
public import LeanPool.RegtsSevenster.RS.Classical.SymFun.PowerSums
public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.ColourCycleSum
public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.JTOrtho
public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.SignResolve
public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.NativeFaithful
public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.SquareGrowth
public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.BranchTrace
public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.JTPad
public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.PackageAssembly
public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.Package
public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.PairingPos
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.TraceZeta
public import LeanPool.RegtsSevenster.RS.Classical.SymFun.ZetaExp
public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.SquareGrowthSharp
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.HookConfinementSharp
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.SkeinDimBound
public import LeanPool.RegtsSevenster.RS.Novel.Skein.PathMatch
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.SuperKill
public import LeanPool.RegtsSevenster.RS.StatementConverse
public import LeanPool.RegtsSevenster.RS.TheoremQuant
public import LeanPool.RegtsSevenster.RS.Classical.SymFun.LGVStrict
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ClosedAgreement
public import LeanPool.RegtsSevenster.RS.Novel.Skein.TransitionMove
public import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueRelTransport
public import LeanPool.RegtsSevenster.RS.Novel.Skein.DisjSubsetSplit
public import LeanPool.RegtsSevenster.RS.Novel.Skein.InterfaceOrderIso
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ThroughValue
public import LeanPool.RegtsSevenster.RS.Novel.Skein.RelabelInvariance
public import LeanPool.RegtsSevenster.RS.Novel.Skein.DisjUnionFactor
public import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueCircuitDelta
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ChainAgreement
public import LeanPool.RegtsSevenster.RS.Novel.Skein.CanonExistence
public import LeanPool.RegtsSevenster.RS.Novel.Skein.RepairInvariance
public import LeanPool.RegtsSevenster.RS.Novel.Skein.PathLedger
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ChordParity
public import LeanPool.RegtsSevenster.RS.Novel.Skein.PairingConnectivity
public import LeanPool.RegtsSevenster.RS.Novel.Skein.StepLedger
public import LeanPool.RegtsSevenster.RS.Novel.Skein.InvolutionCard
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ChordCount
public import LeanPool.RegtsSevenster.RS.Novel.Skein.AllInternalIndependence
public import LeanPool.RegtsSevenster.RS.Novel.Skein.AllInternalAgreement
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ConverseAssembly
public import LeanPool.RegtsSevenster.RS.Novel.Skein.InterfaceAlternate
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ConverseDischarge
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ConverseGram
public import LeanPool.RegtsSevenster.RS.Novel.Skein.TransposeLedger
public import LeanPool.RegtsSevenster.RS.Novel.Skein.TwoPathNonSep
public import LeanPool.RegtsSevenster.RS.Novel.Skein.CanonicalFrame
public import LeanPool.RegtsSevenster.RS.Novel.Skein.StepFrame
public import LeanPool.RegtsSevenster.RS.Novel.Skein.StateFlipSet
public import LeanPool.RegtsSevenster.RS.Novel.Skein.StatusSet
public import LeanPool.RegtsSevenster.RS.Novel.Skein.CrossingDelta
public import LeanPool.RegtsSevenster.RS.Novel.Skein.FlipSignProduct
public import LeanPool.RegtsSevenster.RS.Novel.Skein.FlipSignForm
public import LeanPool.RegtsSevenster.RS.Novel.Skein.LedgerSets
public import LeanPool.RegtsSevenster.RS.Novel.Skein.StepStatus
public import LeanPool.RegtsSevenster.RS.Novel.Skein.StepStatusNonsep
public import LeanPool.RegtsSevenster.RS.Novel.Skein.PairedAssembly
public import LeanPool.RegtsSevenster.RS.Novel.Skein.PropThreeOpen
public import LeanPool.RegtsSevenster.RS.Novel.Skein.FourLabelParity
public import LeanPool.RegtsSevenster.RS.Novel.Skein.PairingSwap
public import LeanPool.RegtsSevenster.RS.Novel.Skein.PairingSignature
public import LeanPool.RegtsSevenster.RS.Novel.Skein.PairingValue
public import LeanPool.RegtsSevenster.RS.Novel.Skein.LedgerValue
public import LeanPool.RegtsSevenster.RS.Novel.Skein.LoopVerify
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ThroughIndCFalse
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ChordLabels
public import LeanPool.RegtsSevenster.RS.Novel.Skein.LabelChords
public import LeanPool.RegtsSevenster.RS.Novel.Skein.FibreValue
public import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueChords
public import LeanPool.RegtsSevenster.RS.Novel.Skein.GluePathMatch
public import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueCrossDelta
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ClosedCutDispatch
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ThroughEdgeCut
public import LeanPool.RegtsSevenster.RS.Novel.Skein.RelabelChords
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ChordSwapParity
public import LeanPool.RegtsSevenster.RS.Classical.SymFun.SuperPowerSums
public import LeanPool.RegtsSevenster.RS.Classical.SymFun.RecurrenceFromVanishing
public import LeanPool.RegtsSevenster.RS.Classical.SymFun.RationalityFromRecurrence
public import LeanPool.RegtsSevenster.RS.Classical.SymFun.HookVanishing
public import LeanPool.RegtsSevenster.RS.Classical.Interfaces.SchurPackage
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.BlockBounds
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.HookConfinement
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.KaroubiMonoidal
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.MatMonoidal
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.MatBraided
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.NilpotentTrace
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.SemisimpleEnd
public import LeanPool.RegtsSevenster.RS.Classical.Super.OrthonormalBasis
public import LeanPool.RegtsSevenster.RS.Classical.Super.SuperVect
public import LeanPool.RegtsSevenster.RS.Classical.Super.SymplecticBasis
public import LeanPool.RegtsSevenster.RS.Novel.Skein.FlagGraph
public import LeanPool.RegtsSevenster.RS.Novel.Skein.Composition
public import LeanPool.RegtsSevenster.RS.Novel.Skein.FragmentEquiv
public import LeanPool.RegtsSevenster.RS.Novel.Skein.CompositionEquiv
public import LeanPool.RegtsSevenster.RS.Novel.Skein.StrandBundle
public import LeanPool.RegtsSevenster.RS.Novel.Skein.IdentityLaw
public import LeanPool.RegtsSevenster.RS.Novel.Skein.IdentityLawRight
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ConnectionRank
public import LeanPool.RegtsSevenster.RS.Novel.Skein.HomSpaces
public import LeanPool.RegtsSevenster.RS.Novel.Skein.Multiplicativity
public import LeanPool.RegtsSevenster.RS.Novel.Skein.Eulerian
public import LeanPool.RegtsSevenster.RS.Novel.Skein.TransitionExists
public import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueAmbient
public import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueComm
public import LeanPool.RegtsSevenster.RS.Novel.Skein.CloseRotate
public import LeanPool.RegtsSevenster.RS.Novel.Skein.CloseRotateLeft
public import LeanPool.RegtsSevenster.RS.Novel.Skein.InterfaceShift
public import LeanPool.RegtsSevenster.RS.Novel.Skein.PairCloseComm
public import LeanPool.RegtsSevenster.RS.Novel.Skein.SimpleUnit
public import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinIdeal
public import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinIdealLeft
public import LeanPool.RegtsSevenster.RS.Novel.Skein.HomCompose
public import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinCategory
public import LeanPool.RegtsSevenster.RS.Novel.Skein.HomTraceNondegenerate
public import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinCatInstance
public import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinLinear
public import LeanPool.RegtsSevenster.RS.Novel.Skein.HomTraceCyclic
public import LeanPool.RegtsSevenster.RS.Novel.Skein.StarDecomposition
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ComposeAssoc
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ComposeNormal
public import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueFold
public import LeanPool.RegtsSevenster.RS.Novel.Skein.MixedPartition
public import LeanPool.RegtsSevenster.RS.Novel.Skein.PermFragment
public import LeanPool.RegtsSevenster.RS.Novel.Skein.PermCompose
public import LeanPool.RegtsSevenster.RS.Novel.Skein.Trace
public import LeanPool.RegtsSevenster.RS.Novel.Skein.TraceCyclic
public import LeanPool.RegtsSevenster.RS.Novel.Skein.TraceNondegenerate
public import LeanPool.RegtsSevenster.RS.Novel.Skein.TensorIdeal
public import LeanPool.RegtsSevenster.RS.Novel.Skein.TensorComm
public import LeanPool.RegtsSevenster.RS.Novel.Skein.HomTensor
public import LeanPool.RegtsSevenster.RS.Novel.Skein.TensorAssoc
public import LeanPool.RegtsSevenster.RS.Novel.Skein.TensorUnit
public import LeanPool.RegtsSevenster.RS.Novel.Skein.PartialCloseTensor
public import LeanPool.RegtsSevenster.RS.Novel.Skein.CloseUnion
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ComposeRelabel
public import LeanPool.RegtsSevenster.RS.Novel.Skein.PartialCloseCompose
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ScalarClass
public import LeanPool.RegtsSevenster.RS.Definitions
public import LeanPool.RegtsSevenster.RS.Novel.Extraction.CircleValue
public import LeanPool.RegtsSevenster.RS.Novel.Extraction.CoordIso
public import LeanPool.RegtsSevenster.RS.Novel.Extraction.Coordinates
public import LeanPool.RegtsSevenster.RS.Novel.Extraction.CopairUnique
public import LeanPool.RegtsSevenster.RS.Novel.Extraction.SnakeTransport
public import LeanPool.RegtsSevenster.RS.Novel.Extraction.Nondegenerate
public import LeanPool.RegtsSevenster.RS.Novel.Extraction.StdDuality
public import LeanPool.RegtsSevenster.RS.Novel.Extraction.StdRigid
public import LeanPool.RegtsSevenster.RS.Novel.Extraction.StdSuper
public import LeanPool.RegtsSevenster.RS.Classical.Interfaces.DeligneBridge
public import LeanPool.RegtsSevenster.RS.Classical.Interfaces.DelignePackage
public import LeanPool.RegtsSevenster.RS.Classical.Interfaces.DeligneTheorem
public import LeanPool.RegtsSevenster.RS.Classical.Interfaces.FibreTransport
public import LeanPool.RegtsSevenster.RS.Classical.Interfaces.EulerianIndependence
public import LeanPool.RegtsSevenster.RS.Novel.Skein.StarTrace
public import LeanPool.RegtsSevenster.RS.Novel.Skein.SnakeClasses
public import LeanPool.RegtsSevenster.RS.Classical.Super.ColourFormMatch
public import LeanPool.RegtsSevenster.RS.Classical.Super.ColourPairing
public import LeanPool.RegtsSevenster.RS.Classical.Super.ColourPairingSymm
public import LeanPool.RegtsSevenster.RS.Novel.Skein.TensorInterchange
public import LeanPool.RegtsSevenster.RS.Novel.Skein.MonoidalInstance
public import LeanPool.RegtsSevenster.RS.Novel.Skein.BraidedInstance
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ExactPairingInstance
public import LeanPool.RegtsSevenster.RS.Novel.Skein.StarCompClass
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OmegaTransport
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.SortFactor
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.StarClassFactor
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OmegaTensor
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OmegaStarVec
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CircleModel
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BraidWord
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.StarSymm
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ModelStarVec
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ParameterModel
public import LeanPool.RegtsSevenster.RS.Classical.Super.ColourConjStep
public import LeanPool.RegtsSevenster.RS.Classical.Super.ColourWord
public import LeanPool.RegtsSevenster.RS.Classical.Super.WordSignPerm
public import LeanPool.RegtsSevenster.RS.Classical.Super.ColourConjTop
public import LeanPool.RegtsSevenster.RS.Classical.Super.ColourAction
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ModelPermCoord
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CapClosed
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.MasterSum
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.StarPerm
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.StarRepeat
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.Reindex
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.FibreParam
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BlockParity
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ReindexVanish
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BetaDiagForm
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ReindexBij
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BlockData
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.RepFlag
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BetaData
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OddFlip
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BlockAlign
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.PatternInv
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ListSignPerm
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OutSignEdges
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.EdgeSign
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OddListMultiset
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OddSignProd
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BetaFlip
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CircuitCount
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.PairEnum
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.FlagEnum
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.IndexPerm
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.TauKey
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CanonPerm
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BlockCanon
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.VertexValue
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BlockOddList
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.VertexSign
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.TauCount
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.GlobalSlotList
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ChainLists
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ConcatSign
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.SignPair
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.RiffleSign
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.NFDef
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.RegroupSign
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CoreParity
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.NFValue
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ReindexHeart
public import LeanPool.RegtsSevenster.RS.TheoremForward
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CapVal
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CapSplit
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ClosedTransition
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ModelCoord
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OneBasis
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.EvLeaf
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CapExpansion
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CapPeelSplit
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BasisCoord
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BetaDiag
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.SlotPairing
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.TopBraidMerge
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.TwoBasis
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.EnvDelignePackage

/-!
# Blueprint: the axiom audit

Every main theorem of the development carries a pinned
`#print axioms` line: an axiom set drifting from the whitelist
`[propext, Classical.choice, Quot.sound]` is a compile error, not a
reading exercise.

**How to read it.** The sections group the categorical, Schur and
coordinate inputs to the forward theorem. The factorial mainline is
audited in `BlueprintFactorial.lean`.
Each pin names one theorem; the section it sits in says what that
theorem contributes.  The converse is audited in
`BlueprintConverse.lean`, the symmetric-group input in
`BlueprintSchur.lean`, and the statement surface — every definition
the summits are phrased in — in `BlueprintStatement.lean`.
-/

/-! ### Hook vanishing and the power sums

A tower whose hook-confined characters vanish has vanishing
super power sums, which is what makes the trace zeta rational.
-/

/- Upstream audit output: 'RS.superPowerSums_of_hook_vanishing' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.powerSums_zero_of_eventually_zero' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/-! ### Hook confinement and nilpotent traces

Exponentially bounded growth confines the surviving Young diagrams
to a hook, nilpotents then have vanishing trace, and the trace
criterion makes every endomorphism algebra semisimple.
-/

/- Upstream audit output: 'RS.PermTower.hook_confinement' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.FrobeniusTower.traceA_eq_zero_of_isNilpotent' depends on axioms:
  [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.isSemisimpleRing_of_trace' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/-! ### The classical bases

The symplectic and orthonormal standard bases the super model is
written in.
-/

/- Upstream audit output: 'RS.exists_symplectic_basis' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.exists_orthonormal_basis' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/-! ### Definition 5 and its transport

The mixed partition value of an edge subset, and its invariance
under a fragment equivalence.
-/

/- Upstream audit output: 'RS.EdgeSubset.mixedSummand_transport' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.mixedPartition_transport' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/-! ### The hypothesis class

The edge-rank hypothesis bounds the dimension of a row span; the
literature bounds the ranks of the finite submatrices of the
connection matrix.  The two are the same condition.
-/

/- Upstream audit output: 'RS.edgeRankBounded_iff_submatrixRank' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/-! ### The gluing calculus

Gluing a list of label pairs: permuting the list, appending,
normalising an interface, and the existence of transition data.
-/

/- Upstream audit output: 'RS.Fragment.glueListPerm' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.glueInterfaceNormal' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.Fragment.glueListAppend' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeRankParameter.val_union' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.exists_transition_orientation' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.RegtsSevensterStatement' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.composeStrandBundleLeft' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.Fragment.gluePairComm' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.composeStrandBundleRight' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/-! ### Coordinates and the standard model

Contraction families, the standard form and copairing, and the
coordinates a nondegenerate pairing gives.
-/

/- Upstream audit output: 'RS.exists_coordinates' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.exists_contraction_families' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.exists_coordinates_of_snake' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.exists_std_iso' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.stdCopair_unique' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.exists_std_model' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.stdForm_comp_stdCopair' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/-! ### Gluing across a disjoint union

The glue list distributes over a disjoint union and commutes with
swaps and folds — the associativity engine of the category.
-/

/- Upstream audit output: 'RS.Fragment.glueListDisjUnionLeft' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.Fragment.glueListDisjUnionRight' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.Fragment.glueListSwap' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.composeAssoc' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.pairCloseComposeRotate' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.pairCloseComposeRotateLeft' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.composeFinsupp_ker_left' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.composeFinsupp_ker_right' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.HomSpace.comp_ofFragment' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.HomSpace.comp_assoc' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.HomSpace.comp_id_left' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.HomSpace.comp_id_right' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.HomSpace.eq_zero_of_traces_vanish' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.skeinCategory' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.starDecomposition' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.homSpace_zero_spanned' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.interfaceShift' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.Fragment.pairCloseComm' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/-! ### The exact pairing

The self-duality of the standard model, and that it is braided.
-/

/- Upstream audit output: 'RS.ExactPairing.map' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.braided_std_model' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/-! ### The trace calculus

Closing a fragment against the strand bundle: relabels cross it,
tensors absorb, and permutation fragments compose.
-/

/- Upstream audit output: 'RS.pairCloseRelabel' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.fragTrace_comm' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.permFragmentCompose' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.mem_ker_of_traces_vanish' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.pairCloseTensorAbsorb' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.tensorFinsupp_ker_left' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.tensorFinsupp_ker_right' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.HomSpace.tensor_ofFragment' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.tensorFragmentAssoc' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.tensorFragmentUnitLeft' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.tensorFragmentUnitRight' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/-! ### The braided envelope

The Karoubi and matrix envelopes inherit the braiding and its
symmetry.
-/

/- Upstream audit output: 'RS.karoubiBraided' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.karoubiSymmetric' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.matBraided' depends on axioms: [propext, Classical.choice, Quot.sound]
  -/

/- Upstream audit output: 'RS.matSymmetric' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/-! ### The skein category

Linear, monoidal and rigid structure on the skein category, and
the trace map it carries.
-/

/- Upstream audit output: 'RS.skeinPreadditive' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.skeinLinear' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.HomSpace.traceMap_comp_comm' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.partialCloseTensor' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.pairCloseUnionRight' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.fragTrace_tensor' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.composeRelabelOut' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.composePermFragment' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.partialCloseEqCompose' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.ofFragment_eq_smul_empty' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.pairCloseStrandBundle' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.starDecomposition' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.snake_left' depends on axioms: [propext, Classical.choice, Quot.sound]
  -/

/- Upstream audit output: 'RS.snake_right' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.braid_comp_evClass' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.Fragment.tensorComposeInterchange' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.skeinMonoidal' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.skeinBraided' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.skeinSymmetric' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.strandExactPairing' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.strand_ev_symmetry' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.star_comp_class' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/-! ### The coordinate model

The fibre functor's image of a star, the standard model it is
identified with, and the transport between them.
-/

/- Upstream audit output: 'RS.omega_star_scalar' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.skein_std_model' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.starUnionFactor' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.starClass_factor' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.omegaVec_tensor' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.parameter_star_factor' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.circleVal_model' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.stdFromOmega_stdToOmega' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.adjWord_spec' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.stdToOmega_powBraid' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.stdToOmega_bmc_perm' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.bundleCapClass_peel' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.point_cotensor' depends on axioms: [propext, Quot.sound] -/

/- Upstream audit output: 'RS.omegaFun_tensor' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.evForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.vertexStarClass_perm' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.stdToOmega_merge' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.stdToOmega_modelStarVec' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.toColour_whisker' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.parameter_model' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.colourExtend_colourSwap' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.colourSwapWord_evenMap' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.parameter_capVal' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.ClosedFragment.eulerian_transition_nonempty' depends on axioms:
  [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.omegaFun_capTensor_merge' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.omegaFun_tensor_oddPair' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.colourMerge_coord' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.colourMerge_coord_oddPair' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.coordOf_modelStarVec' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.evenBasisVec_split' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.evFormOdd' depends on axioms: [propext, Classical.choice, Quot.sound]
  -/

/- Upstream audit output: 'RS.stdToOmega_one' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.stdToOmega_one_even' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.stdToOmega_one_odd' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.evenBasisVec_one' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.oddBasisVec_one' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.stdForm_evenPair' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.stdForm_oddPair' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.omegaFun_ev_basis' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.capVal_expansion' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.splitCapVal_expansion' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.splitCapVal_merge' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.capVal_succ' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.coordOf_evenBasisVec' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.splitCapVal_oddMerge' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.peelColour_spec' depends on axioms: [propext, Quot.sound] -/

/- Upstream audit output: 'RS.eq_peelColour_of' depends on axioms: [propext, Quot.sound] -/

/- Upstream audit output: 'RS.peelColour_isEven' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.pairing_starFlagEnum_symm' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.powMerge_topBraid' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.wordSign_eq_oddInversions' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.toColour_topBraid' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.toColour_powBraid' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.toColour_powBraidWord' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/-! ### The master colour sum

The parameter as a sum over colourings: the star coordinates, the
diagonal cap pairing, every sign family, and the reindexing that
turns the sum into Definition 5.
-/

/- Upstream audit output: 'RS.wordPerm_adjWord' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.coordOf_modelPermMap' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.coordOf_modelPermMap'' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.capVal_closed' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.parameter_colour_sum' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.starVec_perm' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.stdFromOmega_perm' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.starCoord_perm' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.oddInversions_adjacent' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.starCoord_repeat_zero' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.parameter_masterSummand' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.masterSum_partition' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.colourFlags_pairing_mem' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.colourFlags_colouringOf' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.card_even' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.colouringOf_isEven' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.colouringOf_diagonal' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.blockRestrict_parity' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.masterSummand_vanish_of_block_odd' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.masterSummand_vanish_of_not_eulerian' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.mem_colourFlags_iff' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.starFlagEnum_pairing_low' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.starFlagEnum_pairing_high' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.oddDataOf_constancy' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.evenDataOf_constancy' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.betaDiag_eq_betaColour' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.betaColour_perm'' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.masterSummand_vanish_of_impure' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.masterSummand_vanish_of_not_closed' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.colouringOf_reconstruct' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.oddColouringOf_colouringOf' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.evenColouringOf_colouringOf' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.masterSummand_vanish_of_not_diagonal' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.pairPure_of_pattern_closed' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.fibreSum_eq_dataSum' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.koszulCrossings_colouringOf' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.image_blockFlag' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.blockRestrict_colouringOf' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.blockRestrict_colouringOf_isRight' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.repFlag_pairing' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.outRepSet_pairing_mem' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.colourFormEntry_inr_partner' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.betaDiag_colouringOf' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.evenColoursAt_blockVertex' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.OddColouring.sum_flip' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.blockRestrict_colouringOfFlip_mem' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.map_flagsAt_blockVertex' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.oddInversions_colouringOf' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.sortSign_ofFn_comp_perm' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.prod_out_sign_eq_prod_edges' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.edge_sign_sector' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.oddListAt_coe_multiset' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.prod_oddSignAt' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.betaDiag_colouringOfFlip' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/-
info: 'RS.EdgeSubset.TransitionSystem.circuitCount_eq_orbitCount_outPerm' depends on axioms:
  [propext,
 Classical.choice,
 Quot.sound]
-/

/- Upstream audit output: 'RS.EdgeSubset.TransitionSystem.neg_one_pow_circuitCount' depends on
  axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.oddListAt_eq_map' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.pairFlagList_nodup' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.mem_blockOddFlagList_iff_pairFlagList' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.prod_blockVertex' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.sortSign_map_listIndexPerm' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.sign_listIndexPerm_trans' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.sortSign_pairFlagList_key' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.exists_canonPerm' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.oddListOf_blockRestrict' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.evenMultisetOf_blockRestrict' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.starCoord_block_flip_nodup' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.starCoord_block_flip_not_nodup' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.oddListOf_blockRestrict_eq_map' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.vertex_sign_collapse' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.patternOddInv_eq_inversions' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.sortSign_globalPairList' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.sign_listIndexPerm_slot_edge' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.sign_listIndexPerm_edge_oriented' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.hMaster_vertex_nodup' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.defFiveNF_eq_flip' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.sign_listIndexPerm_oriented_matched' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.sign_listIndexPerm_matched_global' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.core_parity' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.grand_parity' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.masterSummand_colouringOfFlip' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.fibreSum_eq' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.parameter_eq_mixedPartition' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.hMaster_colouringOfFlip' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.mixedSummand_eq_nf' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.eulerian_independence_closed' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.mixedValue_eq_summand_closed' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/-! ### Deligne's hypotheses for the envelope

Each hypothesis of the cited theorem, discharged for the concrete
envelope, and the package they assemble into.
-/

/- Upstream audit output: 'RS.env_deligneSemisimple' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.env_deligneGenerated' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.env_deligneModerateGrowth' depends on axioms: [propext,
  Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.env_delignePackage' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/- Upstream audit output: 'RS.skein_delignePackage' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/

/-! ### The forward theorem -/
