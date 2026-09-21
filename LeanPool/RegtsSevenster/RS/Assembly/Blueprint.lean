/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.MathlibDeps
import LeanPool.RegtsSevenster.RS.Common.YoungDiagrams
import LeanPool.RegtsSevenster.RS.Classical.SymFun.PowerSums
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.ColourCycleSum
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.JTOrtho
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.SignResolve
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.NativeFaithful
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.SquareGrowth
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.BranchTrace
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.JTPad
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.PackageAssembly
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.Package
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.PairingPos
import LeanPool.RegtsSevenster.RS.Novel.Envelope.TraceZeta
import LeanPool.RegtsSevenster.RS.Classical.SymFun.ZetaExp
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.SquareGrowthSharp
import LeanPool.RegtsSevenster.RS.Novel.Envelope.HookConfinementSharp
import LeanPool.RegtsSevenster.RS.Novel.Envelope.SkeinDimBound
import LeanPool.RegtsSevenster.RS.Novel.Skein.PathMatch
import LeanPool.RegtsSevenster.RS.Novel.Envelope.SuperKill
import LeanPool.RegtsSevenster.RS.StatementConverse
import LeanPool.RegtsSevenster.RS.TheoremQuant
import LeanPool.RegtsSevenster.RS.Classical.SymFun.LGVStrict
import LeanPool.RegtsSevenster.RS.Novel.Skein.ClosedAgreement
import LeanPool.RegtsSevenster.RS.Novel.Skein.TransitionMove
import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueRelTransport
import LeanPool.RegtsSevenster.RS.Novel.Skein.DisjSubsetSplit
import LeanPool.RegtsSevenster.RS.Novel.Skein.InterfaceOrderIso
import LeanPool.RegtsSevenster.RS.Novel.Skein.ThroughValue
import LeanPool.RegtsSevenster.RS.Novel.Skein.RelabelInvariance
import LeanPool.RegtsSevenster.RS.Novel.Skein.DisjUnionFactor
import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueCircuitDelta
import LeanPool.RegtsSevenster.RS.Novel.Skein.ChainAgreement
import LeanPool.RegtsSevenster.RS.Novel.Skein.CanonExistence
import LeanPool.RegtsSevenster.RS.Novel.Skein.RepairInvariance
import LeanPool.RegtsSevenster.RS.Novel.Skein.PathLedger
import LeanPool.RegtsSevenster.RS.Novel.Skein.ChordParity
import LeanPool.RegtsSevenster.RS.Novel.Skein.PairingConnectivity
import LeanPool.RegtsSevenster.RS.Novel.Skein.StepLedger
import LeanPool.RegtsSevenster.RS.Novel.Skein.InvolutionCard
import LeanPool.RegtsSevenster.RS.Novel.Skein.ChordCount
import LeanPool.RegtsSevenster.RS.Novel.Skein.AllInternalIndependence
import LeanPool.RegtsSevenster.RS.Novel.Skein.AllInternalAgreement
import LeanPool.RegtsSevenster.RS.Novel.Skein.ConverseAssembly
import LeanPool.RegtsSevenster.RS.Novel.Skein.InterfaceAlternate
import LeanPool.RegtsSevenster.RS.Novel.Skein.ConverseDischarge
import LeanPool.RegtsSevenster.RS.Novel.Skein.ConverseGram
import LeanPool.RegtsSevenster.RS.Novel.Skein.TransposeLedger
import LeanPool.RegtsSevenster.RS.Novel.Skein.TwoPathNonSep
import LeanPool.RegtsSevenster.RS.Novel.Skein.CanonicalFrame
import LeanPool.RegtsSevenster.RS.Novel.Skein.StepFrame
import LeanPool.RegtsSevenster.RS.Novel.Skein.StateFlipSet
import LeanPool.RegtsSevenster.RS.Novel.Skein.StatusSet
import LeanPool.RegtsSevenster.RS.Novel.Skein.CrossingDelta
import LeanPool.RegtsSevenster.RS.Novel.Skein.FlipSignProduct
import LeanPool.RegtsSevenster.RS.Novel.Skein.FlipSignForm
import LeanPool.RegtsSevenster.RS.Novel.Skein.LedgerSets
import LeanPool.RegtsSevenster.RS.Novel.Skein.StepStatus
import LeanPool.RegtsSevenster.RS.Novel.Skein.StepStatusNonsep
import LeanPool.RegtsSevenster.RS.Novel.Skein.PairedAssembly
import LeanPool.RegtsSevenster.RS.Novel.Skein.PropThreeOpen
import LeanPool.RegtsSevenster.RS.Novel.Skein.FourLabelParity
import LeanPool.RegtsSevenster.RS.Novel.Skein.PairingSwap
import LeanPool.RegtsSevenster.RS.Novel.Skein.PairingSignature
import LeanPool.RegtsSevenster.RS.Novel.Skein.PairingValue
import LeanPool.RegtsSevenster.RS.Novel.Skein.LedgerValue
import LeanPool.RegtsSevenster.RS.Novel.Skein.LoopVerify
import LeanPool.RegtsSevenster.RS.Novel.Skein.ThroughIndCFalse
import LeanPool.RegtsSevenster.RS.Novel.Skein.ChordLabels
import LeanPool.RegtsSevenster.RS.Novel.Skein.LabelChords
import LeanPool.RegtsSevenster.RS.Novel.Skein.FibreValue
import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueChords
import LeanPool.RegtsSevenster.RS.Novel.Skein.GluePathMatch
import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueCrossDelta
import LeanPool.RegtsSevenster.RS.Novel.Skein.ClosedCutDispatch
import LeanPool.RegtsSevenster.RS.Novel.Skein.ThroughEdgeCut
import LeanPool.RegtsSevenster.RS.Novel.Skein.RelabelChords
import LeanPool.RegtsSevenster.RS.Novel.Skein.ChordSwapParity
import LeanPool.RegtsSevenster.RS.Classical.SymFun.SuperPowerSums
import LeanPool.RegtsSevenster.RS.Classical.SymFun.RecurrenceFromVanishing
import LeanPool.RegtsSevenster.RS.Classical.SymFun.RationalityFromRecurrence
import LeanPool.RegtsSevenster.RS.Classical.SymFun.HookVanishing
import LeanPool.RegtsSevenster.RS.Classical.Interfaces.SchurPackage
import LeanPool.RegtsSevenster.RS.Novel.Envelope.BlockBounds
import LeanPool.RegtsSevenster.RS.Novel.Envelope.HookConfinement
import LeanPool.RegtsSevenster.RS.Novel.Envelope.KaroubiMonoidal
import LeanPool.RegtsSevenster.RS.Novel.Envelope.MatMonoidal
import LeanPool.RegtsSevenster.RS.Novel.Envelope.MatBraided
import LeanPool.RegtsSevenster.RS.Novel.Envelope.NilpotentTrace
import LeanPool.RegtsSevenster.RS.Novel.Envelope.SemisimpleEnd
import LeanPool.RegtsSevenster.RS.Classical.Super.OrthonormalBasis
import LeanPool.RegtsSevenster.RS.Classical.Super.SuperVect
import LeanPool.RegtsSevenster.RS.Classical.Super.SymplecticBasis
import LeanPool.RegtsSevenster.RS.Novel.Skein.FlagGraph
import LeanPool.RegtsSevenster.RS.Novel.Skein.Composition
import LeanPool.RegtsSevenster.RS.Novel.Skein.FragmentEquiv
import LeanPool.RegtsSevenster.RS.Novel.Skein.CompositionEquiv
import LeanPool.RegtsSevenster.RS.Novel.Skein.StrandBundle
import LeanPool.RegtsSevenster.RS.Novel.Skein.IdentityLaw
import LeanPool.RegtsSevenster.RS.Novel.Skein.IdentityLawRight
import LeanPool.RegtsSevenster.RS.Novel.Skein.ConnectionRank
import LeanPool.RegtsSevenster.RS.Novel.Skein.HomSpaces
import LeanPool.RegtsSevenster.RS.Novel.Skein.Multiplicativity
import LeanPool.RegtsSevenster.RS.Novel.Skein.Eulerian
import LeanPool.RegtsSevenster.RS.Novel.Skein.TransitionExists
import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueAmbient
import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueComm
import LeanPool.RegtsSevenster.RS.Novel.Skein.CloseRotate
import LeanPool.RegtsSevenster.RS.Novel.Skein.CloseRotateLeft
import LeanPool.RegtsSevenster.RS.Novel.Skein.InterfaceShift
import LeanPool.RegtsSevenster.RS.Novel.Skein.PairCloseComm
import LeanPool.RegtsSevenster.RS.Novel.Skein.SimpleUnit
import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinIdeal
import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinIdealLeft
import LeanPool.RegtsSevenster.RS.Novel.Skein.HomCompose
import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinCategory
import LeanPool.RegtsSevenster.RS.Novel.Skein.HomTraceNondegenerate
import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinCatInstance
import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinLinear
import LeanPool.RegtsSevenster.RS.Novel.Skein.HomTraceCyclic
import LeanPool.RegtsSevenster.RS.Novel.Skein.StarDecomposition
import LeanPool.RegtsSevenster.RS.Novel.Skein.ComposeAssoc
import LeanPool.RegtsSevenster.RS.Novel.Skein.ComposeNormal
import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueFold
import LeanPool.RegtsSevenster.RS.Novel.Skein.MixedPartition
import LeanPool.RegtsSevenster.RS.Novel.Skein.PermFragment
import LeanPool.RegtsSevenster.RS.Novel.Skein.PermCompose
import LeanPool.RegtsSevenster.RS.Novel.Skein.Trace
import LeanPool.RegtsSevenster.RS.Novel.Skein.TraceCyclic
import LeanPool.RegtsSevenster.RS.Novel.Skein.TraceNondegenerate
import LeanPool.RegtsSevenster.RS.Novel.Skein.TensorIdeal
import LeanPool.RegtsSevenster.RS.Novel.Skein.TensorComm
import LeanPool.RegtsSevenster.RS.Novel.Skein.HomTensor
import LeanPool.RegtsSevenster.RS.Novel.Skein.TensorAssoc
import LeanPool.RegtsSevenster.RS.Novel.Skein.TensorUnit
import LeanPool.RegtsSevenster.RS.Novel.Skein.PartialCloseTensor
import LeanPool.RegtsSevenster.RS.Novel.Skein.CloseUnion
import LeanPool.RegtsSevenster.RS.Novel.Skein.ComposeRelabel
import LeanPool.RegtsSevenster.RS.Novel.Skein.PartialCloseCompose
import LeanPool.RegtsSevenster.RS.Novel.Skein.ScalarClass
import LeanPool.RegtsSevenster.RS.Definitions
import LeanPool.RegtsSevenster.RS.Novel.Extraction.CircleValue
import LeanPool.RegtsSevenster.RS.Novel.Extraction.CoordIso
import LeanPool.RegtsSevenster.RS.Novel.Extraction.Coordinates
import LeanPool.RegtsSevenster.RS.Novel.Extraction.CopairUnique
import LeanPool.RegtsSevenster.RS.Novel.Extraction.SnakeTransport
import LeanPool.RegtsSevenster.RS.Novel.Extraction.Nondegenerate
import LeanPool.RegtsSevenster.RS.Novel.Extraction.StdDuality
import LeanPool.RegtsSevenster.RS.Novel.Extraction.StdRigid
import LeanPool.RegtsSevenster.RS.Novel.Extraction.StdSuper
import LeanPool.RegtsSevenster.RS.Classical.Interfaces.DeligneBridge
import LeanPool.RegtsSevenster.RS.Classical.Interfaces.DelignePackage
import LeanPool.RegtsSevenster.RS.Classical.Interfaces.DeligneTheorem
import LeanPool.RegtsSevenster.RS.Classical.Interfaces.FibreTransport
import LeanPool.RegtsSevenster.RS.Classical.Interfaces.EulerianIndependence
import LeanPool.RegtsSevenster.RS.Novel.Skein.StarTrace
import LeanPool.RegtsSevenster.RS.Novel.Skein.SnakeClasses
import LeanPool.RegtsSevenster.RS.Classical.Super.ColourFormMatch
import LeanPool.RegtsSevenster.RS.Classical.Super.ColourPairing
import LeanPool.RegtsSevenster.RS.Classical.Super.ColourPairingSymm
import LeanPool.RegtsSevenster.RS.Novel.Skein.TensorInterchange
import LeanPool.RegtsSevenster.RS.Novel.Skein.MonoidalInstance
import LeanPool.RegtsSevenster.RS.Novel.Skein.BraidedInstance
import LeanPool.RegtsSevenster.RS.Novel.Skein.ExactPairingInstance
import LeanPool.RegtsSevenster.RS.Novel.Skein.StarCompClass
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OmegaTransport
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.SortFactor
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.StarClassFactor
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OmegaTensor
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OmegaStarVec
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CircleModel
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BraidWord
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.StarSymm
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ModelStarVec
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ParameterModel
import LeanPool.RegtsSevenster.RS.Classical.Super.ColourConjStep
import LeanPool.RegtsSevenster.RS.Classical.Super.ColourWord
import LeanPool.RegtsSevenster.RS.Classical.Super.WordSignPerm
import LeanPool.RegtsSevenster.RS.Classical.Super.ColourConjTop
import LeanPool.RegtsSevenster.RS.Classical.Super.ColourAction
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ModelPermCoord
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CapClosed
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.MasterSum
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.StarPerm
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.StarRepeat
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.Reindex
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.FibreParam
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BlockParity
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ReindexVanish
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BetaDiagForm
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ReindexBij
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BlockData
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.RepFlag
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BetaData
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OddFlip
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BlockAlign
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.PatternInv
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ListSignPerm
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OutSignEdges
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.EdgeSign
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OddListMultiset
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OddSignProd
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BetaFlip
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CircuitCount
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.PairEnum
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.FlagEnum
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.IndexPerm
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.TauKey
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CanonPerm
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BlockCanon
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.VertexValue
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BlockOddList
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.VertexSign
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.TauCount
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.GlobalSlotList
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ChainLists
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ConcatSign
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.SignPair
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.RiffleSign
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.NFDef
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.RegroupSign
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CoreParity
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.NFValue
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ReindexHeart
import LeanPool.RegtsSevenster.RS.TheoremForward
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CapVal
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CapSplit
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ClosedTransition
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ModelCoord
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.OneBasis
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.EvLeaf
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CapExpansion
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CapPeelSplit
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BasisCoord
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BetaDiag
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.SlotPairing
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.TopBraidMerge
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.TwoBasis
import LeanPool.RegtsSevenster.RS.Novel.Envelope.EnvDelignePackage

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

/-- info: 'RS.superPowerSums_of_hook_vanishing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.powerSums_zero_of_eventually_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-! ### Hook confinement and nilpotent traces

Exponentially bounded growth confines the surviving Young diagrams
to a hook, nilpotents then have vanishing trace, and the trace
criterion makes every endomorphism algebra semisimple.
-/

/-- info: 'RS.PermTower.hook_confinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.FrobeniusTower.traceA_eq_zero_of_isNilpotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.isSemisimpleRing_of_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-! ### The classical bases

The symplectic and orthonormal standard bases the super model is
written in.
-/

/-- info: 'RS.exists_symplectic_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.exists_orthonormal_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-! ### Definition 5 and its transport

The mixed partition value of an edge subset, and its invariance
under a fragment equivalence.
-/

/-- info: 'RS.EdgeSubset.mixedSummand_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.mixedPartition_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-! ### The hypothesis class

The edge-rank hypothesis bounds the dimension of a row span; the
literature bounds the ranks of the finite submatrices of the
connection matrix.  The two are the same condition.
-/

/-- info: 'RS.edgeRankBounded_iff_submatrixRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-! ### The gluing calculus

Gluing a list of label pairs: permuting the list, appending,
normalising an interface, and the existence of transition data.
-/

/-- info: 'RS.Fragment.glueListPerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.glueInterfaceNormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.Fragment.glueListAppend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.EdgeRankParameter.val_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.EdgeSubset.exists_transition_orientation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.RegtsSevensterStatement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.composeStrandBundleLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.Fragment.gluePairComm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.composeStrandBundleRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-! ### Coordinates and the standard model

Contraction families, the standard form and copairing, and the
coordinates a nondegenerate pairing gives.
-/

/-- info: 'RS.exists_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.exists_contraction_families' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.exists_coordinates_of_snake' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.exists_std_iso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.stdCopair_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.exists_std_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.stdForm_comp_stdCopair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-! ### Gluing across a disjoint union

The glue list distributes over a disjoint union and commutes with
swaps and folds — the associativity engine of the category.
-/

/-- info: 'RS.Fragment.glueListDisjUnionLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.Fragment.glueListDisjUnionRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.Fragment.glueListSwap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.composeAssoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.pairCloseComposeRotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.pairCloseComposeRotateLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.composeFinsupp_ker_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.composeFinsupp_ker_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.HomSpace.comp_ofFragment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.HomSpace.comp_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.HomSpace.comp_id_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.HomSpace.comp_id_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.HomSpace.eq_zero_of_traces_vanish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.skeinCategory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.starDecomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.homSpace_zero_spanned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.interfaceShift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.Fragment.pairCloseComm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-! ### The exact pairing

The self-duality of the standard model, and that it is braided.
-/

/-- info: 'RS.ExactPairing.map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.braided_std_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-! ### The trace calculus

Closing a fragment against the strand bundle: relabels cross it,
tensors absorb, and permutation fragments compose.
-/

/-- info: 'RS.pairCloseRelabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.fragTrace_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.permFragmentCompose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.mem_ker_of_traces_vanish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.pairCloseTensorAbsorb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.tensorFinsupp_ker_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.tensorFinsupp_ker_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.HomSpace.tensor_ofFragment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.tensorFragmentAssoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.tensorFragmentUnitLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.tensorFragmentUnitRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-! ### The braided envelope

The Karoubi and matrix envelopes inherit the braiding and its
symmetry.
-/

/-- info: 'RS.karoubiBraided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.karoubiSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.matBraided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.matSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-! ### The skein category

Linear, monoidal and rigid structure on the skein category, and
the trace map it carries.
-/

/-- info: 'RS.skeinPreadditive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.skeinLinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.HomSpace.traceMap_comp_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.partialCloseTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.pairCloseUnionRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.fragTrace_tensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.composeRelabelOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.composePermFragment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.partialCloseEqCompose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.ofFragment_eq_smul_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.pairCloseStrandBundle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.starDecomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.snake_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.snake_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.braid_comp_evClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.Fragment.tensorComposeInterchange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.skeinMonoidal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.skeinBraided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.skeinSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.strandExactPairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.strand_ev_symmetry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.star_comp_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-! ### The coordinate model

The fibre functor's image of a star, the standard model it is
identified with, and the transport between them.
-/

/-- info: 'RS.omega_star_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.skein_std_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.starUnionFactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.starClass_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.omegaVec_tensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.parameter_star_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.circleVal_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.stdFromOmega_stdToOmega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.adjWord_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.stdToOmega_powBraid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.stdToOmega_bmc_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.bundleCapClass_peel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.point_cotensor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.omegaFun_tensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.evForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.vertexStarClass_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.stdToOmega_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.stdToOmega_modelStarVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.toColour_whisker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.parameter_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.colourExtend_colourSwap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.colourSwapWord_evenMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.parameter_capVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.ClosedFragment.eulerian_transition_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.omegaFun_capTensor_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.omegaFun_tensor_oddPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.colourMerge_coord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.colourMerge_coord_oddPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.coordOf_modelStarVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.evenBasisVec_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.evFormOdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.stdToOmega_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.stdToOmega_one_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.stdToOmega_one_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.evenBasisVec_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.oddBasisVec_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.stdForm_evenPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.stdForm_oddPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.omegaFun_ev_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.capVal_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.splitCapVal_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.splitCapVal_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.capVal_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.coordOf_evenBasisVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.splitCapVal_oddMerge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.peelColour_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.eq_peelColour_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.peelColour_isEven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.pairing_starFlagEnum_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.powMerge_topBraid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.wordSign_eq_oddInversions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.toColour_topBraid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.toColour_powBraid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.toColour_powBraidWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-! ### The master colour sum

The parameter as a sum over colourings: the star coordinates, the
diagonal cap pairing, every sign family, and the reindexing that
turns the sum into Definition 5.
-/

/-- info: 'RS.wordPerm_adjWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.coordOf_modelPermMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.coordOf_modelPermMap'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.capVal_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.parameter_colour_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.starVec_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.stdFromOmega_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.starCoord_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.oddInversions_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.starCoord_repeat_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.parameter_masterSummand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.masterSum_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.colourFlags_pairing_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.colourFlags_colouringOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.EdgeSubset.card_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.colouringOf_isEven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.colouringOf_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.blockRestrict_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.masterSummand_vanish_of_block_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.masterSummand_vanish_of_not_eulerian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.mem_colourFlags_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.starFlagEnum_pairing_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.starFlagEnum_pairing_high' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.oddDataOf_constancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.evenDataOf_constancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.betaDiag_eq_betaColour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.betaColour_perm'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.masterSummand_vanish_of_impure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.masterSummand_vanish_of_not_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.colouringOf_reconstruct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.oddColouringOf_colouringOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.evenColouringOf_colouringOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.masterSummand_vanish_of_not_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.pairPure_of_pattern_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.fibreSum_eq_dataSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.koszulCrossings_colouringOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.image_blockFlag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.blockRestrict_colouringOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.blockRestrict_colouringOf_isRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.repFlag_pairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.outRepSet_pairing_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.colourFormEntry_inr_partner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.betaDiag_colouringOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.evenColoursAt_blockVertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.EdgeSubset.OddColouring.sum_flip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.blockRestrict_colouringOfFlip_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.map_flagsAt_blockVertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.oddInversions_colouringOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.sortSign_ofFn_comp_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.prod_out_sign_eq_prod_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.edge_sign_sector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.oddListAt_coe_multiset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.prod_oddSignAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.betaDiag_colouringOfFlip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/--
info: 'RS.EdgeSubset.TransitionSystem.circuitCount_eq_orbitCount_outPerm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in

/-- info: 'RS.EdgeSubset.TransitionSystem.neg_one_pow_circuitCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.oddListAt_eq_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.pairFlagList_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.mem_blockOddFlagList_iff_pairFlagList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.prod_blockVertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.sortSign_map_listIndexPerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.sign_listIndexPerm_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.sortSign_pairFlagList_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.exists_canonPerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.oddListOf_blockRestrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.evenMultisetOf_blockRestrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.starCoord_block_flip_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.starCoord_block_flip_not_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.oddListOf_blockRestrict_eq_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.vertex_sign_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.patternOddInv_eq_inversions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.sortSign_globalPairList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.sign_listIndexPerm_slot_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.sign_listIndexPerm_edge_oriented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.hMaster_vertex_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.defFiveNF_eq_flip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.sign_listIndexPerm_oriented_matched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.sign_listIndexPerm_matched_global' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.core_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.grand_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.masterSummand_colouringOfFlip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.fibreSum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.parameter_eq_mixedPartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.hMaster_colouringOfFlip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.mixedSummand_eq_nf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.eulerian_independence_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.mixedValue_eq_summand_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-! ### Deligne's hypotheses for the envelope

Each hypothesis of the cited theorem, discharged for the concrete
envelope, and the package they assemble into.
-/

/-- info: 'RS.env_deligneSemisimple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.env_deligneGenerated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.env_deligneModerateGrowth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.env_delignePackage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-- info: 'RS.skein_delignePackage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in

/-! ### The forward theorem -/
