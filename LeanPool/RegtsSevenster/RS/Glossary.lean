/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Glossary

Recurring vocabulary of the development, for auditors.

* **Fragment** — a finite multigraph in half-edge (flag) form over
  a boundary-label type, with a fixed-point-free edge involution
  (`pairing`), a distinguished flag at each boundary label
  (`boundaryFlag`), and a separate free-circle count.
* **Closed fragment** — a fragment over `Fin 0`: a plain
  multigraph with free circles.
* **Gluing** (`gluePair`) — joining the half-edges at two boundary
  labels: the closing case makes a free circle, the rewiring case
  unifies two edges end to end.
* **Composition** (`Fragment.compose`) — gluing the last `t`
  labels of an `(s + t)`-fragment to the first `t` of a
  `(t + u)`-fragment, top pair first.
* **Strand bundle** (`strandBundle t`) — `t` parallel edges, the
  identity fragments.
* **Edge subset** (`EdgeSubset`) — a pairing-closed set of flags;
  **Eulerian** when every vertex meets it in an even number of
  flags.
* **Transition system** (`TransitionSystem`) — the local pairing
  `κ` of Definition 5: a fixed-point-free vertex-preserving
  involution of the participating flags.  Its **walk permutation**
  composes `κ` with the edge pairing; each geometric circuit
  carries two walk-orbits (its directions), whence the **circuit
  count**.
* **Mixed functional** (`MixedFunctional`) — the `(k, 2ℓ)` vertex
  data of a mixed partition function: values on multisets of even
  colours and sets of odd colours, with antisymmetry supplied by
  the sorting-sign evaluator (`evalOdd`).
* **Mixed partition function** (`mixedPartition`,
  `IsMixedPartitionFunction`) — Definition 5 on the flag model:
  the sum over Eulerian edge subsets of circuit-signed colouring
  sums against a `(k, 2ℓ)` vertex functional, with the
  `(k − 2ℓ)^{circles}` free-circle convention.  The bounded form
  (`IsMixedPartitionFunctionBounded`) additionally pins `k` and
  `2ℓ` below a stated bound.
* **Total bound** (`TotalBoundedMixedModel`,
  `IsMixedPartitionFunctionTotalBounded`) — a representing functional
  whose total number of colours `k + 2ℓ` is bounded. The witness has
  named dimension, functional and evaluation fields;
  `regts_sevenster_total` gives total bound `R` from edge-rank base `R`.
* **Minimum colour dimension** (`minimumColourDimension`) — the
  least total colour bound of a representing mixed model. It is
  attained and equals the even connection-rank growth rate.
* **Natural connection rank** (`connectionRank`) — the finrank of
  the actual connection-map range. Under an edge-rank bound its
  cardinal cast equals the module rank (`connectionRank_cast_eq_rank`).
* **Prescribed colour bounds** (`PrescribedColourBounds`) — the
  rank bound with base `k + 2ℓ` and free-circle value `k − 2ℓ`.
  `regts_sevenster_prescribed` characterizes models of exactly those
  parity dimensions, including the zero-dimensional case.
* **Colour embedding** (`MixedColourEmbedding`) — embeddings of
  even and odd colours preserving odd order, symplectic partners
  and partner signs. `extendColours` extends a vertex functional by
  zero; `padColours` uses the embeddings supplied by dimension
  inequalities. Balanced padding preserves the partition function.
* **Total space** (`Tot`, `tot`, `totIso`) — the product of the even
  and odd components of a super vector space, its componentwise maps
  and its induced linear equivalences. `colourTotalEquiv` identifies
  a total tensor power with functions on all colour words.
* **Monomial word action** (`MonomialWordAction`) — a permutation of
  positions acting on word coordinates with nonzero scalar weights.
  Its commutant consists of the intertwining endomorphisms; the
  letter-pair counts give `finrank_commutant_le_word_counts`.
* **Connection pairing / edge rank** — the closure pairing of a
  parameter at arity `t`.  `EdgeRankBounded f R` says every arity's
  pairing has rank at most `R ^ t`, rank being the dimension of the
  row span; the literature's reading — the supremum of the ranks of
  the finite submatrices of the connection matrix — is the same
  condition (`SubmatrixRankBounded`,
  `edgeRankBounded_iff_submatrixRank`).  The hypothesis class
  (`EdgeRankParameter`) packages the bound with normalization at
  the empty graph and isomorphism invariance.
* **Relative transition system** (`RelTransitionSystem`) — the
  open-fragment analogue: an involution of the *internal*
  participating flags; boundary flags start **boundary chains**,
  whose end-to-end matching is the **path matching** (`pathMatch`)
  and whose label pairs form the **chord diagram**
  (`labelChords`, a faithful pairing invariant).
* **Chord sign / path sign** (`pathSign`) — `(−1)` to the number
  of interleaving chord pairs of the boundary pairing; a function
  of the diagram alone.
* **Canonical frame** (`PathCanonical`) — the orientation class
  directing every boundary chain low-label-to-high; the **chain
  direction observable** (`chainDir`) equals high-status on it,
  and any orientation re-canonicalizes by whole-chain flips
  (`exists_recanonicalize`) at the cost of symplectic signs and
  odd-partner state relabels (`stateOddFlipSet`).
* **Repair** (`repair`) — the elementary 2-opt re-pairing move;
  non-localized repairs transpose the boundary pairing
  (`pathMatch_repair_swap`), and the pairing fibre is connected by
  π-returning blocks (`pairingConnectivity`).
* **The pairing-fibre ledger** (`pairedLedger`) — open-sector
  Proposition 3: across every π-returning repair block the
  `pathSign`-weighted canonical summand is preserved, so the
  signed canonical value (`signedValueAt`) depends on the boundary
  pairing alone.  Independence *across* pairings is false
  (`not_throughIndependenceC`), which is why the value is
  pairing-resolved.
* **The diagram gluing** (`glueChords`) — the Temperley–Lieb
  concatenation of a label chord diagram at a cut, whose crossing
  parity change is `diagCrossCount_glue_cross`: the chord-sign
  ratio the participating-cut splitting carries.
* **The interface lift** (`liftData`, `pushData`, `bitsOf`) — a
  family of transition data carried up the gluing interface one
  cut at a time and back down again.  A closing cut leaves the
  lift a free bit, since a glued subset has two lifts; read with
  the bits a subset itself determines (`bitsOf`), the round trip
  returns the family up to matching equality.
* **The pair family** (`pairFamily`) — a datum at every subset of
  the composition's base carrying RS21's (13) and (14) at once:
  the pair term as the composition's signed colouring sum, the
  pairing flipping along every interface edge, and the alternation
  across every interface pair that step 1 asks for.
* **The in-set at a vertex** (`relInSetAt`) — the participating
  flags attached to a vertex and marked incoming by a relative
  orientation, of which `relInFlagsAt` is the sorted enumeration.
  Each carries an **incoming sign** (`inSign`); flipping the
  colours on a set negates the sign exactly there, which makes the
  flip analysis a product of independent local factors.
* **The cut factor** (`cutFactor`) — the free circles a subset's
  own closing cuts contribute: `k` where the subset leaves a
  closing cut's edge out and `−2ℓ` where it carries it, the two
  sectors of the circle the glue creates
  (`edgeTermAt_pushData_colourSum`).
* **Tensor power** (`tensorPow A X n`) — `X ^ ⊗ n`, bracketed to
  the left, so that `X ^ ⊗ (n + 1)` is `X ^ ⊗ n ⊗ X` definitionally
  and the recursions below step one factor at a time.
* **The permutation action** (`swapTop`, `insertTop`, `permMor`,
  `permAlg`) — `swapTop` braids the last two factors, `insertTop`
  bubbles the top factor down, `permMor` routes each factor to the
  slot its permutation names, and `permAlg` is the resulting
  representation of the symmetric-group algebra.
* **The tensor power of an endomorphism** (`powHom X g n`) — `g`
  acting on every factor.
* **Cycle-trace tower** (`CycleTraceTower`) — permutation
  representations and tensor-power traces satisfying the cycle
  formula. This is the common input to the categorical and strand
  forms of the factorial obstruction.
* **Single power trace** (`SinglePowerTrace`) — an element with
  nonzero trace whose powers of degree at least two have zero trace.
  A nilpotent with nonzero trace has a positive power of this form;
  its tensor traces separate all permutations, forcing dimension
  at least `n!` at each finite-dimensional level.
* **Categorical trace** (`catTrace`, `catDim`, `ptr`) — close a
  strand into a loop through the pairing of an object with its dual;
  `catDim` is the trace of the identity, and `ptr` closes the last
  factor only, leaving the rest open.
* **Karoubi underlying maps** (`karoubiHomAddHom`,
  `karoubiHomLinearMap`) — the additive and linear maps sending a
  corner morphism to its ambient morphism. `karoubiLinear` supplies
  the shared complex linear structure on every Karoubi completion.
* **Trace criterion** (`isSemisimpleRing_of_trace`,
  `karoubiEnd_isSemisimpleRing_of_trace`) — a nondegenerate trace
  killing nilpotents forces semisimplicity; cyclicity restricts this
  criterion to a Karoubi corner. `isNilpotent_map_of_mul_zero` and
  `karoubiEnd_isNilpotent` transport nilpotence into the ambient ring.
* **Intertwining** (`intertwine_add`, `intertwine_smul`) — addition
  and scalar multiplication preserve an intertwining equation in a
  linear category.
* **Central idempotent expansion** (`eq_sum_shape_e_of_mem_span`) —
  an element in the central span has an expansion in the shape
  idempotents. This supplies both completeness and character splitting.
* **Pair lists** (`edgePairList`, `orientedPairList`) — the endpoint
  pairs of the pendant edges, with membership and no-repetition facts
  shared by the sorting-sign and regrouping arguments in
  `Novel/Coordinates/PairList`. `Common/ListPairs` supplies generic
  flattened-pair indexing; `Common/FinSlots` separates the two slots
  of a finite sum. `sortSign_sq` is the common sorting-sign identity.
* **The block splitting** (`splitPow`, `blockSum`) — the
  reassociation `X ^ ⊗ (p + q) ≅ X ^ ⊗ p ⊗ X ^ ⊗ q` and the
  permutation acting on the two blocks independently.
* **Bounded length** (`LengthLE Y k`) — the subobject order of `Y`
  has no strictly increasing chain of `k + 2` terms; equivalently
  the composition length of `Y` is at most `k`.
* **The odd line** (`OddLine`) — an object squaring to the unit
  whose self-braiding is `−1`; `L.mix p q` is the biproduct of `p`
  copies of the unit and `q` of the line.
* **The free module and the fibre** (`freeMod`, `fibreFun`,
  `gammaAlgebra`) — base change along an algebra object of the
  ind-completion, and the pair `(Hom(𝟙, −), Hom(L, −))` on it,
  which is the super algebra of scalars and the fibre functor over
  it.
* **Splitting** (`IsSplit`, `SplitsOn`) — an object is split by an
  algebra when its free module is a mixed sum; `SplitsOn` says every
  object in the image of a functor is.
* **Ideals of an algebra object** (`IsIdeal`) — a subobject
  absorbing multiplication; an algebra is simple when it has no
  others than the two trivial ones.
* **Countably presented** (`CountablyPresented`) — a countable
  filtered colimit of embedded objects; the property that bounds the
  dimension of the scalars.
* **Statements named as inputs** — `DeligneTheoremStatement`
  (Deligne 2002, Théorème 0.6, carrying Deligne's own hypotheses:
  essentially small, abelian, ℂ-linear, rigid symmetric,
  `End 𝟙 = ℂ`, finitely ⊗-generated, of moderate length growth), of
  which the conclusion is taken in fibre-functor form
  (`DeligneFibreFunctor`) rather than as the ⊗-equivalence with the
  representations of a supergroup, and of that functor only the
  symmetric monoidal ℂ-linear part is consumed, as
  `DelignePackage`.  It is a theorem of this tree
  (`deligne_theorem`), as are `SchurPackage` (`schurPackage`) and
  `EulerianIndependence` (`eulerianIndependence`); nothing is
  assumed.
-/
