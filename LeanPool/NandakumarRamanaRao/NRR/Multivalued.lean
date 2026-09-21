/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.Multivalued.PhaseInterfaces
import LeanPool.NandakumarRamanaRao.NRR.Multivalued.SignedInterval
import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Nice
import LeanPool.NandakumarRamanaRao.NRR.Multivalued.ZeroSet
import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Operations
import LeanPool.NandakumarRamanaRao.NRR.Multivalued.PerimeterObservable
import LeanPool.NandakumarRamanaRao.NRR.Multivalued.ChildEvaluation
import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Separator.Basic
import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Separator.Complement
import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Separator.Fibers
import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Separator.Distance
import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Separator.SignedDistance
import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Separator.ToNiceMV
import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Separator.ObstructionValue

/-!
# `NRR.Multivalued` — nice multivalued functions and top–bottom separators

Public aggregator for the nice-multivalued-function and top–bottom-separator machinery used in the
Akopyan–Avvakumov–Karasev prime-refinement argument.

`SignedInterval` is `[-1,1]`. A `NiceMV X` is a continuous scalar function on
`X × SignedInterval` with strict opposite signs at the endpoints. Connectedness of the interval
gives a zero in every vertical fiber. The API includes pullback, rescaling, reflection, observable
models, perimeter observables, and simultaneous evaluation on variable-body partition children.

A `TopBottomSeparator X` consists of a closed carrier together with disjoint open lower and upper
regions covering its complement and containing the bottom and top boundaries. Every vertical fiber
meets the carrier. Over a nonempty metric base, signed distance converts such a separator into a
`NiceMV` with exactly the same zero set. Separators and nice multivalued functions both support
continuous pullback.
-/
