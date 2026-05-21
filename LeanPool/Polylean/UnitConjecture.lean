/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import LeanPool.Polylean.UnitConjecture.TorsionFree
import LeanPool.Polylean.UnitConjecture.GroupRing
import LeanPool.Polylean.UnitConjecture.GardamTheorem

/-!
# Polylean Unit Conjecture infrastructure

This library contains the verified infrastructure from the Polylean formalization around
Gardam's [disproof](https://arxiv.org/abs/2102.11818) of the Kaplansky Unit Conjecture.


## Imported Results

Gardam proved that for a group `P` (the *Promislow* or *Hantzsche-Wendt* group), we have the
following:

* `P` is torsion free; this is proved in [`TorsionFree.lean`](UnitConjecture/TorsionFree.html)
* `𝔽₂[P]` has a non-trivial unit, so Kaplansky's Unit Conjecture is false;
  this is proved in [`GardamTheorem.lean`](UnitConjecture/GardamTheorem.html).

The imported code constructs `P`, constructs group rings, and proves the required algebraic
properties.

## Constructing the group `P`

The group `P` is a so called _Metabelian Group_, an extension of an abelian group by an abelian
group.

* In the file [`GardamGroup.lean`](UnitConjecture/GardamGroup.html), the specific construction of
  `P` is given using the general construction of metabelian groups.
* In the file [`MetabelianGroup.lean`](UnitConjecture/MetabelianGroup.html), metabelian groups are
  constructed based on appropriate data, and proved to be groups.
* The data for a metabelian group includes a _group action_ and a _cocycle_. These are defined and
  their basic properties proved in [`Cocycle.lean`](UnitConjecture/Cocycle.html).

## Constructing group rings

A group ring $K[G]$ is the free module on $K$ with basis elements of a group $G$ with a natural
ring structure.

* Free modules are constructed in [`FreeModule.lean`](UnitConjecture/FreeModule.html) with
  properties proved. This crucially includes decidable equality of elements, assuming decidable
  equality for $G$ and $R$.
* The Group Ring structure is defined in [`GroupRing.lean`](UnitConjecture/GroupRing.html) and
  shown to give a ring.

## Proofs and Definitions by Computation and Enumeration

We set things up to use typeclasses to deduce decidable equality, both by finite enumeration and by
checking equality on a basis for finitely generated abelian groups.

* In [`EnumDecide.lean`](UnitConjecture/EnumDecide.html) we set up the typeclasses for deducing
  decidable equality, and prove the basic cases.
* In [`AddFreeGroup.lean`](UnitConjecture/AddFreeGroup.html) we define bases of free abelian groups
  via a universal property, show that products of $\mathbb{Z}$ have bases, show that homomorphisms
  can be defined by giving functions on a basis, and show that we have decidable equality for
  homomorphisms on finitely generated free abelian groups.
-/
