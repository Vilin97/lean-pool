/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import LeanPool.QuasiBorelSpaces.Basic
import LeanPool.QuasiBorelSpaces.Chain
import LeanPool.QuasiBorelSpaces.Cont
import LeanPool.QuasiBorelSpaces.Defs
import LeanPool.QuasiBorelSpaces.ENNReal
import LeanPool.QuasiBorelSpaces.Finset
import LeanPool.QuasiBorelSpaces.FlatReal
import LeanPool.QuasiBorelSpaces.Functor
import LeanPool.QuasiBorelSpaces.Hom
import LeanPool.QuasiBorelSpaces.IsHomDiagonal
import LeanPool.QuasiBorelSpaces.Lift
import LeanPool.QuasiBorelSpaces.List
import LeanPool.QuasiBorelSpaces.MeasureTheory
import LeanPool.QuasiBorelSpaces.Multiset
import LeanPool.QuasiBorelSpaces.Nat
import LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder
import LeanPool.QuasiBorelSpaces.OmegaHom
import LeanPool.QuasiBorelSpaces.OmegaQuasiBorelSpace
import LeanPool.QuasiBorelSpaces.Option
import LeanPool.QuasiBorelSpaces.Pi
import LeanPool.QuasiBorelSpaces.PreProbabilityMeasure
import LeanPool.QuasiBorelSpaces.ProbabilityMeasure
import LeanPool.QuasiBorelSpaces.Prod
import LeanPool.QuasiBorelSpaces.Prop
import LeanPool.QuasiBorelSpaces.Quotient
import LeanPool.QuasiBorelSpaces.Rose
import LeanPool.QuasiBorelSpaces.RoseTree
import LeanPool.QuasiBorelSpaces.SeparatesPoints
import LeanPool.QuasiBorelSpaces.Sigma
import LeanPool.QuasiBorelSpaces.Subtype
import LeanPool.QuasiBorelSpaces.Sum
import LeanPool.QuasiBorelSpaces.UnitInterval

/-!
# Quasi-Borel Spaces

Source: url:https://github.com/YellPika/quasi-borel-spaces
Authors: Anthony Vandikas, Kiarash Sotoudeh
Status: verified
Main declarations: `QuasiBorelSpace`, `OmegaQuasiBorelSpace`, `QuasiBorelSpace.ProbabilityMeasure`
Tags: probability, category-theory, measure-theory, denotational-semantics
MSC: 60A05, 18C50, 68Q55
-/

/-!
## Mathematical overview

A formalization of *quasi-Borel spaces* (Heunen, Kammar, Staton, Yang 2017) and
*quasi-Borel pre-domains* (Vákár, Kammar, Staton 2019) in Lean 4. Quasi-Borel
spaces are a convenient category for higher-order probability theory: they
support function spaces while still allowing standard probability-theoretic
constructions.

## Main results

- `QuasiBorelSpace` — definition of a quasi-Borel space as a type together with
  a set of random variables closed under constants, measurable precomposition,
  and gluing.
- `QuasiBorelSpace.IsHom` — morphisms between quasi-Borel spaces.
- `OmegaQuasiBorelSpace` — quasi-Borel spaces enriched with an ω-complete
  partial order structure compatible with the underlying randomness.
- `ProbabilityMeasure` — the probability-measure monad on quasi-Borel spaces,
  obtained by quotienting pre-probability measures by integral equivalence.
-/
