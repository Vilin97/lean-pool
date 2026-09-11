/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import LeanPool.QuasiBorelSpaces.Basic
public import LeanPool.QuasiBorelSpaces.Chain
public import LeanPool.QuasiBorelSpaces.Cont
public import LeanPool.QuasiBorelSpaces.Defs
public import LeanPool.QuasiBorelSpaces.ENNReal
public import LeanPool.QuasiBorelSpaces.Finset
public import LeanPool.QuasiBorelSpaces.FlatReal
public import LeanPool.QuasiBorelSpaces.Functor
public import LeanPool.QuasiBorelSpaces.Hom
public import LeanPool.QuasiBorelSpaces.IsHomDiagonal
public import LeanPool.QuasiBorelSpaces.Lift
public import LeanPool.QuasiBorelSpaces.List
public import LeanPool.QuasiBorelSpaces.MeasureTheory
public import LeanPool.QuasiBorelSpaces.Multiset
public import LeanPool.QuasiBorelSpaces.Nat
public import LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder
public import LeanPool.QuasiBorelSpaces.OmegaHom
public import LeanPool.QuasiBorelSpaces.OmegaQuasiBorelSpace
public import LeanPool.QuasiBorelSpaces.Option
public import LeanPool.QuasiBorelSpaces.Pi
public import LeanPool.QuasiBorelSpaces.PreProbabilityMeasure
public import LeanPool.QuasiBorelSpaces.ProbabilityMeasure
public import LeanPool.QuasiBorelSpaces.Prod
public import LeanPool.QuasiBorelSpaces.Prop
public import LeanPool.QuasiBorelSpaces.Quotient
public import LeanPool.QuasiBorelSpaces.Rose
public import LeanPool.QuasiBorelSpaces.RoseTree
public import LeanPool.QuasiBorelSpaces.SeparatesPoints
public import LeanPool.QuasiBorelSpaces.Sigma
public import LeanPool.QuasiBorelSpaces.Subtype
public import LeanPool.QuasiBorelSpaces.Sum
public import LeanPool.QuasiBorelSpaces.UnitInterval

/-!
# Quasi-Borel Spaces

Source: arxiv:1701.02547, doi:10.1109/LICS.2017.8005137
Authors: Anthony Vandikas, Kiarash Sotoudeh
Status: verified
Main declarations: `QuasiBorelSpace`, `OmegaQuasiBorelSpace`, `QuasiBorelSpace.ProbabilityMeasure`
Tags: probability, category-theory, measure-theory, denotational-semantics
MSC: 60A05, 18C50, 68Q55
-/

@[expose] public section

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
