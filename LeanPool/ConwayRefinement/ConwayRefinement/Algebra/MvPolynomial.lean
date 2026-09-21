/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.BaseChange
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.Components
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.ComponentsSpan
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.Expansion
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.FinitePartDecomposition
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.FinitePartErasure
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.FinitePartVars
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.GCDMonoid
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.LimitOrdinalContradiction
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.MapWeight
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.OrdinalDerivation
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.OrdinalExpansion
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.RemainderBound
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.Syzygy
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.TermDegree
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.WeightedTotalDegree

/-! Supporting modules for Conway refinement for omnific integers. -/
