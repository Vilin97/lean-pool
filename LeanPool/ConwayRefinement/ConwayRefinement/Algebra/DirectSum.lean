/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.GermChainRule
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.GermFinitePartIdeal
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.GermPolynomial
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.GermSuccessorStep
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.GermSyzygy
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.HomogeneousDivisibility
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.HomogeneousPrime
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.InternalGrading
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.LeadingGrade
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.TrailingGrade

/-! Supporting modules for Conway refinement for omnific integers. -/
