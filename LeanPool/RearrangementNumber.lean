/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/

import LeanPool.RearrangementNumber.NonMRR.BlockAnalysis
import LeanPool.RearrangementNumber.NonMRR.Bounding
import LeanPool.RearrangementNumber.NonMRR.Catalogue
import LeanPool.RearrangementNumber.NonMRR.Category
import LeanPool.RearrangementNumber.NonMRR.CategoryBlocks
import LeanPool.RearrangementNumber.NonMRR.CategoryBound
import LeanPool.RearrangementNumber.NonMRR.CategoryReduction
import LeanPool.RearrangementNumber.NonMRR.CategoryTransfer
import LeanPool.RearrangementNumber.NonMRR.Construction
import LeanPool.RearrangementNumber.NonMRR.FiniteAnalytic
import LeanPool.RearrangementNumber.NonMRR.FiniteEmbedding
import LeanPool.RearrangementNumber.NonMRR.FiniteVectors
import LeanPool.RearrangementNumber.NonMRR.GapBounding
import LeanPool.RearrangementNumber.NonMRR.LowerBound
import LeanPool.RearrangementNumber.NonMRR.Main
import LeanPool.RearrangementNumber.NonMRR.Morphism
import LeanPool.RearrangementNumber.NonMRR.Padding
import LeanPool.RearrangementNumber.NonMRR.PermutationBounds
import LeanPool.RearrangementNumber.NonMRR.Relations
import LeanPool.RearrangementNumber.NonMRR.Riemann
import LeanPool.RearrangementNumber.NonMRR.RiemannBaire
import LeanPool.RearrangementNumber.NonMRR.Selection
import LeanPool.RearrangementNumber.NonMRR.Series
import LeanPool.RearrangementNumber.NonMRR.SlalomBound
import LeanPool.RearrangementNumber.NonMRR.SlalomCoding
import LeanPool.RearrangementNumber.NonMRR.Slaloms
import LeanPool.RearrangementNumber.NonMRR.Walsh
import LeanPool.RearrangementNumber.NonMRR
import LeanPool.RearrangementNumber.Solution

/-!
# The nonmeagre lower bound for the rearrangement number

Source: url:https://github.com/vo-rodrigues/rr-equals-nonmeager-paper
Authors: Vinicius de Oliveira Rodrigues
Status: verified
Main declarations: `NonMRR.nonM_le_rr`
Tags: set-theory, cardinal-characteristics, series
MSC: 03E17, 40A05
-/
