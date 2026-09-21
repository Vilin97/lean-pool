/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.MarshallHall.LERFSolution
import LeanPool.MarshallHall.MarshallHall
import LeanPool.MarshallHall.MarshallHall.Completion
import LeanPool.MarshallHall.MarshallHall.CoreSupport
import LeanPool.MarshallHall.MarshallHall.FiniteCore
import LeanPool.MarshallHall.MarshallHall.FreeFactor
import LeanPool.MarshallHall.MarshallHall.GraphBasis
import LeanPool.MarshallHall.MarshallHall.Grushko
import LeanPool.MarshallHall.MarshallHall.GrushkoEdge
import LeanPool.MarshallHall.MarshallHall.GrushkoFold
import LeanPool.MarshallHall.MarshallHall.GrushkoFoldStep
import LeanPool.MarshallHall.MarshallHall.GrushkoFull
import LeanPool.MarshallHall.MarshallHall.GrushkoGeneral
import LeanPool.MarshallHall.MarshallHall.GrushkoGraph
import LeanPool.MarshallHall.MarshallHall.GrushkoInvariant
import LeanPool.MarshallHall.MarshallHall.GrushkoReduction
import LeanPool.MarshallHall.MarshallHall.GrushkoReductionChain
import LeanPool.MarshallHall.MarshallHall.GrushkoRemove
import LeanPool.MarshallHall.MarshallHall.GrushkoRose
import LeanPool.MarshallHall.MarshallHall.GrushkoUnfold
import LeanPool.MarshallHall.MarshallHall.GrushkoUnsafe
import LeanPool.MarshallHall.MarshallHall.Hall
import LeanPool.MarshallHall.MarshallHall.PartialAction
import LeanPool.MarshallHall.MarshallHall.Separation
import LeanPool.MarshallHall.Solution

/-!
# Marshall Hall's theorem through finite cores

Source: url:https://github.com/arthur742ramos/marshallhalltheorem
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
Status: verified
Main declarations: `MarshallHall.marshallHall`, `LERFChallenge.freeGroup_finite_permutation_separator`, `MarshallHall.rank_freeProduct_eq_add`
Tags: group-theory
MSC: 20E07, 20F65, 05C25
-/
