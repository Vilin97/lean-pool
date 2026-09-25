/-
Copyright (c) 2026 Arthur F. Ramos, David Barros Hulak, Ruy J.G.B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.MarshallHall.LERFSolution
public import LeanPool.MarshallHall.MarshallHall
public import LeanPool.MarshallHall.MarshallHall.Completion
public import LeanPool.MarshallHall.MarshallHall.CoreSupport
public import LeanPool.MarshallHall.MarshallHall.FiniteCore
public import LeanPool.MarshallHall.MarshallHall.FreeFactor
public import LeanPool.MarshallHall.MarshallHall.GraphBasis
public import LeanPool.MarshallHall.MarshallHall.Grushko
public import LeanPool.MarshallHall.MarshallHall.GrushkoEdge
public import LeanPool.MarshallHall.MarshallHall.GrushkoFold
public import LeanPool.MarshallHall.MarshallHall.GrushkoFoldStep
public import LeanPool.MarshallHall.MarshallHall.GrushkoFull
public import LeanPool.MarshallHall.MarshallHall.GrushkoGeneral
public import LeanPool.MarshallHall.MarshallHall.GrushkoGraph
public import LeanPool.MarshallHall.MarshallHall.GrushkoInvariant
public import LeanPool.MarshallHall.MarshallHall.GrushkoReduction
public import LeanPool.MarshallHall.MarshallHall.GrushkoReductionChain
public import LeanPool.MarshallHall.MarshallHall.GrushkoRemove
public import LeanPool.MarshallHall.MarshallHall.GrushkoRose
public import LeanPool.MarshallHall.MarshallHall.GrushkoUnfold
public import LeanPool.MarshallHall.MarshallHall.GrushkoUnsafe
public import LeanPool.MarshallHall.MarshallHall.Hall
public import LeanPool.MarshallHall.MarshallHall.PartialAction
public import LeanPool.MarshallHall.MarshallHall.Separation
public import LeanPool.MarshallHall.Solution


/-!
# Marshall Hall's theorem through finite cores

Source: url:https://github.com/arthur742ramos/marshallhalltheorem
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
Status: verified
Main declarations: `MarshallHall.marshallHall`, `MarshallHall.rank_freeProduct_eq_add`
Tags: group-theory
MSC: 20E07, 20F65, 05C25
-/

@[expose] public section
