/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/
module

public import LeanPool.FormalizationOfBoundedArithmetic.Algebra
public import LeanPool.FormalizationOfBoundedArithmetic.AxiomSchemes
public import LeanPool.FormalizationOfBoundedArithmetic.BasicSingleSorted
public import LeanPool.FormalizationOfBoundedArithmetic.Complexity
public import LeanPool.FormalizationOfBoundedArithmetic.DisplayedVariables
public import LeanPool.FormalizationOfBoundedArithmetic.IDelta0
public import LeanPool.FormalizationOfBoundedArithmetic.IOPEN
public import LeanPool.FormalizationOfBoundedArithmetic.IsEnum
public import LeanPool.FormalizationOfBoundedArithmetic.LanguagePeano
public import LeanPool.FormalizationOfBoundedArithmetic.LanguageZambella
public import LeanPool.FormalizationOfBoundedArithmetic.MathlibSimps
public import LeanPool.FormalizationOfBoundedArithmetic.Order
public import LeanPool.FormalizationOfBoundedArithmetic.Register
public import LeanPool.FormalizationOfBoundedArithmetic.Semantics
public import LeanPool.FormalizationOfBoundedArithmetic.SimpRules
public import LeanPool.FormalizationOfBoundedArithmetic.Syntax
public import LeanPool.FormalizationOfBoundedArithmetic.V0
public import LeanPool.FormalizationOfBoundedArithmetic.V0StrAddAssoc
public import LeanPool.FormalizationOfBoundedArithmetic.V0StrAddComm
public import LeanPool.FormalizationOfBoundedArithmetic.V0StrSuccAssoc
import Mathlib.Tactic.Positivity.Finset

/-!
# Strengthened V0 Bounded Arithmetic Interfaces

Source: doi:10.1017/CBO9780511676277
Authors: ruplet
Status: verified
Main declarations: `V0Model.ind_strengthened_v0`, `str_add_assoc_strengthened_v0`
Tags: logic, bounded-arithmetic, model-theory, computational-complexity
MSC: 03F30, 03D15
-/

@[expose] public section
