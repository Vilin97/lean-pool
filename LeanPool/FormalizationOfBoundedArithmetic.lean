/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/

import LeanPool.FormalizationOfBoundedArithmetic.Algebra
import LeanPool.FormalizationOfBoundedArithmetic.AxiomSchemes
import LeanPool.FormalizationOfBoundedArithmetic.BasicSingleSorted
import LeanPool.FormalizationOfBoundedArithmetic.Complexity
import LeanPool.FormalizationOfBoundedArithmetic.DisplayedVariables
import LeanPool.FormalizationOfBoundedArithmetic.IDelta0
import LeanPool.FormalizationOfBoundedArithmetic.IOPEN
import LeanPool.FormalizationOfBoundedArithmetic.IsEnum
import LeanPool.FormalizationOfBoundedArithmetic.LanguagePeano
import LeanPool.FormalizationOfBoundedArithmetic.LanguageZambella
import LeanPool.FormalizationOfBoundedArithmetic.MathlibSimps
import LeanPool.FormalizationOfBoundedArithmetic.Order
import LeanPool.FormalizationOfBoundedArithmetic.Register
import LeanPool.FormalizationOfBoundedArithmetic.Semantics
import LeanPool.FormalizationOfBoundedArithmetic.SimpRules
import LeanPool.FormalizationOfBoundedArithmetic.Syntax
import LeanPool.FormalizationOfBoundedArithmetic.V0
import LeanPool.FormalizationOfBoundedArithmetic.V0StrAddAssoc
import LeanPool.FormalizationOfBoundedArithmetic.V0StrAddComm
import LeanPool.FormalizationOfBoundedArithmetic.V0StrSuccAssoc

/-!
# Strengthened V0 Bounded Arithmetic Interfaces

Source: doi:10.1017/CBO9780511676277
Authors: ruplet
Status: verified
Main declarations: `V0Model.ind_strengthened_v0`, `str_add_assoc_strengthened_v0`
Tags: logic, bounded-arithmetic, model-theory, computational-complexity
MSC: 03F30, 03D15
-/
