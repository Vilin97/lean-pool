/-
Copyright (c) 2026 Hyeon Seung-Hyeon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hyeon Seung-Hyeon
-/

import LeanPool.MassFormula.Convergence
import LeanPool.MassFormula.Defs
import LeanPool.MassFormula.Discriminant
import LeanPool.MassFormula.EisensteinMonogenic
import LeanPool.MassFormula.Finiteness
import LeanPool.MassFormula.First
import LeanPool.MassFormula.HaarScaling
import LeanPool.MassFormula.Orbit
import LeanPool.MassFormula.RootLifting
import LeanPool.MassFormula.Second
import LeanPool.MassFormula.Tame
import LeanPool.MassFormula.UniformizerParam

/-!
# Serre's mass formula for totally ramified local-field extensions

Source: url:https://gallica.bnf.fr/ark:/12148/bpt6k6234149b/f323.item
Authors: Hyeon Seung-Hyeon
Status: verified
Main declarations: `MassFormula.tsum_one_div_q_pow_c`
Tags: number-theory, local-fields, ramification, discriminants, haar-measure
MSC: 11S15, 11S05
-/
