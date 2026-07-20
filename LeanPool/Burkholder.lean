/-
Copyright (c) 2026 Daniel Smania. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Smania
-/

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import LeanPool.Burkholder.Majorants
import LeanPool.Burkholder.MartingaleTransforms

/-!
# Burkholder Martingale Transform Inequality

Source: doi:10.1214/aop/1176993220
Authors: Daniel Smania
Status: verified
Main declarations: `MeasureTheory.Lp_Burkholder_inequality_martingaleTransform`
Tags: probability, martingales, burkholder-inequality
MSC: 60G42
-/
