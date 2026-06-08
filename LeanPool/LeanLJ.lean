/-
Copyright (c) 2026 Colin Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Jones
-/
import LeanPool.LeanLJ.Instance
import LeanPool.LeanLJ.Function
import LeanPool.LeanLJ.LennardJonesProof
import LeanPool.LeanLJ.LongRangeCorrection
import LeanPool.LeanLJ.MinImageDistancePeriodicBC
import LeanPool.LeanLJ.PairsProof
import LeanPool.LeanLJ.CSVParser

/-!
# LeanLJ: a verified Lennard-Jones potential and energy framework

Source: arxiv:2505.09095, url:https://github.com/ATOMSLab/LeanLJ
Authors: Colin Jones
Status: verified
Main declarations: `LeanLJ.long_range_correction_equality`, `LeanLJ.Lj_eq`
Tags: physics, molecular-dynamics, lennard-jones, formal-verification
MSC: 82-08, 70F10
-/
