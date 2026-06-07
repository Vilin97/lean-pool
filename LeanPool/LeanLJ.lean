/-
Copyright (c) 2026 Colin Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Jones
-/
import LeanPool.LeanLJ.Instance
import LeanPool.LeanLJ.Function
import LeanPool.LeanLJ.Lennard_Jones_proof
import LeanPool.LeanLJ.LongRangeCorrection
import LeanPool.LeanLJ.MinImageDistance_PeriodicBC
import LeanPool.LeanLJ.Pairs_Proof
import LeanPool.LeanLJ.CSVParser

/-!
# LeanLJ: a verified Lennard-Jones potential and energy framework

Source: arxiv:2505.09095
Authors: Colin Jones
Status: verified
Main declarations: `LeanLJ.long_range_correction_equality`, `LeanLJ.Lj_eq`, `LeanLJ.ljp_differentiable`, `minImageDistance_real_self`, `pairs_length_eq`
Tags: physics, molecular-dynamics, lennard-jones, formal-verification
MSC: 82-08, 70F10
-/
