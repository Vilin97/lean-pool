/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.Basic
import LeanPool.Chudnovsky.Chudnovsky
import LeanPool.Chudnovsky.Clausen
import LeanPool.Chudnovsky.Coefficients
import LeanPool.Chudnovsky.ComplexMult
import LeanPool.Chudnovsky.DivisionValues
import LeanPool.Chudnovsky.Estimates
import LeanPool.Chudnovsky.Fourier
import LeanPool.Chudnovsky.Kummer
import LeanPool.Chudnovsky.Lattices
import LeanPool.Chudnovsky.Liouville
import LeanPool.Chudnovsky.MainTheorem
import LeanPool.Chudnovsky.Numerics
import LeanPool.Chudnovsky.PicardFuchs
import LeanPool.Chudnovsky.Quasiperiods
import LeanPool.Chudnovsky.Ramanujan
import LeanPool.Chudnovsky.SigmaZeta
import LeanPool.Chudnovsky.SingularModuli
import LeanPool.Chudnovsky.WeierstrassMore

/-!
# A Detailed Proof of the Chudnovsky Formula

Source: arxiv:1809.00533
Authors: Xuanji Li
Status: verified
Main declarations: `Chudnovsky.chudnovskySum_eq_pi_inv`
Tags: number-theory, pi, chudnovsky, modular-forms, complex-multiplication
MSC: 11Y60, 11F03, 33C05
-/
