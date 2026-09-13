/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/
module

public import LeanPool.Chudnovsky.Basic
public import LeanPool.Chudnovsky.Chudnovsky
public import LeanPool.Chudnovsky.Clausen
public import LeanPool.Chudnovsky.Coefficients
public import LeanPool.Chudnovsky.ComplexMult
public import LeanPool.Chudnovsky.DivisionValues
public import LeanPool.Chudnovsky.Estimates
public import LeanPool.Chudnovsky.Fourier
public import LeanPool.Chudnovsky.Kummer
public import LeanPool.Chudnovsky.Lattices
public import LeanPool.Chudnovsky.Liouville
public import LeanPool.Chudnovsky.MainTheorem
public import LeanPool.Chudnovsky.Numerics
public import LeanPool.Chudnovsky.PicardFuchs
public import LeanPool.Chudnovsky.Quasiperiods
public import LeanPool.Chudnovsky.Ramanujan
public import LeanPool.Chudnovsky.SigmaZeta
public import LeanPool.Chudnovsky.SingularModuli
public import LeanPool.Chudnovsky.WeierstrassMore
import Mathlib.Tactic.NormNum.Prime

/-!
# A Detailed Proof of the Chudnovsky Formula

Source: arxiv:1809.00533
Authors: Xuanji Li
Status: verified
Main declarations: `Chudnovsky.chudnovskySum_eq_pi_inv`
Tags: number-theory, pi, chudnovsky, modular-forms, complex-multiplication
MSC: 11Y60, 11F03, 33C05
-/

@[expose] public section
