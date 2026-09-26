/-
Copyright (c) 2026 Petr Girg, Petr Nečesal, Martin Dvořák, Jakub Psutka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Petr Girg, Petr Nečesal, Martin Dvořák, Jakub Psutka
-/



module

public import LeanPool.NemytskiiLebesgue.WeakConvergence
public import LeanPool.NemytskiiLebesgue.Continuity
public import LeanPool.NemytskiiLebesgue.Closure
public import LeanPool.NemytskiiLebesgue.RealIso
public import LeanPool.NemytskiiLebesgue.Nemytskii
public import LeanPool.NemytskiiLebesgue.ConverseImplication
public import LeanPool.NemytskiiLebesgue.Frechet
public import LeanPool.NemytskiiLebesgue.Vitali
public import LeanPool.NemytskiiLebesgue.Lipschitz
public import LeanPool.NemytskiiLebesgue.Caratheodory
public import LeanPool.NemytskiiLebesgue.IntegralFunctional

/-!
# Nemytskii operators on Lebesgue spaces

Source: url:https://github.com/madvorak/nemytskii-lebesgue/tree/d276c27a1e3ebbd9eb09f25243b5e9808ca168d7
Authors: Petr Girg, Petr Nečesal, Martin Dvořák, Jakub Psutka
Status: verified
Main declarations: `NemytskiiLebesgue.IsCaratheodory.memLp_nemytskii_volume_iff_growth`
Tags: nonlinear-analysis, nemytskii-operators, lebesgue-spaces, differentiation
MSC: 47H30, 46E30, 47J05
-/
