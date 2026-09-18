/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/
module

public import LeanPool.Sundogcert.Certificate
public import LeanPool.Sundogcert.Instance
public import LeanPool.Sundogcert.Scaling
public import LeanPool.Sundogcert.Looseness
public import LeanPool.Sundogcert.CertWall
public import LeanPool.Sundogcert.Degradation
public import LeanPool.Sundogcert.CheckCost
public import LeanPool.Sundogcert.RSCertificate
public import LeanPool.Sundogcert.DecodingNPHard
public import LeanPool.Sundogcert.MatchingNPHard
public import LeanPool.Sundogcert.SATNPHard
public import LeanPool.Sundogcert.VarWheel
public import LeanPool.Sundogcert.ClauseGadget
public import LeanPool.Sundogcert.SATReduction
public import LeanPool.Sundogcert.ThreeDMReindex
public import LeanPool.Sundogcert.SATReductionIncidence
public import LeanPool.Sundogcert.SATReductionReverse
public import LeanPool.Sundogcert.SATReductionForward
public import LeanPool.Sundogcert.SATReductionMain

/-!
# Sundog certificates

Source: url:https://github.com/humiliati/sundogcert
Authors: Humiliati
Status: verified
Main declarations: `Sundog.SATReductionMain.sat_iff_decodes`, `Sundog.Certificate.accept_sound`
Tags: complexity, coding-theory, np-hardness
MSC: 68Q17, 94B35
-/

@[expose] public section
