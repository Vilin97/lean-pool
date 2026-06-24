/-
Copyright (c) 2026 Humiliati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Humiliati
-/

import LeanPool.Sundogcert.Basic
import LeanPool.Sundogcert.Certificate
import LeanPool.Sundogcert.Instance
import LeanPool.Sundogcert.Scaling
import LeanPool.Sundogcert.Looseness
import LeanPool.Sundogcert.CertWall
import LeanPool.Sundogcert.Degradation
import LeanPool.Sundogcert.CheckCost
import LeanPool.Sundogcert.ShadowDecay
import LeanPool.Sundogcert.ShadowDecayGeneral
import LeanPool.Sundogcert.ShadowDecayCauchy
import LeanPool.Sundogcert.HaloGeometry
import LeanPool.Sundogcert.FaradayAB
import LeanPool.Sundogcert.SortingCert
import LeanPool.Sundogcert.RSCertificate
import LeanPool.Sundogcert.DecodingNPHard
import LeanPool.Sundogcert.AxiomAudit
import LeanPool.Sundogcert.ShadowDecayLattice
import LeanPool.Sundogcert.AuditCost
import LeanPool.Sundogcert.MatchingNPHard
import LeanPool.Sundogcert.SATNPHard
import LeanPool.Sundogcert.VarWheel
import LeanPool.Sundogcert.ClauseGadget
import LeanPool.Sundogcert.SATReduction
import LeanPool.Sundogcert.ThreeDMReindex
import LeanPool.Sundogcert.SATReductionIncidence
import LeanPool.Sundogcert.SATReductionReverse
import LeanPool.Sundogcert.SATReductionForward
import LeanPool.Sundogcert.SATReductionMain

/-!
# Sundog certificates

Source: url:https://github.com/humiliati/sundogcert
Authors: Humiliati
Status: verified
Main declarations: `Sundog.SATReductionMain.sat_iff_decodes`, `Sundog.Certificate.accept_sound`
Tags: complexity, coding-theory, np-hardness
MSC: 68Q17, 94B35
-/
