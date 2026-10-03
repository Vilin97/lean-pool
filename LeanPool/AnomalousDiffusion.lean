/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/

module
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FullTheorem.HolderTimeL2Le
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FullTheorem.AnomalousDissipationFull
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FullTheorem.LebronStep
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FullTheorem.IsTransportWeakSolution
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FullTheorem.IsHolderTimeL2
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.LatticeShift
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.UnitCube
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.AnomalousDissipation
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.TimeCube
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.GradNormSq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsPeriodicH1With
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.L2NormSq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsWeakSolution
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsContinuousIntoHolder
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsWeakSolutionGrad
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceGrad
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsPeriodicH1
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsHolderClass
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsPeriodicH1WithExistsH1Function
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsTestFunction
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.WeakWellposed
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsDivFree
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsZ2Periodic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceTimeGradNormSq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Gamma
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.IndIcc
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Ingredients
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.ZetaMK
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Delta
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.XiMK
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Nstar
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.ScaledCutoff
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.LIdx
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.HatZetaML
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Psi
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.HatXiML
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.TauP
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Epsilon
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.ShiftCutoff
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Q
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Psi0
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Nonempty
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.TauPP
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.A
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Tau
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Flow.ExistsUniqueFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Flow.IsFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.Flux
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.PermissibleSet
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.KappaAt
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.IsCorrectorSol
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.ChiM
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.CorrTime
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.LRecurse
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.SpaceAvg
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.QMNRChar
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.KhomScalar
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.PsiM
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.GradMatrix
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.QMNR
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.SpaceAvgMat
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.JHat
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.TimeAvgMat
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.ChiMK
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.LMN
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.ChiMKIsUniqueSolution
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.KhomEqScalar
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.PermittedInterval
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.ZetaProd
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.Khom
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.JMN
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.SpaceLap
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.UShear
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.KMat
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.FluxIntegrand
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.SigmaMat
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.Flow
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowIsFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowInvRightInverse
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowInvLeftInverse
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowUnique
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowInv
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.MTheta0
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.MTheta0IsLeast
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.ChiTilde
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IndyStepDown
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.Jcut
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.Amnr
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsThetaAnalytic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.ClassicalWellposed
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.Hm
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.KappaSeqPred
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.SMat
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.VecDiv
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsTIterates
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.AdvDiffOp
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsClassicalSol
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.Ansatz
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.Hmr
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.TForcing
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.KappaSeq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.BigBound
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.FlowGrad
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.XFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.XFlowInv
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.HMinusOneNorm
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.IsAdmissibleStream
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamVel
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.NextStreamTerm
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.NextStreamAdmissible
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.BarNorm
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.LimitFieldRegular
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.NextStreamSummable
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.IsStreamSeqUnique
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.IsStreamSeq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamVelContinuous
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.ExistsIsStreamSeq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.IsStreamSeqAdmPred
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamVelLipschitz
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.NextStream

/-!
# Anomalous diffusion by fractal homogenization

Source: arxiv:2305.05048, url:https://github.com/scottnarmstrong/AVAnomalousDiffusion/tree/fad71d10bff031522cc598a37770238248186964
Authors: Scott Armstrong, Vlad Vicol
Status: verified
Main declarations: `AVenhance.anomalous_dissipation_full`
Tags: anomalous-dissipation, homogenization, advection-diffusion
MSC: 35B27, 35Q35, 76F30
-/

/-!
# Anomalous diffusion by fractal homogenization

Complete public theorem surface of the Armstrong–Vicol formalization, including weak
well-posedness, construction and homogenization estimates, anomalous dissipation, uniform
time regularity, and two different vanishing-diffusivity limits for one drift.

Adapted from https://github.com/scottnarmstrong/AVAnomalousDiffusion at commit
`fad71d10bff031522cc598a37770238248186964`, released on 2026-10-02 under Apache-2.0.
The Sobolev and ambient-space support was adapted upstream from Scott Armstrong and
Tuomo Kuusi's CoarseGraining project at commit `c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
The proofs were produced primarily by AI under the mathematical supervision of the authors.
-/
