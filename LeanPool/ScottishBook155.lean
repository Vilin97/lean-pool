/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/

/-
Upstream license (retained verbatim):

MIT License

Copyright (c) 2026 Yoshito Ishiki

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-/

module

public import LeanPool.ScottishBook155.AdjunctionFormula
public import LeanPool.ScottishBook155.AdjunctionRetraction
public import LeanPool.ScottishBook155.AdjunctionRetractiveEnvelope
public import LeanPool.ScottishBook155.AttachmentMap
public import LeanPool.ScottishBook155.BentSeedStage
public import LeanPool.ScottishBook155.BookkeepingSchedule
public import LeanPool.ScottishBook155.CardinalControl
public import LeanPool.ScottishBook155.Claim14
public import LeanPool.ScottishBook155.CoherentBiSystem
public import LeanPool.ScottishBook155.CoherentRetractionLimit
public import LeanPool.ScottishBook155.CollapsedQuotient
public import LeanPool.ScottishBook155.CombinedEmbedding
public import LeanPool.ScottishBook155.CompletedLimitMap
public import LeanPool.ScottishBook155.DenseSequenceCardinal
public import LeanPool.ScottishBook155.DirectedLimitStage
public import LeanPool.ScottishBook155.FinalAssembly
public import LeanPool.ScottishBook155.FinalChainAssembly
public import LeanPool.ScottishBook155.InitialSegmentOrder
public import LeanPool.ScottishBook155.KuratowskiCoordinate
public import LeanPool.ScottishBook155.LimitCardinal
public import LeanPool.ScottishBook155.LimitStageCore
public import LeanPool.ScottishBook155.LpTruncation
public import LeanPool.ScottishBook155.NormedDirectLimit
public import LeanPool.ScottishBook155.Paper1
public import LeanPool.ScottishBook155.PrefixGlue
public import LeanPool.ScottishBook155.Preliminaries
public import LeanPool.ScottishBook155.ProtectedChain
public import LeanPool.ScottishBook155.ProtectedChainCore
public import LeanPool.ScottishBook155.ProtectedChainLimit
public import LeanPool.ScottishBook155.ProtectedChainLimitAppend
public import LeanPool.ScottishBook155.ProtectedChainReindex
public import LeanPool.ScottishBook155.ProtectedChainSingleton
public import LeanPool.ScottishBook155.ProtectedChainSuccessor
public import LeanPool.ScottishBook155.ProtectedChainTransport
public import LeanPool.ScottishBook155.ProtectedEnvelope
public import LeanPool.ScottishBook155.ProtectedExtension
public import LeanPool.ScottishBook155.ProtectedExtensionAssembly
public import LeanPool.ScottishBook155.ProtectedExtensionTheorem
public import LeanPool.ScottishBook155.RecursionCardinal
public import LeanPool.ScottishBook155.RegularDirectLimit
public import LeanPool.ScottishBook155.RelativeEnvelope
public import LeanPool.ScottishBook155.RetractiveEnvelope
public import LeanPool.ScottishBook155.ScheduledSuccessor
public import LeanPool.ScottishBook155.Solution
public import LeanPool.ScottishBook155.StageSystem
public import LeanPool.ScottishBook155.SuccessorCardinal
public import LeanPool.ScottishBook155.TransfiniteConstruction
public import LeanPool.ScottishBook155.TransfinitePrefix


/-!
# A counterexample to Scottish Book Problem 155

Source: url:https://github.com/yoshito-ishiki-math/lean-scottish-book-155
Authors: Yoshito Ishiki
Status: verified
Main declarations: `ScottishBook155.claim14`
Tags: functional-analysis
MSC: 46B20, 54E40
-/
