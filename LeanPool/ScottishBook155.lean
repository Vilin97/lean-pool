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

import LeanPool.ScottishBook155.AdjunctionFormula
import LeanPool.ScottishBook155.AdjunctionRetraction
import LeanPool.ScottishBook155.AdjunctionRetractiveEnvelope
import LeanPool.ScottishBook155.AttachmentMap
import LeanPool.ScottishBook155.BentSeedStage
import LeanPool.ScottishBook155.BookkeepingSchedule
import LeanPool.ScottishBook155.CardinalControl
import LeanPool.ScottishBook155.Claim14
import LeanPool.ScottishBook155.CoherentBiSystem
import LeanPool.ScottishBook155.CoherentLimit
import LeanPool.ScottishBook155.CoherentRetractionLimit
import LeanPool.ScottishBook155.CollapsedQuotient
import LeanPool.ScottishBook155.CombinedEmbedding
import LeanPool.ScottishBook155.CompletedLimitMap
import LeanPool.ScottishBook155.DenseSequenceCardinal
import LeanPool.ScottishBook155.DirectedLimitStage
import LeanPool.ScottishBook155.EnumeratedStage
import LeanPool.ScottishBook155.FinalAssembly
import LeanPool.ScottishBook155.FinalChainAssembly
import LeanPool.ScottishBook155.InitialSegmentOrder
import LeanPool.ScottishBook155.KuratowskiCoordinate
import LeanPool.ScottishBook155.LimitCardinal
import LeanPool.ScottishBook155.LimitStageCore
import LeanPool.ScottishBook155.LpTruncation
import LeanPool.ScottishBook155.NormedDirectLimit
import LeanPool.ScottishBook155.Paper1
import LeanPool.ScottishBook155.PrefixGlue
import LeanPool.ScottishBook155.Preliminaries
import LeanPool.ScottishBook155.ProtectedChain
import LeanPool.ScottishBook155.ProtectedChainCore
import LeanPool.ScottishBook155.ProtectedChainLimit
import LeanPool.ScottishBook155.ProtectedChainLimitAppend
import LeanPool.ScottishBook155.ProtectedChainReindex
import LeanPool.ScottishBook155.ProtectedChainSingleton
import LeanPool.ScottishBook155.ProtectedChainSuccessor
import LeanPool.ScottishBook155.ProtectedChainTransport
import LeanPool.ScottishBook155.ProtectedEnvelope
import LeanPool.ScottishBook155.ProtectedExtension
import LeanPool.ScottishBook155.ProtectedExtensionAssembly
import LeanPool.ScottishBook155.ProtectedExtensionTheorem
import LeanPool.ScottishBook155.RecursionCardinal
import LeanPool.ScottishBook155.RegularDirectLimit
import LeanPool.ScottishBook155.RelativeEnvelope
import LeanPool.ScottishBook155.RetractiveEnvelope
import LeanPool.ScottishBook155.ScheduledSuccessor
import LeanPool.ScottishBook155.Solution
import LeanPool.ScottishBook155.StageSystem
import LeanPool.ScottishBook155.SuccessorCardinal
import LeanPool.ScottishBook155.TransfiniteConstruction
import LeanPool.ScottishBook155.TransfinitePrefix

/-!
# A counterexample to Scottish Book Problem 155

Source: url:https://github.com/yoshito-ishiki-math/lean-scottish-book-155
Authors: Yoshito Ishiki
Status: verified
Main declarations: `ScottishBook155.claim14`
Tags: functional-analysis
MSC: 46B20, 54E40
-/
