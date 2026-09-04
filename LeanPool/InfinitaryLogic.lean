/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Admissible.HF
import LeanPool.InfinitaryLogic.Admissible.Family
import LeanPool.InfinitaryLogic.Admissible.Fragment.Honest
import LeanPool.InfinitaryLogic.Conditional.GandyHarrington
import LeanPool.InfinitaryLogic.Conditional.MorleyHanfSchemaDischarge
import LeanPool.InfinitaryLogic.Descriptive.IsomorphismBorel
import LeanPool.InfinitaryLogic.Descriptive.LopezEscobar
import LeanPool.InfinitaryLogic.Descriptive.WellOrderNonBorel
import LeanPool.InfinitaryLogic.Karp.CarrierTheorem
import LeanPool.InfinitaryLogic.Methods.Henkin.ModelExistence
import LeanPool.InfinitaryLogic.Methods.Interpolation.CraigArbitrary
import LeanPool.InfinitaryLogic.Methods.Interpolation.LyndonArbitrary
import LeanPool.InfinitaryLogic.Methods.Interpolation.MalitzSublanguage
import LeanPool.InfinitaryLogic.Methods.UniformCollapse
import LeanPool.InfinitaryLogic.Methods.WellOrdering.GraphTranslation
import LeanPool.InfinitaryLogic.ModelTheory.HanfSpectrum.BethLadder
import LeanPool.InfinitaryLogic.ModelTheory.MorleyCounting
import LeanPool.InfinitaryLogic.ModelTheory.ScottCompletion
import LeanPool.InfinitaryLogic.Scott.Rank
import LeanPool.InfinitaryLogic.Scott.RefinementCount
import LeanPool.InfinitaryLogic.Scott.Sentence

/-!
# Infinitary Logic

The proved headline surface for infinitary logic, including Scott analysis, Karp's theorem,
Morley–Hanf theory, interpolation, and descriptive-set-theoretic results about model classes.
-/
