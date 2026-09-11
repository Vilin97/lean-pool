/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import LeanPool.InfinitaryLogic.Admissible.HF
public import LeanPool.InfinitaryLogic.Admissible.Family
public import LeanPool.InfinitaryLogic.Admissible.Fragment.Honest
public import LeanPool.InfinitaryLogic.Conditional.GandyHarrington
public import LeanPool.InfinitaryLogic.Conditional.MorleyHanfSchemaDischarge
public import LeanPool.InfinitaryLogic.Descriptive.IsomorphismBorel
public import LeanPool.InfinitaryLogic.Descriptive.LopezEscobar
public import LeanPool.InfinitaryLogic.Descriptive.WellOrderNonBorel
public import LeanPool.InfinitaryLogic.Karp.CarrierTheorem
public import LeanPool.InfinitaryLogic.Methods.Henkin.ModelExistence
public import LeanPool.InfinitaryLogic.Methods.Interpolation.CraigArbitrary
public import LeanPool.InfinitaryLogic.Methods.Interpolation.LyndonArbitrary
public import LeanPool.InfinitaryLogic.Methods.Interpolation.MalitzSublanguage
public import LeanPool.InfinitaryLogic.Methods.UniformCollapse
public import LeanPool.InfinitaryLogic.Methods.WellOrdering.GraphTranslation
public import LeanPool.InfinitaryLogic.ModelTheory.HanfSpectrum.BethLadder
public import LeanPool.InfinitaryLogic.ModelTheory.MorleyCounting
public import LeanPool.InfinitaryLogic.ModelTheory.ScottCompletion
public import LeanPool.InfinitaryLogic.Scott.Rank
public import LeanPool.InfinitaryLogic.Scott.RefinementCount
public import LeanPool.InfinitaryLogic.Scott.Sentence
import Mathlib.Data.Sym.Sym2.Init

/-!
# Infinitary logic and countable model theory

Source: url:https://github.com/cameronfreer/infinitary-logic
Authors: Cameron Freer
Status: verified
Main declarations: `FirstOrder.Language.scottSentence_characterizes`
Tags: mathematical-logic, infinitary-logic, model-theory, descriptive-set-theory
MSC: 03C75, 03E15, 03C30
-/

@[expose] public section
