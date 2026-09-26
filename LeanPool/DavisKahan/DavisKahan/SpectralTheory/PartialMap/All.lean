/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
public import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.PartialMap.BoundedRealization
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.PartialMap.Complexification
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.PartialMap.RealSpectrum
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.PartialMap.UnitaryConjugation

/-! # `DavisKahan/SpectralTheory/PartialMap`

The Davis--Kahan additions to Mathlib's `LinearPMap`: the real resolvent set and
spectrum, coordinatewise complexification, unitary conjugation, and bounded
realization.  Named `PartialMap` until 2026-08-28, after the bundled record
of that name. -/

@[expose] public section
