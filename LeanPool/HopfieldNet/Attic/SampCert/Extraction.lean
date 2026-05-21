/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.Extractor.Export
import LeanPool.HopfieldNet.SampCert.Extractor.Align
import LeanPool.HopfieldNet.SampCert.Samplers.Uniform.Code
import LeanPool.HopfieldNet.SampCert.Samplers.Bernoulli.Code
import LeanPool.HopfieldNet.SampCert.Samplers.BernoulliNegativeExponential.Code
import LeanPool.HopfieldNet.SampCert.Samplers.Laplace.Code
import LeanPool.HopfieldNet.SampCert.Samplers.Gaussian.Code

open SLang

/-! Extractor

Attributes which trigger extraction.

The names in this file are protected:
the extractor will not work if these names are changed.a

Additionally, the following names are protected:
 - ``UniformPowerOfTwoSample``
-/

attribute [export_dafny] UniformSample
attribute [export_dafny] BernoulliSample
attribute [export_dafny] BernoulliExpNegSampleUnitLoop
attribute [export_dafny] BernoulliExpNegSampleUnitAux
attribute [export_dafny] BernoulliExpNegSampleUnit
attribute [export_dafny] BernoulliExpNegSampleGenLoop
attribute [export_dafny] BernoulliExpNegSample
attribute [export_dafny] DiscreteLaplaceSampleLoopIn1Aux
attribute [export_dafny] DiscreteLaplaceSampleLoopIn1
attribute [export_dafny] DiscreteLaplaceSampleLoopIn2Aux
attribute [export_dafny] DiscreteLaplaceSampleLoopIn2
attribute [export_dafny] DiscreteLaplaceSampleLoop
attribute [export_dafny] DiscreteLaplaceSampleLoop'
attribute [export_dafny] DiscreteLaplaceSample
attribute [export_dafny] DiscreteLaplaceSampleOptimized
attribute [export_dafny] DiscreteLaplaceSampleMixed
attribute [export_dafny] DiscreteGaussianSampleLoop
attribute [export_dafny] DiscreteGaussianSample
