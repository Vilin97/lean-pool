/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import LeanPool.OrdvecFormalization.FiniteExperiment
import LeanPool.OrdvecFormalization.FiniteQuotientSearch
import LeanPool.OrdvecFormalization.QuotientConstraints
import LeanPool.OrdvecFormalization.FiniteQuotientImage
import LeanPool.OrdvecFormalization.QuotientKernel
import LeanPool.OrdvecFormalization.FiniteFiberTopology
import LeanPool.OrdvecFormalization.FiniteProductQuotient
import LeanPool.OrdvecFormalization.FinitePairQuotient
import LeanPool.OrdvecFormalization.QuotientRefinementKernel
import LeanPool.OrdvecFormalization.FiniteObservationWindow
import LeanPool.OrdvecFormalization.ScoreMarginQuotient
import LeanPool.OrdvecFormalization.ProfileStability
import LeanPool.OrdvecFormalization.FiniteBayesRisk
import LeanPool.OrdvecFormalization.OrdinalSufficiency
import LeanPool.OrdvecFormalization.CalibratedEvidence
import LeanPool.OrdvecFormalization.OverlapSufficiency
import LeanPool.OrdvecFormalization.CanonicalTilt
import LeanPool.OrdvecFormalization.OverlapBayesOptimal
import LeanPool.OrdvecFormalization.BitmapIncidence
import LeanPool.OrdvecFormalization.BitmapCalibration
import LeanPool.OrdvecFormalization.BitmapNull
import LeanPool.OrdvecFormalization.BitmapSymmetry
import LeanPool.OrdvecFormalization.OverlapNull
import LeanPool.OrdvecFormalization.Examples

/-!
# OrdVec bitmap overlap formalization

Source: url:https://github.com/Fieldnote-Echo/ordvec-formalization
Authors: Nelson Spence
Status: verified
Main declarations: `OrdvecFormalization.uniformBitmapOverlapTailOptimal`
Tags: finite-probability, bayes-risk, hypergeometric, quotient-sufficiency, bitmap-overlap
MSC: 62C20, 60C05, 68T99
-/

/-!
# Ordvec Formalization

Finite constant-weight bitmap overlap models, quotient sufficiency, Bayes
threshold optimality, and exact hypergeometric calibration.
-/
