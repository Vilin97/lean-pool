/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/

import LeanPool.PhaseRetrieval.Constant
import LeanPool.PhaseRetrieval.DimdPoly

/-!
# Stable phase retrieval for Hermite-Fock expansions

Source: url:https://github.com/susannabertolini/PhaseRetrieval
Authors: Susanna Bertolini, Jaume de Dios Pont
Status: verified
Main declarations: `DimdPolyShowcaseChallenge.stable_phase_retrieval`
Tags: phase-retrieval, hermite-fock, gaussian-measure, complex-analysis
MSC: 42C05, 46E22, 94A12
-/

/-!
## References

Stable phase retrieval is the problem of reconstructing a signal from the
magnitudes of its frame/expansion coefficients up to a single global phase,
with a uniform stability constant under noise. For the named problem and its
stability theory see R. Balan, P. Casazza, and D. Edidin, *On signal
reconstruction without phase*, Appl. Comput. Harmon. Anal. 20 (2006), 345-356
(doi:10.1016/j.acha.2005.07.001), and J. Cahill, P. Casazza, and I. Daubechies,
*Phase retrieval in infinite-dimensional Hilbert spaces*, Trans. Amer. Math.
Soc. Ser. B 3 (2016), 63-76. This project formalises a fixed-dimensional stable
phase-retrieval theorem for the Gaussian L^2 closure of Hermite-Fock
polynomials.
-/
