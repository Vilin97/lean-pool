/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/

module

public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.ContinuousLinearMap
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.IsMaximalSelfAdjoint
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.Isometry
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.LinearEquiv
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.Matrix
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.Misc
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.Tactic


/-!
# Vendor

Supporting modules for Euclidean Jordan algebras: power associativity, the spectral theorem, the
    trace form, Koecher/Alfsen-Shultz, and the frame Peirce decomposition.
-/

@[expose] public section
