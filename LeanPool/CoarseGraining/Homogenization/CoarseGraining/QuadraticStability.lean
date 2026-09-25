/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.QuadraticStability.CauchySchwarz
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.QuadraticStability.Integral

/-!
# Quadratic stability (Lemma 4.1)

Facade re-exporting the three items of the Lean form of Lemma 4.1
(`l.quadratic.stability`) of the high-moment paper (Armstrong–Kuusi–Loher, in
preparation):

* **B′1** `abs_blockVecDot_blockMatVecMul_le_of_isSymmetricBlockMat`
  (Cauchy–Schwarz for a symmetric positive semidefinite block form) and
* **B′2** `abs_blockVecDot_sub_le_of_blockMatLoewnerLE`
  (the mixed-metric inequality) — see `QuadraticStability/CauchySchwarz.lean`;
* **B′3** `abs_setIntegral_energy_sub_le`
  (integral stability of the two quadratic minima, constant `6K`) — see
  `QuadraticStability/Integral.lean`.
-/

@[expose] public section
