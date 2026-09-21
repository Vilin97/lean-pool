/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingForcing

/-!
# Strict finite-`p` to legacy `q = 2` Besov regularity

This adapter transports the source finite-`p` carrier to the legacy signed
`H^s` right-hand-side carrier consumed by the one-cube deterministic theorem.
The quantitative strict-gap summation is owned by
`LocalCoarseGrainingForcing`.
-/

namespace Homogenization
namespace Book
namespace Ch03
namespace ABK26

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem cubeEuclideanWspKernel_neg {d : ℕ}
    (s : FractionalOrder) (p : FiniteLpExponent) (g : Vec d → Vec d) :
    cubeEuclideanWspKernel s p (fun x => -g x) =
      fun z => -cubeEuclideanWspKernel s p g z := by
  funext z
  rw [cubeEuclideanWspKernel_apply, cubeEuclideanWspKernel_apply]
  have hsub : -g z.1 - -g z.2 = -(g z.1 - g z.2) := by abel
  rw [hsub, show HilbertVec.ofVec (-(g z.1 - g z.2)) =
    -HilbertVec.ofVec (g z.1 - g z.2) by
      exact (HilbertVec.ofVecL d).map_neg _, smul_neg]

private theorem memCubeEuclideanFullWsp_neg {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    {g : Vec d → Vec d} (hg : MemCubeEuclideanFullWsp Q s p g) :
    MemCubeEuclideanFullWsp Q s p (fun x => -g x) := by
  constructor
  · simpa only [map_neg] using! hg.1.neg
  · unfold MemCubeEuclideanWsp
    rw [cubeEuclideanWspKernel_neg]
    exact hg.2.neg

/-- A strict finite-`p` Euclidean fractional-Sobolev witness supplies the
legacy `H^s` right-hand-side carrier.  The output sign is the one used by the
weak forced-equation interface. -/
theorem MemCubeEuclideanFullWsp.toCubeVectorBesovHRegularity_neg_of_lt
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {s s2 : FractionalOrder}
    {p : FiniteLpExponent} {g : Vec d → Vec d}
    (hg : MemCubeEuclideanFullWsp Q s2 p g)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) (hss2 : s.1 < s2.1) :
    CubeVectorBesovHRegularity Q s.1 (fun x => -g x) := by
  have hneg : MemCubeEuclideanFullWsp Q s2 p (fun x => -g x) :=
    memCubeEuclideanFullWsp_neg hg
  exact
    { memLp := MemCubeEuclideanFullWsp.memLpTwo hp hneg
      partialSeminorms_bddAbove :=
        cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_memLp_finiteP
          Q s s2 hss2 p hp (fun x => -g x) hneg }

end
end ABK26
end Ch03
end Book
end Homogenization
