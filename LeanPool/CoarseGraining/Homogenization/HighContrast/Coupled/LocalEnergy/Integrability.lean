/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.HighContrast.Coupled.LocalEnergy.TestPair
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2

/-!
# Local block energy: integrability workhorses

Two small `IntegrableOn` workhorses used throughout the test-identity expansion
and the bulk/cutoff estimates.  Every integrand appearing in the coupled
weak-form expansion is either

* `h · (F · G)` with `h ∈ L∞` and `F, G ∈ L²`  (bulk / energy integrands), or
* `u · (F · g)` with `u ∈ L²`, `F ∈ L²` and `g ∈ L∞`  (cutoff integrands).

Both are `L¹` on the finite-measure cube; the two lemmas below package the
Hölder/`L∞` bookkeeping so the downstream files never touch it directly.
-/

@[expose] public section

namespace Homogenization

open Homogenization
open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- **Bulk-type integrability.**  `h · (F · G)` is `L¹` when `h ∈ L∞` and
`F, G ∈ L²`. -/
theorem integrableOn_memLpTop_mul_vecDot {U : Set (Vec d)} {h : Vec d → ℝ}
    {F G : Vec d → Vec d}
    (hh : MemLp h (⊤ : ENNReal) (volumeMeasureOn U))
    (hF : MemVectorL2 U F) (hG : MemVectorL2 U G) :
    IntegrableOn (fun x => h x * vecDot (F x) (G x)) U := by
  have hvd : IntegrableOn (fun x => vecDot (F x) (G x)) U :=
    integrableOn_vecDot_of_memVectorL2 hF hG
  have hmul : Integrable (h * fun x => vecDot (F x) (G x)) (volumeMeasureOn U) :=
    hvd.mul_of_top_right hh
  simpa [Pi.mul_apply] using! hmul

/-- **Cutoff-type integrability.**  `u · (F · g)` is `L¹` when `u, F ∈ L²`
and every coordinate of `g` lies in `L∞`. -/
theorem integrableOn_scalarL2_mul_vecDot_memLpTop {U : Set (Vec d)} {u : Vec d → ℝ}
    {F g : Vec d → Vec d}
    (hu : MemScalarL2 U u) (hF : MemVectorL2 U F)
    (hg : ∀ i, MemLp (fun x => g x i) (⊤ : ENNReal) (volumeMeasureOn U)) :
    IntegrableOn (fun x => u x * vecDot (F x) (g x)) U := by
  classical
  have hrw : (fun x => u x * vecDot (F x) (g x))
      = fun x => ∑ i, (u x * F x i) * g x i := by
    funext x
    rw [vecDot, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hrw]
  refine MeasureTheory.integrable_finsetSum Finset.univ (fun i _ => ?_)
  have hi : Integrable (fun x => u x * F x i) (volumeMeasureOn U) :=
    hu.integrable_mul (memScalarL2_coord_of_memVectorL2 hF i)
  have := hi.mul_of_top_left (hg i)
  simpa [Pi.mul_apply] using! this

end

end Homogenization
