/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfaces.AECongruence
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2

/-! # Hodge Zero -/

@[expose] public section

namespace Homogenization

noncomputable section

/--
If a cube vector field is both a zero-trace potential field and solenoidal, then
it vanishes a.e. on the cube.

This is the uniqueness end of the cube Hodge projection argument: the
solenoidal test against its own zero-trace potential primitive kills its `L²`
norm, and the Hilbert `L²` carrier converts zero norm back to a.e. equality of
plain vector fields.
-/
theorem ae_eq_zero_of_isPotentialZeroTraceOn_of_isSolenoidalOn
    {d : ℕ} (Q : TriadicCube d) {w : Vec d → Vec d}
    (hw : IsPotentialZeroTraceOn (cubeSet Q) w)
    (hsol : IsSolenoidalOn (cubeSet Q) w) :
    w =ᵐ[volumeMeasureOn (cubeSet Q)] (0 : Vec d → Vec d) := by
  let : Fact (MeasureTheory.volume (cubeSet Q) < ⊤) :=
    ⟨volume_cubeSet_lt_top Q⟩
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q)) := by
    change MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict (cubeSet Q))
    infer_instance
  rcases hw with ⟨u, hgrad⟩
  have hwMem : MemVectorL2 (cubeSet Q) w := by
    simpa [hgrad] using u.toH1Function.grad_memVectorL2
  let hzeroMem : MemVectorL2 (cubeSet Q) (0 : Vec d → Vec d) :=
    MeasureTheory.MemLp.zero
  have hww_zero :
      ∫ x in cubeSet Q, vecDot (w x) (w x) ∂MeasureTheory.volume = 0 := by
    simpa [hgrad] using hsol u
  have hzero_hilbert : toHilbertVectorL2OfVecField hwMem = 0 := by
    have hinner_zero :
        inner ℝ (toHilbertVectorL2OfVecField hwMem)
          (toHilbertVectorL2OfVecField hwMem) = 0 := by
      calc
        inner ℝ (toHilbertVectorL2OfVecField hwMem)
            (toHilbertVectorL2OfVecField hwMem)
            = ∫ x in cubeSet Q, vecDot (w x) (w x) ∂MeasureTheory.volume := by
                exact inner_toHilbertVectorL2OfVecField_eq_integral
                  (U := cubeSet Q) hwMem hwMem
        _ = 0 := hww_zero
    have hnorm_sq : ‖toHilbertVectorL2OfVecField hwMem‖ ^ 2 = 0 := by
      simpa [real_inner_self_eq_norm_sq] using hinner_zero
    have hnorm_zero : ‖toHilbertVectorL2OfVecField hwMem‖ = 0 := by
      nlinarith [sq_nonneg ‖toHilbertVectorL2OfVecField hwMem‖, hnorm_sq]
    exact norm_eq_zero.mp hnorm_zero
  have hzero_vector : toVectorL2 hwMem = 0 := by
    have htransport :=
      congrArg (hilbertVectorL2ToVectorL2 (U := cubeSet Q)) hzero_hilbert
    simpa [hilbertVectorL2ToVectorL2_toHilbertVectorL2
      (U := cubeSet Q) (f := w) hwMem] using htransport
  have hzero_vector' :
      toVectorL2 hwMem =
        toVectorL2 (U := cubeSet Q) (f := (0 : Vec d → Vec d)) hzeroMem := by
    rw [show toVectorL2 (U := cubeSet Q) (f := (0 : Vec d → Vec d)) hzeroMem = 0 by
      simp [toVectorL2]]
    exact hzero_vector
  exact
    (toVectorL2_eq_toVectorL2_iff
      (U := cubeSet Q) (f := w) (g := 0) hwMem hzeroMem).mp hzero_vector'

/--
If a cube vector field is both a zero-trace potential field and solenoidal, then
the concrete `q = 2` negative Besov seminorm sees it as zero.
-/
theorem cubeBesovNegativeVectorSeminormTwo_eq_zero_of_isPotentialZeroTraceOn_of_isSolenoidalOn
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) {w : Vec d → Vec d}
    (hw : IsPotentialZeroTraceOn (cubeSet Q) w)
    (hsol : IsSolenoidalOn (cubeSet Q) w) :
    cubeBesovNegativeVectorSeminormTwo Q s w = 0 := by
  have hw_ae_zero :=
    ae_eq_zero_of_isPotentialZeroTraceOn_of_isSolenoidalOn Q hw hsol
  rw [cubeBesovNegativeVectorSeminormTwo_eq_of_ae_eq_on_cubeSet (Q := Q) (s := s) hw_ae_zero]
  exact cubeBesovNegativeVectorSeminormTwo_zero Q s

end

end Homogenization
