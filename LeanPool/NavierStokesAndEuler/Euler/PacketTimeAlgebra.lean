/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldAlgebra

@[expose] public section

/-! Genuine within-interval time derivatives commute with the finite packet algebra. -/

noncomputable section

namespace EulerPacketCylinderField.TimeDerivative

open Set Finset EulerPacketProfileRecursion EulerVolterraConvolution

variable {P T : ℝ} [Fact (0 < P)] {hT : 0 ≤ T}
  {raw raw' next next' : VectorField}
  {G : Field P T raw} {G' : Field P T raw'}
  {H : Field P T next} {H' : Field P T next'}

theorem zero : TimeDerivative hT (Field.zero P T) (Field.zero P T) := by
  intro t
  exact hasDerivWithinAt_const (t : ℝ) (Icc (0 : ℝ) T) (0 : EulerLiftedGradientSpace.LiftL2 P)

theorem add (hG : TimeDerivative hT G G') (hH : TimeDerivative hT H H') :
    TimeDerivative hT (G.add H) (G'.add H') := by
  intro t
  exact (hG t).add (hH t)

theorem smul (hG : TimeDerivative hT G G') (c : ℝ) :
    TimeDerivative hT (G.smul c) (G'.smul c) := by
  intro t
  exact (hG t).const_smul c

theorem finsetSum {ι : Type*} (s : Finset ι) (f f' : ι → VectorField)
    (G : ∀ i, Field P T (f i)) (G' : ∀ i, Field P T (f' i))
    (hG : ∀ i ∈ s, TimeDerivative hT (G i) (G' i)) :
    TimeDerivative hT (Field.finsetSum s f G) (Field.finsetSum s f' G') := by
  intro t
  have h := HasDerivWithinAt.fun_sum (u := s) (fun i hi => hG i hi t)
  change HasDerivWithinAt (fun r => (∑ i ∈ s, (G i).path) (projIcc 0 T hT r))
    ((∑ i ∈ s, (G' i).path) t) (Icc (0 : ℝ) T) t
  simp only [ContinuousMap.sum_apply]
  exact h

theorem of_path_eq (hG : TimeDerivative hT G G')
    (h : H.path=G.path) (h' : H'.path=G'.path) : TimeDerivative hT H H' := by
  unfold TimeDerivative
  rw [h,h']
  exact hG

end EulerPacketCylinderField.TimeDerivative
