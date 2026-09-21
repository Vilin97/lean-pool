/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
import Mathlib.Tactic.Positivity
import LeanPool.ACMax.Spectral.AlgConn
import LeanPool.ACMax.Spectral.RayleighUpper

/-!
# Universal test-vector interface

`algConn_le_two_of_testvector`: any nonzero vector `x` orthogonal to the all-ones
vector whose Laplacian quadratic form is at most `2 ‖x‖²` certifies `algConn G ≤ 2`.

This is the direct corollary of the Courant–Fischer bridge `algConn_mul_sq_le` that
every concrete upper-bound certificate in the `Cuts/` chapter factors through: the
balanced, weighted and signed cuts, the induced-`2K₂` bound and the good-`C₄`/`K_{2,3}`
certificates all build an explicit `x ⊥ 𝟙` and discharge the Rayleigh inequality here.
-/

namespace ACMax

open Matrix

open Classical in
/-- Universal certificate: a nonzero `x ⊥ 𝟙` with `xᵀ L x ≤ 2‖x‖²` forces
`algConn G ≤ 2`. -/
theorem algConn_le_two_of_testvector {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (x : V → ℝ) (hx0 : ∑ i, x i = 0) (hxne : ∃ i, x i ≠ 0)
    (hQ : dotProduct x ((G.lapMatrix ℝ).mulVec x) ≤ 2 * ∑ i, (x i) ^ 2) :
    algConn G ≤ 2 := by
  classical
  set S : ℝ := ∑ i, (x i) ^ 2 with hSdef
  have hSnonneg : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg (x i)
  obtain ⟨j, hj⟩ := hxne
  have hSpos : 0 < S := by
    refine Finset.sum_pos' (fun i _ => sq_nonneg (x i)) ?_
    exact ⟨j, Finset.mem_univ j, by positivity⟩
  have key := algConn_mul_sq_le G x hx0
  have hchain : algConn G * S ≤ 2 * S := le_trans key hQ
  rw [mul_comm (algConn G) S, mul_comm 2 S] at hchain
  exact le_of_mul_le_mul_left hchain hSpos

end ACMax
