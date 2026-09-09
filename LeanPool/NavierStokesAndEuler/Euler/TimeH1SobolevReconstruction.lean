/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeH1Reconstruction
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevPair

/-!
# Uniform-time reconstruction preserves fixed Sobolev word blocks

Time reconstruction is a fixed bounded linear map. Therefore it commutes
with every external and base spatial word and costs no derivative shift.
-/

@[expose] public section


noncomputable section

namespace EulerTimeH1SobolevReconstruction

open Set ContinuousLinearMap EulerTimeLp EulerTimeH1Reconstruction
  EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

variable {P E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

/-- Cache the standard `NormedAddCommGroup (TimeLp T E)` instance to shorten typeclass
synthesis. -/
local instance instTimeH1SobolevReconstruction1 (T : ℝ) : NormedAddCommGroup (TimeLp T E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (TimeLp T E)` instance to shorten typeclass synthesis. -/
local instance instTimeH1SobolevReconstruction2 (T : ℝ) : NormedSpace ℝ (TimeLp T E) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,E)` instance to shorten typeclass
synthesis. -/
local instance instTimeH1SobolevReconstruction3 (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,E)` instance to shorten typeclass
synthesis. -/
local instance instTimeH1SobolevReconstruction4 (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,E) :=
    inferInstance

/-- The exact finite Sobolev block is bounded by the blocks of the L² value
and its genuine L² time derivative. -/
theorem reconstruction_block_le (directions : ι → P) (q : ℕ)
    (T : ℝ) (hT : 0 < T) (p v : P → TimeLp T E)
    (hp : ContDiff ℝ ∞ p) (hv : ContDiff ℝ ∞ v) (n : ℕ) (x : P) :
    block directions q (fun y => reconstruction T hT.le (p y,v y)) n x ≤
      (T⁻¹*Real.sqrt T)*block directions q p n x +
        (2*Real.sqrt T)*block directions q v n x :=
  block_linear_pair_le (P := P) (E := TimeLp T E) (F := TimeLp T E)
    (G := C(Icc (0 : ℝ) T,E)) directions q (reconstruction (E := E) T hT.le)
    (T⁻¹*Real.sqrt T) (2*Real.sqrt T) (reconstruction_norm_le (E := E) T hT) p v hp hv n x

/-- Uniform time evaluation spends neither a spatial derivative nor an
external factorial shift and preserves the original radius. -/
theorem reconstruction_block_gevrey (directions : ι → P) (q : ℕ)
    (T : ℝ) (hT : 0 < T) (p v : P → TimeLp T E)
    (hp : ContDiff ℝ ∞ p) (hv : ContDiff ℝ ∞ v)
    (R C D : ℝ) (d : ℕ)
    (hbp : ∀ n x, block directions q p n x ≤ C * majorant R d n)
    (hbv : ∀ n x, block directions q v n x ≤ D * majorant R d n)
    (n : ℕ) (x : P) :
    block directions q (fun y => reconstruction T hT.le (p y,v y)) n x ≤
      (T⁻¹*Real.sqrt T*C+2*Real.sqrt T*D)*majorant R d n := by
  have hp0 : 0 ≤ T⁻¹*Real.sqrt T := by positivity
  have hv0 : 0 ≤ 2*Real.sqrt T := by positivity
  exact (reconstruction_block_le directions q T hT p v hp hv n x).trans
    ((add_le_add (mul_le_mul_of_nonneg_left (hbp n x) hp0)
      (mul_le_mul_of_nonneg_left (hbv n x) hv0)).trans_eq (by ring))

end EulerTimeH1SobolevReconstruction
