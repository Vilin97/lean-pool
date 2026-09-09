/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevWordBlocks

/-! Exact derivative coordinates of genuine Sobolev word blocks. -/

@[expose] public section


noncomputable section

namespace EulerSobolevWordBlocks

open EulerLiftedGradientSpace EulerCylinderSobolevSpace

variable (period : ℝ) [Fact (0 < period)]

/-- Every derivative coordinate of a true word block is the corresponding concatenated original
word. -/
theorem wordBlock_word (q n : ℕ) (w : Fin n → Fin 4) (u : SobolevSpace period (q + n))
    {m : ℕ} (hm : m ≤ q) (v : Fin m → Fin 4) :
    word period (wordBlock period q n w u) hm v =
      word period u (by omega : m+n ≤ q+n) (Fin.append v w) := by
  induction n with
  | zero =>
    have hw : w = Fin.elim0 := Subsingleton.elim _ _
    subst w
    have he : Fin.append v (Fin.elim0 : Fin 0 → Fin 4) = v := by
      funext i
      exact Fin.append_left v Fin.elim0 i
    rw [he]
    rfl
  | succ n ih =>
    change word period (wordBlock period q n (Fin.init w)
      (derivativeOperator period (q+n) (w (Fin.last n)) u)) hm v = _
    rw [ih]
    change u.val ⟨⟨m+n+1, _⟩, Fin.snoc (Fin.append v (Fin.init w)) (w (Fin.last n))⟩ = _
    rw [← Fin.append_snoc, Fin.snoc_init_self]
    rfl

end EulerSobolevWordBlocks
