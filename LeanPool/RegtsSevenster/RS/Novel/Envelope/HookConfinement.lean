/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Envelope.BlockBounds

/-!
# Hook confinement

A `PermTower` over a family of algebras `E n` is a family of
representations of the symmetric-group algebras with exponentially
bounded dimensions (`finrank (E n) ≤ A ^ n`, the accompanying
paper's hypothesis, with `A` a real constant) in which vanishing
propagates along the standard embeddings.  The main theorem:
relative to any `SchurPackage`, the shapes alive in a tower are
confined to a hook — there is an `s` with every alive shape
satisfying `IsInHook (s − 1) (s − 1)`.

The argument: the square shape of side `s`, for `s` given by the
package's `square_dim` growth field at `⌈√A⌉`, has a block too large
for the tower's dimension bound, so it is dead
(`dim_sq_le_finrank`); by `e_killed_of_contained` and vanishing
propagation no shape containing the square is alive; and a shape
outside the hook contains the square.
-/

namespace RS

universe u

/-- A tower of representations of the symmetric-group algebras on a
family of complex algebras, with vanishing propagating along the
standard embeddings (`symCast`) and exponentially bounded target
dimensions.  The skein endomorphism algebras form such a tower. -/
structure PermTower (E : ℕ → Type u) [∀ n, Ring (E n)]
    [∀ n, Algebra ℂ (E n)] (A : ℝ) where
  /-- The representations. -/
  rep : ∀ n, SymGroupAlgebra n →ₐ[ℂ] E n
  /-- Vanishing propagates along the standard embeddings. -/
  compat : ∀ {m n : ℕ} (h : m ≤ n) (x : SymGroupAlgebra m),
    rep m x = 0 → rep n (symCast h x) = 0
  /-- The exponential dimension bound. -/
  bound : ∀ n, ((Module.finrank ℂ (E n) : ℕ) : ℝ) ≤ A ^ n

namespace PermTower

variable {E : ℕ → Type u}

/-- A shape is alive in a tower when its idempotent is not killed. -/
def Alive [∀ n, Ring (E n)] [∀ n, Algebra ℂ (E n)] {A : ℝ}
    (T : PermTower E A) (P : SchurPackage.{u})
    (μ : YoungDiagram) : Prop :=
  T.rep μ.card (P.e μ) ≠ 0

/-- The growth constant of a tower is nonnegative: it dominates the
dimension at one strand. -/
theorem growth_nonneg [∀ n, Ring (E n)] [∀ n, Algebra ℂ (E n)] {A : ℝ}
    (T : PermTower E A) : 0 ≤ A := by
  have h := T.bound 1
  rw [pow_one] at h
  exact le_trans (Nat.cast_nonneg _) h

/-- **Square death**: the square of side `s` is not alive as soon as
its block dimension squared exceeds the tower's dimension bound at
`s²` strands.  This is the accompanying paper's hypothesis verbatim:
`dim² ≤ finrank ≤ A ^ (s²) < dim²`. -/
theorem not_alive_square [∀ n, Ring (E n)] [∀ n, Algebra ℂ (E n)] {A : ℝ}
    [∀ n, Module.Finite ℂ (E n)]
    (T : PermTower E A) (P : SchurPackage.{u}) {s : ℕ}
    (hs : A ^ (s ^ 2) < ((P.dim (squareDiagram s) : ℕ) : ℝ) ^ 2) :
    ¬ T.Alive P (squareDiagram s) := by
  intro halive
  have hcard : (squareDiagram s).card = s ^ 2 := squareDiagram_card s
  have hle := P.dim_sq_le_finrank (squareDiagram s)
    (T.rep (squareDiagram s).card) halive
  have hleR : ((P.dim (squareDiagram s) : ℕ) : ℝ) ^ 2
      ≤ ((Module.finrank ℂ (E (squareDiagram s).card) : ℕ) : ℝ) := by
    exact_mod_cast hle
  have hb := T.bound (squareDiagram s).card
  rw [hcard] at hleR hb
  linarith

/-- No shape containing a dead shape is alive. -/
theorem not_alive_of_le [∀ n, Ring (E n)] [∀ n, Algebra ℂ (E n)] {A : ℝ}
    (T : PermTower E A) (P : SchurPackage.{u})
    {lam mu : YoungDiagram} (hle : lam ≤ mu)
    (hdead : ¬ T.Alive P lam) : ¬ T.Alive P mu := by
  intro halive
  have hcard : lam.card ≤ mu.card :=
    Finset.card_le_card (YoungDiagram.cells_subset_iff.mpr hle)
  have hkill : T.rep mu.card (symCast hcard (P.e lam)) = 0 :=
    T.compat hcard _ (not_not.mp hdead)
  exact halive (P.e_killed_of_contained hle hcard (T.rep mu.card) hkill)

/-- **Hook confinement**: every shape alive in a tower lies in the
hook `IsInHook (s − 1) (s − 1)` for a side `s` given by the
package's growth field at the tower's bound. -/
theorem hook_confinement [∀ n, Ring (E n)] [∀ n, Algebra ℂ (E n)] {A : ℝ}
    [∀ n, Module.Finite ℂ (E n)]
    (T : PermTower E A) (P : SchurPackage.{u}) :
    ∃ s : ℕ,
      ∀ μ : YoungDiagram, T.Alive P μ → IsInHook (s - 1) (s - 1) μ := by
  -- The package's growth field is stated at a natural base, so it is
  -- fed `⌈√A⌉`, which dominates `√A`.
  obtain ⟨s, hs⟩ := P.square_dim ⌈Real.sqrt A⌉₊
  refine ⟨s, fun μ halive => ?_⟩
  by_contra hout
  rw [not_isInHook_iff] at hout
  have hsq : squareDiagram s ≤ μ := squareDiagram_le_of_rowLen (by omega)
  refine T.not_alive_of_le P hsq (T.not_alive_square P ?_) halive
  have hA0 : 0 ≤ A := T.growth_nonneg
  have hceil : Real.sqrt A ≤ (⌈Real.sqrt A⌉₊ : ℝ) := Nat.le_ceil _
  have hAle : A ≤ ((⌈Real.sqrt A⌉₊ : ℝ)) ^ 2 := by
    calc A = Real.sqrt A ^ 2 := (Real.sq_sqrt hA0).symm
      _ ≤ ((⌈Real.sqrt A⌉₊ : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg A) hceil 2
  have hsR : ((⌈Real.sqrt A⌉₊ : ℝ)) ^ (s ^ 2)
      < ((P.dim (squareDiagram s) : ℕ) : ℝ) := by exact_mod_cast hs
  calc A ^ (s ^ 2)
      ≤ (((⌈Real.sqrt A⌉₊ : ℝ)) ^ 2) ^ (s ^ 2) :=
        pow_le_pow_left₀ hA0 hAle _
    _ = (((⌈Real.sqrt A⌉₊ : ℝ)) ^ (s ^ 2)) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul]
    _ < ((P.dim (squareDiagram s) : ℕ) : ℝ) ^ 2 :=
        pow_lt_pow_left₀ hsR (by positivity) two_ne_zero

end PermTower

end RS
