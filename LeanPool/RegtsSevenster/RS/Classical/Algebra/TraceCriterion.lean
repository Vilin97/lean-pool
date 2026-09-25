/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Semisimplicity from a trace form

A finite-dimensional complex algebra carrying a linear functional
that vanishes on nilpotents and is nondegenerate in the form
`(∀ b, τ (b * a) = 0) → a = 0` is semisimple: every element of the
Jacobson radical is nilpotent (the radical of an Artinian ring is a
nilpotent ideal), so the functional kills `b * j` for every `b`,
forcing `j = 0`.

-/

@[expose] public section

namespace RS

universe u

/-- A finite-dimensional complex algebra with a linear functional
vanishing on nilpotents and nondegenerate in the form
`(∀ b, τ (b * a) = 0) → a = 0` is semisimple. -/
theorem isSemisimpleRing_of_trace {A : Type u} [Ring A] [Algebra ℂ A]
    [FiniteDimensional ℂ A] (τ : A →ₗ[ℂ] ℂ)
    (hnil : ∀ x : A, IsNilpotent x → τ x = 0)
    (hnondeg : ∀ a : A, (∀ b : A, τ (b * a) = 0) → a = 0) :
    IsSemisimpleRing A := by
  have : IsArtinianRing A := isArtinian_of_tower ℂ inferInstance
  -- ═══════ The radical vanishes ═══════
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  have hJbot : Ring.jacobson A = ⊥ := by
    rw [eq_bot_iff]
    intro j hj
    rw [Ideal.mem_bot]
    apply hnondeg
    intro b
    apply hnil
    have hbj : b * j ∈ (⊥ : Ideal A).jacobson := by
      rw [Ideal.jacobson_bot]
      exact Ideal.mul_mem_left _ b hj
    refine ⟨n, ?_⟩
    have hpow := Ideal.pow_mem_pow hbj n
    rw [hn] at hpow
    exact Ideal.mem_bot.mp hpow
  -- ═══════ Transport semisimplicity from the trivial quotient ═══════
  have hquot : IsSemisimpleRing (A ⧸ Ring.jacobson A) :=
    IsSemiprimaryRing.isSemisimpleRing
  have hker : Ring.jacobson A = RingHom.ker (RingHom.id A) := by
    rw [hJbot]
    ext x
    simp [RingHom.mem_ker]
  have e : (A ⧸ Ring.jacobson A) ≃+* A :=
    (Ideal.quotEquivOfEq hker).trans
      (RingHom.quotientKerEquivOfRightInverse
        (f := RingHom.id A) (g := _root_.id) (fun _ => rfl))
  exact RingHom.isSemisimpleRing_of_surjective e.toRingHom e.surjective

end RS
