/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.SquareZeroTraceData
import Mathlib.RingTheory.OreLocalization.OreSet

/-!
# Ore localization of a square-zero deformation

For a ring with a central square-zero parameter, whose commutators are
divisible by that parameter, the inverse image of every multiplicative set in
the commutative special fibre is a left Ore set.  Squaring the denominator is
enough both for the Ore equation and for the weak cancellation axiom.

This is the localization input needed by the minimal-prime trace argument.  No
trace, finite-length, or prime-ideal conclusion is asserted here.
-/

namespace Stafford38.Characteristic.SquareZeroOreLocalization

open Stafford38.Characteristic.SquareZeroTraceData

noncomputable section

universe u_k u_R u_B u_N u_G

variable {k : Type u_k} {R : Type u_R} {B : Type u_B}
variable {N : Type u_N} {G : Type u_G}
variable [Field k] [CommRing R] [Algebra k R]
variable [Ring B] [Algebra k B]
variable [AddCommGroup N] [Module k N] [Module Bᵐᵒᵖ N]
variable [SMulCommClass k Bᵐᵒᵖ N]
variable [AddCommGroup G] [Module k G] [Module R G]

variable (D : RightSquareZeroTraceData k R B N G)

/-- Multiplication by `c` kills the failure of two elements of `B` to
commute. -/
theorem c_mul_commutator_eq_zero (a b : B) :
    D.c * Stafford.commutator a b = 0 := by
  obtain ⟨z, hz, -⟩ := D.commutator_factor a b
  rw [hz, ← mul_assoc, ← pow_two, D.c_sq, zero_mul]

/-- Moving a factor past another factor is legitimate after multiplying by
the square-zero parameter. -/
theorem c_mul_mul_comm (a b : B) : D.c * (a * b) = D.c * (b * a) := by
  have h := c_mul_commutator_eq_zero D a b
  simp only [Stafford.commutator_eq_shared, AlgebraicAnalysis.ringCommutator,
    mul_sub] at h
  exact sub_eq_zero.mp h

private theorem nonempty_oreSet_comap_of
    {A C : Type*} [Ring A] [CommMonoid C]
    (c : A)
    (cCenter : c ∈ Set.center A)
    (commutatorFactor : ∀ a b : A, ∃ z : A,
      Stafford.commutator a b = c * z)
    (cMulComm : ∀ a b : A, c * (a * b) = c * (b * a))
    (pi : A →* C) (S : Submonoid C) :
    Nonempty (OreLocalization.OreSet (S.comap pi)) := by
  rw [OreLocalization.nonempty_oreSet_iff]
  constructor
  · intro r₁ r₂ s hrs
    let delta : A := r₁ - r₂
    obtain ⟨z, hsz⟩ := commutatorFactor (s : A) delta
    let s2 : S.comap pi :=
      ⟨(s : A) ^ 2, by
        change pi ((s : A) ^ 2) ∈ S
        rw [map_pow]
        exact S.pow_mem s.property 2⟩
    refine ⟨s2, ?_⟩
    apply sub_eq_zero.mp
    rw [← mul_sub]
    change (s : A) ^ 2 * delta = 0
    have hdelta_s : delta * (s : A) = 0 := by
      change (r₁ - r₂) * (s : A) = 0
      rw [sub_mul, hrs, sub_self]
    have hs_delta : (s : A) * delta = c * z := by
      simp only [Stafford.commutator_eq_shared, AlgebraicAnalysis.ringCommutator,
        hdelta_s, sub_zero] at hsz
      exact hsz
    calc
      (s : A) ^ 2 * delta = (s : A) * ((s : A) * delta) := by
        simp [pow_two, mul_assoc]
      _ = (s : A) * (c * z) := by rw [hs_delta]
      _ = c * ((s : A) * z) := by
        have hcs : c * (s : A) = (s : A) * c := by
          exact cCenter.comm (s : A)
        rw [← mul_assoc, ← hcs, mul_assoc]
      _ = c * (z * (s : A)) := cMulComm (s : A) z
      _ = (c * z) * (s : A) := by rw [mul_assoc]
      _ = ((s : A) * delta) * (s : A) := by rw [hs_delta]
      _ = (s : A) * (delta * (s : A)) := by rw [mul_assoc]
      _ = 0 := by rw [hdelta_s, mul_zero]
  · intro r s
    obtain ⟨z, hsr⟩ := commutatorFactor (s : A) r
    let s2 : S.comap pi :=
      ⟨(s : A) ^ 2, by
        change pi ((s : A) ^ 2) ∈ S
        rw [map_pow]
        exact S.pow_mem s.property 2⟩
    refine ⟨(s : A) * r + c * z, s2, ?_⟩
    change (s : A) ^ 2 * r = ((s : A) * r + c * z) * (s : A)
    have hmove : (s : A) * r = r * (s : A) + c * z := by
      simp only [Stafford.commutator_eq_shared, AlgebraicAnalysis.ringCommutator] at hsr
      simpa [add_comm] using sub_eq_iff_eq_add.mp hsr
    calc
      (s : A) ^ 2 * r = (s : A) * ((s : A) * r) := by
        simp [pow_two, mul_assoc]
      _ = (s : A) * (r * (s : A) + c * z) := by rw [hmove]
      _ = ((s : A) * r) * (s : A) + (s : A) * (c * z) := by
        rw [mul_add, mul_assoc]
      _ = ((s : A) * r) * (s : A) + c * ((s : A) * z) := by
        have hcs : c * (s : A) = (s : A) * c := by
          exact cCenter.comm (s : A)
        rw [← mul_assoc, ← hcs]
        simp only [mul_assoc]
      _ = ((s : A) * r) * (s : A) + c * (z * (s : A)) := by
        rw [cMulComm (s : A) z]
      _ = ((s : A) * r + c * z) * (s : A) := by
        rw [add_mul]
        simp only [mul_assoc]

/-- The inverse image in `B` of a multiplicative set in the commutative fibre
is a left Ore set.  The construction uses the squared denominator.

The result is returned as `Nonempty` so callers can install the chosen Ore-set
structure locally without introducing a global instance for every `S`. -/
theorem nonempty_oreSet_comap (S : Submonoid R) :
    Nonempty (OreLocalization.OreSet (S.comap D.pi.toMonoidHom)) :=
  nonempty_oreSet_comap_of D.c
    D.c_center
    (fun a b => by
      obtain ⟨z, hz, -⟩ := D.commutator_factor a b
      exact ⟨z, hz⟩)
    (c_mul_mul_comm D) D.pi.toMonoidHom S

/-- Specialization from the opposite deformation ring to the commutative
special fibre. -/
def oppositeSpecializationMonoidHom : Bᵐᵒᵖ →* R where
  toFun b := D.pi b.unop
  map_one' := by simp
  map_mul' a b := by
    change D.pi (b.unop * a.unop) = D.pi a.unop * D.pi b.unop
    rw [map_mul, mul_comm]

/-- The right-module localization uses the opposite ring.  Its pulled-back
denominators are left Ore as well, so the concrete right two-jet module can be
localized by Mathlib's left Ore-localization API. -/
theorem nonempty_oreSet_comap_op (S : Submonoid R) :
    Nonempty (OreLocalization.OreSet
      (S.comap (oppositeSpecializationMonoidHom D))) := by
  apply nonempty_oreSet_comap_of (MulOpposite.op D.c)
  · refine
      { comm := ?_
        left_assoc := by intros; simp [mul_assoc]
        right_assoc := by intros; simp [mul_assoc] }
    intro a
    apply MulOpposite.unop_injective
    change a.unop * D.c = D.c * a.unop
    exact (D.c_center.comm a.unop).symm
  · intro a b
    obtain ⟨z, hz, -⟩ := D.commutator_factor b.unop a.unop
    refine ⟨MulOpposite.op z, ?_⟩
    apply MulOpposite.unop_injective
    change Stafford.commutator b.unop a.unop = z * D.c
    rw [hz, D.c_center.comm z]
  · intro a b
    apply MulOpposite.unop_injective
    change b.unop * a.unop * D.c = a.unop * b.unop * D.c
    rw [← D.c_center.comm (b.unop * a.unop),
      ← D.c_center.comm (a.unop * b.unop)]
    exact c_mul_mul_comm D b.unop a.unop


end

end Stafford38.Characteristic.SquareZeroOreLocalization
