/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.proofs.weyl_symplectic

/-!
# Generic square-zero trace data

This file records the minimal algebraic interface consumed by a later trace
argument.  The deformation ring may be noncommutative, and its module acts on
the right, encoded as a left action of the opposite ring.  In particular,
right multiplication reverses composition of endomorphisms.

No localization, trace theorem, minimal-prime statement, Gabber theorem, or
concrete Weyl instance is asserted here.
-/

namespace Stafford38.Characteristic.SquareZeroTraceData

noncomputable section

universe u_k u_R u_B u_N u_G

variable (k : Type u_k) (B : Type u_B) (N : Type u_N)
variable [Field k] [Ring B]
variable [AddCommGroup N] [Module k N] [Module Bᵐᵒᵖ N]
variable [SMulCommClass k Bᵐᵒᵖ N]

/-- Right multiplication by `b`, regarded as a `k`-linear endomorphism.

The scalar action is by `Bᵐᵒᵖ`; thus `rightActionEnd k B N b` sends `m` to
`m b` in ordinary right-module notation. -/
def rightActionEnd (b : B) : Module.End k N where
  toFun m := MulOpposite.op b • m
  map_add' _ _ := smul_add _ _ _
  map_smul' a m := (smul_comm a (MulOpposite.op b) m).symm

@[simp] theorem rightActionEnd_apply (b : B) (m : N) :
    rightActionEnd k B N b m = MulOpposite.op b • m :=
  rfl

/-- Composition of right actions reverses the displayed endomorphism order. -/
theorem rightActionEnd_mul_reverse (a b : B) :
    rightActionEnd k B N b * rightActionEnd k B N a =
      rightActionEnd k B N (a * b) := by
  ext m
  change MulOpposite.op b • (MulOpposite.op a • m) =
    MulOpposite.op (a * b) • m
  rw [← mul_smul]
  rfl

/-- The commutator of right-action endomorphisms has reversed inputs.

With `R_b(m) = m b`, this is `[R_b,R_a] = R_[a,b]`. -/
theorem rightAction_commutator (a b : B) :
    Stafford.commutator
        (rightActionEnd k B N b) (rightActionEnd k B N a) =
      rightActionEnd k B N (Stafford.commutator a b) := by
  simp only [Stafford.commutator_eq_shared, AlgebraicAnalysis.ringCommutator]
  rw [rightActionEnd_mul_reverse, rightActionEnd_mul_reverse]
  ext m
  simp [rightActionEnd, AlgebraicAnalysis.ringCommutator, sub_smul]

/-- Minimal data for a right-module square-zero deformation and its
first-order commutator bracket.

The structure deliberately records only the interfaces required by the later
trace argument.  It does not assert that such data exist for the Weyl Rees
two-jet. -/
structure RightSquareZeroTraceData
    (k : Type u_k) (R : Type u_R) (B : Type u_B)
    (N : Type u_N) (G : Type u_G)
    [Field k] [CommRing R] [Algebra k R]
    [Ring B] [Algebra k B]
    [AddCommGroup N] [Module k N] [Module Bᵐᵒᵖ N]
    [SMulCommClass k Bᵐᵒᵖ N]
    [AddCommGroup G] [Module k G] [Module R G] where
  /-- The central square-zero deformation parameter. -/
  c : B
  c_center : c ∈ Set.center B
  c_sq : c ^ 2 = 0
  /-- Specialization from the deformation ring to the commutative fibre. -/
  pi : B →ₐ[k] R
  pi_surjective : Function.Surjective pi
  pi_c : pi c = 0
  /-- Action of the deformation parameter on the right module. -/
  cAct : N →ₗ[k] N
  cAct_apply : ∀ m, cAct m = MulOpposite.op c • m
  c_exact : LinearMap.ker cAct = LinearMap.range cAct
  /-- Specialization of the module to its commutative fibre. -/
  rho : N →ₗ[k] G
  rho_surjective : Function.Surjective rho
  rho_ker : LinearMap.ker rho = LinearMap.range cAct
  rho_action : ∀ b m, rho (MulOpposite.op b • m) = pi b • rho m
  /-- The `k`-bilinear first-order bracket on the special fibre. -/
  bracket : R →ₗ[k] R →ₗ[k] R
  /-- Every deformation-ring commutator is divisible on the left by `c`,
  with quotient specializing to the bracket in the displayed input order. -/
  commutator_factor : ∀ a b : B, ∃ z : B,
    Stafford.commutator a b = c * z ∧
      pi z = bracket (pi a) (pi b)

variable {R : Type u_R} {G : Type u_G}
variable [Algebra k B]
variable [CommRing R] [Algebra k R]
variable [AddCommGroup G] [Module k G] [Module R G]

namespace RightSquareZeroTraceData

variable (D : RightSquareZeroTraceData k R B N G)

/-- The recorded parameter action is literally right multiplication by `c`. -/
theorem cAct_eq_rightActionEnd :
    D.cAct = rightActionEnd k B N D.c := by
  ext m
  exact D.cAct_apply m

/-- The parameter action squares to zero. -/
theorem cAct_comp_self : D.cAct.comp D.cAct = 0 := by
  ext m
  simp only [LinearMap.comp_apply, D.cAct_apply, LinearMap.zero_apply]
  rw [← mul_smul]
  rw [← MulOpposite.op_mul]
  rw [← pow_two, D.c_sq]
  exact zero_smul _ _

/-- Module specialization kills the parameter action. -/
theorem rho_comp_cAct : D.rho.comp D.cAct = 0 := by
  ext m
  simp only [LinearMap.comp_apply, D.cAct_apply, LinearMap.zero_apply]
  rw [D.rho_action, D.pi_c, zero_smul]

/-- Special-fibre elements admit deformation lifts whose commutator has the
recorded first-order factorization. -/
theorem exists_lifts_commutator_factor (x y : R) :
    ∃ a b z : B,
      D.pi a = x ∧ D.pi b = y ∧
      Stafford.commutator a b = D.c * z ∧
      D.pi z = D.bracket x y := by
  obtain ⟨a, ha⟩ := D.pi_surjective x
  obtain ⟨b, hb⟩ := D.pi_surjective y
  obtain ⟨z, hz, hbracket⟩ := D.commutator_factor a b
  refine ⟨a, b, z, ha, hb, hz, ?_⟩
  simpa [ha, hb] using hbracket

end RightSquareZeroTraceData


end
end Stafford38.Characteristic.SquareZeroTraceData
