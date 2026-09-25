/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.SquareZeroTraceData


/-!
# Annihilator closure from a square-zero deformation

The exact parameter sequence already forces the annihilator of the special
fibre to be closed under the recorded first-order bracket.  The proof uses
only right-action order, centrality and square-zero exactness; no localization,
trace, finiteness or commutative-algebra hypothesis beyond the existing
commutative special fibre is needed.

This proves closure only when both bracket inputs lie in the annihilator
itself.  It does not prove bracket closure of its radical or of any prime ideal
for inputs that merely lie in that larger ideal.
-/

@[expose] public section

namespace Stafford38.Characteristic.SquareZeroAnnihilatorBracket

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

/-- If the specialization of `a` annihilates `G`, right multiplication by
`a` on the deformation module lands in the image of the parameter action. -/
theorem rightAction_mem_range_cAct_of_pi_mem_annihilator
    {a : B} (ha : D.pi a ∈ Module.annihilator R G) (m : N) :
    MulOpposite.op a • m ∈ LinearMap.range D.cAct := by
  rw [← D.rho_ker, LinearMap.mem_ker]
  rw [D.rho_action]
  exact Module.mem_annihilator.mp ha (D.rho m)

/-- Centrality of the parameter lets every right action pass through its
recorded action on `N`. -/
theorem rightAction_cAct_comm (a : B) (m : N) :
    MulOpposite.op a • D.cAct m = D.cAct (MulOpposite.op a • m) := by
  rw [D.cAct_apply, D.cAct_apply, ← mul_smul, ← mul_smul]
  change MulOpposite.op (D.c * a) • m = MulOpposite.op (a * D.c) • m
  rw [D.c_center.comm a]

/-- Two successive right actions vanish when both specializations annihilate
the special fibre.  The displayed order is literal: first `a`, then `b`. -/
theorem iterated_rightAction_eq_zero_of_pi_mem_annihilator
    {a b : B}
    (ha : D.pi a ∈ Module.annihilator R G)
    (hb : D.pi b ∈ Module.annihilator R G) (m : N) :
    MulOpposite.op b • (MulOpposite.op a • m) = 0 := by
  obtain ⟨u, hu⟩ :=
    rightAction_mem_range_cAct_of_pi_mem_annihilator D ha m
  rw [← hu, rightAction_cAct_comm]
  obtain ⟨v, hv⟩ :=
    rightAction_mem_range_cAct_of_pi_mem_annihilator D hb u
  rw [← hv]
  change (D.cAct.comp D.cAct) v = 0
  rw [D.cAct_comp_self]
  rfl

/-- Consequently the right action of the deformation-ring commutator
vanishes.  The reversal `[R_b,R_a] = R_[a,b]` is explicit. -/
theorem commutator_rightAction_eq_zero_of_pi_mem_annihilator
    {a b : B}
    (ha : D.pi a ∈ Module.annihilator R G)
    (hb : D.pi b ∈ Module.annihilator R G) (m : N) :
    MulOpposite.op (Stafford.commutator a b) • m = 0 := by
  have hab :=
    iterated_rightAction_eq_zero_of_pi_mem_annihilator D ha hb m
  have hba :=
    iterated_rightAction_eq_zero_of_pi_mem_annihilator D hb ha m
  rw [← rightActionEnd_apply (k := k) (B := B) (N := N),
    ← rightAction_commutator (k := k) (B := B) (N := N) a b]
  change MulOpposite.op b • (MulOpposite.op a • m) -
    MulOpposite.op a • (MulOpposite.op b • m) = 0
  rw [hab, hba, sub_self]

/-- If `[a,b]=c*z`, then the quotient `z` acts trivially after module
specialization.  The explicit left factor `c*z` is essential here: centrality
moves it to the right-module order needed by `cAct`. -/
theorem rho_rightAction_eq_zero_of_commutator_factor
    {a b z : B}
    (ha : D.pi a ∈ Module.annihilator R G)
    (hb : D.pi b ∈ Module.annihilator R G)
    (hz : Stafford.commutator a b = D.c * z) (m : N) :
    D.rho (MulOpposite.op z • m) = 0 := by
  have hcomm :=
    commutator_rightAction_eq_zero_of_pi_mem_annihilator D ha hb m
  have hcAct : D.cAct (MulOpposite.op z • m) = 0 := by
    calc
      D.cAct (MulOpposite.op z • m) =
          MulOpposite.op D.c • (MulOpposite.op z • m) := D.cAct_apply _
      _ = MulOpposite.op (z * D.c) • m := by rw [← mul_smul]; rfl
      _ = MulOpposite.op (D.c * z) • m := by rw [D.c_center.comm z]
      _ = MulOpposite.op (Stafford.commutator a b) • m := by rw [hz]
      _ = 0 := hcomm
  have hm : MulOpposite.op z • m ∈ LinearMap.range D.cAct := by
    rw [← D.c_exact, LinearMap.mem_ker]
    exact hcAct
  rw [← D.rho_ker] at hm
  exact LinearMap.mem_ker.mp hm

/-- The recorded bracket preserves the annihilator of the special fibre in
both inputs. -/
theorem bracket_mem_annihilator
    {x y : R}
    (hx : x ∈ Module.annihilator R G)
    (hy : y ∈ Module.annihilator R G) :
    D.bracket x y ∈ Module.annihilator R G := by
  obtain ⟨a, b, z, ha, hb, hz, hbracket⟩ :=
    RightSquareZeroTraceData.exists_lifts_commutator_factor
      (k := k) (B := B) (N := N) D x y
  rw [Module.mem_annihilator]
  intro g
  obtain ⟨m, rfl⟩ := D.rho_surjective g
  have hzrho := rho_rightAction_eq_zero_of_commutator_factor D
    (ha ▸ hx) (hb ▸ hy) hz m
  rw [D.rho_action] at hzrho
  simpa [hbracket] using hzrho


end

end Stafford38.Characteristic.SquareZeroAnnihilatorBracket
