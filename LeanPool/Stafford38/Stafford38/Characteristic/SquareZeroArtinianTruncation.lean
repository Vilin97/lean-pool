/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.SquareZeroAnnihilatorBracket

/-!
# Artinian truncation in a square-zero deformation

This file isolates the algebraic replacement for the invalid pullback-
filtration division step.  If a power of an ideal annihilates the special
fibre, then every deformation-ring element specializing into that power sends
the deformation module into the parameter layer.  Two such blocks act by
zero, because the parameter is central and square-zero.

The result is deliberately stated without a noncommutative ideal on the
deformation ring.  Membership is tested after specialization in the
commutative fibre, which is exactly the datum available in the Rees two-jet.
-/

namespace Stafford38.Characteristic.SquareZeroArtinianTruncation

open Stafford38.Characteristic.SquareZeroTraceData
open Stafford38.Characteristic.SquareZeroAnnihilatorBracket

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
variable (m : Ideal R) (n : ℕ)

/-- If `m^n` annihilates the special fibre, a deformation element whose
specialization lies in `m^n` sends every vector into the parameter layer. -/
theorem rightAction_mem_parameterLayer_of_pi_mem_pow
    (hpow : m ^ n ≤ Module.annihilator R G)
    {a : B} (ha : D.pi a ∈ m ^ n) (z : N) :
    MulOpposite.op a • z ∈ LinearMap.range D.cAct := by
  exact rightAction_mem_range_cAct_of_pi_mem_annihilator D (hpow ha) z

/-- Two blocks specializing into an annihilating ideal power act successively
by zero. This is a two-step parameter-layer statement; it does not say that
every element specializing into `m ^ (2 * n)` acts by zero. -/
theorem iterated_rightAction_eq_zero_of_pi_mem_pow
    (hpow : m ^ n ≤ Module.annihilator R G)
    {a b : B} (ha : D.pi a ∈ m ^ n) (hb : D.pi b ∈ m ^ n) (z : N) :
    MulOpposite.op b • (MulOpposite.op a • z) = 0 := by
  exact iterated_rightAction_eq_zero_of_pi_mem_annihilator D
    (hpow ha) (hpow hb) z

/-- Equivalently, the product of two deformation blocks lying over `m^n`
acts trivially on the deformation module. -/
theorem product_rightAction_eq_zero_of_pi_mem_pow
    (hpow : m ^ n ≤ Module.annihilator R G)
    {a b : B} (ha : D.pi a ∈ m ^ n) (hb : D.pi b ∈ m ^ n) (z : N) :
    MulOpposite.op (a * b) • z = 0 := by
  simpa only [MulOpposite.op_mul, mul_smul] using
    iterated_rightAction_eq_zero_of_pi_mem_pow D m n hpow ha hb z

/-- Every finite sum of two-block products acts trivially. This is the
elementwise ideal-product form needed by an Artinian quotient construction;
no noncommutative ideal API on `B` is required. -/
theorem sum_products_rightAction_eq_zero_of_pi_mem_pow
    {ι : Type*} (s : Finset ι)
    (hpow : m ^ n ≤ Module.annihilator R G)
    (a b : ι → B)
    (ha : ∀ i ∈ s, D.pi (a i) ∈ m ^ n)
    (hb : ∀ i ∈ s, D.pi (b i) ∈ m ^ n) (z : N) :
    MulOpposite.op (∑ i ∈ s, a i * b i) • z = 0 := by
  rw [show MulOpposite.op (∑ i ∈ s, a i * b i) =
      ∑ i ∈ s, MulOpposite.op (a i * b i) by
    exact map_sum (MulOpposite.opAddEquiv : B ≃+ Bᵐᵒᵖ) _ s]
  rw [Finset.sum_smul]
  apply Finset.sum_eq_zero
  intro i hi
  exact product_rightAction_eq_zero_of_pi_mem_pow D m n hpow
    (ha i hi) (hb i hi) z


end

end Stafford38.Characteristic.SquareZeroArtinianTruncation
