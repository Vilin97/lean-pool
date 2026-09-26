/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.SquareZeroArtinianTruncation
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.LocalRing.Module


/-!
# High-power reduction for a square-zero deformation

This file isolates the finite-length reduction used in Singh--Kumar's local
argument.  A finite-length module over a commutative local ring is killed by
a power of the maximal ideal.  In an exact square-zero deformation, two
blocks lying over that power act successively by zero.  Finally, if such a
two-block sum is also a multiple of the deformation parameter, exactness
forces its parameter cofactor to specialize into the maximal ideal.

The last statement is the elementwise form of the parameter-ideal
intersection used in the high-power quotient argument.  It avoids introducing
an artificial multiplication API for two-sided ideals: membership in the
relevant product is recorded by an explicit finite sum of products.
-/

@[expose] public section

namespace Stafford38.Characteristic.SquareZeroHighPowerReduction

open Stafford38.Characteristic.SquareZeroTraceData
open Stafford38.Characteristic.SquareZeroArtinianTruncation

noncomputable section

universe u_k u_R u_B u_N u_G

variable {k : Type u_k} {R : Type u_R} {B : Type u_B}
variable {N : Type u_N} {G : Type u_G}
variable [Field k] [CommRing R] [Algebra k R] [IsLocalRing R]
variable [Ring B] [Algebra k B]
variable [AddCommGroup N] [Module k N] [Module Bᵐᵒᵖ N]
variable [SMulCommClass k Bᵐᵒᵖ N]
variable [AddCommGroup G] [Module k G] [Module R G]

local notation "𝔪" => IsLocalRing.maximalIdeal R

/-- A finite-length module over a commutative local ring is annihilated by a
power of the maximal ideal. -/
theorem exists_maximalIdeal_pow_le_annihilator_of_finiteLength
    (hG : IsFiniteLength R G) :
    ∃ n : ℕ, 𝔪 ^ n ≤ Module.annihilator R G := by
  induction hG with
  | of_subsingleton =>
      refine ⟨0, ?_⟩
      intro r _hr
      rw [Module.mem_annihilator]
      intro g
      exact Subsingleton.elim _ _
  | @of_simple_quotient M _ _ S _ _ ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + 1, ?_⟩
      have hmS : 𝔪 • (⊤ : Submodule R M) ≤ S := by
        rw [Submodule.smul_le]
        intro r hr g _hg
        rw [← Submodule.Quotient.mk_eq_zero S]
        have hmax : IsLocalRing.maximalIdeal R =
            Module.annihilator R (M ⧸ S) :=
          (IsLocalRing.eq_maximalIdeal
            (IsSimpleModule.annihilator_isMaximal
              (R := R) (M := M ⧸ S))).symm
        have hrann : r ∈ Module.annihilator R (M ⧸ S) := hmax ▸ hr
        exact Module.mem_annihilator.mp hrann (Submodule.Quotient.mk g)
      have hpowS : (𝔪 ^ n) • S = ⊥ := by
        apply le_antisymm
        · calc
            (𝔪 ^ n) • S ≤
                Module.annihilator R S • S :=
              Submodule.smul_mono hn le_rfl
            _ = ⊥ := Submodule.annihilator_smul S
        · exact bot_le
      have hpowM : (𝔪 ^ (n + 1)) • (⊤ : Submodule R M) = ⊥ := by
        apply le_antisymm
        · rw [pow_succ, mul_smul]
          calc
            (𝔪 ^ n) • (𝔪 • (⊤ : Submodule R M)) ≤
                (𝔪 ^ n) • S := Submodule.smul_mono le_rfl hmS
            _ = ⊥ := hpowS
        · exact bot_le
      intro r hr
      rw [Module.mem_annihilator]
      intro g
      have hmem : r • g ∈
          (𝔪 ^ (n + 1)) • (⊤ : Submodule R M) :=
        Submodule.smul_mem_smul hr trivial
      have : r • g ∈ (⊥ : Submodule R M) := by
        rw [← hpowM]
        exact hmem
      simpa using this

/-- If a parameter multiple acts trivially on the deformation module, then
its cofactor specializes into the maximal ideal.  This is the exactness and
nonzero-special-fibre step in the parameter-ideal intersection argument. -/
theorem parameterFactor_mem_maximalIdeal_of_rightAction_eq_zero
    [Nontrivial G]
    (D : RightSquareZeroTraceData k R B N G)
    {z : B}
    (hz : ∀ w : N, MulOpposite.op (D.c * z) • w = 0) :
    D.pi z ∈ 𝔪 := by
  have hpiAnn : D.pi z ∈ Module.annihilator R G := by
    rw [Module.mem_annihilator]
    intro g
    obtain ⟨w, rfl⟩ := D.rho_surjective g
    have hcAct : D.cAct (MulOpposite.op z • w) = 0 := by
      rw [D.cAct_apply, ← mul_smul]
      change MulOpposite.op (z * D.c) • w = 0
      rw [← D.c_center.comm z]
      exact hz w
    have hrange : MulOpposite.op z • w ∈ LinearMap.range D.cAct := by
      rw [← D.c_exact, LinearMap.mem_ker]
      exact hcAct
    have hrho : D.rho (MulOpposite.op z • w) = 0 := by
      rw [← D.rho_ker] at hrange
      exact LinearMap.mem_ker.mp hrange
    rw [D.rho_action] at hrho
    exact hrho
  by_contra hnot
  have hunit : IsUnit (D.pi z) := IsLocalRing.notMem_maximalIdeal.mp hnot
  obtain ⟨g, hg⟩ := exists_ne (0 : G)
  have hzero := Module.mem_annihilator.mp hpiAnn g
  exact hg (hunit.smul_eq_zero.mp hzero)

/-- Elementwise parameter-ideal intersection.  A finite sum of products of
two blocks over an annihilating power acts by zero; if that sum is `c*z`, then
the parameter cofactor `z` lies over the maximal ideal. -/
theorem parameterFactor_mem_maximalIdeal_of_eq_sum_products
    [Nontrivial G]
    (D : RightSquareZeroTraceData k R B N G)
    (m : Ideal R) (n : ℕ)
    {z : B} {iota : Type*} (s : Finset iota)
    (hpow : m ^ n ≤ Module.annihilator R G)
    (a b : iota → B)
    (ha : ∀ i ∈ s, D.pi (a i) ∈ m ^ n)
    (hb : ∀ i ∈ s, D.pi (b i) ∈ m ^ n)
    (heq : D.c * z = ∑ i ∈ s, a i * b i) :
    D.pi z ∈ 𝔪 := by
  apply parameterFactor_mem_maximalIdeal_of_rightAction_eq_zero D
  intro w
  rw [heq]
  exact sum_products_rightAction_eq_zero_of_pi_mem_pow
    D m n s hpow a b ha hb w

/-- The exact high-power descent step.  If a parameter multiple is congruent,
modulo a two-block sum, to a parameter multiple whose cofactor is already over
the maximal ideal, then its own cofactor is over the maximal ideal. -/
theorem parameterFactor_mem_maximalIdeal_of_eq_parameter_add_sum_products
    [Nontrivial G]
    (D : RightSquareZeroTraceData k R B N G)
    (m : Ideal R) (n : ℕ)
    {z w : B} {iota : Type*} (s : Finset iota)
    (hpow : m ^ n ≤ Module.annihilator R G)
    (hw : D.pi w ∈ 𝔪)
    (a b : iota → B)
    (ha : ∀ i ∈ s, D.pi (a i) ∈ m ^ n)
    (hb : ∀ i ∈ s, D.pi (b i) ∈ m ^ n)
    (heq : D.c * z = D.c * w + ∑ i ∈ s, a i * b i) :
    D.pi z ∈ 𝔪 := by
  have hsep : D.pi (z - w) ∈ 𝔪 := by
    apply parameterFactor_mem_maximalIdeal_of_eq_sum_products
      D m n s hpow a b ha hb
    calc
      D.c * (z - w) = D.c * z - D.c * w := mul_sub _ _ _
      _ = ∑ i ∈ s, a i * b i := by rw [heq]; abel
  have hsum : D.pi (z - w) + D.pi w ∈ 𝔪 :=
    (IsLocalRing.maximalIdeal R).add_mem hsep hw
  simpa using hsum

/-- Finite length supplies one exponent for both the two-block vanishing and
the parameter-ideal separation theorem. -/
theorem exists_highPower_parameterIdeal_reduction
    [Nontrivial G]
    (D : RightSquareZeroTraceData k R B N G)
    (hG : IsFiniteLength R G) :
    ∃ n : ℕ,
      𝔪 ^ n ≤ Module.annihilator R G ∧
      ∀ {z w : B} {iota : Type*} (s : Finset iota),
        D.pi w ∈ 𝔪 →
        ∀ (a b : iota → B),
          (∀ i ∈ s, D.pi (a i) ∈ 𝔪 ^ n) →
          (∀ i ∈ s, D.pi (b i) ∈ 𝔪 ^ n) →
          D.c * z = D.c * w + ∑ i ∈ s, a i * b i →
          D.pi z ∈ 𝔪 := by
  obtain ⟨n, hpow⟩ :=
    exists_maximalIdeal_pow_le_annihilator_of_finiteLength hG
  refine ⟨n, hpow, ?_⟩
  intro z w iota s hw a b ha hb heq
  exact parameterFactor_mem_maximalIdeal_of_eq_parameter_add_sum_products
    D 𝔪 n s hpow hw a b ha hb heq


end

end Stafford38.Characteristic.SquareZeroHighPowerReduction
