/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.Basic
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# A linear Cauchy–Davenport bound over a full constant field

This file proves the specialization of the Hou–Leung–Xiang linear Kneser theorem needed for
Clifford's theorem. If every element of `K` algebraic over `k` is constant, then nonzero finite
dimensional `k`-subspaces `A, B ⊆ K` satisfy

`finrank A + finrank B ≤ finrank (A * B) + 1`.

The proof is the Dyson e-transform induction from Hou–Leung–Xiang. The full-constant-field
hypothesis makes the stabilizer-field step direct and avoids a separate finite/infinite base-field
split.
-/

@[expose] public section

open scoped Pointwise

namespace FunctionField

variable (k K : Type*) [Field k] [Field K] [Algebra k K]
  [IsFullConstantField k K]

/-- If a finite-dimensional subspace `A` containing `1` has dimension bigger than one, some
nonzero `e ∈ B` makes the Dyson intersection `A ∩ B e⁻¹` proper. -/
theorem exists_dyson_step (A B : Submodule k K) [FiniteDimensional k B]
    (hA1 : (1 : K) ∈ A) (hB1 : (1 : K) ∈ B) (hAdim : 1 < Module.finrank k A) :
    ∃ e : K, e ∈ B ∧ e ≠ 0 ∧
      A ⊓ Submodule.comap (LinearMap.mulRight k e) B ≠ A := by
  by_contra! h
  have hstable : ∀ a ∈ A, ∀ b ∈ B, a * b ∈ B := by
    intro a ha b hb
    by_cases hb0 : b = 0
    · subst b
      simp
    · have heq := h b hb hb0
      have hamem : a ∈ A ⊓ Submodule.comap (LinearMap.mulRight k b) B := heq.symm ▸ ha
      exact hamem.2
  have hBne : B ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨1, hB1, one_ne_zero⟩
  have hBfg : B.FG := (Submodule.fg_top B).mp Module.Finite.fg_top
  have hAle : A ≤ (1 : Submodule k K) := by
    intro a ha
    have haint : IsIntegral k a := isIntegral_of_smul_mem_submodule B hBne hBfg a (by
      intro b hb
      simpa only [smul_eq_mul] using hstable a ha b hb)
    obtain ⟨c, hc⟩ := IsFullConstantField.algebraic_mem (k := k) (K := K) a haint.isAlgebraic
    rw [Submodule.one_eq_span, Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    simpa only [Algebra.smul_def, mul_one] using hc.symm
  have hAeq : A = 1 := le_antisymm hAle (Submodule.one_le.mpr hA1)
  have hdim : Module.finrank k A = 1 := by
    rw [hAeq, Submodule.one_eq_span, finrank_span_singleton one_ne_zero]
  omega

/-- One Dyson e-transform preserves the sum of dimensions, strictly decreases the first
subspace, and does not enlarge the product space. -/
theorem dyson_step (A B : Submodule k K)
    [FiniteDimensional k A] [FiniteDimensional k B]
    (hA1 : (1 : K) ∈ A) (hB1 : (1 : K) ∈ B) (hAdim : 1 < Module.finrank k A) :
    ∃ A' B' : Submodule k K,
      (1 : K) ∈ A' ∧ (1 : K) ∈ B' ∧ A' < A ∧
      A'.FG ∧ B'.FG ∧
      Module.finrank k A' + Module.finrank k B' =
        Module.finrank k A + Module.finrank k B ∧ A' * B' ≤ A * B := by
  obtain ⟨e, heB, he0, hproper⟩ := exists_dyson_step k K A B hA1 hB1 hAdim
  let u : Kˣ := Units.mk0 e he0
  let ε : K ≃ₗ[k] K := u.mulRightLinearEquiv k
  let A' := A ⊓ Submodule.comap (ε : K →ₗ[k] K) B
  let B' := Submodule.map (ε : K →ₗ[k] K) A ⊔ B
  refine ⟨A', B', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨hA1, ?_⟩
    change ε 1 ∈ B
    simpa [ε, u] using heB
  · exact (show B ≤ Submodule.map (ε : K →ₗ[k] K) A ⊔ B from le_sup_right) hB1
  · exact lt_of_le_of_ne inf_le_left hproper
  · exact (Submodule.fg_top A').mp Module.Finite.fg_top
  · have hAfg : A.FG := (Submodule.fg_top A).mp Module.Finite.fg_top
    have hBfg : B.FG := (Submodule.fg_top B).mp Module.Finite.fg_top
    exact (hAfg.map (ε : K →ₗ[k] K)).sup hBfg
  · have hmapA' : Submodule.map (ε : K →ₗ[k] K) A' =
        Submodule.map (ε : K →ₗ[k] K) A ⊓ B := by
      ext x
      simp only [A', Submodule.mem_map_equiv, Submodule.mem_inf, Submodule.mem_comap,
        LinearEquiv.coe_coe]
      rw [ε.apply_symm_apply]
    have hfinA' : Module.finrank k A' =
        Module.finrank k ↑(Submodule.map (ε : K →ₗ[k] K) A ⊓ B) := by
      rw [← hmapA', LinearEquiv.finrank_map_eq]
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq
      (Submodule.map (ε : K →ₗ[k] K) A) B
    have hfinA := LinearEquiv.finrank_map_eq ε A
    have hdim' : Module.finrank k B' +
        Module.finrank k ↑(Submodule.map (ε : K →ₗ[k] K) A ⊓ B) =
          Module.finrank k ↑(Submodule.map (ε : K →ₗ[k] K) A) +
            Module.finrank k B := by
      simpa only [B'] using hdim
    omega
  · dsimp only [B']
    rw [Submodule.mul_sup]
    apply sup_le
    · apply Submodule.mul_le.mpr
      intro a ha b hb
      rw [Submodule.mem_map] at hb
      obtain ⟨b₀, hb₀, rfl⟩ := hb
      have hae : a * e ∈ B := ha.2
      have hmem := Submodule.mul_mem_mul hb₀ hae
      change a * ε b₀ ∈ A * B
      rw [show a * ε b₀ = b₀ * (a * e) by simp [ε, u]; ring]
      exact hmem
    · apply Submodule.mul_le.mpr
      intro a ha b hb
      change a ∈ A ⊓ Submodule.comap (ε : K →ₗ[k] K) B at ha
      exact Submodule.mul_mem_mul ha.1 hb

/-- The normalized linear Cauchy–Davenport bound, for subspaces containing `1`. -/
theorem normalized_mul_finrank (A B : Submodule k K)
    [FiniteDimensional k A] [FiniteDimensional k B]
    (hA1 : (1 : K) ∈ A) (hB1 : (1 : K) ∈ B) :
    Module.finrank k A + Module.finrank k B ≤ Module.finrank k (A * B) + 1 := by
  generalize hn : Module.finrank k A = n
  induction n using Nat.strong_induction_on generalizing A B with
  | h n ih =>
      have hnpos : 0 < n := by
        rw [← hn, Module.finrank_pos_iff]
        exact ⟨⟨1, hA1⟩, 0, by simp⟩
      by_cases hn1 : n = 1
      · have hAeq : A = 1 := by
          have hle : (1 : Submodule k K) ≤ A := Submodule.one_le.mpr hA1
          exact (Submodule.eq_of_le_of_finrank_eq hle (by
            rw [Submodule.one_eq_span, finrank_span_singleton one_ne_zero, hn, hn1])).symm
        subst A
        rw [hn1]
        change 1 + Module.finrank k B ≤
          Module.finrank k ↑((1 : Submodule k K) • B) + 1
        rw [Submodule.one_smul]
        omega
      · have hngt : 1 < n := by omega
        have hAdim : 1 < Module.finrank k A := hn.symm ▸ hngt
        obtain ⟨A', B', hA'1, hB'1, hA'lt, hA'fg, hB'fg, hdim, hprod⟩ :=
          dyson_step k K A B hA1 hB1 hAdim
        let : FiniteDimensional k A' := Module.Finite.of_fg hA'fg
        let : FiniteDimensional k B' := Module.Finite.of_fg hB'fg
        have hsmall : Module.finrank k A' < n := by
          rw [← hn]
          exact Submodule.finrank_lt_finrank_of_lt hA'lt
        have hih := ih (Module.finrank k A') hsmall A' B' hA'1 hB'1 rfl
        have hAfg : A.FG := (Submodule.fg_top A).mp Module.Finite.fg_top
        have hBfg : B.FG := (Submodule.fg_top B).mp Module.Finite.fg_top
        let : FiniteDimensional k (A * B) := Module.Finite.of_fg (hAfg.mul hBfg)
        have hmono : Module.finrank k (A' * B') ≤ Module.finrank k (A * B) :=
          Submodule.finrank_mono hprod
        omega

/-- **Linear Cauchy–Davenport over a full constant field.** Nonzero finite-dimensional
subspaces of `K` have product dimension at least the sum of their dimensions minus one. -/
theorem mul_finrank (A B : Submodule k K)
    [FiniteDimensional k A] [FiniteDimensional k B]
    (hA : A ≠ ⊥) (hB : B ≠ ⊥) :
    Module.finrank k A + Module.finrank k B ≤ Module.finrank k (A * B) + 1 := by
  rw [Submodule.ne_bot_iff] at hA hB
  obtain ⟨a, haA, ha0⟩ := hA
  obtain ⟨b, hbB, hb0⟩ := hB
  let ua : Kˣ := Units.mk0 a ha0
  let ub : Kˣ := Units.mk0 b hb0
  let εa : K ≃ₗ[k] K := (ua⁻¹).mulLeftLinearEquiv k K
  let εb : K ≃ₗ[k] K := (ub⁻¹).mulLeftLinearEquiv k K
  let εab : K ≃ₗ[k] K := (ua * ub).mulLeftLinearEquiv k K
  let A' := Submodule.map (εa : K →ₗ[k] K) A
  let B' := Submodule.map (εb : K →ₗ[k] K) B
  have hA'1 : (1 : K) ∈ A' := by
    apply Submodule.mem_map.mpr
    refine ⟨a, haA, ?_⟩
    change ((ua⁻¹ : Kˣ) : K) * a = 1
    exact inv_mul_cancel₀ ha0
  have hB'1 : (1 : K) ∈ B' := by
    apply Submodule.mem_map.mpr
    refine ⟨b, hbB, ?_⟩
    change ((ub⁻¹ : Kˣ) : K) * b = 1
    exact inv_mul_cancel₀ hb0
  have hAfin : A'.FG := by
    have hAfg : A.FG := (Submodule.fg_top A).mp Module.Finite.fg_top
    exact hAfg.map (εa : K →ₗ[k] K)
  have hBfin : B'.FG := by
    have hBfg : B.FG := (Submodule.fg_top B).mp Module.Finite.fg_top
    exact hBfg.map (εb : K →ₗ[k] K)
  let : FiniteDimensional k A' := Module.Finite.of_fg hAfin
  let : FiniteDimensional k B' := Module.Finite.of_fg hBfin
  have hnorm := normalized_mul_finrank k K A' B' hA'1 hB'1
  have hprod : A' * B' ≤ Submodule.comap (εab : K →ₗ[k] K) (A * B) := by
    apply Submodule.mul_le.mpr
    intro x hx y hy
    obtain ⟨x₀, hx₀, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨y₀, hy₀, rfl⟩ := Submodule.mem_map.mp hy
    change ((ua * ub : Kˣ) : K) *
      ((((ua⁻¹ : Kˣ) : K) * x₀) * (((ub⁻¹ : Kˣ) : K) * y₀)) ∈ A * B
    have hm := Submodule.mul_mem_mul hx₀ hy₀
    simpa [mul_assoc, mul_left_comm, mul_comm] using hm
  have hmap : Submodule.map (εab : K →ₗ[k] K) (A' * B') ≤ A * B :=
    (Submodule.map_le_iff_le_comap).mpr hprod
  have hAfg : A.FG := (Submodule.fg_top A).mp Module.Finite.fg_top
  have hBfg : B.FG := (Submodule.fg_top B).mp Module.Finite.fg_top
  let : FiniteDimensional k (A * B) := Module.Finite.of_fg (hAfg.mul hBfg)
  have hmono : Module.finrank k (A' * B') ≤ Module.finrank k (A * B) := by
    rw [← LinearEquiv.finrank_map_eq εab (A' * B')]
    exact Submodule.finrank_mono hmap
  have hfinA : Module.finrank k A' = Module.finrank k A := by
    exact LinearEquiv.finrank_map_eq εa A
  have hfinB : Module.finrank k B' = Module.finrank k B := by
    exact LinearEquiv.finrank_map_eq εb B
  omega

end FunctionField
