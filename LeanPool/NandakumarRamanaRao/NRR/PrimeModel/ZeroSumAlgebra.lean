/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.PhaseInterfaces

/-!
# Algebra on the zero-sum representation

The pre-existing `ZeroSum n` type is the subtype of functions `Fin n → ℝ` whose coordinates sum to
zero. This module equips it with the pointwise additive and real-linear structures and records the
coordinate-sum linear map.
-/

@[expose] public section

namespace NRR

open scoped BigOperators

variable {n : ℕ}

/-- Sum of all coordinates, as a linear map. -/
def coordinateSum (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ i, v i
  map_add' u v := by simp [Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum]

@[simp] theorem coordinateSum_apply (v : Fin n → ℝ) :
    coordinateSum n v = ∑ i, v i := rfl

namespace ZeroSum

/-- Identify zero-sum coordinate vectors with the kernel of coordinate summation. -/
def equivKernel (n : ℕ) :
    ZeroSum n ≃ LinearMap.ker (coordinateSum n) where
  toFun v := ⟨fun i => v i, v.sum_coe⟩
  invFun v := ⟨v.1, v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance instAddCommGroup : AddCommGroup (ZeroSum n) :=
  (equivKernel n).addCommGroup

noncomputable instance instModule : Module ℝ (ZeroSum n) :=
  (equivKernel n).addEquiv.module ℝ

@[simp] theorem add_apply (u v : ZeroSum n) (i : Fin n) :
    (u + v) i = u i + v i := rfl

@[simp] theorem neg_apply (u : ZeroSum n) (i : Fin n) :
    (-u) i = -u i := rfl

@[simp] theorem sub_apply (u v : ZeroSum n) (i : Fin n) :
    (u - v) i = u i - v i := rfl

@[simp] theorem smul_apply (c : ℝ) (u : ZeroSum n) (i : Fin n) :
    (c • u) i = c * u i := rfl

instance instContinuousAdd : ContinuousAdd (ZeroSum n) where
  continuous_add := by
    refine continuous_induced_rng.2 ?_
    exact continuous_pi fun i =>
      ((continuous_apply i).comp (continuous_induced_dom.comp continuous_fst)).add
        ((continuous_apply i).comp (continuous_induced_dom.comp continuous_snd))

instance instContinuousNeg : ContinuousNeg (ZeroSum n) where
  continuous_neg := by
    refine continuous_induced_rng.2 ?_
    change Continuous (fun a : ZeroSum n => fun i => -a i)
    exact continuous_pi fun i =>
      ((continuous_apply i).comp continuous_subtype_val).neg

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (ZeroSum n) :=
  IsTopologicalAddGroup.mk

instance instContinuousSMul : ContinuousSMul ℝ (ZeroSum n) where
  continuous_smul := by
    refine continuous_induced_rng.2 ?_
    exact continuous_pi fun i =>
      continuous_fst.mul
        ((continuous_apply i).comp (continuous_induced_dom.comp continuous_snd))

/-- The inclusion of the zero-sum representation into the full coordinate space. -/
def coeLinearMap : ZeroSum n →ₗ[ℝ] (Fin n → ℝ) where
  toFun v := fun i => v i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coeLinearMap_apply (v : ZeroSum n) :
    coeLinearMap v = fun i => v i := rfl

noncomputable instance instFiniteDimensional : FiniteDimensional ℝ (ZeroSum n) :=
  FiniteDimensional.of_injective coeLinearMap (by
    intro u v h
    apply ZeroSum.ext
    intro i
    exact congrFun h i)

end ZeroSum

/-- The existing zero-sum subtype is linearly equivalent to the kernel of coordinate summation. -/
noncomputable def ZeroSum.linearEquivKer :
    ZeroSum n ≃ₗ[ℝ] LinearMap.ker (coordinateSum n) where
  toFun v := ⟨fun i => v i, v.sum_coe⟩
  invFun v := ⟨v.1, v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coordinate summation is surjective when there is at least one coordinate. -/
theorem coordinateSum_surjective (hn : 0 < n) :
    Function.Surjective (coordinateSum n) := by
  let i0 : Fin n := ⟨0, hn⟩
  intro c
  let v : Fin n → ℝ := fun i => if i = i0 then c else 0
  refine ⟨v, ?_⟩
  simp [coordinateSum, v, i0]

/-- Dimension of the standard zero-sum representation. -/
theorem ZeroSum.finrank (hn : 0 < n) :
    Module.finrank ℝ (ZeroSum n) = n - 1 := by
  have hrange : LinearMap.range (coordinateSum n) = ⊤ :=
    LinearMap.range_eq_top.2 (coordinateSum_surjective hn)
  have hnullity := LinearMap.finrank_range_add_finrank_ker (coordinateSum n)
  have hdomain : Module.finrank ℝ (Fin n → ℝ) = n := by simp
  have hker : Module.finrank ℝ (LinearMap.ker (coordinateSum n)) = n - 1 := by
    rw [hrange] at hnullity
    simp [hdomain] at hnullity
    omega
  rw [LinearEquiv.finrank_eq (ZeroSum.linearEquivKer (n := n))]
  exact hker

end NRR
