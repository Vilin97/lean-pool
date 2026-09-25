/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.UniformSpace.Completion
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.ContinuousValuations

/-!
# Multiplicative-continuity bridge: non-vanishing on units of the completion

A continuous valuation `v : R → Γ₀` on a topological commutative ring does not
vanish on elements `α : R` whose image `coe α` in `UniformSpace.Completion R`
is a unit. Avoids the substantive Wedhorn 7.49 Spv-extension construction by
exploiting density of `coe` + multiplicativity + continuity at `1`.
-/

@[expose] public section

open UniformSpace

namespace Valuation

variable {R : Type u_1} [CommRing R] [UniformSpace R] [IsTopologicalRing R]
  [IsUniformAddGroup R]
variable {Γ₀ : Type u_2} [LinearOrderedCommGroupWithZero Γ₀]
  [TopologicalSpace Γ₀] [OrderClosedTopology Γ₀] [T2Space Γ₀]
  [ContinuousMul Γ₀]

theorem ne_zero_of_unit_completion
    (v : Valuation R Γ₀) (hv_cont : ContinuousAt v 1)
    {α : R} (hα_unit : IsUnit
      (UniformSpace.Completion.coeRingHom α : UniformSpace.Completion R)) :
    v α ≠ 0 := by
  intro hvα
  obtain ⟨u, hu⟩ := hα_unit
  set xinv : UniformSpace.Completion R := (↑u⁻¹ : UniformSpace.Completion R) with hxinv_def
  have hα_xinv : (UniformSpace.Completion.coeRingHom α :
      UniformSpace.Completion R) * xinv = 1 := by
    rw [hxinv_def, ← hu]; exact_mod_cast u.mul_inv
  set F : Filter R :=
    Filter.comap (UniformSpace.Completion.coe' : R → _) (nhds xinv) with hF_def
  haveI hF_neBot : F.NeBot :=
    UniformSpace.Completion.isDenseInducing_coe.comap_nhds_neBot xinv
  have hcoeF : Filter.Tendsto
      (UniformSpace.Completion.coe' : R → _) F (nhds xinv) :=
    Filter.tendsto_comap
  have h1 : Filter.Tendsto
      (fun y : R ↦ (UniformSpace.Completion.coe' (α * y) :
        UniformSpace.Completion R))
      F (nhds (1 : UniformSpace.Completion R)) := by
    have h_mul : Filter.Tendsto
        (fun y : R ↦ (UniformSpace.Completion.coeRingHom α :
          UniformSpace.Completion R) *
          UniformSpace.Completion.coe' y)
        F (nhds ((UniformSpace.Completion.coeRingHom α :
          UniformSpace.Completion R) * xinv)) :=
      hcoeF.const_mul (UniformSpace.Completion.coeRingHom α)
    rw [hα_xinv] at h_mul
    convert h_mul using 1
    funext y
    show UniformSpace.Completion.coe' (α * y) =
      UniformSpace.Completion.coeRingHom α * UniformSpace.Completion.coe' y
    change UniformSpace.Completion.coe' (α * y) =
      UniformSpace.Completion.coe' α * UniformSpace.Completion.coe' y
    exact UniformSpace.Completion.coe_mul α y
  have hα_mul : Filter.Tendsto (fun y : R ↦ α * y) F (nhds (1 : R)) := by
    have h_nhds : (nhds (1 : R)) = Filter.comap
        (UniformSpace.Completion.coe' : R → _) (nhds (1 : UniformSpace.Completion R)) := by
      have hcoe1 : (UniformSpace.Completion.coe' (1 : R) :
          UniformSpace.Completion R) = 1 := by
        show ((1 : R) : UniformSpace.Completion R) = 1
        exact UniformSpace.Completion.coe_one (α := R)
      rw [← hcoe1]
      exact UniformSpace.Completion.isDenseInducing_coe.nhds_eq_comap 1
    rw [h_nhds]
    exact Filter.tendsto_comap_iff.mpr h1
  have hv_tendsto : Filter.Tendsto (fun y : R ↦ v (α * y)) F (nhds (1 : Γ₀)) := by
    have ht : Filter.Tendsto v (nhds (1 : R)) (nhds (v 1)) := hv_cont
    rw [v.map_one] at ht
    exact ht.comp hα_mul
  have hv_const : (fun y : R ↦ v (α * y)) = fun _ ↦ (0 : Γ₀) := by
    funext y
    rw [v.map_mul, hvα, zero_mul]
  rw [hv_const] at hv_tendsto
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds hv_tendsto)

end Valuation
