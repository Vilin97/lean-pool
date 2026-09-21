/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.ContinuousValuations
import LeanPool.UniformSheafyTateDomains.AdicSpaces.AdicSpectrum
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Group Actions on the Valuation Spectrum

Given a group `G` acting on a ring `A` by ring automorphisms (`MulSemiringAction G A`),
we construct the induced action on the valuation spectrum `Spv(A)` and show it preserves
the subsets `Cont(A)` and `Spa(A, A⁺)`.

## Main definitions

* `ValuationSpectrum.instMulActionSpv` : The `MulAction G (Spv A)` where `(g • v)(a, b) =
  v(g⁻¹ • a, g⁻¹ • b)`.
* `ValuationSpectrum.instMulActionCont` : The induced `MulAction G ↥(Cont A)`.

## Main results

* `ValuationSpectrum.smul_mem_cont` : The `G`-action preserves continuity of valuations.
* `ValuationSpectrum.smul_mem_spa` : The `G`-action preserves `Spa(A, A⁺)` membership
  when `A⁺` is `G`-stable.
-/

open ValuationSpectrum

namespace ValuationSpectrum

/-! ### Group action on Spv(A), Cont(A), and Spa(A, A⁺) -/

section GroupAction

variable (G : Type*) [Group G] [Finite G]
variable (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable [MulSemiringAction G A] [ContinuousConstSMul G A]

/-- The induced `MulAction` of `G` on `Spv(A)` via precomposition: `g • v = Spv(g⁻¹)(v)`.
Concretely, `(g • v)(a, b) = v(g⁻¹ • a, g⁻¹ • b)`. -/
noncomputable instance instMulActionSpv : MulAction G (Spv A) where
  smul g v := comap (MulSemiringAction.toRingHom G A g⁻¹) v
  one_smul v := by
    change comap (MulSemiringAction.toRingHom G A 1⁻¹) v = v
    have : MulSemiringAction.toRingHom G A (1⁻¹ : G) = RingHom.id A := by
      ext a; simp [MulSemiringAction.toRingHom]
    exact congr_fun (this ▸ comap_id) v
  mul_smul g h v := by
    change comap (MulSemiringAction.toRingHom G A (g * h)⁻¹) v =
      comap (MulSemiringAction.toRingHom G A g⁻¹)
        (comap (MulSemiringAction.toRingHom G A h⁻¹) v)
    have : MulSemiringAction.toRingHom G A (g * h)⁻¹ =
        (MulSemiringAction.toRingHom G A h⁻¹).comp
          (MulSemiringAction.toRingHom G A g⁻¹) := by
      ext a; simp [MulSemiringAction.toRingHom, mul_smul]
    exact congr_fun (this ▸ comap_comp _ _) v

/-- The `G`-action on `Spv(A)` preserves continuity of valuations. -/
theorem smul_mem_cont {G : Type*} [Group G] {A : Type*} [CommRing A]
    [TopologicalSpace A] [MulSemiringAction G A] [ContinuousConstSMul G A]
    {v : Spv A} (hv : v ∈ Cont A) (g : G) :
    g • v ∈ Cont A :=
  comap_isContinuous (continuous_const_smul g⁻¹) hv

/-- The induced `MulAction` of `G` on `↥(Cont A)`. -/
noncomputable instance instMulActionCont : MulAction G ↥(Cont A) where
  smul g v := ⟨g • v.1, smul_mem_cont (G := G) v.2 g⟩
  one_smul v := Subtype.ext (one_smul G v.1)
  mul_smul g h v := Subtype.ext (mul_smul g h v.1)

end GroupAction

/-! ### Group action preserves Spa membership -/

section SpaAction

variable (G : Type*) [Group G]
variable (A : Type*) [CommRing A] [TopologicalSpace A]
variable [MulSemiringAction G A] [ContinuousConstSMul G A] [PlusSubring A]

/-- The `G`-action on `Spv(A)` preserves `Spa(A, A⁺)` membership when `A⁺` is `G`-stable. -/
theorem smul_mem_spa (hstab : ∀ (g : G) (a : A), a ∈ A⁺ → g • a ∈ A⁺)
    {v : Spv A} (hv : v ∈ Spa A A⁺) (g : G) :
    g • v ∈ Spa A A⁺ := by
  refine ⟨smul_mem_cont (G := G) hv.1 g, fun f hf => ?_⟩
  change (comap (MulSemiringAction.toRingHom G A g⁻¹) v).vle f 1
  rw [comap_vle]
  simp only [MulSemiringAction.toRingHom, RingHom.coe_mk, map_one]
  exact hv.2 (g⁻¹ • f) (hstab g⁻¹ f hf)

end SpaAction

end ValuationSpectrum
