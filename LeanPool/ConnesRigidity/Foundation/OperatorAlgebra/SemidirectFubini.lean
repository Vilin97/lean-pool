/-
Copyright (c) 2026 Utensil Song, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song, OpenAI
-/
/-

Derived in part from Apache-2.0 `openai/ten-proofs`, `ConnesRigidity.lean` at
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, lines 34960-35158.
Modifications: extracted the semidirect-product coordinate unitary and changed
imports and namespace. Paper: §3. See the upstream PORT_MAP.md.
-/
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Topology.Separation.CompletelyRegular
import LeanPool.ConnesRigidity.Porting.CoreTransfer

/-!
The semidirect fubini component of the Connes rigidity formalization.
-/

namespace Connes
namespace SemidirectFubini

open scoped ENNReal

noncomputable section

universe u v

/- The curry map is the discrete ℓ² Fubini equivalence used for the fibres.
Paper: §3. -/
private def l2CurryFiber {ι : Type u} {κ : Type v}
    (ξ : GroupL2 (ι × κ)) (i : ι) : GroupL2 κ :=
  ⟨fun k => ξ (i, k), by
    change Memℓp (fun k => ξ (i, k)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    exact ((lp.memℓp ξ).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).prod_factor i⟩

private theorem l2Curry_mem {ι : Type u} {κ : Type v}
    (ξ : GroupL2 (ι × κ)) :
    (fun i => l2CurryFiber ξ i) ∈ lp (fun _ : ι => GroupL2 κ) 2 := by
  change Memℓp (fun i => l2CurryFiber ξ i) 2
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  have hprod : Summable (fun p : ι × κ =>
      ‖ξ p‖ ^ (2 : ℝ≥0∞).toReal) :=
    (lp.memℓp ξ).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  apply hprod.prod.congr
  intro i
  rw [lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  rfl

private theorem l2Uncurry_mem {ι : Type u} {κ : Type v}
    (ξ : lp (fun _ : ι => GroupL2 κ) 2) :
    (fun p : ι × κ => ξ p.1 p.2) ∈ GroupL2 (ι × κ) := by
  change Memℓp (fun p : ι × κ => ξ p.1 p.2) 2
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  apply (summable_prod_of_nonneg (fun _ => by positivity)).2
  constructor
  · intro i
    exact (lp.memℓp (ξ i)).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  · have hout : Summable (fun i =>
        ‖ξ i‖ ^ (2 : ℝ≥0∞).toReal) :=
      (lp.memℓp ξ).summable
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    convert hout using 1
    funext i
    rw [lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]

/- The discrete Fubini equivalence itself.  Its proof is the same norm
calculation as the public source, with the surrounding paper APIs omitted.
Paper: §3.
-/
/--
The `l2Curry` construction used in the Connes rigidity formalization.
-/
def l2Curry (ι : Type u) (κ : Type v) :
    GroupL2 (ι × κ) ≃ₗᵢ[ℂ] lp (fun _ : ι => GroupL2 κ) 2 where
  toLinearEquiv :=
    { toFun := fun ξ => ⟨fun i => l2CurryFiber ξ i, l2Curry_mem ξ⟩
      invFun := fun ξ => ⟨fun p => ξ p.1 p.2, l2Uncurry_mem ξ⟩
      left_inv := by
        intro ξ
        ext p
        rfl
      right_inv := by
        intro ξ
        ext i k
        rfl
      map_add' := by
        intro ξ η
        ext i k
        rfl
      map_smul' := by
        intro c ξ
        ext i k
        rfl }
  norm_map' := by
    intro ξ
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    change
      (∑' i, ‖l2CurryFiber ξ i‖ ^ (2 : ℝ≥0∞).toReal) ^
          (1 / (2 : ℝ≥0∞).toReal) =
        (∑' p, ‖ξ p‖ ^ (2 : ℝ≥0∞).toReal) ^
          (1 / (2 : ℝ≥0∞).toReal)
    congr 1
    have hprod : Summable (fun p : ι × κ =>
        ‖ξ p‖ ^ (2 : ℝ≥0∞).toReal) :=
      (lp.memℓp ξ).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    rw [hprod.tsum_prod]
    apply tsum_congr
    intro i
    rw [lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    rfl

@[simp] theorem l2Curry_apply {ι : Type u} {κ : Type v}
    (ξ : GroupL2 (ι × κ)) (i : ι) (k : κ) :
    l2Curry ι κ ξ i k = ξ (i, k) := rfl

@[simp] theorem l2Curry_symm_apply {ι : Type u} {κ : Type v}
    (ξ : lp (fun _ : ι => GroupL2 κ) 2) (i : ι) (k : κ) :
    (l2Curry ι κ).symm ξ (i, k) = ξ i k := rfl

variable {A : Type u} {K : Type v} [Group A] [Group K]

/-- The semidirect product is identified with quotient-indexed kernel fibres.
Paper: §3.
-/
def semidirectFubiniCoordinates (φ : K →* MulAut A) :
    SemidirectProduct A K φ ≃ K × A :=
  SemidirectProduct.equivProd.trans (Equiv.prodComm A K)

@[simp] theorem semidirectFubiniCoordinates_apply
    (φ : K →* MulAut A) (g : SemidirectProduct A K φ) :
    semidirectFubiniCoordinates φ g = (g.right, g.left) := rfl

/-- The semidirect-product ℓ² carrier in fibre coordinates.  Ported from the
public OpenAI construction, then kept local to Zhou's §3 model.
-/
def semidirectFubini (φ : K →* MulAut A) :
    GroupL2 (SemidirectProduct A K φ) ≃ₗᵢ[ℂ]
      lp (fun _ : K => GroupL2 A) 2 :=
  (l2Reindex (semidirectFubiniCoordinates φ)).trans (l2Curry K A)

@[simp] theorem semidirectFubini_apply
    (φ : K →* MulAut A)
    (ξ : GroupL2 (SemidirectProduct A K φ)) (k : K) (a : A) :
    semidirectFubini φ ξ k a =
      ξ (⟨a, k⟩ : SemidirectProduct A K φ) := rfl

@[simp] theorem semidirectFubini_symm_apply
    (φ : K →* MulAut A)
    (ξ : lp (fun _ : K => GroupL2 A) 2)
    (a : A) (k : K) :
    (semidirectFubini φ).symm ξ (⟨a, k⟩ : SemidirectProduct A K φ) =
      ξ k a := rfl

/- Regular translation in fibre coordinates.  This is the key carrier bridge
for the inl and inr generator calculations.  Paper: §3. -/
theorem semidirectFubini_leftRegular_apply
    (φ : K →* MulAut A)
    (g : SemidirectProduct A K φ)
    (ξ : GroupL2 (SemidirectProduct A K φ))
    (k : K) (a : A) :
    semidirectFubini φ
        ((leftRegularUnitary g :
          GroupL2 (SemidirectProduct A K φ) →L[ℂ]
            GroupL2 (SemidirectProduct A K φ)) ξ) k a =
      semidirectFubini φ ξ (g.right⁻¹ * k)
        (φ g.right⁻¹ (g.left⁻¹ * a)) := by
  change ξ ⟨φ g.right⁻¹ g.left⁻¹ * φ g.right⁻¹ a,
    g.right⁻¹ * k⟩ = ξ ⟨φ g.right⁻¹ (g.left⁻¹ * a),
    g.right⁻¹ * k⟩
  rw [map_mul]

theorem semidirectFubini_leftRegular_inl_apply
    (φ : K →* MulAut A) (b : A)
    (ξ : GroupL2 (SemidirectProduct A K φ))
    (k : K) (a : A) :
    semidirectFubini φ
        ((leftRegularUnitary
          (SemidirectProduct.inl b : SemidirectProduct A K φ) :
          GroupL2 (SemidirectProduct A K φ) →L[ℂ]
            GroupL2 (SemidirectProduct A K φ)) ξ) k a =
      semidirectFubini φ ξ k (b⁻¹ * a) := by
  simpa only [semidirectFubini_apply, OpenAIPort.leftRegularUnitary_apply,
    SemidirectProduct.mk_eq_inl_mul_inr, map_mul, map_inv,
    SemidirectProduct.right_inl, inv_one, one_mul, SemidirectProduct.left_inl,
    map_one, MulAut.one_apply] using semidirectFubini_leftRegular_apply φ
    (SemidirectProduct.inl b) ξ k a

theorem semidirectFubini_leftRegular_inr_apply
    (φ : K →* MulAut A) (h : K)
    (ξ : GroupL2 (SemidirectProduct A K φ))
    (k : K) (a : A) :
    semidirectFubini φ
        ((leftRegularUnitary
          (SemidirectProduct.inr h : SemidirectProduct A K φ) :
          GroupL2 (SemidirectProduct A K φ) →L[ℂ]
            GroupL2 (SemidirectProduct A K φ)) ξ) k a =
      semidirectFubini φ ξ (h⁻¹ * k) (φ h⁻¹ a) := by
  simpa only [semidirectFubini_apply, OpenAIPort.leftRegularUnitary_apply,
    SemidirectProduct.mk_eq_inl_mul_inr, map_inv, MulAut.inv_apply, map_mul,
    SemidirectProduct.right_inr, SemidirectProduct.left_inr, inv_one, one_mul]
    using semidirectFubini_leftRegular_apply φ
      (SemidirectProduct.inr h) ξ k a

/- The conjugated regular operator has the same pointwise fibre formula.
Paper: §3. -/
theorem semidirectFubini_conj_leftRegular_apply
    (φ : K →* MulAut A)
    (g : SemidirectProduct A K φ)
    (ξ : lp (fun _ : K => GroupL2 A) 2)
    (k : K) (a : A) :
    ((semidirectFubini φ).conjStarAlgEquiv
      (leftRegularUnitary g :
        GroupL2 (SemidirectProduct A K φ) →L[ℂ]
          GroupL2 (SemidirectProduct A K φ))) ξ k a =
      ξ (g.right⁻¹ * k) (φ g.right⁻¹ (g.left⁻¹ * a)) := by
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    semidirectFubini_leftRegular_apply,
    LinearIsometryEquiv.apply_symm_apply]

theorem semidirectFubini_leftRegular_inl
    (φ : K →* MulAut A) (b : A)
    (ξ : lp (fun _ : K => GroupL2 A) 2)
    (k : K) (a : A) :
    ((semidirectFubini φ).conjStarAlgEquiv
      (leftRegularUnitary
        (SemidirectProduct.inl b : SemidirectProduct A K φ) :
          GroupL2 (SemidirectProduct A K φ) →L[ℂ]
            GroupL2 (SemidirectProduct A K φ))) ξ k a =
      ξ k (b⁻¹ * a) := by
  simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    semidirectFubini_apply, OpenAIPort.leftRegularUnitary_apply,
    SemidirectProduct.mk_eq_inl_mul_inr, SemidirectProduct.right_inl,
    inv_one, one_mul, SemidirectProduct.left_inl, map_one,
    MulAut.one_apply] using semidirectFubini_conj_leftRegular_apply φ
    (SemidirectProduct.inl b) ξ k a

theorem semidirectFubini_leftRegular_inr
    (φ : K →* MulAut A) (h : K)
    (ξ : lp (fun _ : K => GroupL2 A) 2)
    (k : K) (a : A) :
    ((semidirectFubini φ).conjStarAlgEquiv
      (leftRegularUnitary
        (SemidirectProduct.inr h : SemidirectProduct A K φ) :
          GroupL2 (SemidirectProduct A K φ) →L[ℂ]
            GroupL2 (SemidirectProduct A K φ))) ξ k a =
      ξ (h⁻¹ * k) (φ h⁻¹ a) := by
  simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    semidirectFubini_apply, OpenAIPort.leftRegularUnitary_apply,
    SemidirectProduct.mk_eq_inl_mul_inr, map_inv, MulAut.inv_apply,
    SemidirectProduct.right_inr, SemidirectProduct.left_inr, inv_one, one_mul]
    using semidirectFubini_conj_leftRegular_apply φ
      (SemidirectProduct.inr h) ξ k a

end
end SemidirectFubini
end Connes
