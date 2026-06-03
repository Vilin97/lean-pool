/-
Copyright (c) 2026 Scott Harper, Peiran Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Harper, Peiran Wu
-/
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group

/-!
# LeanPool.OrderPQ.SemidirectProduct
-/

variable {N₁ N₂ H₁ H₂ : Type*} [Group N₁] [Group N₂] [Group H₁] [Group H₂]

variable {G : Type*} [Group G]

lemma Subgroup.comm_of_normal_and_inf_eq_bot
    (N H : Subgroup G) (hN : Subgroup.Normal N) (hH : Subgroup.Normal H)
    (inf_eq_bot : N ⊓ H = ⊥) (n : N) (h : H) :
    (n : G) * (h : G) = (h : G) * (n : G) := by
  have : (n : G) * h * (n⁻¹ : G) * (h : G)⁻¹ ∈ N ⊓ H := by
    refine mem_inf.mpr ⟨?_, ?_⟩
    · convert mul_mem (SetLike.coe_mem n) (hN.conj_mem _ (inv_mem (SetLike.coe_mem n)) h) using 1
      group
    · exact mul_mem (hH.conj_mem _ (SetLike.coe_mem _) _) (inv_mem (SetLike.coe_mem _))
  rwa [inf_eq_bot, Subgroup.mem_bot, mul_inv_eq_iff_eq_mul, one_mul, mul_inv_eq_iff_eq_mul] at this

/-- If `N` is a normal subgroup of `G` and `H` is a subgroup with `N ⊓ H = ⊥` and `N ⊔ H = ⊤`,
then `G` is isomorphic to the semidirect product `N ⋊[φ] H` for `φ` the conjugation action. -/
noncomputable def mulEquivSemidirectProduct
    {N H : Subgroup G} (h : Subgroup.Normal N) (inf_eq_bot : N ⊓ H = ⊥) (sup_eq_top : N ⊔ H = ⊤)
    {φ : H →* MulAut N} (conj : φ = MulAut.conjNormal.restrict H) :
    G ≃* N ⋊[φ] H := by
  let f : N ⋊[φ] H → G := fun x => x.1 * x.2
  have inj : f.Injective := by
    intro ⟨x1, x2⟩ ⟨y1, y2⟩ h
    have h12 : (y1 : G)⁻¹ * x1 = y2 * (x2 : G)⁻¹ := by
      rwa [eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul]
    have h1 : (y1 : G)⁻¹ * x1 ∈ N ⊓ H := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact mul_mem (inv_mem <| SetLike.coe_mem y1) (SetLike.coe_mem x1)
      · exact h12 ▸ mul_mem (SetLike.coe_mem y2) (inv_mem <| SetLike.coe_mem x2)
    rw [inf_eq_bot, Subgroup.mem_bot] at h1
    have h2 : y2 * (x2 : G)⁻¹ = 1 := h12 ▸ h1
    rw_mod_cast [inv_mul_eq_one.mp h1, mul_inv_eq_one.mp h2]
  have surj : f.Surjective := by
    intro x
    obtain ⟨n, hN, h, hH, hyp⟩ : ∃ n ∈ N, ∃ h ∈ H, n * h = x := by
      apply Set.mem_mul.mp
      rw [← Subgroup.normal_mul, sup_eq_top]
      exact Set.mem_univ x
    use ⟨⟨n, hN⟩, ⟨h, hH⟩⟩
  refine MulEquiv.ofBijective (MulHom.mk f ?_) ⟨inj, surj⟩ |>.symm
  · intro _ _
    simp only [f, conj, SemidirectProduct.mul_left, SemidirectProduct.mul_right, Subgroup.coe_mul,
      MonoidHom.restrict_apply, MulAut.conjNormal_apply]
    group

/-- If `H ≤ K` are subgroups of `G`, then `H.subgroupOf K` is canonically isomorphic to `H`. -/
@[simps]
def Subgroup.subgroupOfMulEquiv {G : Type*} [Group G] (H K : Subgroup G) (h : H ≤ K) :
    H.subgroupOf K ≃* H where
  toFun x := ⟨x.1.1, mem_subgroupOf.mp x.2⟩
  invFun x := ⟨⟨x.1, h x.2⟩, mem_subgroupOf.mpr <| SetLike.coe_mem ..⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[to_additive]
theorem Subgroup.subgroupOf_inf {H K L : Subgroup G} :
    (H ⊓ K).subgroupOf L = H.subgroupOf L ⊓ K.subgroupOf L :=
  comap_inf H K L.subtype

/-- Variant of `mulEquivSemidirectProduct` that works within the subgroup `N ⊔ H` rather than
requiring `N ⊔ H = ⊤`. -/
noncomputable def mulEquivSemidirectProduct'
    {N H : Subgroup G} (h : Subgroup.Normal N) (inf_eq_bot : N ⊓ H = ⊥)
    {φ : H →* MulAut N} (conj : φ = MulAut.conjNormal.restrict H) :
    (N ⊔ H : Subgroup G) ≃* N ⋊[φ] H := by
  set NH : Subgroup G := N ⊔ H
  let φ' : (H.subgroupOf NH) →* MulAut (N.subgroupOf NH) := MulAut.conjNormal.restrict _
  let fn : N ≃* (N.subgroupOf NH) := N.subgroupOfMulEquiv NH le_sup_left |>.symm
  let fh : H ≃* (H.subgroupOf NH) := H.subgroupOfMulEquiv NH le_sup_right |>.symm
  refine (mulEquivSemidirectProduct (φ := φ') (by infer_instance) ?_ ?_ rfl).trans
    (MulEquiv.symm ?_)
  · rw [Subgroup.subgroupOf_inf.symm, inf_eq_bot, Subgroup.bot_subgroupOf]
  · rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]; simp [NH]
  · refine SemidirectProduct.congr fn fh fun h =>
      MulEquiv.ext fun n => Subtype.ext <| Subtype.ext ?_
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MonoidHom.restrict_apply,
      MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_mul, InvMemClass.coe_inv, conj]
    repeat rw [Subgroup.subgroupOfMulEquiv_symm_apply_coe_coe]
    rw [MonoidHom.restrict_apply, MulAut.conjNormal_apply]

/-- If `N` and `H` are normal subgroups of `G` with trivial intersection that span `G`,
then `G` is isomorphic to the direct product `N × H`. -/
noncomputable def mulEquivProd
    {N H : Subgroup G} (hN : Subgroup.Normal N) (hH : Subgroup.Normal H)
    (inf_eq_bot : N ⊓ H = ⊥) (sup_eq_top : N ⊔ H = ⊤) :
    G ≃* N × H := by
  refine MulEquiv.trans (mulEquivSemidirectProduct hN inf_eq_bot sup_eq_top rfl) ?_
  have : MulAut.conjNormal.restrict H = (1 : H →* MulAut N) := by
    ext
    simp [← Subgroup.comm_of_normal_and_inf_eq_bot N H hN hH inf_eq_bot]
  exact this ▸ SemidirectProduct.mulEquivProd
