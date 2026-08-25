/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
import LeanPool.ConnesRigidity.Paper.Section6.Characteristic
import LeanPool.ConnesRigidity.Foundation.GroupTheory.Sp4KernelCertificate

/-!
This file proves the concrete characteristic-kernel transport needed by the
Zhou-shaped nonisomorphism argument. It is independently written from the
cited public mathematical source.
-/

namespace Connes
namespace PaperCharacteristicTransport

open Construction
open Construction.PaperKernel

noncomputable section

/--
The `N` construction used in the Connes rigidity formalization.
-/
abbrev N := Multiplicative PaperKernel.D
/--
The `S` construction used in the Connes rigidity formalization.
-/
abbrev S := SpecialLinear.SL3
/--
The `Q` construction used in the Connes rigidity formalization.
-/
abbrev Q := PaperKernel.Q
/--
The `H` construction used in the Connes rigidity formalization.
-/
abbrev H := S × Q

/- The kernel subgroup in a paper semidirect product (Zhou §6).
-/
/--
The `kernelSubgroup` construction used in the Connes rigidity formalization.
-/
def kernelSubgroup (action : H →* MulAut N) : Subgroup (PaperKernel.paperGammaCarrier action) :=
  (SemidirectProduct.inl (N := N) (G := H) (φ := action)).range

/- Commutativity descends through a surjective homomorphism (Zhou §6). -/
theorem mapCommutes
    {G M : Type*} [Group G] [Group M]
    (f : G →* M) (E : Subgroup G)
    (hcomm : ∀ x y : E, x * y = y * x) :
    ∀ x y : Subgroup.map f E, x * y = y * x := by
  intro x y
  rcases Subgroup.mem_map.mp x.property with ⟨a, ha, hax⟩
  rcases Subgroup.mem_map.mp y.property with ⟨b, hb, hby⟩
  apply Subtype.ext
  change (x : M) * (y : M) = (y : M) * (x : M)
  rw [← hax, ← hby]
  simpa using congrArg (fun z : E => f (z : G))
    (hcomm ⟨a, ha⟩ ⟨b, hb⟩)

/- The quotient image preserves normality and commutativity (Zhou §6). -/
theorem quotientImage_is_normal_commuting
    (action : H →* MulAut N) (E : Subgroup (PaperKernel.paperGammaCarrier action))
    (hnormal : E.Normal) (hcomm : ∀ x y : E, x * y = y * x) :
    let R := Subgroup.map SemidirectProduct.rightHom E
    R.Normal ∧ (∀ x y : R, x * y = y * x) := by
  dsimp
  constructor
  · exact hnormal.map _ SemidirectProduct.rightHom_surjective
  · exact mapCommutes _ _ hcomm

/- The linear quotient factor has no nontrivial abelian normal image (Zhou §6). -/
theorem sl3Image_is_bot
    (R : Subgroup H) (hnormal : R.Normal)
    (hcomm : ∀ x y : R, x * y = y * x) :
    Subgroup.map (MonoidHom.fst S Q) R = ⊥ := by
  apply PaperCharacteristic.paperSL3NoNontrivialAbelianNormalSubgroup
  · exact hnormal.map _ (by intro s; exact ⟨(s, 1), rfl⟩)
  · exact mapCommutes _ _ hcomm

/- The finite symplectic quotient factor has no such normal image (Zhou §6). -/
theorem qImage_is_bot
    (R : Subgroup H) (hnormal : R.Normal)
    (hcomm : ∀ x y : R, x * y = y * x) :
    Subgroup.map (MonoidHom.snd S Q) R = ⊥ := by
  apply Sp4.no_nontrivial_normal_abelian_subgroup
  · exact hnormal.map _ (by intro q; exact ⟨(1, q), rfl⟩)
  · exact mapCommutes _ _ hcomm

/- Every abelian normal subgroup is contained in the paper kernel (Zhou §6). -/
theorem paperSemidirectNormalAbelian_le_kernel
    (action : H →* MulAut N) (E : Subgroup (PaperKernel.paperGammaCarrier action))
    (hnormal : E.Normal) (hcomm : ∀ x y : E, x * y = y * x) :
    E ≤ kernelSubgroup action := by
  let R : Subgroup H := Subgroup.map SemidirectProduct.rightHom E
  have hRnormal : R.Normal := hnormal.map _ SemidirectProduct.rightHom_surjective
  have hRcomm : ∀ x y : R, x * y = y * x := mapCommutes _ _ hcomm
  have hS : Subgroup.map (MonoidHom.fst S Q) R = ⊥ :=
    sl3Image_is_bot R hRnormal hRcomm
  have hQ : Subgroup.map (MonoidHom.snd S Q) R = ⊥ :=
    qImage_is_bot R hRnormal hRcomm
  intro x hx
  rw [kernelSubgroup, SemidirectProduct.range_inl_eq_ker_rightHom]
  apply MonoidHom.mem_ker.mpr
  have hRx : (SemidirectProduct.rightHom : PaperKernel.paperGammaCarrier action →* H) x ∈ R := by
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hs : ((SemidirectProduct.rightHom : PaperKernel.paperGammaCarrier action →* H) x).1 = 1 := by
    have hm : ((SemidirectProduct.rightHom : PaperKernel.paperGammaCarrier action →* H) x).1 ∈
        Subgroup.map (MonoidHom.fst S Q) R := by
      exact Subgroup.mem_map.mpr ⟨_, hRx, rfl⟩
    rw [hS] at hm
    exact Subgroup.mem_bot.mp hm
  have hq : ((SemidirectProduct.rightHom : PaperKernel.paperGammaCarrier action →* H) x).2 = 1 := by
    have hm : ((SemidirectProduct.rightHom : PaperKernel.paperGammaCarrier action →* H) x).2 ∈
        Subgroup.map (MonoidHom.snd S Q) R := by
      exact Subgroup.mem_map.mpr ⟨_, hRx, rfl⟩
    rw [hQ] at hm
    exact Subgroup.mem_bot.mp hm
  change x.right = 1
  exact Prod.ext hs hq

/- The paper kernel is normal in its semidirect product (Zhou §6). -/
theorem kernelSubgroup_normal (action : H →* MulAut N) :
    (kernelSubgroup action).Normal := by
  rw [kernelSubgroup, SemidirectProduct.range_inl_eq_ker_rightHom]
  refine ⟨?_⟩
  intro n hn g
  apply MonoidHom.mem_ker.mpr
  change SemidirectProduct.rightHom (g * n * g⁻¹) = 1
  rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp hn]
  simp

/- The paper kernel is abelian in multiplicative coordinates (Zhou §6). -/
theorem kernelSubgroup_commuting (action : H →* MulAut N) :
    ∀ x y : kernelSubgroup action, x * y = y * x := by
  intro x y
  rcases MonoidHom.mem_range.mp x.property with ⟨a, hax⟩
  rcases MonoidHom.mem_range.mp y.property with ⟨b, hby⟩
  apply Subtype.ext
  change (x : PaperKernel.paperGammaCarrier action) * (y : PaperKernel.paperGammaCarrier action) =
    (y : PaperKernel.paperGammaCarrier action) * (x : PaperKernel.paperGammaCarrier action)
  rw [← hax, ← hby, ← map_mul, ← map_mul, mul_comm]

/- Group isomorphisms carry the paper kernel onto the paper kernel (Zhou §6). -/
theorem kernelSubgroup_characteristic
    (action₁ action₂ : H →* MulAut N)
    (f : PaperKernel.paperGammaCarrier action₁ ≃* PaperKernel.paperGammaCarrier action₂) :
    Subgroup.map f.toMonoidHom (kernelSubgroup action₁) =
      kernelSubgroup action₂ := by
  have hle : Subgroup.map f.toMonoidHom (kernelSubgroup action₁) ≤
      kernelSubgroup action₂ := by
    apply paperSemidirectNormalAbelian_le_kernel action₂
      (Subgroup.map f.toMonoidHom (kernelSubgroup action₁))
    · exact (kernelSubgroup_normal action₁).map _ f.surjective
    · exact mapCommutes _ _ (kernelSubgroup_commuting action₁)
  have hrev : Subgroup.map f.symm.toMonoidHom (kernelSubgroup action₂) ≤
      kernelSubgroup action₁ := by
    apply paperSemidirectNormalAbelian_le_kernel action₁
      (Subgroup.map f.symm.toMonoidHom (kernelSubgroup action₂))
    · exact (kernelSubgroup_normal action₂).map _ f.symm.surjective
    · exact mapCommutes _ _ (kernelSubgroup_commuting action₂)
  apply le_antisymm hle
  intro x hx
  have hpre : f.symm x ∈
      Subgroup.map f.symm.toMonoidHom (kernelSubgroup action₂) := by
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hk : f.symm x ∈ kernelSubgroup action₁ := hrev hpre
  exact Subgroup.mem_map.mpr ⟨f.symm x, hk, f.apply_symm_apply x⟩

end
end PaperCharacteristicTransport
end Connes
