/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
import LeanPool.ConnesRigidity.Paper.Section6.CharacteristicTransport
import LeanPool.ConnesRigidity.Paper.Section6.Nonisomorphism
import LeanPool.ConnesRigidity.Foundation.GroupTheory.SpecialLinear.ICC

/-!
This file proves the concrete quotient and module transport in Zhou's
Section 6 argument. It uses public project statements only.
-/

namespace Connes
namespace PaperCharacteristicTransport

open Construction
open Construction.PaperKernel
open PaperNonisomorphism

noncomputable section

/- The finite quotient factor inside the product acting group (Zhou §6).
-/
/--
The `qSubgroup` construction used in the Connes rigidity formalization.
-/
def qSubgroup : Subgroup H := (MonoidHom.fst S Q).ker

/-- The quotient factor is normal as a direct-product kernel (Zhou §6). -/
theorem qSubgroup_normal : qSubgroup.Normal := by
  rw [qSubgroup]
  refine ⟨?_⟩
  intro n hn g
  apply MonoidHom.mem_ker.mpr
  rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp hn]
  simp

/- The quotient kernel has the expected finite-factor presentation (Zhou §6). -/
theorem qSubgroup_eq_range :
    qSubgroup = (MonoidHom.inr S Q).range := by
  ext x
  constructor
  · intro hx
    have hs : x.1 = 1 := MonoidHom.mem_ker.mp hx
    exact MonoidHom.mem_range.mpr ⟨x.2, by
      apply Prod.ext
      · exact hs.symm
      · rfl⟩
  · intro hx
    obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp hx
    apply MonoidHom.mem_ker.mpr
    rw [← hq]
    rfl

/- The quotient factor is finite (Zhou §6). -/
theorem qSubgroup_finite : (qSubgroup : Set H).Finite := by
  rw [qSubgroup_eq_range]
  rw [show ((MonoidHom.inr S Q).range : Set H) =
      Set.range (MonoidHom.inr S Q) by rfl]
  rw [← Set.image_univ]
  exact Set.Finite.image _ (Set.toFinite _)

/- Finite normal subgroups of the ICC linear factor vanish (Zhou §6). -/
theorem finiteNormalSubgroup_sl3_bot
    (L : Subgroup S) (hfinite : (L : Set S).Finite)
    (hnormal : L.Normal) : L = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hne
  have hxne : (x : S) ≠ 1 := by
    intro h
    apply hne
    simpa using h
  have hICC := (SpecialLinear.sl3_isICC).2 (x : S) hxne
  have hsubset : conjugatesOf (x : SpecialLinear.sl3Group) ⊆
      (L : Set S) := by
    rintro y hy
    obtain ⟨g, rfl⟩ := isConj_iff.mp hy
    exact hnormal.conj_mem x hx g
  exact (hfinite.subset hsubset).not_infinite hICC

/- Finite normal subgroups of the product lie in its finite factor (Zhou §6). -/
theorem finiteNormalSubgroup_le_q
    (R : Subgroup H) (hfinite : (R : Set H).Finite)
    (hnormal : R.Normal) : R ≤ qSubgroup := by
  have hSnormal : (Subgroup.map (MonoidHom.fst S Q) R).Normal :=
    hnormal.map _ (by intro s; exact ⟨(s, 1), rfl⟩)
  have hSfinite :
      ((Subgroup.map (MonoidHom.fst S Q) R : Subgroup S) : Set S).Finite := by
    rw [Subgroup.coe_map]
    exact hfinite.image _
  have hS : Subgroup.map (MonoidHom.fst S Q) R = ⊥ :=
    finiteNormalSubgroup_sl3_bot _ hSfinite hSnormal
  intro x hx
  apply MonoidHom.mem_ker.mpr
  have hm : x.1 ∈ Subgroup.map (MonoidHom.fst S Q) R := by
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  rw [hS] at hm
  exact Subgroup.mem_bot.mp hm

/- The finite quotient factor is characteristic in the product (Zhou §6). -/
theorem qSubgroup_characteristic (f : H ≃* H) :
    Subgroup.map f.toMonoidHom qSubgroup = qSubgroup := by
  have hle : Subgroup.map f.toMonoidHom qSubgroup ≤ qSubgroup :=
    finiteNormalSubgroup_le_q _
      (qSubgroup_finite.image f)
      (qSubgroup_normal.map _ f.surjective)
  have hrev : Subgroup.map f.symm.toMonoidHom qSubgroup ≤ qSubgroup :=
    finiteNormalSubgroup_le_q _
      (qSubgroup_finite.image f.symm)
      (qSubgroup_normal.map _ f.symm.surjective)
  apply le_antisymm hle
  intro x hx
  have hpre : f.symm x ∈ Subgroup.map f.symm.toMonoidHom qSubgroup := by
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hq : f.symm x ∈ qSubgroup := hrev hpre
  exact Subgroup.mem_map.mpr ⟨f.symm x, hq, f.apply_symm_apply x⟩

/- Coordinates identify the finite quotient with its subgroup (Zhou §6).
-/
/--
The `qSubgroupEquiv` construction used in the Connes rigidity formalization.
-/
def qSubgroupEquiv : Q ≃* qSubgroup where
  toFun q := ⟨(1, q), by
    apply MonoidHom.mem_ker.mpr
    rfl⟩
  invFun x := x.1.2
  left_inv q := rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · exact (MonoidHom.mem_ker.mp x.property).symm
    · rfl
  map_mul' p q := by
    apply Subtype.ext
    simp

/-- A group isomorphism restricts to an invariant subgroup (Zhou §6).
-/
def restrictEquiv
    {G M : Type*} [Group G] [Group M]
    (f : G ≃* M) {K : Subgroup G} {L : Subgroup M}
    (h : Subgroup.map f.toMonoidHom K = L) : K ≃* L where
  toFun x := ⟨f x, by
    rw [← h]
    exact Subgroup.mem_map.mpr ⟨x, x.property, rfl⟩⟩
  invFun y := ⟨f.symm y, by
    have hy : (y : M) ∈ Subgroup.map f.toMonoidHom K := by
      rw [h]
      exact y.property
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    have hsymm : x = f.symm y := by
      rw [← hxy]
      simp
    rw [← hsymm]
    exact hx⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp

/-- The quotient homomorphism induced by a semidirect-product isomorphism (Zhou §6).
-/
def quotientMap
    (action₁ action₂ : H →* MulAut N)
    (f : PaperKernel.paperGammaCarrier action₁ ≃* PaperKernel.paperGammaCarrier action₂) : H →* H :=
  (SemidirectProduct.rightHom (N := N) (G := H) (φ := action₂)).comp
    (f.toMonoidHom.comp
      (SemidirectProduct.inr (N := N) (G := H) (φ := action₁)))

/-- Every semidirect element splits into kernel and quotient coordinates (Zhou §6). -/
theorem semidirect_decompose
    (action : H →* MulAut N) (x : PaperKernel.paperGammaCarrier action) :
    x = SemidirectProduct.inl x.left * SemidirectProduct.inr x.right := by
  apply SemidirectProduct.ext
  · simp
  · simp

/- The induced quotient map agrees with the right coordinate (Zhou §6). -/
theorem quotientMap_apply_right
    (action₁ action₂ : H →* MulAut N)
    (f : PaperKernel.paperGammaCarrier action₁ ≃* PaperKernel.paperGammaCarrier action₂)
    (hchar : Subgroup.map f.toMonoidHom (kernelSubgroup action₁) =
      kernelSubgroup action₂)
    (x : PaperKernel.paperGammaCarrier action₁) :
    quotientMap action₁ action₂ f x.right = (f x).right := by
  have hkernel : f (SemidirectProduct.inl x.left) ∈
      kernelSubgroup action₂ := by
    rw [← hchar]
    exact Subgroup.mem_map.mpr ⟨SemidirectProduct.inl x.left,
      MonoidHom.mem_range.mpr ⟨x.left, rfl⟩, rfl⟩
  have hright : (f (SemidirectProduct.inl x.left)).right = 1 := by
    rw [kernelSubgroup, SemidirectProduct.range_inl_eq_ker_rightHom] at hkernel
    exact MonoidHom.mem_ker.mp hkernel
  change (f (SemidirectProduct.inr x.right)).right = (f x).right
  have hdecomp : f x = f (SemidirectProduct.inl x.left) *
      f (SemidirectProduct.inr x.right) := by
    calc
      f x = f (SemidirectProduct.inl x.left *
          SemidirectProduct.inr x.right) :=
        congrArg f (semidirect_decompose action₁ x)
      _ = f (SemidirectProduct.inl x.left) *
          f (SemidirectProduct.inr x.right) := by rw [map_mul]
  rw [hdecomp]
  simp only [SemidirectProduct.mul_right, hright, one_mul]

/- The quotient homomorphism induced by an isomorphism is invertible (Zhou §6).
-/
/--
The `quotientEquiv` construction used in the Connes rigidity formalization.
-/
def quotientEquiv
    (action₁ action₂ : H →* MulAut N)
    (f : PaperKernel.paperGammaCarrier action₁ ≃* PaperKernel.paperGammaCarrier action₂)
    (hchar : Subgroup.map f.toMonoidHom (kernelSubgroup action₁) =
      kernelSubgroup action₂) : H ≃* H where
  toFun := quotientMap action₁ action₂ f
  invFun := quotientMap action₂ action₁ f.symm
  left_inv h := by
    have hcharsymm : Subgroup.map f.symm.toMonoidHom (kernelSubgroup action₂) =
        kernelSubgroup action₁ := kernelSubgroup_characteristic action₂ action₁ f.symm
    have hqh : quotientMap action₁ action₂ f h =
        (f (SemidirectProduct.inr h)).right := by
      simpa using quotientMap_apply_right action₁ action₂ f hchar
        (SemidirectProduct.inr h)
    calc
      quotientMap action₂ action₁ f.symm (quotientMap action₁ action₂ f h) =
          quotientMap action₂ action₁ f.symm (f (SemidirectProduct.inr h)).right := by
            rw [hqh]
      _ = (f.symm (f (SemidirectProduct.inr h))).right := by
            exact quotientMap_apply_right action₂ action₁ f.symm hcharsymm
              (f (SemidirectProduct.inr h))
      _ = h := by simp
  right_inv h := by
    have hcharsymm : Subgroup.map f.symm.toMonoidHom (kernelSubgroup action₂) =
        kernelSubgroup action₁ := kernelSubgroup_characteristic action₂ action₁ f.symm
    have hqh : quotientMap action₂ action₁ f.symm h =
        (f.symm (SemidirectProduct.inr h)).right := by
      simpa using quotientMap_apply_right action₂ action₁ f.symm hcharsymm
        (SemidirectProduct.inr h)
    calc
      quotientMap action₁ action₂ f (quotientMap action₂ action₁ f.symm h) =
          quotientMap action₁ action₂ f (f.symm (SemidirectProduct.inr h)).right := by
            rw [hqh]
      _ = (f (f.symm (SemidirectProduct.inr h))).right := by
            exact quotientMap_apply_right action₁ action₂ f hchar
              (f.symm (SemidirectProduct.inr h))
      _ = h := by simp
  map_mul' := by
    intro x y
    exact map_mul (quotientMap action₁ action₂ f) x y

/-- The induced quotient automorphism restricts to the finite factor (Zhou §6).
-/
def quotientAutomorphism
    (action₁ action₂ : H →* MulAut N)
    (f : PaperKernel.paperGammaCarrier action₁ ≃* PaperKernel.paperGammaCarrier action₂)
    (hchar : Subgroup.map f.toMonoidHom (kernelSubgroup action₁) =
      kernelSubgroup action₂) : Q ≃* Q :=
  let ψ := quotientEquiv action₁ action₂ f hchar
  qSubgroupEquiv.trans
    ((restrictEquiv ψ (qSubgroup_characteristic ψ)).trans qSubgroupEquiv.symm)

/-- Coordinates identify the kernel with the semidirect kernel subgroup (Zhou §6).
-/
def kernelSubgroupEquiv (action : H →* MulAut N) :
    N ≃* kernelSubgroup action where
  toFun n := ⟨SemidirectProduct.inl n,
    MonoidHom.mem_range.mpr ⟨n, rfl⟩⟩
  invFun x := x.1.left
  left_inv n := rfl
  right_inv x := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · have hxker : x.1 ∈
          (SemidirectProduct.rightHom (N := N) (G := H)
            (φ := action)).ker := by
          rw [← SemidirectProduct.range_inl_eq_ker_rightHom]
          exact x.property
      change 1 = x.1.right
      exact (MonoidHom.mem_ker.mp hxker).symm
  map_mul' x y := by
    apply Subtype.ext
    simp
/-- The kernel map induced by a group isomorphism (Zhou §6).
-/
def kernelMap
    (action₁ action₂ : H →* MulAut N)
    (f : PaperKernel.paperGammaCarrier action₁ ≃* PaperKernel.paperGammaCarrier action₂)
    (hchar : Subgroup.map f.toMonoidHom (kernelSubgroup action₁) =
      kernelSubgroup action₂) : N ≃* N :=
  (kernelSubgroupEquiv action₁).trans
    ((restrictEquiv f hchar).trans (kernelSubgroupEquiv action₂).symm)

/-- The kernel map is read from the kernel coordinate (Zhou §6). -/
theorem kernelMap_apply_left
    (action₁ action₂ : H →* MulAut N)
    (f : PaperKernel.paperGammaCarrier action₁ ≃* PaperKernel.paperGammaCarrier action₂)
    (hchar : Subgroup.map f.toMonoidHom (kernelSubgroup action₁) =
      kernelSubgroup action₂) (n : N) :
    kernelMap action₁ action₂ f hchar n =
      (f (SemidirectProduct.inl n)).left := by
  rfl

/- The kernel map commutes with kernel inclusion (Zhou §6). -/
theorem kernelMap_inl
    (action₁ action₂ : H →* MulAut N)
    (f : PaperKernel.paperGammaCarrier action₁ ≃* PaperKernel.paperGammaCarrier action₂)
    (hchar : Subgroup.map f.toMonoidHom (kernelSubgroup action₁) =
      kernelSubgroup action₂) (n : N) :
    SemidirectProduct.inl (kernelMap action₁ action₂ f hchar n) =
      f (SemidirectProduct.inl n) := by
  apply SemidirectProduct.ext
  · rfl
  · have hk : f (SemidirectProduct.inl n) ∈ kernelSubgroup action₂ := by
      rw [← hchar]
      exact Subgroup.mem_map.mpr ⟨SemidirectProduct.inl n,
        MonoidHom.mem_range.mpr ⟨n, rfl⟩, rfl⟩
    have hk' : f (SemidirectProduct.inl n) ∈
        (SemidirectProduct.rightHom (N := N) (G := H)
          (φ := action₂)).ker := by
      rw [← SemidirectProduct.range_inl_eq_ker_rightHom]
      exact hk
    change 1 = (f (SemidirectProduct.inl n)).right
    exact (MonoidHom.mem_ker.mp hk').symm

/- An abelian kernel coordinate does not affect quotient conjugation (Zhou §6). -/
theorem inl_conjugation_ignores_kernel
    (action : H →* MulAut N) (a n : N) (h : H) :
    ((SemidirectProduct.inl a : PaperKernel.paperGammaCarrier action) *
        SemidirectProduct.inr h) * SemidirectProduct.inl n *
          ((SemidirectProduct.inl a : PaperKernel.paperGammaCarrier action) *
            SemidirectProduct.inr h)⁻¹ =
      (SemidirectProduct.inr h : PaperKernel.paperGammaCarrier action) *
        SemidirectProduct.inl n * SemidirectProduct.inr h⁻¹ := by
  have hinvr : (SemidirectProduct.inr h : PaperKernel.paperGammaCarrier action)⁻¹ =
      SemidirectProduct.inr h⁻¹ := by
    exact (map_inv (SemidirectProduct.inr (N := N) (G := H)
      (φ := action)) h).symm
  calc
    _ = (SemidirectProduct.inl a : PaperKernel.paperGammaCarrier action) *
        ((SemidirectProduct.inr h : PaperKernel.paperGammaCarrier action) *
          SemidirectProduct.inl n * SemidirectProduct.inr h⁻¹) *
            (SemidirectProduct.inl a : PaperKernel.paperGammaCarrier action)⁻¹ := by
              rw [← hinvr]
              group
    _ = (SemidirectProduct.inl a : PaperKernel.paperGammaCarrier action) *
        SemidirectProduct.inl (action h n) *
          (SemidirectProduct.inl a : PaperKernel.paperGammaCarrier action)⁻¹ := by
            rw [SemidirectProduct.inl_aut]
    _ = SemidirectProduct.inl (action h n) := by
      have hinv : (SemidirectProduct.inl a : PaperKernel.paperGammaCarrier action)⁻¹ =
          SemidirectProduct.inl a⁻¹ := by
        exact (map_inv (SemidirectProduct.inl (φ := action)) a).symm
      rw [hinv, ← map_mul, ← map_mul]
      congr 1
      rw [mul_assoc, mul_comm (action h n) a⁻¹, ← mul_assoc]
      calc
        a * a⁻¹ * (action h n) = (a * a⁻¹) * (action h n) := by rfl
        _ = 1 * (action h n) :=
          congrArg (fun z : N => z * (action h n)) (mul_inv_cancel a)
        _ = _ := one_mul _
    _ = _ := SemidirectProduct.inl_aut (φ := action) h n

/- The group isomorphism transports the semidirect action (Zhou §6). -/
theorem kernelMap_intertwines
    (action₁ action₂ : H →* MulAut N)
    (f : PaperKernel.paperGammaCarrier action₁ ≃* PaperKernel.paperGammaCarrier action₂)
    (hchar : Subgroup.map f.toMonoidHom (kernelSubgroup action₁) =
      kernelSubgroup action₂) (h : H) (n : N) :
    kernelMap action₁ action₂ f hchar (action₁ h n) =
      action₂ (quotientEquiv action₁ action₂ f hchar h)
        (kernelMap action₁ action₂ f hchar n) := by
  apply (SemidirectProduct.inl_injective (φ := action₂))
  change SemidirectProduct.inl
      (kernelMap action₁ action₂ f hchar (action₁ h n)) =
    SemidirectProduct.inl
      (action₂ (quotientMap action₁ action₂ f h)
        (kernelMap action₁ action₂ f hchar n))
  rw [SemidirectProduct.inl_aut (φ := action₂)
    (quotientMap action₁ action₂ f h)
    (kernelMap action₁ action₂ f hchar n)]
  rw [kernelMap_inl]
  rw [SemidirectProduct.inl_aut (φ := action₁) h n]
  rw [map_mul, map_inv]
  have hdecomp : f (SemidirectProduct.inr h) =
      SemidirectProduct.inl (f (SemidirectProduct.inr h)).left *
        SemidirectProduct.inr (quotientMap action₁ action₂ f h) := by
    have hq : quotientMap action₁ action₂ f h =
        (f (SemidirectProduct.inr h)).right := by
      simpa using quotientMap_apply_right action₁ action₂ f hchar
        (SemidirectProduct.inr h)
    calc
      f (SemidirectProduct.inr h) =
          SemidirectProduct.inl (f (SemidirectProduct.inr h)).left *
            SemidirectProduct.inr (f (SemidirectProduct.inr h)).right :=
        semidirect_decompose action₂ (f (SemidirectProduct.inr h))
      _ = SemidirectProduct.inl (f (SemidirectProduct.inr h)).left *
            SemidirectProduct.inr (quotientMap action₁ action₂ f h) := by
        rw [hq]
  rw [map_mul]
  rw [map_inv f (SemidirectProduct.inr h)]
  change f (SemidirectProduct.inr h) * f (SemidirectProduct.inl n) *
      (f (SemidirectProduct.inr h))⁻¹ = _
  have hdecomp_inv :
      (f (SemidirectProduct.inr h))⁻¹ =
        (SemidirectProduct.inl (f (SemidirectProduct.inr h)).left *
          SemidirectProduct.inr (quotientMap action₁ action₂ f h))⁻¹ := by
    exact congrArg Inv.inv hdecomp
  rw [hdecomp_inv]
  nth_rewrite 1 [hdecomp]
  rw [← kernelMap_inl action₁ action₂ f hchar n]
  have hconj := inl_conjugation_ignores_kernel action₂
    (f (SemidirectProduct.inr h)).left
    (kernelMap action₁ action₂ f hchar n)
    (quotientMap action₁ action₂ f h)
  exact hconj

/- The transported kernel group map is linear over the Boolean field (Zhou §6).
-/
/--
The `kernelLinearEquiv` construction used in the Connes rigidity formalization.
-/
def kernelLinearEquiv
    (action₁ action₂ : H →* MulAut N)
    (f : PaperKernel.paperGammaCarrier action₁ ≃* PaperKernel.paperGammaCarrier action₂)
    (hchar : Subgroup.map f.toMonoidHom (kernelSubgroup action₁) =
      kernelSubgroup action₂) : PaperKernel.D ≃ₗ[k] PaperKernel.D := by
  let e : PaperKernel.D ≃+ PaperKernel.D := AddEquiv.toMultiplicative.symm
    (kernelMap action₁ action₂ f hchar)
  exact e.toLinearEquiv (by
    intro c d
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl
    · rw [zero_smul, zero_smul, map_zero]
    · rw [one_smul, one_smul])

/-- The transported linear kernel map respects the paper actions (Zhou §6). -/
theorem kernelLinearEquiv_intertwines
    (f : PaperKernel.paperGammaCarrier PaperKernel.paperThetaOneHom ≃*
      PaperKernel.paperGammaCarrier PaperKernel.paperThetaTwoHom)
    (hchar : Subgroup.map f.toMonoidHom
        (kernelSubgroup PaperKernel.paperThetaOneHom) =
      kernelSubgroup PaperKernel.paperThetaTwoHom) (h : H)
      (d : PaperKernel.D) :
    kernelLinearEquiv PaperKernel.paperThetaOneHom
        PaperKernel.paperThetaTwoHom f hchar
        (PaperKernel.paperThetaOneLinearHom h d) =
      PaperKernel.paperThetaTwoLinearHom
        (quotientEquiv PaperKernel.paperThetaOneHom
          PaperKernel.paperThetaTwoHom f hchar h)
        (kernelLinearEquiv PaperKernel.paperThetaOneHom
          PaperKernel.paperThetaTwoHom f hchar d) := by
  have hk := kernelMap_intertwines PaperKernel.paperThetaOneHom
    PaperKernel.paperThetaTwoHom f hchar h (Multiplicative.ofAdd d)
  exact congrArg Multiplicative.toAdd hk

/- The quotient automorphism has the expected finite-factor lift (Zhou §6). -/
theorem quotientAutomorphism_lift
    (f : PaperKernel.paperGammaCarrier PaperKernel.paperThetaOneHom ≃*
      PaperKernel.paperGammaCarrier PaperKernel.paperThetaTwoHom)
    (hchar : Subgroup.map f.toMonoidHom
        (kernelSubgroup PaperKernel.paperThetaOneHom) =
      kernelSubgroup PaperKernel.paperThetaTwoHom) (q : Q) :
    quotientEquiv PaperKernel.paperThetaOneHom
        PaperKernel.paperThetaTwoHom f hchar (1, q) =
      (1, quotientAutomorphism PaperKernel.paperThetaOneHom
        PaperKernel.paperThetaTwoHom f hchar q) := by
  let ψ := quotientEquiv PaperKernel.paperThetaOneHom
    PaperKernel.paperThetaTwoHom f hchar
  have hqmem : ψ (1, q) ∈ qSubgroup := by
    have hq : (1, q) ∈ qSubgroup := by
      apply MonoidHom.mem_ker.mpr
      rfl
    have hm : ψ (1, q) ∈ Subgroup.map ψ.toMonoidHom qSubgroup := by
      exact Subgroup.mem_map.mpr ⟨(1, q), hq, rfl⟩
    rw [qSubgroup_characteristic ψ] at hm
    exact hm
  have hsecond :
      quotientAutomorphism PaperKernel.paperThetaOneHom
        PaperKernel.paperThetaTwoHom f hchar q = (ψ (1, q)).2 := by
    rfl
  apply Prod.ext
  · exact (MonoidHom.mem_ker.mp hqmem)
  · exact hsecond.symm

/- An intertwining kernel equivalence induces a group-algebra map (Zhou §6).
-/
/--
The `moduleMapOfLinearEquiv` construction used in the Connes rigidity formalization.
-/
def moduleMapOfLinearEquiv
    (ρ σ : Representation k Q PaperKernel.D)
    (e : PaperKernel.D ≃ₗ[k] PaperKernel.D)
    (he : ∀ q d, e (ρ q d) = σ q (e d)) :
    ρ.asModule →ₗ[PaperNonisomorphism.Ring] σ.asModule :=
  (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ).toFun
    (e.toLinearMap.intertwiningMap_of_isIntertwiningMap ρ σ he)

/-- The induced group-algebra map is bijective (Zhou §6). -/
theorem moduleMapOfLinearEquiv_bijective
    (ρ σ : Representation k Q PaperKernel.D)
    (e : PaperKernel.D ≃ₗ[k] PaperKernel.D)
    (he : ∀ q d, e (ρ q d) = σ q (e d)) :
    Function.Bijective (moduleMapOfLinearEquiv ρ σ e he) := by
  constructor
  · intro x y hxy
    have hxy' := congrArg σ.asModuleEquiv hxy
    change e (ρ.asModuleEquiv x) = e (ρ.asModuleEquiv y) at hxy'
    exact e.injective hxy'
  · intro y
    refine ⟨ρ.asModuleEquiv.symm (e.symm (σ.asModuleEquiv y)), ?_⟩
    apply σ.asModuleEquiv.injective
    change e (ρ.asModuleEquiv
      (ρ.asModuleEquiv.symm (e.symm (σ.asModuleEquiv y)))) =
      σ.asModuleEquiv y
    simp

/- The concrete paper actions admit the transported intertwiner (Zhou §6).
-/
/--
The `paperModuleIntertwining` construction used in the Connes rigidity formalization.
-/
def paperModuleIntertwining
    (f : PaperKernel.paperGammaCarrier PaperKernel.paperThetaOneHom ≃*
      PaperKernel.paperGammaCarrier PaperKernel.paperThetaTwoHom)
    (hchar : Subgroup.map f.toMonoidHom
        (kernelSubgroup PaperKernel.paperThetaOneHom) =
      kernelSubgroup PaperKernel.paperThetaTwoHom) :
    Representation.IntertwiningMap
      (qRepresentationOne)
      (qRepresentationTwoAlong
        (quotientAutomorphism PaperKernel.paperThetaOneHom
          PaperKernel.paperThetaTwoHom f hchar)) := by
  let σ := quotientAutomorphism PaperKernel.paperThetaOneHom
    PaperKernel.paperThetaTwoHom f hchar
  exact (kernelLinearEquiv PaperKernel.paperThetaOneHom
      PaperKernel.paperThetaTwoHom f hchar).toLinearMap
    |>.intertwiningMap_of_isIntertwiningMap
      (qRepresentationOne)
      (qRepresentationTwoAlong σ) (by
        intro q d
        change kernelLinearEquiv PaperKernel.paperThetaOneHom
            PaperKernel.paperThetaTwoHom f hchar
            (PaperKernel.paperThetaOneLinearHom (1, q) d) =
          PaperKernel.paperThetaTwoLinearHom (1, σ q)
            (kernelLinearEquiv PaperKernel.paperThetaOneHom
              PaperKernel.paperThetaTwoHom f hchar d)
        have h := kernelLinearEquiv_intertwines f hchar (1, q) d
        rw [quotientAutomorphism_lift f hchar q] at h
        exact h)

/-- The concrete module map induced by a group isomorphism (Zhou §6).
-/
def paperModuleLinearMap
    (f : PaperKernel.paperGammaCarrier PaperKernel.paperThetaOneHom ≃*
      PaperKernel.paperGammaCarrier PaperKernel.paperThetaTwoHom)
    (hchar : Subgroup.map f.toMonoidHom
        (kernelSubgroup PaperKernel.paperThetaOneHom) =
      kernelSubgroup PaperKernel.paperThetaTwoHom) :
    (qRepresentationOne).asModule →ₗ[Ring]
      (qRepresentationTwoAlong
        (quotientAutomorphism PaperKernel.paperThetaOneHom
          PaperKernel.paperThetaTwoHom f hchar)).asModule :=
  (Representation.IntertwiningMap.equivLinearMapAsModule
    (qRepresentationOne)
    (qRepresentationTwoAlong
      (quotientAutomorphism PaperKernel.paperThetaOneHom
        PaperKernel.paperThetaTwoHom f hchar))).toFun
    (paperModuleIntertwining f hchar)

/- The concrete module map is an equivalence (Zhou §6). -/
theorem paperModuleLinearMap_bijective
    (f : PaperKernel.paperGammaCarrier PaperKernel.paperThetaOneHom ≃*
      PaperKernel.paperGammaCarrier PaperKernel.paperThetaTwoHom)
    (hchar : Subgroup.map f.toMonoidHom
        (kernelSubgroup PaperKernel.paperThetaOneHom) =
      kernelSubgroup PaperKernel.paperThetaTwoHom) :
    Function.Bijective (paperModuleLinearMap f hchar) := by
  let σ := quotientAutomorphism PaperKernel.paperThetaOneHom
    PaperKernel.paperThetaTwoHom f hchar
  apply moduleMapOfLinearEquiv_bijective
    (qRepresentationOne)
    (qRepresentationTwoAlong σ)
    (kernelLinearEquiv PaperKernel.paperThetaOneHom
      PaperKernel.paperThetaTwoHom f hchar)
  intro q d
  change kernelLinearEquiv PaperKernel.paperThetaOneHom
      PaperKernel.paperThetaTwoHom f hchar
      (PaperKernel.paperThetaOneLinearHom (1, q) d) =
    PaperKernel.paperThetaTwoLinearHom (1, σ q)
      (kernelLinearEquiv PaperKernel.paperThetaOneHom
        PaperKernel.paperThetaTwoHom f hchar d)
  have h := kernelLinearEquiv_intertwines f hchar (1, q) d
  rw [quotientAutomorphism_lift f hchar q] at h
  exact h


end
end PaperCharacteristicTransport
end Connes
