/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.Induced
/-!
# Low-degree Tate cohomology of products

This file proves that multiplicative Tate `H⁰` and `H⁻¹` commute with
dependent products, giving the product step for low-degree Herbrand quotients.
-/

noncomputable section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uι uA

/-- The componentwise multiplicative action on a dependent product. -/
@[reducible]
def piMulDistribMulAction
    (G : Type uG) [Group G]
    {ι : Type uι} (A : ι → Type uA)
    [∀ i, CommGroup (A i)]
    [∀ i, MulDistribMulAction G (A i)] :
    MulDistribMulAction G (∀ i, A i) where
  smul g x i := g • x i
  one_smul x := by
    funext i
    exact one_smul G (x i)
  mul_smul g h x := by
    funext i
    exact mul_smul g h (x i)
  smul_one g := by
    funext i
    exact MulDistribMulAction.smul_one g
  smul_mul g x y := by
    funext i
    exact MulDistribMulAction.smul_mul g (x i) (y i)

/-- The pointwise product of a family of subgroups. -/
def piSubgroup (ι : Type uι) (A : ι → Type uA)
    [∀ i, CommGroup (A i)]
    (N : ∀ i, Subgroup (A i)) :
    Subgroup (∀ i, A i) where
  carrier := {x | ∀ i, x i ∈ N i}
  one_mem' i := (N i).one_mem
  mul_mem' hx hy i := (N i).mul_mem (hx i) (hy i)
  inv_mem' hx i := (N i).inv_mem (hx i)

@[simp]
theorem mem_piSubgroup_iff
    (ι : Type uι) (A : ι → Type uA)
    [∀ i, CommGroup (A i)]
    (N : ∀ i, Subgroup (A i))
    (x : ∀ i, A i) :
    x ∈ piSubgroup ι A N ↔
      ∀ i, x i ∈ N i :=
  Iff.rfl

/-- The componentwise quotient map. -/
noncomputable def piQuotientMap
    (ι : Type uι) (A : ι → Type uA)
    [∀ i, CommGroup (A i)]
    (N : ∀ i, Subgroup (A i)) :
    (∀ i, A i) →* ∀ i, A i ⧸ N i where
  toFun x i := QuotientGroup.mk' (N i) (x i)
  map_one' := by
    ext i
    exact (QuotientGroup.mk' (N i)).map_one
  map_mul' x y := by
    ext i
    exact (QuotientGroup.mk' (N i)).map_mul
      (x i) (y i)

@[simp]
theorem piQuotientMap_apply
    (ι : Type uι) (A : ι → Type uA)
    [∀ i, CommGroup (A i)]
    (N : ∀ i, Subgroup (A i))
    (x : ∀ i, A i) (i : ι) :
    piQuotientMap ι A N x i =
      QuotientGroup.mk' (N i) (x i) :=
  rfl

theorem ker_piQuotientMap
    (ι : Type uι) (A : ι → Type uA)
    [∀ i, CommGroup (A i)]
    (N : ∀ i, Subgroup (A i)) :
    (piQuotientMap ι A N).ker =
      piSubgroup ι A N := by
  ext x
  constructor
  · intro hx i
    have hmap :
        piQuotientMap ι A N x = 1 :=
      MonoidHom.mem_ker.mp hx
    have hi : QuotientGroup.mk' (N i) (x i) = 1 :=
      (piQuotientMap_apply ι A N x i).symm.trans (congrFun hmap i)
    exact
      (QuotientGroup.eq_one_iff
        (N := N i) (x := x i)).mp hi
  · intro hx
    exact MonoidHom.mem_ker.mpr <| by
      ext i
      exact
        (QuotientGroup.eq_one_iff
          (N := N i) (x := x i)).mpr (hx i)

theorem piQuotientMap_surjective
    (ι : Type uι) (A : ι → Type uA)
    [∀ i, CommGroup (A i)]
    (N : ∀ i, Subgroup (A i)) :
    Function.Surjective (piQuotientMap ι A N) := by
  intro y
  choose x hx using fun i =>
    QuotientGroup.mk'_surjective (N i) (y i)
  refine ⟨x, ?_⟩
  ext i
  exact hx i

/-- The quotient of a dependent product by the pointwise subgroup is the
dependent product of the quotients. -/
noncomputable def piQuotientEquiv
    (ι : Type uι) (A : ι → Type uA)
    [∀ i, CommGroup (A i)]
    (N : ∀ i, Subgroup (A i)) :
    (∀ i, A i) ⧸ piSubgroup ι A N ≃*
      ∀ i, A i ⧸ N i :=
  (QuotientGroup.quotientMulEquivOfEq
    (ker_piQuotientMap ι A N).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (piQuotientMap ι A N)
      (piQuotientMap_surjective ι A N))

section TateProducts

variable {G : Type uG} [Group G] [Fintype G]
variable {ι : Type uι} (A : ι → Type uA)
variable [∀ i, CommGroup (A i)]
variable [∀ i, MulDistribMulAction G (A i)]

local instance :
    MulDistribMulAction G (∀ i, A i) :=
  piMulDistribMulAction G A

/-- Fixed points of a product are products of fixed points. -/
def fixedPiEquiv :
    fixedSubgroup G (∀ i, A i) ≃*
      ∀ i, fixedSubgroup G (A i) where
  toFun x i := ⟨x.1 i, fun g ↦ congrFun (x.2 g) i⟩
  invFun x := ⟨fun i ↦ (x i).1, fun g ↦ by
    funext i
    exact (x i).2 g⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

omit [Fintype G] in
@[simp]
theorem fixedPiEquiv_apply_coe
    (x : fixedSubgroup G (∀ i, A i))
    (i : ι) :
    ((fixedPiEquiv (G := G) A x i : A i)) =
      x.1 i :=
  rfl

/-- Norm kernels of a product are products of norm kernels. -/
def normKernelPiEquiv :
    normKernelSubgroup G (∀ i, A i) ≃*
      ∀ i, normKernelSubgroup G (A i) where
  toFun x i := ⟨x.1 i, by
    change tateNorm G (A i) (x.1 i) = 1
    have hi := congrFun x.2 i
    simpa only [tateNormHom_apply, tateNorm, Finset.prod_apply,
      Pi.smul_apply, Pi.one_apply] using hi⟩
  invFun x := ⟨fun i ↦ (x i).1, by
    funext i
    change
      (tateNorm G (∀ i, A i)
        (fun i ↦ (x i).1)) i = 1
    have hi := (x i).2
    change tateNormHom (G := G) (A := A i) (x i).1 = 1 at hi
    rw [tateNormHom_apply] at hi
    simpa only [tateNorm, Finset.prod_apply,
      Pi.smul_apply] using hi⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem normKernelPiEquiv_apply_coe
    (x : normKernelSubgroup G (∀ i, A i))
    (i : ι) :
    ((normKernelPiEquiv (G := G) A x i : A i)) =
      x.1 i :=
  rfl

/-- Tate `H⁰` commutes with dependent products. -/
noncomputable def herbrandH0PiEquiv :
    HerbrandH0 G (∀ i, A i) ≃*
      ∀ i, HerbrandH0 G (A i) := by
  let e :
      fixedSubgroup G (∀ i, A i) ≃*
        ∀ i, fixedSubgroup G (A i) :=
    fixedPiEquiv (G := G) A
  let N :=
    (tateNormSubgroup G (∀ i, A i)).subgroupOf
      (fixedSubgroup G (∀ i, A i))
  let M :=
    piSubgroup ι
      (fun i ↦ fixedSubgroup G (A i))
      (fun i ↦
        (tateNormSubgroup G (A i)).subgroupOf
          (fixedSubgroup G (A i)))
  let q :
      fixedSubgroup G (∀ i, A i) ⧸ N ≃*
        (∀ i, fixedSubgroup G (A i)) ⧸ M :=
    quotientMulEquivOfSplit
      N M e.toMonoidHom e.symm.toMonoidHom
      (fun y ↦ e.apply_symm_apply y)
      (fun x hx ↦ by
        rw [Subgroup.mem_subgroupOf] at hx
        change ∀ i, _ at ⊢
        rcases hx with ⟨a, ha⟩
        intro i
        rw [Subgroup.mem_subgroupOf]
        refine ⟨a i, ?_⟩
        have hi := congrFun ha i
        simpa [tateNormHom_apply, tateNorm, e, fixedPiEquiv] using hi)
      (fun y hy ↦ by
        change ∀ i, _ at hy
        have hy' :
            ∀ i, ∃ a : A i,
              tateNorm G (A i) a = (y i).1 := by
          intro i
          have hyi :
              (y i : A i) ∈ tateNormSubgroup G (A i) := by
            simpa only [Subgroup.mem_subgroupOf] using hy i
          rcases hyi with ⟨a, ha⟩
          exact ⟨a, by simpa only [tateNormHom_apply] using ha⟩
        choose a ha using hy'
        rw [Subgroup.mem_subgroupOf]
        refine ⟨fun i ↦ a i, ?_⟩
        funext i
        have hi := ha i
        simpa [tateNormHom_apply, e, fixedPiEquiv, tateNorm] using hi)
      (fun x hx ↦ by
        have hx1 : x = 1 := by
          apply e.injective
          simpa [e] using hx
        rw [hx1]
        exact N.one_mem)
  exact q.trans
    (piQuotientEquiv ι
      (fun i ↦ fixedSubgroup G (A i))
      (fun i ↦
        (tateNormSubgroup G (A i)).subgroupOf
          (fixedSubgroup G (A i))))

/-- Tate `H⁻¹` commutes with dependent products. -/
noncomputable def herbrandHMinusOnePiEquiv (σ : G) :
    HerbrandHMinusOne G (∀ i, A i) σ ≃*
      ∀ i, HerbrandHMinusOne G (A i) σ := by
  let e :
      normKernelSubgroup G (∀ i, A i) ≃*
        ∀ i, normKernelSubgroup G (A i) :=
    normKernelPiEquiv (G := G) A
  let N :=
    (augmentationSubgroup G (∀ i, A i) σ).subgroupOf
      (normKernelSubgroup G (∀ i, A i))
  let M :=
    piSubgroup ι
      (fun i ↦ normKernelSubgroup G (A i))
      (fun i ↦
        (augmentationSubgroup G (A i) σ).subgroupOf
          (normKernelSubgroup G (A i)))
  let q :
      normKernelSubgroup G (∀ i, A i) ⧸ N ≃*
        (∀ i, normKernelSubgroup G (A i)) ⧸ M :=
    quotientMulEquivOfSplit
      N M e.toMonoidHom e.symm.toMonoidHom
      (fun y ↦ e.apply_symm_apply y)
      (fun x hx ↦ by
        rw [Subgroup.mem_subgroupOf] at hx
        change ∀ i, _ at ⊢
        rcases hx with ⟨a, ha⟩
        intro i
        rw [Subgroup.mem_subgroupOf]
        refine ⟨a i, ?_⟩
        have hi := congrFun ha i
        simpa [sigmaMinusOneHom_apply, sigmaMinusOne, e,
          normKernelPiEquiv] using hi)
      (fun y hy ↦ by
        change ∀ i, _ at hy
        have hy' :
            ∀ i, ∃ a : A i,
              sigmaMinusOne G (A i) σ a =
                (y i).1 := by
          intro i
          have hyi :
              (y i : A i) ∈ augmentationSubgroup G (A i) σ := by
            simpa only [Subgroup.mem_subgroupOf] using hy i
          rcases hyi with ⟨a, ha⟩
          exact ⟨a, by simpa only [sigmaMinusOneHom_apply] using ha⟩
        choose a ha using hy'
        rw [Subgroup.mem_subgroupOf]
        refine ⟨fun i ↦ a i, ?_⟩
        funext i
        have hi := ha i
        simpa [sigmaMinusOneHom_apply, e, normKernelPiEquiv,
          sigmaMinusOne] using hi)
      (fun x hx ↦ by
        have hx1 : x = 1 := by
          apply e.injective
          simpa [e] using hx
        rw [hx1]
        exact N.one_mem)
  exact q.trans
    (piQuotientEquiv ι
      (fun i ↦ normKernelSubgroup G (A i))
      (fun i ↦
        (augmentationSubgroup G (A i) σ).subgroupOf
          (normKernelSubgroup G (A i))))

end TateProducts

end CyclicCohomology
