/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Extraction.Nondegenerate
public import LeanPool.RegtsSevenster.RS.Novel.Extraction.StdRigid

/-!
# Uniqueness of the copairing

The snake identities determine the copairing (accompanying paper
§5.2):
any copairing for the standard form equals `stdCopair`.

The engine is the *contraction operator* of a bilinear form,
`contractionMap B : M ⊗ N →ₗ (M →ₗ N)`, sending `m ⊗ n` to
`x ↦ B(x, m) • n`.  The contraction identities say exactly that
the copairing's blocks are sent to the identity; the operator is
injective for a nondegenerate form on a finite-dimensional space
(`dualTensorHom` is bijective, and the form identifies the space
with its dual), so the blocks are pinned to the standard
copairing elements, which satisfy the same identities.
-/

@[expose] public section

noncomputable section

namespace RS

open CategoryTheory
open scoped TensorProduct
open LinearMap (BilinForm)
open LinearMap.BilinForm
open Module

/-! ### The contraction operator -/

/-- The left contraction operator of a bilinear form:
`m ⊗ n ↦ (x ↦ B(x, m) • n)`. -/
def contractionMap {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (B : BilinForm ℂ M) :
    (M ⊗[ℂ] N) →ₗ[ℂ] (M →ₗ[ℂ] N) :=
  (dualTensorHom ℂ M N).comp
    (TensorProduct.map (LinearMap.flip B) LinearMap.id)

/-- The contraction operator on a pure tensor. -/
theorem contractionMap_tmul {M N : Type*} [AddCommGroup M]
    [Module ℂ M] [AddCommGroup N] [Module ℂ N] (B : BilinForm ℂ M)
    (m : M) (n : N) (x : M) :
    contractionMap B (m ⊗ₜ[ℂ] n) x = B x m • n := by
  simp [contractionMap, TensorProduct.map_tmul]

/-- The contraction operator of a nondegenerate form on a
finite-dimensional space is injective: the form identifies the
space with its dual, and `dualTensorHom` is bijective. -/
theorem contractionMap_injective {M N : Type*} [AddCommGroup M]
    [Module ℂ M] [FiniteDimensional ℂ M] [AddCommGroup N]
    [Module ℂ N] (B : BilinForm ℂ M) (hB : B.Nondegenerate) :
    Function.Injective (contractionMap (N := N) B) := by
  have hm : TensorProduct.map (LinearMap.flip B) LinearMap.id =
      (TensorProduct.congr (LinearMap.BilinForm.toDual B.flip hB.flip)
        (LinearEquiv.refl ℂ N)).toLinearMap := by
    apply TensorProduct.ext'
    intro m n
    rw [TensorProduct.map_tmul, LinearEquiv.coe_coe,
      TensorProduct.congr_tmul]
    exact congrArg (fun f : Module.Dual ℂ M => f ⊗ₜ[ℂ] n)
      (LinearMap.ext fun y => (toDual_def hB.flip).symm)
  have hminj : Function.Injective
      ⇑(TensorProduct.map (LinearMap.flip B)
        (LinearMap.id : N →ₗ[ℂ] N)) := by
    rw [hm]
    exact (TensorProduct.congr
      (LinearMap.BilinForm.toDual B.flip hB.flip)
      (LinearEquiv.refl ℂ N)).injective
  have hdt : Function.Injective ⇑(dualTensorHom ℂ M N) := by
    have hb := (dualTensorHomEquivOfBasis
      (R := ℂ) (M := M) (N := N)
      (Module.Free.chooseBasis ℂ M)).injective
    intro a b hab
    exact hb (by
      simpa only [dualTensorHomEquivOfBasis_apply] using hab)
  intro t t' h
  exact hminj (hdt h)

/-! ### Nondegeneracy of the standard bilinear forms -/

/-- The standard even form is nondegenerate, so its contraction
operator is injective. -/
theorem stdFormEvenBilin_nondegenerate (k : ℕ) :
    (stdFormEvenBilin k).Nondegenerate := by
  constructor
  · intro x hx
    funext j
    have h := hx (stdE k j)
    rw [show stdFormEvenBilin k x (stdE k j) =
        stdFormEven k x (stdE k j) from rfl,
      stdFormEven_comm, stdFormEven_stdE_left] at h
    exact h
  · intro x hx
    funext j
    have h := hx (stdE k j)
    rw [show stdFormEvenBilin k (stdE k j) x =
        stdFormEven k (stdE k j) x from rfl,
      stdFormEven_stdE_left] at h
    exact h

/-- The standard odd form is nondegenerate too. -/
theorem stdFormOddBilin_nondegenerate (ℓ : ℕ) :
    (stdFormOddBilin ℓ).Nondegenerate := by
  constructor
  · intro x hx
    funext j
    have h := hx (stdG ℓ j)
    rw [show stdFormOddBilin ℓ x (stdG ℓ j) =
        stdFormOdd ℓ x (stdG ℓ j) from rfl,
      stdFormOdd_antisymm, stdFormOdd_stdG_left] at h
    exact neg_eq_zero.mp h
  · intro x hx
    funext j
    have h := hx (stdG ℓ j)
    rw [show stdFormOddBilin ℓ (stdG ℓ j) x =
        stdFormOdd ℓ (stdG ℓ j) x from rfl,
      stdFormOdd_stdG_left] at h
    exact h

/-! ### The standard copairing contracts to the identity -/

/-- The standard even copairing element contracts to the identity —
it satisfies the even contraction identity. -/
theorem contractionMap_stdCopairEvenElem (k : ℕ) (x : Fin k → ℂ) :
    contractionMap (stdFormEvenBilin k) (stdCopairEvenElem k) x = x := by
  unfold stdCopairEvenElem
  rw [map_sum, LinearMap.sum_apply,
    Finset.sum_congr rfl fun i _ =>
      contractionMap_tmul (stdFormEvenBilin k) (stdE k i) (stdE k i) x,
    Finset.sum_congr rfl fun i _ => by
      rw [show stdFormEvenBilin k x (stdE k i) =
          stdFormEven k x (stdE k i) from rfl, stdFormEven_comm]]
  exact sum_stdFormEven_smul k x

/-- The standard odd form against a basis vector on the right:
`b(x, f_m) = s_m · x_{p(m)}`. -/
theorem stdFormOdd_stdF_right (ℓ : ℕ) (x : Fin (2 * ℓ) → ℂ)
    (m : Fin (2 * ℓ)) :
    stdFormOdd ℓ x (stdF ℓ m) =
      (oddPartnerSign ℓ m : ℂ) * x (oddPartner ℓ m) := by
  unfold stdFormOdd stdF
  rw [Finset.sum_eq_single (oddPartner ℓ m)]
  · rw [oddPartner_invol, Pi.single_eq_same, mul_one,
      oddPartnerSign_oddPartner]
    push_cast
    ring
  · intro i _ hi
    rw [Pi.single_eq_of_ne (fun hh : oddPartner ℓ i = m =>
        hi (by rw [← hh, oddPartner_invol])), mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- And the odd element satisfies the odd one. -/
theorem contractionMap_stdCopairOddElem (ℓ : ℕ)
    (x : Fin (2 * ℓ) → ℂ) :
    contractionMap (stdFormOddBilin ℓ) (stdCopairOddElem ℓ) x = x := by
  unfold stdCopairOddElem
  rw [map_sum, LinearMap.sum_apply,
    Finset.sum_congr rfl fun i _ =>
      contractionMap_tmul (stdFormOddBilin ℓ) (stdF ℓ i) (stdG ℓ i) x,
    Finset.sum_congr rfl fun i _ => by
      rw [show stdFormOddBilin ℓ x (stdF ℓ i) =
          stdFormOdd ℓ x (stdF ℓ i) from rfl, stdFormOdd_stdF_right]]
  funext j
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single (oddPartner ℓ j)]
  · unfold stdG stdF
    rw [oddPartner_invol, Pi.smul_apply, Pi.smul_apply,
      Pi.single_eq_same, oddPartnerSign_oddPartner]
    push_cast
    rw [smul_eq_mul, smul_eq_mul, mul_one]
    rw [show -(oddPartnerSign ℓ j : ℂ) * x j *
        -(oddPartnerSign ℓ j : ℂ) =
        ((oddPartnerSign ℓ j * oddPartnerSign ℓ j : ℤ) : ℂ) * x j from by
      push_cast; ring, oddPartnerSign_mul_self, Int.cast_one, one_mul]
  · intro i _ hi
    unfold stdG stdF
    rw [Pi.smul_apply, Pi.smul_apply,
      Pi.single_eq_of_ne (fun hh : j = oddPartner ℓ i =>
        hi (by rw [hh, oddPartner_invol])),
      smul_zero, smul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-! ### The standard form's blocks -/

/-- The standard form's even block is the standard even form. -/
theorem formEvenBlock_stdForm (k ℓ : ℕ) (x y : Fin k → ℂ) :
    formEvenBlock (stdForm k ℓ) x y = stdFormEven k x y := by
  change LinearMap.coprod (TensorProduct.lift (stdFormEvenBilin k))
      (TensorProduct.lift (stdFormOddBilin ℓ)) (x ⊗ₜ[ℂ] y, 0) =
    stdFormEven k x y
  rw [LinearMap.coprod_apply, map_zero, add_zero,
    TensorProduct.lift.tmul]
  rfl

/-- And its odd block the standard odd form. -/
theorem formOddBlock_stdForm (k ℓ : ℕ) (x y : Fin (2 * ℓ) → ℂ) :
    formOddBlock (stdForm k ℓ) x y = stdFormOdd ℓ x y := by
  change LinearMap.coprod (TensorProduct.lift (stdFormEvenBilin k))
      (TensorProduct.lift (stdFormOddBilin ℓ)) (0, x ⊗ₜ[ℂ] y) =
    stdFormOdd ℓ x y
  rw [LinearMap.coprod_apply, map_zero, zero_add,
    TensorProduct.lift.tmul]
  rfl

/-! ### Uniqueness -/

private theorem eq_of_contraction_family {M : Type*} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (B : BilinForm ℂ M) (hB : B.Nondegenerate)
    (t t₀ : M ⊗[ℂ] M) (S : Finset (M × M))
    (hS : t = ∑ i ∈ S, i.1 ⊗ₜ[ℂ] i.2)
    (hI : ∀ x, ∑ i ∈ S, B x i.1 • i.2 = x)
    (h₀ : ∀ x, contractionMap B t₀ x = x) : t = t₀ := by
  apply contractionMap_injective B hB
  ext x
  rw [hS, map_sum, LinearMap.sum_apply]
  simp only [contractionMap_tmul]
  exact (hI x).trans (h₀ x).symm

open MonoidalCategory in
/-- **Uniqueness of the copairing** (accompanying paper §5.2): any
copairing satisfying the snake identities against the standard
form is the standard copairing. -/
theorem stdCopair_unique (k ℓ : ℕ)
    (C' : SuperVect.Hom SuperVect.tensorUnit
      (SuperVect.tensorObj (stdSuperPair k ℓ) (stdSuperPair k ℓ)))
    (h1 : stdSuperPair k ℓ ◁
        (show 𝟙_ SuperVect ⟶ stdSuperPair k ℓ ⊗ stdSuperPair k ℓ from C') ≫
        (α_ (stdSuperPair k ℓ) (stdSuperPair k ℓ) (stdSuperPair k ℓ)).inv ≫
        (show stdSuperPair k ℓ ⊗ stdSuperPair k ℓ ⟶ 𝟙_ SuperVect from
          stdForm k ℓ) ▷ stdSuperPair k ℓ =
        (ρ_ (stdSuperPair k ℓ)).hom ≫ (λ_ (stdSuperPair k ℓ)).inv)
    (h2 : (show 𝟙_ SuperVect ⟶ stdSuperPair k ℓ ⊗ stdSuperPair k ℓ from C') ▷
        stdSuperPair k ℓ ≫
        (α_ (stdSuperPair k ℓ) (stdSuperPair k ℓ) (stdSuperPair k ℓ)).hom ≫
        stdSuperPair k ℓ ◁
        (show stdSuperPair k ℓ ⊗ stdSuperPair k ℓ ⟶ 𝟙_ SuperVect from
          stdForm k ℓ) =
        (λ_ (stdSuperPair k ℓ)).hom ≫ (ρ_ (stdSuperPair k ℓ)).inv) :
    C' = stdCopair k ℓ := by
  obtain ⟨S, T, hS, hT, hi, _, hiii, _⟩ :=
    exists_contraction_families (stdForm k ℓ) C' h1 h2
  have he : ((formCoevMap C') 1).1 = stdCopairEvenElem k := by
    apply eq_of_contraction_family (stdFormEvenBilin k)
      (stdFormEvenBilin_nondegenerate k) _ _ S hS
    · intro x
      refine Eq.trans ?_ (hi x)
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (· • i.2) (formEvenBlock_stdForm k ℓ x i.1).symm
    · exact contractionMap_stdCopairEvenElem k
  have ho : ((formCoevMap C') 1).2 = stdCopairOddElem ℓ := by
    apply eq_of_contraction_family (stdFormOddBilin ℓ)
      (stdFormOddBilin_nondegenerate ℓ) _ _ T hT
    · intro x
      refine Eq.trans ?_ (hiii x)
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (· • i.2) (formOddBlock_stdForm k ℓ x i.1).symm
    · exact contractionMap_stdCopairOddElem ℓ
  apply SuperVect.Hom.ext
  · have hval : formCoevMap C' = formCoevMap (stdCopair k ℓ) := by
      apply LinearMap.ext_ring
      refine Prod.ext ?_ ?_
      · exact he.trans (one_smul ℂ (stdCopairEvenElem k)).symm
      · exact ho.trans (one_smul ℂ (stdCopairOddElem ℓ)).symm
    exact hval
  · exact LinearMap.ext fun z => by
      rw [show z = 0 from Subsingleton.elim z 0, map_zero, map_zero]

end RS
