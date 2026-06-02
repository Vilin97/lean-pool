/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.PicardGroup

/-!
# Kernel of the Evaluation Map on Adic Completions

For a Noetherian local ring (R, M) and n : N, an element of the
M-adic completion that maps to zero under the canonical projection
to R/M^n must lie in the n-th power of the extended maximal ideal.
This uses the short exact sequence relating the completion to
successive quotients.
-/

open scoped Pointwise
open AdicCompletion

variable {R : Type*} [CommRing R]

/-! ### R ⧸ I^n is I-adically complete -/

lemma smul_eq_zero_of_quotient (I : Ideal R) (n : ℕ)
    (x : R ⧸ (I ^ n • ⊤ : Submodule R R))
    (hx : x ∈ I ^ n • (⊤ : Submodule R (R ⧸ (I ^ n • ⊤ : Submodule R R)))) :
    x = 0 := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y _
    induction y using Quotient.inductionOn' with
    | h a =>
      change Submodule.Quotient.mk (r • a) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro a b ha hb
    rw [ha, hb]
    exact add_zero 0

instance quotientIsHausdorff (I : Ideal R) (n : ℕ) :
    IsHausdorff I (R ⧸ (I ^ n • ⊤ : Submodule R R)) where
  haus' x hx := smul_eq_zero_of_quotient I n x (by
    have := hx n
    rwa [SModEq.sub_mem, sub_zero] at this)

instance quotientIsPrecomplete (I : Ideal R) (n : ℕ) :
    IsPrecomplete I (R ⧸ (I ^ n • ⊤ : Submodule R R)) where
  prec' f hf := ⟨f n, fun k => by
    rw [SModEq.sub_mem]
    by_cases hkn : k ≤ n
    · exact SModEq.sub_mem.mp (hf hkn)
    · push Not at hkn
      have h0 := smul_eq_zero_of_quotient I n _ (SModEq.sub_mem.mp (hf (le_of_lt hkn)))
      rw [← sub_eq_zero.mp h0, sub_self]
      exact Submodule.zero_mem _⟩

instance quotientAdicComplete (I : Ideal R) (n : ℕ) :
    IsAdicComplete I (R ⧸ (I ^ n • ⊤ : Submodule R R)) :=
  IsAdicComplete.mk

/-! ### Key lemma: evalₐ I n x = 0 → x ∈ I^n • ⊤ -/

/-- If evalₐ I n x = 0, then x ∈ I^n • ⊤ (as R-submodule of R̂).
This is the backward half of ker(evalₐ I n) = (Ideal.map f I)^n. -/
lemma ker_evalₐ_le_smul_top (I : Ideal R) [IsNoetherianRing R] (n : ℕ)
    (x : AdicCompletion I R)
    (hx : evalₐ I n x = 0) :
    x ∈ I ^ n • (⊤ : Submodule R (AdicCompletion I R)) := by
  set p := (I ^ n • ⊤ : Submodule R R) with hp
  -- Step 1: map I (mkQ p) x = 0, since R/p is I-adically complete
  have h_ker : map I p.mkQ x = 0 := by
    have h_eval : eval I R n x = 0 := by
      simp only [evalₐ, AlgHom.coe_comp, AlgHom.ofLinearMap_apply, Function.comp_apply] at hx
      exact (AlgEquiv.injective _) hx
    suffices key : (of I (R ⧸ p)).comp (eval I R n) =
        ((map I p.mkQ).restrictScalars R :
          AdicCompletion I R →ₗ[R] AdicCompletion I (R ⧸ p)) by
      have := LinearMap.congr_fun key x
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, h_eval,
        _root_.map_zero] at this
      exact this.symm
    apply map_ext''
    ext a k
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      mk_apply_coe, map_val_apply, of_apply]
    change (I ^ k • ⊤ : Submodule R (R ⧸ p)).mkQ ((eval I R n) (mk I R a)) =
      (p.mkQ).reduceModIdeal (I ^ k) ((I ^ k • ⊤ : Submodule R R).mkQ (a.1 k))
    rw [show (p.mkQ).reduceModIdeal (I ^ k) ((I ^ k • ⊤ : Submodule R R).mkQ (a.1 k)) =
      (I ^ k • ⊤ : Submodule R (R ⧸ p)).mkQ (p.mkQ (a.1 k)) from rfl]
    rw [show (eval I R n) (mk I R a) = p.mkQ (a.1 n) from rfl]
    simp only [Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    rw [show Submodule.Quotient.mk (p := p) (a.1 n) - Submodule.Quotient.mk (p := p) (a.1 k) =
      Submodule.Quotient.mk (p := p) (a.1 n - a.1 k) from by
      rw [← Submodule.Quotient.mk_sub]]
    by_cases hkn : k ≤ n
    · have hc := a.property hkn
      rw [SModEq.sub_mem] at hc
      rw [show a.1 n - a.1 k = -(a.1 k - a.1 n) from by ring,
        show Submodule.Quotient.mk (p := p) (-(a.1 k - a.1 n)) =
          -Submodule.Quotient.mk (p := p) (a.1 k - a.1 n) from by
          rw [← Submodule.Quotient.mk_neg]]
      exact neg_mem (Submodule.smul_top_le_comap_smul_top (I ^ k) p.mkQ hc)
    · push Not at hkn
      have hc := a.property (le_of_lt hkn)
      rw [SModEq.sub_mem] at hc
      rw [show Submodule.Quotient.mk (p := p) (a.1 n - a.1 k) = 0 from by
        rw [Submodule.Quotient.mk_eq_zero]
        exact hc]
      exact zero_mem _
  -- Step 2: exact sequence gives x ∈ range(map I subtype)
  have h_exact : Function.Exact (map I p.subtype) (map I p.mkQ) :=
    map_exact Subtype.val_injective
      (LinearMap.exact_subtype_mkQ p)
      (Submodule.mkQ_surjective _)
  have h_range : x ∈ LinearMap.range (map I p.subtype) := by
    rw [LinearMap.mem_range]
    exact ((h_exact x).mp h_ker)
  -- Step 3: range(map I subtype) ⊆ I^n • ⊤ via ofTensorProduct naturality
  have aux : ∀ (a : AdicCompletion I R) (r : R), r ∈ I ^ n • (⊤ : Submodule R R) →
      a • of I R r ∈ I ^ n • (⊤ : Submodule R (AdicCompletion I R)) := by
    intro a r hr
    refine Submodule.smul_induction_on hr ?_ ?_
    · intro c hc s _
      rw [map_smul, smul_comm]
      exact Submodule.smul_mem_smul hc Submodule.mem_top
    · intro x y hx hy
      have : a • of I R (x + y) = a • of I R x + a • of I R y := by
        rw [map_add]
        exact smul_add a _ _
      rw [this]
      exact Submodule.add_mem _ hx hy
  have h_smul : LinearMap.range ((map I p.subtype).restrictScalars R) ≤
      I ^ n • (⊤ : Submodule R (AdicCompletion I R)) := by
    rintro z ⟨y, rfl⟩
    simp only [LinearMap.restrictScalars_apply]
    set w := (ofTensorProductEquivOfFiniteNoetherian I ↥p).symm y
    have key : (map I p.subtype) y =
        (ofTensorProduct I R)
          ((TensorProduct.AlgebraTensorModule.map
            (LinearMap.id : AdicCompletion I R →ₗ[AdicCompletion I R] AdicCompletion I R)
            p.subtype) w) := by
      have nat := ofTensorProduct_naturality (N := R) I p.subtype
      have : y = (ofTensorProductEquivOfFiniteNoetherian I ↥p) w :=
        (LinearEquiv.apply_symm_apply _ y).symm
      rw [this, ofTensorProductEquivOfFiniteNoetherian_apply]
      rw [← LinearMap.comp_apply, nat, LinearMap.comp_apply]
    rw [key]
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply]
      rw [ofTensorProduct_tmul]
      exact aux a m.1 m.2
    | add x y hx hy => simp only [map_add]
                       exact Submodule.add_mem _ hx hy
  have h_range' : x ∈ LinearMap.range ((map I p.subtype).restrictScalars R) := by
    rw [LinearMap.mem_range]
    exact LinearMap.mem_range.mp h_range
  exact h_smul h_range'

/-! ### Main theorem: kernel of evalₐ is contained in the power of the extended maximal ideal -/

/-- If an element `x` of the `𝔪`-adic completion of a Noetherian local ring `(R, 𝔪)` satisfies
`evalₐ 𝔪 n x = 0`, then `x ∈ (𝔪̂)^n` where `𝔪̂ = Ideal.map (algebraMap R R̂) 𝔪`. -/
theorem mem_map_pow_of_evalₐ_eq_zero
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (n : ℕ) (x : AdicCompletion (IsLocalRing.maximalIdeal R) R)
    (hx : AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) n x = 0) :
    x ∈ (Ideal.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))
      (IsLocalRing.maximalIdeal R)) ^ n := by
  rw [← Ideal.map_pow]
  have hmem := ker_evalₐ_le_smul_top (IsLocalRing.maximalIdeal R) n x hx
  rw [Ideal.smul_top_eq_map] at hmem
  exact hmem
