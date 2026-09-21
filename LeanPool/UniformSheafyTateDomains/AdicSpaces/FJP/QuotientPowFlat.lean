/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FlatCompletion

/-!
# Flat + trivial special fibre ⟹ all finite levels agree

([hrw-decomposition] L1 elementary leaf `quotient_pow_equiv_of_flat`, per the
adjudicated chain.)  For a flat algebra `A → B` whose level-one map
`A/I → B/IB` is bijective, every level map `A/Iⁿ → B/(IB)ⁿ` is bijective:
surjectivity telescopes (the existing `FlatCompletion` ladder), injectivity
is the five-lemma induction on `0 → Iⁿ/Iⁿ⁺¹ → A/Iⁿ⁺¹ → A/Iⁿ → 0` tensored
against the flat `B` (`Module.Flat.lTensor_exact`).

WIP frontier for the 8.30-conditional L1 assembly
(`qHead_completedLocal_comparison`) — build against the central flatness.
-/

@[expose] public section

open scoped TensorProduct

section QuotientPowFlat

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A)

/-- The level-one equivalence in plain-quotient form. -/
noncomputable def levelOnePlainEquiv
    (h1 : Function.Bijective (levelMap (B := B) I 1)) :
    (A ⧸ I) ≃+* (B ⧸ I.map (algebraMap A B)) :=
  ((Ideal.quotEquivOfEq (pow_one I).symm).trans
    (RingEquiv.ofBijective _ h1)).trans
    (Ideal.quotEquivOfEq (pow_one (I.map (algebraMap A B))))

theorem levelOnePlainEquiv_mk
    (h1 : Function.Bijective (levelMap (B := B) I 1)) (a : A) :
    levelOnePlainEquiv I h1 (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B a) := by
  show (Ideal.quotEquivOfEq (pow_one (I.map (algebraMap A B))))
    ((RingEquiv.ofBijective _ h1)
      ((Ideal.quotEquivOfEq (pow_one I).symm)
        (Ideal.Quotient.mk I a))) = _
  rw [Ideal.quotEquivOfEq_mk]
  show (Ideal.quotEquivOfEq (pow_one (I.map (algebraMap A B))))
    (levelMap (B := B) I 1 (Ideal.Quotient.mk (I ^ 1) a)) = _
  rw [levelMap_mk, Ideal.quotEquivOfEq_mk]

/-- The inverse of the level-one equivalence, as an `A`-linear map. -/
noncomputable def levelOneSymmLin
    (h1 : Function.Bijective (levelMap (B := B) I 1)) :
    (B ⧸ I.map (algebraMap A B)) →ₗ[A] (A ⧸ I) where
  toFun := (levelOnePlainEquiv I h1).symm
  map_add' x y := map_add _ x y
  map_smul' r x := by
    rw [RingHom.id_apply]
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h2 : r • (Ideal.Quotient.mk (I.map (algebraMap A B)) b) =
        Ideal.Quotient.mk (I.map (algebraMap A B))
          (algebraMap A B r * b) := by
      rw [Algebra.smul_def]
      rw [show algebraMap A (B ⧸ I.map (algebraMap A B)) r =
        Ideal.Quotient.mk (I.map (algebraMap A B))
          (algebraMap A B r) from rfl, ← map_mul]
    rw [h2, show Ideal.Quotient.mk (I.map (algebraMap A B))
        (algebraMap A B r * b) =
      Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B r) *
        Ideal.Quotient.mk (I.map (algebraMap A B)) b from map_mul _ _ _,
      map_mul]
    have h4 : (levelOnePlainEquiv I h1).symm
        (Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B r)) =
        Ideal.Quotient.mk I r := by
      rw [RingEquiv.symm_apply_eq, levelOnePlainEquiv_mk]
    rw [h4, Algebra.smul_def]
    rfl

/-- Subtype massage: an element of `Iⁿ` whose value lies in `I·Iⁿ` lies in
the smul submodule. -/
theorem mem_smul_top_of_val_mem_mul {n : ℕ} (m : ↥(I ^ n : Ideal A))
    (hm : (m : A) ∈ I * I ^ n) :
    m ∈ (I • (⊤ : Submodule A ↥(I ^ n : Ideal A))) := by
  classical
  have key : ∃ hz : (m : A) ∈ I ^ n,
      (⟨(m : A), hz⟩ : ↥(I ^ n : Ideal A)) ∈
        (I • (⊤ : Submodule A ↥(I ^ n : Ideal A))) := by
    refine Submodule.mul_induction_on hm ?_ ?_
    · intro i hi a ha
      refine ⟨Ideal.mul_mem_left _ i ha, ?_⟩
      have h5 : (⟨i * a, Ideal.mul_mem_left _ i ha⟩ :
          ↥(I ^ n : Ideal A)) =
          i • (⟨a, ha⟩ : ↥(I ^ n : Ideal A)) := Subtype.ext rfl
      rw [h5]
      exact Submodule.smul_mem_smul hi Submodule.mem_top
    · rintro x y ⟨hx, wx⟩ ⟨hy, wy⟩
      refine ⟨Ideal.add_mem _ hx hy, ?_⟩
      have h6 : (⟨x + y, Ideal.add_mem _ hx hy⟩ :
          ↥(I ^ n : Ideal A)) =
          (⟨x, hx⟩ : ↥(I ^ n : Ideal A)) + ⟨y, hy⟩ := Subtype.ext rfl
      rw [h6]
      exact Submodule.add_mem _ wx wy
  obtain ⟨hz, w⟩ := key
  have h7 : m = ⟨(m : A), hz⟩ := Subtype.ext rfl
  rw [h7]
  exact w

/-- **The graded step**: over a flat algebra with bijective level one, an
element of `Iⁿ` whose image lies in `J^(n+1)` lies in `I^(n+1)`. -/
theorem mem_pow_succ_of_flat [Module.Flat A B]
    (h1 : Function.Bijective (levelMap (B := B) I 1)) {n : ℕ} {a : A}
    (han : a ∈ I ^ n)
    (hab : algebraMap A B a ∈ (I.map (algebraMap A B)) ^ (n + 1)) :
    a ∈ I ^ (n + 1) := by
  classical
  set f : ↥(I ^ n : Ideal A) →ₗ[A] A :=
    (I ^ n : Ideal A).subtype with hfdef
  set φ : (↥(I ^ n : Ideal A)) ⊗[A] B →ₗ[A] B :=
    (TensorProduct.lid A B).toLinearMap.comp (f.rTensor B) with hφdef
  have hφinj : Function.Injective φ := by
    rw [hφdef]
    show Function.Injective
      (⇑(TensorProduct.lid A B).toLinearMap ∘ ⇑(f.rTensor B))
    exact Function.Injective.comp (TensorProduct.lid A B).injective
      (Module.Flat.rTensor_preserves_injective_linearMap f
        (Submodule.injective_subtype _))
  set ι : ↥(I ^ (n + 1) : Ideal A) →ₗ[A] ↥(I ^ n : Ideal A) :=
    Submodule.inclusion (Ideal.pow_le_pow_right (Nat.le_succ n)) with hιdef
  set u : (↥(I ^ n : Ideal A)) ⊗[A] B := ⟨a, han⟩ ⊗ₜ[A] 1 with hudef
  have hφu : φ u = algebraMap A B a := by
    rw [hudef, hφdef]
    show (TensorProduct.lid A B) ((f.rTensor B) (⟨a, han⟩ ⊗ₜ[A] 1)) = _
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
    show a • (1 : B) = _
    rw [Algebra.smul_def, mul_one]
  have hsurj : ∀ y ∈ ((I.map (algebraMap A B)) ^ (n + 1) : Ideal B),
      ∃ w ∈ LinearMap.range (ι.rTensor B), φ w = y := by
    intro y hy
    have hy2 : y ∈ ((I ^ (n + 1)) • (⊤ : Submodule A B)) := by
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem,
        Ideal.map_pow]
      exact hy
    refine Submodule.smul_induction_on hy2 ?_ ?_
    · intro r hr b _
      refine ⟨(ι.rTensor B)
        ((⟨r, hr⟩ : ↥(I ^ (n + 1) : Ideal A)) ⊗ₜ[A] b),
        LinearMap.mem_range_self _ _, ?_⟩
      rw [LinearMap.rTensor_tmul, hφdef]
      show (TensorProduct.lid A B)
        ((f.rTensor B) ((ι ⟨r, hr⟩) ⊗ₜ[A] b)) = _
      rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
      show r • b = _
      rfl
    · rintro x y ⟨wx, hwx, hφx⟩ ⟨wy, hwy, hφy⟩
      exact ⟨wx + wy, Submodule.add_mem _ hwx hwy, by
        rw [map_add, hφx, hφy]⟩
  obtain ⟨w, hwrange, hwφ⟩ := hsurj _ hab
  have huw : u = w := hφinj (by rw [hφu, hwφ])
  set g₁ : (↥(I ^ n : Ideal A)) ⊗[A] B →ₗ[A]
      (↥(I ^ n : Ideal A)) ⊗[A] (B ⧸ I.map (algebraMap A B)) :=
    LinearMap.lTensor _
      (Ideal.Quotient.mkₐ A (I.map (algebraMap A B))).toLinearMap
    with hg₁def
  set g₂ : (↥(I ^ n : Ideal A)) ⊗[A] (B ⧸ I.map (algebraMap A B)) →ₗ[A]
      (↥(I ^ n : Ideal A)) ⊗[A] (A ⧸ I) :=
    LinearMap.lTensor _ (levelOneSymmLin I h1) with hg₂def
  set g₃ : (↥(I ^ n : Ideal A)) ⊗[A] (A ⧸ I) →ₗ[A]
      (↥(I ^ n : Ideal A)) ⧸
        (I • (⊤ : Submodule A ↥(I ^ n : Ideal A))) :=
    (TensorProduct.tensorQuotEquivQuotSMul
      (↥(I ^ n : Ideal A)) I).toLinearMap with hg₃def
  set ψ := g₃.comp (g₂.comp g₁) with hψdef
  have hg₃tmul : ∀ (x : ↥(I ^ n : Ideal A)) (r : A),
      g₃ (x ⊗ₜ[A] (Ideal.Quotient.mk I r)) =
        Submodule.Quotient.mk (r • x) := by
    intro x r
    rw [hg₃def]
    show (TensorProduct.tensorQuotEquivQuotSMul _ I)
      (x ⊗ₜ[A] (Ideal.Quotient.mk I r)) = _
    rw [TensorProduct.tensorQuotEquivQuotSMul, LinearEquiv.trans_apply,
      TensorProduct.comm_tmul,
      TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
  have hψu : ψ u =
      Submodule.Quotient.mk (⟨a, han⟩ : ↥(I ^ n : Ideal A)) := by
    rw [hψdef, hudef]
    show g₃ (g₂ (g₁ (⟨a, han⟩ ⊗ₜ[A] 1))) = _
    rw [hg₁def, LinearMap.lTensor_tmul, hg₂def, LinearMap.lTensor_tmul]
    have h9 : (levelOneSymmLin I h1)
        ((Ideal.Quotient.mkₐ A (I.map (algebraMap A B))).toLinearMap
          (1 : B)) = Ideal.Quotient.mk I 1 := by
      show (levelOnePlainEquiv I h1).symm
        (Ideal.Quotient.mkₐ A (I.map (algebraMap A B)) 1) = _
      rw [map_one, map_one, map_one]
    rw [h9, hg₃tmul, one_smul]
  have hψW : ψ.comp (ι.rTensor B) = 0 := by
    refine TensorProduct.ext' fun x b => ?_
    show ψ ((ι.rTensor B) (x ⊗ₜ[A] b)) = 0
    rw [LinearMap.rTensor_tmul, hψdef]
    show g₃ (g₂ (g₁ ((ι x) ⊗ₜ[A] b))) = 0
    rw [hg₁def, LinearMap.lTensor_tmul, hg₂def, LinearMap.lTensor_tmul]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
      ((levelOneSymmLin I h1)
        ((Ideal.Quotient.mkₐ A (I.map (algebraMap A B))).toLinearMap b))
    rw [← hr, hg₃tmul]
    have hx0 : (Submodule.Quotient.mk (ι x) :
        (↥(I ^ n : Ideal A)) ⧸
          (I • (⊤ : Submodule A ↥(I ^ n : Ideal A)))) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero]
      refine mem_smul_top_of_val_mem_mul I (ι x) ?_
      rw [← pow_succ']
      exact x.2
    rw [Submodule.Quotient.mk_smul, hx0, smul_zero]
  have h0 : ψ u = 0 := by
    rw [huw]
    obtain ⟨v, rfl⟩ := hwrange
    have h10 := LinearMap.congr_fun hψW v
    simpa using h10
  have hmem : (⟨a, han⟩ : ↥(I ^ n : Ideal A)) ∈
      (I • (⊤ : Submodule A ↥(I ^ n : Ideal A))) := by
    rw [hψu] at h0
    exact (Submodule.Quotient.mk_eq_zero _).mp h0
  have h8 : ((⟨a, han⟩ : ↥(I ^ n : Ideal A)) : A) ∈
      Submodule.map (I ^ n : Ideal A).subtype
        (I • (⊤ : Submodule A ↥(I ^ n : Ideal A))) :=
    Submodule.mem_map_of_mem hmem
  rw [Submodule.map_smul'', Submodule.map_top,
    Submodule.range_subtype] at h8
  rw [pow_succ']
  rwa [Ideal.smul_eq_mul] at h8

/-- **Contractions of extended-ideal powers under flatness with trivial
special fibre.** -/
theorem comap_pow_le_of_flat_of_levelOne [Module.Flat A B]
    (h1 : Function.Bijective (levelMap (B := B) I 1)) (n : ℕ) :
    Ideal.comap (algebraMap A B) ((I.map (algebraMap A B)) ^ n) ≤
      I ^ n := by
  induction n with
  | zero =>
    intro a _
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ k ih =>
    intro a ha
    rw [Ideal.mem_comap] at ha
    have hk : a ∈ I ^ k := ih (Ideal.mem_comap.mpr
      (Ideal.pow_le_pow_right (Nat.le_succ k) ha))
    exact mem_pow_succ_of_flat I h1 hk ha

/-- **Flat + bijective level one ⟹ bijective at every level**
([hrw-decomposition] L1 `quotient_pow_equiv_of_flat`). -/
theorem levelMap_bijective_of_flat_of_levelOne [Module.Flat A B]
    (h1 : Function.Bijective (levelMap (B := B) I 1)) (n : ℕ) :
    Function.Bijective (levelMap (B := B) I n) := by
  constructor
  · refine Ideal.quotientMap_injective' ?_
    exact comap_pow_le_of_flat_of_levelOne I h1 n
  · exact levelMap_surjective (h1 := h1.surjective) n

/-- **Completion equivalence from flatness and trivial special fibre**
([hrw-decomposition] L1 `adicCompletionEquivOfQuotientPowEquiv`). -/
noncomputable def adicCompletionEquivOfFlatOfLevelOne [Module.Flat A B]
    (h1 : Function.Bijective (levelMap (B := B) I 1)) :
    AdicCompletion I A ≃+* AdicCompletion (I.map (algebraMap A B)) B :=
  AdicCompletion.congrPow I (I.map (algebraMap A B))
    (fun n => RingEquiv.ofBijective _
      (levelMap_bijective_of_flat_of_levelOne I h1 n))
    (fun {a b} hab x => by
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
      show Ideal.Quotient.factor (Ideal.pow_le_pow_right hab)
        (levelMap (B := B) I b (Ideal.Quotient.mk _ c)) =
        levelMap (B := B) I a
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right hab)
            (Ideal.Quotient.mk _ c))
      rw [levelMap_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
        levelMap_mk])

end QuotientPowFlat
