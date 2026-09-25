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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.AdicNakayama
public import Mathlib.RingTheory.Artinian.Ring

/-!
# Semilocal fibre splitting of adic completions

([hrw-decomposition] HRW-5(iii) / leaf 14 core.) For an ideal `Q` with
Artinian quotient, the `Q`-adic completion splits as the product of the
completions at the finitely many maximal ideals over `Q`: the maximals of
`C⧸Q` are finite, their intersection (the Jacobson radical) is nilpotent,
and `AdicCompletion.semilocalSplit` applies.
-/

@[expose] public section

@[expose] public section


section SemilocalFibre

variable {C : Type*} [CommRing C] (Q : Ideal C) [IsArtinianRing (C ⧸ Q)]

open Classical in
/-- The (finite) index of maximal ideals of the fibre. -/
noncomputable def fibreMaximals : Type _ :=
  {J : Ideal (C ⧸ Q) // J.IsMaximal}

open Classical in
noncomputable instance : Fintype (fibreMaximals Q) :=
  (IsArtinianRing.setOfPred_isMaximal_finite (R := C ⧸ Q)).fintype

open Classical in
/-- The maximal ideals of `C` over `Q`, indexed by the fibre maximals. -/
noncomputable def overMaximal (𝔫 : fibreMaximals Q) : Ideal C :=
  Ideal.comap (Ideal.Quotient.mk Q) 𝔫.1

omit [IsArtinianRing (C ⧸ Q)] in
open Classical in
theorem overMaximal_isMaximal (𝔫 : fibreMaximals Q) :
    (overMaximal Q 𝔫).IsMaximal :=
  haveI := 𝔫.2
  Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective

omit [IsArtinianRing (C ⧸ Q)] in
open Classical in
theorem le_overMaximal (𝔫 : fibreMaximals Q) : Q ≤ overMaximal Q 𝔫 := by
  intro x hx
  change Ideal.Quotient.mk Q x ∈ 𝔫.1
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  exact 𝔫.1.zero_mem

omit [IsArtinianRing (C ⧸ Q)] in
open Classical in
theorem overMaximal_injective :
    Function.Injective (overMaximal Q) := by
  intro a b hab
  refine Subtype.ext ?_
  have h1 : ∀ J : fibreMaximals Q,
      (overMaximal Q J).map (Ideal.Quotient.mk Q) = J.1 :=
    fun J => Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
  rw [← h1 a, ← h1 b, hab]

omit [IsArtinianRing (C ⧸ Q)] in
open Classical in
theorem pairwise_coprime_overMaximal :
    Pairwise fun a b : fibreMaximals Q =>
      IsCoprime (overMaximal Q a) (overMaximal Q b) := by
  intro a b hab
  exact Ideal.isCoprime_iff_sup_eq.mpr
    ((overMaximal_isMaximal Q a).coprime_of_ne (overMaximal_isMaximal Q b)
      (fun h => hab (overMaximal_injective Q h)))

open Classical in
/-- Nilpotence of the intersection modulo `Q` (Jacobson radical of the
Artinian fibre). -/
theorem exists_pow_iInf_overMaximal_le :
    ∃ e : ℕ, 1 ≤ e ∧ (⨅ 𝔫, overMaximal Q 𝔫) ^ e ≤ Q := by
  obtain ⟨e, he⟩ := IsArtinianRing.isNilpotent_jacobson_bot
    (R := C ⧸ Q)
  refine ⟨e + 1, Nat.le_add_left 1 e, ?_⟩
  have hjac : (Ideal.jacobson (⊥ : Ideal (C ⧸ Q))) ^ (e + 1) = ⊥ := by
    rw [pow_succ']
    rw [show (Ideal.jacobson (⊥ : Ideal (C ⧸ Q))) ^ e = ⊥ from he]
    rw [Ideal.mul_bot]
  have hinf : (⨅ 𝔫, overMaximal Q 𝔫) ≤
      Ideal.comap (Ideal.Quotient.mk Q)
        (Ideal.jacobson (⊥ : Ideal (C ⧸ Q))) := by
    intro x hx
    rw [Ideal.mem_comap, Ideal.jacobson, Ideal.mem_sInf]
    rintro J ⟨-, hJmax⟩
    exact Ideal.mem_iInf.mp hx ⟨J, hJmax⟩
  calc (⨅ 𝔫, overMaximal Q 𝔫) ^ (e + 1) ≤
      (Ideal.comap (Ideal.Quotient.mk Q)
        (Ideal.jacobson (⊥ : Ideal (C ⧸ Q)))) ^ (e + 1) :=
        pow_le_pow_left' hinf (e + 1)
    _ ≤ Ideal.comap (Ideal.Quotient.mk Q)
        ((Ideal.jacobson (⊥ : Ideal (C ⧸ Q))) ^ (e + 1)) :=
        Ideal.le_comap_pow _ (e + 1)
    _ = Q := by
        rw [hjac]
        ext x
        rw [Ideal.mem_comap]
        change Ideal.Quotient.mk Q x ∈ (⊥ : Ideal (C ⧸ Q)) ↔ x ∈ Q
        rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]

open Classical in
/-- **The fibre splitting of the adic completion**: the `Q`-adic completion
is the product of the completions at the maximal ideals over `Q`. -/
noncomputable def AdicCompletion.fibreSplit :
    AdicCompletion Q C ≃+* ∀ 𝔫 : fibreMaximals Q,
      AdicCompletion (overMaximal Q 𝔫) C :=
  AdicCompletion.semilocalSplit Q (overMaximal Q)
    (pairwise_coprime_overMaximal Q) (le_overMaximal Q)
    (exists_pow_iInf_overMaximal_le Q).choose
    (exists_pow_iInf_overMaximal_le Q).choose_spec.1
    (exists_pow_iInf_overMaximal_le Q).choose_spec.2

section MapLevelwise

variable {A B : Type*} [CommRing A] [CommRing B]

open Classical in
/-- **Completion homomorphism from levelwise data**: a compatible family of
homomorphisms of power quotients induces a homomorphism of adic
completions. -/
noncomputable def AdicCompletion.mapLevelwise (I : Ideal A) (J : Ideal B)
    (g : ∀ r : ℕ, A ⧸ I ^ r →+* B ⧸ J ^ r)
    (hcompat : ∀ {a b : ℕ} (hab : a ≤ b) (x : A ⧸ I ^ b),
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) (g b x) =
        g a (Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) x)) :
    AdicCompletion I A →+* AdicCompletion J B where
  toFun x := ⟨fun r => (AdicCompletion.levelEquiv J r).symm
      (g r (AdicCompletion.levelEquiv I r (x.1 r))), by
    intro a b hab
    have h3 := AdicCompletion.levelEquiv_transitionMap J hab
      ((AdicCompletion.levelEquiv J b).symm
        (g b (AdicCompletion.levelEquiv I b (x.1 b))))
    rw [RingEquiv.apply_symm_apply] at h3
    refine (RingEquiv.eq_symm_apply _).mpr ?_
    rw [h3, hcompat hab]
    have h4 := AdicCompletion.levelEquiv_transitionMap I hab (x.1 b)
    rw [x.2 hab] at h4
    rw [← h4]⟩
  map_one' := Subtype.ext (funext fun r => by
    change (AdicCompletion.levelEquiv J r).symm
      (g r (AdicCompletion.levelEquiv I r ((1 : AdicCompletion I A).1 r))) = _
    rw [show ((1 : AdicCompletion I A)).1 r = 1 from rfl, map_one, map_one]
    exact map_one _)
  map_mul' x y := Subtype.ext (funext fun r => by
    change (AdicCompletion.levelEquiv J r).symm
      (g r (AdicCompletion.levelEquiv I r ((x * y).1 r))) = _
    rw [show (x * y).1 r = x.1 r * y.1 r from rfl, map_mul, map_mul, map_mul]
    rfl)
  map_zero' := Subtype.ext (funext fun r => by
    change (AdicCompletion.levelEquiv J r).symm
      (g r (AdicCompletion.levelEquiv I r ((0 : AdicCompletion I A).1 r))) =
      ((0 : AdicCompletion J B)).1 r
    rw [show ((0 : AdicCompletion I A)).1 r = 0 from rfl,
      show ((0 : AdicCompletion J B)).1 r = 0 from rfl,
      _root_.map_zero, _root_.map_zero, _root_.map_zero])
  map_add' x y := Subtype.ext (funext fun r => by
    change (AdicCompletion.levelEquiv J r).symm
      (g r (AdicCompletion.levelEquiv I r ((x + y).1 r))) = _
    rw [show (x + y).1 r = x.1 r + y.1 r from rfl, map_add, map_add, map_add]
    rfl)

open Classical in
theorem AdicCompletion.mapLevelwise_injective (I : Ideal A) (J : Ideal B)
    (g : ∀ r : ℕ, A ⧸ I ^ r →+* B ⧸ J ^ r)
    (hcompat : ∀ {a b : ℕ} (hab : a ≤ b) (x : A ⧸ I ^ b),
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) (g b x) =
        g a (Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) x))
    (hinj : ∀ r, Function.Injective (g r)) :
    Function.Injective (AdicCompletion.mapLevelwise I J g hcompat) := by
  intro x y hxy
  refine Subtype.ext (funext fun r => ?_)
  have h1 := congrFun (congrArg Subtype.val hxy) r
  have h1' : (AdicCompletion.levelEquiv J r).symm
      (g r (AdicCompletion.levelEquiv I r (x.1 r))) =
      (AdicCompletion.levelEquiv J r).symm
        (g r (AdicCompletion.levelEquiv I r (y.1 r))) := h1
  have h2 := (AdicCompletion.levelEquiv J r).symm.injective h1'
  exact (AdicCompletion.levelEquiv I r).injective (hinj r h2)

open Classical in
/-- **Reducedness descends along levelwise-injective completion maps.** -/
theorem AdicCompletion.isReduced_of_levelwise_injective (I : Ideal A)
    (J : Ideal B) (g : ∀ r : ℕ, A ⧸ I ^ r →+* B ⧸ J ^ r)
    (hcompat : ∀ {a b : ℕ} (hab : a ≤ b) (x : A ⧸ I ^ b),
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) (g b x) =
        g a (Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) x))
    (hinj : ∀ r, Function.Injective (g r))
    [IsReduced (AdicCompletion J B)] :
    IsReduced (AdicCompletion I A) :=
  isReduced_of_injective (AdicCompletion.mapLevelwise I J g hcompat)
    (AdicCompletion.mapLevelwise_injective I J g hcompat hinj)

open Classical in
/-- **Injectivity from cofinal levelwise kernels**: if kernel elements at a
cofinal level die under the transition maps, the induced completion map is
injective. -/
theorem AdicCompletion.mapLevelwise_injective_of_cofinal (I : Ideal A)
    (J : Ideal B) (g : ∀ r : ℕ, A ⧸ I ^ r →+* B ⧸ J ^ r)
    (hcompat : ∀ {a b : ℕ} (hab : a ≤ b) (x : A ⧸ I ^ b),
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) (g b x) =
        g a (Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) x))
    (hcof : ∀ r : ℕ, ∃ s : ℕ, ∃ hrs : r ≤ s, ∀ y : A ⧸ I ^ s, g s y = 0 →
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hrs) y = 0) :
    Function.Injective (AdicCompletion.mapLevelwise I J g hcompat) := by
  intro x y hxy
  suffices h : ∀ z : AdicCompletion I A,
      AdicCompletion.mapLevelwise I J g hcompat z = 0 → z = 0 by
    have h1 : AdicCompletion.mapLevelwise I J g hcompat (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (h _ h1)
  intro z hz
  refine Subtype.ext (funext fun r => ?_)
  obtain ⟨s, hrs, hkill⟩ := hcof r
  have hzs : g s (AdicCompletion.levelEquiv I s (z.1 s)) = 0 := by
    have h3 : (AdicCompletion.levelEquiv J s).symm
        (g s (AdicCompletion.levelEquiv I s (z.1 s))) =
        ((0 : AdicCompletion J B)).1 s :=
      congrFun (congrArg Subtype.val hz) s
    rw [show ((0 : AdicCompletion J B)).1 s = 0 from rfl] at h3
    have h4 := congrArg (AdicCompletion.levelEquiv J s) h3
    rwa [RingEquiv.apply_symm_apply, _root_.map_zero] at h4
  have h5 := hkill _ hzs
  have h6 := AdicCompletion.levelEquiv_transitionMap I hrs (z.1 s)
  rw [z.2 hrs] at h6
  have h7 : AdicCompletion.levelEquiv I r (z.1 r) = 0 := by
    rw [h6]
    exact h5
  have h8 : z.1 r = 0 := by
    have h9 := congrArg (AdicCompletion.levelEquiv I r).symm h7
    rwa [RingEquiv.symm_apply_apply, _root_.map_zero] at h9
  rw [h8]
  rfl

open Classical in
/-- **Reducedness from a cofinally injective levelwise map.** -/
theorem AdicCompletion.isReduced_of_levelwise_cofinal (I : Ideal A)
    (J : Ideal B) (g : ∀ r : ℕ, A ⧸ I ^ r →+* B ⧸ J ^ r)
    (hcompat : ∀ {a b : ℕ} (hab : a ≤ b) (x : A ⧸ I ^ b),
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) (g b x) =
        g a (Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) x))
    (hcof : ∀ r : ℕ, ∃ s : ℕ, ∃ hrs : r ≤ s, ∀ y : A ⧸ I ^ s, g s y = 0 →
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hrs) y = 0)
    [IsReduced (AdicCompletion J B)] :
    IsReduced (AdicCompletion I A) :=
  isReduced_of_injective (AdicCompletion.mapLevelwise I J g hcompat)
    (AdicCompletion.mapLevelwise_injective_of_cofinal I J g hcompat hcof)

end MapLevelwise

section MapLevelwisePi

variable {A : Type*} [CommRing A] {ι : Type*}
variable {B : ι → Type*} [∀ i, CommRing (B i)]

open Classical in
/-- **Completion homomorphism into a product from levelwise data.** -/
noncomputable def AdicCompletion.mapLevelwisePi (I : Ideal A)
    (J : ∀ i, Ideal (B i))
    (g : ∀ r : ℕ, A ⧸ I ^ r →+* ∀ i, B i ⧸ (J i) ^ r)
    (hcompat : ∀ {a b : ℕ} (hab : a ≤ b) (x : A ⧸ I ^ b) (i : ι),
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) (g b x i) =
        g a (Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) x) i) :
    AdicCompletion I A →+* ∀ i, AdicCompletion (J i) (B i) where
  toFun x := fun i => ⟨fun r => (AdicCompletion.levelEquiv (J i) r).symm
      (g r (AdicCompletion.levelEquiv I r (x.1 r)) i), by
    intro a b hab
    have h3 := AdicCompletion.levelEquiv_transitionMap (J i) hab
      ((AdicCompletion.levelEquiv (J i) b).symm
        (g b (AdicCompletion.levelEquiv I b (x.1 b)) i))
    rw [RingEquiv.apply_symm_apply] at h3
    refine (RingEquiv.eq_symm_apply _).mpr ?_
    rw [h3, hcompat hab]
    have h4 := AdicCompletion.levelEquiv_transitionMap I hab (x.1 b)
    rw [x.2 hab] at h4
    rw [← h4]⟩
  map_one' := funext fun i => Subtype.ext (funext fun r => by
    change (AdicCompletion.levelEquiv (J i) r).symm
      (g r (AdicCompletion.levelEquiv I r
        ((1 : AdicCompletion I A).1 r)) i) =
      ((1 : AdicCompletion (J i) (B i))).1 r
    rw [show ((1 : AdicCompletion I A)).1 r = 1 from rfl,
      show ((1 : AdicCompletion (J i) (B i))).1 r = 1 from rfl,
      map_one, map_one]
    change (AdicCompletion.levelEquiv (J i) r).symm
      ((1 : ∀ j, B j ⧸ (J j) ^ r) i) = 1
    rw [show (1 : ∀ j, B j ⧸ (J j) ^ r) i = 1 from rfl, map_one])
  map_mul' x y := funext fun i => Subtype.ext (funext fun r => by
    change (AdicCompletion.levelEquiv (J i) r).symm
      (g r (AdicCompletion.levelEquiv I r ((x * y).1 r)) i) = _
    rw [show (x * y).1 r = x.1 r * y.1 r from rfl, map_mul, map_mul]
    rw [show (g r (AdicCompletion.levelEquiv I r (x.1 r)) *
        g r (AdicCompletion.levelEquiv I r (y.1 r))) i =
      g r (AdicCompletion.levelEquiv I r (x.1 r)) i *
        g r (AdicCompletion.levelEquiv I r (y.1 r)) i from rfl, map_mul]
    rfl)
  map_zero' := funext fun i => Subtype.ext (funext fun r => by
    change (AdicCompletion.levelEquiv (J i) r).symm
      (g r (AdicCompletion.levelEquiv I r
        ((0 : AdicCompletion I A).1 r)) i) =
      ((0 : AdicCompletion (J i) (B i))).1 r
    rw [show ((0 : AdicCompletion I A)).1 r = 0 from rfl,
      show ((0 : AdicCompletion (J i) (B i))).1 r = 0 from rfl,
      _root_.map_zero, _root_.map_zero]
    change (AdicCompletion.levelEquiv (J i) r).symm
      ((0 : ∀ j, B j ⧸ (J j) ^ r) i) = 0
    rw [show (0 : ∀ j, B j ⧸ (J j) ^ r) i = 0 from rfl, _root_.map_zero])
  map_add' x y := funext fun i => Subtype.ext (funext fun r => by
    change (AdicCompletion.levelEquiv (J i) r).symm
      (g r (AdicCompletion.levelEquiv I r ((x + y).1 r)) i) = _
    rw [show (x + y).1 r = x.1 r + y.1 r from rfl, map_add, map_add]
    rw [show (g r (AdicCompletion.levelEquiv I r (x.1 r)) +
        g r (AdicCompletion.levelEquiv I r (y.1 r))) i =
      g r (AdicCompletion.levelEquiv I r (x.1 r)) i +
        g r (AdicCompletion.levelEquiv I r (y.1 r)) i from rfl, map_add]
    rfl)

open Classical in
theorem AdicCompletion.mapLevelwisePi_injective_of_cofinal (I : Ideal A)
    (J : ∀ i, Ideal (B i))
    (g : ∀ r : ℕ, A ⧸ I ^ r →+* ∀ i, B i ⧸ (J i) ^ r)
    (hcompat : ∀ {a b : ℕ} (hab : a ≤ b) (x : A ⧸ I ^ b) (i : ι),
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) (g b x i) =
        g a (Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) x) i)
    (hcof : ∀ r : ℕ, ∃ s : ℕ, ∃ hrs : r ≤ s, ∀ y : A ⧸ I ^ s, g s y = 0 →
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hrs) y = 0) :
    Function.Injective
      (AdicCompletion.mapLevelwisePi I J g hcompat) := by
  intro x y hxy
  suffices h : ∀ z : AdicCompletion I A,
      AdicCompletion.mapLevelwisePi I J g hcompat z = 0 → z = 0 by
    have h1 : AdicCompletion.mapLevelwisePi I J g hcompat (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (h _ h1)
  intro z hz
  refine Subtype.ext (funext fun r => ?_)
  obtain ⟨s, hrs, hkill⟩ := hcof r
  have hzs : g s (AdicCompletion.levelEquiv I s (z.1 s)) = 0 := by
    funext i
    have h3 : (AdicCompletion.levelEquiv (J i) s).symm
        (g s (AdicCompletion.levelEquiv I s (z.1 s)) i) =
        ((0 : AdicCompletion (J i) (B i))).1 s :=
      congrFun (congrArg Subtype.val (congrFun hz i)) s
    rw [show ((0 : AdicCompletion (J i) (B i))).1 s = 0 from rfl] at h3
    have h4 := congrArg (AdicCompletion.levelEquiv (J i) s) h3
    rw [RingEquiv.apply_symm_apply, _root_.map_zero] at h4
    exact h4
  have h5 := hkill _ hzs
  have h6 := AdicCompletion.levelEquiv_transitionMap I hrs (z.1 s)
  rw [z.2 hrs] at h6
  have h7 : AdicCompletion.levelEquiv I r (z.1 r) = 0 := by
    rw [h6]
    exact h5
  have h8 : z.1 r = 0 := by
    have h9 := congrArg (AdicCompletion.levelEquiv I r).symm h7
    rwa [RingEquiv.symm_apply_apply, _root_.map_zero] at h9
  rw [h8]
  rfl

open Classical in
/-- **Reducedness from a cofinally injective levelwise map into a product of
completions.** -/
theorem AdicCompletion.isReduced_of_levelwisePi_cofinal (I : Ideal A)
    (J : ∀ i, Ideal (B i))
    (g : ∀ r : ℕ, A ⧸ I ^ r →+* ∀ i, B i ⧸ (J i) ^ r)
    (hcompat : ∀ {a b : ℕ} (hab : a ≤ b) (x : A ⧸ I ^ b) (i : ι),
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) (g b x i) =
        g a (Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) x) i)
    (hcof : ∀ r : ℕ, ∃ s : ℕ, ∃ hrs : r ≤ s, ∀ y : A ⧸ I ^ s, g s y = 0 →
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hrs) y = 0)
    [∀ i, IsReduced (AdicCompletion (J i) (B i))] :
    IsReduced (AdicCompletion I A) :=
  isReduced_of_injective (AdicCompletion.mapLevelwisePi I J g hcompat)
    (AdicCompletion.mapLevelwisePi_injective_of_cofinal I J g hcompat hcof)

end MapLevelwisePi

end SemilocalFibre
