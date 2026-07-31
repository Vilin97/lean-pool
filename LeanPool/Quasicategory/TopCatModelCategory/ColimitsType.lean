/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.BicartesianSq
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.Order.CompleteLattice.MulticoequalizerDiagram
import Mathlib.Data.Set.Lattice
import Mathlib.CategoryTheory.Types.Set
import LeanPool.Quasicategory.TopCatModelCategory.Multiequalizer

universe v u

open CategoryTheory Limits

/-namespace Lattice

variable {T : Type u} (x₁ x₂ x₃ x₄ : T) [Lattice T]

structure BicartSq : Prop where
  max_eq : x₂ ⊔ x₃ = x₄
  min_eq : x₂ ⊓ x₃ = x₁

namespace BicartSq

variable {x₁ x₂ x₃ x₄ : T} (sq : BicartSq x₁ x₂ x₃ x₄)

include sq
lemma le₁₂ : x₁ ≤ x₂ := by rw [← sq.min_eq]; exact inf_le_left
lemma le₁₃ : x₁ ≤ x₃ := by rw [← sq.min_eq]; exact inf_le_right
lemma le₂₄ : x₂ ≤ x₄ := by rw [← sq.max_eq]; exact le_sup_left
lemma le₃₄ : x₃ ≤ x₄ := by rw [← sq.max_eq]; exact le_sup_right

-- the associated commutative square in `T`
lemma commSq : CommSq (homOfLE sq.le₁₂) (homOfLE sq.le₁₃)
    (homOfLE sq.le₂₄) (homOfLE sq.le₃₄) := ⟨rfl⟩

end BicartSq

end Lattice-/

@[deprecated (since := "2025-03-18")] alias Set.toTypes := Set.functorToTypes

namespace CategoryTheory.Limits.Types

section Pushouts

section

variable {X X' : Type u} (f : X' → X) (A B : Set X) (A' B' : Set X')
  (hA' : A' = f ⁻¹' A ⊓ B') (hB : B = A ⊔ f '' B')

def pushoutCoconeOfPullbackSets :
    PushoutCocone
      (↾(fun ⟨a', ha'⟩ ↦ (⟨f a', by
        rw [hA'] at ha'
        exact ha'.1⟩ : ↥A)) : (A' : Type u) ⟶ (A : Type u) )
      (Set.functorToTypes.map (homOfLE (by rw [hA']; exact inf_le_right)) : (A' : Type u) ⟶ B') :=
  PushoutCocone.mk (W := (B : Type u))
    (Set.functorToTypes.map (homOfLE (by rw [hB]; exact le_sup_left)) : (A : Type u) ⟶ B)
    (↾(fun ⟨b', hb'⟩ ↦ (⟨f b', by rw [hB]; exact Or.inr (by aesop)⟩ : ↥B))) rfl

variable (T : Set X)

open Classical in
noncomputable def isColimitPushoutCoconeOfPullbackSets
    (hf : Function.Injective (fun (b : (A'ᶜ : Set _)) ↦ f b)) :
    IsColimit (pushoutCoconeOfPullbackSets f A B A' B' hA' hB) := by
  let g₁ : (A' : Type u) ⟶ A := ↾(fun ⟨a', ha'⟩ ↦ (⟨f a', by
        rw [hA'] at ha'
        exact ha'.1⟩ : ↥A))
  let g₂ : (A' : Type u) ⟶ B' :=
    (Set.functorToTypes.map (homOfLE (by rw [hA']; exact inf_le_right)) : (A' : Type u) ⟶ B')
  have imp {b : X} (hb : b ∈ B) (hb' : b ∉ A) : b ∈ f '' B' := by
    simp only [hB, Set.sup_eq_union, Set.mem_union] at hb
    tauto
  let desc (s : PushoutCocone g₁ g₂) : (B : Type u) ⟶ s.pt := ↾(fun ⟨b, hb⟩ ↦
    if hb' : b ∈ A then
      s.inl ⟨b, hb'⟩
    else
      s.inr ⟨(imp hb hb').choose, (imp hb hb').choose_spec.1⟩)
  have inl_desc_apply (s) (a : A) : desc s ⟨a, by
    rw [hB]
    exact Or.inl a.2⟩ = s.inl a := dif_pos a.2
  have inr_desc_apply (s) (b' : B') : desc s ⟨f b', by
      rw [hB]
      exact Or.inr ⟨b'.1, b'.2, rfl⟩⟩ = s.inr b' := by
    obtain ⟨b', hb'⟩ := b'
    dsimp [desc]
    split_ifs with hb''
    · exact ConcreteCategory.congr_hom s.condition ⟨b', by rw [hA']; exact ⟨hb'', hb'⟩⟩
    · apply congr_arg
      ext
      have hb''' : f b' ∈ B := by
        rw [hB]
        exact Or.inr ⟨b', hb', rfl⟩
      dsimp
      subst hA'
      refine congr_arg Subtype.val (@hf ⟨(imp hb''' hb'').choose, ?_⟩ ⟨b', ?_⟩
        (imp hb''' hb'').choose_spec.2)
      · simp only [Set.inf_eq_inter, Set.mem_compl_iff, Set.mem_inter_iff, not_and]
        refine fun h _ ↦ hb'' ?_
        rw [← (imp hb''' hb'').choose_spec.2]
        exact h
      · simp only [Set.inf_eq_inter, Set.mem_compl_iff, Set.mem_inter_iff, not_and]
        exact fun h ↦ (hb'' h).elim
  refine PushoutCocone.IsColimit.mk _ desc
    (fun s ↦ by ext; apply inl_desc_apply)
    (fun s ↦ by ext; apply inr_desc_apply)
    (fun s m h₁ h₂ ↦ ?_)
  ext ⟨b, hb⟩
  dsimp
  by_cases hb' : b ∈ f '' B'
  · obtain ⟨b', hb', rfl⟩ := hb'
    exact (ConcreteCategory.congr_hom h₂ ⟨b', hb'⟩).trans (inr_desc_apply s ⟨b', hb'⟩ ).symm
  · have hb : b ∈ A := by
      simp only [hB, Set.sup_eq_union, Set.mem_union] at hb
      tauto
    exact (ConcreteCategory.congr_hom h₁ ⟨b, hb⟩).trans (inl_desc_apply s ⟨b, hb⟩).symm

end

section

variable {X : Type u} {A₁ A₂ A₃ A₄ : Set X} (sq : Lattice.BicartSq A₁ A₂ A₃ A₄)

def pushoutCoconeOfBicartSqOfSets :
    PushoutCocone (Set.functorToTypes.map (homOfLE sq.le₁₂))
      (Set.functorToTypes.map (homOfLE sq.le₁₃)) :=
  PushoutCocone.mk _ _ (sq.commSq.map Set.functorToTypes).w

noncomputable def isColimitPushoutCoconeOfBicartSqOfSets :
    IsColimit (pushoutCoconeOfBicartSqOfSets sq) :=
  isColimitPushoutCoconeOfPullbackSets id A₂ A₄ A₁ A₃
    sq.inf_eq.symm (by simpa using sq.sup_eq.symm)
      (by rintro ⟨a, _⟩ ⟨b, _⟩ rfl; rfl)

end

end Pushouts

end CategoryTheory.Limits.Types

/-namespace CompleteLattice

variable {T : Type*} [CompleteLattice T] {ι : Type*} (X : T) (U : ι → T) (V : ι → ι → T)

structure MulticoequalizerDiagram : Prop where
  hX : X = ⨆ (i : ι), U i
  hV (i j : ι) : V i j = U i ⊓ U j

namespace MulticoequalizerDiagram

variable {X U V} (d : MulticoequalizerDiagram X U V)

@[simps]
def multispanIndex : MultispanIndex T where
  L := ι × ι
  R := ι
  fstFrom := Prod.fst
  sndFrom := Prod.snd
  left := fun ⟨i, j⟩ ↦ V i j
  right := U
  fst _ := homOfLE (by
    dsimp
    rw [d.hV]
    exact inf_le_left)
  snd _ := homOfLE (by
    dsimp
    rw [d.hV]
    exact inf_le_right)

@[simps! pt]
def multicofork : Multicofork d.multispanIndex :=
  Multicofork.ofπ _ X (fun i ↦ homOfLE (by simpa only [d.hX] using le_iSup U i))
    (fun _ ↦ rfl)

variable [Preorder ι]

@[simps]
def multispanIndex' : MultispanIndex T where
  L := { (i, j) : ι × ι | i < j }
  R := ι
  fstFrom := fun ⟨⟨i, j⟩, _⟩ ↦ i
  sndFrom := fun ⟨⟨i, j⟩, _⟩ ↦ j
  left := fun ⟨⟨i, j⟩, _⟩ ↦ V i j
  right := U
  fst _ := homOfLE (by
    dsimp
    rw [d.hV]
    exact inf_le_left)
  snd _ := homOfLE (by
    dsimp
    rw [d.hV]
    exact inf_le_right)

@[simps! pt]
def multicofork' : Multicofork d.multispanIndex' :=
  Multicofork.ofπ _ X (fun i ↦ homOfLE (by simpa only [d.hX] using le_iSup U i))
    (fun _ ↦ rfl)


end MulticoequalizerDiagram

end CompleteLattice-/

namespace CategoryTheory.Limits

namespace Types

section

variable {T : Type u} {ι : Type v} {X : Set T} {U : ι → Set T} {V : ι → ι → Set T}
  (d : CompleteLattice.MulticoequalizerDiagram X U V)

namespace isColimitMulticoforkMapSetToTypes

include d in
lemma exists_index (x : X) : ∃ (i : ι), x.1 ∈ U i := by
  obtain ⟨x, hx⟩ := x
  rw [← d.iSup_eq] at hx
  aesop

noncomputable def index (x : X) : ι := (exists_index d x).choose

lemma mem (x : X) : x.1 ∈ U (index d x) := (exists_index d x).choose_spec

section

variable {d} (s : Multicofork (d.multispanIndex.map Set.functorToTypes))

noncomputable def desc (x : X) : s.pt := s.π (index d x) ⟨x, mem d x⟩

lemma fac_apply (i : ι) (u : U i) :
    desc s ⟨u, by simp only [← d.iSup_eq]; aesop⟩ = s.π i u :=
  ConcreteCategory.congr_hom (s.condition ⟨index d _, i⟩) ⟨u, by
    simp only [CompleteLattice.MulticoequalizerDiagram.multispanIndex_left, d.eq_inf,
      Set.inf_eq_inter, Set.mem_inter_iff, Subtype.coe_prop, and_true]
    apply mem⟩

end

/-section

variable [LinearOrder ι] {d} (s : Multicofork (d.multispanIndex'.map Set.functorToTypes))

noncomputable def desc' (x : X) : s.pt := s.π (index d x) ⟨x, mem d x⟩

lemma condition'_apply (x : T) (i j : ι) (hi : x ∈ U i) (hj : x ∈ U j) :
    s.π i ⟨x, hi⟩ = s.π j ⟨x, hj⟩ := by
  obtain hij | rfl | hij := lt_trichotomy i j
  · refine ConcreteCategory.congr_hom (s.condition ⟨⟨i, j⟩, hij⟩) ⟨x, ?_⟩
    dsimp
    rw [d.hV]
    exact ⟨hi, hj⟩
  · rfl
  · refine ConcreteCategory.congr_hom (s.condition ⟨⟨j, i⟩, hij⟩).symm ⟨x, ?_⟩
    dsimp
    rw [d.hV]
    exact ⟨hj, hi⟩

lemma fac'_apply (i : ι) (u : U i) :
    desc' s ⟨u, by simp only [d.hX]; aesop⟩ = s.π i u := by
  apply condition'_apply

end-/

end isColimitMulticoforkMapSetToTypes

open isColimitMulticoforkMapSetToTypes in
noncomputable def isColimitMulticoforkMapSetToTypes :
    IsColimit (d.multicofork.map Set.functorToTypes) :=
  Multicofork.IsColimit.mk _ (fun s ↦ ↾(desc s)) (fun s i ↦ by ext x; apply fac_apply)
    (fun s m hm ↦ by
      ext x
      exact ConcreteCategory.congr_hom (hm (index d x)) ⟨x.1, mem d x⟩)

open isColimitMulticoforkMapSetToTypes in
noncomputable def isColimitMulticoforkMapSetToTypes' [LinearOrder ι] :
    IsColimit (d.multicofork.toLinearOrder.map Set.functorToTypes) :=
  Multicofork.isColimitToLinearOrder
    (d.multicofork.map Set.functorToTypes) (isColimitMulticoforkMapSetToTypes _)
    { iso i j := Set.functorToTypes.mapIso (eqToIso (by
        simp only [CompleteLattice.MulticoequalizerDiagram.multispanIndex_left, d.eq_inf,
          inf_comm]))
      iso_hom_fst _ _ := rfl
      iso_hom_snd _ _ := rfl
      fst_eq_snd _ := rfl }

end

lemma isPullback_of_eq_setPreimage {X Y : Type u} (f : X ⟶ Y) (B : Set Y) {A : Set X}
    (hA : A = B.preimage f) :
    IsPullback (↾(fun (⟨a, ha⟩ : A) ↦ (⟨f a, by simpa [hA] using ha⟩ : B)))
      (↾Subtype.val) (↾Subtype.val) f := by
  rw [isPullback_iff]
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨x₁, _⟩ ⟨_, _⟩ ⟨_, rfl⟩
    rfl
  · rintro ⟨_, hx₃⟩ x₃ rfl
    exact ⟨⟨x₃, by rwa [hA]⟩, rfl, rfl⟩

section

variable {ι : Type v} {X : ι → Type u} {c : Cofan X} (hc : IsColimit c)

include hc
lemma jointly_surjective_of_isColimit_cofan (x : c.pt) :
    ∃ (i : ι) (y : X i), c.inj i y = x :=
  Cofan.inj_jointly_surjective_of_isColimit hc x

lemma cofanInj_apply_eq_iff_of_isColimit {i j : ι} (x : X i) (y : X j) :
    c.inj i x = c.inj j y ↔ ∃ (hij : i = j), y = cast (by rw [hij]) x :=
  Cofan.inj_apply_eq_iff_of_isColimit hc x y

lemma cofanInj_injective_of_isColimit (i : ι) :
    Function.Injective (c.inj i) :=
  Cofan.inj_injective_of_isColimit hc i

lemma eq_cofanInj_apply_eq_of_isColimit {i j : ι} (x : X i) (y : X j)
    (h : c.inj i x = c.inj j y) : i = j :=
  Cofan.eq_of_inj_apply_eq_of_isColimit hc x y h

lemma preimage_image_eq_of_coproducts
    {X' : ι → Type u} {c' : Cofan X'} (hc' : IsColimit c') (f : ∀ i, X i ⟶ X' i)
    (φ : c.pt ⟶ c'.pt) (hφ : ∀ i, c.inj i ≫ φ = f i ≫ c'.inj i)
    (i : ι) (F : Set (X' i)) :
    φ ⁻¹' (c'.inj i '' F) = c.inj i '' ((f i) ⁻¹' F) := by
  replace hφ {i : ι} (x : X i) : φ (c.inj i x) = c'.inj i (f i x) :=
    ConcreteCategory.congr_hom (hφ i) x
  ext y
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨x, hx, eq⟩
    obtain ⟨j, z, rfl⟩ := jointly_surjective_of_isColimit_cofan hc y
    rw [hφ] at eq
    obtain rfl := eq_cofanInj_apply_eq_of_isColimit hc' _ _ eq
    obtain rfl := cofanInj_injective_of_isColimit hc' i eq
    refine ⟨z, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, hx, (hφ x).symm⟩

end

section

variable {S X₁ X₂ : Type u} (f : S ⟶ X₁) (g : S ⟶ X₂)

lemma Pushout.inl_eq_inl_iff [Mono f] (x₁ y₁ : X₁) :
    (inl f g x₁ = inl f g y₁) ↔
      x₁ = y₁ ∨ ∃ x₀ y₀, x₁ = f x₀ ∧ y₁ = f y₀ ∧ g x₀ = g y₀ :=
  (Pushout.quot_mk_eq_iff f g (Sum.inl x₁) (Sum.inl y₁)).trans (by aesop)

variable {f g}

lemma pushoutCocone_inl_eq_inl_imp_of_iso {c c' : PushoutCocone f g} (e : c ≅ c')
    (x₁ y₁ : X₁) (h : c.inl x₁ = c.inl y₁) :
    c'.inl x₁ = c'.inl y₁ := by
  convert congr_arg e.hom.hom h
  all_goals apply ConcreteCategory.congr_hom (e.hom.w WalkingSpan.left).symm

lemma pushoutCocone_inl_eq_inl_iff_of_iso {c c' : PushoutCocone f g} (e : c ≅ c')
    (x₁ y₁ : X₁) :
    c.inl x₁ = c.inl y₁ ↔ c'.inl x₁ = c'.inl y₁ := by
  constructor
  · apply pushoutCocone_inl_eq_inl_imp_of_iso e
  · apply pushoutCocone_inl_eq_inl_imp_of_iso e.symm

lemma pushoutCocone_inl_eq_inl_iff_of_isColimit {c : PushoutCocone f g} (hc : IsColimit c)
    (h₁ : Function.Injective f) (x₁ y₁ : X₁) :
    c.inl x₁ = c.inl y₁ ↔
      x₁ = y₁ ∨ ∃ x₀ y₀, x₁ = f x₀ ∧ y₁ = f y₀ ∧ g x₀ = g y₀ := by
  rw [pushoutCocone_inl_eq_inl_iff_of_iso
    (Cocone.ext (IsColimit.coconePointUniqueUpToIso hc (Pushout.isColimitCocone f g))
    (fun j ↦ hc.comp_coconePointUniqueUpToIso_hom _ j))]
  have := (mono_iff_injective f).2 h₁
  apply Pushout.inl_eq_inl_iff f g

end


section

variable {X₁ X₂ X₃ X₄ : Type u} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
  {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

lemma preimage_image_eq_of_isPushout (sq : IsPushout t l r b) (ht : Function.Injective t)
    (F : Set X₃) :
    r ⁻¹' (b '' F) = t '' (l ⁻¹' F) := by
  ext x₂
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨x₃, hx₃, hx₃'⟩
    obtain ⟨x₁, rfl, rfl⟩ := (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
      sq.isColimit ht x₂ x₃).1 hx₃'.symm
    exact ⟨x₁, hx₃, rfl⟩
  · rintro ⟨x₁, hx₁, rfl⟩
    exact ⟨l x₁, hx₁, ConcreteCategory.congr_hom sq.w.symm x₁⟩

lemma injective_of_isPushout (sq : IsPushout t l r b) (ht : Function.Injective t) :
    Function.Injective b :=
  Types.pushoutCocone_inr_injective_of_isColimit sq.isColimit ht

end

end Types

end CategoryTheory.Limits
