/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.InfLists
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Tree.Trees

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Tree.TreeBody

Auxiliary declarations for the Borel determinacy formalization.
-/


namespace Descriptive.Tree
open Stream'.Discrete

variable {A : Type*} (S T : tree A)

/-- The body of a tree T, also written [T] in the literature, is the set of infinite branches,
  implemented as `Stream` -/
def body : Set (Stream' A) := { y | ∀ x, y ∈ principalOpen x → x ∈ T }
@[gcongr] lemma body_mono {S T : tree A} (h : S ≤ T) : body S ⊆ body T :=
  fun _ h' x y ↦ h (h' x y)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simp] lemma take_mem_body {T : tree A} {x} (h : x ∈ body T) n : x.take n ∈ T := h _ (by simp)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps coe] def body.take {T : tree A} (n : ℕ) (x : body T) : T := ⟨_, take_mem_body x.2 n⟩
attribute [simp_lengths] body.take_coe
lemma mem_body_of_take m (T : tree A) (x : Stream' A) (h : ∀ n ≥ m, x.take n ∈ T) :
  x ∈ body T := by
  intro y hy; rw [principalOpen_iff_restrict] at hy
  simpa [← hy] using Tree.take_mem ⟨_, h (m + y.length) (by omega)⟩ (n := y.length)

/-- Taking bodies preserves arbitrary intersections -/
def bodyInfHom : sInfHom (tree A) (Set (Stream' A)) where
  toFun := Tree.body
  map_sInf' := by
    intro s; ext a; simp only [body, principalOpen, Set.mem_range, CompleteSublattice.mem_sInf,
      forall_exists_index, Set.sInf_eq_sInter, Set.sInter_image, Set.mem_iInter]
    constructor
    · rintro h T hT x a rfl; exact h x a rfl _ hT
    · rintro h x a rfl T hT; exact h T hT _ _ rfl
@[simp] lemma body_inter {S T : tree A} : body (S ⊓ T) = body S ∩ body T := by
  change bodyInfHom (S ⊓ T) = bodyInfHom S ∩ bodyInfHom T; simp
@[simp] lemma body_bot : body (⊥ : tree A) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]; exact fun x h ↦ h [] (by simp)
@[simp] lemma body_isClosed : IsClosed (body T) := by
  simp_rw [← isOpen_compl_iff, isOpen_iff_mem_nhds, mem_nhds_iff]
  intro a ha
  conv at ha => simp [body]
  let ⟨x, ha1, ha2⟩ := ha
  exact ⟨principalOpen x, fun a ah h ↦ ha2 (h _ ah), principalOpen_isOpen x, ha1⟩

@[simp] lemma subAt_body (x : List A) :
  body (subAt T x) = (x ++ₛ ·)⁻¹' (body T) := by
  ext a; constructor
  · intro h y ⟨b, h'⟩
    apply mem_of_append (y := b.take (x.length - y.length))
    have hx : x ++ a.take (y.length - x.length) ∈ T := by
      simpa using h (a.take (y.length - x.length)) (extend_sub _ _)
    convert hx using 1
    apply List.ext_getElem (by simp; omega)
    simp [Stream'.append_take, h']
  · intro h _ _; apply h; simpa

/-- Appending lists to the front of a branch lifts as an operation on bodies -/
@[simps -fullyApplied coe]
def body.append {T : tree A} (x : List A) (y : body (subAt T x)) : body T :=
  ⟨x ++ₛ y.val, by simpa using y.prop⟩
@[simp] lemma body_append_nil (y : body T) : body.append (T := no_index _) [] y = y := rfl
lemma body.append_con {T : tree A} (x : List A) : Continuous (@body.append A T x) :=
  Topology.IsInducing.subtypeVal.continuous_iff.mpr <|
    (Stream'.Discrete.append_con x).comp continuous_subtype_val
@[congr] lemma range_body_append (x y : List A) (h : x = y) :
  Set.range (@body.append _ T x) = Set.range (@body.append _ T y) := by congr!
@[simp] lemma subtype_body_append x :
  Subtype.val '' Set.range (@body.append _ T x) = principalOpen x ∩ body T := by
  ext a; constructor
  · rintro ⟨_, ⟨⟨a, rfl⟩, rfl⟩⟩
    exact ⟨by simp, by simpa [subAt_body] using a.prop⟩
  · rintro ⟨⟨b, rfl⟩, ha⟩; use ⟨x ++ₛ b, ha⟩, ⟨⟨b, by simpa⟩, rfl⟩
/-- Dropping the first elements of a branch lifts as an operation on bodies -/
@[simps -fullyApplied coe]
def body.drop {T : tree A} (n : ℕ) (x : body T) : body (subAt T (x.val.take n)) :=
  ⟨x.1.drop n, by simp⟩

section «Section1»
variable {T : tree A} (X : Set (body T)) (x : List A)
@[simp] lemma subAt_body_image : Subtype.val '' ((body.append x)⁻¹' X)
  = (x ++ₛ ·)⁻¹' (Subtype.val '' X) := by
  ext; simp; tauto
lemma subAt_body_image_compl : Subtype.val '' ((body.append x)⁻¹' X)ᶜ
    = (x ++ₛ ·)⁻¹' body T \ (x ++ₛ ·)⁻¹' (Subtype.val '' X) := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    constructor
    · exact (body.append x b).prop
    · rintro ⟨z, hz, hz_eq⟩
      apply hb
      have hbz : body.append x b = z := Subtype.ext hz_eq.symm
      simpa [hbz] using hz
  · intro h
    refine ⟨⟨a, ?_⟩, ?_, rfl⟩
    · simpa [subAt_body] using h.1
    · intro ha
      exact h.2 ⟨body.append x ⟨a, by simpa [subAt_body] using h.1⟩, ha, rfl⟩
lemma subAt_body_image_compl_preimage (y : List A) :
    (fun a ↦ y ++ₛ a) ⁻¹' (Subtype.val '' ((body.append x)⁻¹' X)ᶜ)
      = (fun a ↦ x ++ₛ (y ++ₛ a)) ⁻¹' body T \
        (fun a ↦ x ++ₛ (y ++ₛ a)) ⁻¹' (Subtype.val '' X) := by
  ext a
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_compl_iff, Subtype.exists, subAt_body,
    exists_and_right, exists_eq_right, Set.mem_sdiff, not_exists]
  tauto
lemma subAt_body_image_compl_compl_preimage (y : List A) :
    (fun a ↦ y ++ₛ a) ⁻¹' (Subtype.val '' ((body.append x)⁻¹' X)ᶜᶜ)
      = (fun a ↦ x ++ₛ (y ++ₛ a)) ⁻¹' (Subtype.val '' X) := by
  ext a
  simp
lemma mem_subAt_body y : y ∈ (body.append x)⁻¹' X ↔ x ++ₛ y.val ∈ Subtype.val '' X := by
  simp [body.append, by simpa using y.prop]
end «Section1»

@[simp] lemma pullSub_body (T : tree A) (x : List A) :
  body (pullSub T x) = (x ++ₛ ·) '' body T := by
  ext y; constructor
  · intro h; obtain ⟨z, hzT, hzE⟩ :=
      (mem_pullSub_long (y := y.take x.length) (by simp)).mp (h _ (by simp))
    have hzE' := congr_arg List.length hzE; conv at hzE' => simp
    subst hzE'; conv at hzE => simp
    rw [← Stream'.append_take_drop x.length y, hzE]
    conv => simp
    intro z hz; specialize h (x ++ z); rw [← Stream'.append_take_drop x.length y, hzE] at h
    simpa using h (by rwa [principalOpen_append])
  · rintro ⟨a, haB, rfl⟩; apply mem_body_of_take x.length
    intro n hn; obtain ⟨m, rfl⟩ := le_iff_exists_add.mp hn; rw [← Stream'.append_take]
    simp [haB]

lemma IsPruned.body_ne_iff_ne {T : tree A} (h : IsPruned T) :
  (body T).Nonempty ↔ [] ∈ T := by
  constructor
  · intro ⟨a, ha⟩; apply ha; simp
  · intro hne
    let f (n : ℕ) : T := Nat.recOn n ⟨[], hne⟩ (fun _ p ↦ ⟨_, (Classical.choice (h p)).prop⟩)
    let a (n : ℕ) : A := List.getLast (f (n + 1)).val (by simp [f])
    use a; intro x h'; suffices x = (f x.length).val by rw [this]; exact (f x.length).prop
    induction x using List.reverseRecOn with
    | nil => dsimp [f]
    | append_singleton x b ih =>
      specialize ih (principalOpen_sub _ _ h')
      rw [List.length_append, List.length_eq_one_iff.mpr ⟨b, rfl⟩]
      obtain ⟨z, h'⟩ := h'; apply_fun (fun y ↦ y.get x.length) at h'; conv at h' => simp
      simp_rw [h', a]; congr!; simp [Stream'.get, f]
lemma isPruned_iff_principalOpen_ne {T : tree A} :
  IsPruned T ↔ ∀ x : T, (principalOpen x ∩ body T).Nonempty := by
  constructor
  · intro hP x; obtain ⟨y, h⟩ := (hP.sub x.val).body_ne_iff_ne.mpr (by simp)
    use x.val ++ₛ y; simpa using h
  · intro h x; obtain ⟨y, hx, hT⟩ := h x; use y.get x.val.length
    rw [principalOpen_iff_restrict] at hx; nth_rw 1 [hx, ← Stream'.take_succ']
    exact hT _ (extend_sub _ y)

end Descriptive.Tree
