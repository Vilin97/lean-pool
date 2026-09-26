/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import Mathlib.Topology.Piecewise
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Homeomorph.Lemmas

/-! # Continuous extension across two omitted points -/

@[expose] public noncomputable section
open Set Filter
open scoped Topology
namespace LichnerowiczObata

variable {X Y : Type*}

/-- Replace the values at two specified points, leaving every other value
unchanged. The second point is updated last. -/
def twoPointUpdate (f : X → Y) (a b : X) (A B : Y) : X → Y := by
  classical
  exact Function.update (Function.update f a A) b B

theorem twoPointUpdate_first (f : X → Y) {a b : X} (hab : a ≠ b) (A B : Y) :
    twoPointUpdate f a b A B a = A := by
  classical
  simp [twoPointUpdate, Function.update_of_ne hab]

theorem twoPointUpdate_second (f : X → Y) (a b : X) (A B : Y) :
    twoPointUpdate f a b A B b = B := by
  classical
  simp [twoPointUpdate]

theorem twoPointUpdate_of_ne (f : X → Y) {a b x : X} (A B : Y)
    (hxa : x ≠ a) (hxb : x ≠ b) : twoPointUpdate f a b A B x = f x := by
  classical
  simp [twoPointUpdate, Function.update_of_ne, hxa, hxb]

variable [TopologicalSpace X] [T1Space X] [TopologicalSpace Y]

/-- Limits of the restriction away from two points suffice for a
continuous global extension. The two limiting values are retained exactly. -/
theorem continuous_twoPointUpdate (f : X → Y) {a b : X} (hab : a ≠ b) (A B : Y)
    (hf : ∀ x, x ≠ a → x ≠ b → ContinuousAt f x)
    (hA : Tendsto (fun x : {x : X // x ≠ a ∧ x ≠ b} => f x)
      (Filter.comap Subtype.val (𝓝 a)) (𝓝 A))
    (hB : Tendsto (fun x : {x : X // x ≠ a ∧ x ≠ b} => f x)
      (Filter.comap Subtype.val (𝓝 b)) (𝓝 B)) :
    Continuous (twoPointUpdate f a b A B) := by
  classical
  have ha : Set.range (Subtype.val : {x : X // x ≠ a ∧ x ≠ b} → X) ∈ 𝓝[≠] a := by
    filter_upwards [self_mem_nhdsWithin, eventually_ne_nhdsWithin hab] with x hxa hxb
    exact ⟨⟨x, by simpa only [mem_compl_iff, mem_singleton_iff] using And.intro hxa hxb⟩, rfl⟩
  have hb : Set.range (Subtype.val : {x : X // x ≠ a ∧ x ≠ b} → X) ∈ 𝓝[≠] b := by
    filter_upwards [eventually_ne_nhdsWithin hab.symm, self_mem_nhdsWithin] with x hxa hxb
    exact ⟨⟨x, by simpa only [mem_compl_iff, mem_singleton_iff] using And.intro hxa hxb⟩, rfl⟩
  have hA' : Tendsto f (𝓝[≠] a) (𝓝 A) :=
    (tendsto_comap'_iff ha).mp (hA.mono_left (Filter.comap_mono nhdsWithin_le_nhds))
  have hB' : Tendsto f (𝓝[≠] b) (𝓝 B) :=
    (tendsto_comap'_iff hb).mp (hB.mono_left (Filter.comap_mono nhdsWithin_le_nhds))
  apply continuous_iff_continuousAt.mpr
  intro x
  unfold twoPointUpdate
  by_cases hxa : x = a
  · subst x
    rw [continuousAt_update_of_ne hab, continuousAt_update_same]
    exact hA'
  by_cases hxb : x = b
  · subst x
    rw [continuousAt_update_same]
    exact hB'.congr' (Function.update_eventuallyEq_nhdsNE f a b A).symm
  rw [continuousAt_update_of_ne hxb, continuousAt_update_of_ne hxa]
  exact hf x hxa hxb

omit [TopologicalSpace X] [T1Space X] [TopologicalSpace Y] in
/-- A bijection off two distinct source and target points remains a
bijection after filling in those point pairs. -/
theorem bijective_twoPointUpdate (f : X → Y) {a b : X} (hab : a ≠ b)
    {A B : Y} (hAB : A ≠ B)
    (F : {x : X // x ≠ a ∧ x ≠ b} ≃ {y : Y // y ≠ A ∧ y ≠ B})
    (hf : ∀ x : {x : X // x ≠ a ∧ x ≠ b}, f x = (F x : Y)) :
    Function.Bijective (twoPointUpdate f a b A B) := by
  let H := twoPointUpdate f a b A B
  have hA (x : X) : H x = A ↔ x = a := by
    by_cases hxa : x = a
    · subst x
      simp [H, twoPointUpdate_first f hab]
    by_cases hxb : x = b
    · subst x
      simp [H, twoPointUpdate_second, hAB.symm, hab.symm]
    have he : H x = (F ⟨x, hxa, hxb⟩ : Y) :=
      (twoPointUpdate_of_ne f A B hxa hxb).trans (hf ⟨x, hxa, hxb⟩)
    rw [he]
    exact iff_of_false (F ⟨x, hxa, hxb⟩).property.1 hxa
  have hB (x : X) : H x = B ↔ x = b := by
    by_cases hxb : x = b
    · subst x
      simp [H, twoPointUpdate_second]
    by_cases hxa : x = a
    · subst x
      simp [H, twoPointUpdate_first f hab, hAB, hab]
    have he : H x = (F ⟨x, hxa, hxb⟩ : Y) :=
      (twoPointUpdate_of_ne f A B hxa hxb).trans (hf ⟨x, hxa, hxb⟩)
    rw [he]
    exact iff_of_false (F ⟨x, hxa, hxb⟩).property.2 hxb
  constructor
  · intro x y hxy
    by_cases hxa : x = a
    · exact hxa.trans ((hA y).mp (hxy.symm.trans ((hA x).mpr hxa))).symm
    by_cases hxb : x = b
    · exact hxb.trans ((hB y).mp (hxy.symm.trans ((hB x).mpr hxb))).symm
    have hya : y ≠ a := fun hy => hxa ((hA x).mp (hxy.trans ((hA y).mpr hy)))
    have hyb : y ≠ b := fun hy => hxb ((hB x).mp (hxy.trans ((hB y).mpr hy)))
    have he : F ⟨x, hxa, hxb⟩ = F ⟨y, hya, hyb⟩ := by
      apply Subtype.ext
      simpa only [twoPointUpdate_of_ne f A B hxa hxb,
        twoPointUpdate_of_ne f A B hya hyb, hf ⟨x, hxa, hxb⟩, hf ⟨y, hya, hyb⟩] using hxy
    exact congrArg Subtype.val (F.injective he)
  · intro y
    by_cases hyA : y = A
    · exact ⟨a, (twoPointUpdate_first f hab A B).trans hyA.symm⟩
    by_cases hyB : y = B
    · exact ⟨b, (twoPointUpdate_second f a b A B).trans hyB.symm⟩
    let x := F.symm ⟨y, hyA, hyB⟩
    refine ⟨x, ?_⟩
    rw [twoPointUpdate_of_ne f A B x.property.1 x.property.2, hf x]
    exact congrArg Subtype.val (F.apply_symm_apply ⟨y, hyA, hyB⟩)

/-- For a compact source and Hausdorff target, a regular homeomorphism
with distinct limiting values at the omitted points extends globally. -/
theorem exists_twoPointExtension_homeomorph [CompactSpace X] [T2Space Y]
    (f : X → Y) {a b : X} (hab : a ≠ b) {A B : Y} (hAB : A ≠ B)
    (F : {x : X // x ≠ a ∧ x ≠ b} ≃ₜ {y : Y // y ≠ A ∧ y ≠ B})
    (he : ∀ x : {x : X // x ≠ a ∧ x ≠ b}, f x = (F x : Y))
    (hf : ∀ x, x ≠ a → x ≠ b → ContinuousAt f x)
    (hA : Tendsto (fun x : {x : X // x ≠ a ∧ x ≠ b} => f x)
      (Filter.comap Subtype.val (𝓝 a)) (𝓝 A))
    (hB : Tendsto (fun x : {x : X // x ≠ a ∧ x ≠ b} => f x)
      (Filter.comap Subtype.val (𝓝 b)) (𝓝 B)) :
    ∃ H : X ≃ₜ Y, H a = A ∧ H b = B ∧
      ∀ x : {x : X // x ≠ a ∧ x ≠ b}, H (x : X) = (F x : Y) := by
  let e := Equiv.ofBijective (twoPointUpdate f a b A B)
    (bijective_twoPointUpdate f hab hAB F.toEquiv he)
  let H := Continuous.homeoOfEquivCompactToT2
    (f := e) (continuous_twoPointUpdate f hab A B hf hA hB)
  refine ⟨H, twoPointUpdate_first f hab A B, twoPointUpdate_second f a b A B, ?_⟩
  intro x
  exact (twoPointUpdate_of_ne f A B x.property.1 x.property.2).trans (he x)

end LichnerowiczObata
