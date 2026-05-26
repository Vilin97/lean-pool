/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/

import LeanPool.WhiteheadTheorem.RelHomotopyGroup.Defs
import LeanPool.WhiteheadTheorem.HEP.Retract

open scoped unitInterval Topology Topology.Homotopy
open ContinuousMap


namespace RelHomotopyGroup

variable (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) (a : A)

/-- For `n ≥ 1`, if `⟦f⟧ ∈ π_rel n X A a` and `f` is homotopic rel `∂I^n` to a map `g`
whose image is in `A`, then `f` represents zero in the relative homotopy group. -/
lemma compression_criterion_1 (f : RelGenLoop (n + 1) X A a) (g : C(I^Fin (n + 1), X))
    (rg : Set.range g ⊆ A) (H : ContinuousMap.HomotopyRel f g (∂I^(n + 1))) :
    ⟦f⟧ = (⟦RelGenLoop.const⟧ : π_rel (n + 1) X A a) :=
  -- let g' : RelGenLoop n X A a := RelGenLoop.ofHomotopyRel f g H
  (RelGenLoop.ofHomotopyRel.eq f g H).trans <| Quotient.eq.mpr <| Nonempty.intro <|
    let R := Cube.strongDeformRetrToBoundaryJar n
    let g_bd : ∀ y ∈ ∂I^(n+1), g y = f.val y :=
      fun y hy ↦ (H.map_one_left y).symm.trans (H.prop' 1 y hy)
    { toContinuousMap := (ContinuousMap.Homotopy.refl g).comp R.H.toHomotopy
      map_zero_left y := by simp [RelGenLoop.ofHomotopyRel]
      map_one_left y := by
        unfold RelGenLoop.const
        simp only [id_apply, toFun_eq_coe, ContinuousMap.coe_coe, Homotopy.apply_one, comp_apply,
          ContinuousMap.const_apply]
        have r_y_in_jar : R.r y ∈ ⊔I^(n+1) := Set.range_subset_iff.mp R.r_range y
        have r_y_in_bd : R.r y ∈ ∂I^(n+1) := Cube.boundaryJar_subset_boundary (n+1) r_y_in_jar
        rw [g_bd (R.r y) r_y_in_bd, f.property.right (R.r y) r_y_in_jar]
      prop' t := ⟨fun y hy ↦ Set.range_subset_iff.mp rg _,
        fun y hy ↦ by
          have := R.H.prop' t y hy
          simp only [id_apply, toFun_eq_coe, coe_mk] at this
          change g (R.H (t, y)) = a
          rw [show R.H (t, y) = y from this,
            g_bd y (Cube.boundaryJar_subset_boundary (n+1) hy), f.property.right y hy] ⟩ }

/-- Same as `compression_criterion_1`, except that the codomain of `g` is explicitly `A`. -/
lemma compression_criterion_1_subtype (f : RelGenLoop (n + 1) X A a) (g : C(I^Fin (n + 1), A))
    (H : ContinuousMap.HomotopyRel f ⟨Subtype.val ∘ g, g.continuous.subtype_val⟩ (∂I^(n + 1))) :
    ⟦f⟧ = (⟦RelGenLoop.const⟧ : π_rel (n + 1) X A a) := by
  refine compression_criterion_1 n X A a f _ ?_ H
  intro x
  simp only [coe_mk, Set.mem_range, Function.comp_apply, forall_exists_index]
  intro y hy; rw [← hy]; exact Subtype.coe_prop (g y)

/-- If `f` represents zero in the relative homotopy group `π_rel n X A a`,
then `f` is homotopic rel `∂I^n` to some map `g` whose image is in `A`. -/
lemma compression_criterion_2
    (f : RelGenLoop n X A a) (fz : ⟦f⟧ = (⟦RelGenLoop.const⟧ : π_rel n X A a)) :
    ∃ g : C(I^ Fin n, X), Set.range g ⊆ A ∧ ContinuousMap.HomotopicRel f g (∂I^n) := by
  have H : ContinuousMap.HomotopicWith .. := Quotient.eq.mp fz.symm
  -- have H_fun := H.some.toContinuousMap
  let R := Cube.strongDeformRetrToBoundaryJar n
  use H.some.toContinuousMap.comp <| (toContinuousMap Cube.splitAtLast).comp <|
    R.r.comp <| Cube.inclToTop
  constructor
  · intro x hx
    have ⟨y, hy⟩ := Set.mem_range.mp hx
    rw [← hy]
    have : ∀ y ∈ ⊔I^(n+1), (Nonempty.some H) (Cube.splitAtLast y) ∈ A := by
      intro y hy
      rcases Cube.mem_boundaryJar_iff_splitAtLast.mp hy with h_bot | h_side
      · change (Nonempty.some H).toFun
          ⟨(Cube.splitAtLast y).fst, (Cube.splitAtLast y).snd⟩ ∈ A
        rw [h_bot, H.some.map_zero_left (Cube.splitAtLast y).snd, RelGenLoop.const]
        simp only [ContinuousMap.const_apply, Subtype.coe_prop]
      · exact H.some.prop' (Cube.splitAtLast y).fst |>.left _ h_side
    exact this (R.r <| Cube.inclToTop y) <| R.r_range <| Set.mem_range_self _
  · exact Nonempty.intro <|
    { toFun := (ContinuousMap.Homotopy.refl H.some.toContinuousMap).comp <|
          (ContinuousMap.Homotopy.refl (toContinuousMap Cube.splitAtLast)).comp <|
          R.H.toHomotopy.comp <| ContinuousMap.Homotopy.refl Cube.inclToTop
      continuous_toFun := ContinuousMapClass.map_continuous _
      map_zero_left y := by
        simp only [Homotopy.comp_apply, Homotopy.refl_apply,
          Homotopy.coe_toContinuousMap, HomotopyWith.coe_toHomotopy]
        change H.some (Cube.splitAtLast (R.H (0, Cube.inclToTop y))) = _
        rw [show R.H (0, Cube.inclToTop y) = Cube.inclToTop y from
          R.H.toHomotopy.apply_zero (Cube.inclToTop y)]
        rw [Cube.splitAtLast_inclToTop_eq, HomotopyWith.apply_one]
      map_one_left y := by
        simp only [Homotopy.comp_apply, Homotopy.refl_apply,
          Homotopy.coe_toContinuousMap, HomotopyWith.coe_toHomotopy]
        rw [show R.H (1, Cube.inclToTop y) = R.r (Cube.inclToTop y) from
          R.H.toHomotopy.apply_one (Cube.inclToTop y)]
        rfl
      prop' t y hy := by
        have hRH := R.H.prop' t _ (Cube.inclToTop.mem_boundaryJar_of hy)
        simp only [id_apply, toFun_eq_coe, Homotopy.coe_toContinuousMap,
          HomotopyWith.coe_toHomotopy, coe_mk] at hRH
        change H.some (Cube.splitAtLast (R.H (t, Cube.inclToTop y))) = _
        rw [show R.H (t, Cube.inclToTop y) = Cube.inclToTop y from hRH,
          Cube.splitAtLast_inclToTop_eq, HomotopyWith.apply_one] }

/-- Same as `compression_criterion_2`, except that the codomain of `g` is explicitly `A`. -/
lemma compression_criterion_2_subtype
    (f : RelGenLoop n X A a) (fz : ⟦f⟧ = (⟦RelGenLoop.const⟧ : π_rel n X A a)) :
    ∃ g : C(I^ Fin n, A), ContinuousMap.HomotopicRel f
      ⟨Subtype.val ∘ g, g.continuous.subtype_val⟩ (∂I^n) := by
  have ⟨g', ⟨hg', H'⟩⟩ := compression_criterion_2 n X A a f fz
  use ⟨fun y ↦ ⟨g' y, hg' (Set.mem_range_self y)⟩, Continuous.subtype_mk g'.continuous _⟩
  exact H'

end RelHomotopyGroup
