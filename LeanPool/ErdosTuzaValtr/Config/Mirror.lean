/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/

-- Mirror configuration
import LeanPool.ErdosTuzaValtr.Lib.Core.Rel3
import LeanPool.ErdosTuzaValtr.Lib.List.Default
import LeanPool.ErdosTuzaValtr.Config.Defs

/-!
# LeanPool.ErdosTuzaValtr.Config.Mirror

Imported Lean Pool material for `LeanPool.ErdosTuzaValtr.Config.Mirror`.
-/

variable {α : Type _} [LinearOrder α] (C : Config α)

open OrderDual

-- to_dual : α → αᵒᵈ
-- of_dual : αᵒᵈ → α
/-- The mirror configuration on the order dual, obtained by reversing the cup relation. -/
def Config.Mirror : Config (OrderDual α) :=
  ⟨Mirror3 C.Cup3, C.DecidableCup3.Mirror3⟩

variable {C}

@[simp]
theorem Mirror.cap {l : List α} : C.Mirror.Cap l.Mirror ↔ C.Cap l := by
  constructor
  · rw [Config.Cap]
    intro h
    exact ⟨List.chain'_mirror.mp h.left, List.chain3'_mirror.mp h.right⟩
  · intro h
    rw [Config.Cap]
    exact ⟨List.chain'_mirror.mpr h.left, List.chain3'_mirror.mpr h.right⟩

@[simp]
theorem Mirror.cup {l : List α} : C.Mirror.Cup l.Mirror ↔ C.Cup l := by
  constructor
  · rw [Config.Cup]
    intro h
    exact ⟨List.chain'_mirror.mp h.left, List.chain3'_mirror.mp h.right⟩
  · intro h
    rw [Config.Cup]
    exact ⟨List.chain'_mirror.mpr h.left, List.chain3'_mirror.mpr h.right⟩

theorem Mirror.gon {l1 l2 : List α} : C.Mirror.Gon l1.Mirror l2.Mirror ↔ C.Gon l1 l2 := by
  rw [Config.Gon]; rw [Config.Gon]
  simp only [List.Mirror_length, cap, cup, and_congr_right_iff]
  intro _ _ _ _
  rw [List.Mirror_getLast, List.Mirror_head, List.Mirror_getLast, List.Mirror_head]
  have t_inj : Function.Injective (⇑toDual : α → αᵒᵈ) := fun _ _ => toDual_inj.mp
  have ot_inj := Option.map_injective t_inj
  rw [ot_inj.eq_iff, ot_inj.eq_iff]; tauto

@[simp]
theorem Mirror.ncap {n : ℕ} {l : List α} : C.Mirror.NCap n l.Mirror ↔ C.NCap n l := by
  rw [Config.NCap]; rw [Config.NCap]; simp

@[simp]
theorem Mirror.ncup {n : ℕ} {l : List α} : C.Mirror.NCup n l.Mirror ↔ C.NCup n l := by
  rw [Config.NCup]; rw [Config.NCup]; simp

theorem Mirror.ngon {n : ℕ} {l1 l2 : List α} :
    C.NGon n l1 l2 ↔ C.Mirror.NGon n l1.Mirror l2.Mirror := by
  rw [Config.NGon]; rw [Config.NGon]
  rw [Mirror.gon]; simp

@[simp]
theorem Mirror.hasNCap {n : ℕ} {S : Finset α} : C.Mirror.HasNCap n S.Mirror ↔ C.HasNCap n S :=
  by
  constructor
  · intro h; rcases h with ⟨c, ⟨c_ncap, c_in⟩⟩
    use c.ofMirror
    constructor
    · rw [← Mirror.ncap]; convert c_ncap; simp
    · rw [← @List.ofMirrorMirror α c] at c_in c_ncap
      set co := c.ofMirror
      rw [← List.Mirror_in]; assumption
  · intro h; rcases h with ⟨c, ⟨c_ncap, c_in⟩⟩
    use c.Mirror
    constructor
    · rw [Mirror.ncap]; tauto
    · rw [List.Mirror_in]; assumption

@[simp]
theorem Mirror.hasNCup {n : ℕ} {S : Finset α} : C.Mirror.HasNCup n S.Mirror ↔ C.HasNCup n S :=
  by
  constructor
  · intro h; rcases h with ⟨c, ⟨c_ncup, c_in⟩⟩
    use c.ofMirror
    rw [← @List.ofMirrorMirror α c] at c_in c_ncup
    set co := c.ofMirror
    rw [List.Mirror_in] at c_in
    rw [Mirror.ncup] at c_ncup; tauto
  · intro h; rcases h with ⟨c, ⟨c_ncup, c_in⟩⟩
    use c.Mirror
    constructor
    · rw [Mirror.ncup]; tauto
    · rw [List.Mirror_in]; assumption

theorem Mirror.hasNGon {n : ℕ} {S : Finset α} : C.Mirror.HasNGon n S.Mirror ↔ C.HasNGon n S :=
  by
  constructor
  · intro h; rcases h with ⟨c1, c2, ⟨c_ngon, c1_in, c2_in⟩⟩
    use c1.ofMirror, c2.ofMirror
    rw [← @List.ofMirrorMirror α c1] at c1_in c_ngon
    rw [← @List.ofMirrorMirror α c2] at c2_in c_ngon
    set c1o := c1.ofMirror; set c2o := c2.ofMirror
    rw [List.Mirror_in] at c1_in c2_in
    rw [← Mirror.ngon] at c_ngon; tauto
  · intro h; rcases h with ⟨c1, c2, ⟨c_ngon, c1_in, c2_in⟩⟩
    use c1.Mirror, c2.Mirror
    constructor
    · rw [← Mirror.ngon]; tauto
    · simp [List.Mirror_in]; tauto
