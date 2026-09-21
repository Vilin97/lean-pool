/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModBiprod
import LeanPool.RegtsSevenster.RS.Classical.Deligne.Prop29
import LeanPool.RegtsSevenster.RS.Classical.Deligne.AltPow

/-!
# The dévissage state of the trichotomy

The recursion state of Deligne's 2.9, direction (ii) ⇒ (i): a
nonzero commutative base algebra, counts of split-off unit and
line factors, and a dualizable remainder module, together with a
decomposition of the base change of the object as the mixed free
part plus the remainder.  Each step of the dévissage either
splits a further unit factor off the remainder (through the Key
Lemma), splits a line factor (through the sign-twisted mirror),
or exits with the remainder already zero.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable (D : Type u)

attribute [local instance]
  hasBinaryBiproducts_of_finite_biproducts

/-- **The dévissage state**: a nonzero commutative base, the
counts of unit and line factors already split off, a dualizable
remainder with its zigzag laws, and the decomposition of the base
change of the object. -/
structure DevissageState
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (L : OddLine D) (X : D) where
  /-- The current base algebra. -/
  base : D
  /-- Its monoid structure. -/
  monObj : MonObj base
  /-- Commutativity. -/
  comm : letI := monObj; IsCommMonObj base
  /-- The base is nonzero: its unit does not vanish. -/
  unit_ne_zero : letI := monObj; η[base] ≠ 0
  /-- The number of unit factors split off. -/
  units : ℕ
  /-- The number of line factors split off. -/
  lines : ℕ
  /-- The remainder module. -/
  rest : letI := monObj; Mod D base
  /-- The dual of the remainder. -/
  restDual : letI := monObj; Mod D base
  /-- The duality datum of the remainder. -/
  datum : letI := monObj; letI := comm;
    ModDualityDatum base rest restDual
  /-- The zigzag laws of the duality datum. -/
  zigzag : letI := monObj; letI := comm;
    ModZigzagDatum base datum
  /-- The base change of the object decomposes as the mixed free
  part plus the remainder. -/
  decomp : letI := monObj; letI := comm;
    Nonempty (freeMod base X ≅
      modBiprod base (freeMod base (L.mix units lines)) rest)

section Steps

/-- **Case (a) of the dévissage**: when every symmetric power of
the remainder survives, a further unit factor splits off. -/
def DevissageStepA [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    [Linear ℂ D]
    (L : OddLine D) (X : D) : Prop :=
  ∀ st : DevissageState D L X,
    (letI := st.monObj;
      ∀ n : ℕ, ¬ IsZero (symPow st.base st.rest.X n)) →
    ∃ st' : DevissageState D L X,
      st'.units = st.units + 1 ∧ st'.lines = st.lines

/-- **Case (b)**: when every alternating power of the remainder
survives, a further line factor splits off. -/
def DevissageStepB [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    [Linear ℂ D]
    (L : OddLine D) (X : D) : Prop :=
  ∀ st : DevissageState D L X,
    (letI := st.monObj;
      ∀ n : ℕ, ¬ IsZero (altPow st.base st.rest.X n)) →
    ∃ st' : DevissageState D L X,
      st'.units = st.units ∧ st'.lines = st.lines + 1

/-- **The exit**: a state whose remainder has died witnesses the
local mixed decomposition. -/
def DevissageExit [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (L : OddLine D) (X : D) : Prop :=
  ∀ st : DevissageState D L X,
    (letI := st.monObj; IsZero st.rest.X) →
    L.LocallyMixed X

/-- **The exit holds**: the decomposition collapses onto its
mixed free part once the remainder dies. -/
theorem devissageExit
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (L : OddLine D) (X : D) :
    DevissageExit D L X := by
  intro st hz
  letI := st.monObj
  letI := st.comm
  obtain ⟨e⟩ := st.decomp
  refine ⟨st.units, st.lines, st.base, st.monObj, st.comm,
    st.unit_ne_zero, ⟨e.trans ?_⟩⟩
  have hsnd : (biprod.snd :
      (freeMod st.base (L.mix st.units st.lines)).X ⊞
        st.rest.X ⟶ st.rest.X) = 0 :=
    hz.eq_of_tgt _ _
  refine ⟨modBiprodFst st.base _ st.rest,
    modBiprodInl st.base _ st.rest, ?_, ?_⟩
  · apply Mod.Hom.ext
    show (biprod.fst ≫ biprod.inl :
        (freeMod st.base (L.mix st.units st.lines)).X ⊞
          st.rest.X ⟶ _) = 𝟙 _
    rw [← biprod.total, hsnd, Limits.zero_comp, add_zero]
  · apply Mod.Hom.ext
    show (biprod.inl ≫ biprod.fst : _ ⟶ _) = 𝟙 _
    rw [biprod.inl_fst]

/-- **The trichotomy**: over any state, either every symmetric
power of the remainder survives, or every alternating power
survives, or the remainder has died. -/
def DevissageTrichotomy
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    [Linear ℂ D]
    (L : OddLine D) (X : D) : Prop :=
  ∀ st : DevissageState D L X,
    (letI := st.monObj;
      ∀ n : ℕ, ¬ IsZero (symPow st.base st.rest.X n)) ∨
    (letI := st.monObj;
      ∀ n : ℕ, ¬ IsZero (altPow st.base st.rest.X n)) ∨
    (letI := st.monObj; IsZero st.rest.X)

/-- **The dévissage runs to completion**: given the two step
constructions, the trichotomy, the exit, and a uniform bound on
the number of split-off factors, every state leads to the local
mixed decomposition. -/
theorem devissage_run
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    [Linear ℂ D]
    (L : OddLine D) (X : D)
    (hA : DevissageStepA D L X) (hB : DevissageStepB D L X)
    (hT : DevissageTrichotomy D L X)
    (hE : DevissageExit D L X) (bound : ℕ)
    (hBound : ∀ st : DevissageState D L X,
      st.units + st.lines ≤ bound)
    (st₀ : DevissageState D L X) : L.LocallyMixed X := by
  suffices h : ∀ fuel : ℕ, ∀ st : DevissageState D L X,
      bound + 1 - (st.units + st.lines) ≤ fuel →
      L.LocallyMixed X from
    h (bound + 1) st₀ (by omega)
  intro fuel
  induction fuel with
  | zero =>
    intro st hle
    exact absurd (hBound st) (by omega)
  | succ n ih =>
    intro st hle
    rcases hT st with ha | hb | hdead
    · obtain ⟨st', hu, hl⟩ := hA st ha
      exact ih st' (by omega)
    · obtain ⟨st', hu, hl⟩ := hB st hb
      exact ih st' (by omega)
    · exact hE st hdead

end Steps

end RS
