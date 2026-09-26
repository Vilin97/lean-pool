/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.SymMul
public import LeanPool.RegtsSevenster.RS.Novel.Envelope.SymPermCast

/-!
# Vanishing along the standard embeddings on module powers

The module-power mirror of `Envelope/SymPermCast.lean`: an element
of the symmetric-group algebra whose descended action on the `m`-th
module power vanishes keeps a vanishing action at every higher
arity, along the standard embeddings `S_m ↪ S_n`.

The route is a descent reduction rather than a fresh induction.
The projection `modPowπ` intertwines the ambient action `permAlg`
with the descended action `modPowAlg` (`modPowπ_permAlg`), because
the descended action is defined slot by slot through that very
square; so vanishing of the descended action is exactly vanishing
of the ambient action followed by the projection.  The ambient
compatibility `permAlg_symCast` rewrites the restricted action as a
repeated whiskering, and one letter is attached to a module power
by `modPowAttach` — the first concatenation stage of `SymMul.lean`
taken at a single letter — whose defining square
`(modPowπ ▷ X) ≫ modPowAttach = modPowπ` lets whiskered morphisms
that die after the projection keep dying
(`whiskerRight_modPowπ_zero`).  The compatibility
`modPowAlg_compat` follows.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## Structural helpers -/

section Aux

/-- Collapse of the single-letter concatenation stage: the unitor
triangle, in the shape produced by `tensorPowConcat` at one
letter. -/
private theorem attach_aux [Category.{v} D] [MonoidalCategory D] (X : D)
    (P : D) :
    (P ◁ (λ_ X).inv) ≫ (α_ P (𝟙_ D) X).inv ≫
      ((ρ_ P).hom ▷ X) = 𝟙 (P ⊗ X) := by
  monoidal

end Aux

section Pass

/-- Passing a sum across an intertwiner. -/
private theorem add_pass [Category.{v} D] [Preadditive D]
    {P Q : D} {T : P ⟶ Q} {u v : Q ⟶ Q}
    {u' v' : P ⟶ P} (hu : T ≫ u = u' ≫ T) (hv : T ≫ v = v' ≫ T) :
    T ≫ (u + v) = (u' + v') ≫ T := by
  rw [Preadditive.comp_add, Preadditive.add_comp, hu, hv]

/-- Passing a scalar multiple across an intertwiner. -/
private theorem smul_pass [Category.{v} D] [Preadditive D] [Linear ℂ D]
    {P Q : D} {T : P ⟶ Q} {u : Q ⟶ Q}
    {u' : P ⟶ P} (r : ℂ) (h : T ≫ u = u' ≫ T) :
    T ≫ (r • u) = (r • u') ≫ T := by
  rw [Linear.comp_smul, Linear.smul_comp, h]

end Pass

/-! ## Attaching one letter to a module power -/

section Attach

/-- **Attach one ambient letter** on the right of a module power:
the first concatenation stage of the multiplication of
`SymMul.lean`, taken at a single letter. -/
noncomputable def modPowAttach
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [MonoidalPreadditive D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (p : ℕ) :
    modPow A X p ⊗ X ⟶ modPow A X (p + 1) :=
  (modPow A X p ◁ (show X ⟶ tensorPow D X 1 from (λ_ X).inv)) ≫
    modPowMulStage A X p 1

/-- **Defining square of the attachment**: the projection at `p + 1`
factors through the right-whiskered projection at `p`. -/
theorem modPowπ_attach
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [MonoidalPreadditive D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (p : ℕ) :
    (modPowπ A X p ▷ X) ≫ modPowAttach A X p =
      modPowπ A X (p + 1) := by
  have h2 : (tensorPow D X p ◁
        (show X ⟶ tensorPow D X 1 from (λ_ X).inv)) ≫
      (tensorPowConcat X p 1).hom = 𝟙 (tensorPow D X (p + 1)) :=
    attach_aux X (tensorPow D X p)
  rw [modPowAttach, ← MonoidalCategory.whisker_exchange_assoc,
    modPowπ_whiskerRight_mulStage, ← Category.assoc, h2]
  exact Category.id_comp (modPowπ A X (p + 1))

/-- **Whiskered vanishing**: a morphism of the ambient power that
dies after the projection keeps dying, one letter later, after
whiskering on the right. -/
theorem whiskerRight_modPowπ_zero
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [MonoidalPreadditive D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    {p : ℕ}
    {f : tensorPow D X p ⟶ tensorPow D X p}
    (hf : f ≫ modPowπ A X p = 0) :
    (f ▷ X) ≫ modPowπ A X (p + 1) = 0 := by
  rw [← modPowπ_attach A X p,
    ← MonoidalCategory.comp_whiskerRight_assoc, hf,
    MonoidalPreadditive.zero_whiskerRight, Limits.zero_comp]

end Attach

/-! ## The compatibility -/

section Compat

/-- **The projection intertwines the two algebra actions**: the
`ℂ`-linear extension of the defining square of the descended
permutation action. -/
theorem modPowπ_permAlg
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) (x : SymGroupAlgebra n) :
    modPowπ A X n ≫ modPowAlg A X n x =
      permAlg X n x ≫ modPowπ A X n := by
  induction x using MonoidAlgebra.induction_on with
  | of σ =>
      rw [show (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n))) σ =
          MonoidAlgebra.single σ (1 : ℂ) from rfl,
        modPowAlg_single, permAlg_single]
      exact modPowπ_perm n σ
  | add x₁ x₂ h₁ h₂ =>
      rw [map_add, map_add]
      exact add_pass h₁ h₂
  | smul r y hy =>
      rw [map_smul, map_smul]
      exact smul_pass r hy

/-- **Iterated whiskered vanishing**: an endomorphism of the ambient
power that dies after the projection keeps dying after any number of
letters is attached. -/
theorem whiskerPowAlg_modPowπ_zero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalPreadditive D]
    [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (m k : ℕ)
    (f : tensorPow D X m ⟶ tensorPow D X m)
    (hf : f ≫ modPowπ A X m = 0) :
    whiskerPowAlg X m k f ≫ modPowπ A X (m + k) = 0 := by
  induction k with
  | zero => exact hf
  | succ k ih => exact whiskerRight_modPowπ_zero A X ih

/-- **Vanishing propagates along the standard embeddings** on
module powers: an element of the group algebra killed by the
descended action at arity `m` stays killed at every arity `n ≥ m`.
This is the `compat` field of a tower, for the action on a module
power. -/
theorem modPowAlg_compat
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalPreadditive D]
    [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    {m n : ℕ} (h : m ≤ n)
    (x : SymGroupAlgebra m) (hx : modPowAlg A X m x = 0) :
    modPowAlg A X n (symCast h x) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have hπ : permAlg X m x ≫ modPowπ A X m = 0 := by
    rw [← modPowπ_permAlg A X m x, hx]
    exact Limits.comp_zero
  have h0 : whiskerPowAlg X m k (permAlg X m x) ≫
      modPowπ A X (m + k) = 0 :=
    whiskerPowAlg_modPowπ_zero A X m k (permAlg X m x) hπ
  apply modPow_hom_ext A X
  rw [modPowπ_permAlg, permAlg_symCast, h0]
  exact Limits.comp_zero.symm

end Compat

end RS
