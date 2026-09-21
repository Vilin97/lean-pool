/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.AltPow
import LeanPool.RegtsSevenster.RS.Classical.Deligne.PermNat
import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowAct

/-!
# The idempotent cut of module powers

The generic splitting that `SymAlg.lean` performs for the
symmetriser and `AltPow.lean` for the antisymmetriser, done once
for an arbitrary idempotent `e` of the symmetric-group algebra:
the cut of the module power by `e`, presented as the coequalizer
of the action `modPowAlg e` against the identity, which the
idempotency splits off as a direct summand of the module power —
together with the `A`-module structure descended through the
splitting.  This is the substrate for Schur functors of modules
over an internal monoid; the Young idempotents of the Schur
interface are plugged in elsewhere.

* `modPowCut A X n e`: the cut, with projection `modPowCutπ`,
  section `modPowCutσ`, the splitting identities, extensionality
  and descent.  Idempotency `e * e = e` enters as an explicit
  hypothesis on exactly the declarations that need it.
* `modPowAct_modPowCutIdem`: the descended action commutes with
  the group-algebra action, by the linear extension of the
  permutation case.
* `modPowCutAct`/`modPowCutModObj`/`modPowCutMod`: the action on
  the cut, with `modPowCutσ` a module map.
* `modPowCut_symmetriser`/`modPowCut_antisymmetriser`: at the
  symmetriser and the antisymmetriser the cut is the symmetric and
  the alternating power, definitionally.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## The cut of the module power by an idempotent -/

section IdemCut

/-- A group-algebra element acting on the module power. -/
noncomputable def modPowCutIdem
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) (e : SymGroupAlgebra n) :
    modPow A X n ⟶ modPow A X n :=
  modPowAlg A X n e

/-- An idempotent's action is idempotent. -/
theorem modPowCutIdem_idem
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) (e : SymGroupAlgebra n)
    (he : e * e = e) :
    modPowCutIdem A X n e ≫ modPowCutIdem A X n e =
      modPowCutIdem A X n e := by
  have h := congrArg (modPowAlg A X n) he
  rw [map_mul] at h
  exact h

/-- **The cut of the module power by an idempotent**: the
coequalizer of the idempotent's action against the identity.  The
idempotency splits it off as a direct summand of the module power,
with section `modPowCutσ`; this presentation is chosen because
consumers build morphisms out of the cut by descent along
`modPowCutπ` and morphisms into it through the section. -/
noncomputable def modPowCut
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) (e : SymGroupAlgebra n) : D :=
  coequalizer (modPowCutIdem A X n e) (𝟙 (modPow A X n))

/-- The projection onto the cut. -/
noncomputable def modPowCutπ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) (e : SymGroupAlgebra n) :
    modPow A X n ⟶ modPowCut A X n e :=
  coequalizer.π _ _

instance [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) (e : SymGroupAlgebra n) :
    Epi (modPowCutπ A X n e) :=
  inferInstanceAs (Epi (coequalizer.π _ _))

/-- The idempotent is absorbed by the projection. -/
@[reassoc (attr := simp)]
theorem modPowCutIdem_π
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) (e : SymGroupAlgebra n) :
    modPowCutIdem A X n e ≫ modPowCutπ A X n e =
      modPowCutπ A X n e := by
  have h := coequalizer.condition (modPowCutIdem A X n e)
    (𝟙 (modPow A X n))
  rwa [Category.id_comp] at h

/-- The section of the cut, from idempotency. -/
noncomputable def modPowCutσ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) (e : SymGroupAlgebra n)
    (he : e * e = e) : modPowCut A X n e ⟶ modPow A X n :=
  coequalizer.desc (modPowCutIdem A X n e)
    (by rw [Category.id_comp, modPowCutIdem_idem A X n e he])

/-- The section realises the idempotent as projection followed by
inclusion. -/
@[reassoc (attr := simp)]
theorem modPowCutπ_σ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) (e : SymGroupAlgebra n)
    (he : e * e = e) :
    modPowCutπ A X n e ≫ modPowCutσ A X n e he =
      modPowCutIdem A X n e :=
  coequalizer.π_desc _ _

/-- Morphisms out of the cut are determined by their composite with
the projection. -/
theorem modPowCut_hom_ext
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    {n : ℕ} {e : SymGroupAlgebra n} {W : D}
    {k l : modPowCut A X n e ⟶ W}
    (h : modPowCutπ A X n e ≫ k = modPowCutπ A X n e ≫ l) :
    k = l :=
  coequalizer.hom_ext h

/-- **The cut is a direct summand**: the section followed by the
projection is the identity. -/
@[reassoc (attr := simp)]
theorem modPowCutσ_π
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) (e : SymGroupAlgebra n)
    (he : e * e = e) :
    modPowCutσ A X n e he ≫ modPowCutπ A X n e =
      𝟙 (modPowCut A X n e) := by
  apply modPowCut_hom_ext A X
  rw [← Category.assoc, modPowCutπ_σ, modPowCutIdem_π,
    Category.comp_id]

/-- Descend a morphism absorbed by the idempotent to the cut. -/
noncomputable def modPowCutDesc
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    {n : ℕ} {e : SymGroupAlgebra n}
    {W : D} (k : modPow A X n ⟶ W)
    (h : modPowCutIdem A X n e ≫ k = k) : modPowCut A X n e ⟶ W :=
  coequalizer.desc k (by rw [Category.id_comp, h])

/-- The descent factors the given morphism through the
projection. -/
@[reassoc (attr := simp)]
theorem modPowCutπ_desc
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    {n : ℕ} {e : SymGroupAlgebra n} {W : D}
    (k : modPow A X n ⟶ W) (h : modPowCutIdem A X n e ≫ k = k) :
    modPowCutπ A X n e ≫ modPowCutDesc A X k h = k :=
  coequalizer.π_desc _ _

/-! ### Compatibility with the symmetric and alternating powers -/

/-- At the symmetriser the cut is the symmetric power,
definitionally. -/
theorem modPowCut_symmetriser
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) :
    modPowCut A X n (symmetriser n) = symPow A X n := rfl

/-- At the antisymmetriser the cut is the alternating power,
definitionally. -/
theorem modPowCut_antisymmetriser
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) :
    modPowCut A X n (antisymmetriser n) = altPow A X n := rfl

end IdemCut

/-! ## Whiskered extensionality for the cut -/

section CutWhisker

/-- Morphisms out of a left-whiskered cut are determined by the
whiskered projection, which is split epi. -/
theorem modPowCut_whiskerLeft_hom_ext
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (P : D) (n : ℕ)
    (e : SymGroupAlgebra n) (he : e * e = e) {Z : D}
    {k l : P ⊗ modPowCut A X n e ⟶ Z}
    (h : (P ◁ modPowCutπ A X n e) ≫ k =
      (P ◁ modPowCutπ A X n e) ≫ l) :
    k = l := by
  have hsec : (P ◁ modPowCutσ A X n e he) ≫
      (P ◁ modPowCutπ A X n e) = 𝟙 _ := by
    rw [← MonoidalCategory.whiskerLeft_comp, modPowCutσ_π,
      MonoidalCategory.whiskerLeft_id]
  calc k = ((P ◁ modPowCutσ A X n e he) ≫
        (P ◁ modPowCutπ A X n e)) ≫ k := by
        rw [hsec, Category.id_comp]
    _ = ((P ◁ modPowCutσ A X n e he) ≫
        (P ◁ modPowCutπ A X n e)) ≫ l := by
        rw [Category.assoc, Category.assoc, h]
    _ = l := by rw [hsec, Category.id_comp]

end CutWhisker

/-! ## The cut as a module -/

section CutAct

/-- **The descended action commutes with the idempotent's action**:
the idempotent is a `ℂ`-linear combination of permutations, each of
which the action passes. -/
theorem modPowAct_modPowCutIdem
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ)
    (e : SymGroupAlgebra (n + 1)) :
    modPowAct A X n ≫ modPowCutIdem A X (n + 1) e =
      (A ◁ modPowCutIdem A X (n + 1) e) ≫ modPowAct A X n :=
  modPowAct_alg A X n e

/-- **The monoid action on the cut**, through the section and the
descended action. -/
noncomputable def modPowCutAct
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) (e : SymGroupAlgebra (n + 1))
    (he : e * e = e) :
    A ⊗ modPowCut A X (n + 1) e ⟶ modPowCut A X (n + 1) e :=
  (A ◁ modPowCutσ A X (n + 1) e he) ≫ modPowAct A X n ≫
    modPowCutπ A X (n + 1) e

/-- Defining equation of the cut action. -/
@[reassoc (attr := simp)]
theorem whiskerLeft_modPowCutπ_modPowCutAct
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ)
    (e : SymGroupAlgebra (n + 1)) (he : e * e = e) :
    (A ◁ modPowCutπ A X (n + 1) e) ≫ modPowCutAct A X n e he =
      modPowAct A X n ≫ modPowCutπ A X (n + 1) e := by
  rw [modPowCutAct, ← whiskerLeft_comp_assoc, modPowCutπ_σ,
    reassoc_of% (modPowAct_modPowCutIdem A X n e).symm,
    modPowCutIdem_π]

/-- Unitality of the cut action. -/
theorem modPowCutAct_one
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) (e : SymGroupAlgebra (n + 1))
    (he : e * e = e) :
    η[A] ▷ modPowCut A X (n + 1) e ≫ modPowCutAct A X n e he =
      (λ_ (modPowCut A X (n + 1) e)).hom := by
  apply modPowCut_whiskerLeft_hom_ext A X (𝟙_ D) (n + 1) e he
  rw [whisker_exchange_assoc, whiskerLeft_modPowCutπ_modPowCutAct,
    reassoc_of% (modPowAct_one A X n), leftUnitor_naturality]

/-- Associativity of the cut action. -/
theorem modPowCutAct_mul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) (e : SymGroupAlgebra (n + 1))
    (he : e * e = e) :
    μ[A] ▷ modPowCut A X (n + 1) e ≫ modPowCutAct A X n e he =
      (α_ A A (modPowCut A X (n + 1) e)).hom ≫
        (A ◁ modPowCutAct A X n e he) ≫
        modPowCutAct A X n e he := by
  apply modPowCut_whiskerLeft_hom_ext A X (A ⊗ A) (n + 1) e he
  conv_lhs => rw [whisker_exchange_assoc,
    whiskerLeft_modPowCutπ_modPowCutAct,
    reassoc_of% (modPowAct_mul A X n)]
  conv_rhs => rw [associator_naturality_right_assoc,
    ← whiskerLeft_comp_assoc, whiskerLeft_modPowCutπ_modPowCutAct,
    whiskerLeft_comp_assoc, whiskerLeft_modPowCutπ_modPowCutAct]

/-- **The cut of a module is a module**, in every positive
arity. -/
@[implicit_reducible]
noncomputable def modPowCutModObj
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ)
    (e : SymGroupAlgebra (n + 1)) (he : e * e = e) :
    ModObj A (modPowCut A X (n + 1) e) where
  smul := modPowCutAct A X n e he
  one_smul := modPowCutAct_one A X n e he
  mul_smul := modPowCutAct_mul A X n e he

/-- The cut of a module, bundled as a module. -/
noncomputable def modPowCutMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) (e : SymGroupAlgebra (n + 1))
    (he : e * e = e) : Mod D A :=
  letI := modPowCutModObj A X n e he
  ⟨modPowCut A X (n + 1) e⟩

@[simp] theorem modPowCutMod_X
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) (e : SymGroupAlgebra (n + 1))
    (he : e * e = e) :
    (modPowCutMod A X n e he).X = modPowCut A X (n + 1) e := rfl

end CutAct

/-! ## Naturality substrate: module maps on powers

The transport kit for the cut: a module map `f : X ⟶ Y` induces a
map of module powers and of their cuts, functorially, and killing
the cut transports along retracts and isomorphisms.
-/

section MapNat

/-- Arity transports pass tensor powers of a morphism. -/
theorem powCast_tensorPowMap
    [Category.{v} D] [MonoidalCategory D] {X : D} {Y : D}
    (f : X ⟶ Y) {m n : ℕ} (h : m = n) :
    powCast X h ≫ tensorPowMap f n =
      tensorPowMap f m ≫ powCast Y h := by
  subst h
  rw [powCast_rfl, powCast_rfl, Category.id_comp, Category.comp_id]

/-- The concatenation isomorphism is natural in tensor powers of a
morphism. -/
theorem tensorPowMap_concat
    [Category.{v} D] [MonoidalCategory D] {X : D} {Y : D}
    (f : X ⟶ Y) (a : ℕ) : ∀ b : ℕ,
    (tensorPowMap f a ⊗ₘ tensorPowMap f b) ≫
        (tensorPowConcat Y a b).hom =
      (tensorPowConcat X a b).hom ≫ tensorPowMap f (a + b)
  | 0 => by
    rw [tensorPowConcat_zero, tensorPowConcat_zero]
    show (tensorPowMap f a ⊗ₘ 𝟙 (𝟙_ D)) ≫
        (ρ_ (tensorPow D Y a)).hom =
      (ρ_ (tensorPow D X a)).hom ≫ tensorPowMap f a
    rw [MonoidalCategory.tensorHom_id,
      MonoidalCategory.rightUnitor_naturality]
  | b + 1 => by
    show (tensorPowMap f a ⊗ₘ (tensorPowMap f b ⊗ₘ f)) ≫
        ((α_ (tensorPow D Y a) (tensorPow D Y b) Y).inv ≫
          (tensorPowConcat Y a b).hom ▷ Y) =
      ((α_ (tensorPow D X a) (tensorPow D X b) X).inv ≫
          (tensorPowConcat X a b).hom ▷ X) ≫
        (tensorPowMap f (a + b) ⊗ₘ f)
    rw [MonoidalCategory.associator_inv_naturality_assoc,
      ← MonoidalCategory.tensorHom_id (tensorPowConcat Y a b).hom Y,
      MonoidalCategory.tensorHom_comp_tensorHom,
      tensorPowMap_concat f a b, Category.comp_id, Category.assoc,
      ← MonoidalCategory.tensorHom_id (tensorPowConcat X a b).hom X,
      MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]

/-- The first window leg is natural in module maps. -/
theorem winLegM_natural
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] {X : D} {Y : D} [ModObj A X] [ModObj A Y]
    (f : X ⟶ Y) [IsModHom A f] :
    ((f ⊗ₘ 𝟙 A) ⊗ₘ f) ≫ winLegM A Y = winLegM A X ≫ (f ⊗ₘ f) := by
  rw [winLegM, winLegM,
    ← MonoidalCategory.tensorHom_id (actRight A Y) Y,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id,
    MonoidalCategory.tensorHom_id (f := f),
    ← actRight_natural A X Y f,
    ← MonoidalCategory.tensorHom_id (actRight A X) X,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]

/-- The second window leg is natural in module maps. -/
theorem winLegN_natural
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] {X : D} {Y : D}
    [ModObj A X] [ModObj A Y]
    (f : X ⟶ Y) [IsModHom A f] :
    ((f ⊗ₘ 𝟙 A) ⊗ₘ f) ≫ winLegN A Y = winLegN A X ≫ (f ⊗ₘ f) := by
  rw [winLegN, winLegN, MonoidalCategory.associator_naturality_assoc,
    ← MonoidalCategory.id_tensorHom Y (actLeft A Y),
    MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id,
    MonoidalCategory.id_tensorHom (f := f),
    ← actLeft_natural A X Y f, Category.assoc,
    ← MonoidalCategory.id_tensorHom X (actLeft A X),
    MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]

/-- A tensor of maps followed by a right whiskering, as one
tensor. -/
private theorem tensor_comp_whisker [Category.{v} D] [MonoidalCategory D]
    {P P' P'' Q Q' : D}
    (p : P ⟶ P') (r : P' ⟶ P'') (q : Q ⟶ Q') :
    (p ⊗ₘ q) ≫ (r ▷ Q') = (p ≫ r) ⊗ₘ q := by
  rw [← MonoidalCategory.tensorHom_id r Q',
    MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]

/-- A right whiskering followed by a tensor of maps, as one
tensor. -/
private theorem whisker_comp_tensor [Category.{v} D] [MonoidalCategory D]
    {P P' P'' Q Q' : D}
    (r : P ⟶ P') (p : P' ⟶ P'') (q : Q ⟶ Q') :
    (r ▷ Q) ≫ (p ⊗ₘ q) = (r ≫ p) ⊗ₘ q := by
  rw [← MonoidalCategory.tensorHom_id r Q,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]

/-- The slot gluing is natural in tensor powers of a morphism. -/
theorem modPowGlue_natural [Category.{v} D] [MonoidalCategory D] {X : D} {Y : D}
    (f : X ⟶ Y) (a b : ℕ) :
    ((tensorPowMap f a ⊗ₘ (f ⊗ₘ f)) ⊗ₘ tensorPowMap f b) ≫
        modPowGlue Y a b =
      modPowGlue X a b ≫ tensorPowMap f (a + 2 + b) := by
  erw [modPowGlue, modPowGlue, ← Category.assoc, tensor_comp_whisker,
    MonoidalCategory.associator_inv_naturality,
    ← whisker_comp_tensor, Category.assoc, Category.assoc]
  exact congrArg (CategoryStruct.comp _)
    (tensorPowMap_concat f (a + 2) b)

/-- A tensor of maps followed by a left whiskering, as one
tensor. -/
private theorem tensor_comp_lwhisker [Category.{v} D] [MonoidalCategory D]
    {P P' Q Q' Q'' : D}
    (p : P ⟶ P') (q : Q ⟶ Q') (s : Q' ⟶ Q'') :
    (p ⊗ₘ q) ≫ (P' ◁ s) = p ⊗ₘ (q ≫ s) := by
  rw [← MonoidalCategory.id_tensorHom P' s,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]

/-- A left whiskering followed by a tensor of maps, as one
tensor. -/
private theorem lwhisker_comp_tensor [Category.{v} D] [MonoidalCategory D]
    {P P' Q Q' Q'' : D}
    (s : Q ⟶ Q') (p : P ⟶ P') (q : Q' ⟶ Q'') :
    (P ◁ s) ≫ (p ⊗ₘ q) = p ⊗ₘ (s ≫ q) := by
  rw [← MonoidalCategory.id_tensorHom P s,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]

/-- Both slot legs are natural in module maps, generically over the
window leg. -/
private theorem modPowLeg_natural_aux
    [Category.{v} D] [MonoidalCategory D] (A : D) {X : D} {Y : D}
    (f : X ⟶ Y) (a b : ℕ)
    {wX : (X ⊗ A) ⊗ X ⟶ X ⊗ X} {wY : (Y ⊗ A) ⊗ Y ⟶ Y ⊗ Y}
    (hw : ((f ⊗ₘ 𝟙 A) ⊗ₘ f) ≫ wY = wX ≫ (f ⊗ₘ f)) :
    ((tensorPowMap f a ⊗ₘ ((f ⊗ₘ 𝟙 A) ⊗ₘ f)) ⊗ₘ tensorPowMap f b) ≫
        ((tensorPow D Y a ◁ wY) ▷ tensorPow D Y b) ≫
          modPowGlue Y a b =
      (((tensorPow D X a ◁ wX) ▷ tensorPow D X b) ≫
          modPowGlue X a b) ≫
        tensorPowMap f (a + 2 + b) := by
  rw [← Category.assoc, tensor_comp_whisker, tensor_comp_lwhisker,
    hw, ← lwhisker_comp_tensor, ← whisker_comp_tensor,
    Category.assoc, Category.assoc]
  exact congrArg (CategoryStruct.comp _) (modPowGlue_natural f a b)

/-- The first slot leg is natural in module maps. -/
theorem modPowLegM_natural
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] {X : D} {Y : D} [ModObj A X] [ModObj A Y]
    (f : X ⟶ Y) [IsModHom A f] (a b : ℕ) :
    ((tensorPowMap f a ⊗ₘ ((f ⊗ₘ 𝟙 A) ⊗ₘ f)) ⊗ₘ tensorPowMap f b) ≫
        modPowLegM A Y a b =
      modPowLegM A X a b ≫ tensorPowMap f (a + 2 + b) :=
  modPowLeg_natural_aux (A := A) f a b (winLegM_natural A f)

/-- The second slot leg is natural in module maps. -/
theorem modPowLegN_natural
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] {X : D} {Y : D}
    [ModObj A X] [ModObj A Y]
    (f : X ⟶ Y) [IsModHom A f] (a b : ℕ) :
    ((tensorPowMap f a ⊗ₘ ((f ⊗ₘ 𝟙 A) ⊗ₘ f)) ⊗ₘ tensorPowMap f b) ≫
        modPowLegN A Y a b =
      modPowLegN A X a b ≫ tensorPowMap f (a + 2 + b) :=
  modPowLeg_natural_aux (A := A) f a b (winLegN_natural A f)

/-- **The module power of a module map**: the tensor power of the
map descends to the module powers, since it carries every slot
relation of the source into a slot relation of the target. -/
noncomputable def modPowMap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    {X : D} {Y : D} [ModObj A X] [ModObj A Y]
    (f : X ⟶ Y) [IsModHom A f] (n : ℕ) :
    modPow A X n ⟶ modPow A Y n :=
  modPowDesc A X (tensorPowMap f n ≫ modPowπ A Y n)
    (fun a b hab => by
      rw [reassoc_of% (powCast_tensorPowMap f hab),
        ← reassoc_of% (modPowLegM_natural A f a b),
        ← reassoc_of% (modPowLegN_natural A f a b)]
      exact congrArg (CategoryStruct.comp _)
        (modPow_rel A Y a b hab))

/-- Defining square of the module-power map. -/
@[reassoc (attr := simp)]
theorem modPowπ_map
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    {X : D} {Y : D} [ModObj A X] [ModObj A Y]
    (f : X ⟶ Y) [IsModHom A f] (n : ℕ) :
    modPowπ A X n ≫ modPowMap A f n =
      tensorPowMap f n ≫ modPowπ A Y n :=
  modPowπ_desc A X _ _

/-- The module power of the identity is the identity. -/
@[simp]
theorem modPowMap_id
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    {X : D} [ModObj A X]
    (n : ℕ) :
    modPowMap A (𝟙 X) n = 𝟙 (modPow A X n) := by
  apply modPow_hom_ext A X
  rw [modPowπ_map, tensorPowMap_id, Category.id_comp,
    Category.comp_id]

/-- The module power is functorial in module maps. -/
theorem modPowMap_comp
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    {X : D} {Y : D} [ModObj A X] [ModObj A Y]
    {Z : D} [ModObj A Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsModHom A f] [IsModHom A g] (n : ℕ) :
    modPowMap A (f ≫ g) n = modPowMap A f n ≫ modPowMap A g n := by
  apply modPow_hom_ext A X
  rw [modPowπ_map, modPowπ_map_assoc, modPowπ_map,
    tensorPowMap_comp, Category.assoc]

/-- The module-power map passes the descended permutation
action. -/
theorem modPowMap_perm
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    {X : D} {Y : D} [ModObj A X] [ModObj A Y]
    (f : X ⟶ Y) [IsModHom A f] (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    modPowMap A f n ≫ modPowPerm (A := A) (X := Y) n σ =
      modPowPerm (A := A) (X := X) n σ ≫ modPowMap A f n := by
  apply modPow_hom_ext A X
  rw [modPowπ_map_assoc, modPowπ_perm, modPowπ_perm_assoc,
    modPowπ_map, reassoc_of% (permMor_natural f n σ)]

/-- **The module-power map passes the group-algebra action**, by
linear extension of the permutation case. -/
theorem modPowMap_alg
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [Linear ℂ D] {X : D} {Y : D} [ModObj A X] [ModObj A Y]
    (f : X ⟶ Y) [IsModHom A f] (n : ℕ)
    (z : SymGroupAlgebra n) :
    modPowMap A f n ≫ (modPowAlg A Y n z : End (modPow A Y n)) =
      (modPowAlg A X n z : End (modPow A X n)) ≫
        modPowMap A f n := by
  induction z using MonoidAlgebra.induction_on with
  | of σ =>
    rw [show (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n))) σ =
        MonoidAlgebra.single σ (1 : ℂ) from rfl, modPowAlg_single,
      modPowAlg_single]
    exact modPowMap_perm A f n σ
  | add z₁ z₂ h₁ h₂ =>
    rw [map_add, map_add]
    exact (intertwine_add h₁.symm h₂.symm).symm
  | smul r z h =>
    rw [map_smul, map_smul]
    exact (intertwine_smul r h.symm).symm

/-- The module-power map passes the idempotent's action. -/
theorem modPowMap_cutIdem
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [Linear ℂ D] {X : D} {Y : D} [ModObj A X] [ModObj A Y]
    (f : X ⟶ Y) [IsModHom A f] (n : ℕ)
    (e : SymGroupAlgebra n) :
    modPowCutIdem A X n e ≫ modPowMap A f n =
      modPowMap A f n ≫ modPowCutIdem A Y n e :=
  (modPowMap_alg A f n e).symm

/-- **The cut of a module map**: the module-power map descends to
the cuts by an idempotent. -/
noncomputable def modPowCutMap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [Linear ℂ D] {X : D} {Y : D} [ModObj A X] [ModObj A Y]
    (f : X ⟶ Y) [IsModHom A f] (n : ℕ)
    (e : SymGroupAlgebra n) :
    modPowCut A X n e ⟶ modPowCut A Y n e :=
  modPowCutDesc A X (modPowMap A f n ≫ modPowCutπ A Y n e)
    (by rw [← Category.assoc, modPowMap_cutIdem A f n e,
      Category.assoc, modPowCutIdem_π])

/-- Defining square of the cut map. -/
@[reassoc (attr := simp)]
theorem modPowCutπ_map
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [Linear ℂ D] {X : D} {Y : D} [ModObj A X] [ModObj A Y]
    (f : X ⟶ Y) [IsModHom A f] (n : ℕ)
    (e : SymGroupAlgebra n) :
    modPowCutπ A X n e ≫ modPowCutMap A f n e =
      modPowMap A f n ≫ modPowCutπ A Y n e :=
  modPowCutπ_desc A X _ _

/-- The cut of the identity is the identity. -/
@[simp]
theorem modPowCutMap_id
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [Linear ℂ D] {X : D} [ModObj A X]
    (n : ℕ) (e : SymGroupAlgebra n) :
    modPowCutMap A (𝟙 X) n e = 𝟙 (modPowCut A X n e) := by
  apply modPowCut_hom_ext A X
  rw [modPowCutπ_map, modPowMap_id, Category.id_comp,
    Category.comp_id]

/-- The cut map is functorial in module maps. -/
theorem modPowCutMap_comp
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [Linear ℂ D] {X : D} {Y : D} [ModObj A X] [ModObj A Y]
    {Z : D} [ModObj A Z] (f : X ⟶ Y)
    (g : Y ⟶ Z) [IsModHom A f] [IsModHom A g] (n : ℕ)
    (e : SymGroupAlgebra n) :
    modPowCutMap A (f ≫ g) n e =
      modPowCutMap A f n e ≫ modPowCutMap A g n e := by
  apply modPowCut_hom_ext A X
  rw [modPowCutπ_map, modPowCutπ_map_assoc, modPowCutπ_map,
    modPowMap_comp, Category.assoc]

/-! ### Killing the cut transports along retracts -/

/-- The cut map depends only on the underlying morphism, not on
the module-map witness. -/
theorem modPowCutMap_congr
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [Linear ℂ D] {X : D} {Y : D} [ModObj A X] [ModObj A Y]
    {f g : X ⟶ Y} [IsModHom A f]
    [IsModHom A g] (h : f = g) (n : ℕ) (e : SymGroupAlgebra n) :
    modPowCutMap A f n e = modPowCutMap A g n e := by
  subst h
  rfl

/-- **The cut of a retract is a retract of the cut**: if the cut of
`X` vanishes, so does the cut of a module retract of `X`. -/
theorem modPowCut_isZero_of_retract
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [Linear ℂ D] {X : D} {Y : D} [ModObj A X] [ModObj A Y]
    (r : X ⟶ Y) (s : Y ⟶ X)
    [IsModHom A r] [IsModHom A s] (hs : s ≫ r = 𝟙 Y) (n : ℕ)
    (e : SymGroupAlgebra n) (hX : IsZero (modPowCut A X n e)) :
    IsZero (modPowCut A Y n e) := by
  rw [IsZero.iff_id_eq_zero]
  have hsplit : modPowCutMap A s n e ≫ modPowCutMap A r n e =
      𝟙 (modPowCut A Y n e) := by
    rw [← modPowCutMap_comp A s r n e,
      modPowCutMap_congr A hs n e, modPowCutMap_id]
  rw [← hsplit, hX.eq_of_tgt (modPowCutMap A s n e) 0, zero_comp]

end MapNat

end RS
