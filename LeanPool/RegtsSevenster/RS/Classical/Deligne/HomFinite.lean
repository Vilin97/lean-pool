/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.UnitSimple

/-!
# Finite length bounds Hom-dimension from the unit

In the setting of Deligne's theorem — an abelian ℂ-linear rigid
monoidal category whose unit endomorphisms are exactly the scalars —
the Hom-space out of the tensor unit is finite dimensional whenever
the target has bounded length, with dimension at most the length
bound.  This is the Hom-finiteness input of Deligne's Proposition
2.1.

The route: a nonzero map `φ : 𝟙 ⟶ Z` is a monomorphism because the
unit is simple (`simple_unit_of_hasScalarUnit`), and pulling
subobjects of `cokernel φ` back along the projection embeds its
subobject chains strictly above the nonzero subobject `φ`, so the
length bound drops by one on the cokernel.  Left-exactness of
`Hom (𝟙, −)`, in the concrete form that a map annihilated by the
projection factors through `φ` with a scalar coefficient, bounds the
kernel of the induced linear map by one dimension, and induction
along the length bound does the rest.

At the bottom of the induction sits the simple case, recorded
separately: `Hom (𝟙, S)` vanishes for a simple `S` not isomorphic
to the unit, and is the line `End (𝟙_ A) = ℂ` when it is — the
scalar-unit hypothesis read as a ℂ-linear equivalence.
-/

namespace RS

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

/-! ## The unit endomorphisms are a line

The scalar-unit hypothesis says that scaling the identity of the
tensor unit is a bijection `ℂ → End (𝟙)`.  Scaling is ℂ-linear, so
the bijection is a ℂ-linear equivalence and `End (𝟙)` is a line.
Transporting along an isomorphism `𝟙 ≅ S` gives the same for
`𝟙 ⟶ S`. -/

section ScalarEnd

variable {A : Type u}

/-- Scaling the identity of the tensor unit, as a ℂ-linear map. -/
private def unitScalarMap
    [Category.{v} A] [Preadditive A] [Linear ℂ A] [MonoidalCategory A] :
    ℂ →ₗ[ℂ] (𝟙_ A ⟶ 𝟙_ A) where
  toFun c := c • 𝟙 (𝟙_ A)
  map_add' a b := add_smul a b _
  map_smul' a b := mul_smul a b _

/-- **The scalars exhaust the unit endomorphisms**, as a ℂ-linear
equivalence `ℂ ≃ₗ End (𝟙_ A)`: this is exactly the content of
`HasScalarUnit`, packaged linearly. -/
noncomputable def unitEndEquiv
    [Category.{v} A] [Preadditive A] [Linear ℂ A] [MonoidalCategory A]
    (hu : HasScalarUnit A) :
    ℂ ≃ₗ[ℂ] (𝟙_ A ⟶ 𝟙_ A) :=
  LinearEquiv.ofBijective unitScalarMap hu

@[simp] theorem unitEndEquiv_apply
    [Category.{v} A] [Preadditive A] [Linear ℂ A] [MonoidalCategory A]
    (hu : HasScalarUnit A) (c : ℂ) :
    unitEndEquiv hu c = c • 𝟙 (𝟙_ A) := rfl

/-- **The unit endomorphisms are one dimensional.** -/
theorem finrank_end_unit
    [Category.{v} A] [Preadditive A] [Linear ℂ A] [MonoidalCategory A]
    (hu : HasScalarUnit A) :
    Module.finrank ℂ (𝟙_ A ⟶ 𝟙_ A) = 1 := by
  rw [← (unitEndEquiv hu).finrank_eq, Module.finrank_self]

/-- An isomorphism `𝟙 ≅ S` identifies `𝟙 ⟶ S` with the unit
endomorphisms, ℂ-linearly. -/
noncomputable def homUnitEquivOfIso
    [Category.{v} A] [Preadditive A] [Linear ℂ A] [MonoidalCategory A]
    {S : A} (e : 𝟙_ A ≅ S) :
    (𝟙_ A ⟶ S) ≃ₗ[ℂ] (𝟙_ A ⟶ 𝟙_ A) :=
  Linear.homCongr ℂ (Iso.refl (𝟙_ A)) e.symm

/-- **`Hom (𝟙, S)` is a line when `S` is isomorphic to the unit**:
it is then `End (𝟙_ A) = ℂ`. -/
theorem finrank_hom_unit_of_iso
    [Category.{v} A] [Preadditive A] [Linear ℂ A] [MonoidalCategory A]
    (hu : HasScalarUnit A) {S : A}
    (e : 𝟙_ A ≅ S) : Module.finrank ℂ (𝟙_ A ⟶ S) = 1 :=
  ((homUnitEquivOfIso e).finrank_eq).trans (finrank_end_unit hu)

end ScalarEnd

/-! ## Maps from the unit to a simple object are proportional

Schur's lemma between the simple unit and a simple target: any
nonzero `φ : 𝟙 ⟶ S` is an isomorphism, so every `ψ : 𝟙 ⟶ S` is a
scalar multiple of it, the scalar produced by `HasScalarUnit`. -/

section Proportional

variable {A : Type u}

/-- A nonzero map from the unit to a simple object is an
isomorphism, the unit being simple; so a simple object receiving a
nonzero map from the unit *is* the unit up to isomorphism. -/
theorem nonempty_unitIso_of_hom_ne_zero
    [Category.{v} A] [Abelian A] [Linear ℂ A] [MonoidalCategory A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A] [RigidCategory A]
    (hu : HasScalarUnit A)
    {S : A} [Simple S] {φ : 𝟙_ A ⟶ S} (hφ : φ ≠ 0) :
    Nonempty (𝟙_ A ≅ S) := by
  haveI : Simple (𝟙_ A) := simple_unit_of_hasScalarUnit hu
  haveI : IsIso φ := isIso_of_hom_simple hφ
  exact ⟨asIso φ⟩

/-- **Maps from the unit to a simple object not isomorphic to it
vanish.** -/
theorem hom_unit_simple_eq_zero
    [Category.{v} A] [Abelian A] [Linear ℂ A] [MonoidalCategory A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A] [RigidCategory A]
    (hu : HasScalarUnit A) {S : A}
    [Simple S] (h : IsEmpty (𝟙_ A ≅ S)) (φ : 𝟙_ A ⟶ S) : φ = 0 := by
  by_contra hφ
  exact h.elim (nonempty_unitIso_of_hom_ne_zero hu hφ).some

/-- `Hom (𝟙, S)` is trivial for a simple `S` not isomorphic to the
unit. -/
theorem subsingleton_hom_unit_simple
    [Category.{v} A] [Abelian A] [Linear ℂ A] [MonoidalCategory A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A] [RigidCategory A]
    (hu : HasScalarUnit A) {S : A}
    [Simple S] (h : IsEmpty (𝟙_ A ≅ S)) :
    Subsingleton (𝟙_ A ⟶ S) :=
  ⟨fun f g => by
    rw [hom_unit_simple_eq_zero hu h f, hom_unit_simple_eq_zero hu h g]⟩

/-- **`Hom (𝟙, S)` vanishes for a simple `S` not isomorphic to the
unit.** -/
theorem finrank_hom_unit_simple_eq_zero
    [Category.{v} A] [Abelian A] [Linear ℂ A] [MonoidalCategory A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A] [RigidCategory A]
    (hu : HasScalarUnit A)
    {S : A} [Simple S] (h : IsEmpty (𝟙_ A ≅ S)) :
    Module.finrank ℂ (𝟙_ A ⟶ S) = 0 := by
  haveI := subsingleton_hom_unit_simple hu h
  exact Module.finrank_zero_of_subsingleton

end Proportional

/-! ## Quotients drop the length bound

Pulling a subobject of a quotient back along the projection gives a
subobject of the ambient object.  The operation is monotone, and
along an epimorphism it reflects inequalities, so it embeds strict
chains; every pullback contains the kernel of the projection, so for
the quotient by a nonzero subobject the embedded chain sits strictly
above `⊥` and the length bound drops by one. -/

section QuotientLength

variable {C : Type u}

/-- The pullback of a subobject along a morphism into its ambient
object. -/
private noncomputable def pbSub [Category.{v} C] [Abelian C]
    {Z W : C} (π : Z ⟶ W)
    (P : Subobject W) : Subobject Z :=
  Subobject.mk (pullback.snd P.arrow π)

/-- Pulling subobjects back is monotone. -/
private lemma pbSub_mono [Category.{v} C] [Abelian C]
    {Z W : C} (π : Z ⟶ W) {P Q : Subobject W}
    (h : P ≤ Q) : pbSub π P ≤ pbSub π Q := by
  refine Subobject.mk_le_mk_of_comm
    (pullback.lift (pullback.fst P.arrow π ≫ Subobject.ofLE P Q h)
      (pullback.snd P.arrow π) ?_) (pullback.lift_snd _ _ _)
  rw [Category.assoc, Subobject.ofLE_arrow]
  exact pullback.condition

/-- Along an epimorphism, pulling subobjects back reflects
inequalities: the pullback of `P` maps onto `P`, and a factorisation
of pullbacks descends along that epimorphism. -/
private lemma le_of_pbSub_le [Category.{v} C] [Abelian C]
    {Z W : C} (π : Z ⟶ W) [Epi π]
    {P Q : Subobject W} (h : pbSub π P ≤ pbSub π Q) : P ≤ Q := by
  have hu : Subobject.ofMkLEMk _ _ h ≫ pullback.snd Q.arrow π
      = pullback.snd P.arrow π :=
    Subobject.ofMkLEMk_comp h
  have hker : kernel.ι (pullback.fst P.arrow π)
      ≫ (Subobject.ofMkLEMk _ _ h ≫ pullback.fst Q.arrow π) = 0 := by
    rw [← cancel_mono Q.arrow]
    simp only [Category.assoc, zero_comp]
    rw [pullback.condition, ← Category.assoc (Subobject.ofMkLEMk _ _ h),
      hu, ← pullback.condition, ← Category.assoc, kernel.condition,
      zero_comp]
  have hv := Abelian.comp_epiDesc (pullback.fst P.arrow π)
    (Subobject.ofMkLEMk _ _ h ≫ pullback.fst Q.arrow π) hker
  refine Subobject.le_of_comm
    (Abelian.epiDesc (pullback.fst P.arrow π)
      (Subobject.ofMkLEMk _ _ h ≫ pullback.fst Q.arrow π) hker) ?_
  rw [← cancel_epi (pullback.fst P.arrow π), ← Category.assoc, hv,
    Category.assoc, pullback.condition,
    ← Category.assoc (Subobject.ofMkLEMk _ _ h), hu,
    ← pullback.condition]

/-- Along an epimorphism, pulling subobjects back is strictly
monotone. -/
private lemma pbSub_strictMono [Category.{v} C] [Abelian C]
    {Z W : C} (π : Z ⟶ W) [Epi π]
    {P Q : Subobject W} (h : P < Q) : pbSub π P < pbSub π Q :=
  lt_of_le_of_ne (pbSub_mono π h.le) fun he =>
    h.ne (le_antisymm h.le (le_of_pbSub_le π he.ge))

/-- Every subobject pulled back from the cokernel of `φ` contains
the subobject `φ`. -/
private lemma mk_le_pbSub_cokernel [Category.{v} C] [Abelian C]
    {U Z : C} (φ : U ⟶ Z) [Mono φ]
    (P : Subobject (cokernel φ)) :
    Subobject.mk φ ≤ pbSub (cokernel.π φ) P := by
  refine Subobject.mk_le_mk_of_comm (pullback.lift 0 φ ?_)
    (pullback.lift_snd _ _ _)
  rw [zero_comp, cokernel.condition]

/-- **Quotients by a nonzero subobject drop the length bound**: if
`LengthLE Z (N + 1)` and `φ : U ⟶ Z` is a nonzero monomorphism, then
`LengthLE (cokernel φ) N`.  A strict chain in the cokernel pulls
back to a strict chain in `Z` sitting above the nonzero subobject
`φ`, so prepending `⊥` lengthens it by one. -/
private theorem lengthLE_cokernel [Category.{v} C] [Abelian C]
    {U Z : C} (φ : U ⟶ Z) [Mono φ]
    (hφ : φ ≠ 0) {N : ℕ} (h : LengthLE Z (N + 1)) :
    LengthLE (cokernel φ) N := by
  intro f hf
  refine h (Fin.cons ⊥ fun i => pbSub (cokernel.π φ) (f i)) ?_
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  induction i using Fin.cases with
  | zero =>
    rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]
    refine Ne.bot_lt fun he => hφ ?_
    exact Subobject.mk_eq_bot_iff_zero.mp
      (le_bot_iff.mp (he ▸ mk_le_pbSub_cokernel φ (f 0)))
  | succ j =>
    rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
    exact pbSub_strictMono _ (hf (Fin.castSucc_lt_succ (i := j)))

end QuotientLength

/-! ## The induction along the length bound

`Hom (𝟙, −)` is left exact; concretely, a map `𝟙 ⟶ Z` annihilated
by the projection to `cokernel φ` factors through the kernel `φ` of
that projection, with coefficient a unit endomorphism — a scalar.
So the kernel of postcomposition by the projection is at most one
dimensional, the quotient lemma above drops the length bound on the
cokernel, and rank-nullity closes the induction. -/

section Induction

variable {A : Type u}

/-- A map from the unit annihilated by the projection to the
cokernel of a monomorphism `φ` from the unit is a scalar multiple
of `φ`: it factors through the kernel of the projection, which is
`φ` itself, with coefficient in `End (𝟙) = ℂ`. -/
private theorem eq_smul_of_comp_cokernel_π_zero
    [Category.{v} A] [Abelian A] [Linear ℂ A] [MonoidalCategory A]
    (hu : HasScalarUnit A) {Z : A} {φ ψ : 𝟙_ A ⟶ Z} [Mono φ]
    (hψ : ψ ≫ cokernel.π φ = 0) : ∃ c : ℂ, ψ = c • φ := by
  have hlim : IsLimit (KernelFork.ofι φ (cokernel.condition φ)) :=
    Abelian.monoIsKernelOfCokernel
      (CokernelCofork.ofπ (cokernel.π φ) (cokernel.condition φ))
      (cokernelIsCokernel φ)
  obtain ⟨χ, hχ⟩ := KernelFork.IsLimit.lift' hlim ψ hψ
  simp only [Fork.ι_ofι] at hχ
  obtain ⟨χ₀, hχ₀⟩ : ∃ χ₀ : 𝟙_ A ⟶ 𝟙_ A, χ₀ ≫ φ = ψ := ⟨χ, hχ⟩
  obtain ⟨c, hc⟩ := hu.surjective χ₀
  replace hc : c • 𝟙 (𝟙_ A) = χ₀ := hc
  exact ⟨c, by rw [← hχ₀, ← hc, Linear.smul_comp, Category.id_comp]⟩

/-- The induction workhorse, with simplicity of the unit supplied as
a hypothesis: a length bound of `N` on `Z` makes `𝟙 ⟶ Z` a finite
dimensional ℂ-module of dimension at most `N`. -/
private theorem homFinite_core
    [Category.{v} A] [Abelian A] [Linear ℂ A] [MonoidalCategory A]
    (hu : HasScalarUnit A)
    (hs : Simple (𝟙_ A)) :
    ∀ (N : ℕ) (Z : A), LengthLE Z N →
      Module.Finite ℂ (𝟙_ A ⟶ Z)
        ∧ Module.finrank ℂ (𝟙_ A ⟶ Z) ≤ N := by
  haveI := hs
  intro N
  induction N with
  | zero =>
    intro Z h
    rcases subsingleton_or_nontrivial (𝟙_ A ⟶ Z) with hss | hnt
    · haveI := hss
      exact ⟨inferInstance, by
        rw [Module.finrank_zero_of_subsingleton]⟩
    · haveI := hnt
      obtain ⟨φ, hφ⟩ := exists_ne (0 : 𝟙_ A ⟶ Z)
      haveI : Mono φ := mono_of_nonzero_from_simple hφ
      refine absurd ?_ (h (Fin.cons ⊥ fun _ : Fin 1 => Subobject.mk φ))
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      induction i using Fin.cases with
      | zero =>
        rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]
        exact Ne.bot_lt fun he =>
          hφ (Subobject.mk_eq_bot_iff_zero.mp he)
      | succ j => exact j.elim0
  | succ M ih =>
    intro Z h
    rcases subsingleton_or_nontrivial (𝟙_ A ⟶ Z) with hss | hnt
    · haveI := hss
      exact ⟨inferInstance, by
        rw [Module.finrank_zero_of_subsingleton]; exact Nat.zero_le _⟩
    · haveI := hnt
      obtain ⟨φ, hφ⟩ := exists_ne (0 : 𝟙_ A ⟶ Z)
      haveI : Mono φ := mono_of_nonzero_from_simple hφ
      obtain ⟨hfinQ, hrkQ⟩ := ih (cokernel φ) (lengthLE_cokernel φ hφ h)
      haveI := hfinQ
      set L : (𝟙_ A ⟶ Z) →ₗ[ℂ] (𝟙_ A ⟶ cokernel φ) :=
        Linear.rightComp ℂ (𝟙_ A) (cokernel.π φ) with hLdef
      have hker : LinearMap.ker L ≤ Submodule.span ℂ {φ} := by
        intro ψ hψ
        have hψ0 : ψ ≫ cokernel.π φ = 0 := by
          have hmem := LinearMap.mem_ker.mp hψ
          rwa [hLdef, Linear.rightComp_apply] at hmem
        obtain ⟨c, hc⟩ := eq_smul_of_comp_cokernel_π_zero hu hψ0
        exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
      haveI hkfin : FiniteDimensional ℂ (LinearMap.ker L) :=
        Submodule.finiteDimensional_of_le hker
      haveI hrfin : FiniteDimensional ℂ (LinearMap.range L) :=
        inferInstance
      haveI hfin : Module.Finite ℂ (𝟙_ A ⟶ Z) :=
        Module.finite_def.mpr
          (Submodule.fg_of_fg_map_of_fg_inf_ker L
            (by rw [Submodule.map_top]
                exact Module.Finite.iff_fg.mp hrfin)
            (by rw [top_inf_eq]
                exact Module.Finite.iff_fg.mp hkfin))
      refine ⟨hfin, ?_⟩
      have hsum := LinearMap.finrank_range_add_finrank_ker L
      have h1 : Module.finrank ℂ (LinearMap.range L) ≤ M :=
        le_trans (Submodule.finrank_le _) hrkQ
      have h2 : Module.finrank ℂ (LinearMap.ker L) ≤ 1 := by
        have h3 := Submodule.finrank_mono hker
        rwa [finrank_span_singleton hφ] at h3
      omega

end Induction

/-! ## The theorems -/

section Main

variable {A : Type u}

/-- **Finite length bounds Hom-dimension from the unit**: in the
setting of Deligne's theorem, a length bound of `N` on `Z` makes
`𝟙 ⟶ Z` a finite dimensional ℂ-module of dimension at most `N`. -/
theorem finrank_hom_unit_le
    [Category.{v} A] [Abelian A] [Linear ℂ A] [MonoidalCategory A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A] [RigidCategory A]
    (hu : HasScalarUnit A) {Z : A} {N : ℕ}
    (h : LengthLE Z N) :
    Module.Finite ℂ (𝟙_ A ⟶ Z)
      ∧ Module.finrank ℂ (𝟙_ A ⟶ Z) ≤ N :=
  homFinite_core hu (simple_unit_of_hasScalarUnit hu) N Z h

/-- The duality correspondence `(X ⟶ Y) ≃ₗ (𝟙 ⟶ Y ⊗ Xᘁ)` as a
ℂ-linear equivalence: precomposition by the left unitor followed by
the right-dual adjunction `tensorRightHomEquiv`.  Linearity follows
from bilinearity of composition and of the tensor product. -/
noncomputable def homUnitDualEquiv
    [Category.{v} A] [Abelian A] [Linear ℂ A] [MonoidalCategory A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A] [RigidCategory A]
    (X Y : A) :
    (X ⟶ Y) ≃ₗ[ℂ] (𝟙_ A ⟶ Y ⊗ Xᘁ) where
  toFun f := tensorRightHomEquiv (𝟙_ A) X (Xᘁ) Y ((λ_ X).hom ≫ f)
  map_add' f g := by simp [tensorRightHomEquiv, Preadditive.comp_add]
  map_smul' c f := by simp [tensorRightHomEquiv, Linear.comp_smul]
  invFun g :=
    (λ_ X).inv ≫ (tensorRightHomEquiv (𝟙_ A) X (Xᘁ) Y).symm g
  left_inv f := by simp
  right_inv g := by simp

/-- **Finite length bounds every Hom-dimension**: in the setting of
Deligne's theorem, a length bound of `N` on `Y ⊗ Xᘁ` makes `X ⟶ Y`
a finite dimensional ℂ-module of dimension at most `N`, via the
duality correspondence `(X ⟶ Y) ≃ₗ (𝟙 ⟶ Y ⊗ Xᘁ)`. -/
theorem finrank_hom_le
    [Category.{v} A] [Abelian A] [Linear ℂ A] [MonoidalCategory A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A] [RigidCategory A]
    (hu : HasScalarUnit A) {X Y : A} {N : ℕ}
    (h : LengthLE (Y ⊗ Xᘁ) N) :
    Module.Finite ℂ (X ⟶ Y) ∧ Module.finrank ℂ (X ⟶ Y) ≤ N := by
  obtain ⟨hfin, hrk⟩ := finrank_hom_unit_le hu h
  haveI := hfin
  refine ⟨Module.Finite.equiv (homUnitDualEquiv X Y).symm, ?_⟩
  rw [(homUnitDualEquiv X Y).finrank_eq]
  exact hrk

/-! ### Finite length, unquantified

`LengthLE Z N` is the bound-shaped finite-length predicate of this
development; "`Z` has finite length" is `∃ N, LengthLE Z N`, and
"every object has finite length" is that statement quantified over
all objects.  There is no finite-length typeclass here, so the
hypothesis is carried explicitly. -/

/-- **Hom out of the unit is finite dimensional** whenever the
target has finite length. -/
theorem finiteDimensional_hom_unit
    [Category.{v} A] [Abelian A] [Linear ℂ A] [MonoidalCategory A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A] [RigidCategory A]
    (hu : HasScalarUnit A) {Z : A}
    (h : ∃ N : ℕ, LengthLE Z N) :
    FiniteDimensional ℂ (𝟙_ A ⟶ Z) := by
  obtain ⟨N, hN⟩ := h
  exact (finrank_hom_unit_le hu hN).1

end Main

end RS
