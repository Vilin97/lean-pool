/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.RestrictedPowerSeries
import LeanPool.UniformSheafyTateDomains.AdicSpaces.RestrictedModule
import LeanPool.UniformSheafyTateDomains.AdicSpaces.NoetherianTateModules
import LeanPool.UniformSheafyTateDomains.AdicSpaces.HuberRings
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Lemma745
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornBanachTheorem
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Filtration
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Tate and Laurent Algebras

This file defines the univariate Tate algebra `A⟨X⟩` and the Laurent Tate algebra
`A⟨ζ, ζ⁻¹⟩`, following Wedhorn's *Adic Spaces*, §6.9 and §8.29–8.33.

These are the central reusable objects for the Tate acyclicity proof (Theorem 8.28(b)).

## Main definitions

* `TateAlgebra A` : The univariate restricted power series ring `A⟨X⟩`.
* `TateAlgebra₂ A` : The bivariate restricted power series ring `A⟨X, Y⟩`.
* `LaurentTateAlgebra A` : The Laurent restricted power series ring `A⟨ζ, ζ⁻¹⟩`,
  defined as the quotient `A⟨X, Y⟩ / (XY - 1)`.

## Main results

* `TateAlgebra.evalZeroHom` : The evaluation-at-zero ring hom `A⟨X⟩ →+* A`.
* `TateAlgebra.evalZeroHom_surjective` : Surjectivity of evaluation at zero.
* `LaurentTateAlgebra.zeta_mul_zetaInv` : The defining relation `ζ · ζ⁻¹ = 1`.
* `LaurentTateAlgebra.zetaUnit` : `ζ` is a unit in `A⟨ζ, ζ⁻¹⟩`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §6.9, §8.29–8.33
-/

open Filter MvPowerSeries

universe u

/-! ### Restricted power series: variables are restricted -/

/-- Any variable `MvPowerSeries.X i` is a restricted power series: it has exactly one
nonzero coefficient (at `Finsupp.single i 1`). -/
theorem MvPowerSeries.X_isRestricted {k : ℕ} {A : Type u} [CommRing A] [TopologicalSpace A]
    (i : Fin k) : MvPowerSeries.IsRestricted (MvPowerSeries.X i : MvPowerSeries (Fin k) A) := by
  change Tendsto _ cofinite (nhds 0)
  apply tendsto_nhds.mpr
  intro U hU h0U
  rw [Filter.mem_cofinite]
  apply (Set.finite_singleton (Finsupp.single i 1)).subset
  intro s hs
  simp only [Set.mem_compl_iff, Set.mem_preimage] at hs
  simp only [Set.mem_singleton_iff]
  by_contra h
  exact hs (by rw [MvPowerSeries.coeff_X, if_neg h]; exact h0U)

/-! ### Univariate Tate algebra -/

/-- The univariate Tate algebra `A⟨X⟩`, the ring of restricted power series in one variable.
This is `restrictedMvPowerSeriesSubring 1 A`, specialized to the univariate case.
See Wedhorn, Definition 6.9. -/
abbrev TateAlgebra (A : Type u) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] :
    Subring (MvPowerSeries (Fin 1) A) :=
  restrictedMvPowerSeriesSubring 1 A

namespace TateAlgebra

variable {A : Type u} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- Convert a natural number to the corresponding univariate multi-index `Fin 1 →₀ ℕ`. -/
noncomputable def toIndex (n : ℕ) : Fin 1 →₀ ℕ := Finsupp.single 0 n

@[simp]
theorem toIndex_zero : toIndex (0 : ℕ) = (0 : Fin 1 →₀ ℕ) :=
  Finsupp.single_zero (a := (0 : Fin 1))

/-- Every multi-index `s : Fin 1 →₀ ℕ` equals `toIndex (s 0)`. -/
theorem eq_toIndex (s : Fin 1 →₀ ℕ) : s = toIndex (s 0) := by
  apply Finsupp.ext; intro j
  rw [show j = 0 from Fin.eq_zero j]
  simp only [toIndex, Finsupp.single_eq_same]

/-- The n-th coefficient of a univariate restricted power series `f ∈ A⟨X⟩`. -/
noncomputable def coeff (n : ℕ) (f : ↥(TateAlgebra A)) : A :=
  (MvPowerSeries.coeff (R := A) (toIndex n)) f.val

/-- The coefficients of a restricted power series tend to zero along the
cofinite filter on `ℕ`. This is the univariate form of restrictedness. -/
theorem coeff_tendsto_zero (f : ↥(TateAlgebra A)) :
    Filter.Tendsto (fun n ↦ coeff n f) Filter.cofinite (nhds (0 : A)) :=
  f.prop.comp (Finsupp.single_injective (0 : Fin 1)).tendsto_cofinite

/-- The variable `X` as an element of `A⟨X⟩`. -/
noncomputable def X : ↥(TateAlgebra A) :=
  ⟨MvPowerSeries.X (0 : Fin 1), MvPowerSeries.X_isRestricted 0⟩

/-- Two elements of `A⟨X⟩` are equal iff they have the same coefficients. -/
@[ext]
theorem ext {f g : ↥(TateAlgebra A)} (h : ∀ n : ℕ, coeff n f = coeff n g) : f = g := by
  ext1
  exact MvPowerSeries.ext fun s ↦ by rw [eq_toIndex s]; exact h (s 0)

/-- The constant term (evaluation at zero) is a ring homomorphism `A⟨X⟩ →+* A`. -/
noncomputable def evalZeroHom : ↥(TateAlgebra A) →+* A where
  toFun f := coeff 0 f
  map_one' := by simp only [coeff, toIndex_zero]; norm_cast
  map_mul' f g := by
    simp only [coeff, toIndex_zero, Subring.coe_mul]
    rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_zero]
    simp only [Finset.sum_singleton]
  map_zero' := by simp only [coeff, Subring.coe_zero, map_zero]
  map_add' f g := by simp only [coeff, map_add, Subring.coe_add]

/-- The evaluation-at-zero map is surjective: every `a : A` is the constant term of the
constant power series `algebraMap A _ a`. -/
theorem evalZeroHom_surjective : Function.Surjective (evalZeroHom (A := A)) := by
  intro a
  exact ⟨⟨algebraMap A _ a, MvPowerSeries.IsRestricted_algebraMap a⟩, by
    simp only [evalZeroHom, coeff, toIndex_zero, MvPowerSeries.algebraMap_apply]
    norm_cast⟩

end TateAlgebra

/-! ### Bivariate Tate algebra -/

/-- The bivariate Tate algebra `A⟨X, Y⟩`, the ring of restricted power series in two variables.
See Wedhorn, Definition 6.9. -/
abbrev TateAlgebra₂ (A : Type u) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] :
    Subring (MvPowerSeries (Fin 2) A) :=
  restrictedMvPowerSeriesSubring 2 A

namespace TateAlgebra₂

variable {A : Type u} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- The variable `X` as an element of `A⟨X, Y⟩`. -/
noncomputable def X : ↥(TateAlgebra₂ A) :=
  ⟨MvPowerSeries.X (0 : Fin 2), MvPowerSeries.X_isRestricted 0⟩

/-- The variable `Y` as an element of `A⟨X, Y⟩`. -/
noncomputable def Y : ↥(TateAlgebra₂ A) :=
  ⟨MvPowerSeries.X (1 : Fin 2), MvPowerSeries.X_isRestricted 1⟩

/-- The element `XY - 1` in `A⟨X, Y⟩`. -/
noncomputable def XY_sub_one : ↥(TateAlgebra₂ A) := X * Y - 1

end TateAlgebra₂

/-! ### Laurent Tate algebra (quotient model) -/

/-- The ideal generated by `XY - 1` in `A⟨X, Y⟩`. -/
noncomputable def laurentIdeal (A : Type u) [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] : Ideal ↥(TateAlgebra₂ A) :=
  Ideal.span {TateAlgebra₂.XY_sub_one}

/-- The Laurent Tate algebra `A⟨ζ, ζ⁻¹⟩`, defined as the quotient of the bivariate
restricted power series ring `A⟨X, Y⟩` by the ideal `(XY - 1)`.

This models the ring of bilateral restricted power series
`∑_{n ∈ ℤ} aₙ ζⁿ` with `aₙ → 0` as `|n| → ∞`.

See Wedhorn, §8.29–8.33 (Definition 8.27). -/
noncomputable def LaurentTateAlgebra (A : Type u) [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] :=
  ↥(TateAlgebra₂ A) ⧸ laurentIdeal A

namespace LaurentTateAlgebra

variable {A : Type u} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

noncomputable instance : CommRing (LaurentTateAlgebra A) :=
  Ideal.Quotient.commRing (laurentIdeal A)

/-- The quotient map `A⟨X, Y⟩ →+* A⟨ζ, ζ⁻¹⟩`. -/
noncomputable def mkHom : ↥(TateAlgebra₂ A) →+* LaurentTateAlgebra A :=
  Ideal.Quotient.mk (laurentIdeal A)

/-- The image of `X` in the Laurent algebra, representing `ζ`. -/
noncomputable def zeta : LaurentTateAlgebra A := mkHom TateAlgebra₂.X

/-- The image of `Y` in the Laurent algebra, representing `ζ⁻¹`. -/
noncomputable def zetaInv : LaurentTateAlgebra A := mkHom TateAlgebra₂.Y

/-- The defining relation: `ζ · ζ⁻¹ = 1` in `A⟨ζ, ζ⁻¹⟩`. -/
theorem zeta_mul_zetaInv : zeta * zetaInv = (1 : LaurentTateAlgebra A) := by
  change mkHom TateAlgebra₂.X * mkHom TateAlgebra₂.Y = 1
  rw [← map_mul, ← map_one mkHom]
  apply Ideal.Quotient.eq.mpr
  change TateAlgebra₂.X * TateAlgebra₂.Y - 1 ∈ laurentIdeal A
  exact Ideal.subset_span (Set.mem_singleton _)

/-- The defining relation: `ζ⁻¹ · ζ = 1` in `A⟨ζ, ζ⁻¹⟩`. -/
theorem zetaInv_mul_zeta : zetaInv * zeta = (1 : LaurentTateAlgebra A) := by
  rw [mul_comm, zeta_mul_zetaInv]

/-- `ζ` is a unit in `A⟨ζ, ζ⁻¹⟩`. -/
noncomputable def zetaUnit : (LaurentTateAlgebra A)ˣ where
  val := zeta
  inv := zetaInv
  val_inv := zeta_mul_zetaInv
  inv_val := zetaInv_mul_zeta

/-- The `A`-algebra structure on `A⟨ζ, ζ⁻¹⟩`, via the composition
`A → A⟨X, Y⟩ → A⟨ζ, ζ⁻¹⟩`. -/
noncomputable instance : Algebra A (LaurentTateAlgebra A) :=
  (mkHom.comp (algebraMap A ↥(TateAlgebra₂ A))).toAlgebra

/-! ### Embeddings into the Laurent algebra -/

/-- The underlying function for the variable inclusion: sends a univariate power series to
a `k`-variate one by mapping the single variable to variable `j`. -/
noncomputable def varInclFun {k : ℕ} (j : Fin k) (f : MvPowerSeries (Fin 1) A) :
    MvPowerSeries (Fin k) A :=
  fun e ↦ if e = Finsupp.single j (e j)
    then (MvPowerSeries.coeff (Finsupp.single 0 (e j))) f else 0

omit [TopologicalSpace A] [NonarchimedeanRing A] in
@[simp]
theorem varInclFun_apply {k : ℕ} (j : Fin k) (f : MvPowerSeries (Fin 1) A)
    (e : Fin k →₀ ℕ) : varInclFun j f e =
    if e = Finsupp.single j (e j)
    then (MvPowerSeries.coeff (Finsupp.single 0 (e j))) f else 0 := rfl

omit [TopologicalSpace A] [NonarchimedeanRing A] in
@[simp]
theorem varInclFun_coeff_single {k : ℕ} (j : Fin k) (f : MvPowerSeries (Fin 1) A) (n : ℕ) :
    varInclFun j f (Finsupp.single j n) =
    (MvPowerSeries.coeff (Finsupp.single 0 n)) f := by
  simp only [varInclFun, Finsupp.single_eq_same, ↓reduceIte]

omit [TopologicalSpace A] [NonarchimedeanRing A] in
theorem varInclFun_zero {k : ℕ} (j : Fin k) :
    varInclFun j (0 : MvPowerSeries (Fin 1) A) = 0 := by
  apply MvPowerSeries.ext; intro e
  change varInclFun j 0 e = (MvPowerSeries.coeff e) 0
  rw [varInclFun_apply, map_zero]; split_ifs <;> rfl

omit [TopologicalSpace A] [NonarchimedeanRing A] in
theorem varInclFun_one {k : ℕ} (j : Fin k) :
    varInclFun j (1 : MvPowerSeries (Fin 1) A) = 1 := by
  apply MvPowerSeries.ext; intro e
  change varInclFun j 1 e = (MvPowerSeries.coeff e) 1
  rw [varInclFun_apply, MvPowerSeries.coeff_one]
  split_ifs with h1 h2
  · rw [MvPowerSeries.coeff_one, if_pos]
    rw [h1]; simp only [Finsupp.single_eq_zero.mp h2, Finsupp.single_zero]
  · rw [MvPowerSeries.coeff_one, if_neg]
    intro h0; exact h2 (Finsupp.single_eq_zero.mpr (by rw [h1] at h0; simpa using h0))
  · rw [MvPowerSeries.coeff_one, if_neg]
    intro h0; exact h1 (by rw [h0]; simp only [Finsupp.zero_apply, Finsupp.single_zero])

omit [TopologicalSpace A] [NonarchimedeanRing A] in
theorem varInclFun_add {k : ℕ} (j : Fin k) (f g : MvPowerSeries (Fin 1) A) :
    varInclFun j (f + g) = varInclFun j f + varInclFun j g := by
  apply MvPowerSeries.ext; intro e
  change varInclFun j (f + g) e = varInclFun j f e + varInclFun j g e
  simp only [varInclFun_apply, map_add]; split_ifs <;> ring

omit [TopologicalSpace A] [NonarchimedeanRing A] in
theorem varInclFun_mul {k : ℕ} (j : Fin k) (f g : MvPowerSeries (Fin 1) A) :
    varInclFun j (f * g) = varInclFun j f * varInclFun j g := by
  apply MvPowerSeries.ext; intro e
  by_cases h : e = Finsupp.single j (e j)
  · change varInclFun j (f * g) e = (MvPowerSeries.coeff e) (varInclFun j f * varInclFun j g)
    rw [h]; simp only [varInclFun_coeff_single]
    rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    rw [Finsupp.antidiagonal_single, Finsupp.antidiagonal_single]
    simp only [Finset.sum_map]
    apply Finset.sum_congr rfl; intro ⟨a, b⟩ _
    change _ = varInclFun j f (Finsupp.single j a) * varInclFun j g (Finsupp.single j b)
    simp only [varInclFun_coeff_single]; rfl
  · change varInclFun j (f * g) e = (MvPowerSeries.coeff e) (varInclFun j f * varInclFun j g)
    rw [varInclFun_apply, if_neg h, MvPowerSeries.coeff_mul]
    symm; apply Finset.sum_eq_zero; intro p hp
    rw [Finset.mem_antidiagonal] at hp
    change varInclFun j f p.1 * varInclFun j g p.2 = 0
    rw [varInclFun_apply, varInclFun_apply]
    by_cases h1 : p.1 = Finsupp.single j (p.1 j)
    · have h2 : p.2 ≠ Finsupp.single j (p.2 j) := by
        intro h2; apply h; rw [← hp, h1, h2]
        ext i; simp only [Finsupp.single_apply, Finsupp.add_apply]; split_ifs <;> ring
      rw [if_neg h2]; ring
    · rw [if_neg h1]; ring

/-- The variable inclusion as a ring homomorphism. -/
noncomputable def varInclHom {k : ℕ} (j : Fin k) :
    MvPowerSeries (Fin 1) A →+* MvPowerSeries (Fin k) A where
  toFun := varInclFun j
  map_zero' := varInclFun_zero j
  map_one' := varInclFun_one j
  map_add' := varInclFun_add j
  map_mul' := varInclFun_mul j

omit [NonarchimedeanRing A] in
/-- The variable inclusion preserves the restricted property. -/
theorem varInclHom_isRestricted {k : ℕ} (j : Fin k) (f : MvPowerSeries (Fin 1) A)
    (hf : MvPowerSeries.IsRestricted f) :
    MvPowerSeries.IsRestricted (varInclHom j f) := by
  change Tendsto _ cofinite (nhds 0)
  rw [tendsto_nhds]
  intro U hU h0U
  rw [Filter.mem_cofinite]
  have hfU : {s | (MvPowerSeries.coeff s) f ∉ U}.Finite := by
    have := tendsto_nhds.mp hf U hU h0U
    rwa [Filter.mem_cofinite] at this
  apply (hfU.image (fun d ↦ Finsupp.mapDomain (fun _ ↦ j) d)).subset
  intro e he
  simp only [Set.mem_compl_iff, Set.mem_preimage] at he
  have he2 : varInclFun j f e ∉ U := by
    change (MvPowerSeries.coeff e) (varInclHom j f) ∉ U at he
    exact he
  rw [varInclFun_apply] at he2
  split_ifs at he2 with h
  · refine ⟨Finsupp.single 0 (e j), he2, ?_⟩
    change Finsupp.mapDomain (fun _ ↦ j) (Finsupp.single 0 (e j)) = e
    rw [Finsupp.mapDomain_single]; exact h.symm
  · exact absurd h0U he2

/-- The positive inclusion `A⟨X⟩ →+* A⟨X, Y⟩` sending `f(X) ↦ f(X)`, defined by mapping
the single variable to the first variable `X` of the bivariate ring. -/
noncomputable def posIncl : ↥(TateAlgebra A) →+* ↥(TateAlgebra₂ A) where
  toFun f := ⟨varInclHom 0 f.val, varInclHom_isRestricted 0 f.val f.prop⟩
  map_one' := by ext1; exact map_one (varInclHom (0 : Fin 2))
  map_mul' f g := by ext1; exact map_mul (varInclHom (0 : Fin 2)) f.val g.val
  map_zero' := by ext1; exact map_zero (varInclHom (0 : Fin 2))
  map_add' f g := by ext1; exact map_add (varInclHom (0 : Fin 2)) f.val g.val

/-- The negative inclusion `A⟨X⟩ →+* A⟨X, Y⟩` sending `f(X) ↦ f(Y)`, defined by mapping
the single variable to the second variable `Y` of the bivariate ring. -/
noncomputable def negIncl : ↥(TateAlgebra A) →+* ↥(TateAlgebra₂ A) where
  toFun f := ⟨varInclHom 1 f.val, varInclHom_isRestricted 1 f.val f.prop⟩
  map_one' := by ext1; exact map_one (varInclHom (1 : Fin 2))
  map_mul' f g := by ext1; exact map_mul (varInclHom (1 : Fin 2)) f.val g.val
  map_zero' := by ext1; exact map_zero (varInclHom (1 : Fin 2))
  map_add' f g := by ext1; exact map_add (varInclHom (1 : Fin 2)) f.val g.val

/-- The positive embedding `A⟨X⟩ →+* A⟨ζ, ζ⁻¹⟩` sending `X ↦ ζ`.
Embeds restricted power series in positive powers of `ζ`. -/
noncomputable def posEmbHom : ↥(TateAlgebra A) →+* LaurentTateAlgebra A :=
  mkHom.comp posIncl

/-- The negative embedding `A⟨X⟩ →+* A⟨ζ, ζ⁻¹⟩` sending `X ↦ ζ⁻¹`.
Embeds restricted power series in negative powers of `ζ`. -/
noncomputable def negEmbHom : ↥(TateAlgebra A) →+* LaurentTateAlgebra A :=
  mkHom.comp negIncl

end LaurentTateAlgebra

/-! ### TICKET-2B: Remark 8.29 + Lemma 8.31

The algebraic engine for Tate acyclicity: the quotient `A⟨X⟩/(X) ≅ A`,
faithful flatness of `A⟨X⟩` over `A`, and quotient flatness results.

References: Wedhorn, Remark 8.29, Lemma 8.31.
-/

namespace TateAlgebra

variable {A : Type u} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-! #### The splitting: evalZeroHom ∘ algebraMap = id -/

/-- Evaluating the constant coefficient of `algebraMap a` gives back `a`. -/
theorem evalZeroHom_algebraMap (a : A) :
    evalZeroHom (algebraMap A ↥(TateAlgebra A) a) = a := by
  simp only [evalZeroHom, coeff, toIndex_zero]
  norm_cast

/-- The composition `evalZeroHom ∘ algebraMap` is the identity on `A`.
This means `algebraMap` is a section of `evalZeroHom`. -/
theorem evalZeroHom_comp_algebraMap :
    evalZeroHom.comp (algebraMap A ↥(TateAlgebra A)) = RingHom.id A := by
  ext a
  simp only [RingHom.comp_apply, RingHom.id_apply]
  exact evalZeroHom_algebraMap a

/-! #### The shift operation and kernel of evalZeroHom -/

/-- The "shift" of a univariate power series: `(shiftFun f)(s) = f(s + single 0 1)`.
This extracts the quotient `f / X` when `f(0) = 0`. -/
noncomputable def shiftFun (f : MvPowerSeries (Fin 1) A) : MvPowerSeries (Fin 1) A :=
  fun s ↦ f (s + Finsupp.single 0 1)

omit [NonarchimedeanRing A] in
/-- The shift of a restricted power series is restricted. The map `s ↦ s + single 0 1`
is injective, so composing with it preserves the cofinite-filter condition. -/
theorem shiftFun_isRestricted {f : MvPowerSeries (Fin 1) A}
    (hf : MvPowerSeries.IsRestricted f) : MvPowerSeries.IsRestricted (shiftFun f) := by
  change Tendsto _ cofinite (nhds 0)
  change Tendsto _ cofinite (nhds 0) at hf
  have inj : Function.Injective fun s : Fin 1 →₀ ℕ ↦ s + Finsupp.single 0 1 :=
    fun s t h ↦ by
      simp only [Finsupp.ext_iff, Finsupp.add_apply, Finsupp.single_apply] at h
      exact Finsupp.ext (fun i ↦ by have := h i; omega)
  exact hf.comp inj.tendsto_cofinite

/-- The shift as an element of `A⟨X⟩`: given `f ∈ A⟨X⟩`, `shift f` is the shifted
element, also in `A⟨X⟩`. -/
noncomputable def shift (f : ↥(TateAlgebra A)) : ↥(TateAlgebra A) :=
  ⟨shiftFun f.val, shiftFun_isRestricted f.prop⟩

omit [TopologicalSpace A] [NonarchimedeanRing A] in
private theorem mvps_coeff_eq (g : MvPowerSeries (Fin 1) A) (n : ℕ) :
    MvPowerSeries.coeff (toIndex n) g =
    MvPowerSeries.coeff (toIndex n) (MvPowerSeries.C (g 0)) +
    MvPowerSeries.coeff (toIndex n) (MvPowerSeries.X 0 * shiftFun g) := by
  induction n with
  | zero =>
    simp only [toIndex_zero]
    rw [MvPowerSeries.coeff_zero_C, MvPowerSeries.coeff_zero_X_mul, add_zero,
        MvPowerSeries.coeff_apply]
  | succ n =>
    rw [MvPowerSeries.coeff_C]
    rw [if_neg (show toIndex (n + 1) ≠ 0 from Finsupp.single_ne_zero.mpr (by omega))]
    rw [zero_add]
    rw [show (MvPowerSeries.X (R := A) (0 : Fin 1)) =
        MvPowerSeries.monomial (Finsupp.single 0 1) (1 : A) from rfl]
    rw [MvPowerSeries.coeff_monomial_mul]
    have hle : Finsupp.single (0 : Fin 1) 1 ≤ toIndex (n + 1) := by
      simp only [toIndex, Finsupp.single_le_iff, Finsupp.single_eq_same]; omega
    rw [if_pos hle, one_mul]
    simp only [shiftFun, toIndex, Finsupp.single_add, MvPowerSeries.coeff_apply]
    congr 1
    ext
    simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply]
    omega

omit [TopologicalSpace A] [NonarchimedeanRing A] in
private theorem mvps_eq_const_add_X_mul_shift (g : MvPowerSeries (Fin 1) A) :
    g = MvPowerSeries.C (g 0) + MvPowerSeries.X 0 * shiftFun g := by
  ext s
  rw [map_add, eq_toIndex s]
  exact mvps_coeff_eq g (s 0)

/-- Key identity: `f = const(f(0)) + X * shift(f)` as power series. -/
theorem eq_const_add_X_mul_shift (f : ↥(TateAlgebra A)) :
    f = algebraMap A _ (evalZeroHom f) + X * shift f := by
  ext n
  unfold coeff
  have hval : (algebraMap A ↥(TateAlgebra A) (evalZeroHom f) +
      X * shift f).val = (algebraMap A ↥(TateAlgebra A) (evalZeroHom f)).val +
      ((X : ↥(TateAlgebra A)).val * (shift f).val) := by
    rfl
  rw [hval]
  rw [map_add]
  have halg : (algebraMap A ↥(TateAlgebra A) (evalZeroHom f)).val =
      MvPowerSeries.C (σ := Fin 1) (f.val 0) := by
    change algebraMap A (MvPowerSeries (Fin 1) A) (evalZeroHom f) = _
    rw [MvPowerSeries.algebraMap_apply]
    simp only [evalZeroHom, coeff, toIndex_zero, MvPowerSeries.coeff_apply]; norm_cast
  rw [halg]
  exact mvps_coeff_eq f.val n

/-- An element of `A⟨X⟩` with zero constant term is divisible by `X`. -/
theorem mem_ideal_X_of_evalZeroHom_eq_zero {f : ↥(TateAlgebra A)}
    (hf : evalZeroHom f = 0) : f ∈ Ideal.span ({X} : Set ↥(TateAlgebra A)) := by
  have key : f = X * shift f := by
    have h := eq_const_add_X_mul_shift f
    rw [hf, map_zero, zero_add] at h
    exact h
  rw [key]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))

/-- The constant term of `X * g` is zero. -/
theorem evalZeroHom_X_mul (g : ↥(TateAlgebra A)) : evalZeroHom (X * g) = 0 := by
  simp only [evalZeroHom, coeff, toIndex_zero, map_mul, TateAlgebra.X]
  norm_num

/-- Every element of `Ideal.span {X}` has zero constant term. -/
theorem evalZeroHom_eq_zero_of_mem_ideal_X {f : ↥(TateAlgebra A)}
    (hf : f ∈ Ideal.span ({X} : Set ↥(TateAlgebra A))) : evalZeroHom f = 0 := by
  have hX : (X : ↥(TateAlgebra A)) ∈ RingHom.ker evalZeroHom := by
    rw [RingHom.mem_ker]
    simp only [evalZeroHom, coeff, toIndex_zero, TateAlgebra.X]
    norm_num
  exact RingHom.mem_ker.mp (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hX) hf)

/-- The kernel of `evalZeroHom` equals the ideal generated by `X`. -/
theorem ker_evalZeroHom :
    RingHom.ker evalZeroHom = Ideal.span ({X} : Set ↥(TateAlgebra A)) := by
  ext f
  constructor
  · intro hf
    exact mem_ideal_X_of_evalZeroHom_eq_zero (RingHom.mem_ker.mp hf)
  · intro hf
    exact RingHom.mem_ker.mpr (evalZeroHom_eq_zero_of_mem_ideal_X hf)

/-- The ideal generated by `X` in `A⟨X⟩`. -/
noncomputable def idealX : Ideal ↥(TateAlgebra A) :=
  Ideal.span {X}

/-! #### Coefficient arithmetic helpers -/

/-- Coefficient of a difference of power series. -/
theorem coeff_sub (f g : ↥(TateAlgebra A)) (n : ℕ) :
    coeff n (f - g) = coeff n f - coeff n g := by
  simp only [coeff]; exact map_sub _ _ _

/-- Coefficient of `algebraMap a * u`: the `algebraMap` acts as scalar multiplication. -/
theorem coeff_algebraMap_mul (a : A) (u : ↥(TateAlgebra A)) (n : ℕ) :
    coeff n (algebraMap A _ a * u) = a * coeff n u := by
  simp only [coeff, toIndex]
  change (MvPowerSeries.coeff (Finsupp.single 0 n))
    ((algebraMap A (MvPowerSeries (Fin 1) A) a) * u.val) = _
  rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C_mul]; rfl

/-- The `(n+1)`-th coefficient of `X * u` equals the `n`-th coefficient of `u`. -/
theorem coeff_succ_X_mul (u : ↥(TateAlgebra A)) (n : ℕ) :
    coeff (n + 1) (X * u) = coeff n u := by
  simp only [coeff, X, toIndex]
  change (MvPowerSeries.coeff (Finsupp.single 0 (n + 1)))
    (MvPowerSeries.X (0 : Fin 1) * u.val) = _
  rw [show (MvPowerSeries.X (R := A) (0 : Fin 1)) =
      MvPowerSeries.monomial (Finsupp.single 0 1) (1 : A) from rfl]
  rw [MvPowerSeries.coeff_monomial_mul,
    if_pos (show Finsupp.single (0 : Fin 1) 1 ≤ Finsupp.single 0 (n + 1) by
      simp only [Finsupp.single_le_iff, Finsupp.single_eq_same]; omega), one_mul]
  simp only [Finsupp.single_add, MvPowerSeries.coeff_apply, add_tsub_cancel_right]

/-- The constant coefficient of `X * u` is zero. -/
theorem coeff_zero_X_mul (u : ↥(TateAlgebra A)) :
    coeff 0 (X * u) = 0 := by
  have := evalZeroHom_X_mul u; simp only [evalZeroHom] at this; exact this

/-! #### Noetherian ascending chain lemma -/

omit [TopologicalSpace A] [NonarchimedeanRing A] in
/-- In a noetherian ring, if `a * x 0 = 0` and `x k = a * x (k + 1)` for all `k`,
then `x 0 = 0`. The proof uses the ascending chain of annihilator ideals
`{b | a^n * b = 0}` and its stabilization. -/
private theorem noeth_zero_of_mul_shift [IsNoetherianRing A] (a : A) (x : ℕ → A)
    (h0 : a * x 0 = 0) (hstep : ∀ k, x k = a * x (k + 1)) : x 0 = 0 := by
  have hpow : ∀ k, x 0 = a ^ k * x k := by
    intro k; induction k with
    | zero => simp only [pow_zero, one_mul]
    | succ k ih => rw [ih, hstep k, pow_succ, mul_assoc]
  have hann : ∀ k, a ^ (k + 1) * x k = 0 := by
    intro k
    have : a ^ (k + 1) * x k = a * (a ^ k * x k) := by ring
    rw [this, ← hpow k, h0]
  have chain_monotone : Monotone (fun n ↦ (⟨⟨⟨{b | a ^ n * b = 0},
    fun {x y} (hx : a ^ n * x = 0) (hy : a ^ n * y = 0) => by
      change a ^ n * (x + y) = 0; rw [mul_add, hx, hy, add_zero]⟩,
    by change a ^ n * 0 = 0; simp⟩,
    fun c {x} (hx : a ^ n * x = 0) => by
      change a ^ n * (c • x) = 0; rw [smul_eq_mul, mul_left_comm, hx, mul_zero]⟩
    : Submodule A A)) := by
    intro m n hmn b (hb : a ^ m * b = 0)
    change a ^ n * b = 0
    calc a ^ n * b = a ^ (n - m) * (a ^ m * b) := by
          rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hmn]
      _ = 0 := by rw [hb, mul_zero]
  let chain : ℕ →o Submodule A A := ⟨_, chain_monotone⟩
  obtain ⟨K, hK⟩ :=
    (monotone_stabilizes_iff_noetherian (R := A) (M := A)).mpr inferInstance chain
  have hxK_mem : x K ∈ chain (K + 1) := by
    change a ^ (K + 1) * x K = 0; exact hann K
  have hxK : a ^ K * x K = 0 :=
    (hK (K + 1) (by omega) ▸ hxK_mem : x K ∈ chain K)
  rw [hpow K, hxK]

/-! #### Faithful flatness of A⟨X⟩ over A (Lemma 8.31(1)) -/

/-- `PrimeSpectrum.comap (algebraMap A A⟨X⟩)` is surjective.
This follows because `evalZeroHom` provides a section: the composition
`algebraMap` then `evalZeroHom` is the identity, so `comap evalZeroHom`
is a right inverse of `comap algebraMap`. -/
theorem PrimeSpectrum_comap_algebraMap_surjective :
    Function.Surjective
      (PrimeSpectrum.comap (algebraMap A ↥(TateAlgebra A))) := by
  intro p
  refine ⟨PrimeSpectrum.comap evalZeroHom p, ?_⟩
  ext x
  simp only [PrimeSpectrum.comap, Ideal.mem_comap, evalZeroHom_algebraMap]

/-! #### Discrete-case equivalence: TateAlgebra A ≃ₗ[A] (Fin 1 →₀ ℕ) →₀ A

Under `[DiscreteTopology A]`, a power series is restricted iff it has finite support
(because `nhds 0 = pure 0`, so `Tendsto f cofinite (nhds 0)` means `f` is eventually 0).
This yields a linear equivalence with `(Fin 1 →₀ ℕ) →₀ A`, which is free hence flat. -/

omit [NonarchimedeanRing A] in
/-- Under discrete topology, `IsRestricted` is equivalent to having finite support:
the coefficient function `s ↦ coeff s f` is eventually zero along the cofinite filter. -/
theorem isRestricted_iff_finite_support [DiscreteTopology A]
    (f : MvPowerSeries (Fin 1) A) :
    MvPowerSeries.IsRestricted f ↔
      {s : Fin 1 →₀ ℕ | MvPowerSeries.coeff s f ≠ 0}.Finite := by
  unfold MvPowerSeries.IsRestricted
  rw [nhds_discrete, tendsto_pure, Filter.Eventually, Filter.mem_cofinite]
  constructor
  · intro h
    exact h.subset (fun s hs ↦ by simp only [Set.mem_compl_iff] at hs ⊢; exact hs)
  · intro h
    exact h.subset (fun s hs ↦ by simp only [Set.mem_compl_iff] at hs ⊢; exact hs)

omit [NonarchimedeanRing A] in
/-- A finitely supported function gives a restricted power series (discrete case). -/
theorem finsupp_isRestricted [DiscreteTopology A]
    (g : (Fin 1 →₀ ℕ) →₀ A) :
    MvPowerSeries.IsRestricted
      (fun s ↦ g s : MvPowerSeries (Fin 1) A) := by
  rw [isRestricted_iff_finite_support]
  apply g.support.finite_toSet.subset
  intro s hs
  simp only [Set.mem_setOf_eq, MvPowerSeries.coeff_apply] at hs
  exact Finsupp.mem_support_iff.mpr hs

/-- The forward map: `TateAlgebra A → (Fin 1 →₀ ℕ) →₀ A` sending a restricted power
series to the `Finsupp` of its coefficients (discrete case). -/
noncomputable def toFinsupp [DiscreteTopology A]
    (f : ↥(TateAlgebra A)) : (Fin 1 →₀ ℕ) →₀ A :=
  Finsupp.onFinset
    ((isRestricted_iff_finite_support f.val).mp f.prop).toFinset
    (fun s ↦ MvPowerSeries.coeff s f.val)
    (fun s hs ↦ by
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact hs)

/-- The backward map: `(Fin 1 →₀ ℕ) →₀ A → TateAlgebra A` (discrete case). -/
noncomputable def ofFinsupp [DiscreteTopology A]
    (g : (Fin 1 →₀ ℕ) →₀ A) : ↥(TateAlgebra A) :=
  ⟨fun s ↦ g s, finsupp_isRestricted g⟩

/-- The `A`-linear equivalence `TateAlgebra A ≃ₗ[A] (Fin 1 →₀ ℕ) →₀ A`
(discrete case). This exhibits `TateAlgebra A` as a free `A`-module. -/
noncomputable def linearEquivFinsupp [DiscreteTopology A] :
    ↥(TateAlgebra A) ≃ₗ[A] (Fin 1 →₀ ℕ) →₀ A where
  toFun f := toFinsupp f
  invFun g := ofFinsupp g
  left_inv f := by
    apply Subtype.ext
    apply MvPowerSeries.ext; intro s
    simp only [ofFinsupp, toFinsupp, Finsupp.onFinset_apply]
    rfl
  right_inv g := by
    ext s
    simp only [toFinsupp, ofFinsupp, Finsupp.onFinset_apply]
    rfl
  map_add' f g := by
    ext s
    simp only [toFinsupp, Finsupp.onFinset_apply, Finsupp.add_apply, Subring.coe_add, map_add]
  map_smul' a f := by
    ext s
    simp only [toFinsupp, Finsupp.onFinset_apply, Finsupp.smul_apply, RingHom.id_apply,
      smul_eq_mul, Algebra.smul_def]
    change MvPowerSeries.coeff s (algebraMap A _ a * f.val) = a * MvPowerSeries.coeff s f.val
    rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C_mul]
    rfl

/-! #### Ring equivalence with MvPolynomial (discrete case)

Under `[DiscreteTopology A]`, `TateAlgebra A` (restricted power series) consists of
power series with finitely many nonzero coefficients, which are exactly the polynomials.
We build a ring isomorphism `TateAlgebra A ≃+* MvPolynomial (Fin 1) A`. -/

/-- Convert an element of `TateAlgebra A` to `MvPolynomial (Fin 1) A` (discrete case).
This is `toFinsupp` with the correct type annotation for `MvPolynomial`. -/
noncomputable def toMvPolynomial [DiscreteTopology A]
    (f : ↥(TateAlgebra A)) : MvPolynomial (Fin 1) A :=
  .ofCoeff (toFinsupp f)

/-- Convert an `MvPolynomial (Fin 1) A` to `TateAlgebra A` (discrete case).
This is `ofFinsupp` with the correct type annotation for `MvPolynomial`. -/
noncomputable def fromMvPolynomial [DiscreteTopology A]
    (p : MvPolynomial (Fin 1) A) : ↥(TateAlgebra A) :=
  ofFinsupp (AddMonoidAlgebra.coeff p)

theorem fromMvPolynomial_toMvPolynomial [DiscreteTopology A] (f : ↥(TateAlgebra A)) :
    fromMvPolynomial (toMvPolynomial f) = f := by
  rw [fromMvPolynomial, toMvPolynomial, AddMonoidAlgebra.coeff_ofCoeff]
  exact (linearEquivFinsupp (A := A)).left_inv f

theorem toMvPolynomial_fromMvPolynomial [DiscreteTopology A] (p : MvPolynomial (Fin 1) A) :
    toMvPolynomial (fromMvPolynomial p) = p := by
  rw [toMvPolynomial, fromMvPolynomial,
    show toFinsupp (ofFinsupp (AddMonoidAlgebra.coeff p)) = AddMonoidAlgebra.coeff p from
      (linearEquivFinsupp (A := A)).right_inv (AddMonoidAlgebra.coeff p)]

/-- `fromMvPolynomial` preserves multiplication: it is the restriction of the
coercion `MvPolynomial → MvPowerSeries`, which is a ring homomorphism. -/
theorem fromMvPolynomial_mul [DiscreteTopology A] (p q : MvPolynomial (Fin 1) A) :
    fromMvPolynomial (p * q) = fromMvPolynomial p * fromMvPolynomial q := by
  apply Subtype.ext
  change (↑(p * q) : MvPowerSeries (Fin 1) A) =
    (↑p : MvPowerSeries (Fin 1) A) * (↑q : MvPowerSeries (Fin 1) A)
  exact (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin 1) (R := A)).map_mul p q

theorem fromMvPolynomial_one [DiscreteTopology A] :
    fromMvPolynomial (1 : MvPolynomial (Fin 1) A) = (1 : ↥(TateAlgebra A)) := by
  apply Subtype.ext
  change (↑(1 : MvPolynomial (Fin 1) A) : MvPowerSeries (Fin 1) A) = 1
  exact (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin 1) (R := A)).map_one

theorem toMvPolynomial_mul [DiscreteTopology A] (f g : ↥(TateAlgebra A)) :
    toMvPolynomial (f * g) = toMvPolynomial f * toMvPolynomial g := by
  apply_fun fromMvPolynomial using fun a b h ↦ by
    have := congr_arg toMvPolynomial h
    rwa [toMvPolynomial_fromMvPolynomial, toMvPolynomial_fromMvPolynomial] at this
  rw [fromMvPolynomial_mul, fromMvPolynomial_toMvPolynomial,
      fromMvPolynomial_toMvPolynomial, fromMvPolynomial_toMvPolynomial]

theorem toMvPolynomial_add [DiscreteTopology A] (f g : ↥(TateAlgebra A)) :
    toMvPolynomial (f + g) = toMvPolynomial f + toMvPolynomial g := by
  rw [toMvPolynomial, toMvPolynomial, toMvPolynomial,
    show toFinsupp (f + g) = toFinsupp f + toFinsupp g from
      (linearEquivFinsupp (A := A)).map_add' f g]
  rfl

/-- The ring equivalence `TateAlgebra A ≃+* MvPolynomial (Fin 1) A` (discrete case).
Under `[DiscreteTopology A]`, the restricted power series ring coincides with the
polynomial ring, and this isomorphism respects both the additive and multiplicative
structure. -/
noncomputable def ringEquivMvPolynomial [DiscreteTopology A] :
    ↥(TateAlgebra A) ≃+* MvPolynomial (Fin 1) A where
  toFun := toMvPolynomial
  invFun := fromMvPolynomial
  left_inv := fromMvPolynomial_toMvPolynomial
  right_inv := toMvPolynomial_fromMvPolynomial
  map_mul' := toMvPolynomial_mul
  map_add' := toMvPolynomial_add

/-! #### Evaluation at f (discrete case)

Under `[DiscreteTopology A]`, the evaluation map `A⟨X⟩ → A` sending `X ↦ f`
is a well-defined ring homomorphism, since elements have finite support. -/

/-- Evaluation of `TateAlgebra A` at `f : A`, defined as the composition
`TateAlgebra A ≃+* MvPolynomial (Fin 1) A →[eval] A` (discrete case). -/
noncomputable def evalFHom [DiscreteTopology A] (f : A) : ↥(TateAlgebra A) →+* A :=
  (MvPolynomial.eval (fun _ ↦ f)).comp ringEquivMvPolynomial.toRingHom

theorem ringEquivMvPolynomial_algebraMap [DiscreteTopology A] (a : A) :
    ringEquivMvPolynomial (algebraMap A (↥(TateAlgebra A)) a) = MvPolynomial.C a := by
  ext s
  simp only [ringEquivMvPolynomial, MvPolynomial.C_apply]
  change MvPowerSeries.coeff s (algebraMap A (MvPowerSeries (Fin 1) A) a) = _
  rw [MvPowerSeries.algebraMap_apply]
  simp only [MvPowerSeries.coeff_C, MvPolynomial.coeff_monomial, eq_comm]; norm_cast

theorem ringEquivMvPolynomial_X [DiscreteTopology A] :
    ringEquivMvPolynomial (X : ↥(TateAlgebra A)) = MvPolynomial.X (0 : Fin 1) := by
  suffices h : ∀ s, MvPolynomial.coeff s (ringEquivMvPolynomial (X : ↥(TateAlgebra A))) =
      MvPolynomial.coeff s (MvPolynomial.X (0 : Fin 1)) by
    ext s; exact h s
  intro s
  show MvPolynomial.coeff s (toMvPolynomial (X : ↥(TateAlgebra A))) = _
  rw [toMvPolynomial, MvPolynomial.coeff, AddMonoidAlgebra.coeff_ofCoeff]
  simp only [toFinsupp, Finsupp.onFinset_apply]
  change MvPowerSeries.coeff s (MvPowerSeries.X (0 : Fin 1)) = _
  rw [MvPowerSeries.coeff_X]
  rw [MvPolynomial.coeff_X]
  simp only [eq_comm]

theorem evalFHom_algebraMap [DiscreteTopology A] (f a : A) :
    evalFHom f (algebraMap A _ a) = a := by
  simp only [evalFHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [ringEquivMvPolynomial_algebraMap, MvPolynomial.eval_C]

theorem evalFHom_X [DiscreteTopology A] (f : A) :
    evalFHom f X = f := by
  simp only [evalFHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [ringEquivMvPolynomial_X, MvPolynomial.eval_X]

theorem evalFHom_surjective [DiscreteTopology A] (f : A) :
    Function.Surjective (evalFHom f) := by
  intro a
  exact ⟨algebraMap A _ a, evalFHom_algebraMap f a⟩

theorem evalFHom_fSubX [DiscreteTopology A] (f : A) :
    evalFHom f (algebraMap A _ f - X) = 0 := by
  rw [map_sub, evalFHom_algebraMap, evalFHom_X, sub_self]

/-- `A⟨X⟩` is flat over `A` (Lemma 8.31(1), flatness part, discrete case).

Under `[DiscreteTopology A]`, `A⟨X⟩ ≃ₗ[A] (Fin 1 →₀ ℕ) →₀ A`, which is free
(hence flat) as an `A`-module. -/
instance flat [DiscreteTopology A] : Module.Flat A ↥(TateAlgebra A) :=
  Module.Flat.of_linearEquiv (linearEquivFinsupp (A := A))

/-- `A⟨X⟩` is faithfully flat over `A` (Lemma 8.31(1), discrete case).
Faithful flatness follows from flatness + surjectivity on spectra. -/
instance faithfullyFlat [DiscreteTopology A] : Module.FaithfullyFlat A ↥(TateAlgebra A) :=
  Module.FaithfullyFlat.of_comap_surjective PrimeSpectrum_comap_algebraMap_surjective

/-! #### Quotient flatness via isomorphisms (Lemma 8.31(2), discrete case)

Under `[DiscreteTopology A]`, we prove flatness of the quotients `A⟨X⟩/(f-X)` and
`A⟨X⟩/(1-fX)` directly by constructing isomorphisms:
- `A⟨X⟩/(f-X) ≅ A` via evaluation at `f` (factor theorem)
- `A⟨X⟩/(1-fX) ≅ Localization.Away f` (localization is flat)

**Note:** The general statement "if `g` is a non-zero-divisor in `B` and `B` is flat over `A`,
then `B/(g)` is flat over `A`" is FALSE (counterexample: `g = 2` in `Z[X]`, quotient
`(Z/2Z)[X]` is not flat over `Z`). The correct general statement requires *universal*
regularity: `g·` injective on `M ⊗_A B` for all finitely generated `A`-modules `M`.
For the specific elements `f-X` and `1-fX`, this universal regularity holds,
but we avoid it by using explicit isomorphisms instead. -/

/-- The ideal `Ideal.span {algebraMap f - X}` is contained in `ker evalFHom`.
This is the easy direction of the kernel computation. -/
theorem ideal_fSubX_le_ker_evalFHom [DiscreteTopology A] (f : A) :
    Ideal.span {algebraMap A ↥(TateAlgebra A) f - X} ≤ RingHom.ker (evalFHom f) := by
  rw [Ideal.span_le]
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  simp only [SetLike.mem_coe, RingHom.mem_ker, hx, evalFHom_fSubX]

/-- The factor theorem for `TateAlgebra A` (discrete case): for every element `p`,
`p - algebraMap(evalFHom f p) ∈ Ideal.span {algebraMap f - X}`.

Proof by induction on an upper bound for the coefficient indices, using
the recursive decomposition `p = algebraMap(coeff 0 p) + X * shift(p)`. -/
theorem sub_algebraMap_evalFHom_mem_ideal_fSubX [DiscreteTopology A] (f : A)
    (p : ↥(TateAlgebra A)) :
    p - algebraMap A _ (evalFHom f p) ∈
      Ideal.span {algebraMap A ↥(TateAlgebra A) f - X} := by
  have coeff_shift : ∀ (q : ↥(TateAlgebra A)) (k : ℕ),
      coeff k (shift q) = coeff (k + 1) q := by
    intro q k
    change MvPowerSeries.coeff (Finsupp.single 0 k) (shiftFun q.val) =
      MvPowerSeries.coeff (Finsupp.single 0 (k + 1)) q.val
    simp only [shiftFun, MvPowerSeries.coeff_apply, Finsupp.single_add]
  have eval_decomp : ∀ (q : ↥(TateAlgebra A)),
      evalFHom f q = coeff 0 q + f * evalFHom f (shift q) := by
    intro q
    have hd := eq_const_add_X_mul_shift q
    calc evalFHom f q
        = evalFHom f (algebraMap A _ (evalZeroHom q) + X * shift q) := by rw [← hd]
      _ = evalFHom f (algebraMap A _ (evalZeroHom q)) +
          evalFHom f X * evalFHom f (shift q) := by rw [map_add, map_mul]
      _ = coeff 0 q + f * evalFHom f (shift q) := by
          rw [evalFHom_algebraMap, evalFHom_X]; rfl
  have eval_zero_eq : ∀ (q : ↥(TateAlgebra A)), evalZeroHom q = coeff 0 q := fun _ ↦ rfl
  have key_identity : ∀ (q : ↥(TateAlgebra A)),
      q - algebraMap A _ (evalFHom f q) =
      X * (shift q - algebraMap A _ (evalFHom f (shift q))) +
      (X - algebraMap A _ f) * algebraMap A _ (evalFHom f (shift q)) := by
    intro q
    rw [eval_decomp q]
    nth_rw 1 [eq_const_add_X_mul_shift q]
    rw [map_add, map_mul, eval_zero_eq]; ring
  have hmain : ∀ (n : ℕ) (q : ↥(TateAlgebra A)),
      (∀ k, n < k → coeff k q = 0) →
      q - algebraMap A _ (evalFHom f q) ∈
        Ideal.span {algebraMap A ↥(TateAlgebra A) f - X} := by
    intro n; induction n with
    | zero =>
      intro q hq
      have hshift_zero : shift q = 0 := by
        apply ext; intro k
        rw [coeff_shift, hq (k + 1) (Nat.succ_pos k)]
        simp only [coeff, map_zero, ZeroMemClass.coe_zero]
      have hev : evalFHom f q = coeff 0 q := by
        rw [eval_decomp, hshift_zero, map_zero, mul_zero, add_zero]
      have hq0 : q = algebraMap A _ (coeff 0 q) := by
        have := eq_const_add_X_mul_shift q
        rw [hshift_zero, mul_zero, add_zero, eval_zero_eq] at this
        exact this
      have h1 : algebraMap A _ (evalFHom f q) = q := by
        rw [hev]; exact hq0.symm
      rw [h1, sub_self]
      exact Ideal.zero_mem _
    | succ n ih =>
      intro q hq
      rw [key_identity]
      apply Ideal.add_mem
      · apply Ideal.mul_mem_left
        exact ih (shift q) (fun k hk ↦ by rw [coeff_shift]; exact hq _ (by omega))
      · apply Ideal.mul_mem_right
        have hmem : (X : ↥(TateAlgebra A)) - algebraMap A ↥(TateAlgebra A) f =
            -(algebraMap A ↥(TateAlgebra A) f - X) := by ring
        rw [hmem]
        exact neg_mem (Ideal.subset_span rfl)
  have hfin : Set.Finite {s : Fin 1 →₀ ℕ | p.val s ≠ 0} :=
    (isRestricted_iff_finite_support p.val).mp p.prop
  by_cases hp : ∀ k, coeff k p = 0
  · rw [(ext hp : p = 0), map_zero, map_zero, sub_self]; exact Ideal.zero_mem _
  · push Not at hp
    have hne : hfin.toFinset.Nonempty := by
      obtain ⟨k, hk⟩ := hp
      refine ⟨toIndex k, ?_⟩
      rw [Set.Finite.mem_toFinset]
      simp only [Set.mem_setOf_eq, coeff, toIndex] at hk ⊢
      exact hk
    refine hmain (hfin.toFinset.sup' hne (fun s ↦ s 0)) p (fun k hk ↦ ?_)
    by_contra hne2
    have hmem : toIndex k ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      simp only [Set.mem_setOf_eq, coeff, toIndex] at hne2 ⊢
      exact hne2
    have hle := Finset.le_sup' (fun s : Fin 1 →₀ ℕ ↦ s 0) hmem
    simp only [toIndex, Finsupp.single_apply, ite_true] at hle
    omega

/-- The quotient ring hom from `TateAlgebra A ⧸ (f-X)` to `A`. -/
noncomputable def quotientFSubXToA [DiscreteTopology A] (f : A) :
    (↥(TateAlgebra A) ⧸ Ideal.span {algebraMap A ↥(TateAlgebra A) f - X}) →+* A :=
  Ideal.Quotient.lift _ (evalFHom f) (fun x hx ↦ by
    exact ideal_fSubX_le_ker_evalFHom f hx)

/-- The ring hom from `A` to `TateAlgebra A ⧸ (f-X)`. -/
noncomputable def AToQuotientFSubX [DiscreteTopology A] (f : A) :
    A →+* (↥(TateAlgebra A) ⧸ Ideal.span {algebraMap A ↥(TateAlgebra A) f - X}) :=
  (Ideal.Quotient.mk _).comp (algebraMap A _)

theorem quotientFSubXToA_comp_AToQuotientFSubX [DiscreteTopology A] (f : A) :
    (quotientFSubXToA f).comp (AToQuotientFSubX f) = RingHom.id A := by
  ext a
  simp only [RingHom.comp_apply, AToQuotientFSubX,
    quotientFSubXToA, Ideal.Quotient.lift_mk, evalFHom_algebraMap, RingHom.id_apply]

theorem AToQuotientFSubX_comp_quotientFSubXToA [DiscreteTopology A] (f : A) :
    (AToQuotientFSubX f).comp (quotientFSubXToA f) = RingHom.id _ := by
  rw [← RingHom.cancel_right (Ideal.Quotient.mk_surjective)]
  ext p
  simp only [RingHom.comp_apply, RingHom.id_apply, AToQuotientFSubX,
    quotientFSubXToA, Ideal.Quotient.lift_mk]
  symm
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact sub_algebraMap_evalFHom_mem_ideal_fSubX f p

/-- The isomorphism `TateAlgebra A ⧸ (f - X) ≃+* A` (discrete case). -/
noncomputable def quotientFSubXEquiv [DiscreteTopology A] (f : A) :
    (↥(TateAlgebra A) ⧸ Ideal.span {algebraMap A ↥(TateAlgebra A) f - X}) ≃+* A where
  toFun := quotientFSubXToA f
  invFun := AToQuotientFSubX f
  left_inv x := by
    have h := congr_fun (congr_arg DFunLike.coe
      (AToQuotientFSubX_comp_quotientFSubXToA f)) x
    simp only [RingHom.comp_apply, RingHom.id_apply] at h
    exact h
  right_inv a := by
    have h := congr_fun (congr_arg DFunLike.coe
      (quotientFSubXToA_comp_AToQuotientFSubX f)) a
    simp only [RingHom.comp_apply, RingHom.id_apply] at h
    exact h
  map_mul' := map_mul _
  map_add' := map_add _

/-- Multiplication by `f - X` is injective on `A⟨X⟩` when `A` is noetherian.

The coefficient equations from `(f - X) * u = 0` give `f * coeff n u = coeff n (X * u)`,
which yields `f * coeff 0 u = 0` and `coeff n u = f * coeff (n + 1) u`. The noetherian
ascending chain argument on annihilator ideals forces all coefficients to vanish. -/
theorem mul_fSubX_regular [IsNoetherianRing A] (f : A) :
    ∀ (x : ↥(TateAlgebra A)),
      (algebraMap A _ f - X) * x = 0 → x = 0 := by
  intro u hu
  have hcoeff : ∀ n, f * coeff n u = coeff n (X * u) := by
    intro n
    have h1 : coeff n ((algebraMap A _ f - X) * u) = 0 := by
      rw [hu]; simp only [coeff, map_zero, ZeroMemClass.coe_zero]
    rw [sub_mul, coeff_sub, coeff_algebraMap_mul] at h1
    exact sub_eq_zero.mp h1
  have h0 : f * coeff 0 u = 0 := by rw [hcoeff 0, coeff_zero_X_mul]
  have hstep : ∀ n, coeff n u = f * coeff (n + 1) u := by
    intro n; have h := hcoeff (n + 1); rw [coeff_succ_X_mul] at h; exact h.symm
  have hall : ∀ n, coeff n u = 0 := by
    intro n; induction n using Nat.strongRecOn with
    | ind n ih =>
      refine noeth_zero_of_mul_shift f (fun k ↦ coeff (n + k) u) ?_ (fun k ↦ hstep (n + k))
      simp only [Nat.add_zero]
      cases n with
      | zero => exact h0
      | succ m =>
        have hm : coeff m u = 0 := ih m (by omega)
        rw [← hstep m, hm]
  exact ext hall

/-- Multiplication by `1 - f·X` is injective on `A⟨X⟩` when `A` is noetherian.

The coefficient equations from `(1 - fX) * u = 0` give `coeff n u = f * coeff n (X * u)`,
which yields `coeff 0 u = 0` and `coeff (n+1) u = f * coeff n u`. By induction,
all coefficients vanish (no noetherian argument needed in this case). -/
theorem mul_oneSubfX_regular [IsNoetherianRing A] (f : A) :
    ∀ (x : ↥(TateAlgebra A)),
      (1 - algebraMap A _ f * X) * x = 0 → x = 0 := by
  intro u hu
  have hcoeff : ∀ n, coeff n u = f * coeff n (X * u) := by
    intro n
    have h1 : coeff n ((1 - algebraMap A _ f * X) * u) = 0 := by
      rw [hu]; simp only [coeff, map_zero, ZeroMemClass.coe_zero]
    rw [sub_mul, one_mul, mul_assoc, coeff_sub, coeff_algebraMap_mul] at h1
    exact sub_eq_zero.mp h1
  have h0 : coeff 0 u = 0 := by rw [hcoeff 0, coeff_zero_X_mul, mul_zero]
  have hstep : ∀ n, coeff (n + 1) u = f * coeff n u := by
    intro n; rw [hcoeff (n + 1), coeff_succ_X_mul]
  have hall : ∀ n, coeff n u = 0 := by
    intro n; induction n with
    | zero => exact h0
    | succ n ih => rw [hstep n, ih, mul_zero]
  exact ext hall

/-- `A⟨X⟩/(f - X)` is flat over a noetherian `A` (Lemma 8.31(2), first case).
Under discrete topology, `A⟨X⟩/(f-X) ≅ A` via evaluation at `f`, and `A` is flat
over itself. Identifies with `O_X(R(f/1))` in the presheaf. -/
theorem flat_quotient_fSubX [DiscreteTopology A] [IsNoetherianRing A] (f : A) :
    Module.Flat A (↥(TateAlgebra A) ⧸ Ideal.span {algebraMap A ↥(TateAlgebra A) f - X}) := by
  let e := quotientFSubXEquiv f
  have hsmul : ∀ (a : A)
      (x : ↥(TateAlgebra A) ⧸ Ideal.span {algebraMap A ↥(TateAlgebra A) f - X}),
      e (a • x) = a • e x := by
    intro a x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    have h := congr_fun (congr_arg DFunLike.coe (quotientFSubXToA_comp_AToQuotientFSubX f)) a
    simp only [RingHom.comp_apply, RingHom.id_apply] at h
    convert h using 1 <;> first | rfl | simp
  exact Module.Flat.of_linearEquiv
    { e.toAddEquiv with
      map_smul' := hsmul }

/-! #### Evaluation at `f⁻¹` in `Localization.Away f` (discrete case)

Under `[DiscreteTopology A]`, we build a ring homomorphism
`TateAlgebra A → Localization.Away f` by evaluating at `IsLocalization.Away.invSelf f`.
This factors through the quotient by `(1 - fX)` and yields an isomorphism
`A⟨X⟩/(1-fX) ≃+* Localization.Away f`. -/

/-- Evaluation of `TateAlgebra A` at `IsLocalization.Away.invSelf f` in `Localization.Away f`.
Defined as `MvPolynomial.eval (fun _ => invSelf f)` composed with `ringEquivMvPolynomial`. -/
noncomputable def evalInvFHom [DiscreteTopology A] (f : A) :
    ↥(TateAlgebra A) →+* Localization.Away f :=
  ((MvPolynomial.aeval (R := A) (fun (_ : Fin 1) ↦
    IsLocalization.Away.invSelf (S := Localization.Away f) f)).toRingHom).comp
    ringEquivMvPolynomial.toRingHom

theorem evalInvFHom_algebraMap [DiscreteTopology A] (f a : A) :
    evalInvFHom f (algebraMap A _ a) =
      algebraMap A (Localization.Away f) a := by
  simp only [evalInvFHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    ringEquivMvPolynomial_algebraMap,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C]

theorem evalInvFHom_X [DiscreteTopology A] (f : A) :
    evalInvFHom f X =
      IsLocalization.Away.invSelf (S := Localization.Away f) f := by
  simp only [evalInvFHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    ringEquivMvPolynomial_X,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]

theorem evalInvFHom_oneSubfX [DiscreteTopology A] (f : A) :
    evalInvFHom f (1 - algebraMap A _ f * X) = 0 := by
  rw [map_sub, map_one, map_mul, evalInvFHom_algebraMap, evalInvFHom_X,
    IsLocalization.Away.mul_invSelf, sub_self]

/-- The ideal `(1 - fX)` is contained in the kernel of `evalInvFHom`. -/
theorem ideal_oneSubfX_le_ker_evalInvFHom [DiscreteTopology A] (f : A) :
    Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * X} ≤
      RingHom.ker (evalInvFHom f) := by
  rw [Ideal.span_le]
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  simp only [SetLike.mem_coe, RingHom.mem_ker, hx, evalInvFHom_oneSubfX]

/-- The quotient ring hom from `TateAlgebra A ⧸ (1-fX)` to `Localization.Away f`. -/
noncomputable def quotientOneSubfXToLoc [DiscreteTopology A] (f : A) :
    (↥(TateAlgebra A) ⧸ Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * X}) →+*
      Localization.Away f :=
  Ideal.Quotient.lift _ (evalInvFHom f) (fun _ hx ↦
    ideal_oneSubfX_le_ker_evalInvFHom f hx)

/-- The image of `algebraMap f` is a unit in `TateAlgebra A ⧸ (1-fX)`, with inverse
equal to the image of `X`. -/
theorem isUnit_algebraMap_f_in_quotient [DiscreteTopology A] (f : A) :
    IsUnit (((Ideal.Quotient.mk
      (Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * X})).comp
        (algebraMap A _)) f) := by
  rw [RingHom.comp_apply, isUnit_iff_exists_inv]
  refine ⟨(Ideal.Quotient.mk _) X, ?_⟩
  rw [← map_mul]
  have : (Ideal.Quotient.mk (Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * X}))
      (algebraMap A ↥(TateAlgebra A) f * X) = 1 := by
    rw [← sub_eq_zero]
    change (Ideal.Quotient.mk _) (algebraMap A ↥(TateAlgebra A) f * X) -
      (Ideal.Quotient.mk _) 1 = 0
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by
      rw [show algebraMap A ↥(TateAlgebra A) f * X - 1 =
        -(1 - algebraMap A ↥(TateAlgebra A) f * X) from by ring]
      exact neg_mem (Ideal.subset_span rfl))
  exact this

/-- The ring hom from `Localization.Away f` to `TateAlgebra A ⧸ (1-fX)`. -/
noncomputable def locToQuotientOneSubfX [DiscreteTopology A] (f : A) :
    Localization.Away f →+*
      (↥(TateAlgebra A) ⧸ Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * X}) :=
  IsLocalization.Away.lift (x := f)
    (g := (Ideal.Quotient.mk _).comp (algebraMap A _))
    (isUnit_algebraMap_f_in_quotient f)

theorem locToQuotientOneSubfX_algebraMap [DiscreteTopology A] (f a : A) :
    locToQuotientOneSubfX f (algebraMap A _ a) =
      (Ideal.Quotient.mk _) (algebraMap A _ a) := by
  simp only [locToQuotientOneSubfX]
  rw [IsLocalization.Away.lift_eq]
  rfl

theorem quotientOneSubfXToLoc_comp_locToQuotientOneSubfX [DiscreteTopology A] (f : A) :
    (quotientOneSubfXToLoc f).comp (locToQuotientOneSubfX f) =
      RingHom.id (Localization.Away f) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext a
  simp only [RingHom.comp_apply, RingHom.id_apply]
  rw [locToQuotientOneSubfX_algebraMap]
  simp only [quotientOneSubfXToLoc, Ideal.Quotient.lift_mk, evalInvFHom_algebraMap]

/-- Every element `p` of `TateAlgebra A` satisfies
`p - algebraMap(evalInvFHom f p) ∈ Ideal.span {1 - fX}` in the appropriate sense:
`mk(p) = locToQuotientOneSubfX(evalInvFHom f p)`.

The proof uses induction on the polynomial degree. In the quotient, since `fX = 1`,
we have `X = f⁻¹` and every polynomial `∑ aₙXⁿ` evaluates to `∑ aₙ/fⁿ`.
The key identity is `p = algebraMap(coeff 0 p) + X * shift(p)`, and in the quotient,
`X = algebraMap(f)⁻¹` (via the ideal relation `fX = 1`). -/
theorem locToQuotientOneSubfX_comp_quotientOneSubfXToLoc [DiscreteTopology A] (f : A) :
    (locToQuotientOneSubfX f).comp (quotientOneSubfXToLoc f) =
      RingHom.id _ := by
  rw [← RingHom.cancel_right (Ideal.Quotient.mk_surjective)]
  ext p
  simp only [RingHom.comp_apply, RingHom.id_apply, quotientOneSubfXToLoc,
    Ideal.Quotient.lift_mk]
  have loc_alg : ∀ (a : A),
      locToQuotientOneSubfX f (algebraMap A _ a) =
        (Ideal.Quotient.mk _) (algebraMap A _ a) :=
    locToQuotientOneSubfX_algebraMap f
  have loc_inv : locToQuotientOneSubfX f
      (IsLocalization.Away.invSelf (S := Localization.Away f) f) =
      (Ideal.Quotient.mk _) X := by
    set I := Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * X} with hI_def
    have hfX : (Ideal.Quotient.mk I)
        (algebraMap A (↥(TateAlgebra A)) f * X) = 1 := by
      rw [← sub_eq_zero]
      change (Ideal.Quotient.mk I) (algebraMap A _ f * X) -
        (Ideal.Quotient.mk I) 1 = 0
      rw [← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (by
        rw [show algebraMap A ↥(TateAlgebra A) f * X - 1 =
          -(1 - algebraMap A ↥(TateAlgebra A) f * X) from by ring]
        exact neg_mem (Ideal.subset_span rfl))
    have hunit : IsUnit ((Ideal.Quotient.mk I) (algebraMap A _ f)) := by
      rw [isUnit_iff_exists_inv]
      exact ⟨(Ideal.Quotient.mk I) X, by rw [← map_mul]; exact hfX⟩
    have h1 : (Ideal.Quotient.mk I) (algebraMap A (↥(TateAlgebra A)) f) *
        locToQuotientOneSubfX f
          (IsLocalization.Away.invSelf (S := Localization.Away f) f) = 1 := by
      rw [← loc_alg, ← map_mul,
        IsLocalization.Away.mul_invSelf, map_one]
    have h2 : (Ideal.Quotient.mk I) (algebraMap A (↥(TateAlgebra A)) f) *
        (Ideal.Quotient.mk I) X = 1 := by
      rw [← map_mul]; exact hfX
    exact hunit.mul_left_cancel (h1.trans h2.symm)
  have coeff_shift : ∀ (q : ↥(TateAlgebra A)) (k : ℕ),
      coeff k (shift q) = coeff (k + 1) q := by
    intro q k
    change MvPowerSeries.coeff (Finsupp.single 0 k) (shiftFun q.val) =
      MvPowerSeries.coeff (Finsupp.single 0 (k + 1)) q.val
    simp only [shiftFun, MvPowerSeries.coeff_apply, Finsupp.single_add]
  have eval_zero_eq : ∀ (q : ↥(TateAlgebra A)), evalZeroHom q = coeff 0 q := fun _ ↦ rfl
  have hmain : ∀ (n : ℕ) (q : ↥(TateAlgebra A)),
      (∀ k, n < k → coeff k q = 0) →
      locToQuotientOneSubfX f (evalInvFHom f q) =
        (Ideal.Quotient.mk _) q := by
    intro n; induction n with
    | zero =>
      intro q hq
      have hshift_zero : shift q = 0 := by
        apply ext; intro k
        rw [coeff_shift, hq (k + 1) (Nat.succ_pos k)]
        simp only [coeff, map_zero, ZeroMemClass.coe_zero]
      have hq0 : q = algebraMap A _ (evalZeroHom q) := by
        have := eq_const_add_X_mul_shift q
        rw [hshift_zero, mul_zero, add_zero] at this
        exact this
      rw [hq0, evalInvFHom_algebraMap, loc_alg]
    | succ n ih =>
      intro q hq
      have hdecomp := eq_const_add_X_mul_shift q
      conv_rhs => rw [hdecomp]
      rw [map_add, map_mul]
      have hev : evalInvFHom f q =
          evalInvFHom f (algebraMap A _ (evalZeroHom q)) +
          evalInvFHom f X * evalInvFHom f (shift q) := by
        conv_lhs => rw [hdecomp]
        rw [map_add, map_mul]
      rw [hev, map_add, map_mul, evalInvFHom_algebraMap, loc_alg,
        evalInvFHom_X, loc_inv]
      congr 1
      congr 1
      exact ih (shift q) (fun k hk ↦ by rw [coeff_shift]; exact hq _ (by omega))
  have hfin : Set.Finite {s : Fin 1 →₀ ℕ | p.val s ≠ 0} :=
    (isRestricted_iff_finite_support p.val).mp p.prop
  by_cases hp : ∀ k, coeff k p = 0
  · rw [(ext hp : p = 0), map_zero, map_zero, map_zero]
  · push Not at hp
    have hne : hfin.toFinset.Nonempty := by
      obtain ⟨k, hk⟩ := hp
      refine ⟨toIndex k, ?_⟩
      rw [Set.Finite.mem_toFinset]
      simp only [Set.mem_setOf_eq, coeff, toIndex] at hk ⊢
      exact hk
    exact hmain (hfin.toFinset.sup' hne (fun s ↦ s 0)) p (fun k hk ↦ by
      by_contra hne2
      have hmem : toIndex k ∈ hfin.toFinset := by
        rw [Set.Finite.mem_toFinset]
        simp only [Set.mem_setOf_eq, coeff, toIndex] at hne2 ⊢
        exact hne2
      have hle := Finset.le_sup' (fun s : Fin 1 →₀ ℕ ↦ s 0) hmem
      simp only [toIndex, Finsupp.single_apply, ite_true] at hle
      omega)

/-- The ring equivalence `TateAlgebra A ⧸ (1-fX) ≃+* Localization.Away f` (discrete case). -/
noncomputable def quotientOneSubfXEquiv [DiscreteTopology A] (f : A) :
    (↥(TateAlgebra A) ⧸ Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * X}) ≃+*
      Localization.Away f where
  toFun := quotientOneSubfXToLoc f
  invFun := locToQuotientOneSubfX f
  left_inv x := by
    have h := congr_fun (congr_arg DFunLike.coe
      (locToQuotientOneSubfX_comp_quotientOneSubfXToLoc f)) x
    simp only [RingHom.comp_apply, RingHom.id_apply] at h
    exact h
  right_inv s := by
    have h := congr_fun (congr_arg DFunLike.coe
      (quotientOneSubfXToLoc_comp_locToQuotientOneSubfX f)) s
    simp only [RingHom.comp_apply, RingHom.id_apply] at h
    exact h
  map_mul' := map_mul _
  map_add' := map_add _

/-- `A⟨X⟩/(1 - f·X)` is flat over a noetherian `A` (Lemma 8.31(2), second case).
Under discrete topology, `A⟨X⟩/(1-fX) ≅ Localization.Away f` via the universal
property of localization, and localization is flat.
Identifies with `O_X(R(1/f))` in the presheaf. -/
theorem flat_quotient_oneSubfX [DiscreteTopology A] [IsNoetherianRing A] (f : A) :
    Module.Flat A
      (↥(TateAlgebra A) ⧸ Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * X}) := by
  let e := quotientOneSubfXEquiv f
  have hsmul : ∀ (a : A)
      (x : ↥(TateAlgebra A) ⧸ Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * X}),
      e (a • x) = a • e x := by
    intro a x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    change quotientOneSubfXToLoc f ((Ideal.Quotient.mk _) (algebraMap A _ a)) = algebraMap A _ a
    simp only [quotientOneSubfXToLoc, Ideal.Quotient.lift_mk, evalInvFHom_algebraMap]
  have : Module.Flat A (Localization.Away f) := IsLocalization.flat _ (Submonoid.powers f)
  exact Module.Flat.of_linearEquiv
    { e.toAddEquiv with
      map_smul' := hsmul }

end TateAlgebra

/-! ### Chase's theorem and general flatness (Lemma 8.31, no DiscreteTopology)

Over a noetherian commutative ring, arbitrary products of copies of the ring are flat.
This is a special case of Chase's theorem. We use this to prove flatness of the
full power series ring `MvPowerSeries σ A` and then of the Tate algebra `A⟨X⟩`
over noetherian `A` (Lemma 8.31(1) of Wedhorn, general case).

References: [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 8.31
-/

section ChaseFlatness

/-- An element of `span(range s)` can be written as `∑ c(j) • s(j)` for some `c : Fin k → R`.
This extracts `Finsupp` coefficients into a plain function. -/
private lemma mem_span_range_iff_exists_fin {R : Type u} [CommRing R] {M : Type u}
    [AddCommGroup M] [Module R M] {k : ℕ} {s : Fin k → M} {x : M} :
    x ∈ Submodule.span R (Set.range s) ↔
      ∃ c : Fin k → R, x = ∑ j, c j • s j := by
  constructor
  · intro hx
    obtain ⟨cf, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
    refine ⟨cf, ?_⟩
    rw [← hcf, Finsupp.sum, Finset.sum_subset (s₂ := Finset.univ) (Finset.subset_univ _)]
    intro j _ hj; rw [Finsupp.notMem_support_iff] at hj; simp [hj]
  · intro ⟨c, hc⟩; rw [hc]
    exact Submodule.sum_mem _
      (fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

/-- The relation map for syzygies: sends `r` to `∑ f(i) * r(i)`. -/
private noncomputable def relMapFlat {R : Type u} [CommRing R] {l : ℕ}
    (f : Fin l → R) : (Fin l → R) →ₗ[R] R where
  toFun r := ∑ i, f i * r i
  map_add' r s := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a r := by simp [smul_eq_mul, mul_left_comm, Finset.mul_sum]

/-- **Chase's theorem (special case):** Products of copies of `R` are flat over
noetherian `R`.

The proof uses the equational criterion for flatness. Given a relation
`∑ f(i) • x(i) = 0` where `x(i) : ι → R`, for each coordinate `n ∈ ι` the tuple
`(x(0)(n), …, x(l-1)(n))` is a syzygy of `(f(0), …, f(l-1))`. Since `R` is noetherian,
the syzygy module is finitely generated. Decomposing each coordinate's syzygy in terms
of generators gives the witnesses for `IsTrivialRelation`. -/
theorem Module.Flat.pi_self {R : Type u} [CommRing R] [IsNoetherianRing R]
    (ι : Type u) : Module.Flat R (ι → R) := by
  apply Module.Flat.of_forall_isTrivialRelation
  intro l f x hfx
  -- Coordinate-wise relation: for all n, ∑ f(i) * x(i)(n) = 0
  have hcoord : ∀ n : ι, ∑ i, f i * (x i n) = 0 := by
    intro n
    have : (∑ i, f i • x i) n = (0 : ι → R) n := congr_fun hfx n
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  -- Get generators of the syzygy module (kernel of the relation map)
  obtain ⟨k, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian
      (⊤ : Submodule R ↥(LinearMap.ker (relMapFlat f))))
  -- Decompose each coordinate's syzygy using the generators
  have hdecomp : ∀ n : ι, ∃ c : Fin k → R,
      ∀ i, x i n = ∑ j, c j * (s j : Fin l → R) i := by
    intro n
    have hmem : (⟨fun i ↦ x i n, by
        simp only [LinearMap.mem_ker, relMapFlat]; exact hcoord n⟩ :
        ↥(LinearMap.ker (relMapFlat f))) ∈
        Submodule.span R (Set.range s) := by
      rw [hs]; trivial
    obtain ⟨c, hc⟩ := mem_span_range_iff_exists_fin.mp hmem
    exact ⟨c, fun i ↦ by
      have := congr_arg
        (fun (v : ↥(LinearMap.ker (relMapFlat f))) ↦
          (v : Fin l → R) i) hc
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      exact this⟩
  choose c hc using hdecomp
  -- Build IsTrivialRelation witnesses:
  -- a(i,j) = s(j)(i) (syzygy generator components)
  -- y(j)(n) = c(n)(j) (coefficient at coordinate n)
  refine ⟨k, fun i j ↦ (s j : Fin l → R) i,
    fun j n ↦ c n j, ?_, ?_⟩
  · -- x(i) = ∑_j a(i,j) • y(j)
    intro i; ext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hc n i]; congr 1; ext j; ring
  · -- ∑_i f(i) * a(i,j) = 0 (syzygy condition)
    intro j
    have hker := (s j).prop
    simp only [LinearMap.mem_ker, relMapFlat] at hker
    simpa only [LinearMap.coe_mk, AddHom.coe_mk] using hker

/-- The multivariate power series ring `MvPowerSeries σ R` is flat over noetherian `R`.
Since `MvPowerSeries σ R = (σ →₀ ℕ) → R` as an `R`-module, this is a direct
consequence of `Module.Flat.pi_self`. -/
instance MvPowerSeries.instModuleFlat {R : Type u} [CommRing R]
    [IsNoetherianRing R] (σ : Type u) :
    Module.Flat R (MvPowerSeries σ R) :=
  Module.Flat.pi_self (σ →₀ ℕ)

end ChaseFlatness

/-! ### Remark 8.29: Restricted modules and flatness (general, no DiscreteTopology)

This section establishes the free case equivalence `(Aⁿ)⟨X⟩ ≅ A⟨X⟩ⁿ`, the natural
transformation `μ_M : M ⊗ A⟨X⟩ → M⟨X⟩`, the injectivity of `restrictedModule.map`
for injections, and the flatness of `A⟨X⟩` over noetherian `A`. These are the
building blocks for Remark 8.29 and Lemma 8.31 of Wedhorn.

References: [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Remark 8.29, Lemma 8.31
-/

section Remark829

variable {A : Type u} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-! #### Coefficient of smul in TateAlgebra -/

/-- The coefficient of `a • f` in `TateAlgebra A` equals `a` times the
coefficient of `f`. Bridges the Subring-based scalar multiplication
(via `algebraMap`) with pointwise scaling. -/
theorem TateAlgebra.smul_val_eq (a : A) (f : ↥(TateAlgebra A))
    (s : Fin 1 →₀ ℕ) : (a • f).val s = a * f.val s := by
  rw [show (a • f).val s =
    MvPowerSeries.coeff s ((a • f).val) from
    (MvPowerSeries.coeff_apply _ _).symm]
  change MvPowerSeries.coeff s
    (MvPowerSeries.C (σ := Fin 1) a * f.val) = _
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_apply]

/-! #### Step 1: Free case — (Aⁿ)⟨X⟩ ≅ A⟨X⟩ⁿ -/

/-- For `M = Fin n → A` (the free module of rank `n`), the restricted
module `M⟨X⟩` is linearly equivalent to `Fin n → A⟨X⟩`.
A restricted `(Fin n → A)`-valued power series is the same as `n`
restricted `A`-valued power series (componentwise).
Remark 8.29 of Wedhorn. -/
noncomputable def restrictedModule_fin_equiv (n : ℕ) :
    restrictedModule A (Fin n → A) ≃ₗ[A]
      Fin n → ↥(TateAlgebra A) where
  toFun f i := ⟨fun s ↦ f.val s i,
    (tendsto_pi_nhds.mp f.prop i).congr fun _ ↦ rfl⟩
  invFun g := ⟨fun s i ↦ (g i).val s,
    tendsto_pi_nhds.mpr fun i ↦
      ((g i).prop).congr fun s ↦
        (MvPowerSeries.coeff_apply _ _).symm⟩
  left_inv f := by apply Subtype.ext; rfl
  right_inv g := by funext i; apply Subtype.ext; rfl
  map_add' f g := by funext i; apply Subtype.ext; rfl
  map_smul' a f := by
    funext i; apply Subtype.ext; funext s
    simp only [RingHom.id_apply, Pi.smul_apply]
    change (a • f.val) s i =
      (a • (⟨fun s ↦ f.val s i, _⟩ :
        ↥(TateAlgebra A))).val s
    rw [TateAlgebra.smul_val_eq]; rfl

/-! #### Step 2: The natural transformation μ_M -/

/-- The natural transformation `μ_M : M ⊗[A] A⟨X⟩ → M⟨X⟩` sending
`m ⊗ f ↦ (s ↦ f(s) • m)` (scalar multiplication of each coefficient
by `m`). Requires `ContinuousSMul A M` so that `aₛ → 0` in `A`
implies `aₛ • m → 0` in `M`. Remark 8.29 of Wedhorn. -/
noncomputable def muMap
    {M : Type*} [AddCommGroup M] [Module A M]
    [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul A M] :
    TensorProduct A M ↥(TateAlgebra A) →ₗ[A]
      ↥(restrictedModule A M) :=
  TensorProduct.lift (LinearMap.mk₂ A
    (fun m f ↦ ⟨fun s ↦ f.val s • m, by
      change Tendsto _ cofinite (nhds 0)
      rw [show (0 : M) = (0 : A) • m from
        (zero_smul A m).symm]
      exact (f.prop.congr fun s ↦
        (MvPowerSeries.coeff_apply _ _).symm).smul_const
          m⟩)
    (fun m₁ m₂ f ↦
      Subtype.ext (funext fun s ↦ smul_add _ _ _))
    (fun a m f ↦ Subtype.ext (funext fun s ↦ by
      change f.val s • (a • m) = a • (f.val s • m)
      rw [smul_comm]))
    (fun m f₁ f₂ ↦
      Subtype.ext (funext fun s ↦ add_smul _ _ _))
    (fun a m f ↦ Subtype.ext (funext fun s ↦ by
      change (a • f).val s • m = a • (f.val s • m)
      rw [TateAlgebra.smul_val_eq, mul_smul])))

/-! #### Injectivity of restrictedModule.map -/

/-- The induced map `M⟨X⟩ → N⟨X⟩` is injective when `f` is injective.
The map applies `f` pointwise to coefficients, so injectivity is
immediate. -/
theorem restrictedModule_map_injective
    {M : Type*} [AddCommGroup M] [Module A M]
    [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul A M]
    {N : Type*} [AddCommGroup N] [Module A N]
    [TopologicalSpace N] [IsTopologicalAddGroup N]
    [ContinuousConstSMul A N]
    (f : M →ₗ[A] N) (hf_cont : Continuous f)
    (hf_inj : Function.Injective f) :
    Function.Injective
      (restrictedModule.map (A := A) f hf_cont) := by
  intro ⟨g₁, _⟩ ⟨g₂, _⟩ h
  apply Subtype.ext; funext s
  exact hf_inj (congr_fun (congr_arg Subtype.val h) s)

/-! #### Equivalence restrictedModule A A ≃ TateAlgebra A -/

/-- The restricted module `A⟨X⟩` (as an `A`-submodule of
`MvPowerSeries`) is linearly equivalent to the Tate algebra `A⟨X⟩`
(as a subring). The two have the same carrier (restricted power
series) viewed through different type-class lenses. -/
noncomputable def restrictedModuleA_equiv :
    ↥(restrictedModule A A) ≃ₗ[A] ↥(TateAlgebra A) where
  toFun f := ⟨f.val,
    f.prop.congr fun s ↦
      MvPowerSeries.coeff_apply f.val s⟩
  invFun g := ⟨g.val,
    g.prop.congr fun s ↦
      (MvPowerSeries.coeff_apply g.val s).symm⟩
  left_inv f := by apply Subtype.ext; rfl
  right_inv g := by apply Subtype.ext; rfl
  map_add' f g := by apply Subtype.ext; rfl
  map_smul' a f := by
    apply Subtype.ext; ext s
    simp only [RingHom.id_apply]
    change (a • f).val s =
      (a • (⟨f.val, _⟩ : ↥(TateAlgebra A))).val s
    rw [show (a • f).val s = a * f.val s from rfl]
    rw [show
      (a • (⟨f.val, _⟩ : ↥(TateAlgebra A))).val s =
        a * f.val s from by
      rw [show
        (a • (⟨f.val, _⟩ : ↥(TateAlgebra A))).val s =
          MvPowerSeries.coeff s
            ((a • (⟨f.val, _⟩ :
              ↥(TateAlgebra A))).val) from
          (MvPowerSeries.coeff_apply _ _).symm]
      change MvPowerSeries.coeff s
        (MvPowerSeries.C (σ := Fin 1) a * f.val) = _
      rw [MvPowerSeries.coeff_C_mul,
        MvPowerSeries.coeff_apply]]

end Remark829

/-! ### NonarchimedeanAddGroup on Fin n → A -/

section PiNonarchimedean

variable {A : Type u} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [IsTopologicalRing A]

omit [NonarchimedeanRing A] [IsTopologicalRing A] in
private def piOpenAddSubgroup {n : ℕ} (W : Fin n → OpenAddSubgroup A) :
    OpenAddSubgroup (Fin n → A) where
  toAddSubgroup := {
    carrier := Set.pi Set.univ (fun i ↦ (W i : Set A))
    add_mem' := fun ha hb ↦ fun i _ ↦ (W i).add_mem (ha i trivial) (hb i trivial)
    zero_mem' := fun i _ ↦ (W i).zero_mem
    neg_mem' := fun ha ↦ fun i _ ↦ (W i).neg_mem (ha i trivial) }
  isOpen' := isOpen_set_pi (Set.toFinite _) (fun i _ ↦ (W i).isOpen)

/-- Finite pi types over a nonarchimedean ring are nonarchimedean.
Every open neighborhood of 0 contains a product of open subgroups. -/
instance nonarchimedeanPiFin (n : ℕ) :
    NonarchimedeanAddGroup (Fin n → A) where
  is_nonarchimedean U hU := by
    classical
    rw [nhds_pi, Filter.mem_pi'] at hU
    obtain ⟨I, S, hS, hSU⟩ := hU
    have hW : ∀ i : Fin n, ∃ W : OpenAddSubgroup A,
        (i ∈ I → (W : Set A) ⊆ S i) := by
      intro i
      by_cases hi : i ∈ I
      · obtain ⟨W, hW⟩ := NonarchimedeanAddGroup.is_nonarchimedean (S i) (hS i)
        exact ⟨W, fun _ ↦ hW⟩
      · obtain ⟨V, _⟩ := NonarchimedeanAddGroup.is_nonarchimedean
            (Set.univ : Set A) Filter.univ_mem
        exact ⟨V, fun h ↦ absurd h hi⟩
    choose W hW using hW
    exact ⟨piOpenAddSubgroup W, fun f hf ↦ hSU (fun i hi ↦ hW i hi (hf i trivial))⟩

end PiNonarchimedean

/-! ### Remark 8.29 continued: μ_M surjective

References: [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Remark 8.29
-/

section MuMapSurjective

variable {A : Type u} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [IsTopologicalRing A] [T2Space A] [FirstCountableTopology A]

-- IsNoetherianRing not needed for muMap_surjective itself (only for muMap_injective later).

/-- The natural map `μ_M : M ⊗[A] A⟨X⟩ → M⟨X⟩` is surjective for finitely generated
modules `M` over a noetherian topological ring `A`.

The proof: take a surjection `p : Aⁿ → M` from finite generation. Since `Aⁿ` and `M`
carry the module topology, `p` is open (Prop 6.18(2)), hence `p⟨X⟩ : (Aⁿ)⟨X⟩ → M⟨X⟩`
is surjective. Given `g ∈ M⟨X⟩`, lift to `h ∈ (Aⁿ)⟨X⟩`, decompose via the free case
equivalence `(Aⁿ)⟨X⟩ ≅ A⟨X⟩ⁿ` to get `(h₁,...,hₙ)`, and verify
`g = μ_M(∑ p(eᵢ) ⊗ hᵢ)`. Remark 8.29 of Wedhorn. -/
theorem muMap_surjective
    {M : Type u} [AddCommGroup M] [Module A M]
    [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul A M] [ContinuousConstSMul A M]
    [IsModuleTopology A M] [Module.Finite A M] [T2Space M] :
    Function.Surjective (muMap (A := A) (M := M)) := by
  obtain ⟨n, p, hp_surj⟩ := Module.Finite.exists_fin' A M
  have hp_cont : Continuous p :=
    IsModuleTopology.continuous_linearMap_of_finite p
  have hp_open : IsOpenMap p :=
    IsModuleTopology.isOpenMap_of_surjective_of_finite p hp_surj
  have hp_surj_mod : Function.Surjective
      (restrictedModule.map (A := A) p hp_cont) :=
    restrictedModule_map_surjective p hp_cont hp_surj hp_open
  intro g
  obtain ⟨h, hh⟩ := hp_surj_mod g
  refine ⟨∑ i : Fin n, p (Pi.single i 1) ⊗ₜ[A]
      (restrictedModule_fin_equiv n h i), ?_⟩
  suffices muMap (∑ i : Fin n, p (Pi.single i 1) ⊗ₜ[A]
      (restrictedModule_fin_equiv n h i)) = restrictedModule.map p hp_cont h by
    rw [this, hh]
  apply Subtype.ext; funext s
  have lhs : (muMap (∑ i : Fin n, p (Pi.single i 1) ⊗ₜ[A]
      (restrictedModule_fin_equiv n h i))).val s =
      ∑ i : Fin n, h.val s i • p (Pi.single i 1) := by
    simp only [map_sum, muMap, TensorProduct.lift.tmul, LinearMap.mk₂_apply]
    rw [show (∑ x : Fin n, (⟨fun s ↦
        (restrictedModule_fin_equiv n h x : ↥(TateAlgebra A)).val s •
          p (Pi.single x 1), _⟩ : ↥(restrictedModule A M))).val s =
        ∑ x : Fin n, (restrictedModule_fin_equiv n h x : ↥(TateAlgebra A)).val s •
          p (Pi.single x 1) from by
      simp only [AddSubmonoidClass.coe_finsetSum]
      exact Fintype.sum_apply s _]
    rfl
  rw [lhs]
  change _ = p (h.val s)
  rw [show h.val s = ∑ i : Fin n, h.val s i • Pi.single i (1 : A) from
    funext fun j ↦ by simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]; congr 1; funext i; rw [map_smul]
  congr 1
  simp [Finset.sum_apply, Pi.single_apply]

omit [IsTopologicalRing A] [T2Space A] [FirstCountableTopology A] in
/-- **Naturality of `μ`** (Remark 8.29): for an `A`-linear continuous `f : M → N`, the square
`μ_N ∘ (f ⊗ id) = (f⟨X⟩) ∘ μ_M` commutes, where `f⟨X⟩ = restrictedModule.map f`. This is the
naturality that drives the 5-lemma proof of `muMap_injective`. -/
theorem muMap_naturality
    {M : Type u} [AddCommGroup M] [Module A M] [TopologicalSpace M]
      [IsTopologicalAddGroup M] [ContinuousSMul A M] [ContinuousConstSMul A M]
    {N : Type u} [AddCommGroup N] [Module A N] [TopologicalSpace N]
      [IsTopologicalAddGroup N] [ContinuousSMul A N] [ContinuousConstSMul A N]
    (f : M →ₗ[A] N) (hf : Continuous f) :
    (restrictedModule.map f hf).comp (muMap (A := A) (M := M)) =
      (muMap (A := A) (M := N)).comp (TensorProduct.map f LinearMap.id) := by
  apply TensorProduct.ext'
  intro m a
  apply Subtype.ext
  funext s
  exact map_smul f (a.val s) m

/-- The candidate inverse to `μ_{Aᵐ}` in the free case: a restricted `(Fin m → A)`-valued
series `c` maps to `∑ᵢ eᵢ ⊗ cᵢ`, where `cᵢ ∈ A⟨X⟩` is the `i`-th component series of `c` under
`restrictedModule_fin_equiv` and `eᵢ = Pi.single i 1`. -/
private noncomputable def muMapFreeInv (m : ℕ) :
    ↥(restrictedModule A (Fin m → A)) →ₗ[A]
      TensorProduct A (Fin m → A) ↥(TateAlgebra A) :=
  (∑ i : Fin m, (TensorProduct.mk A (Fin m → A) ↥(TateAlgebra A)
      (Pi.single i 1)).comp ((LinearMap.proj i).comp
        (restrictedModule_fin_equiv m).toLinearMap))

omit [T2Space A] [FirstCountableTopology A] in
/-- **Step 6 of Remark 8.29 (free case).** For a finite free module `M = Aᵐ`, the natural map
`μ_{Aᵐ} : Aᵐ ⊗ A⟨X⟩ → (Aᵐ)⟨X⟩` is **injective**. Wedhorn: "this is clear if `M` is a finitely
generated free `A`-module." We exhibit `muMapFreeInv` as a left inverse: on a generator
`(Pi.single j a) ⊗ f`, the `i`-th component series of `μ(generator)` is `(Pi.single j a) i • f`,
so `muMapFreeInv (μ z) = ∑ᵢ ((Pi.single j a) i • Pi.single i 1) ⊗ f = (Pi.single j a) ⊗ f = z`. -/
private theorem muMap_free_injective (m : ℕ) :
    Function.Injective (muMap (A := A) (M := Fin m → A)) := by
  have hli : (muMapFreeInv m).comp (muMap (A := A) (M := Fin m → A)) = LinearMap.id := by
    apply TensorProduct.ext'
    intro x f
    -- muMapFreeInv (muMap (x ⊗ f)).  Compute its value.
    change muMapFreeInv m (muMap (x ⊗ₜ[A] f)) = x ⊗ₜ[A] f
    rw [muMapFreeInv]
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
      LinearMap.coe_proj, Function.eval, LinearEquiv.coe_coe, TensorProduct.mk_apply]
    -- The `i`-th component of `restrictedModule_fin_equiv m (muMap (x ⊗ f))` is
    -- the series `s ↦ (f.val s • x) i = x i • (f.val s)`, i.e. `x i • f` in `A⟨X⟩`.
    have hcomp : ∀ i : Fin m,
        (restrictedModule_fin_equiv m (muMap (x ⊗ₜ[A] f))) i = x i • f := by
      intro i
      apply Subtype.ext; funext s
      change (f.val s • x) i = (x i • f).val s
      rw [Pi.smul_apply, smul_eq_mul, TateAlgebra.smul_val_eq, mul_comm]
    simp only [hcomp]
    -- Now: ∑ᵢ (Pi.single i 1) ⊗ (x i • f) = x ⊗ f.
    rw [show (∑ i : Fin m, (Pi.single i (1 : A) : Fin m → A) ⊗ₜ[A] (x i • f)) =
        (∑ i : Fin m, (x i • Pi.single i (1 : A) : Fin m → A)) ⊗ₜ[A] f from by
      rw [TensorProduct.sum_tmul]
      exact Finset.sum_congr rfl fun i _ ↦ by
        rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul]]
    congr 1
    funext j
    simp [Finset.sum_apply, Pi.single_apply, Pi.smul_apply]
  exact Function.LeftInverse.injective (g := muMapFreeInv m)
    (fun z ↦ by rw [← LinearMap.comp_apply, hli, LinearMap.id_apply])

/-- **Step 3 of Remark 8.29 (middle exactness).** For a presentation `Aⁿ →u Aᵐ →p M → 0`
with `p` surjective and `range u = ker p`, the restricted-power-series row
`Aⁿ⟨X⟩ →u⟨X⟩ Aᵐ⟨X⟩ →p⟨X⟩ M⟨X⟩` is exact at the middle: every `c ∈ Aᵐ⟨X⟩` with
`p⟨X⟩ c = 0` is of the form `u⟨X⟩ b`.

The proof realizes Wedhorn's "Proposition 6.18(2) shows that `u` is open onto its image":
since `range u` is closed (image of a fg module is fg, fg submodules of a fg module over a
noetherian Tate ring are closed) the corestriction `u' : Aⁿ ↠ ↥(range u)` is a continuous
open surjection (`wedhorn_6_18_open_onto_image`), so the surjection-lifting lemma
`restrictedModule_map_surjective` lifts the `↥(range u)`-valued series `c'` (whose coefficients
`c.val s ∈ ker p = range u` converge to `0`) to `b ∈ Aⁿ⟨X⟩` with `u⟨X⟩ b = c`. -/
private theorem muMap_middle_exact
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsTateRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M]
    [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul A M] [ContinuousConstSMul A M] [T2Space M]
    {n m : ℕ}
    (u : (Fin n → A) →ₗ[A] (Fin m → A)) (hu_cont : Continuous u)
    (p : (Fin m → A) →ₗ[A] M) (hp_cont : Continuous p)
    (hp_surj : Function.Surjective p)
    (hrange : LinearMap.range u = LinearMap.ker p)
    (c : ↥(restrictedModule A (Fin m → A)))
    (hc : restrictedModule.map p hp_cont c = 0) :
    ∃ b, restrictedModule.map u hu_cont b = c := by
  classical
  -- Subspace typeclass setup on `↥(range u)` (needed to form `↥(range u)⟨X⟩` and to apply
  -- the surjection-lifting lemma; only `T2`/`IsTopologicalAddGroup`/`ContinuousConstSMul`
  -- are required of the target, all inherited from the subspace structure).
  haveI : ContinuousSMul A ↥(LinearMap.range u) := by
    refine ⟨?_⟩
    rw [show (fun pr : A × ↥(LinearMap.range u) ↦ pr.1 • pr.2) =
        fun pr ↦ (⟨pr.1 • (pr.2 : Fin m → A), Submodule.smul_mem _ pr.1 pr.2.2⟩ :
          ↥(LinearMap.range u)) from rfl]
    refine Topology.IsInducing.subtypeVal.continuous_iff.mpr ?_
    exact continuous_smul.comp ((continuous_fst).prodMk
      ((continuous_subtype_val.comp continuous_snd)))
  -- **Wedhorn Prop 6.18(2)** ("`u` is continuous and open onto its image", p. 81,
  -- `wedhorn.txt:4087`): the corestriction `u' = u.rangeRestrict : Aⁿ ↠ ↥(range u)` is an
  -- open map.  This is exactly `ValuationSpectrum.wedhorn_6_18_open_onto_image u`
  -- (axiom-clean) in `WedhornBanachTheorem.lean`, which `TateAlgebra.lean` does not import;
  -- it discharges to that one lemma (a `UniformSpace A := rightUniformSpace A` bundle with
  -- `[CompleteSpace A] [IsTateRing A] [IsNoetherianRing A]`, and `range u` closed via
  -- `fg_topologicalClosure_isClosed` since it is fg over the noetherian Tate ring).
  have hu'_open : IsOpenMap (u.rangeRestrict) := by
    letI uA : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
    haveI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
    haveI : (nhds (0 : A)).IsCountablyGenerated :=
      FirstCountableTopology.nhds_generated_countable 0
    haveI : (uniformity A).IsCountablyGenerated :=
      IsUniformAddGroup.uniformity_countably_generated
    exact ValuationSpectrum.wedhorn_6_18_open_onto_image u
  have hu'_surj : Function.Surjective u.rangeRestrict := LinearMap.surjective_rangeRestrict u
  have hu'_cont : Continuous u.rangeRestrict :=
    Topology.IsInducing.subtypeVal.continuous_iff.mpr hu_cont
  -- Coefficients of `c` lie in `ker p = range u`.
  have hcoef : ∀ s, c.val s ∈ LinearMap.range u := by
    intro s
    rw [hrange, LinearMap.mem_ker]
    exact congr_fun (congr_arg Subtype.val hc) s
  -- Realize `c` as an `↥(range u)`-valued restricted series `c'`.
  have hc'_restricted :
      MvPowerSeries.IsRestrictedModule (fun s ↦ (⟨c.val s, hcoef s⟩ : ↥(LinearMap.range u))) := by
    change Tendsto (fun s ↦ (⟨c.val s, hcoef s⟩ : ↥(LinearMap.range u))) cofinite (nhds 0)
    rw [Topology.IsInducing.subtypeVal.tendsto_nhds_iff]
    exact c.2
  set c' : ↥(restrictedModule A ↥(LinearMap.range u)) :=
    ⟨fun s ↦ ⟨c.val s, hcoef s⟩, hc'_restricted⟩ with hc'_def
  -- Surjection lifting: lift `c'` to `b ∈ Aⁿ⟨X⟩` along `u'⟨X⟩`.
  obtain ⟨b, hb⟩ := restrictedModule_map_surjective u.rangeRestrict hu'_cont hu'_surj hu'_open c'
  refine ⟨b, ?_⟩
  -- `u = (range u).subtype ∘ u.rangeRestrict`, so `u⟨X⟩ = subtype⟨X⟩ ∘ u'⟨X⟩`.
  have hcomp : (LinearMap.range u).subtype.comp u.rangeRestrict = u := LinearMap.ext fun _ ↦ rfl
  have hsub_cont : Continuous (LinearMap.range u).subtype := continuous_subtype_val
  have key : restrictedModule.map u hu_cont b =
      restrictedModule.map (LinearMap.range u).subtype hsub_cont
        (restrictedModule.map u.rangeRestrict hu'_cont b) := by
    rw [← LinearMap.comp_apply, ← restrictedModule.map_comp]
    congr 1
  rw [key, hb]
  -- `subtype⟨X⟩ c' = c`.
  apply Subtype.ext; funext s; rfl

/-- **Remark 8.29, injective half** (Wedhorn *Adic Spaces* p. 81, `wedhorn.txt:4074`): the
natural map `μ_M : M ⊗_A A⟨X⟩ → M⟨X⟩`, `m ⊗ a ↦ ma`, is **injective** for a finitely
generated module `M` over a (complete) **noetherian Tate ring** `A`.

This is the faithful keystone of Lemma 8.31 (hence Prop 8.30 / Cor 8.32 / Thm 8.28(b)).
Wedhorn's proof: take a presentation `Aⁿ →u Aᵐ →p M → 0` (`A` noetherian ⇒ the kernel is
finitely generated); by **Prop 6.18(2)** the maps `u, p` are continuous and open onto their
image (`wedhorn_6_18_open_onto_image`); the restricted-power-series functor then gives an
exact sequence `Aᵐ⟨X⟩ → Aⁿ⟨X⟩ → M⟨X⟩ → 0`; the 5-lemma yields bijectivity
(`muMap_surjective` is the right exactness, this is injectivity).

**Hypotheses (Wedhorn-faithful, verbatim from the source).** Remark 8.29 opens with
"Let `A` be **a complete noetherian Tate ring**" (wedhorn.txt:4074). The proof invokes
**Prop 6.18(2)** — "`u` and `p` are continuous and open onto their image" — whose
*open-onto-image* (strictness) half is the Banach open mapping theorem and therefore needs
`A` complete and Tate. Accordingly this declaration carries exactly Wedhorn's bundle:
`[CompleteSpace A]` (w.r.t. the right uniformity of the topological add group),
`[IsTateRing A]`, `[IsNoetherianRing A]` — the same bundle on the
binder of `muMap_middle_exact` and of `ValuationSpectrum.wedhorn_6_18_open_onto_image`.
(No `[IsLinearTopology A A]`: it is unsatisfiable for a Tate ring, and the `A°`-layer
obligations it used to feed are now discharged via `[IsHuberRing A]`'s
`NonarchimedeanAddGroup` instance.)
These are **not** work-deferral hypotheses (the open-mapping work is fully discharged by
`muMap_middle_exact`/`wedhorn_6_18_open_onto_image`); they are the literal premises of
Remark 8.29, without which Prop 6.18(2) — hence the middle-exactness step — is unavailable.

**Faithfulness:** uses `[IsNoetherianRing A]` — noetherianity of the **Tate ring** `A`, the
`k = 0` instance of `IsStronglyNoetherian A` — and **never** a noetherian ring of definition
`A₀`. This is the Wedhorn-faithful replacement for the divergent noeth-`A₀` Artin–Rees route
`TateAlgebra.tateAlgebra_flat (P) [IsNoetherianRing P.A₀]`. See
`.mathlib-quality/decomposition.md` §LEAF A1 (2026-06-02 authoritative decompose). -/
theorem muMap_injective
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsTateRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M]
    [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul A M] [ContinuousConstSMul A M]
    [IsModuleTopology A M] [Module.Finite A M] [T2Space M] :
    Function.Injective (muMap (A := A) (M := M)) := by
  -- Presentation: `p : Aᵐ ↠ M` from the generators.
  obtain ⟨m, p, hp_surj⟩ := Module.Finite.exists_fin' A M
  have hp_cont : Continuous p := IsModuleTopology.continuous_linearMap_of_finite p
  -- `ker p` is finitely generated (`A` noetherian, `Aᵐ` finite).
  haveI : Module.Finite A ↥(LinearMap.ker p) := by
    have : IsNoetherian A (Fin m → A) := inferInstance
    exact Module.Finite.iff_fg.mpr (this.noetherian _)
  obtain ⟨n, v, hv_surj⟩ := Module.Finite.exists_fin' A ↥(LinearMap.ker p)
  -- `u = (ker p).subtype ∘ v : Aⁿ → Aᵐ`, with `range u = ker p`.
  set u : (Fin n → A) →ₗ[A] (Fin m → A) := (LinearMap.ker p).subtype.comp v with hu_def
  have hu_cont : Continuous u := IsModuleTopology.continuous_linearMap_of_finite u
  have hrange : LinearMap.range u = LinearMap.ker p := by
    rw [hu_def, LinearMap.range_comp, LinearMap.range_eq_top.mpr hv_surj, Submodule.map_top,
      Submodule.range_subtype]
  -- `p ∘ u = 0` (since `range u = ker p`).
  have hpu : p.comp u = 0 := by
    apply LinearMap.ext; intro x
    have : u x ∈ LinearMap.ker p := by rw [← hrange]; exact LinearMap.mem_range_self u x
    simpa using this
  -- The 5-lemma chase.
  rw [injective_iff_map_eq_zero]
  intro z hz
  -- Step 1: `p ⊗ id` surjective; lift `z` to `w`.
  have hPtensor_surj : Function.Surjective (TensorProduct.map p (LinearMap.id (R := A)
      (M := ↥(TateAlgebra A)))) := by
    rw [← LinearMap.rTensor_def]
    exact LinearMap.rTensor_surjective _ hp_surj
  obtain ⟨w, hw⟩ := hPtensor_surj z
  -- Step 2: `p⟨X⟩ (μ_{Aᵐ} w) = μ_M (p ⊗ id w) = μ_M z = 0`.
  have hstep2 : restrictedModule.map p hp_cont (muMap w) = 0 := by
    have hnat := muMap_naturality p hp_cont
    have := LinearMap.congr_fun hnat w
    simp only [LinearMap.comp_apply] at this
    rw [this, hw, hz]
  -- Step 3: middle exactness gives `b` with `u⟨X⟩ b = μ_{Aᵐ} w`.
  obtain ⟨b, hb⟩ := muMap_middle_exact u hu_cont p hp_cont hp_surj hrange (muMap w) hstep2
  -- Step 4: `μ_{Aⁿ}` surjective; lift `b` to `v'`.
  obtain ⟨v', hv'⟩ := muMap_surjective (M := Fin n → A) b
  -- Step 5: `μ_{Aᵐ} w = u⟨X⟩ b = u⟨X⟩ (μ_{Aⁿ} v') = μ_{Aᵐ} (u ⊗ id v')`.
  have hstep5 : muMap w = muMap ((TensorProduct.map u (LinearMap.id (R := A)
      (M := ↥(TateAlgebra A)))) v') := by
    have hnat := muMap_naturality u hu_cont
    have := LinearMap.congr_fun hnat v'
    simp only [LinearMap.comp_apply] at this
    rw [← hb, ← hv', this]
  -- Step 6: `μ_{Aᵐ}` injective (free case) ⟹ `w = u ⊗ id v'`.
  have hstep6 : w = (TensorProduct.map u (LinearMap.id (R := A)
      (M := ↥(TateAlgebra A)))) v' := muMap_free_injective m hstep5
  -- Step 7: `z = p ⊗ id w = p ⊗ id (u ⊗ id v') = (p ∘ u) ⊗ id v' = 0`.
  rw [← hw, hstep6, ← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp,
    hpu, TensorProduct.map_zero_left, LinearMap.zero_apply]

end MuMapSurjective

/-! ### Quotient equivalence (moved outside namespace for typeclass inference) -/

/-- The isomorphism `A⟨X⟩/(X) ≃+* A`. -/
noncomputable def TateAlgebra.quotientXEquiv {A : Type u}
    [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] :
    (TateAlgebra A : Type u) ⧸
    (Ideal.span {TateAlgebra.X (A := A)} :
      Ideal (TateAlgebra A)) ≃+* A :=
  (Ideal.quotEquivOfEq TateAlgebra.ker_evalZeroHom.symm).trans
    (RingHom.quotientKerEquivOfSurjective
      TateAlgebra.evalZeroHom_surjective)

/-! ### Flatness of the Tate algebra (Lemma 8.31(1), general case)

We prove `Module.Flat A ↥(TateAlgebra A)` for noetherian nonarchimedean topological
rings `A`. The proof adapts Chase's theorem (equational criterion) from the full power
series ring `MvPowerSeries` to the restricted power series `TateAlgebra A`.

The key mathematical input is: given a syzygy `∑ fᵢ xᵢ = 0` with `xᵢ ∈ A⟨X⟩`, the
decomposition coefficients (expressing each coordinate vector in terms of finitely many
syzygy generators) can be chosen to form restricted power series. This uses the Artin-Rees
lemma for module topologies: the surjection from `A^k` onto the syzygy module (with module
topology) is open, allowing the surjection lifting lemma (`restrictedModule_map_surjective`)
to produce convergent lifts.

References: [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 8.31(1), Remark 8.29
-/

section TateAlgebraFlat

variable {A : Type u} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [IsTopologicalRing A] [T2Space A] [IsNoetherianRing A]
  [IsTateRing A]

omit [IsTopologicalRing A] [T2Space A] [IsNoetherianRing A]
  [IsTateRing A] in
/-- Coordinate-wise extraction of a relation in `TateAlgebra A`:
if `∑ fᵢ • xᵢ = 0` in `A⟨X⟩`, then `∑ fᵢ * xᵢ(s) = 0` in `A` for each
multi-index `s`. -/
private theorem tate_coord_relation {l : ℕ} {f : Fin l → A}
    {x : Fin l → ↥(TateAlgebra A)}
    (hfx : ∑ i, f i • x i = 0) (s : Fin 1 →₀ ℕ) :
    ∑ i, f i * (x i).val s = 0 := by
  have h' := congr_fun (congr_arg Subtype.val hfx) s
  rw [show (∑ i, f i • x i : ↥(TateAlgebra A)).val =
    (TateAlgebra A).subtype (∑ i, f i • x i) from rfl,
    map_sum] at h'
  simp only [Subring.coe_subtype, ZeroMemClass.coe_zero] at h'
  -- h' now has the form (∑ i, (f i • x i).val) s = 0
  -- We need ∑ f i * x i s = 0.
  -- Use that Subtype.val commutes with sums, and smul_val_eq.
  suffices h : ∀ i, (f i • x i : ↥(TateAlgebra A)).val s = f i * (x i).val s by
    trans ∑ i, (f i • x i : ↥(TateAlgebra A)).val s
    · exact Finset.sum_congr rfl (fun i _ ↦ (h i).symm)
    · -- The goal after trans: ∑ i, (f i • x i).val s = 0
      -- Use h' which says (∑ i, (f i • x i).val) s = 0
      exact Fintype.sum_apply (α := Fin 1 →₀ ℕ) s
        (fun i ↦ (f i • x i : ↥(TateAlgebra A)).val) ▸ h'
  exact fun i ↦ TateAlgebra.smul_val_eq (f i) (x i) s

/-- The relation map for syzygies in the Tate algebra flatness proof. -/
private noncomputable def tateRelMap {l : ℕ}
    (f : Fin l → A) : (Fin l → A) →ₗ[A] A where
  toFun r := ∑ i, f i * r i
  map_add' r s := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a r := by simp [smul_eq_mul, mul_left_comm, Finset.mul_sum]

omit [TopologicalSpace A] [NonarchimedeanRing A] [IsTopologicalRing A]
  [T2Space A] [IsNoetherianRing A] [IsTateRing A] in
/-- Extraction of `Finsupp` coefficients to plain function coefficients
in the span of a finite family. -/
private lemma tate_mem_span_range {l : ℕ} {g : Fin l → A} {k : ℕ}
    {s : Fin k → ↥(LinearMap.ker (tateRelMap g))}
    {x : ↥(LinearMap.ker (tateRelMap (A := A) g))} :
    x ∈ Submodule.span A (Set.range s) ↔
      ∃ c : Fin k → A, x = ∑ j, c j • s j := by
  constructor
  · intro hx
    obtain ⟨cf, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
    refine ⟨cf, ?_⟩
    rw [← hcf, Finsupp.sum,
      Finset.sum_subset (s₂ := Finset.univ) (Finset.subset_univ _)]
    intro j _ hj; rw [Finsupp.notMem_support_iff] at hj; simp [hj]
  · intro ⟨c, hc⟩; rw [hc]
    exact Submodule.sum_mem _
      (fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

/-- **Flatness of the Tate algebra** (`A⟨X⟩` is flat over noetherian `A`).

For a strongly noetherian Tate ring `A` (with noetherian ring of definition `A₀`),
the Tate algebra `A⟨X⟩` is flat as an `A`-module. The proof uses the equational
criterion for flatness, working over `A₀` with the Artin-Rees lemma to produce
decomposition coefficients that converge to zero.

Given `∑ fᵢ xᵢ = 0` in `A⟨X⟩`, we:
1. Clear denominators using the pseudo-uniformizer: `gᵢ = w^N fᵢ ∈ A₀`.
2. Study the `A₀`-kernel `K₀ = {r ∈ A₀^l : ∑ gᵢ rᵢ = 0}`, which is f.g. over `A₀`
   and generates the `A`-kernel over `A` (since `w` is a unit).
3. Apply Artin-Rees over `A₀` with ideal `I` to get, for each filtration level `m`,
   decomposition coefficients in `I^m` that map to `image(I^m)`.
4. Assemble restricted power series witnesses using the diagonal construction.

Lemma 8.31(1) of Wedhorn's *Adic Spaces*. -/
theorem tateAlgebra_flat (P : PairOfDefinition A) [IsNoetherianRing P.A₀] :
    Module.Flat A ↥(TateAlgebra A) := by
  apply Module.Flat.of_forall_isTrivialRelation
  intro l f x hfx
  -- Step 1: Coordinate-wise relation
  have hcoord : ∀ s : Fin 1 →₀ ℕ, ∑ i, f i * (x i).val s = 0 :=
    tate_coord_relation hfx
  -- Step 2: Clear denominators. Get pseudo-uniformizer w and N with g_i = w^N f_i ∈ A₀.
  obtain ⟨w, hw_nil⟩ := ‹IsTateRing A›.exists_topologicallyNilpotent_unit
  -- For each a ∈ A, the set {n | w^n * a ∈ A₀} is eventually true:
  -- {b | b * a ∈ A₀} is open (A₀ open, mult by a continuous) and contains 0,
  -- so it's a nhd of 0. Since w^n → 0, eventually w^n is in this set.
  have hw_event : ∀ a : A, ∀ᶠ n in Filter.atTop, (w : A) ^ n * a ∈ P.A₀ :=
    fun a ↦ hw_nil.eventually ((P.isOpen.preimage (continuous_mul_const a)).mem_nhds
      (by simp [P.A₀.zero_mem]))
  -- Intersect finitely many (one for each f_i) to get a common N.
  have hg_ex : ∃ N : ℕ, ∀ i : Fin l, (w : A) ^ N * f i ∈ P.A₀ := by
    have h_all : ∀ᶠ n in Filter.atTop, ∀ i : Fin l, (w : A) ^ n * f i ∈ P.A₀ := by
      rw [Filter.eventually_all]; exact fun i ↦ hw_event (f i)
    exact h_all.exists
  obtain ⟨N, hg_mem⟩ := hg_ex
  set g : Fin l → P.A₀ := fun i ↦ ⟨(w : A) ^ N * f i, hg_mem i⟩
  -- The scaled relation: w^N is a unit in A.
  have hw_unit : IsUnit ((w : A) ^ N) := w.isUnit.pow N
  -- Step 3: A₀-kernel and its generators.
  set relMap₀ : (Fin l → P.A₀) →ₗ[P.A₀] P.A₀ :=
    { toFun := fun r ↦ ∑ i, g i * r i
      map_add' := fun r s ↦ by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun a r ↦ by simp [smul_eq_mul, mul_left_comm, Finset.mul_sum] }
  set K₀ := LinearMap.ker relMap₀
  obtain ⟨k, s₀, hs₀⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (⊤ : Submodule P.A₀ ↥K₀))
  -- Step 4: A₀-syzygies give A-syzygies of f.
  have hsyz : ∀ j : Fin k, ∑ i, f i * P.A₀.subtype ((s₀ j : Fin l → P.A₀) i) = 0 := by
    intro j
    have hker : relMap₀ (s₀ j : Fin l → P.A₀) = 0 := (s₀ j).prop
    have h_A := congr_arg P.A₀.subtype hker
    simp only [relMap₀, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_zero,
      map_mul, Subring.coe_subtype] at h_A
    have h_scaled : (↑w : A) ^ N *
        ∑ i, f i * P.A₀.subtype ((s₀ j : Fin l → P.A₀) i) = 0 := by
      trans ∑ i, ((↑w : A) ^ N * f i) *
        P.A₀.subtype ((s₀ j : Fin l → ↥P.A₀) i)
      · rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ ↦ by ring)
      · exact h_A
    exact (hw_unit.mul_left_cancel (by rw [h_scaled, mul_zero])).symm
  -- Step 5: Artin-Rees over A₀.
  obtain ⟨k₀, hAR⟩ := Ideal.exists_pow_inf_eq_pow_smul P.I K₀
  -- Step 6: For each n and m, if all components ∈ image(I^{m+k₀}), get controlled decomp.
  -- This is the core Artin-Rees argument.
  have hAR_ctrl : ∀ n : Fin 1 →₀ ℕ, ∀ m : ℕ,
      (∀ i, (x i).val n ∈ Subtype.val '' ((P.I ^ (m + k₀) : Ideal P.A₀) : Set P.A₀)) →
      ∃ c₀ : Fin k → A, (∀ j, c₀ j ∈
          Subtype.val '' ((P.I ^ m : Ideal P.A₀) : Set P.A₀)) ∧
        ∀ i, (x i).val n = ∑ j, c₀ j * P.A₀.subtype ((s₀ j : Fin l → P.A₀) i) := by
    intro n m hn
    have hcomp : ∀ i, ∃ a : P.A₀, a ∈ P.I ^ (m + k₀) ∧ P.A₀.subtype a = (x i).val n := by
      intro i; obtain ⟨a, ha, heq⟩ := hn i; exact ⟨a, ha, heq⟩
    choose lift₀ hlift₀_mem hlift₀_eq using hcomp
    have h_ker : (fun i ↦ lift₀ i) ∈ K₀ := by
      -- K₀ = ker relMap₀, so need relMap₀ (fun i => lift₀ i) = 0
      -- i.e., ∑ g(i) * lift₀(i) = 0 in A₀
      -- Proof by injectivity of A₀ → A.
      have h_sum_zero : P.A₀.subtype (∑ i : Fin l, g i * lift₀ i) = 0 := by
        simp only [map_sum, map_mul, Subring.coe_subtype]
        -- Goal: ∑ i, ↑(g i) * ↑(lift₀ i) = 0
        -- ↑(g i) = ↑w ^ N * f i, ↑(lift₀ i) = (x i).val n
        trans (↑w : A) ^ N * ∑ i, f i * (x i).val n
        · rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ ↦ by
            rw [show (↑(lift₀ i) : A) = (x i).val n from hlift₀_eq i]; ring)
        · rw [hcoord, mul_zero]
      have h_eq_zero : ∑ i : Fin l, g i * lift₀ i = 0 := by
        ext; simpa [Subring.coe_subtype] using h_sum_zero
      change (fun i ↦ lift₀ i) ∈ LinearMap.ker relMap₀
      rw [LinearMap.mem_ker]
      exact h_eq_zero
    have h_smul_top : (fun i ↦ lift₀ i) ∈
        (P.I ^ (m + k₀) • ⊤ : Submodule P.A₀ (Fin l → P.A₀)) := by
      rw [show (fun i ↦ lift₀ i) = ∑ i, lift₀ i • Pi.single i 1 from by
        ext j; simp [Finset.sum_apply, Pi.single_apply]]
      exact Submodule.sum_mem _ (fun i _ ↦
        Submodule.smul_mem_smul (hlift₀_mem i) Submodule.mem_top)
    have h_in_inf : (fun i ↦ lift₀ i) ∈
        (P.I ^ (m + k₀) • ⊤ ⊓ K₀ : Submodule P.A₀ (Fin l → P.A₀)) :=
      Submodule.mem_inf.mpr ⟨h_smul_top, h_ker⟩
    rw [hAR (m + k₀) (by omega : k₀ ≤ m + k₀),
      show m + k₀ - k₀ = m from by omega] at h_in_inf
    -- h_in_inf : lift₀ ∈ I^m • (I^{k₀} • ⊤ ⊓ K₀) in (Fin l → A₀)
    -- Since I^{k₀} • ⊤ ⊓ K₀ ≤ K₀, lift₀ ∈ I^m • K₀.
    -- In the submodule K₀, this means ⟨lift₀, h_ker⟩ ∈ I^m • ⊤ as a K₀-element.
    -- Then decompose over the generators s₀ to get coefficients in I^m.
    -- We use Submodule.smul_mono_right to pass to I^m • K₀,
    -- then the generating family to extract Fin k coefficients.
    have h_in_smul_K₀ : (fun i ↦ lift₀ i) ∈
        (P.I ^ m • K₀ : Submodule P.A₀ (Fin l → P.A₀)) :=
      Submodule.smul_mono le_rfl inf_le_right h_in_inf
    -- Now extract coefficients. An element of I^m • K₀ is a finite sum ∑ aⱼ • vⱼ
    -- with aⱼ ∈ I^m and vⱼ ∈ K₀. Each vⱼ ∈ span(s₀) over A₀.
    -- So the total element decomposes over s₀ with I^m-coefficients.
    -- We extract this using Submodule.smul_induction_on.
    -- The element (as a K₀-element) decomposes over the span of s₀.
    -- Step A: Prove that any element of I^m • K₀ decomposes over s₀ with I^m coeffs.
    suffices ∃ c₀ : Fin k → P.A₀, (∀ j, c₀ j ∈ P.I ^ m) ∧
        ∀ i, lift₀ i = ∑ j, c₀ j * (s₀ j : Fin l → P.A₀) i by
      obtain ⟨c₀, hc₀_mem, hc₀_eq⟩ := this
      refine ⟨fun j ↦ P.A₀.subtype (c₀ j), fun j ↦ ⟨c₀ j, hc₀_mem j, rfl⟩, fun i ↦ ?_⟩
      have h := congr_arg P.A₀.subtype (hc₀_eq i)
      simp only [map_sum, map_mul] at h
      rw [← hlift₀_eq i]; exact h
    -- Step B: Use smul_induction_on on h_in_smul_K₀ with the predicate
    -- "can be decomposed over s₀ with I^m coefficients".
    refine Submodule.smul_induction_on (p := fun v ↦
        ∃ c₀ : Fin k → ↥P.A₀, (∀ j, c₀ j ∈ P.I ^ m) ∧
          ∀ i, v i = ∑ j, c₀ j * (s₀ j : Fin l → ↥P.A₀) i) h_in_smul_K₀
      (fun a ha v hv ↦ ?_) (fun u v ⟨cu, hcu, heu⟩ ⟨cv, hcv, hev⟩ ↦ ?_)
    · -- Base case: a • v with a ∈ I^m and v ∈ K₀.
      -- Decompose v ∈ K₀ over s₀ using the spanning hypothesis.
      have hv_span : (⟨v, hv⟩ : K₀) ∈ Submodule.span P.A₀ (Set.range s₀) :=
        hs₀ ▸ Submodule.mem_top
      obtain ⟨cf, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hv_span
      -- Convert Finsupp.sum to Finset.sum over univ
      have hcf_sum : (⟨v, hv⟩ : K₀) = ∑ j : Fin k, cf j • s₀ j := by
        rw [← hcf, Finsupp.sum,
          Finset.sum_subset (Finset.subset_univ _)]
        intro j _ hj; rw [Finsupp.notMem_support_iff.mp hj, zero_smul]
      -- Extract component-wise equality
      have hv_eq : ∀ i, v i = ∑ j, (cf j : P.A₀) * (s₀ j : Fin l → P.A₀) i := by
        intro i
        have := congr_arg (fun (w : K₀) ↦ (w : Fin l → P.A₀) i) hcf_sum
        simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
        exact this
      -- Set c₀(j) = a * cf(j), which are in I^m since a ∈ I^m.
      refine ⟨fun j ↦ a * cf j, fun j ↦ Ideal.mul_mem_right _ _ ha, fun i ↦ ?_⟩
      have : (a • v) i = a * v i := by simp [Pi.smul_apply, smul_eq_mul]
      rw [this, hv_eq i, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ ↦ by ring)
    · -- Addition case: combine coefficients.
      exact ⟨fun j ↦ cu j + cv j, fun j ↦ (P.I ^ m).add_mem (hcu j) (hcv j), fun i ↦ by
        have : (u + v) i = u i + v i := Pi.add_apply u v i
        rw [this, heu i, hev i, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ ↦ by ring)⟩
  -- Step 7: Assemble the IsTrivialRelation witness.
  -- For each n, hdecomp_A gives a decomposition over the A₀-generators.
  -- For convergence, hAR_ctrl gives controlled coefficients.
  -- We use the diagonal construction: for each n, pick the best available level.
  -- The hAR_ctrl decomposition at level m gives c₀ ∈ image(I^m) satisfying the decomp.
  -- For each n, we use the level-0 decomposition (from hdecomp_A below), and
  -- prove convergence by showing that for each m, cofinitely many n admit
  -- the level-m decomposition (from hAR_ctrl), hence the level-0 choice
  -- coincides with a controlled choice.
  --
  -- ACTUALLY: we cannot control the `choose`-based coefficients.
  -- Instead, for each n, we directly use hAR_ctrl at the appropriate level.
  -- For n where all components ∈ image(I^{0+k₀}), use hAR_ctrl at m=0.
  -- For other n (finitely many), use any decomposition (from hdecomp below).
  --
  -- KEY: we use hAR_ctrl(n, 0) for ALL n where components are in image(I^{k₀}).
  -- For the finitely many other n, use any A-decomposition.
  -- The resulting c' satisfies: for m, cofinitely many n have c'(n)(j) ∈ image(I^m)
  -- because hAR_ctrl(n, m) gives image(I^m)-coefficients (a DIFFERENT decomposition,
  -- but the suffices only needs EXISTENCE of c' with both properties, not that
  -- a specific c' satisfies both).
  --
  -- WAIT: the suffices asks for ∃ c', (∀ n i, decomp(c')) ∧ (∀ j, restricted(c')).
  -- A SINGLE c' must satisfy BOTH. We can't use different c' for different m.
  --
  -- The solution: for each n, define c'(n) from hAR_ctrl at some level q(n).
  -- For cofinitely many n, q(n) is large, giving c'(n)(j) ∈ image(I^{q(n)}).
  -- As q(n) → ∞, the coefficients → 0.
  --
  -- Define q(n) = max {m | ∀ i, (x i).val n ∈ image(I^{m+k₀})} (capped or defaulted).
  -- Use hAR_ctrl(n, q(n)) for the decomposition.
  -- For finitely many n where no level works, use arbitrary decomposition.
  --
  -- This is the DIAGONAL CONSTRUCTION.
  -- For each n, we define c'(n) by choosing from the highest available level.
  have hdecomp_or_ctrl : ∀ n : Fin 1 →₀ ℕ,
      ∃ c₀ : Fin k → A,
        (∀ i, (x i).val n =
          ∑ j, c₀ j * P.A₀.subtype ((s₀ j : Fin l → P.A₀) i)) ∧
        (∀ m, (∀ i, (x i).val n ∈
            Subtype.val '' ((P.I ^ (m + k₀) : Ideal P.A₀) : Set P.A₀)) →
          ∀ j, c₀ j ∈ Subtype.val '' ((P.I ^ m : Ideal P.A₀) : Set P.A₀)) := by
    intro n
    -- The set of valid levels S = {m | ∀ i, (x i).val n ∈ image(I^{m+k₀})} is downward
    -- closed (hyp(m+1) → hyp(m) since I^{m+1+k₀} ⊆ I^{m+k₀}).
    -- Case split: either all levels valid (components = 0) or some level fails.
    by_cases h_all_levels :
        ∀ m, ∀ i, (x i).val n ∈
          Subtype.val '' ((P.I ^ (m + k₀) : Ideal P.A₀) : Set P.A₀)
    · -- All levels valid: each component ∈ ⋂ image(I^{m+k₀}) = {0} (by T2).
      have h_zero : ∀ i, (x i).val n = 0 := by
        intro i
        by_contra hne
        obtain ⟨U, _, hU_open, _, h0U, hxV, hUV⟩ := t2_separation (Ne.symm hne)
        obtain ⟨p, _, hp⟩ := P.hasBasis_nhds_zero.mem_iff.mp (hU_open.mem_nhds h0U)
        exact Set.disjoint_left.mp hUV (hp (Set.image_mono
          (show (↑(P.I ^ (p + k₀)) : Set ↥P.A₀) ⊆ ↑(P.I ^ p) from
            Ideal.pow_le_pow_right (by omega))
          (h_all_levels p i))) hxV
      refine ⟨0, fun i ↦ by simp [h_zero i],
        fun m _ j ↦ ⟨0, (P.I ^ m).zero_mem, by simp⟩⟩
    · -- Some level fails. Find the smallest failing level q.
      push Not at h_all_levels
      obtain ⟨m_fail, hm_fail⟩ := h_all_levels
      -- The set of failing levels is upward closed: if hyp(m) fails,
      -- then hyp(m') fails for m' ≥ m (contrapositively, hyp(m'+1) → hyp(m')).
      -- So there exists a smallest failing level.
      have h_fail_exists : ∃ m, ∃ i, (x i).val n ∉
          Subtype.val '' ((P.I ^ (m + k₀) : Ideal P.A₀) : Set P.A₀) :=
        ⟨m_fail, hm_fail⟩
      -- Nat.find gives the smallest failing level q.
      classical
      set q := Nat.find h_fail_exists with hq_def
      have hq_fail := Nat.find_spec h_fail_exists
      -- For m < q, the hypothesis holds (by minimality of q).
      have hq_valid : ∀ m < q, ∀ i, (x i).val n ∈
          Subtype.val '' ((P.I ^ (m + k₀) : Ideal P.A₀) : Set P.A₀) := by
        intro m hm
        by_contra h; push Not at h
        exact Nat.find_min h_fail_exists hm h
      -- For m ≥ q, the hypothesis fails (upward closure).
      have hq_fail_above : ∀ m, q ≤ m → ¬(∀ i, (x i).val n ∈
          Subtype.val '' ((P.I ^ (m + k₀) : Ideal P.A₀) : Set P.A₀)) := by
        intro m hm hall
        obtain ⟨i₀, hi₀⟩ := hq_fail
        exact hi₀ (Set.image_mono (Ideal.pow_le_pow_right (by omega)) (hall i₀))
      -- Case split on q: either q = 0 or q ≥ 1.
      by_cases hq0 : q = 0
      · -- q = 0: hypothesis fails at all levels. Filtration is vacuous.
        -- Need unconditional decomposition via denominator-clearing.
        -- Clear denominators: find M with w^M * (x i).val n ∈ A₀ for all i.
        have h_clear : ∃ M : ℕ, ∀ i, (w : A) ^ M * (x i).val n ∈ P.A₀ :=
          (Filter.eventually_all.mpr (fun i ↦ hw_event ((x i).val n))).exists
        obtain ⟨M, hM⟩ := h_clear
        -- The scaled vector is in K₀.
        have h_scaled_ker : (fun i ↦ (⟨(w : A) ^ M * (x i).val n, hM i⟩ : ↥P.A₀)) ∈ K₀ := by
          have h_zero : P.A₀.subtype
            (∑ i : Fin l, g i * (⟨(w : A) ^ M * (x i).val n, hM i⟩ : ↥P.A₀)) = 0 := by
            simp only [map_sum, map_mul, Subring.coe_subtype]
            trans (↑w : A) ^ (N + M) * ∑ i, f i * (x i).val n
            · rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun i _ ↦ by rw [pow_add]; ring)
            · rw [hcoord n, mul_zero]
          have h_eq : ∑ i : Fin l, g i * (⟨(w : A) ^ M * (x i).val n, hM i⟩ : ↥P.A₀) = 0 := by
            ext; simpa [Subring.coe_subtype] using h_zero
          change (fun i ↦ (⟨(w : A) ^ M * (x i).val n, hM i⟩ : ↥P.A₀)) ∈ LinearMap.ker relMap₀
          rw [LinearMap.mem_ker]
          exact h_eq
        -- Decompose over s₀.
        have h_in_span : (⟨fun i ↦ (⟨(w : A) ^ M * (x i).val n, hM i⟩ : ↥P.A₀),
            h_scaled_ker⟩ : K₀) ∈ Submodule.span P.A₀ (Set.range s₀) :=
          hs₀ ▸ Submodule.mem_top
        obtain ⟨cf, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h_in_span
        have hcf_sum : (⟨fun i ↦ (⟨(w : A) ^ M * (x i).val n, hM i⟩ : ↥P.A₀),
            h_scaled_ker⟩ : K₀) = ∑ j : Fin k, cf j • s₀ j := by
          rw [← hcf, Finsupp.sum,
            Finset.sum_subset (Finset.subset_univ _)]
          intro j _ hj; rw [Finsupp.notMem_support_iff.mp hj, zero_smul]
        -- Extract component-wise equality (in A₀).
        have hcf_eq : ∀ i, (⟨(w : A) ^ M * (x i).val n, hM i⟩ : ↥P.A₀) =
            ∑ j, cf j * (s₀ j : Fin l → P.A₀) i := by
          intro i
          have := congr_arg (fun (v : K₀) ↦ (v : Fin l → P.A₀) i) hcf_sum
          simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower,
            Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
          exact this
        -- Unscale: divide by w^M (which is a unit).
        have hw_M_unit : IsUnit ((w : A) ^ M) := w.isUnit.pow M
        set c₀ := fun j ↦ ↑(hw_M_unit.unit⁻¹ : Aˣ) * P.A₀.subtype (cf j)
        refine ⟨c₀, fun i ↦ ?_, fun m hm ↦ ?_⟩
        · -- Decomposition: (x i).val n = ∑ c₀ j * s₀(j)(i)
          have h_scaled := congr_arg P.A₀.subtype (hcf_eq i)
          simp only [map_sum, map_mul, Subring.coe_subtype] at h_scaled
          -- h_scaled : w^M * (x i).val n = ∑ j, ↑(cf j) * s₀(j)(i) in A
          have : (x i).val n = ↑(hw_M_unit.unit⁻¹ : Aˣ) *
              ((w : A) ^ M * (x i).val n) := by
            rw [← mul_assoc, hw_M_unit.val_inv_mul, one_mul]
          rw [this, h_scaled, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ ↦ by
            simp only [c₀, Subring.coe_subtype]; ring)
        · -- Filtration: vacuously true since q = 0 means hypothesis fails for all m.
          exfalso
          exact hq_fail_above m (by omega) hm
      · -- q ≥ 1: use hAR_ctrl at level q - 1.
        have hq_pos : 0 < q := Nat.pos_of_ne_zero hq0
        have hq_hyp : ∀ i, (x i).val n ∈
            Subtype.val '' ((P.I ^ ((q - 1) + k₀) : Ideal P.A₀) : Set P.A₀) :=
          hq_valid (q - 1) (by omega)
        obtain ⟨c₀, hc₀_mem, hc₀_decomp⟩ := hAR_ctrl n (q - 1) hq_hyp
        refine ⟨c₀, hc₀_decomp, fun m hm j ↦ ?_⟩
        -- Need: c₀ j ∈ image(I^m).
        -- We have: c₀ j ∈ image(I^{q-1}).
        -- If m ≤ q-1: I^{q-1} ⊆ I^m, so image(I^{q-1}) ⊆ image(I^m). Done.
        -- If m ≥ q: hypothesis fails, contradiction.
        by_cases hmq : m < q
        · -- m ≤ q-1: use monotonicity
          exact Set.image_mono (Ideal.pow_le_pow_right (by omega)) (hc₀_mem j)
        · -- m ≥ q: hypothesis fails, contradiction
          exact absurd hm (hq_fail_above m (by omega))
  choose c' hc'_decomp hc'_filt using hdecomp_or_ctrl
  suffices ∃ c' : (Fin 1 →₀ ℕ) → Fin k → A,
      (∀ n i, (x i).val n =
        ∑ j, c' n j * P.A₀.subtype ((s₀ j : Fin l → P.A₀) i)) ∧
      (∀ j, (fun n ↦ c' n j) ∈ TateAlgebra A) by
    obtain ⟨c'', hc'', hrestr''⟩ := this
    refine ⟨k, fun i j ↦ P.A₀.subtype ((s₀ j : Fin l → P.A₀) i),
      fun j ↦ ⟨fun n ↦ c'' n j, hrestr'' j⟩, ?_, ?_⟩
    · intro i; apply Subtype.ext; funext n
      have hrhs : (∑ j, P.A₀.subtype ((s₀ j : Fin l → P.A₀) i) •
          (⟨fun n ↦ c'' n j, hrestr'' j⟩ : ↥(TateAlgebra A)) :
          ↥(TateAlgebra A)).val n =
        ∑ j, P.A₀.subtype ((s₀ j : Fin l → P.A₀) i) * c'' n j := by
        rw [show (∑ j, P.A₀.subtype ((s₀ j : Fin l → P.A₀) i) •
            (⟨fun n ↦ c'' n j, hrestr'' j⟩ : ↥(TateAlgebra A))).val =
          (TateAlgebra A).subtype (∑ j, P.A₀.subtype ((s₀ j : Fin l → P.A₀) i) •
            (⟨fun n ↦ c'' n j, hrestr'' j⟩ : ↥(TateAlgebra A))) from rfl,
          map_sum]
        simp only [Subring.coe_subtype]
        trans ∑ j, (P.A₀.subtype ((s₀ j : Fin l → P.A₀) i) •
            (⟨fun n ↦ c'' n j, hrestr'' j⟩ : ↥(TateAlgebra A))).val n
        · exact Fintype.sum_apply n
            (fun j ↦ (P.A₀.subtype ((s₀ j : Fin l → P.A₀) i) •
              (⟨fun n ↦ c'' n j, hrestr'' j⟩ : ↥(TateAlgebra A))).val)
        · exact Finset.sum_congr rfl (fun j _ ↦
            TateAlgebra.smul_val_eq _ _ n)
      rw [hrhs, hc'' n i]
      exact Finset.sum_congr rfl (fun j _ ↦ by ring)
    · exact fun j ↦ hsyz j
  -- Prove the suffices using c' from the diagonal construction.
  refine ⟨c', hc'_decomp, fun j ↦ ?_⟩
  -- Goal: (fun n => c' n j) ∈ TateAlgebra A
  -- Show Tendsto (c'(·)(j)) cofinite (nhds 0) using the filtration property hc'_filt.
  change MvPowerSeries.IsRestricted (fun n ↦ c' n j)
  rw [MvPowerSeries.IsRestricted, P.hasBasis_nhds_zero.tendsto_right_iff]
  intro m _
  rw [Filter.eventually_cofinite]
  -- Goal: {n | c' n j ∉ image(P.I^m)}.Finite
  -- By hc'_filt: if all (x i).val n ∈ image(I^{m+k₀}), then c' n j ∈ image(I^m).
  -- So {n | c' n j ∉ image(I^m)} ⊆ {n | ∃ i, (x i).val n ∉ image(I^{m+k₀})}.
  apply Set.Finite.subset (Set.finite_iUnion (fun i : Fin l ↦ by
      have hxi := (x i).prop
      change MvPowerSeries.IsRestricted (x i).val at hxi
      rw [MvPowerSeries.IsRestricted] at hxi
      have := P.hasBasis_nhds_zero.tendsto_right_iff.mp hxi (m + k₀) trivial
      rwa [Filter.eventually_cofinite] at this))
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  by_contra h_all; push Not at h_all
  exact hn (hc'_filt n m h_all j)

end TateAlgebraFlat

/-! ### Quotient flatness via universal saturation (Lemma 8.31(2), general case)

We prove that `A⟨X⟩/(f-X)` and `A⟨X⟩/(1-fX)` are flat over `A` for noetherian
nonarchimedean topological rings, without requiring `[DiscreteTopology A]`.

The proof proceeds in three steps:

1. **Abstract engine** (`Module.Flat.quotient_of_flat_of_saturated`): If `S` is a flat
   `R`-algebra, `g ∈ S` is regular, and for every ideal `I` of `R` the submodule `I·S` is
   `g`-saturated (`g*s ∈ I·S → s ∈ I·S`), then `S/(g)` is flat over `R`. The proof uses the
   equational criterion: lift a relation from the quotient, apply saturation to adjust the
   lift, then use flatness of `S` to decompose.

2. **Ascending chain argument** (`noeth_mem_ideal_of_mul_shift`): In a noetherian ring, if
   `a*x₀ ∈ I` and `xₖ ≡ a*xₖ₊₁ (mod I)` for all `k`, then `x₀ ∈ I`. This generalises the
   existing `noeth_zero_of_mul_shift` from `I = 0` to arbitrary ideals by passing to `A/I`.

3. **Saturation for `f-X` and `1-fX`** (`fSubX_saturated`, `oneSubfX_saturated`): The
   coefficient equations from `(f-X)*h ∈ I·A⟨X⟩` yield exactly the hypotheses of the
   ascending chain lemma, forcing all coefficients of `h` into `I`.

References: [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 8.31(2)
-/

/-! #### Step 1: Abstract flat quotient engine -/

/-- **Flat quotient by universally saturated element.** If `S` is a flat `R`-algebra,
`g ∈ S` is regular (non-zero-divisor), and for every ideal `I` of `R` the extended ideal
`I·S = Ideal.map (algebraMap R S) I` is `g`-saturated (`g*s ∈ I·S → s ∈ I·S`), then the
quotient `S/(g)` is flat over `R`.

The proof uses the equational criterion. Given `∑ fᵢ • x̄ᵢ = 0` in `S/(g)`:
1. Lift `x̄ᵢ` to `xᵢ ∈ S`; then `∑ fᵢ xᵢ = gw` for some `w`.
2. By saturation with `I = ⟨f₁,…,fₗ⟩`: write `w = ∑ fᵢ cᵢ`.
3. Then `∑ fᵢ (xᵢ - g cᵢ) = 0` in `S`; apply flatness of `S`.
4. Project witnesses to `S/(g)`.

This is the abstract engine behind Lemma 8.31(2) of Wedhorn. -/
theorem Module.Flat.quotient_of_flat_of_saturated
    {R : Type u} [CommRing R]
    {S : Type u} [CommRing S] [Algebra R S] [Module.Flat R S]
    {g : S} (_hreg : ∀ x : S, g * x = 0 → x = 0)
    (hsat : ∀ (I : Ideal R) (s : S),
      g * s ∈ Ideal.map (algebraMap R S) I → s ∈ Ideal.map (algebraMap R S) I) :
    Module.Flat R (S ⧸ Ideal.span ({g} : Set S)) := by
  set Q := S ⧸ Ideal.span ({g} : Set S)
  set π := Ideal.Quotient.mk (Ideal.span ({g} : Set S))
  apply Module.Flat.of_forall_isTrivialRelation
  intro l f x hfx
  -- Step 1: Lift x̄ᵢ from Q to S.
  choose x' hx' using fun i ↦ Ideal.Quotient.mk_surjective (x i)
  -- Step 2: ∑ fᵢ • x'ᵢ maps to 0 in Q, so it lies in Ideal.span {g}.
  have hπ_sum : π (∑ i, f i • x' i) = 0 := by
    rw [map_sum]
    convert hfx using 1
    congr 1; ext i
    change π (f i • x' i) = f i • x i
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← RingHom.comp_apply,
      show (π : S →+* Q).comp (algebraMap R S) = algebraMap R Q from rfl, hx']
  have hsum_mem : ∑ i, f i • x' i ∈ Ideal.span ({g} : Set S) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hπ_sum
  -- Extract: w * g = ∑ fᵢ • x'ᵢ for some w.
  rw [Ideal.mem_span_singleton'] at hsum_mem
  obtain ⟨w, hw⟩ := hsum_mem
  -- Step 3: g * w ∈ Ideal.map (algebraMap R S) (Ideal.span (Set.range f)).
  set J := Ideal.span (Set.range f)
  have hgw_mem : g * w ∈ Ideal.map (algebraMap R S) J := by
    rw [show g * w = w * g from mul_comm g w, hw]
    apply Ideal.sum_mem
    intro i _
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _
      (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self i)))
  -- Step 4: By saturation, w ∈ Ideal.map (algebraMap R S) J.
  have hw_mem := hsat J w hgw_mem
  -- Decompose w: Ideal.map (algebraMap R S) J = Ideal.span (range (algebraMap R S ∘ f)).
  have hJ_map : Ideal.map (algebraMap R S) J = Ideal.span (Set.range (algebraMap R S ∘ f)) := by
    rw [Ideal.map_span]; congr 1; exact (Set.range_comp _ _).symm
  rw [hJ_map] at hw_mem
  rw [Ideal.mem_span_range_iff_exists_fun] at hw_mem
  obtain ⟨c, hc⟩ := hw_mem
  -- So w = ∑ cᵢ * algebraMap(fᵢ).
  -- Step 5: Set x''ᵢ = x'ᵢ - g * cᵢ. Then ∑ fᵢ • x''ᵢ = 0 in S.
  set x'' : Fin l → S := fun i ↦ x' i - g * c i
  have hrel : ∑ i, f i • x'' i = 0 := by
    simp only [x'', smul_sub, Finset.sum_sub_distrib]
    suffices h : ∑ i, f i • (g * c i) = ∑ i, f i • x' i by
      rw [h, sub_self]
    rw [← hw, show w * g = g * w from mul_comm w g,
      show g * w = g * (∑ i, c i * (algebraMap R S ∘ f) i) from by rw [hc]]
    rw [Finset.mul_sum]
    congr 1; ext i
    rw [Algebra.smul_def, Function.comp_apply]; ring
  -- Step 6: Apply flatness of S to get trivial relation witnesses.
  have hrel' : ∑ i : Fin l, f i • x'' i = (0 : S) := hrel
  obtain ⟨k, a, y, ha, hsyz⟩ :=
    (Module.Flat.iff_forall_isTrivialRelation.mp ‹Module.Flat R S›) hrel'
  -- Step 7: Project to Q.
  -- x̄ᵢ = π(x'ᵢ) = π(x''ᵢ + g * cᵢ) = π(x''ᵢ) since π(g) = 0.
  -- x''ᵢ = ∑ⱼ aᵢⱼ • yⱼ, so π(x''ᵢ) = ∑ⱼ aᵢⱼ • π(yⱼ).
  have hπg : π g = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton g))
  refine ⟨k, a, fun j ↦ π (y j), fun i ↦ ?_, hsyz⟩
  -- x i = π(x'' i)
  have hxi_eq : x i = π (x'' i) := by
    -- x'' i = x' i - g * c i. Since g * c i ∈ Ideal.span {g},
    -- π(x' i) = π(x' i - g * c i), so x i = π(x'' i).
    change x i = π (x' i - g * c i)
    have hgci : g * c i ∈ Ideal.span ({g} : Set S) :=
      Ideal.mem_span_singleton'.mpr ⟨c i, mul_comm (c i) g⟩
    -- π(x' i - g * c i) = π(x' i) because x' i ≡ x' i - g*ci (mod span {g})
    have : (Ideal.Quotient.mk (Ideal.span ({g} : Set S))) (x' i - g * c i) =
           (Ideal.Quotient.mk (Ideal.span ({g} : Set S))) (x' i) := by
      rw [Ideal.Quotient.eq]
      -- Goal: (x' i - g * c i) - x' i ∈ Ideal.span {g}
      -- This is -(g * c i), which is in the ideal.
      have : x' i - g * c i - x' i = -(g * c i) := by ring
      rw [this]
      exact (Ideal.span ({g} : Set S)).neg_mem hgci
    rw [this, hx']
  -- π(x'' i) = π(∑ a_ij • y_j) = ∑ a_ij • π(y_j)
  -- The smul from IsTrivialRelation uses Module.toDistribSMul, same as Algebra.toModule.
  -- Use calc to handle this explicitly.
  calc x i = π (x'' i) := hxi_eq
    _ = π (∑ j, a i j • y j) := congr_arg π (ha i)
    _ = ∑ j, π (a i j • y j) := map_sum π _ _
    _ = ∑ j, a i j • π (y j) := by
        exact Finset.sum_congr rfl (fun j _ ↦
          map_smul (Ideal.Quotient.mkₐ R _).toLinearMap (a i j) (y j))

/-! #### Step 2: Modular ascending chain lemma -/

/-- **Ascending chain lemma modulo an ideal.** In a noetherian ring, if `a * x₀ ∈ I`
and `xₖ ≡ a * xₖ₊₁ (mod I)` for all `k`, then `x₀ ∈ I`.

This generalises `noeth_zero_of_mul_shift` (which is the case `I = 0`) by passing to
the quotient ring `A/I`, which is noetherian since `A` is. -/
theorem noeth_mem_ideal_of_mul_shift {R : Type u} [CommRing R] [IsNoetherianRing R]
    (a : R) (I : Ideal R) (x : ℕ → R)
    (h0 : a * x 0 ∈ I) (hstep : ∀ k, x k - a * x (k + 1) ∈ I) : x 0 ∈ I := by
  -- Reduce to noeth_zero_of_mul_shift in A/I.
  -- In A/I: ā * x̄₀ = 0 and x̄ₖ = ā * x̄ₖ₊₁, so x̄₀ = 0 by the ascending chain argument.
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  haveI : IsNoetherianRing (R ⧸ I) := Ideal.Quotient.isNoetherianRing I
  set mk := Ideal.Quotient.mk I
  -- Set up notation for the quotient
  set a' := mk a with ha'_def
  -- Quotient hypotheses
  have h0' : a' * mk (x 0) = 0 := by
    rw [← map_mul]; exact Ideal.Quotient.eq_zero_iff_mem.mpr h0
  have hstep' : ∀ k, mk (x k) = a' * mk (x (k + 1)) := by
    intro k
    have hmem := hstep k
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hmem
    rw [map_sub, map_mul] at hmem
    exact sub_eq_zero.mp hmem
  -- Apply noeth_zero_of_mul_shift in A/I (inlined since it is private)
  -- Power relation: mk(x 0) = a'^k * mk(x k)
  have hpow : ∀ k, mk (x 0) = a' ^ k * mk (x k) := by
    intro k; induction k with
    | zero => simp only [pow_zero, one_mul]
    | succ k ih => rw [ih, hstep' k, pow_succ, mul_assoc]
  -- Annihilation: a'^(k+1) * mk(x k) = 0
  have hann : ∀ k, a' ^ (k + 1) * mk (x k) = 0 := by
    intro k
    have : a' ^ (k + 1) * mk (x k) = a' * (a' ^ k * mk (x k)) := by ring
    rw [this, ← hpow k, h0']
  -- Ascending chain of annihilator submodules in A/I: ann(a'^n) = ker(a'^n • ·)
  -- Use LinearMap.ker of left-multiplication by a'^n
  let mulPow (n : ℕ) : (R ⧸ I) →ₗ[R ⧸ I] (R ⧸ I) :=
    LinearMap.lsmul (R ⧸ I) (R ⧸ I) (a' ^ n)
  have chain_monotone : Monotone (fun n ↦ LinearMap.ker (mulPow n)) := by
    intro m n hmn b hb
    simp only [mulPow, LinearMap.mem_ker, LinearMap.lsmul_apply, smul_eq_mul] at hb ⊢
    have key : a' ^ n * b = a' ^ (n - m) * (a' ^ m * b) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hmn]
    rw [key, hb, mul_zero]
  let chain : ℕ →o Submodule (R ⧸ I) (R ⧸ I) := ⟨_, chain_monotone⟩
  obtain ⟨K, hK⟩ :=
    (monotone_stabilizes_iff_noetherian (R := R ⧸ I) (M := R ⧸ I)).mpr inferInstance chain
  have hxK_mem : mk (x K) ∈ chain (K + 1) := by
    change mk (x K) ∈ LinearMap.ker (mulPow (K + 1))
    rw [LinearMap.mem_ker]
    change a' ^ (K + 1) • mk (x K) = 0
    rw [smul_eq_mul]; exact hann K
  have hxK : a' ^ K * mk (x K) = 0 := by
    have hmem : mk (x K) ∈ chain K := hK (K + 1) (by omega) ▸ hxK_mem
    have hmem' : mk (x K) ∈ LinearMap.ker (mulPow K) := hmem
    rw [LinearMap.mem_ker] at hmem'
    change a' ^ K • mk (x K) = 0 at hmem'
    rwa [smul_eq_mul] at hmem'
  rw [hpow K, hxK]

/-! #### Step 3: Saturation for f-X and 1-fX -/

section QuotientFlatnessGeneral

variable {A : Type u} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [IsNoetherianRing A]

namespace TateAlgebra

/-- All coefficients of elements in the extended ideal `I · A⟨X⟩` lie in `I`.
This uses `span_induction` with the predicate strengthened to all coefficients
simultaneously, and the convolution formula for the scalar multiplication case. -/
theorem forall_coeff_mem_of_mem_ideal_map (I : Ideal A) (g : ↥(TateAlgebra A))
    (hg : g ∈ Ideal.map (algebraMap A ↥(TateAlgebra A)) I) :
    ∀ n, coeff n g ∈ I := by
  -- Use span_induction with predicate "all coefficients in I".
  -- The dependent predicate ignores the membership proof.
  refine Submodule.span_induction
    (p := fun (g' : ↥(TateAlgebra A)) _ ↦ ∀ n, coeff n g' ∈ I)
    ?_ ?_ ?_ ?_ hg
  · -- Generators: algebraMap a for a ∈ I.
    rintro _ ⟨a, ha, rfl⟩ n
    by_cases hn : n = 0
    · subst hn; simp only [coeff, toIndex_zero]; exact ha
    · simp only [coeff, toIndex]
      change MvPowerSeries.coeff (Finsupp.single 0 n) (algebraMap A _ a) ∈ I
      rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C]
      split
      · next h => exact absurd (Finsupp.single_eq_zero.mp h) hn
      · exact I.zero_mem
  · -- Zero
    intro n; simp only [coeff, map_zero, ZeroMemClass.coe_zero]; exact I.zero_mem
  · -- Addition
    intro g₁ g₂ _ _ ih₁ ih₂ n
    change coeff n (g₁ + g₂) ∈ I
    rw [show coeff n (g₁ + g₂) = coeff n g₁ + coeff n g₂ from by
      simp only [coeff, map_add, Subring.coe_add]]
    exact I.add_mem (ih₁ n) (ih₂ n)
  · -- Scalar multiplication: coeff n (r * g'') ∈ I when all coeff of g'' are in I.
    intro r g'' _ ih n
    change coeff n (r • g'') ∈ I
    change coeff n (r * g'') ∈ I
    simp only [coeff, toIndex]
    change MvPowerSeries.coeff (Finsupp.single 0 n) (r.val * g''.val) ∈ I
    rw [MvPowerSeries.coeff_mul]
    apply Ideal.sum_mem
    intro ⟨s₁, s₂⟩ _hmem_anti
    apply I.mul_mem_left
    -- s₂ is a Fin 1 →₀ ℕ, so s₂ = Finsupp.single 0 (s₂ 0)
    have hs₂ : s₂ = Finsupp.single 0 (s₂ 0) := by
      apply Finsupp.ext
      intro i
      simp [show i = 0 from Fin.ext_iff.mpr (Nat.lt_one_iff.mp i.isLt)]
    rw [hs₂]; exact ih (s₂ 0)

/-! #### Assembling: quotient flatness (general case) -/

variable [IsTopologicalRing A] [T2Space A] [IsTateRing A]

/-- A restricted power series with all coefficients in `I` belongs to `Ideal.map I`
in the Tate algebra. This is the reverse direction of `forall_coeff_mem_of_mem_ideal_map`.

The proof uses the Artin-Rees lemma via the pair of definition: for each coefficient level `m`,
the Artin-Rees argument gives controlled decompositions over generators of `I`, which assemble
into restricted power series witnesses via the diagonal construction. -/
theorem mem_ideal_map_of_forall_coeff_mem (I : Ideal A)
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (h : ↥(TateAlgebra A)) (hcoeffs : ∀ n, coeff n h ∈ I) :
    h ∈ Ideal.map (algebraMap A ↥(TateAlgebra A)) I := by
  classical
  -- Helper: h.val n ∈ I for every multi-index n.
  have hval_mem_I : ∀ n : Fin 1 →₀ ℕ, h.val n ∈ I := by
    intro n; rw [eq_toIndex n]; exact hcoeffs (n 0)
  -- Step 1: Set up I₀ = I ∩ A₀ and its generators.
  set I₀ : Ideal P.A₀ := I.comap P.A₀.subtype
  obtain ⟨numG, g₀, hg₀⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp
      (IsNoetherian.noetherian (⊤ : Submodule P.A₀ I₀))
  -- Step 2: Apply Artin-Rees: P.I^n ∩ I₀ stabilizes.
  obtain ⟨k₁, hAR⟩ := Ideal.exists_pow_inf_eq_pow_smul P.I
    (I₀.restrictScalars P.A₀ : Submodule P.A₀ P.A₀)
  -- Step 3: Get pseudo-uniformizer.
  obtain ⟨w, hw_nil⟩ := ‹IsTateRing A›.exists_topologicallyNilpotent_unit
  have hw_event : ∀ a : A, ∀ᶠ n in Filter.atTop, (w : A) ^ n * a ∈ P.A₀ :=
    fun a ↦ hw_nil.eventually ((P.isOpen.preimage (continuous_mul_const a)).mem_nhds
      (by simp [P.A₀.zero_mem]))
  -- Step 4: Each generator maps to I.
  have hg₀_in_I : ∀ q : Fin numG, P.A₀.subtype (g₀ q : I₀).val ∈ I :=
    fun q ↦ (g₀ q : I₀).prop
  -- Step 5: The diagonal decomposition.
  have hdecomp_ctrl : ∀ n : Fin 1 →₀ ℕ,
      ∃ c : Fin numG → A,
        (h.val n = ∑ q, P.A₀.subtype (g₀ q : I₀).val * c q) ∧
        (∀ l, h.val n ∈ Subtype.val '' ((P.I ^ (l + k₁) : Ideal P.A₀) : Set P.A₀) →
          ∀ q, c q ∈ Subtype.val '' ((P.I ^ l : Ideal P.A₀) : Set P.A₀)) := by
    intro n
    by_cases h_all :
        ∀ l, h.val n ∈ Subtype.val '' ((P.I ^ (l + k₁) : Ideal P.A₀) : Set P.A₀)
    · -- All levels valid ⟹ h.val n = 0.
      have h_zero : h.val n = 0 := by
        by_contra hne
        obtain ⟨U, _, hU_open, _, h0U, hxV, hUV⟩ := t2_separation (Ne.symm hne)
        obtain ⟨p, _, hp⟩ := P.hasBasis_nhds_zero.mem_iff.mp (hU_open.mem_nhds h0U)
        exact Set.disjoint_left.mp hUV (hp (Set.image_mono
          (Ideal.pow_le_pow_right (by omega) :
            (↑(P.I ^ (p + k₁)) : Set ↥P.A₀) ⊆ ↑(P.I ^ p))
          (h_all p))) hxV
      exact ⟨0, by simp [h_zero], fun l _ q ↦ ⟨0, (P.I ^ l).zero_mem, by simp⟩⟩
    · push Not at h_all
      obtain ⟨l_fail, hl_fail⟩ := h_all
      have h_fail_ex : ∃ l, h.val n ∉
          Subtype.val '' ((P.I ^ (l + k₁) : Ideal P.A₀) : Set P.A₀) :=
        ⟨l_fail, hl_fail⟩
      set qn := Nat.find h_fail_ex
      have hqn_fail := Nat.find_spec h_fail_ex
      have hqn_valid : ∀ l < qn, h.val n ∈
          Subtype.val '' ((P.I ^ (l + k₁) : Ideal P.A₀) : Set P.A₀) :=
        fun l hl ↦ Decidable.not_not.mp (Nat.find_min h_fail_ex hl)
      have hqn_fail_above : ∀ l, qn ≤ l →
          h.val n ∉ Subtype.val '' ((P.I ^ (l + k₁) : Ideal P.A₀) : Set P.A₀) :=
        fun l hl hmem ↦ hqn_fail (Set.image_mono (Ideal.pow_le_pow_right (by omega)) hmem)
      by_cases hq0 : qn = 0
      · -- qn = 0: hypothesis fails at all levels. Use arbitrary decomposition.
        obtain ⟨M, hM⟩ := (hw_event (h.val n)).exists
        have hM_I₀ : ⟨(w : A) ^ M * h.val n, hM⟩ ∈ I₀ := by
          change P.A₀.subtype ⟨_, hM⟩ ∈ I; simp [I.mul_mem_left _ (hval_mem_I n)]
        have h_in_sp : (⟨⟨_, hM⟩, hM_I₀⟩ : I₀) ∈
            Submodule.span P.A₀ (Set.range g₀) := hg₀ ▸ Submodule.mem_top
        obtain ⟨cf, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h_in_sp
        have hcf_sum : (⟨⟨(w : A) ^ M * h.val n, hM⟩, hM_I₀⟩ : I₀) =
            ∑ q : Fin numG, cf q • g₀ q := by
          rw [← hcf, Finsupp.sum, Finset.sum_subset (Finset.subset_univ _)]
          intro q _ hq; rw [Finsupp.notMem_support_iff.mp hq, zero_smul]
        have hcf_A : (w : A) ^ M * h.val n =
            ∑ q, P.A₀.subtype ((g₀ q : I₀).val) * P.A₀.subtype (cf q) := by
          have h' := congr_arg (fun (x : I₀) ↦ P.A₀.subtype x.val) hcf_sum
          simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower,
            map_sum, smul_eq_mul, map_mul, Subring.coe_subtype] at h'
          rw [h']; congr 1; ext q
          simp only [Subring.coe_subtype]; ring
        have hw_unit : IsUnit ((w : A) ^ M) := w.isUnit.pow M
        refine ⟨fun q ↦ ↑(hw_unit.unit⁻¹ : Aˣ) * P.A₀.subtype (cf q),
          ?_, fun l hl ↦ absurd hl (hqn_fail_above l (by omega))⟩
        have hinv : h.val n = ↑(hw_unit.unit⁻¹ : Aˣ) * ((w : A) ^ M * h.val n) := by
          rw [← mul_assoc, hw_unit.val_inv_mul, one_mul]
        rw [hinv, hcf_A, Finset.mul_sum]
        congr 1; ext q; ring
      · -- qn ≥ 1: use AR at level qn - 1.
        have hqn_pos : 0 < qn := Nat.pos_of_ne_zero hq0
        obtain ⟨y, hy_mem, hy_eq⟩ := hqn_valid (qn - 1) (by omega)
        have hy_I₀ : y ∈ I₀ := show P.A₀.subtype y ∈ I by
          change (↑y : A) ∈ I; rw [hy_eq]; exact hval_mem_I n
        have hy_inter : y ∈ (P.I ^ ((qn - 1) + k₁) • ⊤ ⊓
            I₀.restrictScalars P.A₀ : Submodule P.A₀ P.A₀) := by
          refine Submodule.mem_inf.mpr ⟨?_, hy_I₀⟩
          rw [Ideal.smul_top_eq_map (P.I ^ ((qn - 1) + k₁))]
          exact Ideal.mem_map_of_mem _ hy_mem
        rw [hAR ((qn - 1) + k₁) (by omega),
          show (qn - 1) + k₁ - k₁ = qn - 1 from by omega] at hy_inter
        have hy_smul : y ∈ (P.I ^ (qn - 1) • I₀.restrictScalars P.A₀ :
            Submodule P.A₀ P.A₀) :=
          Submodule.smul_mono le_rfl inf_le_right hy_inter
        -- Decompose y over generators of I₀ with P.I^{qn-1}-coefficients.
        have hy_decomp : ∃ c₀ : Fin numG → P.A₀,
            (∀ j, c₀ j ∈ P.I ^ (qn - 1)) ∧
            y = ∑ j, c₀ j * (g₀ j : I₀).val := by
          refine Submodule.smul_induction_on (p := fun v ↦
              ∃ c₀ : Fin numG → P.A₀,
                (∀ j, c₀ j ∈ P.I ^ (qn - 1)) ∧
                v = ∑ j, c₀ j * (g₀ j : I₀).val)
            hy_smul (fun a ha v hv ↦ ?_) (fun u v ⟨cu, hcu, heu⟩ ⟨cv, hcv, hev⟩ ↦ ?_)
          · -- Base: a ∈ P.I^{qn-1}, v ∈ I₀.
            have hv_sp : (⟨v, hv⟩ : I₀) ∈ Submodule.span P.A₀ (Set.range g₀) :=
              hg₀ ▸ Submodule.mem_top
            obtain ⟨cf, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hv_sp
            have hv_eq : v = ∑ j : Fin numG, (cf j : P.A₀) * (g₀ j : I₀).val := by
              have h' := congr_arg (fun (x : I₀) ↦ x.val) (show (⟨v, hv⟩ : I₀) =
                ∑ j, cf j • g₀ j from by
                  rw [← hcf, Finsupp.sum, Finset.sum_subset (Finset.subset_univ _)]
                  intro j _ hj; rw [Finsupp.notMem_support_iff.mp hj, zero_smul])
              simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, smul_eq_mul] at h'
              exact h'
            refine ⟨fun j ↦ a * cf j, fun j ↦ Ideal.mul_mem_right _ _ ha, ?_⟩
            rw [show a • v = a * v from smul_eq_mul _ _, hv_eq, Finset.mul_sum]
            exact Finset.sum_congr rfl (fun j _ ↦ by ring)
          · exact ⟨fun j ↦ cu j + cv j,
              fun j ↦ (P.I ^ (qn - 1)).add_mem (hcu j) (hcv j), by
              rw [heu, hev, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl (fun j _ ↦ by ring)⟩
        obtain ⟨c₀, hc₀_mem, hc₀_eq⟩ := hy_decomp
        refine ⟨fun j ↦ P.A₀.subtype (c₀ j), ?_, fun l hl j ↦ ?_⟩
        · rw [← hy_eq]
          have := congr_arg P.A₀.subtype hc₀_eq
          simp only [map_sum, map_mul, Subring.coe_subtype] at this
          rw [this]; congr 1; ext j; simp only [Subring.coe_subtype]; ring
        · by_cases hlq : l < qn
          · exact ⟨c₀ j, Ideal.pow_le_pow_right (by omega) (hc₀_mem j), rfl⟩
          · exact absurd hl (hqn_fail_above l (by omega))
  -- Step 6: Choose the decomposition for all n.
  choose c' hc'_decomp hc'_filt using hdecomp_ctrl
  -- Step 7: Restrictedness.
  have hrestr : ∀ q : Fin numG, MvPowerSeries.IsRestricted (fun n ↦ c' n q) := by
    intro q
    rw [MvPowerSeries.IsRestricted, P.hasBasis_nhds_zero.tendsto_right_iff]
    intro l _; rw [Filter.eventually_cofinite]
    apply Set.Finite.subset (by
      have := P.hasBasis_nhds_zero.tendsto_right_iff.mp
        (show Tendsto h.val cofinite (nhds 0) from h.prop) (l + k₁) trivial
      rwa [Filter.eventually_cofinite] at this)
    intro n hn; simp only [Set.mem_setOf_eq] at hn ⊢
    intro hmem; exact hn (hc'_filt n l hmem q)
  -- Step 8: Assemble.
  set g : Fin numG → ↥(TateAlgebra A) := fun q ↦ ⟨fun n ↦ c' n q, hrestr q⟩
  have hmem : h = ∑ q : Fin numG,
      algebraMap A ↥(TateAlgebra A) (P.A₀.subtype (g₀ q : I₀).val) * g q := by
    apply Subtype.ext; funext n
    -- LHS = h.val n = ∑ q, ↑(g₀ q) * c' n q (from hc'_decomp)
    -- RHS = ∑ q, (algebraMap(↑(g₀ q)) * g q).val n = ∑ q, ↑(g₀ q) * c' n q
    have lhs := hc'_decomp n
    -- Unfold RHS
    have rhs : (∑ q : Fin numG,
        algebraMap A ↥(TateAlgebra A) (P.A₀.subtype ↑↑(g₀ q)) * g q :
        ↥(TateAlgebra A)).val n =
        ∑ q, P.A₀.subtype (g₀ q : I₀).val * c' n q := by
      trans ∑ q, (algebraMap A ↥(TateAlgebra A) (P.A₀.subtype ↑↑(g₀ q)) * g q :
        ↥(TateAlgebra A)).val n
      · change (TateAlgebra A).subtype (∑ q, _) n = _
        rw [map_sum]; exact Fintype.sum_apply n _
      · congr 1; ext q
        change (algebraMap A (MvPowerSeries (Fin 1) A) (P.A₀.subtype ↑↑(g₀ q)) *
          (g q).val) n = _
        rw [MvPowerSeries.algebraMap_apply]
        change MvPowerSeries.coeff n
          (MvPowerSeries.C (P.A₀.subtype ↑↑(g₀ q)) * (g q).val) = _
        rw [MvPowerSeries.coeff_C_mul]
        rfl
    rw [lhs, rhs]
  rw [hmem]
  exact Ideal.sum_mem _ (fun q _ ↦
    Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hg₀_in_I q)))

theorem fSubX_saturated
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (f : A) (I : Ideal A)
    (h : ↥(TateAlgebra A))
    (hmem : (algebraMap A ↥(TateAlgebra A) f - X) * h ∈
      Ideal.map (algebraMap A ↥(TateAlgebra A)) I) :
    h ∈ Ideal.map (algebraMap A ↥(TateAlgebra A)) I := by
  -- Step 1: Extract coefficient information from the hypothesis.
  have hcoeffs_prod : ∀ n, coeff n ((algebraMap A _ f - X) * h) ∈ I :=
    forall_coeff_mem_of_mem_ideal_map I _ hmem
  -- Step 2: Derive the coefficient equations for h.
  -- coeff n ((f - X) * h) = f * coeff n h - coeff n (X * h)
  have hcoeff_eq : ∀ n, f * coeff n h - coeff n (X * h) ∈ I := by
    intro n
    have h1 := hcoeffs_prod n
    rw [sub_mul, coeff_sub, coeff_algebraMap_mul] at h1
    exact h1
  -- coeff 0 (X * h) = 0, so f * coeff 0 h ∈ I
  have h0 : f * coeff 0 h ∈ I := by
    have := hcoeff_eq 0; rw [coeff_zero_X_mul, sub_zero] at this; exact this
  -- coeff (n+1) (X * h) = coeff n h, so f * coeff (n+1) h - coeff n h ∈ I
  -- i.e., coeff n h - f * coeff (n+1) h ∈ I
  have hstep : ∀ n, coeff n h - f * coeff (n + 1) h ∈ I := by
    intro n
    have h1 := hcoeff_eq (n + 1); rw [coeff_succ_X_mul] at h1
    -- h1 : f * coeff (n + 1) h - coeff n h ∈ I
    have : -(f * coeff (n + 1) h - coeff n h) ∈ I := I.neg_mem h1
    rwa [neg_sub] at this
  -- Step 3: Apply the ascending chain lemma to get coeff 0 h ∈ I.
  have hcoeff0 : coeff 0 h ∈ I := noeth_mem_ideal_of_mul_shift f I (fun n ↦ coeff n h) h0 hstep
  -- Step 4: By induction, ALL coefficients of h are in I.
  -- Once coeff 0 h ∈ I, from coeff 0 h - f * coeff 1 h ∈ I we get f * coeff 1 h ∈ I.
  -- Apply the ascending chain starting from coeff 1 h to get coeff 1 h ∈ I. Etc.
  have hall : ∀ n, coeff n h ∈ I := by
    intro n; induction n with
    | zero => exact hcoeff0
    | succ n ih =>
      -- From ih: coeff n h ∈ I, and hstep n: coeff n h - f * coeff (n+1) h ∈ I.
      -- So f * coeff (n+1) h = coeff n h - (coeff n h - f * coeff (n+1) h) ∈ I.
      have hf_succ : f * coeff (n + 1) h ∈ I := by
        have := I.sub_mem ih (hstep n)
        rwa [sub_sub_cancel] at this
      -- Apply ascending chain starting from coeff (n+1) h.
      exact noeth_mem_ideal_of_mul_shift f I (fun k ↦ coeff (n + 1 + k) h)
        (by simp only [Nat.add_zero]; exact hf_succ)
        (fun k ↦ by
          change coeff (n + 1 + k) h - f * coeff (n + 1 + (k + 1)) h ∈ I
          rw [show n + 1 + (k + 1) = (n + 1 + k) + 1 from by omega]
          exact hstep (n + 1 + k))
  -- Step 5: Conclude h ∈ Ideal.map I.
  exact mem_ideal_map_of_forall_coeff_mem I P h hall

/-- The element `1 - f·X` is universally saturated in `A⟨X⟩` over noetherian `A`.

Similar coefficient analysis as `fSubX_saturated`: the equations from `(1-fX)*h ∈ I·A⟨X⟩`
give `coeff 0 h ∈ I` directly and `coeff (n+1) h - f * coeff n h ∈ I`, which by induction
forces all coefficients into `I`. -/
theorem oneSubfX_saturated
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (f : A) (I : Ideal A)
    (h : ↥(TateAlgebra A))
    (hmem : (1 - algebraMap A ↥(TateAlgebra A) f * X) * h ∈
      Ideal.map (algebraMap A ↥(TateAlgebra A)) I) :
    h ∈ Ideal.map (algebraMap A ↥(TateAlgebra A)) I := by
  -- Step 1: Extract coefficient information.
  have hcoeffs_prod : ∀ n, coeff n ((1 - algebraMap A _ f * X) * h) ∈ I :=
    forall_coeff_mem_of_mem_ideal_map I _ hmem
  -- Step 2: Coefficient equations.
  -- (1 - fX) * h = h - fX * h, so coeff n = coeff n h - f * coeff n (X * h)
  have hcoeff_eq : ∀ n, coeff n h - f * coeff n (X * h) ∈ I := by
    intro n
    have h1 := hcoeffs_prod n
    rw [sub_mul, one_mul, mul_assoc, coeff_sub, coeff_algebraMap_mul] at h1
    exact h1
  -- coeff 0 h - f * 0 = coeff 0 h ∈ I
  have h0 : coeff 0 h ∈ I := by
    have := hcoeff_eq 0; rw [coeff_zero_X_mul, mul_zero, sub_zero] at this; exact this
  -- coeff (n+1) h - f * coeff n h ∈ I
  have hstep : ∀ n, coeff (n + 1) h - f * coeff n h ∈ I := by
    intro n; have := hcoeff_eq (n + 1); rwa [coeff_succ_X_mul] at this
  -- Step 3: By induction, all coefficients of h are in I.
  have hall : ∀ n, coeff n h ∈ I := by
    intro n; induction n with
    | zero => exact h0
    | succ n ih =>
      -- coeff (n+1) h = f * coeff n h + (coeff (n+1) h - f * coeff n h) ∈ I
      have hfn : f * coeff n h ∈ I := I.mul_mem_left f ih
      have hdiff : coeff (n + 1) h - f * coeff n h ∈ I := hstep n
      have : coeff (n + 1) h = f * coeff n h + (coeff (n + 1) h - f * coeff n h) := by ring
      rw [this]; exact I.add_mem hfn hdiff
  exact mem_ideal_map_of_forall_coeff_mem I P h hall

/-- `A⟨X⟩/(f-X)` is flat over noetherian `A` (Lemma 8.31(2), general case).

The proof combines:
- `tateAlgebra_flat`: `A⟨X⟩` is flat over `A`
- `mul_fSubX_regular`: `f-X` is regular on `A⟨X⟩`
- `fSubX_saturated`: universal saturation of `f-X`
- `quotient_of_flat_of_saturated`: the abstract flat quotient engine -/
theorem flat_quotient_fSubX_general
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (f : A) :
    Module.Flat A (↥(TateAlgebra A) ⧸
      Ideal.span {algebraMap A ↥(TateAlgebra A) f - X}) := by
  haveI := tateAlgebra_flat P
  exact Module.Flat.quotient_of_flat_of_saturated
    (mul_fSubX_regular f) (fun I s hmem ↦ fSubX_saturated P f I s hmem)

/-- `A⟨X⟩/(1-fX)` is flat over noetherian `A` (Lemma 8.31(2), general case). -/
theorem flat_quotient_oneSubfX_general
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (f : A) :
    Module.Flat A (↥(TateAlgebra A) ⧸
      Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * X}) := by
  haveI := tateAlgebra_flat P
  exact Module.Flat.quotient_of_flat_of_saturated
    (mul_oneSubfX_regular f) (fun I s hmem ↦ oneSubfX_saturated P f I s hmem)

/-- **Lemma 8.31(1), general case**: `A⟨X⟩` is **faithfully flat** over a
noetherian Tate ring `A`.

This is the non-discrete analog of the discrete `TateAlgebra.faithfullyFlat`
instance (line ~783): it uses the general flatness result
`tateAlgebra_flat P` (Artin-Rees over the pair-of-definition ring),
combined with surjectivity of `PrimeSpectrum.comap (algebraMap A A⟨X⟩)`
(which is algebraic and requires no topology), via
`Module.FaithfullyFlat.of_comap_surjective`. -/
theorem faithfullyFlat_general (P : PairOfDefinition A) [IsNoetherianRing P.A₀] :
    Module.FaithfullyFlat A ↥(TateAlgebra A) := by
  haveI := tateAlgebra_flat P
  exact Module.FaithfullyFlat.of_comap_surjective
    PrimeSpectrum_comap_algebraMap_surjective

end TateAlgebra

end QuotientFlatnessGeneral
