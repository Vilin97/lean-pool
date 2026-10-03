/-
Copyright (c) 2026 Arnaud Mayeux, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arnaud Mayeux, Jujian Zhang
-/
module

public import LeanPool.Dilatations.RingComparison
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Tactic.LinearCombination

/-!
# A counterexample to the naive ring comparison

From Arnaud Mayeux, *Dilatations of categories, via their Lean formalization*,
https://arxiv.org/abs/2608.09305, and `rndmx/DilCat` at commit
`604559654c948566675da3f7709b8ad3126bd487` (Apache-2.0).
The ring construction includes work by Arnaud Mayeux and Jujian Zhang from
`ProjConstruction/Proj` (Apache-2.0).
-/

public section

noncomputable section

open CategoryTheory Finset
open CategoryTheory.Localization.Construction

universe v u v' pu pv u₁ v₁ u₂ v₂ u₃ v₃

namespace CategoryTheory.Dilatations

variable {C : Type u} [Category.{v} C]
variable (Z : Center C)
variable {D : Type u} [Category.{v'} D]
variable (F : C ⥤ D)

/-! ### Erratum to Proposition 5.1 : the naive `I`-indexed center is *not* the right one

The printed `\citep[Proposition~5.1]{Mayeux}` identifies `𝒞[{(aᵢ)⁻¹∘Mᵢ}ᵢ∈I]` (dilating by the
center indexed directly by `i ∈ I`, one generator per index) with `A[M]`. This identification is
false : composition in `SingleObj A'` is multiplication, so the image of every morphism of this
naive center's dilatation is a product `c·∏ⱼ(mⱼ/aᵢⱼ)`, and not every element of `A[M]` has this
form. The concrete witness below : `A = ℤ[X]`, `a = 2`, `M = (X)`, and `(X+2)/2 ∈ A[M]` is not
reachable. See `\S`10.2 of the paper for the informal argument this formalizes. -/
namespace NaiveCenterCounterexample

open Family Polynomial Multicenter

/-- The single-center example with ideal `(X)` and denominator `2` in `ℤ[X]`. -/
abbrev CEx : Multicenter (Polynomial ℤ) where
  index := Unit
  ideal _ := Ideal.span {X}
  elem _ := 2

/-- The localization of the integers obtained by inverting `2`. -/
abbrev Target := Localization (Submonoid.powers (2 : ℤ))

open Family in
lemma CEx_elem_pow_eval (ν : CEx^ℕ) : (CEx.elem ^ ν).eval 0 = 2 ^ (ν ()) := by
  have hν : ν = Finsupp.single () (ν ()) := by
    apply Finsupp.ext; intro i; cases i; simp
  erw [hν, familyPow_def, Finsupp.prod_single_index (by simp)]
  simp [CEx]

/-- Evaluate a fraction representative at `X = 0` in the localization of `ℤ`. -/
def psiPreDil (x : CEx.PreDil) : Target :=
  IsLocalization.mk' Target (x.num.eval 0) (⟨2 ^ (x.pow ()), x.pow (), rfl⟩ : Submonoid.powers
    (2 : ℤ))

lemma psiPreDil_respects {x y : CEx.PreDil} (h : CEx.r x y) : psiPreDil x = psiPreDil y := by
  obtain ⟨β, hβ⟩ := h
  have hβ' := congrArg (Polynomial.eval 0) hβ
  simp only [eval_mul] at hβ'
  change x.num.eval 0 * (CEx.elem ^ (β + y.pow)).eval 0 =
    y.num.eval 0 * (CEx.elem ^ (β + x.pow)).eval 0 at hβ'
  rw [CEx_elem_pow_eval, CEx_elem_pow_eval] at hβ'
  simp only [Finsupp.add_apply] at hβ'
  refine IsLocalization.eq.mpr ⟨⟨2 ^ (β ()), β (), rfl⟩, ?_⟩
  change (2 : ℤ) ^ (β ()) * (2 ^ (y.pow ()) * x.num.eval 0) =
    2 ^ (β ()) * (2 ^ (x.pow ()) * y.num.eval 0)
  calc (2 : ℤ) ^ (β ()) * (2 ^ (y.pow ()) * x.num.eval 0)
      = (2 ^ (β ()) * 2 ^ (y.pow ())) * x.num.eval 0 := by ring
    _ = 2 ^ (β () + y.pow ()) * x.num.eval 0 := by rw [pow_add]
    _ = x.num.eval 0 * 2 ^ (β () + y.pow ()) := by ring
    _ = y.num.eval 0 * 2 ^ (β () + x.pow ()) := hβ'
    _ = 2 ^ (β () + x.pow ()) * y.num.eval 0 := by ring
    _ = (2 ^ (β ()) * 2 ^ (x.pow ())) * y.num.eval 0 := by rw [pow_add]
    _ = 2 ^ (β ()) * (2 ^ (x.pow ()) * y.num.eval 0) := by ring

/-- **The evaluation-at-`X=0` invariant `ψ`.** Descends to the dilatation ring because it kills
exactly what fraction-composition can produce from `(X)`-numerators. -/
def psi : (Polynomial ℤ)[CEx] → Target :=
  Multicenter.Dilatation.descFun psiPreDil (fun _ _ h => psiPreDil_respects h)

open Multicenter.Dilatation in
lemma psi_algebraMap (c : Polynomial ℤ) : psi (algebraMap _ _ c) = algebraMap ℤ Target (c.eval
    0) := by
  rw [algebraMap_apply]
  change psiPreDil ⟨0, c, _⟩ = _
  unfold psiPreDil
  simp only [Finsupp.zero_apply, pow_zero]
  erw [show (⟨1, 0, rfl⟩ : Submonoid.powers (2 : ℤ)) = 1 from rfl, IsLocalization.mk'_one]

open Multicenter.Dilatation in
lemma psi_mul (x y : (Polynomial ℤ)[CEx]) : psi (x * y) = psi x * psi y := by
  induction x using induction_on with
  | h x =>
    induction y using induction_on with
    | h y =>
      change psi (mk (Dilatation.mul' x y)) = psi (mk x) * psi (mk y)
      change psiPreDil (Dilatation.mul' x y) = psiPreDil x * psiPreDil y
      unfold psiPreDil Dilatation.mul'
      simp only [Finsupp.add_apply, eval_mul, pow_add]
      rw [← IsLocalization.mk'_mul]
      congr 1

open Multicenter.Dilatation in
lemma X_add_two_mem :
    (X + 2 : Polynomial ℤ) ∈ CEx.LargeIdeal ^ (Finsupp.single () 1 : CEx^ℕ) := by
  erw [familyPow_def, Finsupp.prod_single_index (by simp)]
  simp only [pow_one]
  change (X + 2 : Polynomial ℤ) ∈ Ideal.span {X} + Ideal.span {(2 : Polynomial ℤ)}
  apply Submodule.add_mem_sup
  · exact Ideal.mem_span_singleton_self X
  · exact Ideal.mem_span_singleton_self 2

open Multicenter.Dilatation in
/-- The target element `(X+2)/2 ∈ A[M]`, which we show is unreachable. -/
noncomputable def targetElement : (Polynomial ℤ)[CEx] :=
  Dilatation.frac (Finsupp.single () 1 : CEx^ℕ) ⟨X + 2, X_add_two_mem⟩

open Multicenter.Dilatation in
lemma psi_target : psi targetElement = 1 := by
  change psiPreDil ⟨_, _, _⟩ = 1
  unfold psiPreDil
  simp only [eval_add, eval_X, eval_ofNat, Finsupp.single_eq_same]
  norm_num

open Multicenter.Dilatation in
lemma psi_frac_eq_zero (m : Polynomial ℤ) (hm : m ∈ Ideal.span ({X} : Set (Polynomial ℤ)))
    (hL : m ∈ CEx.LargeIdeal ^ (Finsupp.single () 1 : CEx^ℕ)) :
    psi (Dilatation.frac (Finsupp.single () 1 : CEx^ℕ) ⟨m, hL⟩) = 0 := by
  change psiPreDil ⟨_, _, _⟩ = 0
  unfold psiPreDil
  have : m.eval 0 = 0 := by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hm
    simp
  simp only [this]
  exact IsLocalization.mk'_zero _

/-- The naive `I`-indexed center `{(a_i, M_i)}` (here a single index): index `Unit`, morphism
`2`, sieve generated by `(X)` directly (not the large ideal). -/
@[expose]
def centerNaive : Center (CategoryTheory.SingleObj (Polynomial ℤ)) where
  I := Unit
  nonempty := ⟨()⟩
  dom _ := CategoryTheory.SingleObj.star (Polynomial ℤ)
  cod _ := CategoryTheory.SingleObj.star (Polynomial ℤ)
  mor _ := (2 : Polynomial ℤ)
  N _ := CategoryTheory.Dilatations.Prop51.Sieve.ofIdeal (Ideal.span {X})

open CategoryTheory Prop51 in
/-- **The comparison functor for the naive center**, built directly from the universal property
(`Dila_universal_property`), exactly as the printed proof's `Φ` is meant to be. -/
theorem prop_naive :
    ∃! (Φ : Dila centerNaive ⥤ CategoryTheory.SingleObj (Polynomial ℤ)[CEx]),
      CatToDila centerNaive ⋙ Φ = toDilatationFunctor CEx := by
  apply Dila_universal_property
  · change (ImageCenterMorphismProperty centerNaive (toDilatationFunctor CEx)).Q.Faithful
    set Sgen : Submonoid (Polynomial ℤ)[CEx] :=
      Submonoid.closure (Set.range (fun _ : Unit => algebraMap (Polynomial ℤ) _ (CEx.elem ())))
      with hSgendef
    have hSgennzd : Sgen ≤ nonZeroDivisors (Polynomial ℤ)[CEx] := by
      rw [hSgendef, Submonoid.closure_le]
      rintro x ⟨i, rfl⟩
      exact Multicenter.Dilatation.nonzerodiv_image_single CEx ()
    let e0 : CategoryTheory.SingleObj (Polynomial ℤ)[CEx] ⥤ CategoryTheory.SingleObj
      (Localization Sgen) :=
      CategoryTheory.SingleObj.mapHom _ _ (algebraMap (Polynomial ℤ)[CEx] (Localization
        Sgen)).toMonoidHom
    have he0faith : e0.Faithful := by
      constructor
      intro _ _ f g h
      exact IsLocalization.injective (M := Sgen) (Localization Sgen) hSgennzd h
    have he0inv :
        (ImageCenterMorphismProperty centerNaive (toDilatationFunctor CEx)).IsInvertedBy e0 := by
      rintro X Y f ⟨i0, hi⟩
      have hX : X = (toDilatationFunctor CEx).obj (centerNaive.dom i0) :=
        congrArg Sigma.fst hi
      have hY : Y = (toDilatationFunctor CEx).obj (centerNaive.cod i0) :=
        congrArg (fun s => s.2.1) hi
      subst hX
      subst hY
      have hf : f = (toDilatationFunctor CEx).map (centerNaive.mor i0) := by
        cases hi; rfl
      have hmem : algebraMap (Polynomial ℤ) _ (centerNaive.mor i0) ∈ Sgen := by
        change algebraMap (Polynomial ℤ) _ (CEx.elem ()) ∈ Sgen
        rw [hSgendef]
        exact Submonoid.subset_closure ⟨(), rfl⟩
      rw [hf, isIso_iff_isUnit]
      exact IsLocalization.map_units (Localization Sgen)
        (⟨algebraMap (Polynomial ℤ) _ (centerNaive.mor i0), hmem⟩ : Sgen)
    exact faithful_Q_of_isInvertedBy_of_faithful _ e0 he0inv he0faith
  · intro i0
    rintro Y f ⟨Z, g, h, hg, rfl⟩
    obtain rfl : Y = CategoryTheory.SingleObj.star (Polynomial ℤ)[CEx] := Subsingleton.elim _ _
    obtain rfl : Z = CategoryTheory.SingleObj.star (Polynomial ℤ) := Subsingleton.elim _ _
    let h' : (Polynomial ℤ)[CEx] := h
    let d : (Polynomial ℤ)[CEx] :=
      @CategoryTheory.Functor.map (CategoryTheory.SingleObj (Polynomial ℤ)) _
        (CategoryTheory.SingleObj (Polynomial ℤ)[CEx]) _
        (toDilatationFunctor CEx) (CategoryTheory.SingleObj.star (Polynomial ℤ))
        (CategoryTheory.SingleObj.star (Polynomial ℤ)) (centerNaive.mor i0)
    have hd : d = algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] (centerNaive.mor i0) := by
      change (@CategoryTheory.Functor.map (CategoryTheory.SingleObj (Polynomial ℤ)) _
        (CategoryTheory.SingleObj (Polynomial ℤ)[CEx]) _ (toDilatationFunctor CEx)
        (CategoryTheory.SingleObj.star (Polynomial ℤ)) (CategoryTheory.SingleObj.star
          (Polynomial ℤ))
        (centerNaive.mor i0)) = _
      simp [toDilatationFunctor, CategoryTheory.SingleObj.mapHom]
    have hgeq : @CategoryTheory.Functor.map (CategoryTheory.SingleObj (Polynomial ℤ)) _
        (CategoryTheory.SingleObj (Polynomial ℤ)[CEx]) _ (toDilatationFunctor CEx)
        (CategoryTheory.SingleObj.star (Polynomial ℤ)) (CategoryTheory.SingleObj.star
          (Polynomial ℤ)) g
        = algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] g := by
      simp [toDilatationFunctor, CategoryTheory.SingleObj.mapHom]
    have hgmem : g ∈ Ideal.span ({X} : Set (Polynomial ℤ)) := hg
    have hgL : g ∈ CEx.LargeIdeal ^ (Finsupp.single () 1 : CEx^ℕ) := by
      erw [familyPow_def, Finsupp.prod_single_index (by simp)]
      simp only [pow_one, Multicenter.LargeIdeal, Submodule.add_eq_sup]
      exact Submodule.mem_sup_left (M := Polynomial ℤ) hgmem
    have hmem : algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] g ∈
        Ideal.span {algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] (centerNaive.mor i0)} := by
      change algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] g ∈
        Ideal.span {algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] (CEx.elem ())}
      have heq := Multicenter.Dilatation.image_elem_LargeIdeal_equal (M := CEx)
        (Finsupp.single () 1 : CEx^ℕ)
      rw [show CEx.elem ^ (Finsupp.single () 1 : CEx^ℕ) = CEx.elem () by
        erw [familyPow_def, Finsupp.prod_single_index (by simp)]; simp] at heq
      rw [heq]
      exact Ideal.mem_map_of_mem _ hgL
    rw [Ideal.mem_span_singleton'] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨CategoryTheory.SingleObj.star (Polynomial ℤ)[CEx], c * h', d,
      Presieve.singleton_self _, ?_⟩
    rw [CategoryTheory.SingleObj.comp_as_mul, CategoryTheory.SingleObj.comp_as_mul, hd, hgeq, ← hc]
    change algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] (centerNaive.mor i0) * (c * h') =
      c * algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] (centerNaive.mor i0) * h'
    ring

/-- The functor `Φ_naive` produced by `prop_naive`, matching the printed paper's `Φ`. -/
noncomputable def PhiNaive : Dila centerNaive ⥤ CategoryTheory.SingleObj (Polynomial ℤ)[CEx] :=
  prop_naive.choose

open CategoryTheory.Dilatations.Prop51 in
lemma PhiNaive_spec : CatToDila centerNaive ⋙ PhiNaive = toDilatationFunctor CEx :=
  prop_naive.choose_spec.1

open CategoryTheory.Dilatations.Prop51 in
lemma PhiNaive_unique (G' : Dila centerNaive ⥤ CategoryTheory.SingleObj (Polynomial ℤ)[CEx])
    (hG' : CatToDila centerNaive ⋙ G' = toDilatationFunctor CEx) : G' = PhiNaive :=
  prop_naive.choose_spec.2 G' hG'

/-- `CEx.elem ^ ν = 2 ^ (ν ())` as a polynomial identity (no evaluation), for arbitrary `ν`. -/
lemma CEx_elem_pow (ν : CEx^ℕ) : CEx.elem ^ ν = (2 : Polynomial ℤ) ^ (ν ()) := by
  have hν : ν = Finsupp.single () (ν ()) := by apply Finsupp.ext; intro i; cases i; simp
  erw [hν, familyPow_def, Finsupp.prod_single_index (by simp)]
  simp [CEx]

/-- `c·Xᵏ` always lies in the `k`-th large-ideal power, for every `c` and every `k`. -/
lemma cXk_mem (c : Polynomial ℤ) (k : ℕ) :
    c * X ^ k ∈ CEx.LargeIdeal ^ (Finsupp.single () k : CEx^ℕ) := by
  erw [familyPow_def, Finsupp.prod_single_index (by simp)]
  have hXmem : (X : Polynomial ℤ) ∈ CEx.LargeIdeal () := by
    simp only [Multicenter.LargeIdeal, Submodule.add_eq_sup]
    exact Submodule.mem_sup_left (Ideal.mem_span_singleton_self X)
  exact Ideal.mul_mem_left _ c (Ideal.pow_mem_pow hXmem k)

/-- `ψ` kills every fraction `(c·Xᵏ)/2ᵏ` with `k ≥ 1` (numerator divisible by `X`). -/
lemma psi_cXk_eq_zero (c : Polynomial ℤ) (k : ℕ) (hk : 1 ≤ k) :
    psi (Multicenter.Dilatation.frac (Finsupp.single () k : CEx^ℕ) ⟨c * X ^ k, cXk_mem c k⟩) =
      0 := by
  change psiPreDil ⟨_, _, _⟩ = 0
  unfold psiPreDil
  have : (c * X ^ k).eval 0 = 0 := by
    have : (0 : ℤ) ^ k = 0 := zero_pow (by omega)
    simp [this]
  simp only [this]
  exact IsLocalization.mk'_zero _

open Multicenter.Dilatation in
/-- **The key non-surjectivity fact.** `targetElement = (X+2)/2` is never `algebraMap c` for any
`c : ℤ[X]`: cross-multiplying gives `2c = X+2` (up to a harmless common power of `2`), and
    evaluating
at `X = 1` turns this into `2·c(1) = 3` in `ℤ`, which is false (2 does not divide 3). -/
lemma targetElement_ne_algebraMap (c : Polynomial ℤ) :
    algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] c ≠ targetElement := by
  intro heq
  rw [algebraMap_apply, targetElement, Multicenter.Dilatation.mk_eq_mk] at heq
  obtain ⟨β, hβ⟩ := heq
  simp only [add_zero] at hβ
  rw [CEx_elem_pow, CEx_elem_pow] at hβ
  simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hβ
  rw [pow_succ] at hβ
  have hne : (2 : Polynomial ℤ) ^ (β ()) ≠ 0 := by
    apply pow_ne_zero
    intro h
    have := congrArg (Polynomial.eval 0) h
    simp at this
  have hrearranged : (2 : Polynomial ℤ) ^ (β ()) * (c * 2) = (2 : Polynomial ℤ) ^ (β ()) * (X
    + 2) := by
    linear_combination hβ
  have h2 : c * (2 : Polynomial ℤ) = X + 2 := mul_left_cancel₀ hne hrearranged
  have hmap := congrArg (Polynomial.eval 1) h2
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_ofNat] at hmap
  omega

lemma mem_LargeIdeal_single1_of_mem_ideal {m : Polynomial ℤ}
    (hm : m ∈ Ideal.span ({X} : Set (Polynomial ℤ))) :
    m ∈ CEx.LargeIdeal ^ (Finsupp.single () 1 : CEx^ℕ) := by
  erw [familyPow_def, Finsupp.prod_single_index (by simp)]
  simp only [pow_one, Multicenter.LargeIdeal, Submodule.add_eq_sup]
  exact Submodule.mem_sup_left (M := Polynomial ℤ) hm

open Multicenter.Dilatation CategoryTheory.Dilatations.Prop51 in
/-- The defining identity for our specific `[X,2]` fraction, specialized from
`algebraMap_elem_pow_mul_frac`. -/
lemma algebraMap_two_mul_frac (m : Polynomial ℤ) (hm : m ∈ CEx.LargeIdeal ^ (Finsupp.single ()
    1 : CEx^ℕ)) :
    algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] 2 * frac (Finsupp.single () 1 : CEx^ℕ) ⟨m, hm⟩ =
    algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] m := by
  have h := algebraMap_elem_pow_mul_frac CEx (Finsupp.single () 1) m hm
  erw [CEx_elem_pow, Finsupp.single_eq_same, pow_one] at h
  exact h

open CategoryTheory.Dilatations.Prop51 Multicenter.Dilatation in
/-- **The image of a fraction generator.** `Φ_naive` sends the "`m`-over-`2`" generator (for
`m ∈ (X)`) to the honest dilatation fraction `m/2` — no more, no less. This is forced : composing
with `Θ(2)` on both sides and cancelling the nonzerodivisor `algebraMap 2` pins the value down
uniquely (cf. `Phi51_full`, the analogous computation for the `ν`-indexed center). -/
lemma PhiNaive_map_fraction (X' : CategoryTheory.SingleObj (Polynomial ℤ)) (m : Polynomial ℤ)
    (hm : m ∈ Ideal.span ({X} : Set (Polynomial ℤ))) :
    PhiNaive.map (fractionInDilatation centerNaive ⟨(), X', m, hm⟩) =
      frac (Finsupp.single () 1 : CEx^ℕ) ⟨m, mem_LargeIdeal_single1_of_mem_ideal hm⟩ := by
  have hcomp := fraction_in_dila_comp_mor centerNaive () X' m hm
  have hmap := congrArg PhiNaive.map hcomp
  rw [CategoryTheory.Functor.map_comp] at hmap
  have hspec1 : PhiNaive.map ((CatToDila centerNaive).map (centerNaive.mor ())) =
      algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] (centerNaive.mor ()) := by
    have h := CategoryTheory.Functor.congr_hom PhiNaive_spec (centerNaive.mor ())
    simpa [toDilatationFunctor, CategoryTheory.SingleObj.mapHom,
      CategoryTheory.Functor.comp_map] using h
  set mMor : CategoryTheory.SingleObj.star (Polynomial ℤ) ⟶ CategoryTheory.SingleObj.star
    (Polynomial ℤ) :=
    m with hmMor
  have hspec2 : PhiNaive.map ((CatToDila centerNaive).map mMor) =
      algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] m := by
    have h := CategoryTheory.Functor.congr_hom PhiNaive_spec mMor
    simpa [toDilatationFunctor, CategoryTheory.SingleObj.mapHom,
      CategoryTheory.Functor.comp_map] using h
  rw [hspec1, hspec2] at hmap
  rw [← CategoryTheory.End.mul_def] at hmap
  have hnzd : algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] (centerNaive.mor ()) ∈
      nonZeroDivisors (Polynomial ℤ)[CEx] := Multicenter.Dilatation.nonzerodiv_image_single CEx ()
  exact (mul_cancel_left_mem_nonZeroDivisors hnzd).mp
    (hmap.trans (algebraMap_two_mul_frac m (mem_LargeIdeal_single1_of_mem_ideal hm)).symm)

open CategoryTheory.Dilatations.Prop51 Multicenter.Dilatation in
/-- **Every reachable morphism is `c·Xᵏ/2ᵏ`.** Since `Dila centerNaive`'s only generators are
`C`'s original morphisms (ring elements) and the single fraction generator `X/2` (from the sieve
`(X)`), and composition is multiplication, every morphism's `Φ_naive`-image is a product of these,
hence of the stated shape. -/
lemma exists_c_k : ∀ {A B : GeneratedCategory centerNaive} (f : A ⟶ B),
    ∃ (c : Polynomial ℤ) (k : ℕ) (hmem : c * X ^ k ∈ CEx.LargeIdeal ^ (Finsupp.single () k :
      CEx^ℕ)),
      (PhiNaive.map ((GeneratedToDila centerNaive).map f) : (Polynomial ℤ)[CEx]) =
        frac (Finsupp.single () k : CEx^ℕ) ⟨c * X ^ k, hmem⟩ := by
  apply GeneratedCategory_morphism_induction centerNaive
    (P := fun {A B} (f : A ⟶ B) =>
      ∃ (c : Polynomial ℤ) (k : ℕ) (hmem : c * X ^ k ∈ CEx.LargeIdeal ^ (Finsupp.single () k :
        CEx^ℕ)),
        (PhiNaive.map ((GeneratedToDila centerNaive).map f) : (Polynomial ℤ)[CEx]) =
          frac (Finsupp.single () k : CEx^ℕ) ⟨c * X ^ k, hmem⟩)
  · -- identity
    intro A
    refine ⟨1, 0, by exact cXk_mem 1 0, ?_⟩
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    change (𝟙 (PhiNaive.obj ((GeneratedToDila centerNaive).obj A)) : (Polynomial ℤ)[CEx]) = _
    rw [CategoryTheory.SingleObj.id_as_one, ← map_one (algebraMap (Polynomial ℤ) (Polynomial
      ℤ)[CEx])]
    simp [algebraMap_apply, frac]
  · -- composition
    rintro X Y W f g ⟨c1, k1, hmem1, heq1⟩ ⟨c2, k2, hmem2, heq2⟩
    refine ⟨c1 * c2, k1 + k2, by
      have := cXk_mem (c1 * c2) (k1 + k2)
      rw [pow_add] at this ⊢
      exact this, ?_⟩
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    set a : (Polynomial ℤ)[CEx] := PhiNaive.map ((GeneratedToDila centerNaive).map f) with ha
    set b : (Polynomial ℤ)[CEx] := PhiNaive.map ((GeneratedToDila centerNaive).map g) with hb
    rw [CategoryTheory.SingleObj.comp_as_mul, heq1, heq2, frac_mul_frac]
    change Multicenter.Dilatation.mk (M := CEx) _ = Multicenter.Dilatation.mk (M := CEx) _
    rw [mk_eq_mk]
    refine ⟨0, ?_⟩
    simp only [zero_add]
    rw [CEx_elem_pow, CEx_elem_pow]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    rw [pow_add]
    ring
  · -- generator
    intro A B g
    obtain ⟨f0, data⟩ := g
    cases data with
    | original h =>
        obtain ⟨g0, heq⟩ := h
        subst heq
        refine ⟨g0, 0, by exact cXk_mem g0 0, ?_⟩
        change (PhiNaive.map ((CatToDila centerNaive).map g0) : (Polynomial ℤ)[CEx]) = _
        have hh := CategoryTheory.Functor.congr_hom PhiNaive_spec g0
        have heq2 : PhiNaive.map ((CatToDila centerNaive).map g0) =
            algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] g0 := by
          simpa [toDilatationFunctor, CategoryTheory.SingleObj.mapHom,
            CategoryTheory.Functor.comp_map] using hh
        rw [heq2]
        simp [algebraMap_apply, frac]
    | fraction h =>
        obtain ⟨p, heq⟩ := h
        cases heq
        obtain ⟨i0, X0, m, hm⟩ := p
        obtain rfl : i0 = () := rfl
        let m2 : Polynomial ℤ := m
        have hm2 : m2 ∈ Ideal.span ({X} : Set (Polynomial ℤ)) := hm
        obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp hm2
        refine ⟨c', 1, ?_, ?_⟩
        · rw [pow_one, hc']; exact mem_LargeIdeal_single1_of_mem_ideal hm2
        · change (PhiNaive.map (fractionInDilatation centerNaive ⟨(), X0, m, hm⟩) :
            (Polynomial ℤ)[CEx]) = _
          rw [PhiNaive_map_fraction X0 m hm]
          congr 1
          apply Subtype.ext
          change (m : Polynomial ℤ) = c' * X ^ 1
          rw [pow_one]
          exact hc'.symm

open CategoryTheory.Dilatations.Prop51 Multicenter.Dilatation in
/-- **`targetElement = (X+2)/2` is not in the image of `Φ_naive`.** Every morphism of `Dila
centerNaive` lifts (via `GeneratedToDila_full`) to a path of generators, whose image under
`Φ_naive` is `c·Xᵏ/2ᵏ` by `exists_c_k`. If `k = 0` this is `algebraMap c`, ruled out by
`targetElement_ne_algebraMap`; if `k ≥ 1` the numerator `c·Xᵏ` is divisible by `X`, so `ψ` kills it
(`psi_cXk_eq_zero`), while `ψ (targetElement) = 1 ≠ 0`. -/
theorem targetElement_not_in_range :
    ∀ {A B : Dila centerNaive} (φ : A ⟶ B), (PhiNaive.map φ : (Polynomial ℤ)[CEx]) ≠
      targetElement := by
  intro A B φ hφ
  obtain ⟨ψ, hψ⟩ := (GeneratedToDila centerNaive).map_surjective φ
  obtain ⟨c, k, hmem, heq⟩ := exists_c_k ψ
  erw [← hψ, heq] at hφ
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0
    have hrw : frac (Finsupp.single () 0 : CEx^ℕ) ⟨c * X ^ 0, hmem⟩ =
        algebraMap (Polynomial ℤ) (Polynomial ℤ)[CEx] c := by
      rw [algebraMap_apply]
      simp only [frac, mk_eq_mk]
      exact ⟨0, by simp⟩
    rw [hrw] at hφ
    exact targetElement_ne_algebraMap c hφ
  · have h0 := congrArg psi hφ
    rw [psi_target, psi_cXk_eq_zero c k hk1] at h0
    have hpow_nzd : Submonoid.powers (2 : ℤ) ≤ nonZeroDivisors ℤ := by
      rw [Submonoid.powers_le]
      simp
    have hinj : Function.Injective (algebraMap ℤ Target) := IsLocalization.injective Target hpow_nzd
    have : (0 : ℤ) = 1 := hinj (by rw [map_zero, map_one]; exact h0)
    exact absurd this (by norm_num)

open CategoryTheory.Dilatations.Prop51 Multicenter.Dilatation in
/-- `Φ_naive` itself is not full (its image on the relevant `End` misses `targetElement`). -/
theorem PhiNaive_not_full : ¬ PhiNaive.Full := by
  intro hfull
  have := hfull
  obtain ⟨φ, hφ⟩ := PhiNaive.map_surjective
    (X := (CatToDila centerNaive).obj (CategoryTheory.SingleObj.star (Polynomial ℤ)))
    (Y := (CatToDila centerNaive).obj (CategoryTheory.SingleObj.star (Polynomial ℤ)))
    (targetElement :
      PhiNaive.obj ((CatToDila centerNaive).obj (CategoryTheory.SingleObj.star (Polynomial ℤ))) ⟶
      PhiNaive.obj ((CatToDila centerNaive).obj (CategoryTheory.SingleObj.star (Polynomial ℤ))))
  exact targetElement_not_in_range φ hφ

open CategoryTheory.Dilatations.Prop51 in
/-- **The main theorem.** No functor `Dila centerNaive ⥤ SingleObj ℤ[X][CEx]` compatible with the
two canonical inclusion functors (i.e. matching the printed paper's comparison functor `Φ`) can be
part of an equivalence of categories : by `prop_naive`'s uniqueness clause any such functor equals
`Φ_naive`, and `Φ_naive` is not full (`PhiNaive_not_full`), while every equivalence functor is
full. This refutes Proposition 5.1's claimed identification `𝒞[(aᵢ)⁻¹∘Mᵢ] ≅ A[M]` for the naive
`I`-indexed center. -/
theorem no_C_compatible_equiv :
    ¬ ∃ (Φ' : Dila centerNaive ≌ CategoryTheory.SingleObj (Polynomial ℤ)[CEx]),
      CatToDila centerNaive ⋙ Φ'.functor = toDilatationFunctor CEx := by
  rintro ⟨Φ', hΦ'⟩
  have heq : Φ'.functor = PhiNaive := PhiNaive_unique Φ'.functor hΦ'
  have hfull : Φ'.functor.Full := inferInstance
  rw [heq] at hfull
  exact PhiNaive_not_full hfull

end NaiveCenterCounterexample

end CategoryTheory.Dilatations
