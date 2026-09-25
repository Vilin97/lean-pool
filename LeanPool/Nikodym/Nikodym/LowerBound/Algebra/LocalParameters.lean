/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module


public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Dimension
public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Interface
public import LeanPool.Nikodym.Nikodym.LowerBound.Jets.Defs

/-!
# Tangent cone ideal and local parameters

This file implements blueprint node **J01** of the algebra backend (see
`docs/algebra_backend_design.md`, §1.2 item 5 and §2, J01).

Throughout, `P := MvPolynomial (Fin d) K` and `𝔪 := idealOfVars (Fin d) K` is the ideal of the
origin. For an ideal `I` of `P` we define the *tangent-cone ideal*

* `Nikodym.LowerBound.tangentIdeal I`, the ideal spanned by the forms `F` of some degree `n` with
  `F ∈ I ⊔ 𝔪 ^ (n + 1)` (the lowest-degree forms of elements of `I`),

and prove

* `tangentIdeal_isHomogeneous`: it is a homogeneous ideal;
* `homogeneousComponent_mem_of_mem_tangentIdeal` / `mem_tangentIdeal_iff`: a form of degree `n`
  lies in `tangentIdeal I` iff it lies in `I ⊔ 𝔪 ^ (n + 1)`;
* `tangentIdeal_ne_top`: `tangentIdeal I` is proper when `I ≤ 𝔪`;
* `quotDim_le_of_pow_idealOfVars_le_tangentIdeal_sup`: if `I` is prime, `I ≤ 𝔪`, and `s` linear
  forms `y` satisfy `𝔪 ^ N ≤ tangentIdeal I ⊔ (y)`, then `quotDim I ≤ s`. The proof is a single
  Nakayama step showing that `𝔪` is a minimal prime over `I ⊔ (y)`, followed by Krull's height
  theorem in `P ⧸ I` and the closed-point height formula of A01.
-/

@[expose] public section

namespace Nikodym.LowerBound

open MvPolynomial

open scoped Pointwise

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K] {d : ℕ}

/-! ### The ideal of the origin -/

section IdealOfVars

/-- Blueprint J01 (auxiliary): a form of degree `n` lies in `𝔪 ^ n`. -/
theorem mem_pow_idealOfVars_of_isHomogeneous {n : ℕ} {F : MvPolynomial (Fin d) K}
    (hF : F.IsHomogeneous n) : F ∈ idealOfVars (Fin d) K ^ n := by
  rw [mem_pow_idealOfVars_iff]
  intro x hx
  rw [Finsupp.degree_eq_weight_one]
  exact (hF (mem_support_iff.mp hx)).ge

/-- Blueprint J01 (auxiliary): a form of degree `i` times an element of `I ⊔ 𝔪 ^ (j + 1)` lies
in `I ⊔ 𝔪 ^ (i + j + 1)`. -/
theorem mul_mem_sup_pow_idealOfVars_of_isHomogeneous {I : Ideal (MvPolynomial (Fin d) K)}
    {i j : ℕ} {a F : MvPolynomial (Fin d) K} (ha : a.IsHomogeneous i)
    (hF : F ∈ I ⊔ idealOfVars (Fin d) K ^ (j + 1)) :
    a * F ∈ I ⊔ idealOfVars (Fin d) K ^ (i + j + 1) := by
  have h1 : a * F ∈ idealOfVars (Fin d) K ^ i * (I ⊔ idealOfVars (Fin d) K ^ (j + 1)) :=
    Ideal.mul_mem_mul (mem_pow_idealOfVars_of_isHomogeneous ha) hF
  refine (?_ : idealOfVars (Fin d) K ^ i * (I ⊔ idealOfVars (Fin d) K ^ (j + 1)) ≤
    I ⊔ idealOfVars (Fin d) K ^ (i + j + 1)) h1
  rw [Ideal.mul_sup, ← pow_add, add_assoc]
  exact sup_le_sup_right Ideal.mul_le_right _

end IdealOfVars

/-! ### The tangent-cone ideal -/

section TangentIdeal

/-- Blueprint J01: the tangent-cone ideal `in(I)` of an ideal `I ⊆ P`: the ideal spanned by the
forms `F` of some degree `n` with `F ∈ I ⊔ 𝔪 ^ (n + 1)`, i.e. by the lowest-degree homogeneous
parts of the elements of `I` (relative to the origin). -/
noncomputable def tangentIdeal (I : Ideal (MvPolynomial (Fin d) K)) :
    Ideal (MvPolynomial (Fin d) K) :=
  Ideal.span {F | ∃ n : ℕ, F.IsHomogeneous n ∧ F ∈ I ⊔ idealOfVars (Fin d) K ^ (n + 1)}

variable (I : Ideal (MvPolynomial (Fin d) K))

/-- Blueprint J01: the tangent-cone ideal is homogeneous. -/
theorem tangentIdeal_isHomogeneous :
    (tangentIdeal I).IsHomogeneous (homogeneousSubmodule (Fin d) K) :=
  Ideal.homogeneous_span _ _ fun _ ⟨n, hFn, _⟩ ↦ ⟨n, hFn⟩

variable {I}

/-- Blueprint J01: a form of degree `n` lying in `I ⊔ 𝔪 ^ (n + 1)` lies in the tangent-cone
ideal. -/
theorem mem_tangentIdeal_of_isHomogeneous {n : ℕ} {F : MvPolynomial (Fin d) K}
    (hF : F.IsHomogeneous n) (h : F ∈ I ⊔ idealOfVars (Fin d) K ^ (n + 1)) :
    F ∈ tangentIdeal I :=
  Ideal.subset_span ⟨n, hF, h⟩

/-- Blueprint J01 (key step): every degree-`n` homogeneous component of an element of the
tangent-cone ideal lies in `I ⊔ 𝔪 ^ (n + 1)`. -/
theorem homogeneousComponent_mem_of_mem_tangentIdeal {F : MvPolynomial (Fin d) K}
    (hF : F ∈ tangentIdeal I) (n : ℕ) :
    homogeneousComponent n F ∈ I ⊔ idealOfVars (Fin d) K ^ (n + 1) := by
  refine Submodule.span_induction
    (p := fun F _ ↦ ∀ n, homogeneousComponent n F ∈ I ⊔ idealOfVars (Fin d) K ^ (n + 1))
    ?_ ?_ ?_ ?_ hF n
  · rintro F ⟨m, hFm, hFmem⟩ n
    rw [homogeneousComponent_of_mem hFm]
    split_ifs with h
    · subst h
      exact hFmem
    · exact zero_mem _
  · intro n
    simp
  · intro F G _ _ hF hG n
    rw [map_add]
    exact add_mem (hF n) (hG n)
  · intro a F _ hF n
    rw [smul_eq_mul, ← sum_homogeneousComponent a, ← sum_homogeneousComponent F,
      Finset.sum_mul_sum, map_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [map_sum]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    rw [homogeneousComponent_of_mem
      ((homogeneousComponent_isHomogeneous i a).mul (homogeneousComponent_isHomogeneous j F))]
    split_ifs with h
    · subst h
      exact mul_mem_sup_pow_idealOfVars_of_isHomogeneous (homogeneousComponent_isHomogeneous i a)
        (hF j)
    · exact zero_mem _

variable (I) in
/-- Blueprint J01: a form of degree `n` lies in the tangent-cone ideal iff it lies in
`I ⊔ 𝔪 ^ (n + 1)`. -/
theorem mem_tangentIdeal_iff {n : ℕ} {F : MvPolynomial (Fin d) K} (hF : F.IsHomogeneous n) :
    F ∈ tangentIdeal I ↔ F ∈ I ⊔ idealOfVars (Fin d) K ^ (n + 1) := by
  refine ⟨fun h ↦ ?_, mem_tangentIdeal_of_isHomogeneous hF⟩
  have := homogeneousComponent_mem_of_mem_tangentIdeal h n
  rwa [homogeneousComponent_eq_self hF] at this

/-- Blueprint J01: the tangent-cone ideal of an ideal contained in `𝔪` is proper. -/
theorem tangentIdeal_ne_top (hI : I ≤ idealOfVars (Fin d) K) : tangentIdeal I ≠ ⊤ := by
  intro h
  have h1 : (1 : MvPolynomial (Fin d) K) ∈ tangentIdeal I := (Ideal.eq_top_iff_one _).mp h
  rw [mem_tangentIdeal_iff I (isHomogeneous_one _ _), zero_add, pow_one,
    sup_eq_right.mpr hI] at h1
  exact idealOfVars_ne_top ((Ideal.eq_top_iff_one _).mpr h1)

end TangentIdeal

/-! ### Local parameters bound the dimension -/

section LocalParameters

/-- Blueprint J01: **the parameters of the tangent cone bound the height of `𝔪 / I`.** If `I` is a
prime ideal contained in `𝔪`, and `y₁, …, yₛ` are linear forms with
`𝔪 ^ N ≤ tangentIdeal I ⊔ (y₁, …, yₛ)`, then `quotDim I ≤ s`.

Proof: taking homogeneous components, `𝔪 ^ N ≤ J₀ ⊔ 𝔪 ^ (N + 1)` with `J₀ := I ⊔ (y)`; Nakayama
gives `ρ ≡ 1 (mod 𝔪)` with `ρ 𝔪 ^ N ≤ J₀`, so `𝔪` is a minimal prime over `J₀`. In `P ⧸ I` the
maximal ideal `𝔪 / I` is then minimal over the `s` classes of the `yᵢ`, so its height is at most
`s` by Krull's height theorem, and this height is `dim (P ⧸ I)` by A01. -/
theorem quotDim_le_of_pow_idealOfVars_le_tangentIdeal_sup (I : Ideal (MvPolynomial (Fin d) K))
    [I.IsPrime] (hI : I ≤ idealOfVars (Fin d) K) {s N : ℕ} {y : Fin s → MvPolynomial (Fin d) K}
    (hy : ∀ i, (y i).IsHomogeneous 1)
    (hN : idealOfVars (Fin d) K ^ N ≤ tangentIdeal I ⊔ Ideal.span (Set.range y)) :
    quotDim I ≤ s := by
  classical
  have h𝔪max : (idealOfVars (Fin d) K).IsMaximal := idealOfVars_isMaximal
  have hspan : (Ideal.span (Set.range y)).IsHomogeneous (homogeneousSubmodule (Fin d) K) :=
    Ideal.homogeneous_span _ _ (by rintro _ ⟨i, rfl⟩; exact ⟨1, hy i⟩)
  set J₀ : Ideal (MvPolynomial (Fin d) K) := I ⊔ Ideal.span (Set.range y) with hJ₀
  have hIJ₀ : I ≤ J₀ := le_sup_left
  have hJ₀𝔪 : J₀ ≤ idealOfVars (Fin d) K := by
    refine sup_le hI (Ideal.span_le.mpr ?_)
    rintro _ ⟨i, rfl⟩
    simpa using mem_pow_idealOfVars_of_isHomogeneous (hy i)
  -- Step 1: `𝔪 ^ N ≤ J₀ ⊔ 𝔪 ^ (N + 1)`, by taking homogeneous components.
  have hstep : idealOfVars (Fin d) K ^ N ≤ J₀ ⊔ idealOfVars (Fin d) K ^ (N + 1) := by
    intro F hF
    obtain ⟨G, hG, H, hH, hGH⟩ := Submodule.mem_sup.mp (hN hF)
    rw [← sum_homogeneousComponent F]
    refine Submodule.sum_mem _ fun n _ ↦ ?_
    rcases lt_or_ge n N with hn | hn
    · rw [homogeneousComponent_eq_zero']
      · exact zero_mem _
      · intro x hx
        have := (mem_pow_idealOfVars_iff N F).mp hF x hx
        omega
    · rw [← hGH, map_add]
      refine add_mem ?_ ?_
      · have hle : I ⊔ idealOfVars (Fin d) K ^ (n + 1) ≤ J₀ ⊔ idealOfVars (Fin d) K ^ (N + 1) :=
          sup_le_sup hIJ₀ (Ideal.pow_le_pow_right (by omega))
        exact hle (homogeneousComponent_mem_of_mem_tangentIdeal hG n)
      · exact Ideal.mem_sup_left (Ideal.mem_sup_right (homogeneousComponent_mem_of_mem hspan hH n))
  -- Step 2: Nakayama gives `ρ ≡ 1 (mod 𝔪)` with `ρ 𝔪 ^ N ≤ J₀`.
  obtain ⟨ρ, hρ1, hρ⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (I := idealOfVars (Fin d) K) (N := J₀) (N' := idealOfVars (Fin d) K ^ N)
    (P := idealOfVars (Fin d) K ^ N) (Ideal.fg_of_isNoetherianRing _) le_rfl
    (by rwa [Ideal.smul_eq_mul, ← pow_succ'])
  -- Step 3: `𝔪` is a minimal prime over `J₀`.
  have hmin : idealOfVars (Fin d) K ∈ J₀.minimalPrimes := by
    refine ⟨⟨h𝔪max.isPrime, hJ₀𝔪⟩, ?_⟩
    rintro q ⟨hq, hJ₀q⟩ hq𝔪
    have hρq : ρ ∉ q := fun h ↦ by
      have h1 : ρ - (ρ - 1) ∈ idealOfVars (Fin d) K := sub_mem (hq𝔪 h) hρ1
      rw [sub_sub_cancel] at h1
      exact idealOfVars_ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    intro x hx
    have hx' : ρ * x ^ N ∈ q :=
      hJ₀q (hρ (Submodule.smul_mem_pointwise_smul _ ρ _ (Ideal.pow_mem_pow hx N)))
    exact hq.mem_of_pow_mem N ((hq.mem_or_mem hx').resolve_left hρq)
  -- Step 4: push to `P ⧸ I`: `𝔪 / I` is minimal over the classes of the `yᵢ`.
  have hmin' : (idealOfVars (Fin d) K).map (Ideal.Quotient.mk I) ∈
      (J₀.map (Ideal.Quotient.mk I)).minimalPrimes := by
    rw [Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr hIJ₀]
    exact ⟨_, hmin, rfl⟩
  have hmap : J₀.map (Ideal.Quotient.mk I) =
      Ideal.span (↑(Finset.univ.image fun i ↦ Ideal.Quotient.mk I (y i)) :
        Set (MvPolynomial (Fin d) K ⧸ I)) := by
    rw [hJ₀, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Finset.coe_image,
      Finset.coe_univ, Set.image_univ, ← Set.range_comp]
    rfl
  rw [hmap] at hmin'
  -- Step 5: Krull's height theorem and A01.
  have hht : ((idealOfVars (Fin d) K).map (Ideal.Quotient.mk I)).height ≤ (s : ℕ∞) := by
    refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin').trans ?_
    exact_mod_cast Finset.card_image_le.trans (Finset.card_fin s).le
  have h1 := height_map_eq_ringKrullDim_of_isMaximal K I h𝔪max hI
  have h2 := coe_quotDim I Ideal.IsPrime.ne_top'
  have h3 : ((quotDim I : ℕ) : WithBot ℕ∞) ≤ ((s : ℕ) : WithBot ℕ∞) := by
    rw [h2, ← h1, ← WithBot.coe_natCast]
    exact WithBot.coe_le_coe.mpr hht
  exact_mod_cast h3

end LocalParameters

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
