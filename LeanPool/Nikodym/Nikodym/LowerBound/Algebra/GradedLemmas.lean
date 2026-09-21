/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.Defs
import LeanPool.Nikodym.Nikodym.LowerBound.Jets.Defs

/-!
# Graded lemmas for homogeneous ideals of polynomial rings

Shared toolbox of the algebra backend (design document §1.3 and §4, risk 3; blueprint nodes
**A05**, **B01**, **B02(i)**). Everything is stated for `MvPolynomial σ K` over a field `K`, with
the standard grading `MvPolynomial.homogeneousSubmodule σ K` (made a local instance through
`MvPolynomial.gradedAlgebra`).

## Main declarations

* `Nikodym.LowerBound.homHilbert J t`: the homogeneous Hilbert function
  `dim_K (P_t / J_t) = dim_K (image of P_t in P ⧸ J)`.
* `finrank_map_mkₐ_add_finrank_comap_subtype`, `homHilbert_add_finrank_inf`: rank–nullity for
  the image of a finite-dimensional subspace in a quotient ring; `homHilbert_anti`,
  `homHilbert_top`.
* `homogeneousComponent_mul_of_isHomogeneous`, `homogeneousComponent_sum`: homogeneous
  components of products with a form and of finite sums.
* `inf_homogeneousSubmodule_sup`, `inf_homogeneousSubmodule_inf`: graded pieces of `A ⊔ B` and
  `A ⊓ B` for homogeneous ideals `A, B`, and the inclusion–exclusion identity
  `homHilbert_inf_add_homHilbert_sup` (blueprint B02(i)).
* `mem_idealOfVars_of_isHomogeneous`, `le_idealOfVars_of_isHomogeneous`,
  `eq_top_of_isHomogeneous_of_X_sub_C_mem`, `one_mem_of_isHomogeneous_of_X_sub_one_mem`: a form
  of positive degree lies in the ideal of the variables, a proper homogeneous ideal lies in it,
  and a homogeneous ideal containing `X i - c` (`c ≠ 0`) is the unit ideal.
-/

namespace Nikodym.LowerBound

open MvPolynomial Module

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K] {σ : Type*}

/-! ### Rank–nullity for images in a quotient ring -/

section RankNullity

variable {A : Type*} [CommRing A] [Algebra K A]

/-- Blueprint A05/B01: the kernel of the quotient map, as a `K`-linear map, is the ideal viewed as
a `K`-submodule. -/
theorem ker_mkₐ_toLinearMap (J : Ideal A) :
    LinearMap.ker (Ideal.Quotient.mkₐ K J).toLinearMap = J.restrictScalars K := by
  ext x
  simp [Ideal.Quotient.eq_zero_iff_mem]

/-- Blueprint A05/B01 (rank–nullity): for a finite-dimensional `K`-subspace `V` of a `K`-algebra
`A` and an ideal `J`, `dim (image of V in A ⧸ J) + dim (V ∩ J) = dim V`, with `V ∩ J` written as
a subspace of `V`. -/
theorem finrank_map_mkₐ_add_finrank_comap_subtype (J : Ideal A) (V : Submodule K A)
    [Module.Finite K V] :
    finrank K (V.map (Ideal.Quotient.mkₐ K J).toLinearMap) +
      finrank K ((J.restrictScalars K).comap V.subtype) = finrank K V := by
  have h := LinearMap.finrank_range_add_finrank_ker
    ((Ideal.Quotient.mkₐ K J).toLinearMap ∘ₗ V.subtype)
  rwa [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp, ker_mkₐ_toLinearMap]
    at h

/-- Blueprint A05/B01 (rank–nullity): for a finite-dimensional `K`-subspace `V` of a `K`-algebra
`A` and an ideal `J`, `dim (image of V in A ⧸ J) + dim (J ∩ V) = dim V`, with `J ∩ V` a subspace
of `A`. -/
theorem finrank_map_mkₐ_add_finrank_inf (J : Ideal A) (V : Submodule K A) [Module.Finite K V] :
    finrank K (V.map (Ideal.Quotient.mkₐ K J).toLinearMap) +
      finrank K ↥(J.restrictScalars K ⊓ V) = finrank K V := by
  rw [← finrank_map_mkₐ_add_finrank_comap_subtype J V,
    ← (Submodule.comapSubtypeEquivOfLe (inf_le_right : J.restrictScalars K ⊓ V ≤ V)).finrank_eq,
    Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]

end RankNullity

/-! ### The homogeneous Hilbert function -/

section HomHilbert

/-- Blueprint A05: the homogeneous pieces `P_t` are finite-dimensional for finitely many
variables. -/
instance instModuleFiniteHomogeneousSubmodule [Finite σ] (t : ℕ) :
    Module.Finite K (homogeneousSubmodule σ K t) :=
  Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg σ K t)

/-- Blueprint A05/B01/B02: the homogeneous Hilbert function `t ↦ dim_K (P_t ⧸ J_t)`, realized as
the dimension of the image of the degree-`t` forms in `P ⧸ J`. -/
noncomputable def homHilbert (J : Ideal (MvPolynomial σ K)) (t : ℕ) : ℕ :=
  finrank K ((homogeneousSubmodule σ K t).map (Ideal.Quotient.mkₐ K J).toLinearMap)

/-- Blueprint B01/B02: `homHilbert ⊤ t = 0`. -/
theorem homHilbert_top (t : ℕ) : homHilbert (⊤ : Ideal (MvPolynomial σ K)) t = 0 := by
  haveI : Subsingleton (MvPolynomial σ K ⧸ (⊤ : Ideal (MvPolynomial σ K))) :=
    Ideal.Quotient.subsingleton_iff.mpr rfl
  rw [homHilbert]
  exact Module.finrank_zero_of_subsingleton

/-- Blueprint B01: the image of `P_t` in `P ⧸ B` is the image of the image in `P ⧸ A` under the
factor map, for `A ≤ B`. -/
theorem map_mkₐ_eq_map_factor {A B : Ideal (MvPolynomial σ K)} (h : A ≤ B) (t : ℕ) :
    (homogeneousSubmodule σ K t).map (Ideal.Quotient.mkₐ K B).toLinearMap =
      ((homogeneousSubmodule σ K t).map (Ideal.Quotient.mkₐ K A).toLinearMap).map
        (Ideal.Quotient.factorₐ K h).toLinearMap := by
  rw [← Submodule.map_comp]
  congr 1

variable [Finite σ]

/-- Blueprint B01 (rank–nullity): `homHilbert J t + dim_K J_t = dim_K P_t`, with
`J_t = J ⊓ P_t` as a subspace of `P`. -/
theorem homHilbert_add_finrank_inf (J : Ideal (MvPolynomial σ K)) (t : ℕ) :
    homHilbert J t + finrank K ↥(J.restrictScalars K ⊓ homogeneousSubmodule σ K t) =
      finrank K (homogeneousSubmodule σ K t) :=
  finrank_map_mkₐ_add_finrank_inf J _

/-- Blueprint B01 (rank–nullity): `homHilbert J t + dim_K J_t = dim_K P_t`, with `J_t` as a
subspace of `P_t`. -/
theorem homHilbert_add_finrank_comap_subtype (J : Ideal (MvPolynomial σ K)) (t : ℕ) :
    homHilbert J t +
      finrank K ((J.restrictScalars K).comap (homogeneousSubmodule σ K t).subtype) =
      finrank K (homogeneousSubmodule σ K t) :=
  finrank_map_mkₐ_add_finrank_comap_subtype J _

/-- Blueprint B01: `homHilbert` is antitone in the ideal. -/
theorem homHilbert_anti {A B : Ideal (MvPolynomial σ K)} (h : A ≤ B) (t : ℕ) :
    homHilbert B t ≤ homHilbert A t := by
  rw [homHilbert, homHilbert, map_mkₐ_eq_map_factor h]
  exact Submodule.finrank_map_le _ _

/-- Blueprint B01/B02: `homHilbert J t ≤ dim_K P_t`. -/
theorem homHilbert_le (J : Ideal (MvPolynomial σ K)) (t : ℕ) :
    homHilbert J t ≤ finrank K (homogeneousSubmodule σ K t) :=
  Submodule.finrank_map_le _ _

end HomHilbert

/-! ### Homogeneous components -/

section Components

/-- Blueprint A02/B01 (risk 3): homogeneous components of a finite sum. -/
theorem homogeneousComponent_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ K)
    (n : ℕ) :
    homogeneousComponent n (∑ i ∈ s, f i) = ∑ i ∈ s, homogeneousComponent n (f i) :=
  map_sum _ _ _

/-- Blueprint A02/B01 (risk 3): the degree-`(m + n)` component of `F * G`, for a form `F` of
degree `m`, is `F` times the degree-`n` component of `G`. -/
theorem homogeneousComponent_mul_of_isHomogeneous {F : MvPolynomial σ K} {m : ℕ}
    (hF : F.IsHomogeneous m) (n : ℕ) (G : MvPolynomial σ K) :
    homogeneousComponent (m + n) (F * G) = F * homogeneousComponent n G := by
  induction G using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [homogeneousComponent_of_mem (hF.mul (isHomogeneous_monomial c rfl)),
      homogeneousComponent_of_mem (isHomogeneous_monomial c rfl)]
    by_cases h : n = d.degree
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (by omega), mul_zero]
  | add p q hp hq =>
    rw [mul_add, map_add, map_add, hp, hq, mul_add]

/-- Blueprint A02/B01 (risk 3): the degree-`(n + m)` component of `G * F`, for a form `F` of
degree `m`, is `(G)_n * F`. -/
theorem homogeneousComponent_mul_of_isHomogeneous' {F : MvPolynomial σ K} {m : ℕ}
    (hF : F.IsHomogeneous m) (n : ℕ) (G : MvPolynomial σ K) :
    homogeneousComponent (n + m) (G * F) = homogeneousComponent n G * F := by
  rw [mul_comm, add_comm, homogeneousComponent_mul_of_isHomogeneous hF, mul_comm]

/-- Blueprint A05: every exponent in the support of a form of degree `t` has degree `t`. -/
theorem degree_eq_of_isHomogeneous {F : MvPolynomial σ K} {t : ℕ} (hF : F.IsHomogeneous t)
    {d : σ →₀ ℕ} (hd : d ∈ F.support) : d.degree = t := by
  rw [Finsupp.degree_eq_weight_one]
  exact hF (mem_support_iff.mp hd)

end Components

/-! ### Graded pieces of sums and intersections of homogeneous ideals -/

section Pieces

variable {A B : Ideal (MvPolynomial σ K)}

/-- Blueprint B02(i): the degree-`t` piece of `A ⊓ B` (no homogeneity needed). -/
theorem inf_homogeneousSubmodule_inf (A B : Ideal (MvPolynomial σ K)) (t : ℕ) :
    (A ⊓ B).restrictScalars K ⊓ homogeneousSubmodule σ K t =
      (A.restrictScalars K ⊓ homogeneousSubmodule σ K t) ⊓
        (B.restrictScalars K ⊓ homogeneousSubmodule σ K t) := by
  ext x
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem]
  tauto

/-- Blueprint B02(i): the degree-`t` piece of `A ⊔ B` is `A_t ⊔ B_t` for homogeneous `A, B`. -/
theorem inf_homogeneousSubmodule_sup (hA : A.IsHomogeneous (homogeneousSubmodule σ K))
    (hB : B.IsHomogeneous (homogeneousSubmodule σ K)) (t : ℕ) :
    (A ⊔ B).restrictScalars K ⊓ homogeneousSubmodule σ K t =
      (A.restrictScalars K ⊓ homogeneousSubmodule σ K t) ⊔
        (B.restrictScalars K ⊓ homogeneousSubmodule σ K t) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxAB, hxt⟩ := Submodule.mem_inf.mp hx
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      Submodule.mem_sup.mp ((Submodule.restrictScalars_mem _ _ _).mp hxAB)
    have hx : homogeneousComponent t (a + b) = a + b := homogeneousComponent_eq_self hxt
    rw [map_add] at hx
    rw [← hx, Submodule.mem_sup]
    exact ⟨_, ⟨homogeneousComponent_mem_of_mem hA ha t, homogeneousComponent_mem _ _⟩,
      _, ⟨homogeneousComponent_mem_of_mem hB hb t, homogeneousComponent_mem _ _⟩, rfl⟩
  · exact sup_le (inf_le_inf_right _ (Submodule.restrictScalars_mono K le_sup_left))
      (inf_le_inf_right _ (Submodule.restrictScalars_mono K le_sup_right))

/-- Blueprint B02(i): inclusion–exclusion for the homogeneous Hilbert function of homogeneous
ideals: `homHilbert (A ⊓ B) t + homHilbert (A ⊔ B) t = homHilbert A t + homHilbert B t`. -/
theorem homHilbert_inf_add_homHilbert_sup [Finite σ]
    (hA : A.IsHomogeneous (homogeneousSubmodule σ K))
    (hB : B.IsHomogeneous (homogeneousSubmodule σ K)) (t : ℕ) :
    homHilbert (A ⊓ B) t + homHilbert (A ⊔ B) t = homHilbert A t + homHilbert B t := by
  have hAt : FiniteDimensional K ↥(A.restrictScalars K ⊓ homogeneousSubmodule σ K t) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have hBt : FiniteDimensional K ↥(B.restrictScalars K ⊓ homogeneousSubmodule σ K t) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have h1 := homHilbert_add_finrank_inf A t
  have h2 := homHilbert_add_finrank_inf B t
  have h3 := homHilbert_add_finrank_inf (A ⊓ B) t
  have h4 := homHilbert_add_finrank_inf (A ⊔ B) t
  rw [inf_homogeneousSubmodule_inf] at h3
  rw [inf_homogeneousSubmodule_sup hA hB] at h4
  have h5 := Submodule.finrank_sup_add_finrank_inf_eq
    (A.restrictScalars K ⊓ homogeneousSubmodule σ K t)
    (B.restrictScalars K ⊓ homogeneousSubmodule σ K t)
  omega

end Pieces

/-! ### Homogeneous ideals and the ideal of the variables -/

section IdealOfVars

/-- Blueprint A02.b: a form of degree `t ≥ 1` lies in the ideal `𝔪 = (X i)_i` of the
variables. -/
theorem mem_idealOfVars_of_isHomogeneous {F : MvPolynomial σ K} {t : ℕ} (hF : F.IsHomogeneous t)
    (ht : 1 ≤ t) : F ∈ idealOfVars σ K := by
  rw [← pow_one (idealOfVars σ K), mem_pow_idealOfVars_iff]
  intro d hd
  rw [degree_eq_of_isHomogeneous hF hd]
  exact ht

/-- Blueprint A02.b: a homogeneous ideal containing a nonzero constant is the unit ideal. -/
theorem eq_top_of_C_mem {J : Ideal (MvPolynomial σ K)} {c : K} (hc : c ≠ 0) (h : C c ∈ J) :
    J = ⊤ :=
  J.eq_top_of_isUnit_mem h ((isUnit_map_iff C c).mpr hc.isUnit)

/-- Blueprint A02.b: a proper homogeneous ideal is contained in the ideal `𝔪 = (X i)_i` of the
variables (its elements have zero constant term). -/
theorem le_idealOfVars_of_isHomogeneous {J : Ideal (MvPolynomial σ K)}
    (hJ : J.IsHomogeneous (homogeneousSubmodule σ K)) (hJ' : J ≠ ⊤) : J ≤ idealOfVars σ K := by
  intro x hx
  have h0 := homogeneousComponent_mem_of_mem hJ hx 0
  rw [homogeneousComponent_zero] at h0
  have hc : coeff 0 x = 0 := by
    by_contra hc
    exact hJ' (eq_top_of_C_mem hc h0)
  rw [← pow_one (idealOfVars σ K), mem_pow_idealOfVars_iff']
  intro d hd
  rw [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at hd
  rw [hd]
  exact hc

/-- Blueprint A05: a homogeneous ideal containing `X i - C c` with `c ≠ 0` is the unit ideal. -/
theorem eq_top_of_isHomogeneous_of_X_sub_C_mem {J : Ideal (MvPolynomial σ K)}
    (hJ : J.IsHomogeneous (homogeneousSubmodule σ K)) {i : σ} {c : K} (hc : c ≠ 0)
    (h : X i - C c ∈ J) : J = ⊤ := by
  have h0 := homogeneousComponent_mem_of_mem hJ h 0
  rw [homogeneousComponent_zero, coeff_sub, coeff_zero_X, coeff_zero_C, zero_sub] at h0
  exact eq_top_of_C_mem (neg_ne_zero.mpr hc) h0

/-- Blueprint A05: a homogeneous ideal containing `X i - 1` contains `1`. -/
theorem one_mem_of_isHomogeneous_of_X_sub_one_mem {J : Ideal (MvPolynomial σ K)}
    (hJ : J.IsHomogeneous (homogeneousSubmodule σ K)) {i : σ} (h : X i - 1 ∈ J) :
    (1 : MvPolynomial σ K) ∈ J := by
  rw [← C_1] at h
  rw [eq_top_of_isHomogeneous_of_X_sub_C_mem hJ one_ne_zero h]
  exact Submodule.mem_top

end IdealOfVars

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
