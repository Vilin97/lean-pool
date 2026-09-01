/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Data.FunLike.Fintype

import LeanPool.QuadraticIterates.ArchMath1992.Irreducibility
import LeanPool.QuadraticIterates.Mathlib.Algebra.Polynomial.Roots
import LeanPool.QuadraticIterates.Mathlib.GroupTheory.RegularWreathProduct

/-!
# The relative degree `[K_{n+1} : K_n]`

`K_{n+1}` is generated over `K_n` by square roots of the shifted roots `β - a` of `f_n`
(`rootShift`), so its relative degree is `2` to the power of `2^n` minus the dimension of the
`𝔽₂`-space of multiplicative relations among them (`relfinrank_succ_eq_pow`). The relation space is
trivial exactly when `c_{n+1}` is not a square in `K_n`, which is Lemma 1.6 (`degree_criterion`);
Lemma 1.5 (`kummer_extension_criterion`) then says which rationals stay non-squares in `K_n`.

Part of the formalization of M. Stoll, *Galois groups over ℚ of some iterated polynomials*,
Arch. Math. **59** (1992), 239-244; see `QuadraticIterates.ArchMath1992`.
-/

open Polynomial

namespace QuadraticIterates

section

variable (a : ℤ)

/-! ### The relative degree `[K_{n+1} : K_n]` -/

/-- The shifted root `β - a` of `f_n`, as an element of `K_n`: these are the radicands whose
square roots generate `K_{n+1}` over `K_n`. -/
noncomputable def rootShift (a : ℤ) (n : ℕ) (β : (fℚ[a, n]).rootSet (AlgebraicClosure ℚ)) :
    ↥(splittingField a n) :=
  ⟨(β : AlgebraicClosure ℚ) - (a : AlgebraicClosure ℚ),
    sub_mem (IntermediateField.subset_adjoin ℚ _ β.2) (IntermediateField.intCast_mem _ a)⟩

@[simp] lemma coe_rootShift (n : ℕ) (β : (fℚ[a, n]).rootSet (AlgebraicClosure ℚ)) :
    (rootShift a n β : AlgebraicClosure ℚ)
      = (β : AlgebraicClosure ℚ) - (a : AlgebraicClosure ℚ) := rfl

lemma rootShift_ne_zero (ha : ¬IsSquare (-a : ℚ)) {n : ℕ} (hn : 1 ≤ n)
    (β : (fℚ[a, n]).rootSet (AlgebraicClosure ℚ)) : rootShift a n β ≠ 0 := by
  rw [ne_eq, Subtype.ext_iff, coe_rootShift]
  simpa using sub_intCast_ne_zero_of_mem_rootSet a ha hn β.2

/-- The relative degree `[K_{n+1} : K_n]` equals `2 ^ (2^n - d)`, where `d` is the `𝔽₂`-dimension
of the multiquadratic relations among the shifted roots `β - a` of `f_n`. -/
theorem relfinrank_succ_eq_pow {n : ℕ} (hn : 1 ≤ n) (hirr : Irreducible (fℚ[a, n])) :
    (splittingField a n).relfinrank (splittingField a (n + 1))
      = 2 ^ (2 ^ n - Module.finrank (ZMod 2) (rootRelations (rootShift a n))) := by
  classical
  have hnsq : ¬IsSquare (-a : ℚ) := not_isSquare_neg_of_irreducible a hn hirr
  choose g hg using exists_sq_eq_sub a
  set x : ↥((fℚ[a, n]).rootSet (AlgebraicClosure ℚ)) → AlgebraicClosure ℚ := fun β ↦ g β
  have hx (β) :
      x β ^ 2 = algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ) (rootShift a n β) :=
    hg β.1
  have hxinj : Function.Injective x := by
    intro β β' h
    have h2 : (β : AlgebraicClosure ℚ) - (a : AlgebraicClosure ℚ)
        = (β' : AlgebraicClosure ℚ) - (a : AlgebraicClosure ℚ) := by
      rw [← hg β.1, ← hg β'.1]
      exact congrArg (· ^ 2) h
    exact Subtype.ext (by linear_combination h2)
  have hset : g '' ((fℚ[a, n]).rootSet (AlgebraicClosure ℚ))
      = Set.range x := Set.image_eq_range g _
  rw [relfinrank_succ_eq_finrank_adjoin a n g hg, hset,
    multiquadratic_degree_family hxinj hx (rootShift_ne_zero a hnsq hn),
    card_rootSet_iteratedPoly a hirr]

lemma exists_ringEquiv_radicand_smul {n : ℕ}
    [Fact (map (algebraMap ℚ (AlgebraicClosure ℚ)) (fℚ[a, n])).Splits]
    (r : ((fℚ[a, n]).rootSet (AlgebraicClosure ℚ))
        → ↥(splittingField a n))
    (hr : ∀ β, (algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ) (r β))
      = (β : AlgebraicClosure ℚ) - (a : AlgebraicClosure ℚ)) (σ : GaloisGroup a n) :
    ∃ φ : (↥(splittingField a n)) ≃+* (↥(splittingField a n)), ∀ β, φ (r β) = r (σ • β) := by
  have : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  obtain ⟨ϕ, rfl⟩ := Gal.restrict_surjective (fℚ[a, n]) (AlgebraicClosure ℚ) σ
  refine ⟨(ϕ.restrictNormal (splittingField a n)).toRingEquiv, fun β ↦ ?_⟩
  apply (algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ)).injective
  have hσβ : (((Gal.restrict (fℚ[a, n]) (AlgebraicClosure ℚ)) ϕ • β :
      ↥((fℚ[a, n]).rootSet (AlgebraicClosure ℚ))) :
        AlgebraicClosure ℚ) = ϕ (β : AlgebraicClosure ℚ) :=
    Gal.restrict_smul ϕ β
  have hcomm : algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ)
      ((ϕ.restrictNormal (splittingField a n)).toRingEquiv (r β))
      = ϕ (algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ) (r β)) :=
    AlgEquiv.restrictNormal_commutes ϕ (splittingField a n) (r β)
  rw [hcomm, hr β, hr _, hσβ, map_sub, map_intCast]

lemma isPretransitive_galoisGroup (n : ℕ)
    (hirr : Irreducible (fℚ[a, n]))
    [Fact (map (algebraMap ℚ (AlgebraicClosure ℚ)) (fℚ[a, n])).Splits] :
    MulAction.IsPretransitive (GaloisGroup a n)
      ↑((fℚ[a, n]).rootSet (AlgebraicClosure ℚ)) :=
  Gal.galAction_isPretransitive (fℚ[a, n]) (AlgebraicClosure ℚ) hirr

lemma prod_aroots_sub_eq_cSeq (n : ℕ) :
    (Multiset.map (fun α ↦ α - (a : AlgebraicClosure ℚ))
        ((fℚ[a, n]).aroots (AlgebraicClosure ℚ))).prod
      = (cSeq a (n + 1) : AlgebraicClosure ℚ) := by
  set F := fℚ[a, n] with hF
  have hmonic : F.Monic := (monic_iteratedPoly a n).map (Int.castRingHom ℚ)
  have hsplits : (F.map (algebraMap ℚ (AlgebraicClosure ℚ))).Splits := IsAlgClosed.splits _
  have hcard : (F.aroots (AlgebraicClosure ℚ)).card = 2 ^ n := by
    rw [aroots_def, ← hsplits.natDegree_eq_card_roots, hmonic.natDegree_map, hF,
      (monic_iteratedPoly a n).natDegree_map, natDegree_iteratedPoly]
  calc (Multiset.map (fun α ↦ α - (a : AlgebraicClosure ℚ))
          (F.aroots (AlgebraicClosure ℚ))).prod
      = (((F.aroots (AlgebraicClosure ℚ)).map
          (fun α ↦ (a : AlgebraicClosure ℚ) - α)).map (fun x ↦ -x)).prod := by
        rw [Multiset.map_map]
        exact congrArg _ (Multiset.map_congr rfl fun α _ ↦ by simp)
    _ = (-1 : AlgebraicClosure ℚ) ^ (F.aroots (AlgebraicClosure ℚ)).card
          * ((F.aroots (AlgebraicClosure ℚ)).map
              (fun α ↦ (a : AlgebraicClosure ℚ) - α)).prod := by
        rw [Multiset.prod_map_neg, Multiset.card_map]
    _ = (-1 : AlgebraicClosure ℚ) ^ 2 ^ n
          * (aeval (a : AlgebraicClosure ℚ)) F := by
        rw [hcard, ← hsplits.aeval_eq_prod_aroots_of_monic hmonic (a : AlgebraicClosure ℚ)]
    _ = (-1 : AlgebraicClosure ℚ) ^ 2 ^ n
          * (((iteratedPoly a n).eval a : ℤ) : AlgebraicClosure ℚ) := by
        rw [hF, aeval_intCast_map]
    _ = (cSeq a (n + 1) : AlgebraicClosure ℚ) := by
        rw [cSeq_succ_eq_neg_one_pow_mul_eval a n]
        push_cast
        ring

lemma prod_radicand_eq_cSeq {n : ℕ} (hirr : Irreducible (fℚ[a, n]))
    (r : ((fℚ[a, n]).rootSet (AlgebraicClosure ℚ))
        → ↥(splittingField a n))
    (hr : ∀ β, (algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ) (r β))
      = (β : AlgebraicClosure ℚ) - (a : AlgebraicClosure ℚ)) :
    ∏ β, r β = algebraMap ℚ ↥(splittingField a n) (cSeq a (n + 1) : ℚ) := by
  classical
  apply (algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ)).injective
  have hnodup : ((fℚ[a, n]).aroots (AlgebraicClosure ℚ)).Nodup := nodup_roots hirr.separable.map
  have hleft : algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ) (∏ β, r β)
      = ∏ β : ↥((fℚ[a, n]).rootSet (AlgebraicClosure ℚ)),
          ((β : AlgebraicClosure ℚ) - (a : AlgebraicClosure ℚ)) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun β _ ↦ hr β
  have hright : algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ)
      (algebraMap ℚ (↥(splittingField a n)) (cSeq a (n + 1) : ℚ))
      = (cSeq a (n + 1) : AlgebraicClosure ℚ) := by
    simp
  rw [hleft, prod_rootSet_eq_prod_aroots hnodup (· - (a : AlgebraicClosure ℚ)), hright]
  exact prod_aroots_sub_eq_cSeq a n

end

section

variable (a : ℤ)

/-! ### The degree criterion and the Kummer extension criterion -/

/-- If `-a` is not a rational square, `K_1 = ℚ(√(-a))` has degree `2` over `ℚ`. -/
lemma finrank_splittingField_one (hsq : ¬IsSquare (-a : ℚ)) :
    Module.finrank ℚ ↥(splittingField a 1) = 2 := by
  classical
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq
    (-(algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ))) (n := 2) (by norm_num)
  have hβsq : β ^ 2 = algebraMap ℚ (AlgebraicClosure ℚ) (-a : ℚ) := by rw [hβ, map_neg]
  have hpoly := map_iteratedPoly_one a
  have hβroot : β ∈ (fℚ[a, 1]).rootSet (AlgebraicClosure ℚ) := by
    rw [mem_rootSet', hpoly]
    refine ⟨?_, ?_⟩
    · rw [Polynomial.map_add, Polynomial.map_pow, map_X, map_C]
      exact X_pow_add_C_ne_zero (by norm_num) _
    · simp [map_add, map_pow, aeval_X, hβ]
  have hadjeq : splittingField a 1 = IntermediateField.adjoin ℚ {β} := by
    apply le_antisymm
    · refine IntermediateField.adjoin_le_iff.mpr fun x hx ↦ ?_
      rw [mem_rootSet', hpoly] at hx
      obtain ⟨-, hx2⟩ := hx
      simp only [map_add, map_pow, aeval_X, aeval_C] at hx2
      have hβmem : β ∈ IntermediateField.adjoin ℚ ({β} : Set (AlgebraicClosure ℚ)) :=
        IntermediateField.subset_adjoin ℚ _ rfl
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp
        (show x ^ 2 = β ^ 2 by linear_combination hx2 - hβ) with rfl | rfl
      · exact hβmem
      · exact neg_mem hβmem
    · refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro x rfl
      exact IntermediateField.subset_adjoin ℚ _ hβroot
  rw [hadjeq, finrank_adjoin_sq_eq hβsq, ite_eq_right hsq]

lemma degree_criterion_zero :
    (splittingField a 0).relfinrank (splittingField a 1) = 2 ^ 2 ^ 0 ↔
      ¬IsSquare (algebraMap ℚ ↥(splittingField a 0) (cSeq a (0 + 1) : ℚ)) := by
  have hK0bot := splittingField_zero_eq_bot a
  have hrf : (splittingField a 0).relfinrank (splittingField a 1)
      = Module.finrank ℚ ↥(splittingField a 1) := by
    rw [hK0bot, IntermediateField.relfinrank_bot_left]
  have hsq_iff : IsSquare (algebraMap ℚ ↥(splittingField a 0) (cSeq a (0 + 1) : ℚ))
      ↔ IsSquare (-a : ℚ) := by
    rw [hK0bot, show (cSeq a (0 + 1) : ℚ) = -(a : ℚ) by norm_num]
    exact isSquare_algebraMap_bot_iff _
  rw [hrf, hsq_iff]
  by_cases hsq : IsSquare (-a : ℚ)
  · rw [splittingField_one_eq_bot_of_isSquare a hsq, IntermediateField.finrank_bot]
    simp [hsq]
  · simp only [hsq, not_false_iff, iff_true, pow_zero, pow_one]
    exact finrank_splittingField_one a hsq

/-- Lemma 1.6: if `f_n` is irreducible over `ℚ`, then `[K_{n+1} : K_n] = 2^{2^n}` iff `c_{n+1}`
is not a square in `K_n`. -/
theorem degree_criterion {n : ℕ} (hirr : Irreducible (fℚ[a, n])) :
    (splittingField a n).relfinrank (splittingField a (n + 1)) = 2 ^ 2 ^ n ↔
      ¬IsSquare (algebraMap ℚ ↥(splittingField a n) (cSeq a (n + 1) : ℚ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact degree_criterion_zero a
  · have hna : ¬IsSquare (-a : ℚ) := not_isSquare_neg_of_irreducible a hn hirr
    have hrne := rootShift_ne_zero a hna hn
    have : Fact (map (algebraMap ℚ (AlgebraicClosure ℚ))
        (fℚ[a, n])).Splits := ⟨IsAlgClosed.splits _⟩
    have hcard := card_rootSet_iteratedPoly a hirr
    have : Nonempty ↥((fℚ[a, n]).rootSet (AlgebraicClosure ℚ)) :=
      Fintype.card_pos_iff.mp (by rw [hcard]; positivity)
    have hdle : Module.finrank (ZMod 2) (rootRelations (rootShift a n)) ≤ 2 ^ n := by
      rw [← hcard]
      exact rootRelations_finrank_le _
    have : MulAction.IsPretransitive (GaloisGroup a n)
        ↥((fℚ[a, n]).rootSet (AlgebraicClosure ℚ)) :=
      isPretransitive_galoisGroup a n hirr
    have hrfd : (splittingField a n).relfinrank (splittingField a (n + 1)) = 2 ^ 2 ^ n
        ↔ Module.finrank (ZMod 2) (rootRelations (rootShift a n)) = 0 := by
      rw [relfinrank_succ_eq_pow a hn hirr, Nat.pow_right_inj (by norm_num : 1 < 2)]
      lia
    have hallne : (fun _ ↦ (1 : ZMod 2)) ∈ rootRelations (rootShift a n)
        ↔ rootRelations (rootShift a n) ≠ ⊥ := by
      refine ⟨fun hmem hbot ↦ one_ne_zero (α := ZMod 2) ?_,
        fun hbot ↦ rootRelations_all_ones (isPGroup_galoisGroup a n) hrne ?_ hbot⟩
      · rw [hbot, Submodule.mem_bot] at hmem
        exact congrFun hmem (Classical.arbitrary _)
      · exact exists_ringEquiv_radicand_smul a (rootShift a n) fun _ ↦ rfl
    have hallsq : (fun _ ↦ (1 : ZMod 2)) ∈ rootRelations (rootShift a n)
        ↔ IsSquare (algebraMap ℚ ↥(splittingField a n) (cSeq a (n + 1) : ℚ)) :=
      (all_ones_mem_rootRelations hrne).trans
        (by rw [prod_radicand_eq_cSeq a hirr (rootShift a n) fun _ ↦ rfl])
    rw [hrfd, Submodule.finrank_eq_zero, ← not_iff_not]
    simpa using hallne.symm.trans hallsq

lemma finrank_eq_of_nonempty_mulEquiv {n : ℕ}
    (hiso : Nonempty (GaloisGroup a n ≃* WreathPower n)) :
    Module.finrank ℚ ↥(splittingField a n) = 2 ^ (2 ^ n - 1) := by
  rw [← card_galoisGroup_eq_finrank a n, Nat.card_congr hiso.some.toEquiv, card_wreathPower]

/-- Package a family of square roots `x i` of the `algebraMap`-images of nonzero rationals `v i`
as the finset `Finset.univ.image x` together with a coefficient function `cf`, in the form
consumed by the multiquadratic API (`multiquadratic_degree`, `square_descent`). -/
private lemma exists_coeffs_of_sq_eq_algebraMap {K : Type*} [Field K] [Algebra ℚ K]
    [DecidableEq K] {n : ℕ}
    {v : Fin n → ℚ} (hv0 : ∀ i, v i ≠ 0) {x : Fin n → K} (hxinj : Function.Injective x)
    (hx : ∀ i, x i ^ 2 = algebraMap ℚ K (v i)) :
    ∃ cf : K → ℚ,
      (∀ i, cf (x i) = v i) ∧
      (∀ y ∈ Finset.univ.image x, y ^ 2 = algebraMap ℚ K (cf y)) ∧
      (∀ y ∈ Finset.univ.image x, cf y ≠ 0) ∧
      ∀ S : Finset (Fin n), ∏ y ∈ S.image x, cf y = ∏ i ∈ S, v i := by
  classical
  refine ⟨Function.extend x v 1, fun i ↦ hxinj.extend_apply _ _ i, ?_, ?_, fun S ↦ ?_⟩
  · intro y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    rw [hxinj.extend_apply]
    exact hx i
  · intro y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    rw [hxinj.extend_apply]
    exact hv0 i
  · rw [Finset.prod_image fun i _ j _ h ↦ hxinj h]
    exact Finset.prod_congr rfl fun i _ ↦ hxinj.extend_apply _ _ i

lemma finrank_adjoin_range_eq_two_pow {n : ℕ}
    (hindep : TwoIndependent (fun i : Fin n ↦ (cSeq a ((i : ℕ) + 1) : ℚ)))
    {x : Fin n → ↥(splittingField a n)}
    (hx : ∀ i, x i ^ 2 = algebraMap ℚ ↥(splittingField a n) (cSeq a ((i : ℕ) + 1) : ℚ)) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ (Set.range x)) = 2 ^ n := by
  classical
  have hxinj : Function.Injective x := hindep.sqrt_injective hx
  obtain ⟨cf, hcf_eq, hs_sq, hs_ne, hprodS⟩ := exists_coeffs_of_sq_eq_algebraMap hindep.1 hxinj hx
  set s : Finset ↥(splittingField a n) := Finset.univ.image x with hs
  have hrange : (s : Set ↥(splittingField a n)) = Set.range x := by
    simp [hs, Finset.coe_image]
  have hscard : s.card = n := by
    rw [hs, Finset.card_image_of_injective _ hxinj, Finset.card_univ, Fintype.card_fin]
  have hrelbot : multiquadraticRelations s cf = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro ε hε
    obtain ⟨hεsupp, hεsq⟩ := (mem_multiquadraticRelations hs_ne).mp hε
    set S : Finset (Fin n) := Finset.univ.filter (fun i ↦ ε (x i) = 1) with hS
    have hfilter_img : s.filter (fun y ↦ ε y = 1) = S.image x := by
      simpa [hs, hS] using Finset.filter_image (p := fun y ↦ ε y = 1) (f := x)
        (s := Finset.univ)
    rw [hfilter_img, hprodS S] at hεsq
    have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp fun hSnon ↦ hindep.2 S hSnon hεsq
    funext y
    by_cases hy : y ∈ s
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (hs ▸ hy)
      have hne1 : ¬ ε (x i) = 1 := fun h1 ↦ Finset.notMem_empty i (hSempty ▸ (by
        rw [hS]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1⟩ : i ∈ S))
      exact ((by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (ε (x i))).resolve_right hne1
    · exact hεsupp y hy
  rw [← hrange, multiquadratic_degree hs_sq hs_ne, hscard, hrelbot, finrank_bot, Nat.sub_zero]

lemma card_monoidHom_eq_two_pow {n : ℕ} (hiso : Nonempty (GaloisGroup a n ≃* WreathPower n)) :
    Nat.card (((splittingField a n) ≃ₐ[ℚ] (splittingField a n)) →*
      Multiplicative (ZMod 2)) = 2 ^ n := by
  refine (Nat.card_congr ?_).trans (wreath_max_elem_ab n)
  exact ((AlgEquiv.autCongr (IsSplittingField.algEquiv _ (fℚ[a, n]))).trans
    hiso.some).monoidHomCongrLeftEquiv

lemma finrank_adjoin_le_two_pow {n : ℕ} (hiso : Nonempty (GaloisGroup a n ≃* WreathPower n))
    (t : Finset ↥(splittingField a n))
    (ht : ∀ y ∈ t, ∃ q : ℚ, y ^ 2 = algebraMap ℚ ↥(splittingField a n) q) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ (t : Set ↥(splittingField a n))) ≤ 2 ^ n := by
  set M := IntermediateField.adjoin ℚ (t : Set ↥(splittingField a n))
  have hgalM : IsGalois ℚ ↥M := isGalois_adjoin_of_sq_eq_algebraMap ht
  have hexp : ∀ τ : ↥M ≃ₐ[ℚ] ↥M, τ ^ 2 = 1 := algEquiv_adjoin_sq_eq_one ht
  have hinv (g : ↥M ≃ₐ[ℚ] ↥M) : g⁻¹ = g := (eq_inv_of_mul_eq_one_left (sq (a := g) ▸ hexp g)).symm
  rw [← IsGalois.card_aut_eq_finrank ℚ ↥M,
    elem_ab_card_hom (↥M ≃ₐ[ℚ] ↥M)
      (fun σ τ ↦ by simpa [hinv] using ((hinv (σ * τ)).symm.trans (mul_inv_rev σ τ))) hexp]
  have hfin : Finite ((↥(splittingField a n) ≃ₐ[ℚ] ↥(splittingField a n)) →*
      Multiplicative (ZMod 2)) := DFunLike.finite _
  refine le_trans (Nat.card_le_card_of_injective
    (fun φ ↦ φ.comp (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := splittingField a n) ↥M)) ?_)
    (card_monoidHom_eq_two_pow a hiso).le
  intro φ₁ φ₂ hφ
  ext x
  obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (splittingField a n) x
  exact DFunLike.congr_fun hφ g

/-- If `Ω_n ≅ [C_2]^n` and the `c_i` are 2-independent with square roots `x i` in `K_n`, then for
nonzero `c : ℚ`, the image of `c` in `K_n` is a square iff it is the square of some
`z ∈ IntermediateField.adjoin ℚ (Set.range x)`. -/
theorem isSquare_algebraMap_iff_exists_sq_eq {n : ℕ}
    (hiso : Nonempty (GaloisGroup a n ≃* WreathPower n))
    (hindep : TwoIndependent (fun i : Fin n ↦ (cSeq a ((i : ℕ) + 1) : ℚ)))
    {x : Fin n → ↥(splittingField a n)}
    (hx : ∀ i, x i ^ 2 = algebraMap ℚ ↥(splittingField a n) (cSeq a ((i : ℕ) + 1) : ℚ))
    {c : ℚ} (hc : c ≠ 0) :
    IsSquare (algebraMap ℚ ↥(splittingField a n) c) ↔
      ∃ z ∈ IntermediateField.adjoin ℚ (Set.range x),
        z ^ 2 = algebraMap ℚ ↥(splittingField a n) c := by
  classical
  refine ⟨fun hsq ↦ ?_, fun ⟨z, hzmem, hz2⟩ ↦ (isSquare_iff_exists_sq _).mpr ⟨z, hz2.symm⟩⟩
  obtain ⟨w, hw2⟩ := hsq.exists_sq
  replace hw2 := hw2.symm
  have hxinj : Function.Injective x := hindep.sqrt_injective hx
  suffices hwM : w ∈ IntermediateField.adjoin ℚ (Set.range x) from ⟨w, hwM, hw2⟩
  by_contra hwnotM
  have hwnotr : w ∉ Set.range x := fun hr ↦ hwnotM (IntermediateField.subset_adjoin ℚ _ hr)
  have hnotsqM : ¬ IsSquare (algebraMap ℚ ↥(IntermediateField.adjoin ℚ (Set.range x)) c) :=
    not_isSquare_algebraMap_of_sqrt_notMem hw2 hwnotM
  have hinsdeg : Module.finrank ℚ
      (IntermediateField.adjoin ℚ (insert w (Set.range x))) = 2 ^ (n + 1) :=
    multiquadratic_degree_insert_family hxinj hx hindep.1 hwnotr hw2 hc
      (finrank_adjoin_range_eq_two_pow a hindep hx) hnotsqM
  have hle : Module.finrank ℚ
      (IntermediateField.adjoin ℚ (insert w (Set.range x))) ≤ 2 ^ n := by
    have h := finrank_adjoin_le_two_pow a hiso (insert w (Finset.univ.image x)) (fun y hy ↦ by
      rcases Finset.mem_insert.mp hy with rfl | hys
      · exact ⟨c, hw2⟩
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hys
        exact ⟨_, hx i⟩)
    rwa [Finset.coe_insert, Finset.coe_image, Finset.coe_univ, Set.image_univ] at h
  rw [hinsdeg] at hle
  exact absurd hle (by simp [pow_succ])

lemma isSquare_algebraMap_cSeq (n : ℕ) (hnsq : ¬IsSquare (-a : ℚ)) (m : ℕ) (hm1 : 1 ≤ m)
    (hmn : m ≤ n) :
    IsSquare (algebraMap ℚ ↥(splittingField a n) (cSeq a m : ℚ)) := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : m ≠ 0)
  have hmono : splittingField a (k + 1) ≤ splittingField a n := splittingField_mono a hmn
  have hinj := (algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ)).injective
  have hsqrt (β : ↥((fℚ[a, k]).rootSet (AlgebraicClosure ℚ))) :
      ∃ γ : ↥(splittingField a n),
        (algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ) γ) ^ 2
          = (β : AlgebraicClosure ℚ) - (a : AlgebraicClosure ℚ) := by
    obtain ⟨δ, hδ⟩ := exists_sq_eq_sub a β
    have hroot : δ ∈ (fℚ[a, k + 1]).rootSet (AlgebraicClosure ℚ) :=
      (mem_rootSet_iteratedPoly_succ a k δ).mpr (by simp [hδ, sub_add_cancel, β.2])
    exact ⟨⟨δ, hmono (IntermediateField.subset_adjoin ℚ _ hroot)⟩, hδ⟩
  choose w hw using hsqrt
  have hnodup : ((fℚ[a, k]).aroots (AlgebraicClosure ℚ)).Nodup := by
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp
    · exact nodup_roots (irreducible_iteratedPoly_of_pos a hnsq hkpos).separable.map
  refine ⟨∏ β, w β, hinj ?_⟩
  have hlhs : algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ)
      ((algebraMap ℚ (↥(splittingField a n))) (cSeq a (k + 1) : ℚ))
      = (cSeq a (k + 1) : AlgebraicClosure ℚ) := by
    simp
  rw [hlhs, map_mul, map_prod]
  have hsplit : (∏ β, algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ) (w β))
        * (∏ β, algebraMap (↥(splittingField a n)) (AlgebraicClosure ℚ) (w β))
      = ∏ β : ↥((fℚ[a, k]).rootSet (AlgebraicClosure ℚ)),
          ((β : AlgebraicClosure ℚ) - (a : AlgebraicClosure ℚ)) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun β _ ↦ by rw [← sq, hw β]
  rw [hsplit, prod_rootSet_eq_prod_aroots hnodup (· - (a : AlgebraicClosure ℚ))]
  exact (prod_aroots_sub_eq_cSeq a k).symm

lemma isSquare_algebraMap_iff_exists_mul_prod {n : ℕ}
    (hiso : Nonempty (GaloisGroup a n ≃* WreathPower n))
    (hindep : TwoIndependent (fun i : Fin n ↦ (cSeq a ((i : ℕ) + 1) : ℚ))) {c : ℚ} (hc : c ≠ 0) :
    IsSquare (algebraMap ℚ ↥(splittingField a n) c) ↔
      ∃ S : Finset (Fin n), IsSquare (c * ∏ i ∈ S, (cSeq a ((i : ℕ) + 1) : ℚ)) := by
  classical
  have hmax := finrank_eq_of_nonempty_mulEquiv a hiso
  have hroot (i : Fin n) :
      IsSquare (algebraMap ℚ ↥(splittingField a n) (cSeq a ((i : ℕ) + 1) : ℚ)) := by
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · exact absurd i.2 (by simp)
    · have hnsq : ¬IsSquare (-a : ℚ) := not_isSquare_neg_of_finrank_eq a hnpos hmax
      simpa using isSquare_algebraMap_cSeq a n hnsq ((i : ℕ) + 1) (by lia)
        (by have := i.2; lia)
  choose x hx using hroot
  have hx2 (i) : x i ^ 2 = algebraMap ℚ ↥(splittingField a n) (cSeq a ((i : ℕ) + 1) : ℚ) := by
    rw [sq]
    exact (hx i).symm
  rw [isSquare_algebraMap_iff_exists_sq_eq a hiso hindep hx2 hc]
  have hxinj : Function.Injective x := hindep.sqrt_injective hx2
  obtain ⟨cf, hcf_eq, hs_sq, hs_ne, hprodS⟩ := exists_coeffs_of_sq_eq_algebraMap hindep.1 hxinj hx2
  set s : Finset ↥(splittingField a n) := Finset.univ.image x with hs
  have hrange : (s : Set ↥(splittingField a n)) = Set.range x := by
    rw [hs, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [← hrange, square_descent hs_sq hs_ne c]
  refine ⟨fun ⟨t, hts, hsq⟩ ↦ ?_, fun ⟨S, hsq⟩ ↦ ?_⟩
  · refine ⟨Finset.univ.filter (fun i ↦ x i ∈ t), ?_⟩
    have htimg : t = (Finset.univ.filter (fun i ↦ x i ∈ t)).image x := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun hy ↦ ?_, fun ⟨i, hi, hxy⟩ ↦ hxy ▸ hi⟩
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (hs ▸ hts hy)
      exact ⟨i, hy, rfl⟩
    rwa [htimg, hprodS] at hsq
  · refine ⟨S.image x, by rw [hs]; exact Finset.image_subset_image (Finset.subset_univ S), ?_⟩
    rwa [hprodS]

lemma twoIndependent_snoc_iff {n : ℕ} {v : Fin n → ℚ} (hv : TwoIndependent v) {c : ℚ} (hc : c ≠ 0) :
    TwoIndependent (Fin.snoc v c) ↔
      ∀ S : Finset (Fin n), ¬IsSquare (c * ∏ i ∈ S, v i) := by
  obtain ⟨hv0, hvsq⟩ := hv
  have hprod_no (S : Finset (Fin n)) :
      ∏ i ∈ S.map Fin.castSuccEmb, Fin.snoc v c i = ∏ i ∈ S, v i := by
    simp [Fin.snoc_castSucc]
  have hprod_yes (S : Finset (Fin n)) :
      ∏ i ∈ insert (Fin.last n) (S.map Fin.castSuccEmb), Fin.snoc v c i
        = c * ∏ i ∈ S, v i := by
    simp [Fin.snoc_last, hprod_no S]
  have hdecomp (T : Finset (Fin (n + 1))) :
      ∃ S : Finset (Fin n),
        (Fin.last n ∉ T → T = S.map Fin.castSuccEmb) ∧
        (Fin.last n ∈ T → T = insert (Fin.last n) (S.map Fin.castSuccEmb)) := by
    refine ⟨Finset.univ.filter (fun i : Fin n ↦ i.castSucc ∈ T), ?_, ?_⟩ <;>
      · intro hlast
        ext x
        rcases Fin.eq_castSucc_or_eq_last x with ⟨j, rfl⟩ | rfl <;> simp [hlast]
  refine ⟨fun ⟨_, hsnocsq⟩ S ↦ ?_, fun hcS ↦ ⟨fun i ↦ ?_, fun T hT ↦ ?_⟩⟩
  · simpa [hprod_yes S] using
      hsnocsq (insert (Fin.last n) (S.map Fin.castSuccEmb)) (Finset.insert_nonempty _ _)
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [Fin.snoc_castSucc]
      exact hv0 j
    · rwa [Fin.snoc_last]
  · obtain ⟨S, hno, hyes⟩ := hdecomp T
    by_cases hlast : Fin.last n ∈ T
    · rw [hyes hlast, hprod_yes S]
      exact hcS S
    · rw [hno hlast, hprod_no S]
      exact hvsq S ((Finset.map_nonempty (f := Fin.castSuccEmb)).mp (hno hlast ▸ hT))

/-- Lemma 1.5: if `Ω_n ≅ [C_2]^n` and `c_1, …, c_n` are 2-independent, then a nonzero `c ∈ ℚ` is a
non-square in `K_n` iff `c_1, …, c_n, c` are 2-independent. -/
theorem kummer_extension_criterion {n : ℕ} (hiso : Nonempty (GaloisGroup a n ≃* WreathPower n))
    (hindep : TwoIndependent (fun i : Fin n ↦ (cSeq a ((i : ℕ) + 1) : ℚ))) {c : ℚ} (hc : c ≠ 0) :
    ¬IsSquare (algebraMap ℚ ↥(splittingField a n) c) ↔
      TwoIndependent (Fin.snoc (fun i : Fin n ↦ (cSeq a ((i : ℕ) + 1) : ℚ)) c) := by
  rw [twoIndependent_snoc_iff hindep hc,
    isSquare_algebraMap_iff_exists_mul_prod a hiso hindep hc, not_exists]

end

end QuadraticIterates
