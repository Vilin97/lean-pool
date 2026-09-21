/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.NormalizationSetting

/-!
# Homogeneous rational basis and conductor

This file implements blueprint node **A06′** of the algebra backend
(`docs/algebra_backend_design.md`), in the shared setting of
`Nikodym.LowerBound.Algebra.NormalizationSetting`: `Q := MvPolynomial (Fin n) K`, `J` a homogeneous
prime of `Q`, `R := Q ⧸ J`, `y : Fin s → Q` linear forms with `𝔪ₙ ^ N ≤ J ⊔ span (range y)`,
`S := MvPolynomial (Fin s) K` acting on `R` through an instance `[Algebra S R]` with
`halg : algebraMap S R = (aeval fun i ↦ mk J (y i)).toRingHom`.

## Main declarations

* `algebraMap_injective_of_halg`, `faithfulSMul_of_halg`, `noZeroSMulDivisors_of_halg`: from the
  injectivity of `aeval (mk J ∘ y)` (A02.g) to `FaithfulSMul S R` and `NoZeroSMulDivisors S R`.
* `isHomogeneousElem_algebraMap`: `algebraMap S R` sends forms of degree `e` to homogeneous
  elements of degree `e`.
* `exists_homogeneous_fraction_basis`: there are homogeneous elements `r : Fin Δ → R`, linearly
  independent over `S`, whose images form a basis of `FractionRing R` over `FractionRing S`.
* `exists_conductor`, `exists_conductor_of_pow_idealOfVars_le`: for such a basis there is `c ≠ 0`
  in `S` with `c • R ⊆ span S (range r)`.
* `finrank_fractionRing_eq_of_basis`, `pos_of_basis_fractionRing`: `Δ = finrank` and `0 < Δ`.
* `mk_homogeneousComponent_mem_span`, `exists_homogeneous_conductor` (optional, for A07′/A08):
  `span S (range r)` is graded when the `r i` are homogeneous, so the conductor can be chosen
  homogeneous.

The fraction-field part is proved first for an arbitrary pair of domains `S → R` with
`[FaithfulSMul S R]` and `[Module.Finite S R]` (`span_image_algebraMap_fractionRing_eq_top`,
`exists_basis_fractionRing_of_span_eq_top`, `exists_conductor`), and then specialised.

## Conventions

* `FractionRing R` is an algebra over `FractionRing S` through `FractionRing.liftAlgebra`, which
  Mathlib deliberately does not make a global instance. We activate it with
  `attribute [local instance] FractionRing.liftAlgebra`; all statements below mentioning
  `Module (FractionRing S) (FractionRing R)` refer to this instance, so a consumer must install it
  the same way (or with `letI := FractionRing.liftAlgebra S (FractionRing R)`, which is the same
  term). `liftAlgebra` needs `[FaithfulSMul S R]`, which is therefore an instance argument of the
  theorems in the shared setting (it is provided by `faithfulSMul_of_halg` from A02.g).
* As in `LinearNormalization.lean`, synthesizing `Module (MvPolynomial (Fin s) K) (Q ⧸ J)` from
  an `[Algebra _ _]` argument first explores `Submodule.Quotient.module'` and is expensive; the
  declarations in the shared setting that need it use `set_option synthInstance.maxHeartbeats
  80000 in` (`200000` for the two that also synthesize the fraction-field instances). Note that
  `lake build` (with the `maxSynthPendingDepth` option of the lakefile) needs more heartbeats than
  a bare `lake env lean`.
-/

namespace Nikodym.LowerBound

open MvPolynomial

/-! ### Fraction fields of a finite extension of domains -/

section FractionRing

variable {S R : Type*} [CommRing S] [IsDomain S] [CommRing R] [IsDomain R] [Algebra S R]
  [FaithfulSMul S R]

attribute [local instance] FractionRing.liftAlgebra

/-- Blueprint A06′: **a finite spanning set of `R` over `S` spans `Frac R` over `Frac S`.** The
`Frac S`-span `V` of the image of `T` contains the image of `R`, is closed under multiplication,
hence is a finite-dimensional subalgebra of the field `Frac R`, hence a field, hence contains the
inverses of the images of nonzero elements of `R`, hence everything. -/
theorem span_image_algebraMap_fractionRing_eq_top {T : Set R} (hT : T.Finite)
    (hspan : Submodule.span S T = ⊤) :
    Submodule.span (FractionRing S) (algebraMap R (FractionRing R) '' T) = ⊤ := by
  set f : R →ₐ[S] FractionRing R := IsScalarTower.toAlgHom S R (FractionRing R) with hf
  set V := Submodule.span (FractionRing S) (algebraMap R (FractionRing R) '' T) with hV
  -- the image of `R` lies in `V`
  have hR : ∀ x : R, algebraMap R (FractionRing R) x ∈ V := by
    intro x
    have hx : x ∈ Submodule.span S T := hspan ▸ Submodule.mem_top
    have h1 : f.toLinearMap x ∈ (Submodule.span S T).map f.toLinearMap :=
      Submodule.mem_map_of_mem hx
    rw [Submodule.map_span] at h1
    have h2 := Submodule.span_le_restrictScalars S (FractionRing S) (⇑f.toLinearMap '' T) h1
    rw [Submodule.restrictScalars_mem] at h2
    have himg : ⇑f.toLinearMap '' T = algebraMap R (FractionRing R) '' T := by
      congr 1
    rw [himg] at h2
    exact h2
  have h1 : (1 : FractionRing R) ∈ V := by simpa using hR 1
  have hmul : ∀ a b : FractionRing R, a ∈ V → b ∈ V → a * b ∈ V := by
    intro a b ha hb
    have hVV : V * V ≤ V := by
      rw [hV, Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨_, ⟨u, -, rfl⟩, _, ⟨w, -, rfl⟩, rfl⟩
      change algebraMap R (FractionRing R) u * algebraMap R (FractionRing R) w ∈ V
      rw [← map_mul]
      exact hR _
    exact hVV (Submodule.mul_mem_mul ha hb)
  -- `V` as a subalgebra: finite-dimensional, a domain, hence a field
  set A : Subalgebra (FractionRing S) (FractionRing R) := V.toSubalgebra h1 hmul with hA
  haveI : Module.Finite (FractionRing S) A := by
    have : Module.Finite (FractionRing S) V :=
      Module.Finite.span_of_finite (FractionRing S) (hT.image _)
    refine Subalgebra.finiteDimensional_toSubmodule.mp ?_
    rw [hA, Submodule.toSubalgebra_toSubmodule]
    exact this
  haveI : Algebra.IsIntegral (FractionRing S) A := Algebra.IsIntegral.of_finite _ _
  have hinjA : Function.Injective (algebraMap (FractionRing S) A) := by
    intro a b hab
    have := congrArg Subtype.val hab
    rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap] at this
    exact (algebraMap (FractionRing S) (FractionRing R)).injective this
  have hfield : IsField A :=
    (Algebra.IsIntegral.isField_iff_isField hinjA).mp (Field.toIsField (FractionRing S))
  -- inverses of nonzero elements of `R` lie in `V`
  have hinv : ∀ x : R, x ≠ 0 → (algebraMap R (FractionRing R) x)⁻¹ ∈ V := by
    intro x hx
    have hxA : (⟨algebraMap R (FractionRing R) x, hR x⟩ : A) ≠ 0 := by
      intro h
      apply hx
      have h' := congrArg Subtype.val h
      exact (map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mp h'
    obtain ⟨w, hw⟩ := hfield.mul_inv_cancel hxA
    have hw' : algebraMap R (FractionRing R) x * (w : FractionRing R) = 1 := congrArg Subtype.val hw
    rw [← eq_inv_of_mul_eq_one_right hw']
    exact w.2
  rw [eq_top_iff]
  rintro z -
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R z
  rw [div_eq_mul_inv]
  exact hmul _ _ (hR a) (hinv b (nonZeroDivisors.ne_zero hb))

/-- Blueprint A06′: **extracting a rational basis from a finite spanning family.** If `v : ι → R`
spans `R` over `S` (with `ι` finite), some subfamily `v ∘ a`, `a : Fin Δ → ι`, is `S`-linearly
independent and its image is a basis of `Frac R` over `Frac S`. -/
theorem exists_basis_fractionRing_of_span_eq_top {ι : Type*} [Finite ι] {v : ι → R}
    (hspan : Submodule.span S (Set.range v) = ⊤) :
    ∃ (Δ : ℕ) (a : Fin Δ → ι), LinearIndependent S (v ∘ a) ∧
      ∃ b : Module.Basis (Fin Δ) (FractionRing S) (FractionRing R),
        ∀ i, b i = algebraMap R (FractionRing R) (v (a i)) := by
  set f : R →ₐ[S] FractionRing R := IsScalarTower.toAlgHom S R (FractionRing R) with hf
  have htop : Submodule.span (FractionRing S) (Set.range (⇑f ∘ v)) = ⊤ := by
    rw [Set.range_comp]
    exact span_image_algebraMap_fractionRing_eq_top (Set.finite_range v) hspan
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' (FractionRing S) (⇑f ∘ v)
  cases nonempty_fintype ι
  haveI : Fintype κ := Fintype.ofInjective a ha
  set e := Fintype.equivFin κ with he
  have hli' : LinearIndependent (FractionRing S) ((⇑f ∘ v) ∘ a ∘ e.symm) := by
    rw [← Function.comp_assoc]
    exact hli.comp e.symm e.symm.injective
  refine ⟨Fintype.card κ, a ∘ e.symm, ?_, ?_⟩
  · have hS : LinearIndependent S (⇑f.toLinearMap ∘ (v ∘ a ∘ e.symm)) :=
      hli'.restrict_scalars' S
    exact LinearIndependent.of_comp f.toLinearMap hS
  · have hsp' : ⊤ ≤ Submodule.span (FractionRing S) (Set.range ((⇑f ∘ v) ∘ a ∘ e.symm)) := by
      rw [← Function.comp_assoc, e.symm.surjective.range_comp, hsp, htop]
    refine ⟨Module.Basis.mk hli' hsp', fun i ↦ ?_⟩
    rw [Module.Basis.mk_apply]
    rfl

/-- Blueprint A06′: **the size of a rational basis is the generic rank.** -/
theorem finrank_fractionRing_eq_of_basis {Δ : ℕ}
    (b : Module.Basis (Fin Δ) (FractionRing S) (FractionRing R)) :
    Module.finrank (FractionRing S) (FractionRing R) = Δ := by
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

omit [IsDomain S] in
/-- Blueprint A06′: **a rational basis is nonempty.** -/
theorem pos_of_basis_fractionRing {Δ : ℕ}
    (b : Module.Basis (Fin Δ) (FractionRing S) (FractionRing R)) : 0 < Δ :=
  (b.index_nonempty.some).pos

/-- Blueprint A06′: **the conductor.** If `R` is module-finite over `S` and the images of
`r : Fin Δ → R` form a basis of `Frac R` over `Frac S`, there is `c ≠ 0` in `S` with
`c • x ∈ span S (range r)` for every `x : R`: write each of finitely many `S`-generators of `R` as a
`Frac S`-combination of the `r i` and clear the denominators. -/
theorem exists_conductor [Module.Finite S R] {Δ : ℕ} {r : Fin Δ → R}
    (hb : ∃ b : Module.Basis (Fin Δ) (FractionRing S) (FractionRing R),
      ∀ i, b i = algebraMap R (FractionRing R) (r i)) :
    ∃ c : S, c ≠ 0 ∧ ∀ x : R, c • x ∈ Submodule.span S (Set.range r) := by
  classical
  obtain ⟨b, hb⟩ := hb
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := S) (M := R)
  set f : R →ₐ[S] FractionRing R := IsScalarTower.toAlgHom S R (FractionRing R) with hf
  set M := Submodule.span S (Set.range r) with hM
  -- the coefficients of the generators
  set c : T × Fin Δ → FractionRing S := fun p ↦ b.repr (f p.1) p.2 with hc
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors S) Finset.univ c
  refine ⟨d, nonZeroDivisors.coe_ne_zero d, ?_⟩
  have key : ∀ t ∈ T, (d : S) • t ∈ M := by
    intro t ht
    choose a ha using fun i ↦ hd (⟨t, ht⟩, i) (Finset.mem_univ _)
    have heq : (d : S) • t = ∑ i, a i • r i := by
      apply IsFractionRing.injective R (FractionRing R)
      have hft : f t = ∑ i, c (⟨t, ht⟩, i) • b i := (b.sum_repr (f t)).symm
      calc algebraMap R (FractionRing R) ((d : S) • t) = f ((d : S) • t) := rfl
        _ = (d : S) • f t := map_smul f _ _
        _ = ∑ i, ((d : S) • c (⟨t, ht⟩, i)) • b i := by
          rw [hft, Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ ↦ (smul_assoc (d : S) _ _).symm
        _ = ∑ i, a i • f (r i) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [← ha i, algebraMap_smul, hb i]
          rfl
        _ = algebraMap R (FractionRing R) (∑ i, a i • r i) := by
          change _ = f (∑ i, a i • r i)
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ ↦ (map_smul f _ _).symm
    rw [heq]
    exact Submodule.sum_mem _ fun i _ ↦ M.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  intro x
  have hx : x ∈ Submodule.span S (T : Set R) := hT ▸ Submodule.mem_top
  have hle : Submodule.span S (T : Set R) ≤ M.comap (LinearMap.lsmul S R d) :=
    Submodule.span_le.mpr fun t ht ↦ key t ht
  exact hle hx

end FractionRing

/-! ### The shared setting -/

section Setting

variable {K : Type*} [Field K] {n s : ℕ} {J : Ideal (MvPolynomial (Fin n) K)}
  {y : Fin s → MvPolynomial (Fin n) K}

attribute [local instance] FractionRing.liftAlgebra MvPolynomial.gradedAlgebra

/-- Blueprint A06′: in the shared setting, `algebraMap S R` is injective. -/
theorem algebraMap_injective_of_halg
    [Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)]
    (halg : algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) =
      (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).toRingHom)
    (hinj : Function.Injective (MvPolynomial.aeval (fun i ↦ Ideal.Quotient.mk J (y i)) :
      MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin n) K ⧸ J)) :
    Function.Injective (algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)) := by
  rw [halg]
  exact hinj

/-- Blueprint A06′: in the shared setting, `S` acts faithfully on `R`. -/
theorem faithfulSMul_of_halg
    [Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)]
    (halg : algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) =
      (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).toRingHom)
    (hinj : Function.Injective (MvPolynomial.aeval (fun i ↦ Ideal.Quotient.mk J (y i)) :
      MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin n) K ⧸ J)) :
    FaithfulSMul (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap_injective_of_halg halg hinj)

/-- Blueprint A06′: in the shared setting (`J` prime), `R` has no `S`-torsion. -/
theorem noZeroSMulDivisors_of_halg [J.IsPrime]
    [Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)]
    (halg : algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) =
      (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).toRingHom)
    (hinj : Function.Injective (MvPolynomial.aeval (fun i ↦ Ideal.Quotient.mk J (y i)) :
      MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin n) K ⧸ J)) :
    NoZeroSMulDivisors (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) where
  eq_zero_or_eq_zero_of_smul_eq_zero {c x} h := by
    rw [Algebra.smul_def] at h
    refine (mul_eq_zero.mp h).imp (fun hc ↦ ?_) id
    exact (map_eq_zero_iff _ (algebraMap_injective_of_halg halg hinj)).mp hc

/-- Blueprint A06′: in the shared setting, `algebraMap S R p` is the class of `aeval y p`. -/
theorem algebraMap_eq_mk_aeval
    [Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)]
    (halg : algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) =
      (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).toRingHom)
    (p : MvPolynomial (Fin s) K) :
    algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) p =
      Ideal.Quotient.mk J (MvPolynomial.aeval y p) := by
  rw [halg, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← Ideal.Quotient.mkₐ_eq_mk K,
    ← AlgHom.comp_apply, MvPolynomial.comp_aeval]

/-- Blueprint A06′: in the shared setting, **`algebraMap S R` sends a form of degree `e` to a
homogeneous element of degree `e`**, since the `y i` are linear forms. -/
theorem isHomogeneousElem_algebraMap (hy : ∀ i, (y i).IsHomogeneous 1)
    [Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)]
    (halg : algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) =
      (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).toRingHom)
    {p : MvPolynomial (Fin s) K} {e : ℕ} (hp : p.IsHomogeneous e) :
    IsHomogeneousElem J (algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) p) e :=
  ⟨MvPolynomial.aeval y p, by simpa using hp.aeval y hy, (algebraMap_eq_mk_aeval halg p).symm⟩

-- synthesizing `Module (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)` from the `Algebra`
-- instance first explores `Submodule.Quotient.module'` and needs about `40000` heartbeats; the
-- fraction-field instances (`FaithfulSMul S (FractionRing R)`, `IsScalarTower`, `liftAlgebra`)
-- run this search several times
/-- Blueprint A06′: **homogeneous rational basis.** In the shared setting (`J` a homogeneous prime,
`𝔪ₙ ^ N ≤ J ⊔ (y)`, `S` acting faithfully on `R := Q ⧸ J` through `y`), there are homogeneous
elements `r : Fin Δ → R` of degrees `e`, linearly independent over `S`, whose images in
`FractionRing R` form a basis over `FractionRing S` (algebra structure `FractionRing.liftAlgebra`).
`Δ` is the generic rank (`finrank_fractionRing_eq_of_basis`) and `0 < Δ`
(`pos_of_basis_fractionRing`). -/
theorem exists_homogeneous_fraction_basis [J.IsPrime]
    (hJh : J.IsHomogeneous (homogeneousSubmodule (Fin n) K)) {N : ℕ}
    (hy : ∀ i, (y i).IsHomogeneous 1)
    (hN : idealOfVars (Fin n) K ^ N ≤ J ⊔ Ideal.span (Set.range y))
    [Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)]
    [FaithfulSMul (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)]
    (halg : algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) =
      (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).toRingHom) :
    ∃ (Δ : ℕ) (r : Fin Δ → MvPolynomial (Fin n) K ⧸ J) (e : Fin Δ → ℕ),
      (∀ i, IsHomogeneousElem J (r i) (e i)) ∧
      LinearIndependent (MvPolynomial (Fin s) K) r ∧
      ∃ b : Module.Basis (Fin Δ) (FractionRing (MvPolynomial (Fin s) K))
          (FractionRing (MvPolynomial (Fin n) K ⧸ J)),
        ∀ i, b i = algebraMap (MvPolynomial (Fin n) K ⧸ J) _ (r i) := by
  obtain ⟨gens, hgens, hspan⟩ := span_image_mk_eq_top_of_pow_idealOfVars_le hJh hy hN halg
  choose u hu using hgens
  set v : gens → MvPolynomial (Fin n) K ⧸ J := fun g ↦ Ideal.Quotient.mk J g.1 with hv
  have hspan' : Submodule.span (MvPolynomial (Fin s) K) (Set.range v) = ⊤ := by
    rw [← hspan, Set.image_eq_range]
    rfl
  obtain ⟨Δ, a, hli, b, hb⟩ := exists_basis_fractionRing_of_span_eq_top hspan'
  exact ⟨Δ, v ∘ a, fun i ↦ u (a i).1 (a i).2, fun i ↦ isHomogeneousElem_mk J (hu _ _).2, hli,
    b, hb⟩

-- synthesizing `Module (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)` from the `Algebra`
-- instance first explores `Submodule.Quotient.module'` and needs about `40000` heartbeats; the
-- fraction-field instances (`FaithfulSMul S (FractionRing R)`, `IsScalarTower`, `liftAlgebra`)
-- run this search several times
/-- Blueprint A06′: **the conductor, in the shared setting.** `Module.Finite S R` comes from
A02.h (`finite_of_pow_idealOfVars_le'`); see `exists_conductor` for the general statement. -/
theorem exists_conductor_of_pow_idealOfVars_le [J.IsPrime]
    (hJh : J.IsHomogeneous (homogeneousSubmodule (Fin n) K)) {N : ℕ}
    (hy : ∀ i, (y i).IsHomogeneous 1)
    (hN : idealOfVars (Fin n) K ^ N ≤ J ⊔ Ideal.span (Set.range y))
    [Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)]
    [FaithfulSMul (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)]
    (halg : algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) =
      (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).toRingHom)
    {Δ : ℕ} {r : Fin Δ → MvPolynomial (Fin n) K ⧸ J}
    (hb : ∃ b : Module.Basis (Fin Δ) (FractionRing (MvPolynomial (Fin s) K))
        (FractionRing (MvPolynomial (Fin n) K ⧸ J)),
      ∀ i, b i = algebraMap (MvPolynomial (Fin n) K ⧸ J) _ (r i)) :
    ∃ c : MvPolynomial (Fin s) K, c ≠ 0 ∧ ∀ x : MvPolynomial (Fin n) K ⧸ J,
      c • x ∈ Submodule.span (MvPolynomial (Fin s) K) (Set.range r) := by
  haveI := finite_of_pow_idealOfVars_le' hJh hy hN halg
  exact exists_conductor hb

/-! ### Optional: a homogeneous conductor

The `S`-submodule `M := span S (range r)` generated by homogeneous elements is graded: the class
of every homogeneous component of a representative of an element of `M` lies in `M`
(`mk_homogeneousComponent_mem_span`). Consequently the annihilator of `R ⧸ M` is a homogeneous
ideal of `S`, and a nonzero conductor can be replaced by one of its nonzero homogeneous
components (`exists_homogeneous_conductor`). This is not needed by the main results of this node;
it is provided for A07′/A08. -/

-- synthesizing `Module (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)` from the `Algebra`
-- instance first explores `Submodule.Quotient.module'` and needs about `40000` heartbeats
/-- Blueprint A06′ (optional): **the span of homogeneous elements is graded.** If the `r i` are
homogeneous and `mk J G ∈ span S (range r)`, then so is the class of every homogeneous component
of `G`. -/
theorem mk_homogeneousComponent_mem_span
    (hJh : J.IsHomogeneous (homogeneousSubmodule (Fin n) K)) (hy : ∀ i, (y i).IsHomogeneous 1)
    [Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)]
    (halg : algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) =
      (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).toRingHom)
    {Δ : ℕ} {r : Fin Δ → MvPolynomial (Fin n) K ⧸ J} {e : Fin Δ → ℕ}
    (hr : ∀ i, IsHomogeneousElem J (r i) (e i)) {G : MvPolynomial (Fin n) K}
    (hG : Ideal.Quotient.mk J G ∈ Submodule.span (MvPolynomial (Fin s) K) (Set.range r)) (t : ℕ) :
    Ideal.Quotient.mk J (homogeneousComponent t G) ∈
      Submodule.span (MvPolynomial (Fin s) K) (Set.range r) := by
  classical
  set M := Submodule.span (MvPolynomial (Fin s) K) (Set.range r) with hM
  choose Rr hRr hRr' using hr
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (MvPolynomial (Fin s) K)).mp hG
  -- a representative of `mk J G` adapted to the grading
  set H : MvPolynomial (Fin n) K := ∑ i, ∑ δ ∈ Finset.range ((a i).totalDegree + 1),
    MvPolynomial.aeval y (homogeneousComponent δ (a i)) * Rr i with hH
  have hGH : Ideal.Quotient.mk J G = Ideal.Quotient.mk J H := by
    rw [← ha, hH, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, algebraMap_eq_mk_aeval halg, ← hRr' i, ← map_mul, ← Finset.sum_mul,
      ← map_sum, sum_homogeneousComponent]
  have hmem : Ideal.Quotient.mk J (homogeneousComponent t G) =
      Ideal.Quotient.mk J (homogeneousComponent t H) := by
    rw [Ideal.Quotient.eq] at hGH ⊢
    rw [← map_sub]
    exact homogeneousComponent_mem_of_mem hJh hGH t
  rw [hmem, hH, map_sum, map_sum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [map_sum, map_sum]
  refine Submodule.sum_mem _ fun δ _ ↦ ?_
  have hhom : MvPolynomial.aeval y (homogeneousComponent δ (a i)) * Rr i ∈
      homogeneousSubmodule (Fin n) K (1 * δ + e i) :=
    ((homogeneousComponent_isHomogeneous δ (a i)).aeval y hy).mul (hRr i)
  rw [homogeneousComponent_of_mem hhom]
  split_ifs
  · rw [map_mul, hRr' i, ← algebraMap_eq_mk_aeval halg, ← Algebra.smul_def]
    exact M.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [map_zero]
    exact M.zero_mem

-- synthesizing `Module (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)` from the `Algebra`
-- instance first explores `Submodule.Quotient.module'` and needs about `40000` heartbeats
/-- Blueprint A06′ (optional): **a homogeneous conductor.** If the `r i` are homogeneous and
`c ≠ 0` satisfies `c • R ⊆ span S (range r)`, then some nonzero homogeneous component of `c`
does as well. -/
theorem exists_homogeneous_conductor
    (hJh : J.IsHomogeneous (homogeneousSubmodule (Fin n) K)) (hy : ∀ i, (y i).IsHomogeneous 1)
    [Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)]
    (halg : algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) =
      (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).toRingHom)
    {Δ : ℕ} {r : Fin Δ → MvPolynomial (Fin n) K ⧸ J} {e : Fin Δ → ℕ}
    (hr : ∀ i, IsHomogeneousElem J (r i) (e i)) {c : MvPolynomial (Fin s) K} (hc : c ≠ 0)
    (hcond : ∀ x : MvPolynomial (Fin n) K ⧸ J,
      c • x ∈ Submodule.span (MvPolynomial (Fin s) K) (Set.range r)) :
    ∃ (c' : MvPolynomial (Fin s) K) (γ : ℕ), c' ≠ 0 ∧ c'.IsHomogeneous γ ∧
      ∀ x : MvPolynomial (Fin n) K ⧸ J,
        c' • x ∈ Submodule.span (MvPolynomial (Fin s) K) (Set.range r) := by
  classical
  set M := Submodule.span (MvPolynomial (Fin s) K) (Set.range r) with hM
  -- a nonzero homogeneous component of `c`
  obtain ⟨γ, hγ⟩ : ∃ γ, homogeneousComponent γ c ≠ 0 := by
    by_contra h
    apply hc
    rw [← sum_homogeneousComponent c]
    exact Finset.sum_eq_zero fun γ _ ↦ by_contra fun h' ↦ h ⟨γ, h'⟩
  have hγle : γ ∈ Finset.range (c.totalDegree + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff]
    by_contra h
    exact hγ (homogeneousComponent_eq_zero _ _ (not_le.mp h))
  refine ⟨homogeneousComponent γ c, γ, hγ, homogeneousComponent_isHomogeneous γ c, fun x ↦ ?_⟩
  obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective x
  -- reduce to homogeneous `x = mk J F` of degree `t`, via the submodule `{x | c' • x ∈ M}`
  suffices key : ∀ t, Ideal.Quotient.mk J (homogeneousComponent t G) ∈
      M.comap (LinearMap.lsmul (MvPolynomial (Fin s) K) _ (homogeneousComponent γ c)) by
    have := Submodule.sum_mem _ fun t (_ : t ∈ Finset.range (G.totalDegree + 1)) ↦ key t
    rw [← map_sum, sum_homogeneousComponent] at this
    exact this
  intro t
  rw [Submodule.mem_comap, LinearMap.lsmul_apply]
  set F := homogeneousComponent t G with hF
  have hFt : F.IsHomogeneous t := homogeneousComponent_isHomogeneous t G
  have h1 : Ideal.Quotient.mk J (MvPolynomial.aeval y c * F) ∈ M := by
    rw [map_mul, ← algebraMap_eq_mk_aeval halg, ← Algebra.smul_def]
    exact hcond _
  have h2 := mk_homogeneousComponent_mem_span hJh hy halg hr h1 (γ + t)
  have h3 : homogeneousComponent (γ + t) (MvPolynomial.aeval y c * F) =
      MvPolynomial.aeval y (homogeneousComponent γ c) * F := by
    conv_lhs => rw [← sum_homogeneousComponent c, map_sum, Finset.sum_mul, map_sum]
    rw [Finset.sum_eq_single γ]
    · have hhom : MvPolynomial.aeval y (homogeneousComponent γ c) * F ∈
          homogeneousSubmodule (Fin n) K (1 * γ + t) :=
        ((homogeneousComponent_isHomogeneous γ c).aeval y hy).mul hFt
      rw [homogeneousComponent_of_mem hhom, if_pos (by omega)]
    · intro δ _ hδ
      have hhom : MvPolynomial.aeval y (homogeneousComponent δ c) * F ∈
          homogeneousSubmodule (Fin n) K (1 * δ + t) :=
        ((homogeneousComponent_isHomogeneous δ c).aeval y hy).mul hFt
      rw [homogeneousComponent_of_mem hhom, if_neg (by omega)]
    · intro h
      exact absurd hγle h
  rw [h3, map_mul, ← algebraMap_eq_mk_aeval halg, ← Algebra.smul_def] at h2
  exact h2

end Setting

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
