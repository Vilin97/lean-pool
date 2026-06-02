/-
Copyright (c) 2026 Anne Baanen et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.Algebra.GroupWithZero.Defs

open Module BigOperators Polynomial

/-! # Auxiliary algebra lemmas.

This file contains some auxiliary lemmas mainly about subalgebras and adjoining a root.

## Note
A similar version of some of these results can be found already in Mathlib, but here we avoid
some assumptions, like that of some spaces being fields or integrally closed. -/

lemma IsAdjoinRoot.minpoly_root {Q K : Type*} [Field Q] [CommRing K] [Algebra Q K]
    {f : Q[X]} (A : IsAdjoinRoot K f) (hf : f ≠ 0) :
    minpoly Q (A.root) = f * Polynomial.C (Polynomial.leadingCoeff f)⁻¹ := by
  let φ := A.algEquiv (AdjoinRoot.isAdjoinRoot f)
  rw [← minpoly.algEquiv_eq φ (root A), IsAdjoinRoot.algEquiv_root A (AdjoinRoot.isAdjoinRoot f)]
  exact AdjoinRoot.minpoly_root hf

/-- Similar to Polynomial.Monic.dvd_iff_fraction_map_dvd_fraction_map but does assume
  that `p` is monic· -/
lemma Polynomial.Monic_dvd_iff_fraction_map_dvd_fraction_map' {R K : Type*} [CommRing R]
    [Nontrivial R] [Field K] [Algebra R K] [IsFractionRing R K] {p q : R[X]}
    (hq : Monic q) : map (algebraMap R K) q ∣ map (algebraMap R K) p ↔ q ∣ p := by
  refine ⟨?_, fun a => map_dvd (algebraMap R K) a⟩
  intro hdvd
  obtain ⟨ k, hk ⟩ := hdvd
  rw [← Polynomial.modByMonic_add_div p q] at hk
  simp only [ Polynomial.map_add, Polynomial.map_mul] at hk
  have hdvd : (map (algebraMap R K) q) ∣ map (algebraMap R K) (p %ₘ q) := by
    use (k - map (algebraMap R K) (p /ₘ q))
    rw [mul_sub, ← hk]
    ring
  have : p %ₘ q = 0 := by
    by_contra h
    have hdeg1 : (map (algebraMap R K) (p  %ₘ q)).degree = (p %ₘ q).degree :=
      Polynomial.degree_map_eq_of_injective (IsFractionRing.injective R K) (p %ₘ q)
    have hdeg2 : (map (algebraMap R K) q).degree = q.degree :=
      Polynomial.degree_map_eq_of_injective (IsFractionRing.injective R K) q
    have hdle := Polynomial.degree_le_of_dvd hdvd ((Polynomial.map_ne_zero_iff
      (IsFractionRing.injective R K)).2 h)
    rw [hdeg1, hdeg2] at hdle
    exact (lt_self_iff_false _).1 (lt_of_le_of_lt hdle (Polynomial.degree_modByMonic_lt p hq))
  rw [Polynomial.modByMonic_eq_zero_iff_dvd hq, ← AdjoinRoot.mk_eq_zero] at this
  exact AdjoinRoot.mk_eq_zero.mp this

-- We don't use minpoly.isIntegrallyClosed_eq_field_fractions because we don't assume K is a domain·
lemma Algebra.minpoly_fraction_field {R Q K : Type*} [CommRing R] [IsDomain R] [Field Q]
    [Algebra R Q] [IsFractionRing R Q] [CommRing K]
    [Algebra R K] [Algebra Q K] [IsScalarTower R Q K] (T : Polynomial R)
    (hm : Monic T) (x : K) (hmin : minpoly Q x = map (algebraMap R Q) T) :
    minpoly R x = T := by
  have hcomp : (algebraMap Q K).comp (algebraMap R Q) = (algebraMap R K) :=
    (IsScalarTower.algebraMap_eq R Q K).symm
  have hint : IsIntegral R x := by
    use T
    constructor
    · exact hm
    · rw [← hcomp, ← Polynomial.eval₂_map, ← hmin, ← Polynomial.aeval_def, minpoly.aeval]
  have heval: (Polynomial.aeval x) T = 0 := by
    rw [Polynomial.aeval_def, ← hcomp, ← Polynomial.eval₂_map, ← hmin, ← Polynomial.aeval_def,
      minpoly.aeval]
  have hdvd : T ∣ (minpoly R x) := by
    rw [← Polynomial.Monic_dvd_iff_fraction_map_dvd_fraction_map' (K := Q) hm, ← hmin]
    refine minpoly.dvd Q x ?_
    simp only [aeval_map_algebraMap, minpoly.aeval]
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le hm (minpoly.monic hint) hdvd ?_
  exact Polynomial.natDegree_le_natDegree (minpoly.min R x hm heval)

-- We don't use minpoly.equivAdjoin because we don't assume that `K` is a domain·
/-- Imported declaration. -/
noncomputable def Algebra.adjoinIsAdjoinRoot {R Q K : Type*} [CommRing R] [IsDomain R] [Field Q]
    [Algebra R Q] [IsFractionRing R Q] [CommRing K]
    [Algebra R K] [Algebra Q K] [IsScalarTower R Q K] (T : Polynomial R)
    (hm : Monic T) (x : K) (hmin : minpoly Q x = map (algebraMap R Q) T) :
    IsAdjoinRoot (Algebra.adjoin R {x}) T := by
    have hmin2 : minpoly R x = T := Algebra.minpoly_fraction_field T hm x hmin
    refine (AdjoinRoot.isAdjoinRoot T).ofAlgEquiv ?_
    let e : AdjoinRoot T ≃ₐ[R] AdjoinRoot (minpoly R x) := by
      refine Ideal.quotientEquivAlgOfEq R (show Ideal.span {T} =
        Ideal.span {(minpoly R x)} by rw [hmin2])
    refine AlgEquiv.trans (A₂ := AdjoinRoot (minpoly R x)) e ?_
    refine AlgEquiv.ofBijective (AdjoinRoot.Minpoly.toAdjoin R x) ⟨?_,
      AdjoinRoot.Minpoly.toAdjoin.surjective R x⟩
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    rintro a ha
    obtain ⟨P, hP⟩ := AdjoinRoot.mk_surjective a
    rw [← hP, AdjoinRoot.Minpoly.coe_toAdjoin] at ha
    simp only [AdjoinRoot.liftAlgHom_mk] at ha
    have : aeval x ((map (algebraMap R Q)) P) = 0 := by
      have hR : eval₂ (algebraMap R K) x P = 0 := by
        have hcoerced :
            (↑((aeval (⟨x, Algebra.self_mem_adjoin_singleton R x⟩ :
              Algebra.adjoin R ({x} : Set K))) P) : K) = 0 := by
          simpa [aeval_def] using
            congrArg (fun y : Algebra.adjoin R ({x} : Set K) => (y : K)) ha
        change (aeval x) P = 0
        rw [← Polynomial.aeval_subalgebra_coe P (Algebra.adjoin R ({x} : Set K))
          (⟨x, Algebra.self_mem_adjoin_singleton R x⟩ : Algebra.adjoin R ({x} : Set K))]
        exact hcoerced
      have hcomp : (algebraMap Q K).comp (algebraMap R Q) = algebraMap R K := by
        ext r
        exact (IsScalarTower.algebraMap_apply R Q K r).symm
      simpa [aeval_def, Polynomial.eval₂_map, hcomp] using hR
    have := minpoly.dvd Q x this
    rw [hmin, Polynomial.Monic_dvd_iff_fraction_map_dvd_fraction_map' hm, ← AdjoinRoot.mk_eq_zero,
      ← hmin2 ] at this
    rw [this] at hP
    exact hP.symm

lemma Algebra.adjoinIsAdjoinRoot_root {R Q K : Type*} [CommRing R] [IsDomain R] [Field Q]
    [Algebra R Q] [IsFractionRing R Q] [CommRing K]
    [Algebra R K] [Algebra Q K] [IsScalarTower R Q K] (T : Polynomial R)
    (hm : Monic T) (x : K) (hmin : minpoly Q x = map (algebraMap R Q) T) :
    (Algebra.adjoinIsAdjoinRoot T hm x hmin).root = x := by
  unfold Algebra.adjoinIsAdjoinRoot
  erw [IsAdjoinRoot.ofAlgEquiv_root, Equiv.trans_apply, AdjoinRoot.isAdjoinRoot_root_eq_root]
  unfold AdjoinRoot.root; unfold AdjoinRoot.mk
  erw [Ideal.quotientEquivAlgOfEq_mk R _  (X : R[X]), AdjoinRoot.mk_X,
    AdjoinRoot.Minpoly.coe_toAdjoin_mk_X]
  rw [Algebra.minpoly_fraction_field T hm x hmin]

/-- Imported declaration. -/
noncomputable def Algebra.adjoinIsAdjoinRootOfIsAdjoinRoot [CommRing R] [IsDomain R] [Field Q]
    [Algebra R Q] [IsFractionRing R Q] [CommRing K] [Algebra R K] [Algebra Q K]
    [IsScalarTower R Q K]
    (T : Polynomial R) (hm : Monic T)
    (k : IsAdjoinRoot K (T.map (algebraMap R Q))) : IsAdjoinRoot (Algebra.adjoin R {k.root}) T := by
  refine Algebra.adjoinIsAdjoinRoot (Q := Q) T hm k.root ?_
  rw [IsAdjoinRoot.minpoly_root k (Monic.ne_zero (Monic.map (algebraMap R Q) hm)),
    Monic.map _ hm, inv_one, map_one, mul_one]

/-- Imported declaration. -/
noncomputable def Algebra.adjoinRootEquivOfRootMem [CommRing R] [IsDomain R] [Field Q] [Algebra R Q]
    [IsFractionRing R Q] [CommRing K] [Algebra R K] [Algebra Q K] [IsScalarTower R Q K]
    (O : Type*) [CommRing O] [Algebra R O] (T : Polynomial R) (hm : Monic T)
    (f : IsAdjoinRoot O T) (k : IsAdjoinRoot K (T.map (algebraMap R Q))) :
    O ≃ₐ[R] (Algebra.adjoin R {k.root}) := by
  refine f.algEquiv (Algebra.adjoinIsAdjoinRoot (Q := Q) T hm k.root ?_)
  rw [IsAdjoinRoot.minpoly_root k (Monic.ne_zero (Monic.map (algebraMap R Q) hm)),
    Monic.map _ hm, inv_one, map_one, mul_one]

lemma surj_fraction_ring_of_eq_rank [NeZero n] [CommRing R] [IsDomain R] [Field Q] [Algebra R Q]
    [IsFractionRing R Q] [CommRing K] [Algebra R K] [Algebra Q K] [IsScalarTower R Q K]
    [FiniteDimensional Q K] (hd : Module.finrank Q K = n) (O : Subalgebra R K)
    (b : Basis (Fin n) R O) (x : K) : ∃ (d : R) (y : O), d • x = y ∧ d ∈ nonZeroDivisors R := by
  have : Submodule.span Q (Set.range (O.val ∘ b)) = ⊤ := by
    refine LinearIndependent.span_eq_top_of_card_eq_finrank ?_ ?_
    · rw [← LinearIndependent.iff_fractionRing (R := R)]
      refine LinearIndependent.map' b.linearIndependent (SMulMemClass.subtype O) ?_
      · refine LinearMap.ker_eq_bot_of_injective ?_
        simp only [SMulMemClass.coe_subtype]
        exact Subtype.val_injective
    · rw [hd, Fintype.card_fin]
  let P : K → Prop := fun x => ∃ (d : R) (y : O), d • x = y ∧ d ∈ nonZeroDivisors R
  change (P x)
  have h : x ∈ Submodule.span Q (Set.range (O.val ∘ b)) := by
    rw [this]
    exact Submodule.mem_top
  refine Submodule.span_induction ?_ ?_ ?_ ?_ h
  · rintro x ⟨i, hi⟩
    use 1, (b i)
    rw [← hi]
    simp only [Subalgebra.coe_val, Function.comp_apply, one_smul, true_and]
    exact Submonoid.one_mem (nonZeroDivisors R)
  · use 1, 0
    simp only [smul_zero, ZeroMemClass.coe_zero, true_and]
    exact Submonoid.one_mem (nonZeroDivisors R)
  · rintro x y _ _ ⟨d1, n1, ⟨h1, h1z⟩⟩ ⟨d2, n2, ⟨h2, h2z⟩⟩
    use d1 * d2, d2 • n1 + d1 • n2
    constructor
    · simp only [smul_add, AddMemClass.coe_add, SetLike.val_smul]
      rw [← h1, ← h2, mul_smul, mul_smul, smul_comm]
    · exact Submonoid.mul_mem (nonZeroDivisors R) h1z h2z
  · intro a x _ ⟨d1, n1, ⟨h1, h1z⟩⟩
    obtain ⟨⟨m1, m2⟩, h⟩ := IsLocalization.surj (nonZeroDivisors R) a
    use ((m2 : R) * d1), (m1 • n1)
    constructor
    · rw [mul_comm, Algebra.smul_def, Algebra.smul_def,
      IsScalarTower.algebraMap_apply (R := R) (A := K) (S := Q), map_mul, map_mul, mul_assoc,
      SetLike.val_smul_of_tower, Algebra.smul_def,
        IsScalarTower.algebraMap_apply (R := R) (A := K) (S := Q),
        ← h, ← h1, Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply (R := R) (A := K) (S
          := Q)]
      ring
    · exact Submonoid.mul_mem (nonZeroDivisors R) m2.2 h1z

-- Similar to NumberField.RingOfIntegers.instIsLocalizationAlgebraMapSubmonoidIntNonZeroDivisors,
-- which uses IsIntegralClosure.isLocalization_of_isSeparable· But we don't need to assume that `K`
-- is a field
--nor that `O` is the integral closure of `R`·

lemma isLocalization_fraction_ring_of_eq_rank [NeZero n] [CommRing R] [IsDomain R] [Field Q]
    [Algebra R Q] [IsFractionRing R Q] [CommRing K] [Algebra R K] [Algebra Q K]
    [IsScalarTower R Q K]
    [FiniteDimensional Q K] (hd : Module.finrank Q K = n) (O : Subalgebra R K)
    (b : Basis (Fin n) R O) : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors R)) K
      := by
  rw [isLocalization_iff]
  constructor
  · rintro ⟨y, ⟨yp, ⟨hyz, hya⟩ ⟩ ⟩
    refine IsUnit.of_mul_eq_one ((algebraMap Q K) (algebraMap R Q yp)⁻¹) ?_
    dsimp
    rw [← hya]
    change (algebraMap R K yp) * (algebraMap Q K) ((algebraMap R Q yp)⁻¹) = 1
    rw [IsScalarTower.algebraMap_apply (R := R) (A := K) (S := Q), ← map_mul,
      mul_inv_cancel₀, map_one]
    exact IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors Q (fun x a => a) hyz
  constructor
  · intro x
    obtain ⟨d, y, hy, hd⟩ := surj_fraction_ring_of_eq_rank hd O b x
    have hdmem: (algebraMap R O d) ∈ Algebra.algebraMapSubmonoid O (nonZeroDivisors R) := by
      use d
      exact ⟨hd, rfl⟩
    use ⟨y, ⟨(algebraMap R O d), hdmem⟩ ⟩
    dsimp
    have heq : (algebraMap (↥O) K) y = ↑y := rfl
    rw [← hy, Algebra.smul_def, mul_comm]
  · intro x y hxy
    use 1
    simp only [OneMemClass.coe_one, one_mul]
    exact SetCoe.ext hxy

lemma discr_eq_discr_fraction_field [NeZero n] [CommRing R] [IsDomain R] [Field Q] [Algebra R Q]
    [IsFractionRing R Q] [CommRing K] [Algebra R K] [Algebra Q K] [IsScalarTower R Q K]
    [FiniteDimensional Q K] (hd : Module.finrank Q K = n) (O : Subalgebra R K)
    (b : Basis (Fin n) R O) : algebraMap R Q (Algebra.discr R b) = Algebra.discr Q (O.val ∘ b) := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors R)) K :=
    isLocalization_fraction_ring_of_eq_rank hd O b
  have : (Basis.localizationLocalization Q (nonZeroDivisors R) K) b = (O.val ∘ b) := by
    ext i
    simp only [Basis.localizationLocalization_apply, Subalgebra.coe_val, Function.comp_apply]
    rfl
  rw [← this, Algebra.discr_localizationLocalization]

lemma discr_of_matrix_mulVec_fraction_field [NeZero n] [CommRing R] [IsDomain R] [Field Q]
    [Algebra R Q] [IsFractionRing R Q] [CommRing K] [Algebra R K] [Algebra Q K]
    [IsScalarTower R Q K]
    [FiniteDimensional Q K] (hd : Module.finrank Q K = n) (O O' : Subalgebra R K)
    (b : Basis (Fin n) R O) (b' : Basis (Fin n) R O') (A : Matrix (Fin n) (Fin n) Q)
    (hb : O'.val ∘ b' = (A.map (algebraMap Q K)).mulVec (O.val ∘ b)) :
  algebraMap R Q (Algebra.discr R b') = A.det ^ 2 * algebraMap R Q (Algebra.discr R b) := by
  rw [discr_eq_discr_fraction_field hd O, discr_eq_discr_fraction_field hd O',
    hb, Algebra.discr_of_matrix_mulVec]

lemma discr_eq_discr_fraction_field_powerBasis {n : ℕ} [NeZero n] [CommRing R] [IsDomain R]
    [Field Q] [Algebra R Q] [IsFractionRing R Q] [CommRing K] [Algebra R K] [Algebra Q K]
    [IsScalarTower R Q K]
    (O : Type*) [CommRing O] [Algebra R O] (T : Polynomial R) (hdeg : T.natDegree = n)
    (f : IsAdjoinRootMonic O T) (k : IsAdjoinRootMonic K (T.map (algebraMap R Q))) :
    (algebraMap R Q) (Algebra.discr R f.powerBasis.basis) =
      (Algebra.discr Q k.powerBasis.basis) := by
  haveI : FiniteDimensional Q K := Module.Basis.finiteDimensional_of_finite k.powerBasis.basis
  have hdegeq : (map (algebraMap R Q) T).natDegree = T.natDegree := by
    rw [natDegree_map_eq_iff, f.monic]
    simp only [map_one, ne_eq, one_ne_zero, not_false_eq_true, true_or]
  have hkdim : Module.finrank Q K = n:= by
    rw [← hdeg, Module.finrank_eq_card_basis
    k.powerBasis.3, IsAdjoinRootMonic.powerBasis_dim, Fintype.card_fin]
    exact hdegeq
  have pbdim : f.powerBasis.dim = n := by
    rw [IsAdjoinRootMonic.powerBasis_dim, hdeg]
  have pbdim' : k.powerBasis.dim = n := by
    rw [IsAdjoinRootMonic.powerBasis_dim, hdegeq, hdeg]
  haveI : NeZero (f.powerBasis.dim) := by rw [pbdim];  infer_instance
  rw [Algebra.discr_eq_discr_of_algEquiv f.powerBasis.basis (Algebra.adjoinRootEquivOfRootMem
    O T f.monic f.toIsAdjoinRoot k.toIsAdjoinRoot)]
  let B := Basis.map f.powerBasis.basis (Algebra.adjoinRootEquivOfRootMem O T f.monic
    f.toIsAdjoinRoot k.toIsAdjoinRoot).toLinearEquiv
  erw [← Algebra.discr_reindex _ B (finCongr pbdim),  ← Basis.coe_reindex ]
  rw [← Algebra.discr_reindex _ ((k.powerBasis).basis) (finCongr pbdim')]
  rw [discr_eq_discr_fraction_field hkdim]
  congr
  ext i
  simp only [Subalgebra.coe_val, Algebra.adjoinRootEquivOfRootMem, Basis.coe_reindex,
    finCongr_symm, Function.comp_apply, finCongr_apply, Basis.map_apply,
    AlgEquiv.toLinearEquiv_apply, PowerBasis.coe_basis, B]
  simp [map_pow, IsAdjoinRoot.algEquiv_root, Algebra.adjoinIsAdjoinRoot_root]

/-- Imported declaration. -/
noncomputable def Subalgebra.algEquivOfInclusion {R M : Type _} [CommRing R] [CommRing M]
    [Algebra R M]
    (O Om : Subalgebra R M) (hm : O ≤ Om) :
    O  ≃ₐ[R] (Subalgebra.inclusion hm).range := by
  apply AlgEquiv.ofInjective
  exact inclusion_injective hm

/-- Imported declaration. -/
noncomputable def Subalgebra.linearEquivOfInclusion {R M : Type _} [CommRing R] [CommRing M]
    [Algebra R M]
    (O Om : Subalgebra R M) (hm : O ≤ Om) :
    O ≃ₗ[R] Subalgebra.toSubmodule (Subalgebra.inclusion hm).range := by
  have equiv := AlgEquiv.toLinearEquiv (Subalgebra.algEquivOfInclusion _ _ hm)
  exact equiv

/-- If `O ≤ O'` and a basis for `O'` is obtained from a basis `(b₁, …, bₙ)` of `O`
  by multiplying it with a matrix `A` over `Q`. Then the inverse of `A` is given by the
  matrix representing the inclusion map `O → O'` with respect to these bases. -/
lemma inv_matrix_eq_integral_fraction_field [NeZero n] [CommRing R] [IsDomain R] [Field Q]
    [Algebra R Q] [IsFractionRing R Q] [CommRing K] [Algebra R K] [Algebra Q K]
    [IsScalarTower R Q K] (O O' : Subalgebra R K)
    (hm : O ≤ O') (b : Basis (Fin n) R O) (b' : Basis (Fin n) R O') (A : Matrix (Fin n) (Fin n) Q)
    (hb : O'.val ∘ b' = (A.map (algebraMap Q K)).mulVec (O.val ∘ b)) :
    A⁻¹ = Matrix.map (LinearMap.toMatrix (b.map (Subalgebra.linearEquivOfInclusion _ _ hm))
      b' (Submodule.subtype ((Subalgebra.toSubmodule (Subalgebra.inclusion hm).range)))).transpose
        (algebraMap R Q) := by
  have hbc := hb
  have hlin : LinearIndependent Q (Subtype.val ∘ b') := by
      rw [← LinearIndependent.iff_fractionRing (R := R)]
      refine LinearIndependent.map' b'.linearIndependent
        (SMulMemClass.subtype O') (LinearMap.ker_eq_bot_of_injective (Subtype.val_injective))
  apply_fun (fun x => (A⁻¹.map (algebraMap Q K)).mulVec x) at hb
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul,
    Matrix.map_one, Matrix.one_mulVec] at hb
  · apply_fun (fun x => (x.map (algebraMap Q K)).mulVec (O'.val ∘ b'))
    · dsimp
      have : (algebraMap Q K) ∘ (algebraMap R Q) = (algebraMap R K) := by
        ext x
        exact Eq.symm (IsScalarTower.algebraMap_apply R Q K _)
      erw [hb, Matrix.map_map, this]
      ext i
      unfold Matrix.mulVec
      unfold dotProduct
      simp only [ Matrix.map_apply, LinearMap.toMatrix_transpose_apply]
      simp only [Subalgebra.coe_val, Function.comp_apply, Basis.map_apply, Submodule.coe_subtype]
      have : (b i : K) = algebraMap O' K ((O.linearEquivOfInclusion O' hm) (b i)) := rfl
      rw [this]
      nth_rw 1 [← Basis.sum_repr b' ((O.linearEquivOfInclusion O' hm) (b i))]
      simp only [Algebra.smul_def, map_sum, map_mul]
      rfl
    · intro x y hxy
      unfold Matrix.mulVec dotProduct at hxy
      ext i j
      replace hxy := congrFun hxy i
      simp_rw [Matrix.map_apply, ← Algebra.smul_def] at hxy
      replace hxy := sub_eq_zero_of_eq hxy
      simp_rw [← Finset.sum_sub_distrib, ← sub_smul] at hxy
      exact eq_of_sub_eq_zero (linearIndependent_iff'.1 hlin _ _ hxy j (Finset.mem_univ j))
  · exact algebraMap.coe_zero
  · exact algebraMap.coe_one
  · by_contra hc
    rw [isUnit_iff_ne_zero, ne_eq, not_not, ← Matrix.exists_vecMul_eq_zero_iff] at hc
    obtain ⟨v, hvz, hveq⟩ := hc
    apply_fun (fun x => dotProduct ((algebraMap Q K) ∘ v) x) at hbc
    rw [Matrix.dotProduct_mulVec] at hbc
    unfold dotProduct at hbc
    simp only [← RingHom.map_vecMul (algebraMap Q K) A v, hveq, Function.comp_apply, Pi.zero_apply,
      map_zero, zero_mul,
      Finset.sum_const_zero, ← Algebra.smul_def] at hbc
    apply hvz
    ext j
    exact (linearIndependent_iff'.1 hlin _ _ hbc j (Finset.mem_univ j))

lemma inv_det_eq_integral_fraction_field [NeZero n] [CommRing R] [IsDomain R] [Field Q]
    [Algebra R Q] [IsFractionRing R Q] [CommRing K] [Algebra R K] [Algebra Q K]
    [IsScalarTower R Q K] (O O' : Subalgebra R K)
    (hm : O ≤ O') (b : Basis (Fin n) R O) (b' : Basis (Fin n) R O') (A : Matrix (Fin n) (Fin n) Q)
    (hb : O'.val ∘ b' = (A.map (algebraMap Q K)).mulVec (O.val ∘ b)) :
    ∃ (r : R), (algebraMap R Q r) = A.det⁻¹ := by
  use ((LinearMap.toMatrix (b.map (Subalgebra.linearEquivOfInclusion _ _ hm))
    b' (Submodule.subtype ((Subalgebra.toSubmodule (Subalgebra.inclusion
      hm).range)))).transpose).det
  simp_rw [RingHom.map_det, RingHom.mapMatrix_apply,
    ← inv_matrix_eq_integral_fraction_field O O' hm b b' A hb]
  simp only [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']


/-- If `s` is a subset of an `R`-algebra `M`, then the `R`-span of `s` is closed under
  multiplication
if and only if every pairwise product of elements in `s` lies in the span of `s`· -/
lemma span_closed_multiplication_iff_closed_mul_mems {R M : Type*} [CommSemiring R] [Semiring M]
    [Algebra R M] (s : Set M) :
    (∀ (x y : M), x ∈ Submodule.span R s  → y ∈ Submodule.span R s → x * y ∈ Submodule.span R s)
    ↔ (∀ (x y : M), x ∈ s → y ∈ s → x * y ∈ Submodule.span R s) := by
  constructor
  · intros h x y hx hy
    exact h x y (Submodule.subset_span hx) (Submodule.subset_span hy)
  · intros h x y hx hy
    have := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span R s s]  at this
    refine (Submodule.span_le.2 ?_) this
    intros a ha
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.1 ha
    simpa [hxy] using h x y hx hy

/-- Equivalent to span_closed_multiplication_iff_closed_mul_mems
  but the elements of `s` are indexed by `ι`· -/
lemma span_closed_multiplication_iff_closed_mul_mems' {R M ι : Type*} [CommSemiring R] [Semiring M]
    [Algebra R M] (v : ι → M) :
    (∀ (x y : M), x ∈ Submodule.span R (Set.range v)  → y ∈ Submodule.span R (Set.range v)
      → x * y ∈ Submodule.span R (Set.range v))
    ↔ (∀ (i j : ι), (v i) * (v j)  ∈ Submodule.span R (Set.range v)) := by
  constructor
  · intro h
    rw [span_closed_multiplication_iff_closed_mul_mems] at h
    intros i j
    exact h (v i) (v j) (Set.mem_range_self i) (Set.mem_range_self j)
  · intro h
    rw [span_closed_multiplication_iff_closed_mul_mems]
    intros x y hx hy
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    rw [← hi, ← hj]
    exact h i j

/-- If `O` is an `R`-subalgebra of `K` and is noetherian as an `R`-module, then it is
  contained in the integral closure of `R` in `K`· -/
lemma le_integralClosure_of_noetherian {K R : Type*} [CommRing K] [CommRing R] [Algebra R K]
    (O : Subalgebra R K) [hN : IsNoetherian R O] : O ≤ integralClosure R K :=
fun x hx ↦ (isIntegral_of_submodule_noetherian O hN x hx)

/-- If `R` is a noetherian ring and `O` is an `R`-subalgebra with a finite basis,
  then it is a noetherian `R`-module· -/
lemma subalgebraIsNoetherianOfFintypeBasis {K R ι : Type*} [Finite ι] [CommRing K] [CommRing R]
    [Algebra R K] [IsNoetherianRing R] (O : Subalgebra R K)
    (b : Basis ι R O) : IsNoetherian R O := by
  refine isNoetherian_of_fg_of_noetherian (Subalgebra.toSubmodule O) ?_
  rw [← Submodule.fg_top, ← Module.finite_def]
  exact Module.Finite.of_basis b

/-- If `R` is a noetherian ring and `O` is an `R`-subalgebra with a finite basis,
  then it is a noetherian ring· -/
lemma subalgebraIsNoetherianRingOfFintypeBasis {K R ι : Type*} [Finite ι] [CommRing K]
  [CommRing R] [Algebra R K]
[IsNoetherianRing R] (O : Subalgebra R K) (b : Basis ι R O) : IsNoetherianRing O := by
  rw [isNoetherianRing_iff]
  have hnoeth : IsNoetherian R O := by
    refine isNoetherian_of_fg_of_noetherian (Subalgebra.toSubmodule O) ?_
    rw [← Submodule.fg_top, ← Module.finite_def]
    exact Module.Finite.of_basis b
  letI : Module O O := Semiring.toModule
  convert @isNoetherian_of_tower R O O _ _ _ _ _ _ _ hnoeth

/-- If `R` is a PID and `O` is an `R`-subalgebra contained in a finite free subalgebra,
then `O` is a noetherian ring· -/
lemma subalgebraIsNoetherianRingOfLeFreeFiniteSubalgebra {K R ι : Type*} [Finite ι] [CommRing K]
    [CommRing R] [IsDomain R] [Algebra R K] [IsPrincipalIdealRing R] (O Om : Subalgebra R K)
    (h : O ≤ Om) (b : Basis ι R Om) : IsNoetherianRing O := by
  have hm': Subalgebra.toSubmodule O ≤ Subalgebra.toSubmodule Om := by
    simp only [OrderEmbedding.le_iff_le]
    exact h
  obtain ⟨ k, bk ⟩ := Submodule.basisOfPidOfLE hm' b
  rw [isNoetherianRing_iff]
  have hnoeth: IsNoetherian R O := by convert subalgebraIsNoetherianOfFintypeBasis O bk
  letI : Module O O := Semiring.toModule
  convert @isNoetherian_of_tower R O O _ _ _ _ _ _ _ hnoeth

/-- If `R` is a noetherian ring and `O` is an `R`-subalgebra of `K` with a finite basis,
  then it is contained in the integral closure of `R` in `K`· -/
lemma le_integralClosure_of_basis {K R ι : Type*} [Finite ι] [CommRing K] [CommRing R]
    [Algebra R K] [IsNoetherianRing R] (O : Subalgebra R K) (b : Basis ι R O) :
  O ≤ integralClosure R K := by
  haveI := subalgebraIsNoetherianOfFintypeBasis O b
  exact le_integralClosure_of_noetherian O

/-- If `O` is obtained by adjoining to a domain `R` a root of a prime polynomial with
coefficients in `R`, then it is a domain· -/
theorem isDomainOfIsAdjointRootPrime {O R : Type _} [CommRing O] [CommRing R] [IsDomain R]
    [Algebra R O]
    (T : R[X]) (hp : Prime T) (hj : IsAdjoinRoot O T) : IsDomain O := by
  have := AlgEquiv.toRingEquiv (hj.algEquiv (AdjoinRoot.isAdjoinRoot T))
  have _ : IsDomain (AdjoinRoot T) := AdjoinRoot.isDomain_of_prime hp
  exact this.toMulEquiv.isDomain (AdjoinRoot T)

lemma rank_subalgebra_eq_card_basis {n : ℕ} {K R : Type*} [CommRing K] [CommRing R]
    [StrongRankCondition R] [Algebra R K] (O : Subalgebra R K)
    (b : Basis (Fin n) R O) : Module.rank R O = n := by
  rw [rank_eq_card_basis b]
  simp only [Fintype.card_fin]

/-- An auxiliary lemma to prove irreducibility· Let `p` be a polynomial that is not a unit
in `R[X]`, and `q` a non-constant polynomial· Then `p` is irreducible if `p ∘ q` is irreducible· -/
lemma Polynomial.irreducible_of_irreducible_comp {R : Type _} [CommRing R] [NoZeroDivisors R]
    (p q : Polynomial R) (hp : ¬ (IsUnit p)) (hgd : q.natDegree ≠ 0) :
  Irreducible (p.comp q) → Irreducible p := by
  cases (irreducible_or_factor hp)
  · case _ hc1 =>
    intro _
    exact hc1
  case _ hc2 =>
  intro h
  exfalso
  obtain ⟨a, b, ⟨hanu, hbnu, hab⟩ ⟩ := hc2
  rw [hab, mul_comp] at h
  cases of_irreducible_mul h
  · case _ h_1 =>
    have hcompn : (a.comp q).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit h_1
    rw [Polynomial.natDegree_comp] at hcompn
    simp only [Nat.mul_eq_zero, hgd, or_false] at hcompn
    rw [Polynomial.eq_C_of_natDegree_eq_zero hcompn] at h_1
    simp only [C_comp] at h_1
    rw [← Polynomial.eq_C_of_natDegree_eq_zero hcompn] at h_1
    exact hanu h_1
  · case _ h_1 =>
    have hcompn : (b.comp q).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit h_1
    rw [Polynomial.natDegree_comp] at hcompn
    simp only [Nat.mul_eq_zero, hgd, or_false] at hcompn
    rw [Polynomial.eq_C_of_natDegree_eq_zero hcompn] at h_1
    simp only [C_comp] at h_1
    rw [← Polynomial.eq_C_of_natDegree_eq_zero hcompn] at h_1
    exact hbnu h_1
