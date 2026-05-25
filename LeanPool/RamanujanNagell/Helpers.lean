/-
Copyright (c) 2026 Barinder S. Banwait. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Barinder S. Banwait
-/

import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import LeanPool.RamanujanNagell.QuadraticIntegers.RingOfIntegers
import LeanPool.RamanujanNagell.QuadraticIntegers.FieldIsomorphism

open Polynomial NumberField QuadraticAlgebra RingOfIntegers Algebra Nat Ideal InfinitePlace
  UniqueFactorizationMonoid

/-! ## Algebraic Number Theory Facts

The following lemmas encode number-theoretic facts about the ring of integers of ℚ(√-7)
that are used in the proof of the Ramanujan-Nagell theorem but require algebraic number
theory machinery beyond what is currently available in Mathlib.

Reference: These facts can be found in standard algebraic number theory textbooks.
The class number of ℚ(√-7) being 1 is part of the Heegner-Stark theorem which classifies
all imaginary quadratic fields with class number 1: d = -1, -2, -3, -7, -11, -19, -43, -67, -163.
-/
noncomputable section
/-- The minimal polynomial of θ: X² - X + 2.
    Its discriminant is -7, so it is irreducible over ℚ. -/
abbrev f_minpoly : ℚ[X] := X ^ 2 - X + C 2

instance : Fact (Irreducible f_minpoly) := ⟨by
-- Since $f_minpoly$ is a quadratic polynomial with no rational roots, it must be irreducible over $\mathbb{Q}$.
have h_irred : ∀ p q : ℚ[X], p.degree > 0 → q.degree > 0 → f_minpoly = p * q → False := by
  intros p q hp hq h_eq
  have h_deg : p.degree + q.degree = 2 := by
    erw [ ← Polynomial.degree_mul, ← h_eq, Polynomial.degree_add_C ] <;> erw [ Polynomial.degree_sub_eq_left_of_degree_lt ] <;> norm_num;
  -- Since $p$ and $q$ are non-constant polynomials with degrees adding up to 2, they must both be linear.
  have h_linear : p.degree = 1 ∧ q.degree = 1 := by
    rw [ Polynomial.degree_eq_natDegree ( Polynomial.ne_zero_of_degree_gt hp ), Polynomial.degree_eq_natDegree ( Polynomial.ne_zero_of_degree_gt hq ) ] at * ; norm_cast at * ; exact ⟨ by linarith, by linarith ⟩;
  -- Let $r$ be a root of $p$. Then $p(r) = 0$, which implies $r^2 - r + 2 = 0$.
  obtain ⟨r, hr⟩ : ∃ r : ℚ, p.eval r = 0 := by
    exact Polynomial.exists_root_of_degree_eq_one h_linear.1;
  replace h_eq := congr_arg ( Polynomial.eval r ) h_eq; norm_num [ hr ] at h_eq; nlinarith [ sq_nonneg ( r - 1 / 2 ) ] ;
-- Apply the definition of irreducibility using h_irred.
apply Irreducible.mk;
· exact fun h => absurd ( Polynomial.degree_eq_zero_of_isUnit h ) ( by erw [ show f_minpoly = Polynomial.X ^ 2 - Polynomial.X + 2 from rfl ] ; erw [ Polynomial.degree_add_C ] <;> erw [ Polynomial.degree_sub_eq_left_of_degree_lt ] <;> norm_num );
· contrapose! h_irred;
  obtain ⟨ a, b, h₁, h₂, h₃ ⟩ := h_irred; exact ⟨ a, b, not_le.mp fun h => h₂ <| Polynomial.isUnit_iff_degree_eq_zero.mpr <| le_antisymm h <| le_of_not_gt fun h' => by { apply_fun Polynomial.eval 0 at h₁; aesop }, not_le.mp fun h => h₃ <| Polynomial.isUnit_iff_degree_eq_zero.mpr <| le_antisymm h <| le_of_not_gt fun h' => by { apply_fun Polynomial.eval 0 at h₁; aesop }, h₁, trivial ⟩ ;⟩

notation "K" => QuadraticAlgebra ℚ (-2) 1

-- ω² = -2 + 1*ω, i.e. ω = (1 + √(-7))/2, the generator of the ring of integers of Q(√(-7)).
-- The Fact says the polynomial x² - x + 2 has no rational roots (discriminant = -7 < 0).
instance : Fact (∀ (r : ℚ), r ^ 2 ≠ (-2 : ℚ) + (1 : ℚ) * r) := by
  constructor
  intro r h
  have h1 : r ^ 2 - r + 2 = 0 := by linarith
  have h2 : 4 * (r ^ 2 - r + 2) = (2 * r - 1) ^ 2 + 7 := by ring
  have h3 : (2 * r - 1) ^ 2 + 7 = 0 := by linarith
  have h4 : (2 * r - 1) ^ 2 ≥ 0 := sq_nonneg _
  linarith

-- QuadraticAlgebra provides Module.Finite via instFinite, but NumberField expects
-- FiniteDimensional via DivisionRing.toRatAlgebra. These Algebra instances are propositionally
-- equal by Rat.algebra_rat_subsingleton, so we transport the finiteness proof.
instance : NumberField K := by
  have h_alg : (QuadraticAlgebra.instAlgebra : Algebra ℚ K) = DivisionRing.toRatAlgebra :=
    Subsingleton.elim _ _
  have h_mod : @Algebra.toModule ℚ K _ _ QuadraticAlgebra.instAlgebra =
      @Algebra.toModule ℚ K _ _ DivisionRing.toRatAlgebra := by rw [h_alg]
  refine @NumberField.mk K _ inferInstance ?_
  rw [show @Algebra.toModule ℚ K _ _ DivisionRing.toRatAlgebra =
      (QuadraticAlgebra.instModule : Module ℚ K) from h_mod.symm]
  exact inferInstance

-- Field instance is provided automatically by QuadraticAlgebra.instField

notation "R" => (𝓞 K)

lemma is_integral_ω : IsIntegral ℤ (ω : K) := by
  -- ω satisfies X² - X + 2 = 0 (since ω² = -2 + ω in QuadraticAlgebra ℚ (-2) 1)
  refine ⟨X ^ 2 - X + C 2, ?_, ?_⟩
  · -- Monic: rewrite as X² - (X - 2) and use degree argument
    rw [show (X ^ 2 - X + C (2 : ℤ) : ℤ[X]) = X ^ 2 - (X - C 2) from by ring]
    exact monic_X_pow_sub (by rw [degree_X_sub_C]; norm_num)
  · -- Evaluation: ω² - ω + 2 = (-2 + ω) - ω + 2 = 0
    rw [← aeval_def]
    simp only [map_add, map_sub, aeval_X_pow, aeval_X, aeval_C]
    rw [sq, omega_mul_omega_eq_mk]
    ext <;> simp

/-- The element θ = (1 + √-7)/2 of 𝓞 K, expressed as ω = (1+√-7)/2 with its integrality proof. -/
abbrev θ : 𝓞 K := ⟨ω, is_integral_ω⟩

lemma is_integral_one_sub_ω : IsIntegral ℤ ((1 : K) - ω) := by
-- 1 - ω satisfies the same polynomial X² - X + 2 = 0
  refine ⟨X ^ 2 - X + C 2, ?_, ?_⟩
  · -- Monic: same argument as for ω
    rw [show (X ^ 2 - X + C (2 : ℤ) : ℤ[X]) = X ^ 2 - (X - C 2) from by ring]
    exact monic_X_pow_sub (by rw [degree_X_sub_C]; norm_num)
  · -- Evaluation: (1 - ω)² - (1 - ω) + 2 = 0
    rw [← aeval_def]
    simp only [map_add, map_sub, aeval_X_pow, aeval_X, aeval_C]
    -- Expand (1 - ω)² = 1 - 2ω + ω²
    rw [sub_sq, one_pow, mul_one]
    -- Substitute ω² = -2 + ω
    rw [sq, omega_mul_omega_eq_mk]
    -- Verify the arithmetic holds in each component of the QuadraticAlgebra
    ext <;> simp
    ring

/-- θ' = (1 - √-7)/2, the conjugate of θ in the ring of integers. -/
abbrev θ' : 𝓞 K := ⟨1 - ω, is_integral_one_sub_ω⟩

lemma my_minpoly : minpoly ℤ θ = X ^ 2 - X + 2 := by
  -- Reduce from θ : 𝓞 K to ω : K via minpoly_coe
  rw [show minpoly ℤ θ = minpoly ℤ (ω : K) from
    (NumberField.RingOfIntegers.minpoly_coe ⟨ω, is_integral_ω⟩).symm]
  -- X² - X + 2 is monic over ℤ
  have h_monic : (X ^ 2 - X + C (2 : ℤ) : ℤ[X]).Monic := by
    rw [show (X ^ 2 - X + C (2 : ℤ) : ℤ[X]) = X ^ 2 - (X - C 2) from by ring]
    exact monic_X_pow_sub (by rw [degree_X_sub_C]; norm_num)
  -- Irreducible over ℤ via Gauss's lemma + Fact (Irreducible f_minpoly)
  have h_irred : Irreducible (X ^ 2 - X + C (2 : ℤ) : ℤ[X]) := by
    rw [Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast h_monic.isPrimitive]
    have : Polynomial.map (Int.castRingHom ℚ) (X ^ 2 - X + C (2 : ℤ)) = f_minpoly := by
      simp [f_minpoly, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow, map_X]
      rfl
    rw [this]
    exact Fact.out
  -- ω is a root of X² - X + 2
  have h_root : Polynomial.aeval (ω : K) (X ^ 2 - X + C (2 : ℤ)) = 0 := by
    simp only [map_add, map_sub, map_pow, aeval_X, map_ofNat]
    rw [sq, omega_mul_omega_eq_mk]; ext <;> simp
  -- minpoly ℤ ω divides X² - X + 2; since the latter is irreducible, they're associated
  have h_dvd := minpoly.isIntegrallyClosed_dvd is_integral_ω h_root
  exact eq_of_monic_of_associated (minpoly.monic is_integral_ω) h_monic
    ((minpoly.irreducible is_integral_ω).associated_of_dvd h_irred h_dvd)

lemma my_minpoly_theta_prime : minpoly ℤ θ' = X ^ 2 - X + 2 := by
  -- Reduce from θ' : 𝓞 K to (1 - ω) : K via minpoly_coe
  rw [show minpoly ℤ θ' = minpoly ℤ ((1 : K) - ω) from
    (NumberField.RingOfIntegers.minpoly_coe ⟨1 - ω, is_integral_one_sub_ω⟩).symm]
  -- X² - X + 2 is monic over ℤ
  have h_monic : (X ^ 2 - X + C (2 : ℤ) : ℤ[X]).Monic := by
    rw [show (X ^ 2 - X + C (2 : ℤ) : ℤ[X]) = X ^ 2 - (X - C 2) from by ring]
    exact monic_X_pow_sub (by rw [degree_X_sub_C]; norm_num)
  -- Irreducible over ℤ via Gauss's lemma + Fact (Irreducible f_minpoly)
  have h_irred : Irreducible (X ^ 2 - X + C (2 : ℤ) : ℤ[X]) := by
    rw [Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast h_monic.isPrimitive]
    have : Polynomial.map (Int.castRingHom ℚ) (X ^ 2 - X + C (2 : ℤ)) = f_minpoly := by
      simp [f_minpoly, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow, map_X]
      rfl
    rw [this]
    exact Fact.out
  -- (1 - ω) is a root of X² - X + 2
  have h_root : Polynomial.aeval ((1 : K) - ω) (X ^ 2 - X + C (2 : ℤ)) = 0 := by
    simp only [map_add, map_sub, map_pow, aeval_X, map_ofNat]
    rw [sub_sq, one_pow, mul_one, sq, omega_mul_omega_eq_mk]
    ext <;> simp
    ring
  -- minpoly ℤ (1-ω) divides X² - X + 2; since the latter is irreducible, they're associated
  have h_dvd := minpoly.isIntegrallyClosed_dvd is_integral_one_sub_ω h_root
  exact eq_of_monic_of_associated (minpoly.monic is_integral_one_sub_ω) h_monic
    ((minpoly.irreducible is_integral_one_sub_ω).associated_of_dvd h_irred h_dvd)

lemma K_degree_2 : Module.finrank ℚ K = 2 := by
  rw [QuadraticAlgebra.finrank_eq_two]

lemma K_nrRealPlaces_zero : nrRealPlaces K = 0 := by
  rw [nrRealPlaces_eq_zero_iff]
  constructor
  intro v
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hv
  rw [InfinitePlace.isReal_iff] at hv
  -- Get a ring hom ψ : K →+* ℝ from the real embedding
  let ψ := NumberField.ComplexEmbedding.IsReal.embedding hv
  -- ω satisfies ω * ω = ⟨-2, 1⟩ = -2 + ω in K
  have h_eq : (ω : K) * ω = (⟨-2, 1⟩ : K) := by
    exact QuadraticAlgebra.omega_mul_omega_eq_mk
  -- ω² - ω + 2 = 0 in K, so ψ(ω)² - ψ(ω) + 2 = 0 in ℝ
  -- But x² - x + 2 = (x-1/2)² + 7/4 > 0 for all real x
  -- ⟨-2, 1⟩ = -2 + ω in K
  have h_mk : (⟨-2, 1⟩ : K) = -2 + ω := by
    have := @QuadraticAlgebra.mk_eq_add_smul_omega ℚ (-2) 1 _ (-2 : ℚ) (1 : ℚ)
    simp at this
    exact this
  rw [h_mk] at h_eq
  have h1 := congr_arg ψ h_eq
  simp only [map_mul, map_add, map_neg, map_ofNat] at h1
  have h2 : (ψ ω - 1/2) ^ 2 + 7/4 = ψ ω * ψ ω - ψ ω + 2 := by ring
  have h4 : (ψ ω - 1/2) ^ 2 ≥ 0 := sq_nonneg _
  linarith

lemma K_nrComplexPlaces_2 : nrComplexPlaces K = 1 := by
  have h := card_add_two_mul_card_eq_rank K
  have h_alg : (QuadraticAlgebra.instAlgebra : Algebra ℚ K) = DivisionRing.toRatAlgebra :=
    Subsingleton.elim _ _
  have h2 : @Module.finrank ℚ K _ _ DivisionRing.toRatAlgebra.toModule = 2 := by
    rw [← h_alg]; exact K_degree_2
  rw [h2, K_nrRealPlaces_zero] at h
  omega

lemma span_eq_top : adjoin ℤ {θ} = ⊤ := by
  -- Strategy:
  -- 1. `ring_of_integers_neg7` gives IsIntegralClosure (QuadraticAlgebra ℤ (-2) 1) ℤ K'
  -- 2. `fieldIso : K' ≃ₐ[ℚ] K` transports this to IsIntegralClosure (QuadraticAlgebra ℤ (-2) 1) ℤ K
  --    (see `isIntegralClosure_K`)
  -- 3. `IsIntegralClosure.equiv` gives AlgEquiv ℤ (QuadraticAlgebra ℤ (-2) 1) (𝓞 K) sending ω ↦ θ
  -- 4. Pull back `adjoin ℤ {ω} = ⊤` (in QuadraticAlgebra ℤ (-2) 1) via the iso
  obtain ⟨iso, h_iso_omega⟩ :
      ∃ (iso : QuadraticAlgebra ℤ (-2 : ℤ) 1 ≃ₐ[ℤ] 𝓞 K), iso ω = θ := by
    -- Use OK_to_K (FieldIsomorphism.lean) which maps ω ↦ ω directly (not via K').
    letI alg_int_K : Algebra (QuadraticAlgebra ℤ (-2 : ℤ) 1) K :=
      OK_to_K.toAlgebra
    haveI hST : IsScalarTower ℤ (QuadraticAlgebra ℤ (-2 : ℤ) 1) K :=
      IsScalarTower.of_algebraMap_eq fun r => (OK_to_K.commutes r).symm
    haveI hIC : IsIntegralClosure (QuadraticAlgebra ℤ (-2 : ℤ) 1) ℤ K := isIntegralClosure_K (by
      change OK_to_K ω = ω
      rw [OK_to_K, QuadraticAlgebra.lift_apply_apply]
      simp [omega_re, omega_im])
    -- Apply IsIntegralClosure.equiv to obtain the canonical AlgEquiv
    refine ⟨IsIntegralClosure.equiv ℤ (QuadraticAlgebra ℤ (-2 : ℤ) 1) K (𝓞 K), ?_⟩
    -- Show iso ω = θ = ⟨ω, is_integral_ω⟩ by comparing underlying elements in K
    apply Subtype.ext
    have h := IsIntegralClosure.algebraMap_equiv
      ℤ (QuadraticAlgebra ℤ (-2 : ℤ) 1) K (𝓞 K) ω
    -- h : algebraMap (𝓞 K) K (iso ω) = algebraMap (QuadraticAlgebra ℤ (-2) 1) K ω
    -- With alg_int_K = OK_to_K.toAlgebra, algebraMap ... K ω = OK_to_K ω = ω.
    have h2 : (algebraMap (QuadraticAlgebra ℤ (-2 : ℤ) 1) K) ω = (ω : K) := by
      change OK_to_K ω = ω
      rw [OK_to_K, QuadraticAlgebra.lift_apply_apply]
      simp [omega_re, omega_im]
    exact h.trans h2
  -- Every element of QuadraticAlgebra ℤ (-2) 1 is in adjoin ℤ {ω}
  have h_top : Algebra.adjoin ℤ ({ω} : Set (QuadraticAlgebra ℤ (-2 : ℤ) 1)) = ⊤ :=
    quadraticAlgebra_adjoin_omega_eq_top (-2 : ℤ) 1
  -- The pullback: adjoin ℤ {iso ω} = ⊤ in 𝓞 K
  have h_pull : Algebra.adjoin ℤ ({iso (ω : QuadraticAlgebra ℤ (-2 : ℤ) 1)} : Set (𝓞 K)) = ⊤ := by
    have key : Subalgebra.map iso.toAlgHom
        (Algebra.adjoin ℤ ({ω} : Set (QuadraticAlgebra ℤ (-2 : ℤ) 1))) = ⊤ := by
      rw [h_top, Algebra.map_top, AlgHom.range_eq_top]
      intro b
      exact ⟨iso.symm b, by simp⟩
    rw [AlgHom.map_adjoin_singleton] at key
    exact key
  -- Conclude: adjoin ℤ {θ} = ⊤
  rwa [h_iso_omega] at h_pull

-- θ² = θ - 2 in 𝓞 K (from ω² = -2 + ω in K)
private lemma theta_sq : (θ : 𝓞 K) * θ = θ - 2 := by
  apply Subtype.ext
  show (ω : K) * ω = ω - 2
  have h1 := @QuadraticAlgebra.omega_mul_omega_eq_mk ℚ (-2) 1 _
  have h2 := @QuadraticAlgebra.mk_eq_add_smul_omega ℚ (-2) 1 _ (-2 : ℚ) (1 : ℚ)
  simp at h2
  rw [h1, h2]; ring

lemma K_discriminant : discr K = -7 := by
  have h_int : IsIntegral ℤ (θ : 𝓞 K) := RingOfIntegers.isIntegral θ
  let pb := PowerBasis.ofAdjoinEqTop' h_int span_eq_top
  -- Step 1: any ℤ-basis of 𝓞 K computes the same discriminant
  rw [← discr_eq_discr K pb.basis]
  -- Step 2: the discriminant equals the determinant of the trace matrix
  rw [Algebra.discr_def]
  -- Step 3: pb has dimension 2 (minpoly of θ is X² - X + 2, degree 2)
  have h_dim : pb.dim = 2 := by
    have h1 := pb.natDegree_minpoly
    have h2 : pb.gen = θ := PowerBasis.ofAdjoinEqTop'_gen h_int span_eq_top
    rw [h2, my_minpoly] at h1
    change (X ^ 2 - X + C (2 : ℤ) : ℤ[X]).natDegree = pb.dim at h1
    have h3 : (X ^ 2 - X + C (2 : ℤ) : ℤ[X]).natDegree = 2 := by compute_degree!
    linarith
  -- Step 4: reindex the trace matrix from Fin pb.dim to Fin 2
  --         (det is invariant under reindexing by an equivalence)
  rw [← Matrix.det_reindex_self (finCongr h_dim)]
  -- Step 5: the reindexed trace matrix for the power basis {1, θ} is !![2, 1; 1, -3]
  -- Justification:
  --   pb.basis 0 = θ^0 = 1,  pb.basis 1 = θ^1 = θ  (by pb.basis_eq_pow + h_gen)
  --   trace(1 · 1)   = trace(1) = 2
  --   trace(1 · θ)   = trace(θ) = 1       (sum of conjugates θ + θ' = 1)
  --   trace(θ · θ)   = trace(θ²) = trace(θ - 2) = 1 - 4 = -3  (by theta_sq)
  -- The trace matrix for the power basis {1, θ}, reindexed to Fin 2, is !![2, 1; 1, -3]
  have h_mat : (Matrix.reindex (finCongr h_dim) (finCongr h_dim)) (traceMatrix ℤ ⇑pb.basis) =
      !![2, 1; 1, -3] := by
    have h_gen : pb.gen = θ := PowerBasis.ofAdjoinEqTop'_gen h_int span_eq_top
    -- trace(1) = finrank = 2
    have h_tr_one : Algebra.trace ℤ (𝓞 K) (1 : 𝓞 K) = 2 := by
      rw [show (1 : 𝓞 K) = algebraMap ℤ _ 1 from (map_one _).symm,
          Algebra.trace_algebraMap_of_basis pb.basis,
          show Fintype.card (Fin pb.dim) = 2 from by rw [Fintype.card_fin, h_dim]]
      simp
    -- trace(θ) = -(minpoly).nextCoeff = -(-1) = 1
    have h_tr_gen : Algebra.trace ℤ (𝓞 K) θ = 1 := by
      rw [← h_gen,
          Algebra.trace_eq_matrix_trace pb.basis, Matrix.trace_eq_neg_charpoly_nextCoeff,
          charpoly_leftMulMatrix, h_gen, my_minpoly]
      have hnd : (X ^ 2 - X + (2 : ℤ[X])).natDegree = 2 := by compute_degree!
      rw [nextCoeff_of_natDegree_pos (by omega : 0 < _), hnd]
      norm_num [coeff_add, coeff_sub, coeff_X_pow, coeff_X]
    -- trace(θ²) = trace(θ - 2) = 1 - 4 = -3
    have h_tr_sq : Algebra.trace ℤ (𝓞 K) (θ * θ) = -3 := by
      rw [theta_sq, map_sub,
          show (2 : 𝓞 K) = algebraMap ℤ _ 2 from by simp,
          Algebra.trace_algebraMap_of_basis pb.basis,
          show Fintype.card (Fin pb.dim) = 2 from by rw [Fintype.card_fin, h_dim],
          h_tr_gen]; ring
    -- Prove matrix equality entrywise
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, traceMatrix, Matrix.of_apply,
      traceForm_apply]
    rw [pb.basis_eq_pow, pb.basis_eq_pow]
    have hvi : ((finCongr h_dim).symm i).val = i.val := by simp [finCongr]
    have hvj : ((finCongr h_dim).symm j).val = j.val := by simp [finCongr]
    rw [hvi, hvj, h_gen]
    fin_cases i <;> fin_cases j <;>
      simp only [pow_zero, pow_one, one_mul, mul_one, Matrix.vecCons]
    · exact h_tr_one
    · exact h_tr_gen
    · exact h_tr_gen
    · exact h_tr_sq
  calc ((Matrix.reindex (finCongr h_dim) (finCongr h_dim)) (traceMatrix ℤ ⇑pb.basis)).det
      = (!![2, 1; 1, -3] : Matrix (Fin 2) (Fin 2) ℤ).det := congr_arg Matrix.det h_mat
    _ = -7 := by rw [Matrix.det_fin_two_of]; norm_num

private lemma hno_cube_aux : ∀ z : 𝓞 K, z ^ 2 + z + 1 ≠ 0 := by
  intro z hz_eq
  -- Build a power basis for 𝓞 K / ℤ with generator θ
  have h_int : IsIntegral ℤ θ := RingOfIntegers.isIntegral θ
  let pb := PowerBasis.ofAdjoinEqTop' h_int span_eq_top
  have h_gen : pb.gen = θ := PowerBasis.ofAdjoinEqTop'_gen h_int span_eq_top
  have h_dim : pb.dim = 2 := by
    have h1 := pb.natDegree_minpoly
    rw [h_gen, my_minpoly] at h1
    change (X ^ 2 - X + C (2 : ℤ) : ℤ[X]).natDegree = pb.dim at h1
    have h3 : (X ^ 2 - X + C (2 : ℤ) : ℤ[X]).natDegree = 2 := by compute_degree!
    linarith
  -- Integer coordinates: z = m·1 + n·θ  in the basis {pb.basis 0 = 1, pb.basis 1 = θ}
  set m : ℤ := pb.basis.repr z ⟨0, by omega⟩
  set n : ℤ := pb.basis.repr z ⟨1, by omega⟩
  -- Basis elements: pb.basis 0 = 1, pb.basis 1 = θ = ω
  have hb0 : pb.basis ⟨0, by omega⟩ = (1 : 𝓞 K) := by
    rw [pb.basis_eq_pow]; simp
  have hb1 : pb.basis ⟨1, by omega⟩ = θ := by
    rw [pb.basis_eq_pow, h_gen]; simp
  -- Coordinate representation: z = m • 1 + n • θ
  have hz : z = m • pb.basis ⟨0, by omega⟩ + n • pb.basis ⟨1, by omega⟩ := by
    apply pb.basis.repr.injective
    ext ⟨j, hj⟩
    simp only [LinearEquiv.map_add, LinearEquiv.map_smul,
               Finsupp.add_apply, Finsupp.smul_apply,
               smul_eq_mul]
    have hj2 : j = 0 ∨ j = 1 := by omega
    have eval0 : pb.basis.repr (pb.basis ⟨0, by omega⟩) = Finsupp.single ⟨0, by omega⟩ 1 :=
      LinearEquiv.apply_symm_apply pb.basis.repr _
    have eval1 : pb.basis.repr (pb.basis ⟨1, by omega⟩) = Finsupp.single ⟨1, by omega⟩ 1 :=
      LinearEquiv.apply_symm_apply pb.basis.repr _
    rcases hj2 with rfl | rfl <;>
      rw [eval0, eval1] <;>
      simp [m, n, Fin.ext_iff]
  -- Lift equation to K and record (z : K) = ⟨(m : ℚ), (n : ℚ)⟩
  have hz_K : (z : K) = ⟨(m : ℚ), (n : ℚ)⟩ := by
    have hcoe : (z : K) = m • (1 : K) + n • (ω : K) := by
      have h := congr_arg ((↑) : 𝓞 K → K) hz
      simp only [map_add, hb0, hb1] at h
      exact h
    rw [hcoe]
    ext
    · simp [re_add, omega_re]
    · simp [im_add, omega_im]
  have hz_eq_K : (z : K) ^ 2 + (z : K) + 1 = 0 := by
    have := congr_arg ((↑) : 𝓞 K → K) hz_eq
    push_cast at this
    exact this
  have hcomputed : (⟨(m : ℚ), (n : ℚ)⟩ : K) ^ 2 + ⟨(m : ℚ), (n : ℚ)⟩ + 1 = 0 := by
    rw [← hz_K]; exact hz_eq_K
  -- Substituting into z² + z + 1 = 0 yields two ℤ equations
  have hre : m ^ 2 - 2 * n ^ 2 + m + 1 = 0 := by
    have h := congr_arg (·.re) hcomputed
    simp only [sq, re_add, re_mul, re_one, re_zero] at h
    norm_num at h
    norm_cast at h
    linear_combination h
  have him : n * (2 * m + n + 1) = 0 := by
    have h := congr_arg (·.im) hcomputed
    simp only [sq, im_add, im_mul, im_one, im_zero] at h
    have key : (n : ℚ) * (2 * m + n + 1) = 0 := by linarith
    exact_mod_cast key
  -- Case split on the imaginary-part equation
  rcases mul_eq_zero.mp him with hn0 | h2mn
  · -- n = 0: reduces to m² + m + 1 = 0, no integer solution
    have hm_eq : m ^ 2 + m + 1 = 0 := by nlinarith [sq_nonneg n, hn0]
    nlinarith [sq_nonneg (2 * m + 1)]
  · -- 2m + n + 1 = 0: reduces to 7m² + 7m + 1 = 0, impossible mod 7
    have hn_val : n = -2 * m - 1 := by linarith
    have hn2 : n ^ 2 = 4 * m ^ 2 + 4 * m + 1 := by nlinarith [sq_nonneg (n + 2 * m + 1)]
    have h7 : 7 * m ^ 2 + 7 * m + 1 = 0 := by nlinarith [hre, hn2]
    have h7dvd1 : (7 : ℤ) ∣ 1 := ⟨-(m ^ 2 + m), by linarith⟩
    exact absurd h7dvd1 (by intro ⟨x, hx⟩; omega)

private lemma hno_i_aux : ∀ z : 𝓞 K, z ^ 2 + 1 ≠ 0 := by
  intro z hz_eq
  -- Build a power basis for 𝓞 K / ℤ with generator θ
  have h_int : IsIntegral ℤ θ := RingOfIntegers.isIntegral θ
  let pb := PowerBasis.ofAdjoinEqTop' h_int span_eq_top
  have h_gen : pb.gen = θ := PowerBasis.ofAdjoinEqTop'_gen h_int span_eq_top
  have h_dim : pb.dim = 2 := by
    have h1 := pb.natDegree_minpoly
    rw [h_gen, my_minpoly] at h1
    change (X ^ 2 - X + C (2 : ℤ) : ℤ[X]).natDegree = pb.dim at h1
    have h3 : (X ^ 2 - X + C (2 : ℤ) : ℤ[X]).natDegree = 2 := by compute_degree!
    linarith
  -- Integer coordinates: z = m·1 + n·θ  in the basis {pb.basis 0 = 1, pb.basis 1 = θ}
  set m : ℤ := pb.basis.repr z ⟨0, by omega⟩
  set n : ℤ := pb.basis.repr z ⟨1, by omega⟩
  -- Basis elements: pb.basis 0 = 1, pb.basis 1 = θ = ω
  have hb0 : pb.basis ⟨0, by omega⟩ = (1 : 𝓞 K) := by
    rw [pb.basis_eq_pow]; simp
  have hb1 : pb.basis ⟨1, by omega⟩ = θ := by
    rw [pb.basis_eq_pow, h_gen]; simp
  -- Coordinate representation: z = m • 1 + n • θ
  have hz : z = m • pb.basis ⟨0, by omega⟩ + n • pb.basis ⟨1, by omega⟩ := by
    apply pb.basis.repr.injective
    ext ⟨j, hj⟩
    simp only [LinearEquiv.map_add, LinearEquiv.map_smul,
               Finsupp.add_apply, Finsupp.smul_apply,
               smul_eq_mul]
    have hj2 : j = 0 ∨ j = 1 := by omega
    have eval0 : pb.basis.repr (pb.basis ⟨0, by omega⟩) = Finsupp.single ⟨0, by omega⟩ 1 :=
      LinearEquiv.apply_symm_apply pb.basis.repr _
    have eval1 : pb.basis.repr (pb.basis ⟨1, by omega⟩) = Finsupp.single ⟨1, by omega⟩ 1 :=
      LinearEquiv.apply_symm_apply pb.basis.repr _
    rcases hj2 with rfl | rfl <;>
      rw [eval0, eval1] <;>
      simp [m, n, Fin.ext_iff]
  -- Lift equation to K and record (z : K) = ⟨(m : ℚ), (n : ℚ)⟩
  have hz_K : (z : K) = ⟨(m : ℚ), (n : ℚ)⟩ := by
    have hcoe : (z : K) = m • (1 : K) + n • (ω : K) := by
      have h := congr_arg ((↑) : 𝓞 K → K) hz
      simp only [map_add, hb0, hb1] at h
      exact h
    rw [hcoe]
    ext
    · simp [re_add, omega_re]
    · simp [im_add, omega_im]
  have hz_eq_K : (z : K) ^ 2 + 1 = 0 := by
    have := congr_arg ((↑) : 𝓞 K → K) hz_eq
    push_cast at this
    exact this
  have hcomputed : (⟨(m : ℚ), (n : ℚ)⟩ : K) ^ 2 + 1 = 0 := by
    rw [← hz_K]; exact hz_eq_K
  -- Substituting into z² + 1 = 0 yields two ℤ equations
  have hre : m ^ 2 - 2 * n ^ 2 + 1 = 0 := by
    have h := congr_arg (·.re) hcomputed
    simp only [sq, re_add, re_mul, re_one, re_zero] at h
    norm_num at h
    norm_cast at h
    linear_combination h
  have him : n * (2 * m + n) = 0 := by
    have h := congr_arg (·.im) hcomputed
    simp only [sq, im_add, im_mul, im_one, im_zero] at h
    have key : (n : ℚ) * (2 * m + n) = 0 := by linarith
    exact_mod_cast key
  -- Case split on the imaginary-part equation
  rcases mul_eq_zero.mp him with hn0 | h2mn
  · -- n = 0: reduces to m² + 1 = 0, no integer solution
    have hm_eq : m ^ 2 + 1 = 0 := by nlinarith [sq_nonneg n, hn0]
    nlinarith [sq_nonneg m]
  · -- 2m + n = 0: reduces to 7m² = 1, impossible mod 7
    have hn_val : n = -2 * m := by linarith
    have hn2 : n ^ 2 = 4 * m ^ 2 := by rw [hn_val]; ring
    have h7 : 7 * m ^ 2 = 1 := by nlinarith [hre, hn2]
    have h7dvd1 : (7 : ℤ) ∣ 1 := ⟨m ^ 2, by linarith⟩
    exact absurd h7dvd1 (by intro ⟨x, hx⟩; omega)

lemma units_pm_one : ∀ u : Rˣ, u = 1 ∨ u = -1 := by
  intro u
  -- Step 1: reduce to "u is a root of unity in K"
  suffices h_torsion : u ∈ NumberField.Units.torsion K by
    -- u has finite order (torsion = elements of finite order)
    have h_fin : IsOfFinOrder u := (CommGroup.mem_torsion Rˣ u).mp h_torsion
    -- KEY fact: orderOf u divides 2.
    -- Proof sketch: any primitive nth root of unity ζ in K satisfies φ(n) ≤ [K:ℚ] = 2,
    -- so n ∈ {1,2,3,4,6}. But n ∈ {3,4,6} would force K = ℚ(ζ₃) or ℚ(i),
    -- which have discriminants -3 or -4, contradicting disc(K) = -7.
    have h_div2 : orderOf u ∣ 2 := by
      have h_pos : 0 < orderOf u := orderOf_pos_iff.mpr h_fin
      -- φ(orderOf u) ≤ [K:ℚ] = 2 (IsPrimitiveRoot.totient_le_degree_minpoly + my_minpoly)
      have h_totient_le : Nat.totient (orderOf u) ≤ 2 := by
        -- Rewrite orderOf u as orderOf (u : R) via orderOf_units
        rw [← orderOf_units (y := u)]
        -- (u : R) is a primitive (orderOf (u : R))-th root of unity
        have h_prim : IsPrimitiveRoot (u : R) (orderOf (u : R)) := IsPrimitiveRoot.orderOf _
        -- φ(orderOf (u:R)) ≤ natDegree (minpoly ℤ (u:R))
        have h1 : Nat.totient (orderOf (u : R)) ≤ (minpoly ℤ (u : R)).natDegree :=
          IsPrimitiveRoot.totient_le_degree_minpoly h_prim
        -- natDegree (minpoly ℤ (u:R)) ≤ 2 via Cayley-Hamilton for the left-multiplication map
        have h2' : (minpoly ℤ (u : R)).natDegree ≤ 2 := by
          set lm := Algebra.lmul ℤ R (u : R)
          -- Cayley-Hamilton: aeval lm lm.charpoly = 0
          have h_cayham : aeval lm lm.charpoly = 0 := LinearMap.aeval_self_charpoly lm
          -- aeval commutes with algebra hom lmul
          have h_aeval_lmul : aeval lm lm.charpoly =
              Algebra.lmul ℤ R (aeval (u : R) lm.charpoly) :=
            Polynomial.aeval_algHom_apply (Algebra.lmul ℤ R) (u : R) lm.charpoly
          -- Therefore aeval (u:R) lm.charpoly = 0
          have h_aeval_zero : aeval (u : R) lm.charpoly = 0 := by
            -- lmul ℤ R applied to (aeval (u:R) charpoly) equals 0 as a linear map
            have h_key : Algebra.lmul ℤ R (aeval (u : R) lm.charpoly) = 0 :=
              h_aeval_lmul.symm.trans h_cayham
            -- Evaluate both sides at 1 to extract the element equation
            have h1 := LinearMap.congr_fun h_key 1
            simp [Algebra.lmul] at h1
            exact h1
          -- minpoly ℤ (u:R) divides charpoly of lm
          have h_int : IsIntegral ℤ (u : R) := Algebra.IsIntegral.isIntegral _
          have h_dvd : minpoly ℤ (u : R) ∣ lm.charpoly :=
            minpoly.isIntegrallyClosed_dvd h_int h_aeval_zero
          have h_ne : lm.charpoly ≠ 0 := (LinearMap.charpoly_monic lm).ne_zero
          -- charpoly has degree = finrank ℤ R = 2
          have h_deg : lm.charpoly.natDegree = 2 := by
            rw [LinearMap.charpoly_natDegree, NumberField.RingOfIntegers.rank K]
            convert K_degree_2 using 2
            exact Subsingleton.elim _ _
          linarith [Polynomial.natDegree_le_of_dvd h_dvd h_ne]
        omega
      -- For n ≥ 7, φ(n) ≥ 4 > 2, so orderOf u ≤ 6
      have h_le6 : orderOf u ≤ 6 := by
        by_contra h
        push_neg at h
        have hn7 : 7 ≤ orderOf u := h
        have hphi2 : φ (orderOf u) = 2 := by
          have hev := Nat.totient_even (show 2 < orderOf u by omega)
          have hpos := Nat.totient_pos.2 h_pos
          obtain ⟨k, hk⟩ := hev; omega
        have h_primes_le3 : ∀ p, p.Prime → p ∣ orderOf u → p ≤ 3 := by
          intro p hp hpd
          have hdvd := Nat.totient_dvd_of_dvd hpd
          rw [Nat.totient_prime hp, hphi2] at hdvd
          have := Nat.le_of_dvd (by norm_num) hdvd; omega
        have h_no8 : ¬ 8 ∣ orderOf u := fun h8 => by
          have hdvd := Nat.totient_dvd_of_dvd h8
          have h8phi : φ 8 = 4 := by decide
          rw [h8phi, hphi2] at hdvd; omega
        have h_no9 : ¬ 9 ∣ orderOf u := fun h9 => by
          have hdvd := Nat.totient_dvd_of_dvd h9
          have h9phi : φ 9 = 6 := by decide
          rw [h9phi, hphi2] at hdvd; omega
        have h_not_prime : ¬ (orderOf u).Prime := fun hp => by
          have := Nat.totient_prime hp; omega
        have aux : ∀ n' : ℕ, 1 < n' → ¬ 2 ∣ n' → (∀ p, p.Prime → p ∣ n' → p ≤ 3) → 3 ∣ n' := by
          intro n' hn' hodd hle3
          obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n' ≠ 1 by omega)
          have hple3 := hle3 p hp hpn
          have hge2 := hp.two_le
          have hoddp : ¬ 2 ∣ p := fun h2 => hodd (h2.trans hpn)
          have : p = 3 := by omega
          exact this ▸ hpn
        by_cases hn_odd : ¬ 2 ∣ orderOf u
        · have h3n : 3 ∣ orderOf u := aux _ (by omega) hn_odd h_primes_le3
          have hmin3 : (orderOf u).minFac = 3 := by
            have hmp := Nat.minFac_prime (show orderOf u ≠ 1 by omega)
            have hmd := Nat.minFac_dvd (orderOf u)
            have hle3 := h_primes_le3 _ hmp hmd
            have hodd_mf : ¬ 2 ∣ (orderOf u).minFac := fun h => hn_odd (h.trans hmd)
            have hge2 := hmp.two_le
            have hne2 : (orderOf u).minFac ≠ 2 := by
              intro heq; apply hodd_mf; rw [heq]
            omega
          have h9le : 9 ≤ orderOf u := by
            have hsq := Nat.minFac_sq_le_self (show 0 < orderOf u by omega) h_not_prime
            rw [hmin3] at hsq; linarith
          obtain ⟨j, hj⟩ := h3n
          have hn3_dvd : orderOf u / 3 ∣ orderOf u := ⟨3, by omega⟩
          have hn3_gt1 : 1 < orderOf u / 3 := by omega
          have hn3_odd : ¬ 2 ∣ orderOf u / 3 := fun h2 => hn_odd (h2.trans hn3_dvd)
          have hn3_primes : ∀ p, p.Prime → p ∣ orderOf u / 3 → p ≤ 3 :=
            fun p hp hpd => h_primes_le3 p hp (hpd.trans hn3_dvd)
          have h3n3 : 3 ∣ orderOf u / 3 := aux _ hn3_gt1 hn3_odd hn3_primes
          obtain ⟨k, hk⟩ := h3n3
          exact h_no9 ⟨k, by omega⟩
        · push_neg at hn_odd
          have hn2_dvd : orderOf u / 2 ∣ orderOf u := by
            obtain ⟨j, hj⟩ := hn_odd; exact ⟨2, by omega⟩
          have hn2_gt1 : 1 < orderOf u / 2 := by omega
          have hn2_primes : ∀ p, p.Prime → p ∣ orderOf u / 2 → p ≤ 3 :=
            fun p hp hpd => h_primes_le3 p hp (hpd.trans hn2_dvd)
          by_cases h3n : 3 ∣ orderOf u
          · obtain ⟨m, hm⟩ := h3n
            obtain ⟨j, hj⟩ := hn_odd
            have hn12 : 12 ≤ orderOf u := by omega
            have hn3_dvd : orderOf u / 3 ∣ orderOf u := ⟨3, by omega⟩
            have hn3_gt1 : 1 < orderOf u / 3 := by omega
            have hm_even : 2 ∣ m := ⟨j / 3, by omega⟩
            have hn3_even : 2 ∣ orderOf u / 3 := by
              have heq : orderOf u / 3 = m := by omega
              rw [heq]; exact hm_even
            have hn3_primes : ∀ p, p.Prime → p ∣ orderOf u / 3 → p ≤ 3 :=
              fun p hp hpd => h_primes_le3 p hp (hpd.trans hn3_dvd)
            by_cases h3n3 : 3 ∣ orderOf u / 3
            · obtain ⟨k, hk⟩ := h3n3
              exact h_no9 ⟨k, by omega⟩
            · obtain ⟨j2, hj2⟩ := hn3_even
              have hn3_eq_m : orderOf u / 3 = m := by omega
              have hn6_dvd : orderOf u / 6 ∣ orderOf u / 3 := ⟨2, by omega⟩
              have hn6_dvd_n : orderOf u / 6 ∣ orderOf u := hn6_dvd.trans hn3_dvd
              have hn6_gt1 : 1 < orderOf u / 6 := by omega
              have hn6_primes : ∀ p, p.Prime → p ∣ orderOf u / 6 → p ≤ 3 :=
                fun p hp hpd => h_primes_le3 p hp (hpd.trans hn6_dvd_n)
              have hn6_not3 : ¬ 3 ∣ orderOf u / 6 := fun h36 => h3n3 (h36.trans hn6_dvd)
              have h2n6 : 2 ∣ orderOf u / 6 := by
                by_contra hodd6
                exact hn6_not3 (aux _ hn6_gt1 hodd6 hn6_primes)
              obtain ⟨k, hk⟩ := h2n6
              have h12n : 12 ∣ orderOf u := ⟨k, by omega⟩
              have h12phi : φ 12 = 4 := by decide
              have hdvd12 := Nat.totient_dvd_of_dvd h12n
              rw [h12phi, hphi2] at hdvd12; omega
          · have h2n2_not3 : ¬ 3 ∣ orderOf u / 2 := fun h => h3n (h.trans hn2_dvd)
            have h4n : 4 ∣ orderOf u := by
              have h2n2 : 2 ∣ orderOf u / 2 := by
                by_contra hodd2
                exact h2n2_not3 (aux _ hn2_gt1 hodd2 hn2_primes)
              obtain ⟨j, hj⟩ := hn_odd; obtain ⟨k, hk⟩ := h2n2
              exact ⟨k, by omega⟩
            have hn4_dvd : orderOf u / 4 ∣ orderOf u := by
              obtain ⟨j, hj⟩ := h4n; exact ⟨4, by omega⟩
            have hn4_gt1 : 1 < orderOf u / 4 := by omega
            have hn4_primes : ∀ p, p.Prime → p ∣ orderOf u / 4 → p ≤ 3 :=
              fun p hp hpd => h_primes_le3 p hp (hpd.trans hn4_dvd)
            have h4n_not3 : ¬ 3 ∣ orderOf u / 4 := fun h => h3n (h.trans hn4_dvd)
            have h8n : 8 ∣ orderOf u := by
              have h2n4 : 2 ∣ orderOf u / 4 := by
                by_contra hodd4
                exact h4n_not3 (aux _ hn4_gt1 hodd4 hn4_primes)
              obtain ⟨j, hj⟩ := h4n; obtain ⟨k, hk⟩ := h2n4
              exact ⟨k, by omega⟩
            exact h_no8 h8n
      -- K has no cube roots of unity (K ≇ ℚ(ζ₃) = ℚ(√-3), since -7 ≠ -3):
      have hno_cube : ∀ z : R, z ^ 2 + z + 1 ≠ 0 := hno_cube_aux
      -- K has no square root of -1 (K ≇ ℚ(i), since -7 ≠ -4):
      have hno_i : ∀ z : R, z ^ 2 + 1 ≠ 0 := hno_i_aux
      -- Helper: lift u^k = 1 in Rˣ to (↑u : R)^k = 1
      have lift_pow : ∀ k : ℕ, u ^ k = 1 → (u : R) ^ k = 1 := fun k hk => by
        have := congr_arg Units.val hk; simpa using this
      -- Helper: orderOf u = k → (↑u : R) ≠ 1 (for k ≥ 2)
      have ne_one_R : orderOf u ≥ 2 → (u : R) ≠ 1 := fun hk heq => by
        have hU1 : u = 1 := Units.val_inj.mp heq
        simp [hU1, orderOf_one] at hk
      -- Helper: orderOf u = k → (↑u : R)^2 ≠ 1 (for k ∤ 2)
      have sq_ne_one_R : ¬ orderOf u ∣ 2 → (u : R) ^ 2 ≠ 1 := fun hnd heq => by
        have hU2 : u ^ 2 = 1 := Units.val_inj.mp (by simpa using heq)
        exact hnd (orderOf_dvd_iff_pow_eq_one.mpr hU2)
      -- Case analysis: orderOf u ∈ {1, 2, 3, 4, 5, 6}
      have h1 : 1 ≤ orderOf u := h_pos
      interval_cases h : orderOf u
      · norm_num  -- 1 ∣ 2
      · norm_num  -- 2 ∣ 2
      · -- n = 3: (↑u)^2 + (↑u) + 1 = 0 in R, contradicts hno_cube
        exfalso; apply hno_cube (u : R)
        have hR3 : (u : R) ^ 3 = 1 := lift_pow 3 (h ▸ pow_orderOf_eq_one u)
        have hne : (u : R) ≠ 1 := ne_one_R (by omega)
        have fac : ((u : R) - 1) * ((u : R) ^ 2 + (u : R) + 1) = 0 := by
          have eq : ((u : R) - 1) * ((u : R) ^ 2 + (u : R) + 1) = (u : R) ^ 3 - 1 := by ring
          rw [eq, hR3]; ring
        exact (mul_eq_zero.mp fac).resolve_left (sub_ne_zero.mpr hne)
      · -- n = 4: (↑u)^2 + 1 = 0, contradicts hno_i
        exfalso; apply hno_i (u : R)
        have hR4 : (u : R) ^ 4 = 1 := lift_pow 4 (h ▸ pow_orderOf_eq_one u)
        have hne2 : (u : R) ^ 2 ≠ 1 := sq_ne_one_R (by norm_num)
        have fac : ((u : R) ^ 2 - 1) * ((u : R) ^ 2 + 1) = 0 := by
          have eq : ((u : R) ^ 2 - 1) * ((u : R) ^ 2 + 1) = (u : R) ^ 4 - 1 := by ring
          rw [eq, hR4]; ring
        exact (mul_eq_zero.mp fac).resolve_left (sub_ne_zero.mpr hne2)
      · -- n = 5: φ(5) = 4 > 2, contradicts h_totient_le
        exfalso
        have : (5 : ℕ).totient = 4 := by decide
        omega
      · -- n = 6: (↑u)^2 satisfies X^2 + X + 1 = 0, contradicts hno_cube
        exfalso; apply hno_cube ((u : R) ^ 2)
        have hR6 : (u : R) ^ 6 = 1 := lift_pow 6 (h ▸ pow_orderOf_eq_one u)
        have hne2 : (u : R) ^ 2 ≠ 1 := sq_ne_one_R (by norm_num)
        have fac : ((u : R) ^ 2 - 1) * (((u : R) ^ 2) ^ 2 + (u : R) ^ 2 + 1) = 0 := by
          have eq : ((u : R) ^ 2 - 1) * (((u : R) ^ 2) ^ 2 + (u : R) ^ 2 + 1)
                  = (u : R) ^ 6 - 1 := by ring
          rw [eq, hR6]; ring
        exact (mul_eq_zero.mp fac).resolve_left (sub_ne_zero.mpr hne2)
    -- Deduce u^2 = 1 in Rˣ
    have h_sq : u ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h_div2
    -- Lift to R: (↑u : R)^2 = 1
    have h_sq_R : (u : R) ^ 2 = 1 := by
      have : ((u ^ 2 : Rˣ) : R) = ((1 : Rˣ) : R) := congr_arg Units.val h_sq
      simpa using this
    -- In R (integral domain), a^2 = 1 ↔ a = 1 ∨ a = -1
    rcases sq_eq_one_iff.mp h_sq_R with h | h
    · left;  exact Units.val_inj.mp h
    · right; exact Units.val_inj.mp (by simp [h])
  -- Step 2: card(InfinitePlace K) = 1 (since nrRealPlaces = 0, nrComplexPlaces = 1)
  have h_card : Fintype.card (InfinitePlace K) = 1 := by
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces, K_nrRealPlaces_zero, K_nrComplexPlaces_2]
  -- Step 3: unit rank of K is 0
  have h_rank : NumberField.Units.rank K = 0 := by
    simp [NumberField.Units.rank, h_card]
  -- Step 4: apply Dirichlet — every unit = torsion × ∏ fundSystem^eᵢ
  obtain ⟨⟨ζ, e⟩, h_eq, _⟩ := NumberField.Units.exist_unique_eq_mul_prod K u
  -- With rank 0, the index type Fin (rank K) = Fin 0 is empty, so the product collapses to 1
  haveI h_empty : IsEmpty (Fin (NumberField.Units.rank K)) := by
    rw [h_rank]; exact inferInstance
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at h_eq
  -- h_eq : u = ↑ζ, and ζ ∈ torsion K by construction
  exact h_eq ▸ ζ.prop

lemma class_number_one_PID : IsPrincipalIdealRing R := by
  apply isPrincipalIdealRing_of_abs_discr_lt
  simp only [K_nrComplexPlaces_2, K_discriminant]
  have h_alg : (QuadraticAlgebra.instAlgebra : Algebra ℚ K) = DivisionRing.toRatAlgebra :=
    Subsingleton.elim _ _
  have h2 : @Module.finrank ℚ K _ _ DivisionRing.toRatAlgebra.toModule = 2 := by
    rw [← h_alg]; exact K_degree_2
  rw [h2]; norm_num [Nat.factorial]
  -- 7 < π²; since π > 3, π² > 9 > 7
  nlinarith [Real.pi_gt_three]

lemma class_number_one : UniqueFactorizationMonoid R :=
  haveI := class_number_one_PID
  inferInstance

-- The Algebra.norm on a QuadraticAlgebra coincides with the QuadraticAlgebra.norm
lemma algebra_norm_eq_quadratic_norm (z : K) : Algebra.norm ℚ z = QuadraticAlgebra.norm z := by
  have h_alg : (QuadraticAlgebra.instAlgebra : Algebra ℚ K) = DivisionRing.toRatAlgebra :=
    Subsingleton.elim _ _
  have : @Algebra.norm ℚ K _ _ DivisionRing.toRatAlgebra z =
      @Algebra.norm ℚ K _ _ QuadraticAlgebra.instAlgebra z := by
    rw [h_alg]
  rw [this]
  rw [@Algebra.norm_apply ℚ K _ _ QuadraticAlgebra.instAlgebra]
  rw [← QuadraticAlgebra.det_toLinearMap_eq_norm]
  congr 1

lemma exponent : exponent θ = 1 := by
  rw [exponent_eq_one_iff, span_eq_top]

lemma ne_dvd_exponent (p : ℕ) [hp : Fact p.Prime] : ¬ (p ∣ RingOfIntegers.exponent θ) := by
  rw [exponent, dvd_one]
  exact hp.1.ne_one

lemma two_factorisation_R : θ * (1 - θ) = 2 := by
-- Strip the subtype wrapper to check equality in the field K
  apply Subtype.ext
  -- Push the coercion through multiplication, subtraction, and numerals
  push_cast
  show (ω : K) * (1 - ω) = 2
  calc
    ω * ((1 : K) - ω) = ω - ω ^ 2 := by ring
    _ = ω - (-2 + ω) := by
      rw [pow_two, omega_mul_omega_eq_mk]
      ext <;> simp
    _ = 2 := by ring


-- Local helper: Algebra.norm is a unit iff the element is a unit
lemma norm_isUnit_iff (x : 𝓞 K) : IsUnit (Algebra.norm ℤ x) ↔ IsUnit x := by
  constructor <;> intro h <;> contrapose! h;
  · -- By definition of norm, if $x$ is not a unit, then its norm $N(x)$ is not a unit in $\mathbb{Z}$.
    have h_norm_not_unit : ∀ y : 𝓞 K, ¬IsUnit y → ¬IsUnit (Algebra.norm ℤ y) := by
      intro y hy; intro H; have := H.exists_left_inv; obtain ⟨ z, hz ⟩ := this; simp_all +decide [ Algebra.norm ] ;
      -- Since $y$ is not a unit, the linear map $mul y$ is not invertible, hence its determinant is zero.
      have h_det_zero : ¬IsUnit (LinearMap.mul ℤ (𝓞 K) y) := by
        intro h_inv
        have h_inv_mul : ∃ z : 𝓞 K, y * z = 1 := by
          obtain ⟨ z, hz ⟩ := h_inv.exists_right_inv;
          exact ⟨ z 1, by simpa using congr_arg ( fun f => f 1 ) hz ⟩;
        exact hy (isUnit_iff_exists_inv.mpr h_inv_mul)
      apply h_det_zero;
      exact (LinearMap.isUnit_iff_isUnit_det ((LinearMap.mul ℤ (𝓞 K)) y)).mpr H;
    exact h_norm_not_unit x h;
  · contrapose! h with hx;
    exact IsUnit.map (Algebra.norm ℤ) hx

-- Local lemma equating the norm to the constant term of the minimal polynomial (up to sign)
lemma norm_eq_coeff_zero_minpoly (x : 𝓞 K) (h_deg : (minpoly ℤ x).natDegree = 2) :
    Algebra.norm ℤ x = (-1) ^ (minpoly ℤ x).natDegree * (minpoly ℤ x).coeff 0 := by
  -- By definition of minimal polynomial, we know that its degree is 2.
  have h_deg : (minpoly ℤ x).degree = 2 := by
    rw [ Polynomial.degree_eq_natDegree ] <;> aesop;
  -- Since $x$ is an algebraic integer, its minimal polynomial is monic and has integer coefficients.
  have h_minpoly_monic : (minpoly ℤ x).Monic := by
    exact minpoly.monic ( show IsIntegral ℤ x from by exact isIntegral x );
  -- Since $x$ is an algebraic integer, its minimal polynomial is monic and has integer coefficients. Therefore, the characteristic polynomial of $x$ is equal to its minimal polynomial.
  have h_charpoly_eq_minpoly : (LinearMap.charpoly (LinearMap.mulLeft ℤ x)) = (minpoly ℤ x) := by
    have h_charpoly_eq_minpoly : (LinearMap.charpoly (LinearMap.mulLeft ℤ x)).degree = 2 := by
      have h_charpoly_eq_minpoly : (LinearMap.charpoly (LinearMap.mulLeft ℤ x)).degree = Module.finrank ℤ (𝓞 K) := by
        rw [ LinearMap.charpoly ];
        rw [ Matrix.charpoly_degree_eq_dim ];
        rw [ Module.finrank_eq_card_basis ( Module.Free.chooseBasis ℤ (𝓞 K) ) ];
      have h_charpoly_eq_minpoly : Module.finrank ℤ (𝓞 K) = Module.finrank ℚ K := by
        exact Eq.symm (IsAlgebraic.finrank_of_isFractionRing ℤ ℚ (𝓞 K) K)
      have h_charpoly_eq_minpoly : Module.finrank ℚ K = Polynomial.natDegree f_minpoly := by
        rw [QuadraticAlgebra.finrank_eq_two]
        simp +decide [f_minpoly, Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      simp_all +decide [ f_minpoly ];
      norm_num [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ];
    have h_charpoly_eq_minpoly : (minpoly ℤ x) ∣ (LinearMap.charpoly (LinearMap.mulLeft ℤ x)) := by
      refine' minpoly.isIntegrallyClosed_dvd _ _;
      · exact isIntegral x;
      · have := LinearMap.aeval_self_charpoly ( LinearMap.mulLeft ℤ x );
        convert congr_arg ( fun f => f 1 ) this using 1;
        simp +decide [ Polynomial.aeval_eq_sum_range ];
    obtain ⟨ q, hq ⟩ := h_charpoly_eq_minpoly;
    have hq_monic : q.Monic := by
      have hq_monic : Polynomial.Monic (LinearMap.charpoly (LinearMap.mulLeft ℤ x)) := by
        convert LinearMap.charpoly_monic ( LinearMap.mulLeft ℤ x );
      rw [ hq, Polynomial.Monic.def, Polynomial.leadingCoeff_mul ] at hq_monic ; aesop;
    have hq_one : q.degree = 0 := by
      have := congr_arg Polynomial.degree hq; rw [ Polynomial.degree_mul, h_charpoly_eq_minpoly, h_deg ] at this; rw [ Polynomial.degree_eq_natDegree hq_monic.ne_zero ] at *; norm_cast at *; linarith;
    rw [ Polynomial.degree_eq_natDegree ] at hq_one <;> aesop;
  have h_det_eq_charpoly : ∀ (f : Module.End ℤ (𝓞 K)), f.charpoly.coeff 0 = (-1) ^ (Module.finrank ℤ (𝓞 K)) * LinearMap.det f := by
    intro f; rw [ LinearMap.det_eq_sign_charpoly_coeff ] ; ring;
    norm_num [ pow_mul' ];
  have h_finrank : Module.finrank ℤ (𝓞 K) = 2 := by
    have := Eq.symm (IsAlgebraic.finrank_of_isFractionRing ℤ ℚ (𝓞 K) K)
    rw [QuadraticAlgebra.finrank_eq_two] at this
    exact this
  specialize h_det_eq_charpoly ( LinearMap.mulLeft ℤ x ) ; aesop;

/-! ## Facts about θ

blah

-/

lemma norm_theta_eq_two : Algebra.norm ℤ θ = 2 := by
  -- The norm is related to the constant coefficient of the minimal polynomial.
  -- Formula: N(x) = (-1)^(n) * a_0
  have h_deg : (minpoly ℤ θ).natDegree = 2 := by
      rw [my_minpoly]
      compute_degree
      exact Int.one_ne_zero
  erw [norm_eq_coeff_zero_minpoly θ h_deg]
  rw [my_minpoly]
  have h_deg : (X ^ 2 - X + 2 : Polynomial ℤ).natDegree = 2 := by
    compute_degree
    exact Int.one_ne_zero
  rw [h_deg]
  simp

lemma norm_theta_prime_eq_two : Algebra.norm ℤ θ' = 2 := by
  -- The norm is related to the constant coefficient of the minimal polynomial.
  -- Formula: N(x) = (-1)^(n) * a_0
  have h_deg : (minpoly ℤ θ').natDegree = 2 := by
      rw [my_minpoly_theta_prime]
      compute_degree
      exact Int.one_ne_zero
  erw [norm_eq_coeff_zero_minpoly θ' h_deg]
  rw [my_minpoly_theta_prime]
  have h_deg : (X ^ 2 - X + 2 : Polynomial ℤ).natDegree = 2 := by
    compute_degree
    exact Int.one_ne_zero
  rw [h_deg]
  simp

lemma theta_not_unit : ¬ IsUnit θ := by
  intro h_unit
  -- Apply the norm to the unit hypothesis
  -- (Units map to Units under Monoid Homomorphisms like norm)
  have h_norm_unit := IsUnit.map (Algebra.norm ℤ) h_unit
  -- Substitute the known norm value
  rw [norm_theta_eq_two] at h_norm_unit
  -- Contradiction: 2 is not a unit in ℤ (±1)
  contradiction

lemma theta_prime_not_unit : ¬ IsUnit θ' := by
  intro h_unit
  -- Apply the norm to the unit hypothesis
  -- (Units map to Units under Monoid Homomorphisms like norm)
  have h_norm_unit := IsUnit.map (Algebra.norm ℤ) h_unit
  -- Substitute the known norm value
  rw [norm_theta_prime_eq_two] at h_norm_unit
  -- Contradiction: 2 is not a unit in ℤ (±1)
  contradiction

/-- Exercise 3: In the UFD R, if α · β = θ^m · θ'^m and gcd(α, β) = 1, then
    α = ±θ^m or α = ±θ'^m. This combines two steps: (1) unique factorization
    (`class_number_one`) implies α is associate to θ^m or θ'^m, and (2) the only
    units are ±1 (`units_pm_one`), pinning down the sign. -/
-- θ is irreducible in R
lemma theta_irreducible : Irreducible θ := by
  -- Use the definition of irreducibility
  rw [irreducible_iff]
  constructor
  · -- Show θ is not a unit
    exact theta_not_unit
  · -- Show any factorization includes a unit
    intro a b h_factor
    -- Apply norm to the factorization: N(θ) = N(a) * N(b)
    have h_norm_factor : Algebra.norm ℤ θ = Algebra.norm ℤ (a * b) := by rw [h_factor]
    rw [MonoidHom.map_mul, norm_theta_eq_two] at h_norm_factor
    -- We have 2 = N(a) * N(b) in ℤ.
    -- Since 2 is irreducible in ℤ, one factor must be a unit.
    have h_prime_two : Irreducible (2 : ℤ) := Int.prime_two.irreducible
    -- Irreducible definition in ℤ: a * b = p → IsUnit a ∨ IsUnit b
    have h_units_Z : IsUnit (Algebra.norm ℤ a) ∨ IsUnit (Algebra.norm ℤ b) :=
      h_prime_two.isUnit_or_isUnit h_norm_factor
    -- Convert back to units in R
    exact h_units_Z.imp (norm_isUnit_iff a).mp (norm_isUnit_iff b).mp

-- θ' is irreducible in R
lemma theta'_irreducible : Irreducible θ' := by
  -- Use the definition of irreducibility
  rw [irreducible_iff]
  constructor
  · -- Show θ is not a unit
    exact theta_prime_not_unit
  · -- Show any factorization includes a unit
    intro a b h_factor
    -- Apply norm to the factorization: N(θ) = N(a) * N(b)
    have h_norm_factor : Algebra.norm ℤ θ' = Algebra.norm ℤ (a * b) := by rw [h_factor]
    rw [MonoidHom.map_mul, norm_theta_prime_eq_two] at h_norm_factor
    -- We have 2 = N(a) * N(b) in ℤ.
    -- Since 2 is irreducible in ℤ, one factor must be a unit.
    have h_prime_two : Irreducible (2 : ℤ) := Int.prime_two.irreducible
    -- Irreducible definition in ℤ: a * b = p → IsUnit a ∨ IsUnit b
    have h_units_Z : IsUnit (Algebra.norm ℤ a) ∨ IsUnit (Algebra.norm ℤ b) :=
      h_prime_two.isUnit_or_isUnit h_norm_factor
    -- Convert back to units in R
    exact h_units_Z.imp (norm_isUnit_iff a).mp (norm_isUnit_iff b).mp

-- θ and θ' are not associated (they are distinct primes up to units)
lemma theta_theta'_not_associated : ¬ Associated θ θ' := by
  intro h
  -- Definition of Associated: θ = θ' * u for some unit u
  rcases h with ⟨u, hu⟩
  -- The only units are 1 and -1
  rcases units_pm_one u with rfl | rfl
  · -- Case u = 1
    simp only [Units.val_one, mul_one] at hu
    -- Move to K to compare coefficients
    apply_fun ((↑) : R → K) at hu
    -- Simplify the components (θ is ω, θ' is 1-ω)
    dsimp at hu
    -- Compare real and imaginary parts
    rw [QuadraticAlgebra.ext_iff] at hu
    -- 0 = 1 is False
    simp at hu
  · -- Case u = -1
    simp only [Units.val_neg, Units.val_one, mul_neg, mul_one] at hu
    apply_fun ((↑) : R → K) at hu
    dsimp at hu
    -- -θ' = -(1 - ω) = -1 + ω
    -- ω = -1 + ω implies 0 = -1
    rw [QuadraticAlgebra.ext_iff] at hu
    simp at hu

-- Skeleton sub-lemmas for ufd_associated_dichotomy

-- θ does not divide θ' (they are non-associated irreducibles)
lemma theta_not_dvd_theta' : ¬ (θ ∣ θ') := by
  intro h
  exact theta_theta'_not_associated (theta_irreducible.associated_of_dvd theta'_irreducible h)

-- θ' does not divide θ
lemma theta'_not_dvd_theta : ¬ (θ' ∣ θ) := by
  intro h
  exact theta_theta'_not_associated (theta'_irreducible.associated_of_dvd theta_irreducible h).symm

-- In a coprime factorization α * β = θ^m * θ'^m, the prime power θ^m
-- divides one of the coprime factors.
-- Proof idea: by induction on m, using Prime.dvd_or_dvd and coprimality
-- to force each copy of θ to the same side.
lemma theta_pow_dvd_of_coprime_prod (α β : R) (m : ℕ)
    (h_prod : α * β = θ ^ m * θ' ^ m)
    (h_coprime : IsCoprime α β) :
    θ ^ m ∣ α ∨ θ ^ m ∣ β := by
  haveI := class_number_one
  -- Trivial case: m = 0
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact Or.inl (one_dvd α)
  have hθ_prime : _root_.Prime θ :=
    @Irreducible.prime R _ (UniqueFactorizationMonoid.instDecompositionMonoid) θ theta_irreducible
  -- θ^m divides α * β
  have h_dvd_prod : θ ^ m ∣ α * β := h_prod ▸ dvd_mul_right (θ ^ m) (θ' ^ m)
  -- θ divides α or θ divides β (since θ is prime and θ ∣ θ^m ∣ α*β)
  have h_dvd_or : θ ∣ α ∨ θ ∣ β :=
    hθ_prime.dvd_or_dvd (dvd_trans (dvd_pow_self θ (by omega)) h_dvd_prod)
  -- Case split: whichever side θ divides, coprimality forces ¬(θ ∣ other side),
  -- then Prime.pow_dvd_of_dvd_mul_right/left upgrades to θ^m
  rcases h_dvd_or with h_dvd_α | h_dvd_β
  · -- θ ∣ α, so ¬(θ ∣ β) by coprimality
    have h_not_dvd_β : ¬ (θ ∣ β) := fun h_dvd_β =>
      hθ_prime.not_unit (h_coprime.isUnit_of_dvd' h_dvd_α h_dvd_β)
    exact Or.inl (hθ_prime.pow_dvd_of_dvd_mul_right m h_not_dvd_β h_dvd_prod)
  · -- θ ∣ β, so ¬(θ ∣ α) by coprimality
    have h_not_dvd_α : ¬ (θ ∣ α) := fun h_dvd_α =>
      hθ_prime.not_unit (h_coprime.isUnit_of_dvd' h_dvd_α h_dvd_β)
    exact Or.inr (hθ_prime.pow_dvd_of_dvd_mul_left m h_not_dvd_α h_dvd_prod)

-- If θ^m ∣ α and α * β = θ^m * θ'^m with coprime α, β, then α is
-- associated to θ^m.
-- Proof idea: write α = θ^m * γ, cancel to get γ * β = θ'^m. Since
-- IsCoprime α β and θ' is prime, ¬(θ' ∣ γ), so γ is a unit (its only
-- prime factors could be θ or θ', but θ ∤ θ'^m and ¬(θ' ∣ γ)).
lemma associated_of_theta_pow_dvd (α β : R) (m : ℕ)
    (h_prod : α * β = θ ^ m * θ' ^ m)
    (h_coprime : IsCoprime α β)
    (hα : ¬IsUnit α) (hβ : ¬IsUnit β)
    (h_dvd : θ ^ m ∣ α) :
    Associated α (θ ^ m) := by
  haveI := class_number_one
  -- Extract γ from divisibility: α = θ^m * γ
  obtain ⟨γ : R, hγ⟩ := h_dvd
  -- Cancel θ^m to get γ * β = θ'^m
  have hθm_ne : θ ^ m ≠ 0 := pow_ne_zero m (Irreducible.ne_zero theta_irreducible)
  have hθ'm_ne : θ' ^ m ≠ 0 := pow_ne_zero m (Irreducible.ne_zero theta'_irreducible)
  have h_cancel : γ * β = θ' ^ m := by
    have h1 := h_prod
    rw [hγ, mul_assoc] at h1
    exact mul_left_cancel₀ hθm_ne h1
  -- θ' is prime
  have hθ'_prime : _root_.Prime θ' :=
    @Irreducible.prime R _ (UniqueFactorizationMonoid.instDecompositionMonoid) θ' theta'_irreducible
  -- Show θ' does not divide γ
  have h_not_dvd_γ : ¬ (θ' ∣ γ) := by
    intro h_dvd_γ
    -- If θ' ∣ γ, then θ' ∣ α (since α = θ^m * γ)
    have h_dvd_α : θ' ∣ α := hγ ▸ dvd_mul_of_dvd_right h_dvd_γ (θ ^ m)
    -- From coprimality, ¬(θ' ∣ β)
    have h_not_dvd_β : ¬ (θ' ∣ β) := fun h_dvd_β =>
      hθ'_prime.not_unit (h_coprime.isUnit_of_dvd' h_dvd_α h_dvd_β)
    -- From γ * β = θ'^m and ¬(θ' ∣ β), get θ'^m ∣ γ
    have h_dvd_prod : θ' ^ m ∣ γ * β := h_cancel ▸ dvd_refl (θ' ^ m)
    have h_θ'_pow_dvd_γ : θ' ^ m ∣ γ :=
      hθ'_prime.pow_dvd_of_dvd_mul_right m h_not_dvd_β h_dvd_prod
    -- Write γ = θ'^m * δ, cancel to get δ * β = 1
    obtain ⟨δ : R, hδ⟩ := h_θ'_pow_dvd_γ
    have h_eq := h_cancel
    rw [hδ, mul_assoc] at h_eq
    -- h_eq : θ'^m * (δ * β) = θ'^m, so δ * β = 1
    have h_δβ : δ * β = 1 := by
      conv at h_eq => rhs; rw [← mul_one (θ' ^ m)]
      exact mul_left_cancel₀ hθ'm_ne h_eq
    -- So β is a unit, contradiction
    exact hβ (IsUnit.of_mul_eq_one δ (by rw [mul_comm]; exact h_δβ))
  -- So θ'^m ∣ β (from γ * β = θ'^m and ¬(θ' ∣ γ))
  have h_dvd_prod : θ' ^ m ∣ γ * β := h_cancel ▸ dvd_refl (θ' ^ m)
  have h_θ'_dvd_β : θ' ^ m ∣ β :=
    hθ'_prime.pow_dvd_of_dvd_mul_left m h_not_dvd_γ h_dvd_prod
  -- Get β = θ'^m * ε, cancel to get γ * ε = 1
  obtain ⟨ε : R, hε⟩ := h_θ'_dvd_β
  have h_eq := h_cancel
  rw [hε, ← mul_assoc, mul_comm γ (θ' ^ m), mul_assoc] at h_eq
  -- h_eq : θ'^m * (γ * ε) = θ'^m, so γ * ε = 1
  have h_γε : γ * ε = 1 := by
    conv at h_eq => rhs; rw [← mul_one (θ' ^ m)]
    exact mul_left_cancel₀ hθ'm_ne h_eq
  -- γ is a unit
  have hγ_unit : IsUnit γ := IsUnit.of_mul_eq_one ε h_γε
  -- Conclude Associated α (θ^m)
  rw [hγ]
  exact associated_mul_unit_left (θ ^ m) γ hγ_unit

-- Symmetric version: if θ^m ∣ β instead, then α is associated to θ'^m.
-- Proof idea: cancelling θ^m from β gives α * δ = θ'^m, then a symmetric
-- argument (using ¬(θ ∣ α) from coprimality) shows α ~ θ'^m.
lemma associated_of_theta_pow_dvd_right (α β : R) (m : ℕ)
    (h_prod : α * β = θ ^ m * θ' ^ m)
    (h_coprime : IsCoprime α β)
    (hα : ¬IsUnit α) (hβ : ¬IsUnit β)
    (h_dvd : θ ^ m ∣ β) :
    Associated α (θ' ^ m) := by
  haveI := class_number_one
  -- Extract γ from divisibility: β = θ^m * γ
  obtain ⟨γ : R, hγ⟩ := h_dvd
  have hθm_ne : θ ^ m ≠ 0 := pow_ne_zero m (Irreducible.ne_zero theta_irreducible)
  have hθ'm_ne : θ' ^ m ≠ 0 := pow_ne_zero m (Irreducible.ne_zero theta'_irreducible)
  -- Cancel θ^m to get α * γ = θ'^m
  have h_cancel : α * γ = θ' ^ m := by
    have h1 := h_prod
    rw [hγ, ← mul_assoc, mul_comm α (θ ^ m), mul_assoc] at h1
    exact mul_left_cancel₀ hθm_ne h1
  -- θ' is prime
  have hθ'_prime : _root_.Prime θ' :=
    @Irreducible.prime R _ (UniqueFactorizationMonoid.instDecompositionMonoid) θ' theta'_irreducible
  -- Show θ' does not divide γ
  have h_not_dvd_γ : ¬ (θ' ∣ γ) := by
    intro h_dvd_γ
    -- If θ' ∣ γ, then θ' ∣ β
    have h_dvd_β : θ' ∣ β := hγ ▸ dvd_mul_of_dvd_right h_dvd_γ (θ ^ m)
    -- From α * γ = θ'^m, θ' divides α * γ, so θ' ∣ α or θ' ∣ γ
    -- If θ' ∣ α, coprimality gives θ' unit, contradiction
    have h_not_dvd_α : ¬ (θ' ∣ α) := fun h_dvd_α =>
      hθ'_prime.not_unit (h_coprime.isUnit_of_dvd' h_dvd_α h_dvd_β)
    -- From α * γ = θ'^m and ¬(θ' ∣ α), get θ'^m ∣ γ
    have h_dvd_prod : θ' ^ m ∣ α * γ := h_cancel ▸ dvd_refl (θ' ^ m)
    have h_θ'_pow_dvd_γ : θ' ^ m ∣ γ :=
      hθ'_prime.pow_dvd_of_dvd_mul_left m h_not_dvd_α h_dvd_prod
    -- Write γ = θ'^m * δ, cancel to get α * δ = 1
    obtain ⟨δ : R, hδ⟩ := h_θ'_pow_dvd_γ
    have h_eq := h_cancel
    rw [hδ, ← mul_assoc, mul_comm α (θ' ^ m), mul_assoc] at h_eq
    have h_αδ : α * δ = 1 := by
      conv at h_eq => rhs; rw [← mul_one (θ' ^ m)]
      exact mul_left_cancel₀ hθ'm_ne h_eq
    -- So α is a unit, contradiction
    exact hα (IsUnit.of_mul_eq_one δ h_αδ)
  -- So θ'^m ∣ α (from α * γ = θ'^m and ¬(θ' ∣ γ))
  have h_dvd_prod : θ' ^ m ∣ α * γ := h_cancel ▸ dvd_refl (θ' ^ m)
  have h_θ'_dvd_α : θ' ^ m ∣ α :=
    hθ'_prime.pow_dvd_of_dvd_mul_right m h_not_dvd_γ h_dvd_prod
  -- Get α = θ'^m * ε, cancel to get ε * γ = 1
  obtain ⟨ε : R, hε⟩ := h_θ'_dvd_α
  have h_eq := h_cancel
  rw [hε, mul_assoc] at h_eq
  have h_εγ : ε * γ = 1 := by
    conv at h_eq => rhs; rw [← mul_one (θ' ^ m)]
    exact mul_left_cancel₀ hθ'm_ne h_eq
  -- ε is a unit
  have hε_unit : IsUnit ε := IsUnit.of_mul_eq_one γ h_εγ
  -- Conclude Associated α (θ'^m)
  rw [hε]
  exact associated_mul_unit_left (θ' ^ m) ε hε_unit

-- Step 1: In the UFD R, coprimality and the product equation force α to be
-- associated to θ^m or to θ'^m.
lemma ufd_associated_dichotomy (α β : R) (m : ℕ)
    (h_prod : α * β = θ ^ m * θ' ^ m)
    (h_coprime : IsCoprime α β)
    (hα : ¬IsUnit α) (hβ : ¬IsUnit β) :
    Associated α (θ ^ m) ∨ Associated α (θ' ^ m) := by
  haveI := class_number_one
  rcases theta_pow_dvd_of_coprime_prod α β m h_prod h_coprime with h | h
  · exact Or.inl (associated_of_theta_pow_dvd α β m h_prod h_coprime hα hβ h)
  · exact Or.inr (associated_of_theta_pow_dvd_right α β m h_prod h_coprime hα hβ h)

-- Step 2: If α is associated to some γ in R, then α = u * γ for some unit u,
-- and the only units in R are ±1, so α = γ or α = -γ.
lemma associated_eq_or_neg (α γ : R) (h : Associated α γ) :
    α = γ ∨ α = -γ := by
  -- Unpack the definition of Associated: γ = α * u (or α = γ * u)
  rcases h with ⟨u, rfl⟩
  -- Split into cases where the unit u is 1 or -1
  rcases units_pm_one u with rfl | rfl
  · -- Case u = 1: α * 1 = α
    left
    simp
  · -- Case u = -1: α * -1 = -α
    right
    simp

lemma ufd_power_association (α β : R) (m : ℕ)
    (h_prod : α * β = θ ^ m * θ' ^ m)
    (h_coprime : IsCoprime α β)
    (hα : ¬IsUnit α) (hβ : ¬IsUnit β) :
    (α = θ ^ m ∨ α = -(θ ^ m)) ∨ (α = θ' ^ m ∨ α = -(θ' ^ m)) := by
  haveI := class_number_one
  -- Step 1: α is associated to θ^m or θ'^m
  have h_assoc := ufd_associated_dichotomy α β m h_prod h_coprime hα hβ
  -- Step 2: pin down the sign using units_pm_one
  rcases h_assoc with h_left | h_right
  · left; exact associated_eq_or_neg α (θ ^ m) h_left
  · right; exact associated_eq_or_neg α (θ' ^ m) h_right
