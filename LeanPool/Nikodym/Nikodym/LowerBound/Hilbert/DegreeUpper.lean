/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import Mathlib.Algebra.MvPolynomial.Funext
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.FreeFiber
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.GradedNorm
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Homogenization
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.LinearNormalization

/-!
# Uniform Hilbert bounds from the generic rank (node A08-core)

Let `I ⊆ P = K[X₁, …, X_d]` be a prime ideal over an infinite field, `k := quotDim I`,
`J := homogenization I ⊆ Q = K[X₀, …, X_d]` (a homogeneous prime with `quotDim J = k + 1`, node A05)
and `R := Q ⧸ J`. A linear Noether normalization (node A02) makes `R` a finite faithful module over
`S := K[Y₀, …, Y_k]` through homogeneous linear forms `y`; node A06′ provides `S`-linearly
independent homogeneous elements `r : Fin Δ → R` of degrees `e` whose images form a
`Frac S`-basis of `Frac R` (`Δ` is the generic rank), and a conductor `c ≠ 0` with
`c • R ⊆ M := span S (range r)`. This file proves the two bounds on the Hilbert function
`hilbert I t = homHilbert J t = dim_K R_t` (`R_t` the image of the forms of degree `t`):

* **lower bound** (`sum_choose_le_homHilbert`, node A04′'s `sum_choose_le_hilbert`): the map
  `⨁_{i : e i ≤ t} S_{t - e i} → R_t`, `(p i) ↦ ∑ p i • r i`, is injective, so
  `∑_{i : e i ≤ t} (t - e i + k).choose k ≤ hilbert I t`;
* **upper bound** (`homHilbert_le_rank_mul_choose`, steps 1–6 of the design note): choosing a point
  `a ∈ K^k` with `c(1, a) ≠ 0`, the *fiber map* `Φ : R_t → (Fin Δ → K[Y₁, …, Y_k] ⧸ 𝔪ₐ ^ (t + 1))`,
  `F ↦ (coordinates of c • F in the basis r, dehomogenized, mod 𝔪ₐ ^ (t + 1))` is `K`-linear and
  injective, whence `hilbert I t ≤ Δ * (t + k).choose k`. Injectivity: if `Φ F = 0`, the matrix
  `A` of multiplication by `c² F` on `M` has entries in `𝔮 := dehom⁻¹(𝔪ₐ ^ (t + 1))`, so
  `A.det ∈ 𝔮 ^ Δ` (`det_mem_pow_of_forall_mem`); but `A.det = c ^ (2Δ) · N(F)` where
  `N(F) ∈ S` is the norm of `F`, a form of degree `t Δ` (node A07′, `algebraMap_det_eq_norm`);
  by primality of `𝔪ₐ ^ ((t + 1) Δ)` the dehomogenization of `N(F)` lies in `𝔪ₐ ^ ((t + 1) Δ)`
  while having total degree `≤ t Δ`, so `N(F) = 0` (`eq_zero_of_mul_mem_comap_pow`), hence
  `A.det = 0`, hence `c² F = 0` and `F = 0` (`eq_zero_of_det_eq_zero`).

The packaged statement consumed by node A04′ is `exists_hilbert_bounds`.

## Implementation notes

* The `Frac S`-algebra structure on `Frac R` is `FractionRing.liftAlgebra` (a local instance, as in
  `FreeFiber.lean`); the shortcut instance `fracModule` makes the search for
  `Module (Frac S) (Frac R)` terminate quickly.
* The lower bound is stated as a sum over `i` with `e i ≤ t`; for `t ≥ max e` this is the full sum
  `∑ i, (t - e i + k).choose k`.
-/

namespace Nikodym.LowerBound

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Generic lemmas -/

section Generic

/-- Node A08 (step 3): **the determinant of a matrix with entries in an ideal `I` lies in
`I ^ Δ`**, `Δ` the size of the matrix. -/
theorem det_mem_pow_of_forall_mem {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {I : Ideal A} {M : Matrix ι ι A} (h : ∀ i j, M i j ∈ I) : M.det ∈ I ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  refine Ideal.sum_mem _ fun σ _ ↦ ?_
  have hprod : ∏ i, M (σ i) i ∈ I ^ Fintype.card ι := by
    have := Ideal.prod_mem_prod (s := Finset.univ) (I := fun _ ↦ I) (x := fun i ↦ M (σ i) i)
      fun i _ ↦ h _ _
    rwa [Finset.prod_const, Finset.card_univ] at this
  rw [Units.smul_def, zsmul_eq_mul]
  exact Ideal.mul_mem_left _ _ hprod

/-- Node A08 (step 6): **a linear relation with a singular matrix forces `u = 0`.** If
`u * r j = ∑ i, A i j • r i` for an `S`-linearly independent family `r` in a domain `R` and
`A.det = 0`, then `u = 0`. -/
theorem eq_zero_of_det_eq_zero {S R : Type*} [CommRing S] [IsDomain S] [CommRing R] [IsDomain R]
    [Algebra S R] {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ι → R}
    (hli : LinearIndependent S r) {u : R} {A : Matrix ι ι S}
    (hA : ∀ j, u * r j = ∑ i, A i j • r i) (hdet : A.det = 0) : u = 0 := by
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hm : ∑ j, v j • r j ≠ 0 := fun h ↦
    hv0 (funext fun j ↦ Fintype.linearIndependent_iff.mp hli v h j)
  have hzero : u * ∑ j, v j • r j = 0 := by
    have hcoord : ∀ i, ∑ j, v j * A i j = 0 := fun i ↦ by
      have := congrFun hv i
      rw [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
      simpa only [mul_comm] using this
    calc u * ∑ j, v j • r j = ∑ j, v j • (u * r j) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ ↦ (mul_smul_comm _ _ _)
      _ = ∑ j, ∑ i, (v j * A i j) • r i := by
          simp_rw [hA, Finset.smul_sum, smul_smul]
      _ = ∑ i, (∑ j, v j * A i j) • r i := by
          rw [Finset.sum_comm]
          simp_rw [Finset.sum_smul]
      _ = 0 := by simp [hcoord]
  exact (mul_eq_zero.mp hzero).resolve_right hm

/-- Node A08 (step 2): the coordinates of an element of `span S (range r)` in the basis
`Module.Basis.span hli`. -/
theorem coe_eq_sum_repr_span_smul {S R : Type*} [Ring S] [AddCommGroup R] [Module S R]
    {ι : Type*} [Fintype ι] {r : ι → R} (hli : LinearIndependent S r)
    (m : Submodule.span S (Set.range r)) :
    (m : R) = ∑ i, (Module.Basis.span hli).repr m i • r i := by
  conv_lhs => rw [← (Module.Basis.span hli).sum_repr m]
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul, Module.Basis.coe_span_apply]

end Generic

/-! ### Norm and determinant -/

section FractionRing

variable {S R : Type*} [CommRing S] [CommRing R] [Algebra S R]
  [Algebra (FractionRing S) (FractionRing R)] [IsScalarTower S (FractionRing S) (FractionRing R)]

/-- Node A08 (step 4): **the determinant of the matrix of `u` is the norm of `u`.** If the images
of `r : ι → R` form a `Frac S`-basis of `Frac R` and `u * r j = ∑ i, A i j • r i`, then
`algebraMap S (Frac S) A.det = Algebra.norm (Frac S) (algebraMap R (Frac R) u)`. (The algebra
structure of `Frac R` over `Frac S` is an instance argument, as in `GradedNorm.lean`; it is
`FractionRing.liftAlgebra` in the application.) -/
theorem algebraMap_det_eq_norm {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ι → R}
    (b : Module.Basis ι (FractionRing S) (FractionRing R))
    (hb : ∀ i, b i = algebraMap R (FractionRing R) (r i)) {u : R} {A : Matrix ι ι S}
    (hA : ∀ j, u * r j = ∑ i, A i j • r i) :
    algebraMap S (FractionRing S) A.det =
      Algebra.norm (FractionRing S) (algebraMap R (FractionRing R) u) := by
  rw [Algebra.norm_eq_matrix_det b, RingHom.map_det]
  congr 1
  ext i j
  have key : algebraMap R (FractionRing R) u * b j =
      ∑ i', algebraMap S (FractionRing S) (A i' j) • b i' := by
    rw [hb, ← map_mul, hA, map_sum]
    refine Finset.sum_congr rfl fun i' _ ↦ ?_
    rw [hb, Algebra.smul_def, map_mul, Algebra.smul_def,
      ← IsScalarTower.algebraMap_apply S R (FractionRing R),
      IsScalarTower.algebraMap_apply S (FractionRing S) (FractionRing R)]
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, key,
    Module.Basis.repr_sum_self]

end FractionRing

/-! ### Point ideals, degrees and dehomogenization -/

section PointIdeal

variable {K : Type*} [Field K] {k : ℕ}

/-- Node A08 (step 5, auxiliary): substituting polynomials of total degree at most one does not
increase the total degree (a local copy of `totalDegree_aeval_le_of_totalDegree_le_one` from
`Algebra/BaseChange.lean`, which cannot be imported here). -/
theorem totalDegree_aeval_le_of_totalDegree_le_one' {f : Fin k → MvPolynomial (Fin k) K}
    (hf : ∀ i, (f i).totalDegree ≤ 1) (g : MvPolynomial (Fin k) K) :
    (aeval f g).totalDegree ≤ g.totalDegree := by
  conv_lhs => rw [g.as_sum]
  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun α hα ↦ ?_)
  rw [aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add, Finsupp.prod]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ ↦
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left (α i) (hf i))).trans ?_
  simp only [mul_one]
  exact le_totalDegree hα

/-- Node A08 (step 5): **a polynomial of total degree `< m` lying in `𝔪ₐ ^ m` is zero**: after
translating the point `a` to the origin, all monomials of an element of `𝔪₀ ^ m` have degree
`≥ m`. -/
theorem eq_zero_of_mem_pointIdeal_pow_of_totalDegree_lt {a : Fin k → K} {m : ℕ}
    {g : MvPolynomial (Fin k) K} (hg : g ∈ pointIdeal a ^ m) (hdeg : g.totalDegree < m) :
    g = 0 := by
  rw [pointIdeal_pow_eq_map, Ideal.mem_map_iff_of_surjective
    (translate a : MvPolynomial (Fin k) K →+* MvPolynomial (Fin k) K) (translate a).surjective]
    at hg
  obtain ⟨g', hg', rfl⟩ := hg
  have hle : g'.totalDegree ≤ (translate a g').totalDegree := by
    have h := totalDegree_aeval_le_of_totalDegree_le_one' (f := fun i ↦ X i + C (a i))
      (fun i ↦ (totalDegree_add _ _).trans
        (max_le (totalDegree_X i).le (by rw [totalDegree_C]; exact Nat.zero_le _)))
      (translate a g')
    rwa [← translate_symm_apply, AlgEquiv.symm_apply_apply] at h
  rw [mem_pow_idealOfVars_iff] at hg'
  have h0 : g' = 0 := by
    by_contra hne
    obtain ⟨α, hα⟩ := Finset.nonempty_iff_ne_empty.mpr (mt support_eq_empty.mp hne)
    have h1 := hg' α hα
    have h2 : α.degree ≤ g'.totalDegree := le_totalDegree hα
    rw [RingHom.coe_coe] at hdeg
    omega
  rw [RingHom.coe_coe, h0, map_zero]

/-- Node A08 (step 4): **`𝔪ₐ ^ m` is `𝔪ₐ`-primary**: if `x * y ∈ 𝔪ₐ ^ m` and `y ∉ 𝔪ₐ`, then
`x ∈ 𝔪ₐ ^ m`. -/
theorem mem_pointIdeal_pow_of_mul_mem {a : Fin k → K} {m : ℕ} (hm : m ≠ 0)
    {x y : MvPolynomial (Fin k) K} (hxy : x * y ∈ pointIdeal a ^ m) (hy : y ∉ pointIdeal a) :
    x ∈ pointIdeal a ^ m := by
  have hrad : (pointIdeal a ^ m).radical = pointIdeal a := by
    rw [Ideal.radical_pow _ hm, (pointIdeal_isPrime a).radical]
  have hprim : (pointIdeal a ^ m).IsPrimary :=
    Ideal.isPrimary_of_isMaximal_radical (by rw [hrad]; exact pointIdeal_isMaximal a)
  rcases (Ideal.isPrimary_iff.mp hprim).2 hxy with h | h
  · exact h
  · exact absurd (hrad ▸ h) hy

/-- Node A08 (step 1): **a nonzero polynomial over an infinite field has a non-root.** -/
theorem exists_eval_ne_zero [Infinite K] {g : MvPolynomial (Fin k) K} (hg : g ≠ 0) :
    ∃ a : Fin k → K, eval a g ≠ 0 := by
  by_contra h
  refine hg (MvPolynomial.funext fun a ↦ ?_)
  rw [map_zero]
  by_contra ha
  exact h ⟨a, ha⟩

/-- Node A08 (step 5): **a form with vanishing dehomogenization is zero**
(`homogenizeTo_dehom`). -/
theorem eq_zero_of_dehom_eq_zero {m : ℕ} {s : MvPolynomial (Fin (k + 1)) K}
    (hs : s.IsHomogeneous m) (h : dehom s = 0) : s = 0 := by
  rw [← homogenizeTo_dehom hs, h, ← homogenizeToₗ_apply, map_zero]

/-- Node A08 (step 5): the dehomogenization of a form of degree `m` has total degree `≤ m`. -/
theorem totalDegree_dehom_le {m : ℕ} {s : MvPolynomial (Fin (k + 1)) K}
    (hs : s.IsHomogeneous m) : (dehom s).totalDegree ≤ m :=
  mem_restrictTotalDegree_iff.mp (dehom_mem_restrictTotalDegree hs)

/-- Node A08 (step 1): **the rational point.** For a nonzero form `c` in `k + 1` variables there
is `a : Fin k → K` with `c (1, a) ≠ 0`, i.e. `dehom c ∉ 𝔪ₐ`. -/
theorem exists_dehom_notMem_pointIdeal [Infinite K] {γ : ℕ} {c : MvPolynomial (Fin (k + 1)) K}
    (hc : c.IsHomogeneous γ) (hc0 : c ≠ 0) : ∃ a : Fin k → K, dehom c ∉ pointIdeal a := by
  have hne : dehom c ≠ 0 := fun h ↦ hc0 (eq_zero_of_dehom_eq_zero hc h)
  obtain ⟨a, ha⟩ := exists_eval_ne_zero hne
  exact ⟨a, fun h ↦ ha (mem_pointIdeal.mp h)⟩

/-- Node A08 (steps 4–5): **the vanishing of the norm.** Let `s` be a form of degree `t * Δ` in
`k + 1` variables, `0 < Δ`, and `c` with `dehom c ∉ 𝔪ₐ`. If `(c * c) ^ Δ * s` lies in the `Δ`-th
power of `𝔮 := dehom⁻¹ (𝔪ₐ ^ (t + 1))`, then `s = 0`: `dehom s ∈ 𝔪ₐ ^ ((t + 1) Δ)` by primality,
while `dehom s` has total degree `≤ t Δ < (t + 1) Δ`. -/
theorem eq_zero_of_mul_mem_comap_pow {t Δ : ℕ} (hΔ : 0 < Δ) {a : Fin k → K}
    {c s : MvPolynomial (Fin (k + 1)) K} (hc : dehom c ∉ pointIdeal a)
    (hs : s.IsHomogeneous (t * Δ))
    (h : (c * c) ^ Δ * s ∈ ((pointIdeal a ^ (t + 1)).comap dehom) ^ Δ) : s = 0 := by
  have h1 : dehom ((c * c) ^ Δ * s) ∈ pointIdeal a ^ ((t + 1) * Δ) := by
    have := Ideal.mem_map_of_mem dehom h
    rwa [Ideal.map_pow, Ideal.map_comap_of_surjective _ dehom_surjective, ← pow_mul] at this
  rw [map_mul, map_pow, map_mul, mul_comm ((dehom c * dehom c) ^ Δ)] at h1
  have h2 : dehom s ∈ pointIdeal a ^ ((t + 1) * Δ) := by
    refine mem_pointIdeal_pow_of_mul_mem (by positivity) h1 fun hmem ↦ hc ?_
    exact ((pointIdeal_isPrime a).mem_or_mem
      ((pointIdeal_isPrime a).mem_of_pow_mem _ hmem)).elim id id
  have h3 : (dehom s).totalDegree < (t + 1) * Δ :=
    (totalDegree_dehom_le hs).trans_lt (by nlinarith)
  exact eq_zero_of_dehom_eq_zero hs (eq_zero_of_mem_pointIdeal_pow_of_totalDegree_lt h2 h3)

/-- Node A08 (lower bound): `dim_K S_j = (j + k).choose k` for `S = MvPolynomial (Fin (k + 1)) K`
(via `dehomEquiv j : S_j ≃ P_{≤ j}`). -/
theorem finrank_homogeneousSubmodule_succ (j : ℕ) :
    Module.finrank K (homogeneousSubmodule (Fin (k + 1)) K j) = (j + k).choose k := by
  rw [(dehomEquiv j).finrank_eq, finrank_restrictTotalDegree]

end PointIdeal

/-! ### Coordinates with respect to a free submodule and a conductor -/

section Coordinates

variable {S R : Type*} [CommRing S] [CommRing R] [Algebra S R] {ι : Type*} [Fintype ι]
  {r : ι → R} (hli : LinearIndependent S r) {c : S}
  (hc : ∀ x : R, c • x ∈ Submodule.span S (Set.range r))

/-- Node A08 (step 2): the `S`-linear map `x ↦ (coordinates of c • x in the basis r of
`M = span S (range r)`)`, for a conductor `c` with `c • R ⊆ M`. -/
noncomputable def conductorCoord : R →ₗ[S] (ι →₀ S) :=
  (Module.Basis.span hli).repr.toLinearMap ∘ₗ
    (LinearMap.lsmul S R c).codRestrict (Submodule.span S (Set.range r)) hc

/-- Node A08 (step 2): `c • x = ∑ i, conductorCoord x i • r i`. -/
theorem smul_eq_sum_conductorCoord_smul (x : R) :
    c • x = ∑ i, conductorCoord hli hc x i • r i :=
  coe_eq_sum_repr_span_smul hli ⟨c • x, hc x⟩

/-- Node A08 (step 3): `(c * c) • x * r j = ∑ i, A i j • r i` with
`A i j := conductorCoord (c • x * r j) i`. -/
theorem mul_eq_sum_conductorCoord_smul (x : R) (j : ι) :
    (c * c) • x * r j = ∑ i, conductorCoord hli hc (c • x * r j) i • r i := by
  rw [← smul_eq_sum_conductorCoord_smul, mul_smul, smul_mul_assoc]

omit [Fintype ι] in
/-- Node A08 (step 3): **if all coordinates of `c • x` lie in an ideal `I`, so do the entries of
the matrix `A` of `(c * c) • x`**: `c • x * r j = ∑ l, (c • x)_l • (r l * r j)` and
`conductorCoord` is `S`-linear. -/
theorem conductorCoord_mem {I : Ideal S} {x : R} (hx : ∀ i, conductorCoord hli hc x i ∈ I)
    (j i : ι) : conductorCoord hli hc (c • x * r j) i ∈ I := by
  have h1 : c • x = (conductorCoord hli hc x).sum fun l s ↦ s • r l := by
    have h := congrArg Subtype.val
      ((Module.Basis.span hli).linearCombination_repr ⟨c • x, hc x⟩)
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum] at h
    simp only [Submodule.coe_smul, Module.Basis.coe_span_apply] at h
    exact h.symm
  have h2 : c • x * r j = (conductorCoord hli hc x).sum fun l s ↦ s • (r l * r j) := by
    rw [h1, Finsupp.sum_mul]
    simp_rw [smul_mul_assoc]
  rw [h2, map_finsuppSum, Finsupp.sum_apply, Finsupp.sum]
  refine Ideal.sum_mem _ fun l _ ↦ ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact I.mul_mem_right _ (hx l)

end Coordinates

/-! ### Homogeneous elements and the graded pieces `R_t` -/

section Pieces

variable {K : Type*} [Field K] {n : ℕ} {J : Ideal (MvPolynomial (Fin n) K)}

/-- Node A08: a homogeneous element of degree `t` of `R = Q ⧸ J` lies in the image `R_t` of the
forms of degree `t`. -/
theorem mem_map_mkₐ_of_isHomogeneousElem {x : MvPolynomial (Fin n) K ⧸ J} {t : ℕ}
    (hx : IsHomogeneousElem J x t) :
    x ∈ (homogeneousSubmodule (Fin n) K t).map (Ideal.Quotient.mkₐ K J).toLinearMap := by
  obtain ⟨G, hG, rfl⟩ := hx
  exact Submodule.mem_map_of_mem (f := (Ideal.Quotient.mkₐ K J).toLinearMap) hG

/-- Node A08: every element of `R_t` is homogeneous of degree `t`. -/
theorem isHomogeneousElem_of_mem_map_mkₐ {x : MvPolynomial (Fin n) K ⧸ J} {t : ℕ}
    (hx : x ∈ (homogeneousSubmodule (Fin n) K t).map (Ideal.Quotient.mkₐ K J).toLinearMap) :
    IsHomogeneousElem J x t := by
  obtain ⟨G, hG, rfl⟩ := Submodule.mem_map.mp hx
  exact ⟨G, hG, rfl⟩

end Pieces

/-! ### The shared setting -/

attribute [local instance] normalizationPolynomialQuotientSMul normalizationPolynomialQuotientModule
attribute [local instance] gradedNormAlgebraSMul gradedNormAlgebraModule gradedNormQuotientMulAction

section Setting

variable {K : Type*} [Field K] {n s : ℕ} {J : Ideal (MvPolynomial (Fin n) K)}
  {y : Fin s → MvPolynomial (Fin n) K}

-- synthesizing `Module (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)` from the `Algebra`
-- instance first explores `Submodule.Quotient.module'` and needs about `40000` heartbeats
/-- Node A08: in the shared setting, the scalar `C a ∈ S` acts on `R` as `a ∈ K`. -/
theorem C_smul_eq_smul [Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)]
    (halg : algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) =
      (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).toRingHom)
    (a : K) (x : MvPolynomial (Fin n) K ⧸ J) : (C a : MvPolynomial (Fin s) K) • x = a • x := by
  rw [Algebra.smul_def, algebraMap_C_eq_mk halg, Algebra.smul_def, ← MvPolynomial.algebraMap_eq,
    Ideal.Quotient.mk_algebraMap]

-- synthesizing `Module (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)` from the `Algebra`
-- instance first explores `Submodule.Quotient.module'` and needs about `40000` heartbeats
/-- Node A08: in the shared setting, `(a • p) • x = a • (p • x)` for `a : K`, `p : S`, `x : R`. -/
theorem smul_smul_eq_smul_smul [Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)]
    (halg : algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) =
      (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).toRingHom)
    (a : K) (p : MvPolynomial (Fin s) K) (x : MvPolynomial (Fin n) K ⧸ J) :
    (a • p) • x = a • (p • x) := by
  rw [smul_eq_C_mul, mul_smul, C_smul_eq_smul halg]

-- synthesizing `Module (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)` from the `Algebra`
-- instance first explores `Submodule.Quotient.module'` and is expensive
/-- Node A04′/A08: **the lower bound from the free submodule.** In the shared setting with
`s = k + 1`, if `r : Fin Δ → R` are `S`-linearly independent homogeneous elements of degrees `e`,
then `∑_{i : e i ≤ t} (t - e i + k).choose k ≤ homHilbert J t`: the `K`-linear map
`⨁_{i : e i ≤ t} S_{t - e i} → R_t`, `(p i) ↦ ∑ i, p i • r i`, is injective. -/
theorem sum_choose_le_homHilbert (hy : ∀ i, (y i).IsHomogeneous 1)
    [Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J)]
    (halg : algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ J) =
      (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).toRingHom)
    {Δ : ℕ} {r : Fin Δ → MvPolynomial (Fin n) K ⧸ J} {e : Fin Δ → ℕ}
    (hr : ∀ i, IsHomogeneousElem J (r i) (e i)) (hli : LinearIndependent (MvPolynomial (Fin s) K) r)
    {k : ℕ} (hs : s = k + 1) (t : ℕ) :
    ∑ i ∈ Finset.univ.filter (fun i ↦ e i ≤ t), (t - e i + k).choose k ≤ homHilbert J t := by
  subst hs
  classical
  set R_t := (homogeneousSubmodule (Fin n) K t).map (Ideal.Quotient.mkₐ K J).toLinearMap
  -- the source: forms of degree `t - e i` for each `i` with `e i ≤ t`
  let ι := {i : Fin Δ // e i ≤ t}
  let V := ∀ i : ι, homogeneousSubmodule (Fin (k + 1)) K (t - e i.1)
  let ψ : V →ₗ[K] MvPolynomial (Fin n) K ⧸ J :=
    { toFun := fun f ↦ ∑ i, (f i : MvPolynomial (Fin (k + 1)) K) • r i.1
      map_add' := fun f g ↦ by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        change ((f i + g i : homogeneousSubmodule (Fin (k + 1)) K (t - e i.1)) :
          MvPolynomial (Fin (k + 1)) K) • r i.1 = _
        rw [Submodule.coe_add, add_smul]
      map_smul' := fun a f ↦ by
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        change ((a • f i : homogeneousSubmodule (Fin (k + 1)) K (t - e i.1)) :
          MvPolynomial (Fin (k + 1)) K) • r i.1 = _
        rw [Submodule.coe_smul, smul_smul_eq_smul_smul halg] }
  have hmem : ∀ f, ψ f ∈ R_t := by
    intro f
    change ∑ i : ι, (f i : MvPolynomial (Fin (k + 1)) K) • r i.1 ∈ R_t
    refine Submodule.sum_mem _ fun i _ ↦ mem_map_mkₐ_of_isHomogeneousElem ?_
    have h := (isHomogeneousElem_algebraMap hy halg (f i).2).mul (hr i.1)
    rw [← Algebra.smul_def, Nat.sub_add_cancel i.2] at h
    exact h
  have hinj : Function.Injective (ψ.codRestrict R_t hmem) := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have h0 : ∑ i, (f i : MvPolynomial (Fin (k + 1)) K) • (r ∘ Subtype.val) i = 0 :=
      congrArg Subtype.val hf
    have hli' : LinearIndependent (MvPolynomial (Fin (k + 1)) K)
        (r ∘ (Subtype.val : ι → Fin Δ)) :=
      hli.comp Subtype.val Subtype.val_injective
    funext i
    exact Subtype.ext (Fintype.linearIndependent_iff.mp hli' _ h0 i)
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi_fintype] at hle
  simp_rw [finrank_homogeneousSubmodule_succ] at hle
  rw [Finset.sum_subtype (p := fun i ↦ e i ≤ t) (Finset.univ.filter fun i ↦ e i ≤ t)
    (fun i ↦ by simp)]
  exact hle

end Setting

/-! ### The upper bound: the fiber map -/

section Upper

variable {K : Type*} [Field K] {n k : ℕ} {J : Ideal (MvPolynomial (Fin n) K)}
  {y : Fin (k + 1) → MvPolynomial (Fin n) K}

-- `Frac R` is an algebra over `Frac S` through `FractionRing.liftAlgebra`, as in `FreeFiber.lean`
attribute [local instance] FractionRing.liftAlgebra

-- see the comment on `sum_choose_le_homHilbert`
/-- Node A08: the `Frac S`-module structure of `Frac R` coming from `FractionRing.liftAlgebra`,
as a shortcut instance: the generic search for `Module (Frac S) (Frac R)` explores the quotient and
localization instances first and does not terminate in reasonable time. -/
noncomputable abbrev fracModule [J.IsPrime]
    [Algebra (MvPolynomial (Fin (k + 1)) K) (MvPolynomial (Fin n) K ⧸ J)]
    [FaithfulSMul (MvPolynomial (Fin (k + 1)) K) (MvPolynomial (Fin n) K ⧸ J)] :
    Module (FractionRing (MvPolynomial (Fin (k + 1)) K))
      (FractionRing (MvPolynomial (Fin n) K ⧸ J)) :=
  Algebra.toModule

attribute [local instance] fracModule

-- synthesizing `Module (MvPolynomial (Fin (k + 1)) K) (MvPolynomial (Fin n) K ⧸ J)` from the
-- `Algebra` instance first explores `Submodule.Quotient.module'` and needs about `40000` heartbeats
/-- Node A08 (step 2): **the fiber map** `Φ : R →ₗ[K] (Fin Δ → T ⧸ 𝔪ₐ ^ (t + 1))`,
`Φ F i := (dehom of the i-th coordinate of c • F) mod 𝔪ₐ ^ (t + 1)`, where `T = K[y₁, …, y_k]`
and `dehom : S → T` is the substitution `Y₀ ↦ 1`. -/
noncomputable def fiberMap [Algebra (MvPolynomial (Fin (k + 1)) K) (MvPolynomial (Fin n) K ⧸ J)]
    (halg : algebraMap (MvPolynomial (Fin (k + 1)) K) (MvPolynomial (Fin n) K ⧸ J) =
      (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).toRingHom)
    {Δ : ℕ} {r : Fin Δ → MvPolynomial (Fin n) K ⧸ J}
    (hli : LinearIndependent (MvPolynomial (Fin (k + 1)) K) r) {c : MvPolynomial (Fin (k + 1)) K}
    (hc : ∀ x : MvPolynomial (Fin n) K ⧸ J,
      c • x ∈ Submodule.span (MvPolynomial (Fin (k + 1)) K) (Set.range r))
    (a : Fin k → K) (t : ℕ) :
    (MvPolynomial (Fin n) K ⧸ J) →ₗ[K]
      (Fin Δ → MvPolynomial (Fin k) K ⧸ pointIdeal a ^ (t + 1)) where
  toFun x i := Ideal.Quotient.mk _ (dehom (conductorCoord hli hc x i))
  map_add' x x' := by
    funext i
    rw [map_add, Finsupp.add_apply, map_add, map_add, Pi.add_apply]
  map_smul' b x := by
    funext i
    rw [RingHom.id_apply, Pi.smul_apply, ← C_smul_eq_smul halg, map_smul, Finsupp.smul_apply,
      smul_eq_mul, map_mul, dehom_C, map_mul, ← MvPolynomial.algebraMap_eq,
      Ideal.Quotient.mk_algebraMap, ← Algebra.smul_def]

-- synthesizing `Module (MvPolynomial (Fin (k + 1)) K) (MvPolynomial (Fin n) K ⧸ J)` from the
-- `Algebra` instance first explores `Submodule.Quotient.module'` and needs about `40000`
-- heartbeats; the fraction-field instances run this search several times, and already the
-- statement needs more than the default `200000` heartbeats in total

/-- Node A08 (steps 3–6): **the fiber map is injective on `R_t`.** If `F` is homogeneous of degree
`t` and `Φ F = 0`, then the matrix `A` of multiplication by `(c * c) • F` on `M = span S (range r)`
has entries in `𝔮 := dehom⁻¹ (𝔪ₐ ^ (t + 1))`, so `A.det ∈ 𝔮 ^ Δ`; but
`A.det = (c * c) ^ Δ * N(F)` with `N(F) ∈ S` a form of degree `t Δ` (A07′), which forces
`N(F) = 0` (`eq_zero_of_mul_mem_comap_pow`), hence `A.det = 0`, hence `(c * c) • F = 0` and
`F = 0`. The `Frac S`-algebra structure on `Frac R` is `FractionRing.liftAlgebra`. -/
theorem eq_zero_of_fiberMap_eq_zero [Infinite K]
    (hJh : J.IsHomogeneous (homogeneousSubmodule (Fin n) K)) (hy : ∀ i, (y i).IsHomogeneous 1)
    {N : ℕ} (hN : idealOfVars (Fin n) K ^ N ≤ J ⊔ Ideal.span (Set.range y)) [J.IsPrime]
    [Algebra (MvPolynomial (Fin (k + 1)) K) (MvPolynomial (Fin n) K ⧸ J)]
    [FaithfulSMul (MvPolynomial (Fin (k + 1)) K) (MvPolynomial (Fin n) K ⧸ J)]
    (halg : algebraMap (MvPolynomial (Fin (k + 1)) K) (MvPolynomial (Fin n) K ⧸ J) =
      (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).toRingHom)
    {Δ : ℕ} {r : Fin Δ → MvPolynomial (Fin n) K ⧸ J}
    (hli : LinearIndependent (MvPolynomial (Fin (k + 1)) K) r)
    (b : Module.Basis (Fin Δ) (FractionRing (MvPolynomial (Fin (k + 1)) K))
      (FractionRing (MvPolynomial (Fin n) K ⧸ J)))
    (hb : ∀ i, b i = algebraMap (MvPolynomial (Fin n) K ⧸ J) _ (r i))
    {c : MvPolynomial (Fin (k + 1)) K} (hc0 : c ≠ 0)
    (hc : ∀ x : MvPolynomial (Fin n) K ⧸ J,
      c • x ∈ Submodule.span (MvPolynomial (Fin (k + 1)) K) (Set.range r))
    {a : Fin k → K} (ha : dehom c ∉ pointIdeal a) {t : ℕ} {F : MvPolynomial (Fin n) K ⧸ J}
    (hF : IsHomogeneousElem J F t) (hΦ : fiberMap halg hli hc a t F = 0) : F = 0 := by
  set 𝔮 : Ideal (MvPolynomial (Fin (k + 1)) K) := (pointIdeal a ^ (t + 1)).comap dehom with h𝔮
  -- the coordinates of `c • F` lie in `𝔮`
  have hm : ∀ i, conductorCoord hli hc F i ∈ 𝔮 := fun i ↦ by
    rw [h𝔮, Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
    exact congrFun hΦ i
  -- the matrix of `(c * c) • F` has entries in `𝔮`
  set A : Matrix (Fin Δ) (Fin Δ) (MvPolynomial (Fin (k + 1)) K) :=
    fun i j ↦ conductorCoord hli hc (c • F * r j) i
  have hA : ∀ j, (c * c) • F * r j = ∑ i, A i j • r i := fun j ↦
    mul_eq_sum_conductorCoord_smul hli hc F j
  have hA𝔮 : ∀ i j, A i j ∈ 𝔮 := fun i j ↦ conductorCoord_mem hli hc hm j i
  have hdet : A.det ∈ 𝔮 ^ Δ := by
    have := det_mem_pow_of_forall_mem hA𝔮
    rwa [Fintype.card_fin] at this
  -- the determinant is `(c * c) ^ Δ` times the norm of `F`
  have hΔ : Module.finrank (FractionRing (MvPolynomial (Fin (k + 1)) K))
      (FractionRing (MvPolynomial (Fin n) K ⧸ J)) = Δ := finrank_fractionRing_eq_of_basis b
  obtain ⟨s, hs⟩ := norm_mem_range_algebraMap hJh hy hN halg F
  have hdet_eq : A.det = (c * c) ^ Δ * s := by
    apply IsFractionRing.injective (MvPolynomial (Fin (k + 1)) K)
      (FractionRing (MvPolynomial (Fin (k + 1)) K))
    have h1 : algebraMap (MvPolynomial (Fin n) K ⧸ J) (FractionRing (MvPolynomial (Fin n) K ⧸ J))
        ((c * c) • F) =
        algebraMap (FractionRing (MvPolynomial (Fin (k + 1)) K))
          (FractionRing (MvPolynomial (Fin n) K ⧸ J))
          (algebraMap (MvPolynomial (Fin (k + 1)) K) (FractionRing (MvPolynomial (Fin (k + 1)) K))
            (c * c)) *
        algebraMap (MvPolynomial (Fin n) K ⧸ J) (FractionRing (MvPolynomial (Fin n) K ⧸ J)) F := by
      rw [Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin (k + 1)) K)
          (MvPolynomial (Fin n) K ⧸ J),
        IsScalarTower.algebraMap_apply (MvPolynomial (Fin (k + 1)) K)
          (FractionRing (MvPolynomial (Fin (k + 1)) K))]
    rw [algebraMap_det_eq_norm b hb hA, h1, map_mul, Algebra.norm_algebraMap, hΔ, ← hs]
    simp only [map_mul, map_pow]
  -- the norm is a form of degree `t Δ`, hence zero
  have hshom : s.IsHomogeneous (t * Δ) := by
    have := norm_isHomogeneous hJh hy halg hF hs
    rwa [hΔ] at this
  have hs0 : s = 0 :=
    eq_zero_of_mul_mem_comap_pow (pos_of_basis_fractionRing b) ha hshom (hdet_eq ▸ hdet)
  -- hence `A.det = 0`, `(c * c) • F = 0`, `F = 0`
  have hu : (c * c) • F = 0 :=
    eq_zero_of_det_eq_zero hli hA (by rw [hdet_eq, hs0, mul_zero])
  rw [Algebra.smul_def] at hu
  refine (mul_eq_zero.mp hu).resolve_left fun h ↦ mul_ne_zero hc0 hc0 ?_
  exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mp h

-- see the comment on `eq_zero_of_fiberMap_eq_zero`

/-- Node A08: **the uniform upper bound in the shared setting.** With `Δ` the generic rank, `c` a
conductor and `a` a point with `dehom c ∉ 𝔪ₐ`, the fiber map `Φ : R_t → (Fin Δ → T ⧸ 𝔪ₐ ^ (t + 1))`
is injective, so `homHilbert J t ≤ Δ * (t + k).choose k`. -/
theorem homHilbert_le_rank_mul_choose [Infinite K]
    (hJh : J.IsHomogeneous (homogeneousSubmodule (Fin n) K)) (hy : ∀ i, (y i).IsHomogeneous 1)
    {N : ℕ} (hN : idealOfVars (Fin n) K ^ N ≤ J ⊔ Ideal.span (Set.range y)) [J.IsPrime]
    [Algebra (MvPolynomial (Fin (k + 1)) K) (MvPolynomial (Fin n) K ⧸ J)]
    [FaithfulSMul (MvPolynomial (Fin (k + 1)) K) (MvPolynomial (Fin n) K ⧸ J)]
    (halg : algebraMap (MvPolynomial (Fin (k + 1)) K) (MvPolynomial (Fin n) K ⧸ J) =
      (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).toRingHom)
    {Δ : ℕ} {r : Fin Δ → MvPolynomial (Fin n) K ⧸ J}
    (hli : LinearIndependent (MvPolynomial (Fin (k + 1)) K) r)
    (b : Module.Basis (Fin Δ) (FractionRing (MvPolynomial (Fin (k + 1)) K))
      (FractionRing (MvPolynomial (Fin n) K ⧸ J)))
    (hb : ∀ i, b i = algebraMap (MvPolynomial (Fin n) K ⧸ J) _ (r i))
    {c : MvPolynomial (Fin (k + 1)) K} (hc0 : c ≠ 0)
    (hc : ∀ x : MvPolynomial (Fin n) K ⧸ J,
      c • x ∈ Submodule.span (MvPolynomial (Fin (k + 1)) K) (Set.range r))
    {a : Fin k → K} (ha : dehom c ∉ pointIdeal a) (t : ℕ) :
    homHilbert J t ≤ Δ * (t + k).choose k := by
  set R_t := (homogeneousSubmodule (Fin n) K t).map (Ideal.Quotient.mkₐ K J).toLinearMap
  let Φ := (fiberMap halg hli hc a t).comp R_t.subtype
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro F hF
    exact Subtype.ext (eq_zero_of_fiberMap_eq_zero hJh hy hN halg hli b hb hc0 hc ha
      (isHomogeneousElem_of_mem_map_mkₐ F.2) hF)
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hle
  -- the `Module K` instance on the quotient is found along a different path here, so `rw` fails
  have hfin : Module.finrank K (MvPolynomial (Fin k) K ⧸ pointIdeal a ^ (t + 1)) =
      (t + k).choose k := by
    have h := finrank_quotient_pointIdeal_pow (K := K) (x := a) (r := t + 1) (by omega)
    rw [Nat.add_sub_cancel] at h
    exact h
  exact hle.trans (le_of_eq (congrArg (Δ * ·) hfin))

end Upper

/-! ### The packaged statement -/

section Main

variable {K : Type*} [Field K] {d : ℕ}

attribute [local instance] FractionRing.liftAlgebra fracModule

-- see the comment on `eq_zero_of_fiberMap_eq_zero`

/-- Node A08-core: **uniform Hilbert bounds for a prime ideal.** For a prime `I ⊆ K[X₁, …, X_d]`
with `k := quotDim I` there are `Δ > 0` (the generic rank of `(Q ⧸ Iʰ)` over a linear Noether
normalization `S = K[Y₀, …, Y_k]`) and degrees `e : Fin Δ → ℕ` with
`∑_{i : e i ≤ t} (t - e i + k).choose k ≤ hilbert I t ≤ Δ * (t + k).choose k` for every `t`. -/
theorem exists_hilbert_bounds [Infinite K] (I : Ideal (MvPolynomial (Fin d) K)) [I.IsPrime] :
    ∃ (Δ : ℕ) (e : Fin Δ → ℕ), 0 < Δ ∧
      (∀ t, ∑ i ∈ Finset.univ.filter (fun i ↦ e i ≤ t),
        (t - e i + quotDim I).choose (quotDim I) ≤ hilbert I t) ∧
      (∀ t, hilbert I t ≤ Δ * (t + quotDim I).choose (quotDim I)) := by
  set k := quotDim I
  set J := homogenization I
  have hJne : J ≠ ⊤ := homogenization_ne_top I Ideal.IsPrime.ne_top'
  have hJh := homogenization_isHomogeneous I
  have hdim : quotDim J = k + 1 := quotDim_homogenization I
  have hnorm := exists_linear_normalization J hJne hJh
  rw [hdim] at hnorm
  obtain ⟨y, hy, hinj, N, hN⟩ := hnorm
  let : Algebra (MvPolynomial (Fin (k + 1)) K) (MvPolynomial (Fin (d + 1)) K ⧸ J) :=
    (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).toRingHom.toAlgebra
  have halg : algebraMap (MvPolynomial (Fin (k + 1)) K) (MvPolynomial (Fin (d + 1)) K ⧸ J) =
      (MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk J (y i)).toRingHom :=
    RingHom.algebraMap_toAlgebra _
  have := faithfulSMul_of_halg halg hinj
  obtain ⟨Δ, r, e, hr, hli, b, hb⟩ := exists_homogeneous_fraction_basis hJh hy hN halg
  obtain ⟨c, hc0, hc⟩ := exists_conductor_of_pow_idealOfVars_le hJh hy hN halg ⟨b, hb⟩
  obtain ⟨c', γ, hc'0, hc'h, hc'⟩ := exists_homogeneous_conductor hJh hy halg hr hc0 hc
  obtain ⟨a, ha⟩ := exists_dehom_notMem_pointIdeal hc'h hc'0
  refine ⟨Δ, e, pos_of_basis_fractionRing b, fun t ↦ ?_, fun t ↦ ?_⟩
  · rw [← homHilbert_homogenization I t]
    exact sum_choose_le_homHilbert hy halg hr hli rfl t
  · rw [← homHilbert_homogenization I t]
    exact homHilbert_le_rank_mul_choose hJh hy hN halg hli b hb hc'0 hc' ha t

end Main

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
