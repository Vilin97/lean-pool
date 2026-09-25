/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# The limit theorem for flatness at a finite stage

The ordinary-ring case of the limit theorem for flatness
(EGA IV, 11.2.6.1): when `R` is a directed colimit of commutative
rings `Rᵢ` and a finitely presented flat `R`-module arises by base
change from a stage `i₀`, the base change to some finite stage
`j ≥ i₀` is already flat.

We work with the matrix form of Lazard's equational criterion.  A
finitely presented module is the cokernel of a presentation matrix
`K : Matrix (Fin n) (Fin m) A`; such a cokernel is projective —
equivalently flat, see the bridge below — precisely when `K`
admits a *certificate*: a matrix `T` with `K * T * K = K`
(`projective_of_matrix_certificate` and
`matrix_certificate_of_projective`).  A certificate is a finite
system of ring equations, so it descends along a directed colimit
of rings (`exists_stage_matrix_certificate`); the headline
statement is `exists_stage_projective`.

The colimit is presented abstractly by
`DirectedColimitPresentation`: a compatible cocone `gᵢ : Rᵢ →+* R`
which is jointly surjective and detects equalities at a finite
stage.  `Ring.DirectLimit` provides these data via
`Ring.DirectLimit.exists_of` and `Ring.DirectLimit.of.zero_exact`
(module `Mathlib.Algebra.Colimit.Ring`, outside our import
funnel), so the statements here apply to it directly.

## The flatness bridge

`Module.Flat` lives in `Mathlib.RingTheory.Flat.Basic`, which is
not reachable through `RS.Common.MathlibDeps`, so the statements
here are phrased with `Module.Projective`.  The translation to
flatness is a pair of Mathlib lemmas for the consumer:

* `Module.Flat.of_projective`
  (`Mathlib.RingTheory.Flat.Basic`): projective modules are flat;
* `Module.Flat.projective_of_finitePresentation`
  (`Mathlib.RingTheory.Flat.EquationalCriterion`): a finitely
  presented flat module is projective.

With these, `exists_stage_projective` is the flatness statement:
a finitely presented flat `R`-module presented by the base change
of a stage-`i₀` matrix is projective, its certificate descends to
a stage `j`, and every module presented over `Rⱼ` by the pushed
matrix — in particular the base change `Rⱼ ⊗_{R_{i₀}} M_{i₀}` —
is projective, hence flat.
-/

namespace RS
namespace FlatLimit

/-! ## Lazard certificates

A module presented by the matrix `K` — the cokernel of
`K.mulVecLin : A^m →ₗ A^n` — is projective exactly when `K` admits
a matrix `T` with `K * T * K = K`.  The two directions are
`projective_of_matrix_certificate` and
`matrix_certificate_of_projective`.
-/

section Certificate

variable {A : Type*}

/-- Matrices inducing the same linear map are equal. -/
theorem matrix_eq_of_mulVecLin_eq [CommRing A]
    {p q : ℕ}
    {K L : Matrix (Fin p) (Fin q) A}
    (h : K.mulVecLin = L.mulVecLin) : K = L := by
  ext a b
  have h1 : K.mulVec (Pi.single b 1) = L.mulVec (Pi.single b 1) := by
    have h2 := DFunLike.congr_fun h (Pi.single b 1)
    simpa [Matrix.mulVecLin_apply] using h2
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h1
  simpa [Matrix.col_apply] using congrFun h1 a

/-- The matrix assembled from the prescribed columns
`t 0, …, t (q-1)` sends the `j`-th basis vector to `t j`. -/
theorem mulVecLin_ofCols_single [CommRing A]
    {p q : ℕ} (t : Fin q → Fin p → A)
    (j : Fin q) :
    (Matrix.of fun a b => t b a).mulVecLin (Pi.single j (1 : A))
      = t j := by
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  funext a
  simp [Matrix.col_apply]

/-- One half of the matrix form of Lazard's criterion: a
certificate `K * T * K = K` splits the presentation, so any module
presented by `K` is a direct summand of `A ^ n` and therefore
projective.  Combined with `Module.Flat.of_projective` (outside
the funnel) this shows certified modules are flat. -/
theorem projective_of_matrix_certificate [CommRing A]
    {m n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M]
    {K : Matrix (Fin n) (Fin m) A} {π : (Fin n → A) →ₗ[A] M}
    (hsurj : Function.Surjective π)
    (hker : LinearMap.ker π = LinearMap.range K.mulVecLin)
    {T : Matrix (Fin m) (Fin n) A} (hT : K * T * K = K) :
    Module.Projective A M := by
  have hSK : (1 - K * T) * K = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hT, sub_self]
  have hπK : ∀ y, π (K.mulVec y) = 0 := by
    intro y
    have hy : K.mulVec y ∈ LinearMap.ker π := by
      rw [hker]
      exact ⟨y, Matrix.mulVecLin_apply K y⟩
    exact LinearMap.mem_ker.mp hy
  have hkerle :
      LinearMap.ker π ≤ LinearMap.ker (1 - K * T).mulVecLin := by
    rw [hker]
    rintro x ⟨y, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hSK,
      Matrix.zero_mulVec]
  refine Module.Projective.of_split
    ((LinearMap.ker π).liftQ (1 - K * T).mulVecLin hkerle ∘ₗ
      (π.quotKerEquivOfSurjective hsurj).symm.toLinearMap) π ?_
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := hsurj x
  simp only [LinearMap.comp_apply, LinearMap.id_apply,
    LinearEquiv.coe_toLinearMap,
    LinearMap.quotKerEquivOfSurjective_symm_apply,
    Submodule.liftQ_apply]
  rw [Matrix.mulVecLin_apply,
    Matrix.sub_mulVec, Matrix.one_mulVec, map_sub,
    ← Matrix.mulVec_mulVec, hπK, sub_zero]

/-- The other half of the matrix form of Lazard's criterion: a
projective module presented by `K` yields a certificate
`K * T * K = K`.  Via
`Module.Flat.projective_of_finitePresentation` (outside the
funnel) the hypothesis holds for any finitely presented flat
module. -/
theorem matrix_certificate_of_projective [CommRing A]
    {m n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Projective A M]
    {K : Matrix (Fin n) (Fin m) A} {π : (Fin n → A) →ₗ[A] M}
    (hsurj : Function.Surjective π)
    (hker : LinearMap.ker π = LinearMap.range K.mulVecLin) :
    ∃ T : Matrix (Fin m) (Fin n) A, K * T * K = K := by
  obtain ⟨s, hs⟩ :=
    Module.projective_lifting_property π LinearMap.id hsurj
  have hsec : ∀ z, π (s z) = z := by
    intro z
    simpa using DFunLike.congr_fun hs z
  have hπK : ∀ y, π (K.mulVecLin y) = 0 := by
    intro y
    have hy : K.mulVecLin y ∈ LinearMap.ker π := by
      rw [hker]
      exact ⟨y, rfl⟩
    exact LinearMap.mem_ker.mp hy
  -- each basis column of `1 - s ∘ π` is a relation, so it lifts
  -- through `K`
  have hcol : ∀ j : Fin n, ∃ t : Fin m → A,
      K.mulVecLin t = Pi.single j 1 - s (π (Pi.single j 1)) := by
    intro j
    have hmem : (Pi.single j 1 - s (π (Pi.single j 1)) : Fin n → A)
        ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker, map_sub, hsec, sub_self]
    rw [hker] at hmem
    exact hmem
  choose t ht using hcol
  refine ⟨Matrix.of fun a b => t b a, ?_⟩
  apply matrix_eq_of_mulVecLin_eq
  -- `K * T` induces `1 - s ∘ π`, checked on basis vectors
  have hKT : K.mulVecLin ∘ₗ
        (Matrix.of fun a b => t b a).mulVecLin
      = LinearMap.id - s ∘ₗ π := by
    apply LinearMap.pi_ext'
    intro j
    apply LinearMap.ext
    intro a
    have hsingle : (Pi.single j a : Fin n → A)
        = a • Pi.single j 1 := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    simp only [LinearMap.comp_apply, LinearMap.coe_single,
      LinearMap.sub_apply, LinearMap.id_apply]
    rw [hsingle, map_smul, map_smul, mulVecLin_ofCols_single,
      ht j, map_smul, map_smul, smul_sub]
  rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, hKT]
  apply LinearMap.ext
  intro y
  simp only [LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.id_apply]
  rw [hπK, map_zero, sub_zero]

end Certificate

/-! ## Directed colimit presentations of a ring

The colimit `R = colim Rᵢ` enters only through three properties of
the cocone `gᵢ : Rᵢ →+* R`: compatibility with the transition
maps, joint surjectivity, and detection of equalities at a finite
stage.  `Ring.DirectLimit` satisfies all three.
-/

section Colimit

variable {ι : Type*}

/-- A presentation of the commutative ring `R` as the directed
colimit of the system `F` with transition maps `f`: a compatible
cocone which is jointly surjective and detects equalities at a
finite stage.  These are the only properties of a filtered colimit
of rings used by the limit theorem. -/
structure DirectedColimitPresentation
    [Preorder ι] {F : ι → Type*} [∀ i, CommRing (F i)]
    (f : ∀ ⦃i j : ι⦄, i ≤ j → F i →+* F j)
    (R : Type*) [CommRing R] where
  /-- The cocone maps from the stages to the colimit. -/
  toColim : ∀ i, F i →+* R
  /-- The cocone commutes with the transition maps. -/
  compat : ∀ ⦃i j : ι⦄ (h : i ≤ j) (x : F i),
    toColim j (f h x) = toColim i x
  /-- Every element of the colimit comes from some stage. -/
  exhaustive : ∀ x : R, ∃ i, ∃ y : F i, toColim i y = x
  /-- An equality in the colimit holds at some later stage. -/
  eventuallyEq : ∀ i (x y : F i), toColim i x = toColim i y →
    ∃ j, ∃ h : i ≤ j, f h x = f h y

/-- Every finite family of elements of the colimit lifts jointly
to a single stage. -/
theorem DirectedColimitPresentation.exists_stage_family
    [Preorder ι] {F : ι → Type*} [∀ i, CommRing (F i)] [Nonempty ι]
    [IsDirectedOrder ι] {f : ∀ ⦃i j : ι⦄, i ≤ j → F i →+* F j} {R : Type*}
    [CommRing R]
    (P : DirectedColimitPresentation f R)
    {κ : Type*} [Finite κ] (x : κ → R) :
    ∃ i, ∃ y : κ → F i, ∀ k, P.toColim i (y k) = x k := by
  classical
  let := Fintype.ofFinite κ
  choose idx y hy using fun k => P.exhaustive (x k)
  obtain ⟨i, hi⟩ := (Finset.univ.image idx).exists_le
  refine ⟨i, fun k => f (hi (idx k)
    (Finset.mem_image_of_mem idx (Finset.mem_univ k))) (y k),
    fun k => ?_⟩
  exact (P.compat _ _).trans (hy k)

/-- Finitely many equalities holding in the colimit hold
simultaneously at some common later stage. -/
theorem DirectedColimitPresentation.exists_stage_eq
    [Preorder ι] {F : ι → Type*} [∀ i, CommRing (F i)] [Nonempty ι]
    [IsDirectedOrder ι] {f : ∀ ⦃i j : ι⦄, i ≤ j → F i →+* F j} {R : Type*}
    [CommRing R]
    (P : DirectedColimitPresentation f R)
    (hDS : DirectedSystem F fun _ _ h => f h)
    {κ : Type*} [Finite κ] {i : ι} {a b : κ → F i}
    (hab : ∀ k, P.toColim i (a k) = P.toColim i (b k)) :
    ∃ j, ∃ h : i ≤ j, ∀ k, f h (a k) = f h (b k) := by
  classical
  let := Fintype.ofFinite κ
  choose jdx hjdx hj using fun k =>
    P.eventuallyEq i (a k) (b k) (hab k)
  obtain ⟨j, hjle⟩ := (insert i (Finset.univ.image jdx)).exists_le
  have hij : i ≤ j := hjle i (Finset.mem_insert_self _ _)
  refine ⟨j, hij, fun k => ?_⟩
  have hk : jdx k ≤ j := hjle _ (Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem jdx (Finset.mem_univ k)))
  calc f hij (a k)
      = f hk (f (hjdx k) (a k)) := (hDS.map_map _ _ _).symm
    _ = f hk (f (hjdx k) (b k)) := by rw [hj k]
    _ = f hij (b k) := hDS.map_map _ _ _

/-- Every matrix over the colimit lifts to a matrix at some
stage. -/
theorem DirectedColimitPresentation.exists_stage_matrix
    [Preorder ι] {F : ι → Type*} [∀ i, CommRing (F i)] [Nonempty ι]
    [IsDirectedOrder ι] {f : ∀ ⦃i j : ι⦄, i ≤ j → F i →+* F j} {R : Type*}
    [CommRing R]
    (P : DirectedColimitPresentation f R)
    {p q : ℕ} (X : Matrix (Fin p) (Fin q) R) :
    ∃ i, ∃ Y : Matrix (Fin p) (Fin q) (F i),
      Y.map (P.toColim i) = X := by
  obtain ⟨i, y, hy⟩ := P.exists_stage_family
    (fun k : Fin p × Fin q => X k.1 k.2)
  refine ⟨i, Matrix.of fun a b => y (a, b), ?_⟩
  ext a b
  simpa [Matrix.map_apply] using hy (a, b)

/-- An equality of matrices in the colimit holds at some later
stage. -/
theorem DirectedColimitPresentation.exists_stage_matrix_eq
    [Preorder ι] {F : ι → Type*} [∀ i, CommRing (F i)] [Nonempty ι]
    [IsDirectedOrder ι] {f : ∀ ⦃i j : ι⦄, i ≤ j → F i →+* F j} {R : Type*}
    [CommRing R]
    (P : DirectedColimitPresentation f R)
    (hDS : DirectedSystem F fun _ _ h => f h)
    {p q : ℕ} {i : ι} {Xa Xb : Matrix (Fin p) (Fin q) (F i)}
    (h : Xa.map (P.toColim i) = Xb.map (P.toColim i)) :
    ∃ j, ∃ hij : i ≤ j, Xa.map (f hij) = Xb.map (f hij) := by
  have h' : ∀ k : Fin p × Fin q,
      P.toColim i (Xa k.1 k.2) = P.toColim i (Xb k.1 k.2) := by
    intro k
    have h1 := (Matrix.ext_iff.mpr h) k.1 k.2
    simpa [Matrix.map_apply] using h1
  obtain ⟨j, hij, he⟩ := P.exists_stage_eq hDS h'
  refine ⟨j, hij, ?_⟩
  ext a b
  simpa [Matrix.map_apply] using he (a, b)

end Colimit

/-! ## The limit theorem -/

section Limit

variable {ι : Type*}

/-- Certificates descend to a finite stage: when the base change
to the colimit of a stage-`i₀` presentation matrix admits a
certificate over `R`, its base change to some finite stage
`j ≥ i₀` admits a certificate over `F j`.  This is the equational
heart of the limit theorem for flatness: the certificate is a
finite system of ring equations, its entries live at a finite
stage, and the equations hold at a further stage. -/
theorem DirectedColimitPresentation.exists_stage_matrix_certificate
    [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] {F : ι → Type*}
    [∀ i, CommRing (F i)] {f : ∀ ⦃i j : ι⦄, i ≤ j → F i →+* F j} {R : Type*}
    [CommRing R]
    (P : DirectedColimitPresentation f R)
    (hDS : DirectedSystem F fun _ _ h => f h)
    {m n : ℕ} {i₀ : ι} (K₀ : Matrix (Fin n) (Fin m) (F i₀))
    (T : Matrix (Fin m) (Fin n) R)
    (hT : K₀.map (P.toColim i₀) * T * K₀.map (P.toColim i₀)
      = K₀.map (P.toColim i₀)) :
    ∃ j, ∃ hij : i₀ ≤ j, ∃ Tj : Matrix (Fin m) (Fin n) (F j),
      K₀.map (f hij) * Tj * K₀.map (f hij) = K₀.map (f hij) := by
  -- lift the certificate entries to a stage `i₁`
  obtain ⟨i₁, T₁, hT₁⟩ := P.exists_stage_matrix T
  -- move everything to a common stage `i₂`
  obtain ⟨i₂, h₀₂, h₁₂⟩ := exists_ge_ge i₀ i₁
  -- the certificate equation holds in the colimit at stage `i₂`
  have hK₂ : (K₀.map (f h₀₂)).map (P.toColim i₂)
      = K₀.map (P.toColim i₀) := by
    ext a b
    simp [Matrix.map_apply, P.compat]
  have hT₂ : (T₁.map (f h₁₂)).map (P.toColim i₂) = T := by
    rw [← hT₁]
    ext a b
    simp [Matrix.map_apply, P.compat]
  have hg : (K₀.map (f h₀₂) * T₁.map (f h₁₂) * K₀.map (f h₀₂)).map
        (P.toColim i₂)
      = (K₀.map (f h₀₂)).map (P.toColim i₂) := by
    rw [Matrix.map_mul, Matrix.map_mul, hK₂, hT₂, hT]
  -- the equation therefore holds at a later stage `j`
  obtain ⟨j, h₂ⱼ, he⟩ := P.exists_stage_matrix_eq hDS hg
  refine ⟨j, h₀₂.trans h₂ⱼ, (T₁.map (f h₁₂)).map (f h₂ⱼ), ?_⟩
  have hKj : (K₀.map (f h₀₂)).map (f h₂ⱼ)
      = K₀.map (f (h₀₂.trans h₂ⱼ)) := by
    ext a b
    simp only [Matrix.map_apply]
    exact hDS.map_map _ _ _
  rw [← hKj]
  rw [Matrix.map_mul, Matrix.map_mul] at he
  exact he

/-- The limit theorem for flatness, projective form (the
ordinary-ring case of EGA IV, 11.2.6.1).  Let `R` be a directed
colimit of the commutative rings `F i` and let `M` be a projective
`R`-module presented by the base change of a stage-`i₀` matrix
`K₀` — for instance a finitely presented flat module arising by
base change from a finitely presented module at stage `i₀`, via
`Module.Flat.projective_of_finitePresentation`.  Then there is a
stage `j ≥ i₀` at which every module presented by the pushed
matrix `K₀.map (f hij)` — in particular the base change
`F j ⊗_{F i₀} M_{i₀}`, whose presentation matrix it is by right
exactness of the tensor product — is projective, hence flat via
`Module.Flat.of_projective`. -/
theorem DirectedColimitPresentation.exists_stage_projective
    [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] {F : ι → Type*}
    [∀ i, CommRing (F i)] {f : ∀ ⦃i j : ι⦄, i ≤ j → F i →+* F j} {R : Type*}
    [CommRing R]
    (P : DirectedColimitPresentation f R)
    (hDS : DirectedSystem F fun _ _ h => f h)
    {m n : ℕ} {i₀ : ι} (K₀ : Matrix (Fin n) (Fin m) (F i₀))
    {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Projective R M]
    {π : (Fin n → R) →ₗ[R] M} (hsurj : Function.Surjective π)
    (hker : LinearMap.ker π
      = LinearMap.range (K₀.map (P.toColim i₀)).mulVecLin) :
    ∃ j, ∃ hij : i₀ ≤ j,
      ∀ (N : Type*) [AddCommGroup N] [Module (F j) N]
        (ρ : (Fin n → F j) →ₗ[F j] N), Function.Surjective ρ →
        LinearMap.ker ρ
          = LinearMap.range (K₀.map (f hij)).mulVecLin →
        Module.Projective (F j) N := by
  obtain ⟨T, hT⟩ := matrix_certificate_of_projective hsurj hker
  obtain ⟨j, hij, Tj, hTj⟩ :=
    P.exists_stage_matrix_certificate hDS K₀ T hT
  exact ⟨j, hij, fun N _ _ ρ hρsurj hρker =>
    projective_of_matrix_certificate hρsurj hρker hTj⟩

end Limit

end FlatLimit
end RS
