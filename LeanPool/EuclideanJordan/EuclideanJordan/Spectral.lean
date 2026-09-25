/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
module

public import LeanPool.EuclideanJordan.EuclideanJordan.Subalgebra
public import LeanPool.EuclideanJordan.EuclideanJordan.FormallyReal
public import LeanPool.EuclideanJordan.EuclideanJordan.Witness
public import LeanPool.EuclideanJordan.EuclideanJordan.Bridge
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain



/-!
# The single-element spectral theorem for a formally real Jordan algebra

Every element of a finite-dimensional formally real Jordan algebra is a real combination of
pairwise-orthogonal idempotents drawn from the subalgebra it generates
(`spectral_resolution`), and, when a unit is available, of a family summing to it
(`spectral_resolution_complete`). Both are instantiated on `HermitianMat d 𝕜` at the end of
the file, so the abstract statements have a live carrier.

## The route, and why it carries no ring structure on `jspan x`

The classical treatment works inside the unital algebra `ℝ[x] = span{1, x, x², …}` and needs
that algebra to be a *ring* — which forces either a unit on `J` or a `Unitization` of a
subtype, and with it a `NonUnitalCommRing ↥(jspan x)` instance and its scalar towers. **None
of that appears here.** The polynomial bookkeeping is carried by a linear map

  `jeval x : ℝ[X] →ₗ[ℝ] J`,  `jeval x p = ∑ₙ p.coeff n • x^{n+1}`,

which is "`x·p(x)`" — the shape available with no unit at all, since every monomial carries
at least one factor of `x`. Its whole content is one identity,

  `jeval_mul : jeval x p * jeval x q = jeval x (X * p * q)`,

which is `EuclideanJordan/PowerAssoc.lean`'s `jpow_mul_jpow` transported along bilinearity.
    Everything
downstream is ideal theory in `ℝ[X]`, where Mathlib already has what is needed, and the
values live in the ambient `J`, where `EuclideanJordan/FormallyReal.lean` already applies.

The steps, each a named declaration below:

| step | statement | declaration |
| --- | --- | --- |
| 1 | the annihilator `{p | x·p(x) = 0}` is an ideal of `ℝ[X]`, nonzero in finite dimension |
    `jann`, `exists_annihilator_generator` |
| 2 | its generator `m` is radical, hence squarefree | `isRadical_of_annihilator` |
| 3 | `m` has a nonzero constant term | `coeff_zero_ne_zero_of_annihilator` |
| 4 | `m` has no non-real complex root | `annihilator_aeval_ne_zero_of_im_ne_zero` |
| 5 | so some product of distinct linear factors, none of them `X`, annihilates `x` |
    `exists_split_annihilator` |
| 6 | Lagrange interpolation at those roots together with `0` gives the idempotents |
    `exists_orthIdem_finset` |

★ **Step 2 is where formal reality enters the polynomial algebra**, through the identity
`jpow (jeval x f) n = jeval x (Xⁿ f^{n+1})` (`jpow_jeval`): a Jordan power of a value of
`jeval` is again a value of `jeval`, so `EuclideanJordan/FormallyReal.lean`'s no-nilpotents
    theorem —
which is stated about *ambient* elements of `J` — applies with no repackaging. This is why
no `IsReduced` instance on a ring structure over `jspan x` is needed anywhere.

★ **Step 4 uses no idempotent.** The textbook argument builds `e ≡ e² (mod m)` from a Bézout
splitting and applies formal reality to `((x−Re z)e(x))² + (Im z · e(x))²`. Here the
idempotence is never used: with `q ∣ m` the real quadratic through a non-real root `z`, and
`e := βu` from `α q + β u = 1`, the *only* facts consumed are `q·e ≡ 0 (mod m)` and, for the
contradiction, `e ≢ 0 (mod m)`. What formal reality kills is the value `jeval x g` directly,
where `X * g` is `e` corrected to have zero constant term — a correction available exactly
because of step 3. Multiplicities never enter, and neither does `Mathlib`'s `radical` API.

## Scope — what these theorems are NOT

* They are stated at the **typeclass** generality of the rest of the EJA layer
  (`NonUnitalNonAssocCommRing` + `IsCommJordan` + `Module ℝ` + `IsScalarTower` + finite
  dimension + `IsFormallyReal`). A consumer carrying its Jordan product as a *bundled bilinear
  map* `J →ₗ[ℝ] J →ₗ[ℝ] J` reaches them only through `EuclideanJordan/Bridge.lean`'s
  `ringOfBilinear`, for the reason recorded in `EuclideanJordan/Frame.lean`. The interface
  section at the end of this file does exactly that crossing, for this theorem and no other.
* `spectral_resolution` is unit-free and its idempotents therefore sum to the *support* of
  `x`, not to a unit. `spectral_resolution_complete` adds completeness by appending `e − s`
  with coefficient `0`; that member is not in `jspan x`, so the `jspan` clause is the price
  of completeness and is dropped there rather than weakened.
* Nothing here is a functional calculus: the resolution is produced, but no continuous or
  polynomial calculus is built on it.
-/

@[expose] public section

namespace EuclideanJordan

open Polynomial

section Eval

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]
  [IsScalarTower ℝ J J]

/-- `jeval x p = ∑ n, p.coeff n • x^{n+1}`, morally `x * p(x)`. -/
noncomputable def jeval (x : J) : Polynomial ℝ →ₗ[ℝ] J where
  toFun p := p.sum fun n a => a • jpow x n
  map_add' p q :=
    Polynomial.sum_add_index p q _ (fun _ => zero_smul _ _) (fun _ b₁ b₂ => add_smul b₁ b₂ _)
  map_smul' r p := by
    simp only [RingHom.id_apply]
    rw [Polynomial.sum_smul_index p r (fun n a => a • jpow x n) (fun _ => zero_smul ℝ _),
      Polynomial.smul_sum]
    exact Finset.sum_congr rfl fun n _ => (mul_smul r _ _)

omit [IsCommJordan J] [IsScalarTower ℝ J J] in
@[simp] theorem jeval_monomial (x : J) (n : ℕ) (a : ℝ) :
    jeval x (monomial n a) = a • jpow x n :=
  Polynomial.sum_monomial_index a (fun n a => a • jpow x n) (zero_smul _ _)

omit [IsCommJordan J] [IsScalarTower ℝ J J] in
@[simp] theorem jeval_one (x : J) : jeval x 1 = x := by
  rw [← C_1, ← monomial_zero_left, jeval_monomial, one_smul, jpow_zero]

omit [IsCommJordan J] in
/-- Multiplying the argument by `X` multiplies the value by `x`. -/
theorem jeval_X_mul (x : J) (p : Polynomial ℝ) : jeval x (X * p) = x * jeval x p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq, mul_add]
  | monomial n a =>
      rw [X_mul_monomial, jeval_monomial, jeval_monomial, jpow_succ,
        mul_smul_comm']

/-- **The multiplication rule.** `jeval` is "`x·p(x)`", so the product of two values is
`x·p(x)·x·q(x) = x·(X p q)(x)`. -/
theorem jeval_mul (x : J) (p q : Polynomial ℝ) :
    jeval x p * jeval x q = jeval x (X * p * q) := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ hp₁ hp₂ => rw [map_add, add_mul, hp₁, hp₂, mul_add, add_mul, map_add]
  | monomial m a =>
      induction q using Polynomial.induction_on' with
      | add q₁ q₂ hq₁ hq₂ => rw [map_add, mul_add, hq₁, hq₂, mul_add, map_add]
      | monomial n b =>
          rw [jeval_monomial, jeval_monomial, smul_mul_assoc, mul_smul_comm', jpow_mul_jpow,
            smul_smul, X_mul_monomial, monomial_mul_monomial, jeval_monomial]
          congr 2
          omega

end Eval

section Annihilator

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]
  [IsScalarTower ℝ J J]

omit [IsCommJordan J] in
theorem jeval_X_pow_mul {x : J} {p : Polynomial ℝ} (hp : jeval x p = 0) (k : ℕ) :
    jeval x (X ^ k * p) = 0 := by
  induction k with
  | zero => simpa using hp
  | succ k ih => rw [pow_succ', mul_assoc, jeval_X_mul, ih, mul_zero]

omit [IsCommJordan J] in
theorem jeval_mul_eq_zero {x : J} {p : Polynomial ℝ} (hp : jeval x p = 0) (q : Polynomial ℝ) :
    jeval x (q * p) = 0 := by
  induction q using Polynomial.induction_on' with
  | add q₁ q₂ h₁ h₂ => rw [add_mul, map_add, h₁, h₂, add_zero]
  | monomial n a =>
      have hmul : (monomial n a : Polynomial ℝ) * p = a • (X ^ n * p) := by
        rw [← C_mul_X_pow_eq_monomial, smul_eq_C_mul, mul_assoc]
      rw [hmul, map_smul, jeval_X_pow_mul hp n, smul_zero]

/-- The annihilator of `x`: the polynomials `p` with `x·p(x) = 0`. -/
noncomputable def jann (x : J) : Ideal (Polynomial ℝ) where
  carrier := {p | jeval x p = 0}
  add_mem' := fun {p q} hp hq => by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_add, hp, hq, add_zero]
  zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]
  smul_mem' := fun q p hp => by
    simp only [Set.mem_ofPred_eq, smul_eq_mul] at *
    exact jeval_mul_eq_zero hp q

omit [IsCommJordan J] in
theorem mem_jann {x : J} {p : Polynomial ℝ} : p ∈ jann x ↔ jeval x p = 0 := Iff.rfl

omit [IsCommJordan J] in
/-- **The annihilator has a nonzero generator.** Finite dimension makes the powers of `x`
dependent, so the annihilator is a nonzero ideal of the principal ideal ring `ℝ[X]`. -/
theorem exists_annihilator_generator [Module.Finite ℝ J] (x : J) :
    ∃ m : Polynomial ℝ, m ≠ 0 ∧ ∀ f, jeval x f = 0 ↔ m ∣ f := by
  obtain ⟨n, c, ⟨i₀, hi₀⟩, hsum⟩ := exists_jpow_relation x
  have hp0 : jeval x (∑ i : Fin n, monomial (i : ℕ) (c i)) = 0 := by
    rw [map_sum]
    simpa using hsum
  have hpne : (∑ i : Fin n, monomial (i : ℕ) (c i)) ≠ 0 := by
    intro h
    have hco : (∑ i : Fin n, monomial (i : ℕ) (c i)).coeff (i₀ : ℕ) = c i₀ := by
      rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single i₀]
      · simp
      · intro b _ hb
        simp [Polynomial.coeff_monomial, Fin.val_ne_of_ne hb]
      · simp
    rw [h, Polynomial.coeff_zero] at hco
    exact hi₀ hco.symm
  refine ⟨Submodule.IsPrincipal.generator (jann x), ?_, fun f => ?_⟩
  · intro hgen
    have := (Submodule.IsPrincipal.mem_iff_generator_dvd (jann x)).mp (mem_jann.mpr hp0)
    rw [hgen, zero_dvd_iff] at this
    exact hpne this
  · exact (mem_jann (x := x) (p := f)).symm.trans
      (Submodule.IsPrincipal.mem_iff_generator_dvd (jann x))

/-- `x·f(x)` raised to the `n`-th Jordan power is again a value of `jeval`. -/
theorem jpow_jeval (x : J) (f : Polynomial ℝ) (n : ℕ) :
    jpow (jeval x f) n = jeval x (X ^ n * f ^ (n + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [jpow_succ, ih, jeval_mul]
      congr 1
      ring

variable [IsFormallyReal J]

/-- **The generator is radical.** A power of `f` annihilating `x` forces `f` to, because the
Jordan powers of `x·f(x)` are exactly the values of `jeval` on `Xⁿ f^{n+1}` and a formally
real Jordan algebra has no nilpotents. -/
theorem isRadical_of_annihilator {x : J} {m : Polynomial ℝ}
    (hm : ∀ f, jeval x f = 0 ↔ m ∣ f) : IsRadical m := by
  intro n f hdvd
  match n with
  | 0 => exact (isUnit_of_dvd_one (by simpa using hdvd)).dvd
  | (k + 1) =>
      refine (hm f).mp ?_
      have h1 : jeval x (X ^ k * f ^ (k + 1)) = 0 :=
        jeval_X_pow_mul ((hm _).mpr hdvd) k
      rw [← jpow_jeval] at h1
      exact eq_zero_of_jpow_eq_zero k h1

/-- **The generator has a nonzero constant term.** If `X ∣ m` then the cofactor's value
squares to zero, so it too annihilates `x`, and it has smaller degree than the generator. -/
theorem coeff_zero_ne_zero_of_annihilator {x : J} {m : Polynomial ℝ}
    (hm : ∀ f, jeval x f = 0 ↔ m ∣ f) (hm0 : m ≠ 0) : m.coeff 0 ≠ 0 := by
  intro hc
  obtain ⟨m₁, hm₁⟩ := Polynomial.X_dvd_iff.mpr hc
  have hm₁0 : m₁ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm₁
    exact hm0 hm₁
  have hsq : jeval x m₁ * jeval x m₁ = 0 := by
    rw [jeval_mul, ← hm₁]
    exact (hm _).mpr ⟨m₁, rfl⟩
  have hdvd : m ∣ m₁ := (hm m₁).mp (eq_zero_of_mul_self_eq_zero hsq)
  have hle := Polynomial.natDegree_le_of_dvd hdvd hm₁0
  rw [hm₁, Polynomial.natDegree_mul Polynomial.X_ne_zero hm₁0, Polynomial.natDegree_X] at hle
  omega

end Annihilator

section Kill

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]
  [IsScalarTower ℝ J J] [IsFormallyReal J]

open Complex in
/-- **The kill.** The generator of the annihilator has no non-real complex root. -/
theorem annihilator_aeval_ne_zero_of_im_ne_zero {x : J} {m : Polynomial ℝ}
    (hm : ∀ f, jeval x f = 0 ↔ m ∣ f) (hsq : Squarefree m) (h0 : m.coeff 0 ≠ 0)
    {z : ℂ} (hz : z.im ≠ 0) : aeval z m ≠ 0 := by
  intro hroot
  obtain ⟨u, hu⟩ := m.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hroot hz
  set q : Polynomial ℝ := X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) with hqdef
  have hqnu : ¬ IsUnit q := by
    intro h
    have h2 : q.natDegree = 2 := by rw [hqdef]; compute_degree!
    rw [Polynomial.natDegree_eq_zero_of_isUnit h] at h2
    exact absurd h2 (by norm_num)
  have hcop : IsCoprime q u := by
    rw [hu] at hsq
    exact (IsRelPrime.of_squarefree_mul hsq).isCoprime
  obtain ⟨α, β, hbez⟩ := hcop
  set c : ℝ := (β * u).coeff 0 / m.coeff 0 with hcdef
  set g : Polynomial ℝ := (β * u - C c * m).divX with hgdef
  have hXg : X * g = β * u - C c * m := by
    have hc0 : (β * u - C c * m).coeff 0 = 0 := by
      simp [hcdef, div_mul_cancel₀ _ h0]
    rw [hgdef]
    conv_rhs => rw [← Polynomial.X_mul_divX_add (β * u - C c * m)]
    rw [hc0, map_zero, add_zero]
  -- `q` annihilates the class of `X * g`
  have h1 : m ∣ q * (X * g) := by
    rw [hXg]
    exact ⟨β - C c * q, by rw [hu]; ring⟩
  -- `q` is a sum of two squares
  have hqsq : q = (X - C z.re) ^ 2 + C (z.im ^ 2) := by
    have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [hqdef, hnorm]
    simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow, map_ofNat]
    ring
  -- the sum of squares vanishes
  set a : J := jeval x ((X - C z.re) * g) with hadef
  set b : J := z.im • jeval x g with hbdef
  have hsum : a * a + b * b = 0 := by
    have hb2 : b * b = jeval x (C (z.im ^ 2) * (X * g * g)) := by
      rw [hbdef, smul_mul_assoc, mul_smul_comm', smul_smul, jeval_mul, ← Polynomial.smul_eq_C_mul,
        map_smul]
      ring_nf
    rw [hadef, jeval_mul, hb2, ← map_add]
    refine (hm _).mpr (dvd_trans (h1.mul_right g) ?_)
    exact ⟨1, by rw [hqsq]; ring⟩
  have hb0 : b = 0 := by
    have := IsFormallyReal.eq_zero_of_sum_mul_self (Finset.univ : Finset (Fin 2)) ![a, b]
      (by simpa [Fin.sum_univ_two] using hsum)
    simpa using this 1 (Finset.mem_univ 1)
  have hg0 : jeval x g = 0 := by
    rcases smul_eq_zero.mp (hbdef ▸ hb0) with h | h
    · exact absurd h hz
    · exact h
  -- and that forces `q` to be a unit
  have hmg : m ∣ β * u := by
    have h4 : m ∣ β * u - C c * m := by
      rw [← hXg]; exact ((hm g).mp hg0).mul_left X
    simpa using dvd_add h4 (⟨C c, by ring⟩ : m ∣ C c * m)
  have hqm : q ∣ m := ⟨u, hu⟩
  exact hqnu (isUnit_of_dvd_one (hbez ▸ dvd_add (dvd_mul_left q α) (hqm.trans hmg)))

end Kill


section Split

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]
  [IsScalarTower ℝ J J] [IsFormallyReal J] [Module.Finite ℝ J]

/-- **The split annihilator.** Some product of *distinct* linear factors, none of them `X`,
annihilates `x`. -/
theorem exists_split_annihilator (x : J) :
    ∃ S : Finset ℝ, (0 : ℝ) ∉ S ∧ jeval x (∏ a ∈ S, (X - C a)) = 0 := by
  obtain ⟨m, hm0, hm⟩ := exists_annihilator_generator x
  have hsq : Squarefree m := (isRadical_of_annihilator hm).squarefree hm0
  have hc0 : m.coeff 0 ≠ 0 := coeff_zero_ne_zero_of_annihilator hm hm0
  refine ⟨m.roots.toFinset, ?_, ?_⟩
  · rw [Polynomial.coeff_zero_eq_eval_zero] at hc0
    simpa [Polynomial.mem_roots', Polynomial.IsRoot.def] using fun _ => hc0
  · have hPm : (∏ a ∈ m.roots.toFinset, (X - C a)) ∣ m :=
      Finset.prod_dvd_of_coprime
        ((Polynomial.pairwise_coprime_X_sub_C (Function.injective_id (α := ℝ))).set_pairwise _)
        (fun a ha => Polynomial.dvd_iff_isRoot.mpr
          (Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp ha)))
    obtain ⟨W, hW⟩ := hPm
    have hWnr : ∀ r : ℝ, W.eval r ≠ 0 := by
      intro r hr
      have hmr : m.IsRoot r := by rw [hW]; simp [Polynomial.IsRoot.def, hr]
      have hrS : r ∈ m.roots.toFinset :=
        Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hm0, hmr⟩)
      have hdd : (X - C r) * (X - C r) ∣ m := by
        rw [hW]
        exact mul_dvd_mul (Finset.dvd_prod_of_mem _ hrS) (Polynomial.dvd_iff_isRoot.mpr hr)
      have hu := hsq _ hdd
      rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_X_sub_C] at hu
      exact one_ne_zero hu
    have hWu : IsUnit W := by
      by_contra hWnu
      have hW0 : W ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hW
        exact hm0 hW
      have hdeg : W.degree ≠ 0 := fun h => hWnu (Polynomial.isUnit_iff_degree_eq_zero.mpr h)
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ W hdeg
      have him : z.im ≠ 0 := by
        intro h
        refine hWnr z.re ?_
        have hzr : z = algebraMap ℝ ℂ z.re := by
          apply Complex.ext <;> simp [h]
        rw [hzr, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at hz
        simpa using hz
      exact annihilator_aeval_ne_zero_of_im_ne_zero hm hsq hc0 him (by rw [hW, map_mul, hz,
          mul_zero])
    obtain ⟨v, hv⟩ := hWu.exists_right_inv
    refine (hm _).mpr ⟨v, ?_⟩
    calc (∏ a ∈ m.roots.toFinset, (X - C a))
        = (∏ a ∈ m.roots.toFinset, (X - C a)) * (W * v) := by rw [hv, mul_one]
      _ = m * v := by rw [← mul_assoc, ← hW]

omit [IsCommJordan J] [IsScalarTower ℝ J J] [IsFormallyReal J] [Module.Finite ℝ J] in
/-- Every value of `jeval x` lies in the subalgebra generated by `x`. -/
theorem jeval_mem_jspan (x : J) (p : Polynomial ℝ) : jeval x p ∈ jspan x := by
  change p.sum (fun n a => a • jpow x n) ∈ jspan x
  rw [Polynomial.sum_def]
  exact Submodule.sum_mem _ fun n _ => Submodule.smul_mem _ _ (jpow_mem_jspan x n)

omit [IsCommJordan J] [IsFormallyReal J] [Module.Finite ℝ J] in
/-- **The vehicle.** A polynomial vanishing at every node of `S ∪ {0}` is divisible by the
nodal polynomial, and the annihilator absorbs the quotient. -/
theorem jeval_eq_zero_of_eval_eq_zero {x : J} {S : Finset ℝ} (h0S : (0 : ℝ) ∉ S)
    (hA : jeval x (∏ a ∈ S, (X - C a)) = 0) {p f : Polynomial ℝ} (hpf : X * p = f)
    (hf : ∀ ν ∈ insert (0 : ℝ) S, f.eval ν = 0) : jeval x p = 0 := by
  have hnodal : (∏ ν ∈ insert (0 : ℝ) S, (X - C ν)) = X * ∏ a ∈ S, (X - C a) := by
    rw [Finset.prod_insert h0S, map_zero, sub_zero]
  have hdvd : (∏ ν ∈ insert (0 : ℝ) S, (X - C ν)) ∣ f :=
    Finset.prod_dvd_of_coprime
      ((Polynomial.pairwise_coprime_X_sub_C (Function.injective_id (α := ℝ))).set_pairwise _)
      (fun ν hν => Polynomial.dvd_iff_isRoot.mpr (hf ν hν))
  rw [hnodal] at hdvd
  obtain ⟨h, hh⟩ := hdvd
  have hp : p = (∏ a ∈ S, (X - C a)) * h := by
    apply mul_left_cancel₀ (Polynomial.X_ne_zero (R := ℝ))
    rw [hpf, hh, mul_assoc]
  rw [hp, mul_comm]
  exact jeval_mul_eq_zero hA h

/-- **The spectral resolution, indexed by the eigenvalues.** -/
theorem exists_orthIdem_finset (x : J) :
    ∃ (S : Finset ℝ) (c : ℝ → J), (∀ a ∈ S, c a * c a = c a) ∧
      (∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → c a * c a' = 0) ∧
      (∀ a, c a ∈ jspan x) ∧ x = ∑ a ∈ S, a • c a := by
  classical
  obtain ⟨S, h0S, hA⟩ := exists_split_annihilator x
  set b : ℝ → Polynomial ℝ := fun a => Lagrange.basis (insert (0 : ℝ) S) id a with hbdef
  set g : ℝ → Polynomial ℝ := fun a => (b a).divX with hgdef
  have h0T : (0 : ℝ) ∈ insert (0 : ℝ) S := Finset.mem_insert_self 0 S
  have hne : ∀ a ∈ S, a ≠ 0 := fun a ha h => h0S (h ▸ ha)
  have hinj : Set.InjOn (id : ℝ → ℝ) (↑(insert (0 : ℝ) S) : Set ℝ) := fun _ _ _ _ h => h
  have heval : ∀ a ∈ S, ∀ ν ∈ insert (0 : ℝ) S, (b a).eval ν = if ν = a then 1 else 0 := by
    intro a ha ν hν
    by_cases h : ν = a
    · subst h
      simpa [hbdef] using Lagrange.eval_basis_self hinj (Finset.mem_insert_of_mem ha)
    · simpa [hbdef, h] using Lagrange.eval_basis_of_ne (v := (id : ℝ → ℝ)) (Ne.symm h) hν
  have hXg : ∀ a ∈ S, b a = X * g a := by
    intro a ha
    have h0 : (b a).coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, heval a ha 0 h0T, ite_eq_right (Ne.symm (hne a ha))]
    conv_lhs => rw [← Polynomial.X_mul_divX_add (b a)]
    rw [h0, map_zero, add_zero, hgdef]
  refine ⟨S, fun a => jeval x (g a), ?_, ?_, fun a => jeval_mem_jspan x (g a), ?_⟩
  · intro a ha
    have key : jeval x (X * g a * g a - g a) = 0 := by
      refine jeval_eq_zero_of_eval_eq_zero h0S hA (f := b a ^ 2 - b a) ?_ ?_
      · rw [hXg a ha]; ring
      · intro ν hν
        simp only [Polynomial.eval_sub, Polynomial.eval_pow, heval a ha ν hν]
        by_cases h : ν = a <;> simp [h]
    rw [map_sub, sub_eq_zero, ← jeval_mul] at key
    change jeval x (g a) * jeval x (g a) = jeval x (g a)
    exact key
  · intro a ha a' ha' haa'
    have key : jeval x (X * g a * g a') = 0 := by
      refine jeval_eq_zero_of_eval_eq_zero h0S hA (f := b a * b a') ?_ ?_
      · rw [hXg a ha, hXg a' ha']; ring
      · intro ν hν
        simp only [Polynomial.eval_mul, heval a ha ν hν, heval a' ha' ν hν]
        by_cases h : ν = a
        · rw [ite_eq_left h, ite_eq_right (by rw [h]; exact haa'), mul_zero]
        · rw [ite_eq_right h, zero_mul]
    rw [← jeval_mul] at key
    change jeval x (g a) * jeval x (g a') = 0
    exact key
  · have key : jeval x (1 - ∑ a ∈ S, a • g a) = 0 := by
      refine jeval_eq_zero_of_eval_eq_zero h0S hA (f := X - ∑ a ∈ S, a • b a) ?_ ?_
      · rw [mul_sub, mul_one, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun a ha => by rw [mul_smul_comm, ← hXg a ha]
      · intro ν hν
        simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_finsetSum,
          Polynomial.eval_smul, smul_eq_mul]
        rcases Finset.mem_insert.mp hν with rfl | hνS
        · rw [Finset.sum_eq_zero fun a ha => by
            rw [heval a ha 0 hν, ite_eq_right (Ne.symm (hne a ha)), mul_zero], sub_zero]
        · rw [Finset.sum_eq_single ν
            (fun a ha hane => by rw [heval a ha ν hν, ite_eq_right (Ne.symm hane), mul_zero])
            (fun h => absurd hνS h),
            heval ν hνS ν hν, ite_eq_left rfl, mul_one, sub_self]
    rw [map_sub, map_sum, jeval_one, sub_eq_zero] at key
    simpa using key

/-- **The single-element spectral theorem.** -/
theorem spectral_resolution (x : J) :
    ∃ (n : ℕ) (c : Fin n → J) (lam : Fin n → ℝ),
      IsOrthIdemFamily c ∧ (∀ i, c i ∈ jspan x) ∧ x = ∑ i, lam i • c i := by
  classical
  obtain ⟨S, c, hidem, horth, hmem, hx⟩ := exists_orthIdem_finset x
  refine ⟨S.card, fun i => c (S.equivFin.symm i), fun i => ((S.equivFin.symm i : ℝ)),
    ⟨fun i => hidem _ (S.equivFin.symm i).2, fun i j hij => ?_⟩, fun i => hmem _, ?_⟩
  · refine horth _ (S.equivFin.symm i).2 _ (S.equivFin.symm j).2 fun h => hij ?_
    exact S.equivFin.symm.injective (Subtype.ext h)
  · rw [hx, ← Finset.sum_coe_sort S (fun a => a • c a)]
    exact (Equiv.sum_comp S.equivFin.symm (fun a : {y // y ∈ S} => (a : ℝ) • c a)).symm

/-- **The spectral theorem with completeness**, the unit carried as an ordinary hypothesis. -/
theorem spectral_resolution_complete (e : J) (he : ∀ y : J, e * y = y) (x : J) :
    ∃ (n : ℕ) (c : Fin n → J) (lam : Fin n → ℝ),
      IsOrthIdemFamily c ∧ (∑ i, c i) = e ∧ x = ∑ i, lam i • c i := by
  obtain ⟨n, c, lam, hfam, _, hx⟩ := spectral_resolution x
  have hss : (∑ i, c i) * (∑ i, c i) = ∑ i, c i := hfam.sum_idem Finset.univ
  have hsc : ∀ k, (∑ i, c i) * c k = c k := by
    intro k
    rw [Finset.sum_mul, Finset.sum_eq_single k (fun j _ hjk => hfam.orth j k hjk)
      (fun h => absurd (Finset.mem_univ k) h)]
    exact hfam.idem k
  have hes : (∑ i, c i) * e = ∑ i, c i := by rw [mul_comm, he]
  have hlast : (e - ∑ i, c i) * (e - ∑ i, c i) = e - ∑ i, c i := by
    rw [sub_mul, mul_sub, mul_sub, he, he, hss, hes, sub_self, sub_zero]
  have horthlast : ∀ k, (e - ∑ i, c i) * c k = 0 := by
    intro k
    rw [sub_mul, he, hsc, sub_self]
  refine ⟨n + 1, Fin.snoc c (e - ∑ i, c i), Fin.snoc lam 0, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro i
    induction i using Fin.lastCases with
    | last => simpa using hlast
    | cast i => simpa using hfam.idem i
  · intro i j hij
    induction i using Fin.lastCases with
    | last =>
        induction j using Fin.lastCases with
        | last => exact absurd rfl hij
        | cast j => simpa using horthlast j
    | cast i =>
        induction j using Fin.lastCases with
        | last => simpa [mul_comm] using horthlast i
        | cast j =>
            simpa using hfam.orth i j fun h => hij (by rw [h])
  · rw [Fin.sum_univ_castSucc]
    simp
  · rw [Fin.sum_univ_castSucc]
    simpa using hx

end Split


section Concrete

open HermMul

variable {d : Type*} [Fintype d] [DecidableEq d] {𝕜 : Type*} [RCLike 𝕜]

/-- **The spectral theorem live on `H_d(𝕜)`.** -/
theorem hermitian_spectral_resolution (A : HermitianMat d 𝕜) :
    ∃ (n : ℕ) (c : Fin n → HermitianMat d 𝕜) (lam : Fin n → ℝ),
      IsOrthIdemFamily c ∧ (∀ i, c i ∈ jspan A) ∧ A = ∑ i, lam i • c i :=
  spectral_resolution A

/-- **The spectral theorem with completeness, live on `H_d(𝕜)`**: the unit is `1`. -/
theorem hermitian_spectral_resolution_complete (A : HermitianMat d 𝕜) :
    ∃ (n : ℕ) (c : Fin n → HermitianMat d 𝕜) (lam : Fin n → ℝ),
      IsOrthIdemFamily c ∧ (∑ i, c i) = 1 ∧ A = ∑ i, lam i • c i :=
  spectral_resolution_complete 1 (fun y => by rw [mul_eq_symmMul, HermitianMat.symmMul_comm,
    HermitianMat.symmMul_one]) A

end Concrete


section Interface

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]

omit [InnerProductSpace ℝ J] in
/-- Formal reality over an arbitrary `Finset`, from the `Fin k` form. The two differ only by
reindexing. -/
theorem isFormallyReal_of_fin [Module ℝ J] (m : J →ₗ[ℝ] J →ₗ[ℝ] J) (hcomm : ∀ x y : J, m x y = m
    y x)
    (hfr : ∀ (k : ℕ) (f : Fin k → J), (∑ i, m (f i) (f i)) = 0 → ∀ i, f i = 0) :
    letI : NonUnitalNonAssocCommRing J := ringOfBilinear m hcomm
    IsFormallyReal J := by
  let : NonUnitalNonAssocCommRing J := ringOfBilinear m hcomm
  refine ⟨fun {ι} s f hsum i hi => ?_⟩
  classical
  have key : (∑ k : Fin s.card, m (f (s.equivFin.symm k)) (f (s.equivFin.symm k))) = 0 := by
    rw [show (∑ k : Fin s.card, m (f (s.equivFin.symm k)) (f (s.equivFin.symm k)))
        = ∑ a : {y // y ∈ s}, m (f a) (f a) from
      Equiv.sum_comp s.equivFin.symm (fun a : {y // y ∈ s} => m (f a) (f a)),
      Finset.sum_coe_sort s (fun a => m (f a) (f a))]
    exact hsum
  simpa using hfr s.card (fun k => f (s.equivFin.symm k)) key (s.equivFin ⟨i, hi⟩)

/-- **The spectral theorem in bilinear-map vocabulary**: the Jordan product as a bundled
bilinear map, the Jordan identity and formal reality as hypotheses in that vocabulary, and the
conclusion stated without mentioning any ring instance.

★ This is the crossing `EuclideanJordan/Bridge.lean` was built for, and it works here for the
    reason that file
gives: the *statement* is expressible with `m` alone, so no ring instance has to exist before it
elaborates. Only the proof needs one, and `ringOfBilinear` supplies it on the ambient additive
group.

★ Finite-dimensionality is not decoration. Without it the statement is false: `ℝ[X]` with
polynomial multiplication satisfies every hypothesis below and has no nonconstant spectral
resolution, its only idempotents being `0` and `1`. -/
theorem spectral_resolution_bilinear [FiniteDimensional ℝ J] (m : J →ₗ[ℝ] J →ₗ[ℝ] J)
    (hcomm : ∀ x y : J, m x y = m y x)
    (hjordan : ∀ a b : J, m (m a b) (m a a) = m a (m b (m a a)))
    (hfr : ∀ (k : ℕ) (f : Fin k → J), (∑ i, m (f i) (f i)) = 0 → ∀ i, f i = 0)
    (e : J) (he : ∀ y : J, m e y = y) (x : J) :
    ∃ (n : ℕ) (q : Fin n → J) (lam : Fin n → ℝ),
      (∀ i, m (q i) (q i) = q i) ∧
      (∀ i j, i ≠ j → m (q i) (q j) = 0) ∧
      (∑ i, q i) = e ∧
      x = ∑ i, lam i • q i := by
  let : NonUnitalNonAssocCommRing J := ringOfBilinear m hcomm
  let : IsCommJordan J := ⟨hjordan⟩
  let : IsScalarTower ℝ J J := ⟨fun r x y => smul_bilinear m r x y⟩
  let : IsFormallyReal J := isFormallyReal_of_fin m hcomm hfr
  obtain ⟨n, q, lam, hfam, hsum, hx⟩ := spectral_resolution_complete e he x
  exact ⟨n, q, lam, hfam.idem, hfam.orth, hsum, hx⟩

end Interface

end EuclideanJordan
