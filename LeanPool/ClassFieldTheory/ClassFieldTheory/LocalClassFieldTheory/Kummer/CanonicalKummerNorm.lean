/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.SimpleExtension
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Norm.Basic
/-!
# Norms from an irreducible Kummer algebra

When `X^n - a` is irreducible, the canonical algebra obtained by adjoining a
root is isomorphic to the chosen simple Kummer field.  This file transports
the algebra norm through that isomorphism.
-/

@[expose] public section

noncomputable
section

namespace LocalClassFieldTheory.Kummer

/-- Algebra norms multiply across a product of finite algebras. -/
private theorem norm_prod_apply
    (K S T : Type) [Field K] [CommRing S] [CommRing T]
    [Algebra K S] [Algebra K T]
    [Module.Free K S] [Module.Finite K S]
    [Module.Free K T] [Module.Finite K T]
    (x : S × T) :
    Algebra.norm K x = Algebra.norm K x.1 * Algebra.norm K x.2 := by
  have hmul : Algebra.lmul K (S × T) x =
      (Algebra.lmul K S x.1).prodMap (Algebra.lmul K T x.2) := by
    apply LinearMap.ext
    intro z
    rcases z with ⟨s, t⟩
    rfl
  rw [Algebra.norm_apply, hmul, LinearMap.det_prodMap,
    ← Algebra.norm_apply, ← Algebra.norm_apply]

/-- If `X^n - a` is irreducible, being a norm from its canonical root algebra
is equivalent to being a norm from the chosen simple Kummer field. -/
theorem adjoinRoot_norm_iff_chosenSimpleKummerNorm_of_irreducible
    (K : Type) [Field K] (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (a b : Kˣ)
    (hirr : Irreducible
      (Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K))) :
    (∃ y : (AdjoinRoot
          (Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)))ˣ,
        Algebra.norm K
          (y : AdjoinRoot
            (Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K))) = (b : K)) ↔
      ∃ y : (KummerTheory.chosenSimpleKummerExtension K n hnK a)ˣ,
        Algebra.norm K
          (y : KummerTheory.chosenSimpleKummerExtension K n hnK a) = (b : K) := by
  let β : SeparableClosure K := KummerTheory.chosenSimpleKummerRoot K n hnK a
  let p : Polynomial K := Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)
  have hβ : Polynomial.aeval β p = 0 := by
    simp only [p, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      β, KummerTheory.chosenSimpleKummerRoot_pow, sub_self]
  have hp : p = minpoly K β :=
    minpoly.eq_of_irreducible_of_monic hirr hβ
      (Polynomial.monic_X_pow_sub_C (a : K) n.pos.ne')
  have hβint : IsIntegral K β := by
    apply IsIntegral.of_pow n.pos
    rw [show β ^ (n : ℕ) = algebraMap K (SeparableClosure K) (a : K) from
      KummerTheory.chosenSimpleKummerRoot_pow K n hnK a]
    exact isIntegral_algebraMap
  let E := KummerTheory.chosenSimpleKummerExtension K n hnK a
  let e : AdjoinRoot p ≃ₐ[K] E :=
    (AdjoinRoot.algEquivOfEq K p (minpoly K β) hp).trans
      (IntermediateField.adjoinRootEquivAdjoin K hβint)
  change (∃ y : (AdjoinRoot p)ˣ, Algebra.norm K (y : AdjoinRoot p) = (b : K)) ↔
    ∃ y : Eˣ, Algebra.norm K (y : E) = (b : K)
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Units.map e.toMonoidHom y, ?_⟩
    change Algebra.norm K (e (y : AdjoinRoot p)) = (b : K)
    rw [Algebra.norm_eq_of_algEquiv e, hy]
  · rintro ⟨y, hy⟩
    refine ⟨Units.map e.symm.toMonoidHom y, ?_⟩
    change Algebra.norm K (e.symm (y : E)) = (b : K)
    rw [Algebra.norm_eq_of_algEquiv e.symm, hy]

/-- The canonical Kummer algebra separates, by the Chinese remainder theorem,
into the factor containing the chosen radical and a complementary factor.
The two factors are coprime because `n` is nonzero in the base field. -/
theorem adjoinRoot_decompose_chosenMinpoly
    (K : Type) [Field K] (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (a : Kˣ) :
    let p : Polynomial K := Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)
    let q : Polynomial K :=
      minpoly K (KummerTheory.chosenSimpleKummerRoot K n hnK a)
    ∃ r : Polynomial K, p = q * r ∧ IsCoprime q r ∧
      Nonempty (AdjoinRoot p ≃ₐ[K] (AdjoinRoot q × AdjoinRoot r)) := by
  let β : SeparableClosure K := KummerTheory.chosenSimpleKummerRoot K n hnK a
  let p : Polynomial K := Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)
  let q : Polynomial K := minpoly K β
  have hβ : Polynomial.aeval β p = 0 := by
    simp only [p, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      β, KummerTheory.chosenSimpleKummerRoot_pow, sub_self]
  obtain ⟨r, hr⟩ := minpoly.dvd K β hβ
  have hsep : p.Separable := by
    exact Polynomial.separable_X_pow_sub_C (a : K) hnK (Units.ne_zero a)
  have hcoprime : IsCoprime q r := by
    apply Polynomial.Separable.isCoprime
    rw [← hr]
    exact hsep
  let I : Ideal (Polynomial K) := Ideal.span {q}
  let J : Ideal (Polynomial K) := Ideal.span {r}
  have hIJ : Ideal.span ({p} : Set (Polynomial K)) = I * J := by
    change Ideal.span {p} = Ideal.span {q} * Ideal.span {r}
    rw [Ideal.span_singleton_mul_span_singleton, hr]
  have hIcoprime : IsCoprime I J :=
    (Ideal.isCoprime_span_singleton_iff q r).2 hcoprime
  let eRing : AdjoinRoot p ≃+* (AdjoinRoot q × AdjoinRoot r) :=
    (Ideal.quotEquivOfEq hIJ).trans
      (Ideal.quotientMulEquivQuotientProd I J hIcoprime)
  let e : AdjoinRoot p ≃ₐ[K] (AdjoinRoot q × AdjoinRoot r) :=
    AlgEquiv.ofRingEquiv (f := eRing) (fun _ => rfl)
  exact ⟨r, hr, hcoprime, ⟨e⟩⟩

/-- The norm from the canonical Kummer algebra factors through the chosen
simple Kummer field and the complementary algebra. -/
theorem adjoinRoot_norm_decompose_chosenMinpoly
    (K : Type) [Field K] (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (a : Kˣ) :
    let p : Polynomial K := Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)
    let E := KummerTheory.chosenSimpleKummerExtension K n hnK a
    ∃ (r : Polynomial K), r.Monic ∧ r ∣ p ∧
      ∃ e : AdjoinRoot p ≃ₐ[K] (E × AdjoinRoot r),
        ∀ y : AdjoinRoot p,
          Algebra.norm K y =
            Algebra.norm K (e y).1 * Algebra.norm K (e y).2 := by
  let β : SeparableClosure K := KummerTheory.chosenSimpleKummerRoot K n hnK a
  let p : Polynomial K := Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)
  let q : Polynomial K := minpoly K β
  let E := KummerTheory.chosenSimpleKummerExtension K n hnK a
  obtain ⟨r, hr, -, ⟨e₀⟩⟩ :=
    adjoinRoot_decompose_chosenMinpoly K n hnK a
  have hβint : IsIntegral K β := by
    apply IsIntegral.of_pow n.pos
    rw [show β ^ (n : ℕ) = algebraMap K (SeparableClosure K) (a : K) from
      KummerTheory.chosenSimpleKummerRoot_pow K n hnK a]
    exact isIntegral_algebraMap
  let e₁ : AdjoinRoot q ≃ₐ[K] E :=
    IntermediateField.adjoinRootEquivAdjoin K hβint
  let e : AdjoinRoot p ≃ₐ[K] (E × AdjoinRoot r) :=
    e₀.trans (AlgEquiv.prodCongr e₁ AlgEquiv.refl)
  have hpmonic : p.Monic :=
    Polynomial.monic_X_pow_sub_C (a : K) n.pos.ne'
  have hqmonic : q.Monic := minpoly.monic hβint
  have hrmonic : r.Monic := by
    apply hqmonic.of_mul_monic_left
    rw [← hr]
    exact hpmonic
  have : Module.Finite K E :=
    KummerTheory.chosenSimpleKummerExtension_finiteDimensional K n hnK a
  have : Module.Free K (AdjoinRoot r) := hrmonic.free_adjoinRoot
  have : Module.Finite K (AdjoinRoot r) := hrmonic.finite_adjoinRoot
  have hrdiv : r ∣ p := by
    refine ⟨q, ?_⟩
    exact hr.trans (mul_comm q r)
  refine ⟨r, hrmonic, hrdiv, e, ?_⟩
  intro y
  calc
    Algebra.norm K y = Algebra.norm K (e y) :=
      (Algebra.norm_eq_of_algEquiv e y).symm
    _ = Algebra.norm K (e y).1 * Algebra.norm K (e y).2 :=
      norm_prod_apply K E (AdjoinRoot r) (e y)

/-- Every `n`-th root of `a` inside the chosen simple Kummer extension
generates that extension when the base contains the `n`-th roots of unity. -/
theorem adjoin_root_eq_top_of_pow_eq
    (K : Type) [Field K] (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a : Kˣ)
    (γ : KummerTheory.chosenSimpleKummerExtension K n hnK a)
    (hγ : γ ^ (n : ℕ) =
      algebraMap K (KummerTheory.chosenSimpleKummerExtension K n hnK a) (a : K)) :
    IntermediateField.adjoin K {γ} = ⊤ := by
  let E := KummerTheory.chosenSimpleKummerExtension K n hnK a
  let β : Eˣ := KummerTheory.chosenSimpleKummerRootUnit K n hnK a
  have hγne : γ ≠ 0 := by
    intro hz
    rw [hz, zero_pow n.pos.ne'] at hγ
    exact ((map_ne_zero (algebraMap K E)).2 (Units.ne_zero a)) hγ.symm
  let γu : Eˣ := Units.mk0 γ hγne
  have hγpow : γu ^ (n : ℕ) =
      Units.map (algebraMap K E).toMonoidHom a := by
    apply Units.ext
    exact hγ
  have hβpow : β ^ (n : ℕ) =
      Units.map (algebraMap K E).toMonoidHom a :=
    KummerTheory.chosenSimpleKummerRootUnit_pow K n hnK a
  let u : Eˣ := γu / β
  have hu : u ^ (n : ℕ) = 1 := by
    change (γu / β) ^ (n : ℕ) = 1
    rw [div_pow, hγpow, hβpow, div_self']
  obtain ⟨ζ, hζ⟩ :=
    KummerTheory.nthRootsOfUnityInBase_of_primitiveRoots
      (K := K) (L := E) n hmu u hu
  have hζβ : Units.map (algebraMap K E).toMonoidHom ζ * β = γu := by
    rw [hζ]
    exact div_mul_cancel γu β
  have hβζ : β =
      (Units.map (algebraMap K E).toMonoidHom ζ)⁻¹ * γu := by
    have h := congrArg
      (fun x : Eˣ => (Units.map (algebraMap K E).toMonoidHom ζ)⁻¹ * x) hζβ
    simpa only [inv_mul_cancel_left] using h
  have hβζE : (β : E) =
      ((Units.map (algebraMap K E).toMonoidHom ζ : Eˣ) : E)⁻¹ * γ := by
    have h := congrArg (fun x : Eˣ => (x : E)) hβζ
    simpa only [Units.val_mul, Units.val_inv_eq_inv_val, γu, Units.val_mk0] using h
  have hβmem : (β : E) ∈ IntermediateField.adjoin K {γ} := by
    rw [hβζE]
    have hζmem : ((Units.map (algebraMap K E).toMonoidHom ζ : Eˣ) : E) ∈
        IntermediateField.adjoin K {γ} := by
      rw [Units.coe_map]
      exact IntermediateField.algebraMap_mem _ (ζ : K)
    exact mul_mem (inv_mem hζmem)
      (IntermediateField.subset_adjoin K {γ} (Set.mem_singleton γ))
  have hle : IntermediateField.adjoin K {(β : E)} ≤
      IntermediateField.adjoin K {γ} := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    have hx' : x = (β : E) := Set.mem_singleton_iff.mp hx
    rw [hx']
    exact hβmem
  have htop := KummerTheory.chosenSimpleKummerExtension_adjoin_root_eq_top K n hnK a
  exact top_unique (htop ▸ hle)

/-- Every monic irreducible factor of `X^n - a` defines the same Kummer
extension, because all of its roots are scalar multiples of the chosen one. -/
theorem adjoinRoot_factor_equiv_chosenSimpleKummer
    (K : Type) [Field K] (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a : Kˣ)
    (f : Polynomial K) (hfmonic : f.Monic) (hfirr : Irreducible f)
    (hfp : f ∣ Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)) :
    Nonempty (AdjoinRoot f ≃ₐ[K]
      KummerTheory.chosenSimpleKummerExtension K n hnK a) := by
  let E := KummerTheory.chosenSimpleKummerExtension K n hnK a
  let p : Polynomial K := Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)
  let β : E := KummerTheory.chosenSimpleKummerRootUnit K n hnK a
  have hβpow : β ^ (n : ℕ) = algebraMap K E (a : K) := by
    simpa only [E, β, Units.val_pow_eq_pow_val, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] using
      congrArg (fun u : Eˣ => (u : E))
        (KummerTheory.chosenSimpleKummerRootUnit_pow K n hnK a)
  obtain ⟨ζ, hζ⟩ := hmu
  have hprim : IsPrimitiveRoot ζ (n : ℕ) :=
    (mem_primitiveRoots n.pos).1 hζ
  have hsplit : (p.map (algebraMap K E)).Splits := by
    dsimp only [p]
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
    exact X_pow_sub_C_splits_of_isPrimitiveRoot
      (hprim.map_of_injective (algebraMap K E).injective) hβpow
  have hpne : p.map (algebraMap K E) ≠ 0 := by
    dsimp only [p]
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
    exact Polynomial.X_pow_sub_C_ne_zero n.pos _
  have hsplitf : (f.map (algebraMap K E)).Splits :=
    hsplit.of_dvd hpne (Polynomial.map_dvd (algebraMap K E) hfp)
  have hfd : (f.map (algebraMap K E)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (algebraMap K E).injective]
    exact ne_of_gt (Polynomial.degree_pos_of_irreducible hfirr)
  let γ : E := Polynomial.rootOfSplits hsplitf hfd
  have hγf : Polynomial.aeval γ f = 0 := by
    simpa only [Polynomial.aeval_def, Polynomial.eval_map] using
      (Polynomial.eval_rootOfSplits hsplitf hfd)
  have hγp : Polynomial.aeval γ p = 0 := by
    obtain ⟨g, hg⟩ := hfp
    change Polynomial.aeval γ (Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)) = 0
    rw [hg, map_mul, hγf, zero_mul]
  have hγpow : γ ^ (n : ℕ) = algebraMap K E (a : K) := by
    have h := hγp
    simp only [p, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      sub_eq_zero] at h
    exact h
  have hγgen : IntermediateField.adjoin K {γ} = ⊤ :=
    adjoin_root_eq_top_of_pow_eq K n hnK ⟨ζ, hζ⟩ a γ hγpow
  have hγint : IsIntegral K γ := by
    apply IsIntegral.of_pow n.pos
    rw [hγpow]
    exact isIntegral_algebraMap
  have hminpoly : f = minpoly K γ :=
    minpoly.eq_of_irreducible_of_monic hfirr hγf hfmonic
  let e : AdjoinRoot f ≃ₐ[K] E :=
    (AdjoinRoot.algEquivOfEq K f (minpoly K γ) hminpoly).trans
      ((IntermediateField.adjoinRootEquivAdjoin K hγint).trans
        ((IntermediateField.equivOfEq hγgen).trans
          IntermediateField.topEquiv))
  exact ⟨e⟩

/-- For coprime monic polynomials, the norm from an adjunction algebra is the
product of the norms from the two factors. -/
theorem adjoinRoot_norm_decompose_coprime
    (K : Type) [Field K] (q r : Polynomial K)
    (hq : q.Monic) (hr : r.Monic) (hqr : IsCoprime q r) :
    ∃ e : AdjoinRoot (q * r) ≃ₐ[K] (AdjoinRoot q × AdjoinRoot r),
      ∀ y : AdjoinRoot (q * r),
        Algebra.norm K y =
          Algebra.norm K (e y).1 * Algebra.norm K (e y).2 := by
  let I : Ideal (Polynomial K) := Ideal.span {q}
  let J : Ideal (Polynomial K) := Ideal.span {r}
  have hIJ : Ideal.span ({q * r} : Set (Polynomial K)) = I * J := by
    change Ideal.span {q * r} = Ideal.span {q} * Ideal.span {r}
    exact (Ideal.span_singleton_mul_span_singleton q r).symm
  have hIcoprime : IsCoprime I J :=
    (Ideal.isCoprime_span_singleton_iff q r).2 hqr
  let eRing : AdjoinRoot (q * r) ≃+* (AdjoinRoot q × AdjoinRoot r) :=
    (Ideal.quotEquivOfEq hIJ).trans
      (Ideal.quotientMulEquivQuotientProd I J hIcoprime)
  let e : AdjoinRoot (q * r) ≃ₐ[K] (AdjoinRoot q × AdjoinRoot r) :=
    AlgEquiv.ofRingEquiv (f := eRing) (fun _ => rfl)
  have : Module.Free K (AdjoinRoot q) := hq.free_adjoinRoot
  have : Module.Finite K (AdjoinRoot q) := hq.finite_adjoinRoot
  have : Module.Free K (AdjoinRoot r) := hr.free_adjoinRoot
  have : Module.Finite K (AdjoinRoot r) := hr.finite_adjoinRoot
  refine ⟨e, ?_⟩
  intro y
  calc
    Algebra.norm K y = Algebra.norm K (e y) :=
      (Algebra.norm_eq_of_algEquiv e y).symm
    _ = Algebra.norm K (e y).1 * Algebra.norm K (e y).2 :=
      norm_prod_apply K (AdjoinRoot q) (AdjoinRoot r) (e y)

/-- The norm of a unit from any monic factor of `X^n - a` is a norm from the
chosen simple Kummer extension. This includes reducible factors. -/
theorem adjoinRoot_factor_norm_is_chosenSimpleKummerNorm
    (K : Type) [Field K] (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a : Kˣ)
    (f : Polynomial K) (hfmonic : f.Monic)
    (hfp : f ∣ Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K))
    (y : (AdjoinRoot f)ˣ) :
    ∃ z : (KummerTheory.chosenSimpleKummerExtension K n hnK a)ˣ,
      Algebra.norm K (y : AdjoinRoot f) =
        Algebra.norm K
          (z : KummerTheory.chosenSimpleKummerExtension K n hnK a) := by
  let p : Polynomial K := Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)
  let E := KummerTheory.chosenSimpleKummerExtension K n hnK a
  have hpsep : p.Separable :=
    Polynomial.separable_X_pow_sub_C (a : K) hnK (Units.ne_zero a)
  suffices h : ∀ d : ℕ, ∀ g : Polynomial K, g.natDegree = d → g.Monic →
      g ∣ p → ∀ u : (AdjoinRoot g)ˣ,
        ∃ v : Eˣ, Algebra.norm K (u : AdjoinRoot g) = Algebra.norm K (v : E) from
    h f.natDegree f rfl hfmonic hfp y
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro g hgd hgmonic hgp u
    by_cases hd : d = 0
    · have hg1 : g = 1 :=
        Polynomial.eq_one_of_monic_natDegree_zero hgmonic (hgd.trans hd)
      subst g
      have hsub : Subsingleton (AdjoinRoot (1 : Polynomial K)) := by
        change Subsingleton ((Polynomial K) ⧸ Ideal.span {1})
        exact Ideal.Quotient.subsingleton_iff.mpr (by simp)
      have hu1 : (u : AdjoinRoot (1 : Polynomial K)) = 1 :=
        Subsingleton.elim _ _
      refine ⟨1, ?_⟩
      simp only [hu1, map_one, Units.val_one]
    · have hgpos : 0 < g.natDegree := by omega
      obtain ⟨q, hqmonic, hqirr, hqg⟩ :=
        Polynomial.exists_monic_irreducible_factor g
          (Polynomial.not_isUnit_of_natDegree_pos g hgpos)
      obtain ⟨r, hgr⟩ := hqg
      have hrmonic : r.Monic := by
        apply hqmonic.of_mul_monic_left
        rw [← hgr]
        exact hgmonic
      have hqdiv : q ∣ p := dvd_trans ⟨r, hgr⟩ hgp
      have hrdiv : r ∣ p := by
        apply dvd_trans ?_ hgp
        rw [hgr]
        exact dvd_mul_left r q
      have hgsep : g.Separable := hpsep.of_dvd hgp
      have hqr : IsCoprime q r := by
        apply Polynomial.Separable.isCoprime
        rw [← hgr]
        exact hgsep
      have hqpos : 0 < q.natDegree :=
        Polynomial.natDegree_pos_iff_degree_pos.mpr
          (Polynomial.degree_pos_of_irreducible hqirr)
      have hrlt : r.natDegree < d := by
        have hdeg : d = q.natDegree + r.natDegree := by
          calc
            d = g.natDegree := hgd.symm
            _ = (q * r).natDegree := by rw [hgr]
            _ = q.natDegree + r.natDegree :=
              Polynomial.natDegree_mul hqmonic.ne_zero hrmonic.ne_zero
        omega
      obtain ⟨eqv, hnorm⟩ :=
        adjoinRoot_norm_decompose_coprime K q r hqmonic hrmonic hqr
      let eg : AdjoinRoot g ≃ₐ[K] (AdjoinRoot q × AdjoinRoot r) :=
        (AdjoinRoot.algEquivOfEq K g (q * r) hgr).trans eqv
      let uq : (AdjoinRoot q)ˣ :=
        Units.map ((MonoidHom.fst _ _).comp eg.toMonoidHom) u
      let ur : (AdjoinRoot r)ˣ :=
        Units.map ((MonoidHom.snd _ _).comp eg.toMonoidHom) u
      obtain ⟨eq⟩ :=
        adjoinRoot_factor_equiv_chosenSimpleKummer K n hnK hmu a q
          hqmonic hqirr hqdiv
      let vq : Eˣ := Units.map eq.toMonoidHom uq
      obtain ⟨vr, hvr⟩ := ih r.natDegree hrlt r rfl hrmonic hrdiv ur
      have huq : Algebra.norm K (eg (u : AdjoinRoot g)).1 =
          Algebra.norm K (vq : E) := by
        change Algebra.norm K (eg (u : AdjoinRoot g)).1 =
          Algebra.norm K (eq (eg (u : AdjoinRoot g)).1)
        exact (Algebra.norm_eq_of_algEquiv eq _).symm
      have hur : Algebra.norm K (eg (u : AdjoinRoot g)).2 =
          Algebra.norm K (vr : E) := hvr
      refine ⟨vq * vr, ?_⟩
      calc
        Algebra.norm K (u : AdjoinRoot g) =
            Algebra.norm K (eg (u : AdjoinRoot g)).1 *
              Algebra.norm K (eg (u : AdjoinRoot g)).2 := by
          rw [show Algebra.norm K (u : AdjoinRoot g) =
            Algebra.norm K ((AdjoinRoot.algEquivOfEq K g (q * r) hgr)
              (u : AdjoinRoot g)) from
                (Algebra.norm_eq_of_algEquiv
                  (AdjoinRoot.algEquivOfEq K g (q * r) hgr) _).symm]
          exact hnorm _
        _ = Algebra.norm K (vq : E) * Algebra.norm K (vr : E) := by
          rw [huq, hur]
        _ = Algebra.norm K ((vq * vr : Eˣ) : E) := by
          simp only [Units.val_mul, map_mul]

/-- For the (possibly reducible) canonical Kummer algebra, the norm image on
units agrees with that of the chosen simple Kummer extension. -/
theorem adjoinRoot_norm_iff_chosenSimpleKummerNorm
    (K : Type) [Field K] (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    (∃ y : (AdjoinRoot
          (Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)))ˣ,
        Algebra.norm K
          (y : AdjoinRoot
            (Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K))) = (b : K)) ↔
      ∃ z : (KummerTheory.chosenSimpleKummerExtension K n hnK a)ˣ,
        Algebra.norm K
          (z : KummerTheory.chosenSimpleKummerExtension K n hnK a) = (b : K) := by
  let p : Polynomial K := Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)
  let E := KummerTheory.chosenSimpleKummerExtension K n hnK a
  obtain ⟨r, hrmonic, hrdiv, e, hnorm⟩ :=
    adjoinRoot_norm_decompose_chosenMinpoly K n hnK a
  change (∃ y : (AdjoinRoot p)ˣ, Algebra.norm K (y : AdjoinRoot p) = (b : K)) ↔
    ∃ z : Eˣ, Algebra.norm K (z : E) = (b : K)
  constructor
  · rintro ⟨y, hy⟩
    let t : (E × AdjoinRoot r)ˣ := Units.map e.toMonoidHom y
    let z : Eˣ := Units.map (MonoidHom.fst _ _) t
    let w : (AdjoinRoot r)ˣ := Units.map (MonoidHom.snd _ _) t
    obtain ⟨v, hv⟩ :=
      adjoinRoot_factor_norm_is_chosenSimpleKummerNorm K n hnK hmu a r
        hrmonic hrdiv w
    refine ⟨z * v, ?_⟩
    have hzw : Algebra.norm K (y : AdjoinRoot p) =
        Algebra.norm K (z : E) * Algebra.norm K (w : AdjoinRoot r) :=
      hnorm (y : AdjoinRoot p)
    calc
      Algebra.norm K ((z * v : Eˣ) : E) =
          Algebra.norm K (z : E) * Algebra.norm K (v : E) := by
            simp only [Units.val_mul, map_mul]
      _ = Algebra.norm K (y : AdjoinRoot p) := by rw [← hv, ← hzw]
      _ = (b : K) := hy
  · rintro ⟨z, hz⟩
    let t : (E × AdjoinRoot r)ˣ := MulEquiv.prodUnits.symm (z, 1)
    let y : (AdjoinRoot p)ˣ := Units.map e.symm.toMonoidHom t
    refine ⟨y, ?_⟩
    have het : e (y : AdjoinRoot p) = ((z : E), 1) := by
      calc
        e (y : AdjoinRoot p) = e (e.symm (t : E × AdjoinRoot r)) := rfl
        _ = (t : E × AdjoinRoot r) := e.apply_symm_apply _
        _ = ((z : E), 1) := rfl
    rw [hnorm (y : AdjoinRoot p), het]
    simpa only [map_one, mul_one] using hz

end LocalClassFieldTheory.Kummer
