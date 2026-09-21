/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.FieldTheory.KummerExtension

/-!
# Eigencharacter descent in a cyclic Kummer extension

If a prime power of an element in `F(eta)`, with `eta ^ e = v`, lies in the base field and the
base contains a primitive `e`-th root of unity, the element has only one Kummer character.  The
proof constructs the root-scaling automorphism and compares coefficients in the canonical power
basis.  This is the generic descent needed before applying trace-curve Kummer-class independence
at primes dividing both cover exponents.
-/

open Polynomial AdjoinRoot

noncomputable section

universe u

namespace BGS.Algebra

variable {F : Type u} [Field F]

lemma kummerPowerBasis_eigenvector_eq_rootMonomial
    {e : ℕ} (he : 0 < e) {v ζ : F}
    (hζ : IsPrimitiveRoot ζ e)
    (T : AdjoinRoot (X ^ e - C v) →ₐ[F] AdjoinRoot (X ^ e - C v))
    (hTroot : T (AdjoinRoot.root (X ^ e - C v)) =
      algebraMap F (AdjoinRoot (X ^ e - C v)) ζ *
        AdjoinRoot.root (X ^ e - C v))
    (k : Fin (X ^ e - C v).natDegree) (z : AdjoinRoot (X ^ e - C v))
    (hz : T z = algebraMap F (AdjoinRoot (X ^ e - C v)) (ζ ^ (k : ℕ)) * z) :
    ∃ c : F, z = algebraMap F (AdjoinRoot (X ^ e - C v)) c *
      AdjoinRoot.root (X ^ e - C v) ^ (k : ℕ) := by
  let hmonic := monic_X_pow_sub_C v he.ne'
  let b := AdjoinRoot.powerBasisAux' hmonic
  have hpb (j : Fin (X ^ e - C v).natDegree) : b j =
      AdjoinRoot.root (X ^ e - C v) ^ (j : ℕ) := by
    change (AdjoinRoot.powerBasis' hmonic).basis j = _
    exact (AdjoinRoot.powerBasis' hmonic).basis_eq_pow j
  have hTbasis (j : Fin (X ^ e - C v).natDegree) :
      T (b j) = (ζ ^ (j : ℕ)) • b j := by
    rw [hpb, map_pow, hTroot, mul_pow, ← map_pow]
    simp only [Algebra.smul_def]
  have hTcoord (j : Fin (X ^ e - C v).natDegree) :
      b.repr (T z) j = ζ ^ (j : ℕ) * b.repr z j := by
    conv_lhs => rw [← b.sum_repr z]
    simp only [map_sum, map_smul, hTbasis, smul_smul]
    classical
    rw [Finset.sum_apply']
    change (∑ c, (((b.repr z c * ζ ^ (c : ℕ)) • b.repr (b c)) j)) = _
    rw [Finset.sum_eq_single j]
    · simp [mul_comm]
    · intro c _ hc
      simp [hc]
    · simp
  have hzcoord (j : Fin (X ^ e - C v).natDegree) :
      ζ ^ (j : ℕ) * b.repr z j =
        ζ ^ (k : ℕ) * b.repr z j := by
    have h := congrArg (fun w ↦ b.repr w j) hz
    rw [hTcoord] at h
    rw [← Algebra.smul_def] at h
    rw [map_smul] at h
    simpa using h
  let c := b.repr z k
  refine ⟨c, ?_⟩
  rw [← hpb]
  apply b.repr.injective
  ext j
  rw [← Algebra.smul_def]
  rw [map_smul]
  simp only [Finsupp.smul_apply, b.repr_self_apply]
  by_cases hjk : j = k
  · subst k
    simp [c]
  · have hpowers : ζ ^ (j : ℕ) ≠ ζ ^ (k : ℕ) := by
      intro hp
      apply hjk
      apply Fin.ext
      apply hζ.pow_inj
      · exact lt_of_lt_of_eq j.isLt natDegree_X_pow_sub_C
      · exact lt_of_lt_of_eq k.isLt natDegree_X_pow_sub_C
      · exact hp
    have hcoeff : b.repr z j = 0 := by
      have hmul : (ζ ^ (j : ℕ) - ζ ^ (k : ℕ)) * b.repr z j = 0 := by
        rw [sub_mul, hzcoord j, sub_self]
      exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hpowers)
    rw [hcoeff]
    simp [Ne.symm hjk]

/-- If a prime power of an element of a Kummer extension lies in the base field, then the
element occupies one residue character.  The exponent `k` satisfies the exact invariance
condition `e ∣ q*k`; no coprimality between `q` and `e` is assumed. -/
theorem exists_rootMonomial_of_primePower_mem_base
    {e q : ℕ} (he : 0 < e) {v ζ a : F}
    (hζ : IsPrimitiveRoot ζ e)
    (hirr : Irreducible (X ^ e - C v))
    (hq : q.Prime) (hqe : q ∣ e)
    (z : AdjoinRoot (X ^ e - C v))
    (hzq : z ^ q = algebraMap F (AdjoinRoot (X ^ e - C v)) a) :
    ∃ k < e, e ∣ q * k ∧ ∃ c : F,
      z = algebraMap F (AdjoinRoot (X ^ e - C v)) c *
        AdjoinRoot.root (X ^ e - C v) ^ k := by
  letI : Fact (Irreducible (X ^ e - C v)) := ⟨hirr⟩
  letI : NeZero e := ⟨he.ne'⟩
  let ζe : rootsOfUnity e F := rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one
  let T : AdjoinRoot (X ^ e - C v) →ₐ[F] AdjoinRoot (X ^ e - C v) :=
    autAdjoinRootXPowSubCHom e v ζe
  have hTroot : T (AdjoinRoot.root (X ^ e - C v)) =
      algebraMap F (AdjoinRoot (X ^ e - C v)) ζ *
        AdjoinRoot.root (X ^ e - C v) := by
    dsimp [T, autAdjoinRootXPowSubCHom]
    simp [ζe, rootsOfUnity.mkOfPowEq, Algebra.smul_def]
  by_cases hz : z = 0
  · refine ⟨0, he, by simp, 0, ?_⟩
    simp [hz]
  let s := e / q
  have hspos : 0 < s := by
    exact Nat.div_pos (Nat.le_of_dvd he hqe) hq.pos
  have hfactor : e = s * q := by
    exact (Nat.div_mul_cancel hqe).symm
  have hζqF : IsPrimitiveRoot (ζ ^ s) q := hζ.pow he hfactor
  have hζqL : IsPrimitiveRoot
      (algebraMap F (AdjoinRoot (X ^ e - C v)) (ζ ^ s)) q :=
    hζqF.map_of_injective (algebraMap F (AdjoinRoot (X ^ e - C v))).injective
  have hTpow : (T z) ^ q = z ^ q := by
    calc
      (T z) ^ q = T (z ^ q) := by rw [map_pow]
      _ = T (algebraMap F (AdjoinRoot (X ^ e - C v)) a) := by rw [hzq]
      _ = algebraMap F (AdjoinRoot (X ^ e - C v)) a := T.commutes a
      _ = z ^ q := hzq.symm
  have hratioPow : (T z / z) ^ q = 1 := by
    rw [div_pow, hTpow, div_self (pow_ne_zero q hz)]
  letI : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨m, hm, hmratio⟩ := hζqL.eq_pow_of_pow_eq_one hratioPow
  have hTz : T z =
      algebraMap F (AdjoinRoot (X ^ e - C v)) (ζ ^ (s * m)) * z := by
    calc
      T z = (T z / z) * z := (div_mul_cancel₀ (T z) hz).symm
      _ = (algebraMap F (AdjoinRoot (X ^ e - C v)) (ζ ^ s)) ^ m * z := by
        rw [hmratio]
      _ = algebraMap F (AdjoinRoot (X ^ e - C v)) ((ζ ^ s) ^ m) * z := by
        simp only [map_pow]
      _ = algebraMap F (AdjoinRoot (X ^ e - C v)) (ζ ^ (s * m)) * z := by
        rw [pow_mul]
  have hkmLt : s * m < e := by
    calc
      s * m < s * q := (Nat.mul_lt_mul_left hspos).2 hm
      _ = e := hfactor.symm
  have hdeg : (X ^ e - C v).natDegree = e := natDegree_X_pow_sub_C
  let kfin : Fin (X ^ e - C v).natDegree := ⟨s * m, by simpa [hdeg] using hkmLt⟩
  have hTzFin : T z =
      algebraMap F (AdjoinRoot (X ^ e - C v)) (ζ ^ (kfin : ℕ)) * z := hTz
  obtain ⟨c, hc⟩ := kummerPowerBasis_eigenvector_eq_rootMonomial
    he hζ T hTroot kfin z hTzFin
  refine ⟨s * m, hkmLt, ?_, c, hc⟩
  refine ⟨m, ?_⟩
  calc
    q * (s * m) = (s * q) * m := by ac_rfl
    _ = e * m := by rw [← hfactor]

end BGS.Algebra
