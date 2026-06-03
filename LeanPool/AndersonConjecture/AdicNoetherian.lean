/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import LeanPool.AndersonConjecture.AdicKerEval

/-!
# Adic Completion of a Noetherian Local Ring is Noetherian

For a Noetherian local ring (R, M), the M-adic completion R-hat
is Noetherian. The key facts are that R-hat / M-hat^n is
isomorphic to R / M^n for each n, and that the completion is
M-adically complete, so the Noetherian property lifts by
successive approximation (Atiyah--Macdonald, Prop. 10.11).
-/

open AdicCompletion

open scoped Pointwise

variable {R : Type*} [CommRing R]

/-! ### Part 1: ker(evalₐ I n) = (map f I)ⁿ -/

section KernelEvalₐ

variable (I : Ideal R)

/- `(map f I)ⁿ ⊆ ker(evalₐ I n)`: elements from I^n evaluate to zero. -/
include R in lemma map_pow_le_ker_evalₐ (n : ℕ) :
    Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n) ≤
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  change (evalₐ I n) (of I R r) = 0
  rw [evalₐ_of]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hr

/- `ker(evalₐ M n) = M̂ⁿ` for Noetherian local R. -/
include R in lemma ker_evalₐ_eq [IsLocalRing R] [IsNoetherianRing R] (n : ℕ) :
    RingHom.ker (evalₐ (IsLocalRing.maximalIdeal R) n).toRingHom =
    Ideal.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))
      (IsLocalRing.maximalIdeal R) ^ n := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hx
    exact mem_map_pow_of_evalₐ_eq_zero R n x hx
  · rw [← Ideal.map_pow]
    exact map_pow_le_ker_evalₐ (IsLocalRing.maximalIdeal R) n

/- Evaluations are stable along Cauchy sequences. -/
include R in lemma eval_cauchy_stable (f : ℕ → AdicCompletion I R)
    (hf : ∀ {m n : ℕ}, m ≤ n →
      SModEq (I ^ m • (⊤ : Submodule R (AdicCompletion I R))) (f m) (f n))
    {k n : ℕ} (hkn : k ≤ n) :
    evalₐ I k (f n) = evalₐ I k (f k) := by
  have hmem := hf hkn
  rw [SModEq.sub_mem, Ideal.smul_top_eq_map] at hmem
  have := map_pow_le_ker_evalₐ I k hmem
  rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_sub, sub_eq_zero] at this
  exact this.symm

/- `factorPow ∘ evalₐ n = evalₐ m` for m ≤ n. -/
include R in lemma factorPow_comp_evalₐ_noeth {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hmn (evalₐ I n x) = evalₐ I m x := by
  apply induction_on I R
    (p := fun x => Ideal.Quotient.factorPow I hmn (evalₐ I n x) = evalₐ I m x) x
  intro a
  simp only [evalₐ_mk]
  have hfactor : Ideal.Quotient.factorPow I hmn (Ideal.Quotient.mk (I ^ n) (a.1 n)) =
      Ideal.Quotient.mk (I ^ m) (a.1 n) := by
    unfold Ideal.Quotient.factorPow
    simp [Ideal.Quotient.factor_mk]
  rw [hfactor]
  have hcauchy := a.2 hmn
  rw [SModEq.sub_mem] at hcauchy
  have hmem : a.1 m - a.1 n ∈ (I ^ m : Ideal R) := by
    rwa [show I ^ m • (⊤ : Submodule R R) = (I ^ m : Ideal R) by
           ext
           simp] at hcauchy
  rw [Ideal.Quotient.eq]
  rwa [show a.1 n - a.1 m = -(a.1 m - a.1 n) from by ring, neg_mem_iff]

end KernelEvalₐ

/-! ### Part 2: R̂/M̂ⁿ ≅ R/Mⁿ -/

section QuotientIso

variable [IsLocalRing R] [IsNoetherianRing R]

/-- `R̂ / M̂ⁿ ≅ R / Mⁿ` as rings. -/
noncomputable def quotientPowEquiv (n : ℕ) :
    AdicCompletion (IsLocalRing.maximalIdeal R) R ⧸
      (Ideal.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))
        (IsLocalRing.maximalIdeal R)) ^ n ≃+*
    R ⧸ (IsLocalRing.maximalIdeal R) ^ n := by
  have hker := ker_evalₐ_eq (R := R) n
  have hsurj := surjective_evalₐ (IsLocalRing.maximalIdeal R) n
  exact (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective hsurj)

end QuotientIso

/-! ### Part 3: IsPrecomplete M (AdicCompletion M R) -/

section Precomplete

variable [IsLocalRing R] [IsNoetherianRing R]

/-- The adic completion of a Noetherian local ring is M-adically precomplete. -/
instance adicCompletion_isPrecomplete :
    IsPrecomplete (IsLocalRing.maximalIdeal R)
      (AdicCompletion (IsLocalRing.maximalIdeal R) R) := by
  set M := IsLocalRing.maximalIdeal R
  constructor
  intro f hf
  -- For each k, pick r_k ∈ R with mkQ(M^k)(r_k) = evalₐ k (f k).
  choose r hr using fun k => Ideal.Quotient.mk_surjective
    (I := M ^ k) (evalₐ M k (f k))
  -- The sequence r is Cauchy: r k ≡ r (k+1) mod M^k.
  have hr_cauchy : ∀ k, r k ≡ r (k + 1) [SMOD M ^ k • (⊤ : Submodule R R)] := by
    intro k
    rw [SModEq.sub_mem, show M ^ k • (⊤ : Submodule R R) = (M ^ k : Ideal R) by
          ext
          simp]
    have h1 : (Ideal.Quotient.mk (M ^ k)) (r k) = evalₐ M k (f k) := hr k
    have h2 : (Ideal.Quotient.mk (M ^ (k + 1))) (r (k + 1)) = evalₐ M (k + 1) (f (k + 1)) :=
      hr (k + 1)
    have h3 : Ideal.Quotient.factorPow M (Nat.le_succ k) (evalₐ M (k + 1) (f (k + 1))) =
        evalₐ M k (f (k + 1)) := factorPow_comp_evalₐ_noeth M (Nat.le_succ k) (f (k + 1))
    have h4 : evalₐ M k (f (k + 1)) = evalₐ M k (f k) :=
      eval_cauchy_stable M f hf (Nat.le_succ k)
    have h5 : (Ideal.Quotient.mk (M ^ k)) (r (k + 1)) = (Ideal.Quotient.mk (M ^ k)) (r k) := by
      have hfp : Ideal.Quotient.factorPow M (Nat.le_succ k)
          ((Ideal.Quotient.mk (M ^ (k + 1))) (r (k + 1))) =
          (Ideal.Quotient.mk (M ^ k)) (r (k + 1)) := by
        unfold Ideal.Quotient.factorPow
        simp [Ideal.Quotient.factor_mk]
      rw [← hfp, h2, h3, h4, h1]
    have h6 : (Ideal.Quotient.mk (M ^ k)) (r k - r (k + 1)) = 0 := by
      rw [map_sub, h5, sub_self]
    rwa [Ideal.Quotient.eq_zero_iff_mem] at h6
  -- Construct the limit L ∈ R̂ from the Cauchy sequence r.
  let cauchy_seq := AdicCauchySequence.mk M R r hr_cauchy
  use mk M R cauchy_seq
  -- Show f n ≡ L mod M^n • ⊤ for all n.
  intro n
  rw [SModEq.sub_mem, Ideal.smul_top_eq_map]
  suffices h : f n - mk M R cauchy_seq ∈
      Ideal.map (algebraMap R (AdicCompletion M R)) (M ^ n) by exact h
  have : Ideal.map (algebraMap R (AdicCompletion M R)) (M ^ n) =
      Ideal.map (algebraMap R (AdicCompletion M R)) M ^ n := Ideal.map_pow _ _ _
  rw [this, ← ker_evalₐ_eq n]
  rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_sub, sub_eq_zero]
  change evalₐ M n (f n) = evalₐ M n (mk M R cauchy_seq)
  rw [evalₐ_mk]
  exact (hr n).symm

end Precomplete

/-! ### Part 4: Main theorem — IsNoetherianRing R̂ -/

section Main

variable (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Generic helper: build a recursive sequence with proof-carrying data.
This is a standalone `def` so its elaboration budget is independent. -/
noncomputable def buildAdicSeq {α : Type*} {P : ℕ → α → Prop}
    (base : { a // P 0 a })
    (step : ∀ K, { a // P K a } → { a // P (K + 1) a }) :
    ∀ K, { a // P K a } :=
  fun K => Nat.rec base (fun K prev => step K prev) K

/- Auxiliary: M * FN(n) ≤ FN(n+1) for the leading-term filtration FN. -/
omit [IsLocalRing R] [IsNoetherianRing R] in lemma filtration_smul_le
    (Mi : Ideal R) (J : Ideal (AdicCompletion Mi R))
    (FN : ℕ → Ideal R)
    (hFN_def : ∀ n, FN n = Mi ^ n ⊓ Ideal.comap (Ideal.Quotient.mk (Mi ^ (n + 1)))
      (Ideal.map (evalₐ Mi (n + 1)).toRingHom J))
    (n : ℕ) :
    Mi * FN n ≤ FN (n + 1) := by
  rw [Ideal.mul_le]
  intro m hm r hr_mem
  have hr_pow : r ∈ Mi ^ n := by rw [hFN_def] at hr_mem
                                 exact hr_mem.1
  have hr_comap : r ∈ Ideal.comap (Ideal.Quotient.mk (Mi ^ (n + 1)))
      (Ideal.map (evalₐ Mi (n + 1)).toRingHom J) := by rw [hFN_def] at hr_mem
                                                       exact hr_mem.2
  rw [hFN_def]
  refine ⟨?_, ?_⟩
  · rw [pow_succ']
    exact Ideal.mul_mem_mul hm hr_pow
  · obtain ⟨y, hyJ, hyr⟩ := (Ideal.mem_map_iff_of_surjective _
      (surjective_evalₐ Mi (n + 1))).mp hr_comap
    have hmyJ : of Mi R m * y ∈ J := J.mul_mem_left _ hyJ
    apply (Ideal.mem_map_iff_of_surjective _
      (surjective_evalₐ Mi (n + 1 + 1))).mpr
    refine ⟨of Mi R m * y, hmyJ, ?_⟩
    have hlhs : evalₐ Mi (n + 1 + 1) (of Mi R m * y) =
        Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) m * evalₐ Mi (n + 1 + 1) y := by
      simp [map_mul, evalₐ_of]
    rw [hlhs]
    have hfp_y : Ideal.Quotient.factorPow Mi (Nat.le_succ (n + 1))
        (evalₐ Mi (n + 1 + 1) y) = evalₐ Mi (n + 1) y :=
      factorPow_comp_evalₐ_noeth Mi (Nat.le_succ (n + 1)) y
    have hfp_r : Ideal.Quotient.factorPow Mi (Nat.le_succ (n + 1))
        (Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) r) =
        Ideal.Quotient.mk (Mi ^ (n + 1)) r := by
      unfold Ideal.Quotient.factorPow
      simp [Ideal.Quotient.factor_mk]
    have hdiff_quot : evalₐ Mi (n + 1 + 1) y - Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) r ∈
        RingHom.ker (Ideal.Quotient.factorPow Mi (Nat.le_succ (n + 1))) := by
      rw [RingHom.mem_ker, map_sub, hfp_y, hfp_r, hyr, sub_self]
    rw [show Ideal.Quotient.factorPow Mi (Nat.le_succ (n + 1)) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) from rfl,
      Ideal.Quotient.factor_ker] at hdiff_quot
    obtain ⟨s, hs, hseq⟩ := (Ideal.mem_map_iff_of_surjective _
      Ideal.Quotient.mk_surjective).mp hdiff_quot
    suffices h0 : Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) m *
        (evalₐ Mi (n + 1 + 1) y - Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) r) = 0 by
      have := h0
      rw [mul_sub] at this
      rw [show Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) m *
          Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) r =
          Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) (m * r) from by rw [← map_mul]] at this
      exact sub_eq_zero.mp this
    have hseq' : Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) s =
        evalₐ Mi (n + 1 + 1) y - Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) r := hseq
    rw [← hseq', ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    rw [show n + 1 + 1 = (n + 1).succ from rfl, pow_succ']
    exact Ideal.mul_mem_mul hm hs

/- Auxiliary: lift elements of Mi^K • FN(n0) to I₀ with evalₐ compatibility. -/
omit [IsLocalRing R] [IsNoetherianRing R] in lemma smul_lift_of_filtration
    (Mi : Ideal R)
    (n0 K : ℕ)
    (FN_n0 : Ideal R)
    (S_F : Finset R) (hS_F : Ideal.span ↑S_F = FN_n0)
    (I₀ : Ideal (AdicCompletion Mi R))
    (hlift_span : ∀ t : R, t ∈ (Ideal.span ↑S_F : Ideal R) →
        ∃ δ : AdicCompletion Mi R, δ ∈ I₀ ∧
        evalₐ Mi (n0 + 1) δ = Ideal.Quotient.mk (Mi ^ (n0 + 1)) t)
    (r' : R) (hr' : r' ∈ (Mi ^ K • (FN_n0 : Submodule R R) : Submodule R R)) :
    ∃ δ : AdicCompletion Mi R, δ ∈ I₀ ∧
      evalₐ Mi (n0 + K + 1) δ =
      Ideal.Quotient.mk (Mi ^ (n0 + K + 1)) r' := by
  refine Submodule.smul_induction_on hr' ?_ ?_
  · intro m hm s hs
    have hs_span : s ∈ (Ideal.span ↑S_F : Ideal R) :=
      hS_F ▸ hs
    obtain ⟨δ_s, hδ_s_I, hδ_s_eq⟩ := hlift_span s hs_span
    refine ⟨of Mi R m * δ_s, I₀.mul_mem_left _ hδ_s_I, ?_⟩
    rw [map_mul, evalₐ_of]
    have hdiff_ker : evalₐ Mi (n0 + K + 1) δ_s -
        Ideal.Quotient.mk (Mi ^ (n0 + K + 1)) s ∈
        RingHom.ker (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (show n0 + 1 ≤ n0 + K + 1 by omega))) := by
      rw [RingHom.mem_ker, map_sub,
        show Ideal.Quotient.factor _ (evalₐ Mi (n0 + K + 1) δ_s) =
          evalₐ Mi (n0 + 1) δ_s from factorPow_comp_evalₐ_noeth Mi (by omega) δ_s,
        hδ_s_eq, Ideal.Quotient.factor_mk, sub_self]
    rw [Ideal.Quotient.factor_ker] at hdiff_ker
    have hmk_kills : Ideal.Quotient.mk (Mi ^ (n0 + K + 1)) m *
        (evalₐ Mi (n0 + K + 1) δ_s -
          Ideal.Quotient.mk (Mi ^ (n0 + K + 1)) s) = 0 := by
      obtain ⟨q, hq_mem, hq_eq⟩ := (Ideal.mem_map_iff_of_surjective _
        Ideal.Quotient.mk_surjective).mp hdiff_ker
      rw [← hq_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_le_pow_right (by omega)
        (show m * q ∈ Mi ^ (K + (n0 + 1)) by
           rw [pow_add]
           exact Ideal.mul_mem_mul hm hq_mem)
    rw [mul_sub] at hmk_kills
    rw [sub_eq_zero.mp hmk_kills, show m • s = m * s from rfl, ← map_mul]
  · intro a b ⟨δa, hδaI, hδaeq⟩ ⟨δb, hδbI, hδbeq⟩
    exact ⟨δa + δb, I₀.add_mem hδaI hδbI, by rw [map_add, hδaeq, hδbeq, map_add]⟩

/- Auxiliary: per-generator coefficient decomposition for r' ∈ Mi^K • FN_n0. -/
omit [IsLocalRing R] [IsNoetherianRing R] in lemma coeff_decomp_of_smul
    (Mi : Ideal R)
    (n0 K : ℕ)
    (FN_n0 : Ideal R)
    (S_F : Finset R) (hS_F : Ideal.span ↑S_F = FN_n0)
    (genS : Finset (AdicCompletion Mi R))
    (I₀ : Ideal (AdicCompletion Mi R))
    (hI₀_eq : I₀ = Ideal.span (↑genS : Set (AdicCompletion Mi R)))
    (hlift_span : ∀ t : R, t ∈ (Ideal.span ↑S_F : Ideal R) →
        ∃ δ : AdicCompletion Mi R, δ ∈ I₀ ∧
        evalₐ Mi (n0 + 1) δ = Ideal.Quotient.mk (Mi ^ (n0 + 1)) t)
    (r' : R) (hr' : r' ∈ (Mi ^ K • (FN_n0 : Submodule R R) : Submodule R R)) :
    ∃ (c : AdicCompletion Mi R → AdicCompletion Mi R),
      (∀ g, g ∈ genS → c g ∈ (Ideal.map (algebraMap R (AdicCompletion Mi R)) Mi) ^ K) ∧
      evalₐ Mi (n0 + K + 1) (Finset.sum genS (fun g => c g * g)) =
      Ideal.Quotient.mk (Mi ^ (n0 + K + 1)) r' := by
  refine Submodule.smul_induction_on hr' ?_ ?_
  · intro m hm s hs
    obtain ⟨δ_s, hδ_s_I, hδ_s_eq⟩ := hlift_span s (hS_F ▸ hs)
    have hδ_s_span : δ_s ∈ Ideal.span (↑genS : Set (AdicCompletion Mi R)) :=
      hI₀_eq ▸ hδ_s_I
    obtain ⟨f, _, hf_sum⟩ := Submodule.mem_span_finset.mp hδ_s_span
    refine ⟨fun g => of Mi R m * f g,
      fun g _ => Ideal.mul_mem_right (f g) _
        (by
           rw [← Ideal.map_pow]
           exact Ideal.mem_map_of_mem _ hm), ?_⟩
    have hsum_eq : Finset.sum genS (fun g => (of Mi R m * f g) * g) = of Mi R m * δ_s := by
      have : Finset.sum genS (fun g => of Mi R m * f g * g) =
          of Mi R m * Finset.sum genS (fun g => f g * g) := by
        rw [Finset.mul_sum]
        congr 1
        ext g
        ring_nf
      rw [this, ← hf_sum]
      congr 1
    rw [hsum_eq, map_mul, evalₐ_of]
    have hdiff_ker : evalₐ Mi (n0 + K + 1) δ_s -
        Ideal.Quotient.mk (Mi ^ (n0 + K + 1)) s ∈
        RingHom.ker (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (show n0 + 1 ≤ n0 + K + 1 by omega))) := by
      rw [RingHom.mem_ker, map_sub,
        show Ideal.Quotient.factor _ (evalₐ Mi (n0 + K + 1) δ_s) =
          evalₐ Mi (n0 + 1) δ_s from factorPow_comp_evalₐ_noeth Mi (by omega) δ_s,
        hδ_s_eq, Ideal.Quotient.factor_mk, sub_self]
    rw [Ideal.Quotient.factor_ker] at hdiff_ker
    have hmk_kills : Ideal.Quotient.mk (Mi ^ (n0 + K + 1)) m *
        (evalₐ Mi (n0 + K + 1) δ_s -
          Ideal.Quotient.mk (Mi ^ (n0 + K + 1)) s) = 0 := by
      obtain ⟨q, hq_mem, hq_eq⟩ := (Ideal.mem_map_iff_of_surjective _
        Ideal.Quotient.mk_surjective).mp hdiff_ker
      rw [← hq_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_le_pow_right (by omega)
        (show m * q ∈ Mi ^ (K + (n0 + 1)) by
           rw [pow_add]
           exact Ideal.mul_mem_mul hm hq_mem)
    rw [mul_sub] at hmk_kills
    rw [sub_eq_zero.mp hmk_kills, show m • s = m * s from rfl, ← map_mul]
  · intro a b ⟨ca, hcaM, hcaeq⟩ ⟨cb, hcbM, hcbeq⟩
    refine ⟨fun g => ca g + cb g,
      fun g hg => ((Ideal.map (algebraMap R (AdicCompletion Mi R)) Mi) ^ K).add_mem
        (hcaM g hg) (hcbM g hg), ?_⟩
    have hexp : Finset.sum genS (fun g => (ca g + cb g) * g) =
        Finset.sum genS (fun g => ca g * g) + Finset.sum genS (fun g => cb g * g) := by
      simp only [add_mul, Finset.sum_add_distrib]
    rw [hexp, map_add, hcaeq, hcbeq, map_add]

/- Auxiliary: extract a representative r ∈ Mi^K • FN_n0 from e ∈ Mhat^(n0+K) ∩ J. -/
omit [IsLocalRing R] [IsNoetherianRing R] in lemma extract_filtration_rep
    (Mi : Ideal R) (J : Ideal (AdicCompletion Mi R))
    (FN : ℕ → Ideal R) (n0 K : ℕ)
    (hFN_def : ∀ n, FN n = Mi ^ n ⊓ Ideal.comap (Ideal.Quotient.mk (Mi ^ (n + 1)))
      (Ideal.map (evalₐ Mi (n + 1)).toRingHom J))
    (FN_n0_sub : Submodule R R)
    (hn0_pow : ∀ K, Mi ^ K • FN_n0_sub = (fun n => (FN n : Submodule R R)) (n0 + K))
    (Mhat : Ideal (AdicCompletion Mi R))
    (hker_eq : ∀ N, RingHom.ker (evalₐ Mi N).toRingHom = Mhat ^ N)
    (e : AdicCompletion Mi R) (he : e ∈ Mhat ^ (n0 + K)) (heJ : e ∈ J) :
    ∃ r : R, r ∈ (Mi ^ K • FN_n0_sub : Submodule R R) ∧
      evalₐ Mi (n0 + K + 1) e = Ideal.Quotient.mk (Mi ^ (n0 + K + 1)) r := by
  have he_ker : evalₐ Mi (n0 + K) e = 0 := by
    have : e ∈ RingHom.ker (evalₐ Mi (n0 + K)).toRingHom := hker_eq _ ▸ he
    rwa [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
  have he_factor : Ideal.Quotient.factorPow Mi (Nat.le_succ (n0 + K))
      (evalₐ Mi (n0 + K + 1) e) = 0 :=
    (factorPow_comp_evalₐ_noeth Mi (Nat.le_succ (n0 + K)) e).trans he_ker
  have he_in_map : evalₐ Mi (n0 + K + 1) e ∈
      Ideal.map (Ideal.Quotient.mk (Mi ^ (n0 + K + 1))) (Mi ^ (n0 + K)) := by
    have hfp : Ideal.Quotient.factorPow Mi (Nat.le_succ (n0 + K)) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n0 + K))) := rfl
    rw [hfp] at he_factor
    rwa [← Ideal.Quotient.factor_ker (Ideal.pow_le_pow_right (Nat.le_succ (n0 + K))),
      RingHom.mem_ker]
  obtain ⟨r, hr_pow, hr_eq⟩ := (Ideal.mem_map_iff_of_surjective _
    Ideal.Quotient.mk_surjective).mp he_in_map
  have hr_FN : r ∈ FN (n0 + K) := by
    rw [hFN_def]
    exact ⟨hr_pow, by change r ∈ Ideal.comap (Ideal.Quotient.mk (Mi ^ (n0 + K + 1)))
                        (Ideal.map (evalₐ Mi (n0 + K + 1)).toRingHom J)
                      rw [Ideal.mem_comap]
                      rw [hr_eq]
                      exact Ideal.mem_map_of_mem _ heJ⟩
  have hr_in_smul : r ∈ (Mi ^ K • FN_n0_sub : Submodule R R) := by
    rw [hn0_pow]
    exact (hFN_def (n0 + K) ▸ hr_FN : r ∈ (FN (n0 + K) : Submodule R R))
  exact ⟨r, hr_in_smul, hr_eq.symm⟩

/-- Every ideal of the adic completion of a Noetherian local ring is finitely generated. -/
private def adicCompletion_ideal_fg_proof : PLift (
    ∀ J : Ideal (AdicCompletion (IsLocalRing.maximalIdeal R) R), J.FG ) := ⟨by
  set Mi := IsLocalRing.maximalIdeal R
  intro J
  have hJ_img_fg : forall n, (Ideal.map (evalₐ Mi n).toRingHom J).FG := fun n =>
    (isNoetherianRing_iff_ideal_fg _).mp (Ideal.Quotient.isNoetherianRing _)
      (Ideal.map (evalₐ Mi n).toRingHom J)
  -- Leading-term filtration: FN(n) = M^n ∩ comap(mk(M^{n+1}), eval(n+1)(J))
  set FN : Nat -> Ideal R := fun n =>
    Mi ^ n ⊓ Ideal.comap (Ideal.Quotient.mk (Mi ^ (n + 1)))
      (Ideal.map (evalₐ Mi (n + 1)).toRingHom J)
  have hFN_def : ∀ n, FN n = Mi ^ n ⊓ Ideal.comap (Ideal.Quotient.mk (Mi ^ (n + 1)))
      (Ideal.map (evalₐ Mi (n + 1)).toRingHom J) := fun n => rfl
  have hFN_le : forall n, FN n ≤ Mi ^ n := fun n => inf_le_left
  have hFN_mono_sub : forall n, FN (n + 1) ≤ FN n := by
    intro n r ⟨hr1, hr2⟩
    refine ⟨Ideal.pow_le_pow_right (Nat.le_succ n) hr1, ?_⟩
    change Ideal.Quotient.mk (Mi ^ (n + 1)) r ∈ Ideal.map (evalₐ Mi (n + 1)).toRingHom J
    obtain ⟨y, hyJ, hyr⟩ := (Ideal.mem_map_iff_of_surjective _
      (surjective_evalₐ Mi (n + 1 + 1))).mp hr2
    refine (Ideal.mem_map_iff_of_surjective _
      (surjective_evalₐ Mi (n + 1))).mpr ⟨y, hyJ, ?_⟩
    have heval : evalₐ Mi (n + 1) y = Ideal.Quotient.mk (Mi ^ (n + 1)) r := by
      rw [← factorPow_comp_evalₐ_noeth Mi (Nat.le_succ (n + 1)) y]
      change Ideal.Quotient.factorPow Mi _ ((evalₐ Mi (n + 1 + 1)).toRingHom y) =
        Ideal.Quotient.mk (Mi ^ (n + 1)) r
      conv_lhs => rw [show (evalₐ Mi (n + 1 + 1)).toRingHom y =
        Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) r from hyr]
      rfl
    exact heval
  have hFN_smul_sub : forall n, Mi * FN n ≤ FN (n + 1) :=
    filtration_smul_le R Mi J FN hFN_def
  -- Build the Ideal.Filtration and prove stability
  have hFN_smul_R : forall n, Mi • (FN n : Submodule R R) ≤ (FN (n + 1) : Submodule R R) := by
    intro n
    rw [Ideal.smul_eq_mul]
    exact hFN_smul_sub n
  set F_filt : Mi.Filtration R :=
    { N := fun n => (FN n : Submodule R R)
      mono := fun n => hFN_mono_sub n
      smul_le := hFN_smul_R }
  have hF_le : F_filt ≤ Mi.stableFiltration ⊤ := by
    intro n x hx
    change x ∈ Mi ^ n • (⊤ : Submodule R R)
    rw [Ideal.smul_top_eq_map]
    exact Ideal.mem_map_of_mem _ (hFN_le n hx)
  haveI : Module.Finite R R := Module.Finite.self R
  have hF_stable : F_filt.Stable := (Ideal.stableFiltration_stable Mi ⊤).of_le hF_le
  -- Stability: ∃ n0, FN(n0+k) = M^k * FN(n0)
  obtain ⟨n0, hn0_pow⟩ := hF_stable.exists_pow_smul_eq
  obtain ⟨S_F, hS_F⟩ : (FN n0).FG := IsNoetherian.noetherian _
  obtain ⟨S_J, hS_J⟩ := hJ_img_fg n0
  have hS_J_lift : forall a, a ∈ S_J -> ∃ x : AdicCompletion Mi R, x ∈ J ∧
      evalₐ Mi n0 x = a := by
    intro a ha
    exact (Ideal.mem_map_iff_of_surjective _ (surjective_evalₐ Mi n0)).mp
      (hS_J ▸ Ideal.subset_span ha)
  have hS_F_lift : forall r, r ∈ S_F -> ∃ x : AdicCompletion Mi R, x ∈ J ∧
      evalₐ Mi (n0 + 1) x = Ideal.Quotient.mk (Mi ^ (n0 + 1)) r := by
    intro r hr
    have hmem : r ∈ FN n0 := hS_F ▸ Ideal.subset_span hr
    exact (Ideal.mem_map_iff_of_surjective _ (surjective_evalₐ Mi (n0 + 1))).mp hmem.2
  choose lJ hlJ_mem hlJ_eq using hS_J_lift
  choose lF hlF_mem hlF_eq using hS_F_lift
  classical
  set genJ := S_J.image (fun a => if h : a ∈ S_J then lJ a h else 0)
  set genF := S_F.image (fun r => if h : r ∈ S_F then lF r h else 0)
  refine ⟨genJ ∪ genF, le_antisymm ?_ ?_⟩
  · -- EASY DIRECTION: Ideal.span(genJ ∪ genF) ≤ J
    rw [Ideal.span_le]
    intro x hx
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hx
    rcases hx with hx | hx
    · rw [Finset.mem_image] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      rw [dif_pos ha]
      exact hlJ_mem a ha
    · rw [Finset.mem_image] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      rw [dif_pos hr]
      exact hlF_mem r hr
  · -- HARD DIRECTION: J ≤ Ideal.span ↑(genJ ∪ genF)
    -- It suffices to show ∀ x ∈ J, ∀ N, x ∈ I₀ + M̂^N, then conclude by Hausdorff.
    set I₀ := Ideal.span (↑(genJ ∪ genF) : Set (AdicCompletion Mi R))
    -- Successive approximation (Atiyah-Macdonald Prop 10.11 / Matsumura Thm 8.1).
    set Mhat := Ideal.map (algebraMap R (AdicCompletion Mi R)) Mi
    have hker_eq : ∀ N, RingHom.ker (evalₐ Mi N).toRingHom = Mhat ^ N :=
      fun N => ker_evalₐ_eq N
    have hI0_le_J : I₀ ≤ J := by
      rw [Ideal.span_le]
      intro z hz
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hz
      rcases hz with hz | hz
      · rw [Finset.mem_image] at hz
        obtain ⟨a, ha, rfl⟩ := hz
        rw [dif_pos ha]
        exact hlJ_mem a ha
      · rw [Finset.mem_image] at hz
        obtain ⟨r, hr, rfl⟩ := hz
        rw [dif_pos hr]
        exact hlF_mem r hr
    have hgenJ_sub : ∀ a ∈ S_J, (if h : a ∈ S_J then lJ a h else 0) ∈ I₀ := by
      intro a ha
      exact Ideal.subset_span (Finset.mem_coe.mpr
        (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)))
    have hgenF_sub : ∀ r ∈ S_F, (if h : r ∈ S_F then lF r h else 0) ∈ I₀ := by
      intro r hr
      exact Ideal.subset_span (Finset.mem_coe.mpr
        (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, hr, rfl⟩)))
    have hlift_span : ∀ t : R, t ∈ (Ideal.span ↑S_F : Ideal R) →
        ∃ δ : AdicCompletion Mi R, δ ∈ I₀ ∧
        evalₐ Mi (n0 + 1) δ = Ideal.Quotient.mk (Mi ^ (n0 + 1)) t := by
      intro t ht
      refine Submodule.closure_induction
        (p := fun t _ => ∃ δ : AdicCompletion Mi R, δ ∈ I₀ ∧
          evalₐ Mi (n0 + 1) δ = Ideal.Quotient.mk (Mi ^ (n0 + 1)) t)
        ?_ ?_ ?_ ht
      · -- zero
        exact ⟨0, I₀.zero_mem, by simp⟩
      · -- add
        intro _ _ _ _ ⟨δ1, hδ1I, hδ1eq⟩ ⟨δ2, hδ2I, hδ2eq⟩
        exact ⟨δ1 + δ2, I₀.add_mem hδ1I hδ2I, by rw [map_add, hδ1eq, hδ2eq, map_add]⟩
      · -- smul_mem: r • t with t ∈ S_F
        intro c t ht_mem
        have ht_fin : t ∈ S_F := Finset.mem_coe.mp ht_mem
        refine ⟨of Mi R c * (if h : t ∈ S_F then lF t h else 0),
          I₀.mul_mem_left _ (hgenF_sub t ht_fin), ?_⟩
        rw [dif_pos ht_fin, map_mul, evalₐ_of, hlF_eq t ht_fin]
        rw [show c • t = c * t from rfl, ← map_mul]
    -- Phase 1: ∀ K x ∈ J, x ∈ I₀ ⊔ Mhat^(n0 + K)
    suffices hphase1 : ∀ (K : ℕ) (x : AdicCompletion Mi R), x ∈ J →
        x ∈ I₀ ⊔ Mhat ^ (n0 + K) by
      -- Phase 2: Conclude J ≤ I₀
      intro x hx
      have happrox : ∀ N, x ∈ I₀ ⊔ Mhat ^ N := by
        intro N
        by_cases hN : n0 ≤ N
        · obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le hN
          exact hphase1 K x hx
        · push Not at hN
          have h0 := hphase1 0 x hx
          rw [Nat.add_zero] at h0
          exact sup_le_sup_left (Ideal.pow_le_pow_right (by omega)) I₀ h0
      -- Phase 2: show x ∈ I₀ via coefficient tracking + IsPrecomplete + IsHausdorff.
      have hstep : ∀ K (e : AdicCompletion Mi R),
          e ∈ Mhat ^ (n0 + K) → e ∈ J →
          ∃ (δ : AdicCompletion Mi R), δ ∈ I₀ ∧ δ ∈ Mhat ^ K ∧
          e - δ ∈ Mhat ^ (n0 + (K + 1)) := by
        intro K e he heJ
        obtain ⟨r, hr_in_smul, hr_eq⟩ := extract_filtration_rep R Mi J FN n0 K
          hFN_def (F_filt.N n0) (fun K => (hn0_pow K).symm) Mhat hker_eq e he heJ
        obtain ⟨δ, hδI, hδeq⟩ := smul_lift_of_filtration R Mi n0 K
          (FN n0) S_F hS_F I₀ hlift_span r hr_in_smul
        refine ⟨δ, hδI, ?_, ?_⟩
        · have he_K : e ∈ Mhat ^ K := Ideal.pow_le_pow_right (Nat.le_add_left K n0) he
          have herr : e - δ ∈ Mhat ^ (n0 + (K + 1)) := by
            rw [show n0 + (K + 1) = n0 + K + 1 from by omega, ← hker_eq,
              RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
              map_sub, hδeq, ← hr_eq, sub_self]
          have : δ = e - (e - δ) := by abel
          rw [this]
          exact (Mhat ^ K).sub_mem he_K (Ideal.pow_le_pow_right (by omega) herr)
        · rw [show n0 + (K + 1) = n0 + K + 1 from by omega, ← hker_eq,
              RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
              map_sub, hδeq, ← hr_eq, sub_self]
      -- Step 2: Build approximation sequence via Nat.rec on Sigma type.
      obtain ⟨y₀, hy₀, e₀, he₀, hxye₀⟩ := Submodule.mem_sup.mp (hphase1 0 x hx)
      rw [Nat.add_zero] at he₀
      have he₀sub : x - y₀ ∈ Mhat ^ n0 := by
        rwa [eq_sub_of_add_eq' hxye₀] at he₀
      let SeqPred (K : ℕ) (y : AdicCompletion Mi R) :=
        y ∈ I₀ ∧ x - y ∈ Mhat ^ (n0 + K) ∧ x - y ∈ J
      have baseData : { y // SeqPred 0 y } :=
        ⟨y₀, hy₀, by rwa [Nat.add_zero], J.sub_mem hx (hI0_le_J hy₀)⟩
      have stepData : ∀ K, { y // SeqPred K y } → { y // SeqPred (K + 1) y } :=
        fun K ⟨y_K, hy_K_I, hy_K_err, hy_K_J⟩ =>
        let hexists := hstep K (x - y_K) hy_K_err hy_K_J
        let δ := hexists.choose
        let hδ := hexists.choose_spec
        ⟨y_K + δ, I₀.add_mem hy_K_I hδ.1,
          by rw [show x - (y_K + δ) = (x - y_K) - δ from by abel]
             exact hδ.2.2,
          J.sub_mem hx (hI0_le_J (I₀.add_mem hy_K_I hδ.1))⟩
      let seqAll := buildAdicSeq baseData stepData
      set ySeq : ℕ → AdicCompletion Mi R := fun K => (seqAll K).1
      have hySeq_I₀ : ∀ K, ySeq K ∈ I₀ := fun K => (seqAll K).2.1
      have hySeq_err : ∀ K, x - ySeq K ∈ Mhat ^ (n0 + K) := fun K => (seqAll K).2.2.1
      have hySeq_diff : ∀ K, ySeq (K + 1) - ySeq K ∈ Mhat ^ K := by
        intro K
        have h1 := hySeq_err K
        have h2 := hySeq_err (K + 1)
        have hsub : ySeq (K + 1) - ySeq K = (x - ySeq K) - (x - ySeq (K + 1)) := by abel
        rw [hsub]
        apply (Mhat ^ K).sub_mem
        · exact Ideal.pow_le_pow_right (Nat.le_add_left K n0) h1
        · exact Ideal.pow_le_pow_right (by omega) h2
      have hMhat_mem_smul : ∀ K (z : AdicCompletion Mi R),
          z ∈ Mhat ^ K ↔ z ∈ Mi ^ K • (⊤ : Submodule R (AdicCompletion Mi R)) := by
        intro K z
        rw [Ideal.smul_top_eq_map, ← Ideal.map_pow, Submodule.restrictScalars_mem]
      -- Step 3: ySeq is Cauchy in the Mi-adic topology
      have hySeq_cauchy : ∀ {m n : ℕ}, m ≤ n →
          ySeq m ≡ ySeq n [SMOD (Mi ^ m • (⊤ : Submodule R (AdicCompletion Mi R)))] := by
        intro m n hmn
        rw [SModEq.sub_mem, ← hMhat_mem_smul]
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
        induction d with
        | zero => simp [sub_self, (Mhat ^ m).zero_mem]
        | succ d ih =>
          rw [show m + (d + 1) = (m + d) + 1 from by omega]
          have hsplit : ySeq m - ySeq ((m + d) + 1) =
            (ySeq m - ySeq (m + d)) + -(ySeq ((m + d) + 1) - ySeq (m + d)) := by abel
          rw [hsplit]
          exact (Mhat ^ m).add_mem (ih (Nat.le_add_right m d))
            ((Mhat ^ m).neg_mem
              (Ideal.pow_le_pow_right (Nat.le_add_right m d) (hySeq_diff (m + d))))
      -- Step 4: By IsPrecomplete, get limit L
      obtain ⟨L, hL⟩ := IsPrecomplete.prec (adicCompletion_isPrecomplete (R := R)) hySeq_cauchy
      -- Step 5: Show x = L by IsHausdorff
      have hxL : x = L := by
        apply (IsHausdorff.eq_iff_smodEq (I := Mi) (M := AdicCompletion Mi R)).mpr
        intro n
        rw [SModEq.sub_mem, ← hMhat_mem_smul]
        have h1 : x - ySeq n ∈ Mhat ^ n :=
          Ideal.pow_le_pow_right (Nat.le_add_left n n0) (hySeq_err n)
        have h2 : ySeq n - L ∈ Mhat ^ n := by
          rw [hMhat_mem_smul]
          exact SModEq.sub_mem.mp (hL n)
        rw [show x - L = (x - ySeq n) + (ySeq n - L) from by abel]
        exact (Mhat ^ n).add_mem h1 h2
      -- Step 6: Show L ∈ I₀ via per-generator Cauchy coefficient sequences.
      rw [hxL]
      have hySeq_diff_I₀ : ∀ K, ySeq (K + 1) - ySeq K ∈ I₀ :=
        fun K => I₀.sub_mem (hySeq_I₀ (K + 1)) (hySeq_I₀ K)
      let genS := genJ ∪ genF
      let sumG (f : AdicCompletion Mi R → AdicCompletion Mi R) :=
        Finset.sum genS (fun g => f g * g)
      have hstep_coeff : ∀ K (e : AdicCompletion Mi R),
          e ∈ Mhat ^ (n0 + K) → e ∈ J →
          ∃ (c : AdicCompletion Mi R → AdicCompletion Mi R),
            (∀ g, g ∈ genS → c g ∈ Mhat ^ K) ∧
            (e - sumG c) ∈ Mhat ^ (n0 + (K + 1)) := by
        intro K e he heJ
        obtain ⟨r, hr_in_smul, hr_eq⟩ := extract_filtration_rep R Mi J FN n0 K
          hFN_def (F_filt.N n0) (fun K => (hn0_pow K).symm) Mhat hker_eq e he heJ
        obtain ⟨c, hcM, hceq⟩ := coeff_decomp_of_smul R Mi n0 K (FN n0) S_F hS_F
          genS I₀ rfl hlift_span r hr_in_smul
        exact ⟨c, hcM, by
          rw [show n0 + (K + 1) = n0 + K + 1 from by omega, ← hker_eq,
            RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
            map_sub, hceq, ← hr_eq, sub_self]⟩
      -- Step 2: Auxiliary — sum of coeff * gen ∈ I₀
      have hsum_in_I₀ : ∀ (d : AdicCompletion Mi R → AdicCompletion Mi R),
          sumG d ∈ I₀ :=
        fun d => Ideal.sum_mem _ (fun g hg =>
          I₀.mul_mem_left (d g) (Ideal.subset_span (Finset.mem_coe.mpr hg)))
      -- Step 3: Build recursive coefficient sequence via buildAdicSeq
      let CSDPred (K : ℕ) (c : AdicCompletion Mi R → AdicCompletion Mi R) :=
        (x - y₀ - sumG c) ∈ Mhat ^ (n0 + K) ∧ (x - y₀ - sumG c) ∈ J
      have hsum_zero : sumG (fun _ => (0 : AdicCompletion Mi R)) = 0 := by
        simp only [sumG, zero_mul, Finset.sum_const_zero]
      have csd0 : { c // CSDPred 0 c } := ⟨fun _ => 0, by
        constructor
        · show x - y₀ - sumG (fun _ => 0) ∈ _
          rw [hsum_zero, sub_zero]
          rwa [Nat.add_zero]
        · show x - y₀ - sumG (fun _ => 0) ∈ _
          rw [hsum_zero, sub_zero]
          exact J.sub_mem hx (hI0_le_J hy₀)⟩
      let csdS : ∀ K, { c // CSDPred K c } → { c // CSDPred (K + 1) c } :=
        fun K ⟨c_K, hMK, hJK⟩ =>
        let d := (hstep_coeff K _ hMK hJK).choose
        let hd := (hstep_coeff K _ hMK hJK).choose_spec
        ⟨fun g => c_K g + d g, by
          have hsplit : Finset.sum genS (fun g => (c_K g + d g) * g) =
              sumG c_K + sumG d := by
            simp only [sumG, add_mul, Finset.sum_add_distrib]
          have hrw : x - y₀ - Finset.sum genS (fun g => (c_K g + d g) * g) =
              (x - y₀ - sumG c_K) - sumG d := by rw [hsplit]
                                                 abel
          exact ⟨by rw [hrw]
                    exact hd.2,
            by rw [hrw]
               exact J.sub_mem hJK (hI0_le_J (hsum_in_I₀ d))⟩⟩
      let csdAll := buildAdicSeq csd0 csdS
      let pc : ℕ → AdicCompletion Mi R → AdicCompletion Mi R := fun K => (csdAll K).1
      -- Step 4: Per-step bound: pc(K+1)(g) - pc(K)(g) ∈ Mhat^K
      have hpc_diff : ∀ K g, g ∈ genS →
          pc (K + 1) g - pc K g ∈ Mhat ^ K := by
        intro K g hg
        have hcs := hstep_coeff K _ (csdAll K).2.1 (csdAll K).2.2
        have hcsBound : ∀ g, g ∈ genS → hcs.choose g ∈ Mhat ^ K := hcs.choose_spec.1
        change (csdS K (csdAll K)).val g - (csdAll K).val g ∈ Mhat ^ K
        have key : ∀ (dat : { c // CSDPred K c }),
            (csdS K dat).val g - dat.val g =
            (hstep_coeff K _ dat.2.1 dat.2.2).choose g := by
          intro ⟨c_K, _, _⟩
          simp only [csdS, add_sub_cancel_left]
        rw [key]
        exact hcsBound g hg
      -- Step 5: Per-generator Cauchy
      have hpc_cauchy : ∀ g, g ∈ genS →
          ∀ {m n : ℕ}, m ≤ n →
          pc m g ≡ pc n g [SMOD (Mi ^ m • ⊤ : Submodule R (AdicCompletion Mi R))] := by
        intro g hg m n hmn
        rw [SModEq.sub_mem, ← hMhat_mem_smul]
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
        induction d with
        | zero => simp [sub_self, (Mhat ^ m).zero_mem]
        | succ d ih =>
          rw [show m + (d + 1) = (m + d) + 1 from by omega]
          have : pc m g - pc ((m + d) + 1) g =
            (pc m g - pc (m + d) g) + -(pc ((m + d) + 1) g - pc (m + d) g) := by abel
          rw [this]
          exact (Mhat ^ m).add_mem (ih (Nat.le_add_right m d))
            ((Mhat ^ m).neg_mem
              (Ideal.pow_le_pow_right (Nat.le_add_right m d) (hpc_diff (m + d) g hg)))
      -- Step 6: Get per-generator limits via IsPrecomplete
      have hpc_lim : ∀ g, g ∈ genS →
          ∃ cg, ∀ n,
            pc n g ≡ cg [SMOD (Mi ^ n • ⊤ :
              Submodule R (AdicCompletion Mi R))] :=
        fun g hg => IsPrecomplete.prec
          (adicCompletion_isPrecomplete (R := R))
          (hpc_cauchy g hg)
      let cLim : AdicCompletion Mi R → AdicCompletion Mi R :=
        fun g => if hg : g ∈ genS then (hpc_lim g hg).choose else 0
      have hcLim_spec : ∀ g, g ∈ genS → ∀ n,
          pc n g ≡ cLim g [SMOD (Mi ^ n • ⊤ : Submodule R (AdicCompletion Mi R))] := by
        intro g hg n
        simp only [cLim, dif_pos hg]
        exact (hpc_lim g hg).choose_spec n
      -- Step 7: L = y₀ + ∑ cLim(g) * g by Hausdorff, hence L ∈ I₀
      suffices hL_eq : L = y₀ + sumG cLim from
        hL_eq ▸ I₀.add_mem hy₀ (hsum_in_I₀ cLim)
      apply (IsHausdorff.eq_iff_smodEq (I := Mi) (M := AdicCompletion Mi R)).mpr
      intro n
      rw [SModEq.sub_mem, ← hMhat_mem_smul, ← hxL]
      have hsplit : x - (y₀ + sumG cLim) =
          (x - y₀ - sumG (pc n)) + Finset.sum genS (fun g => (pc n g - cLim g) * g) := by
        change x - (y₀ + Finset.sum genS (fun g => cLim g * g)) =
          (x - y₀ - Finset.sum genS (fun g => pc n g * g)) +
          Finset.sum genS (fun g => (pc n g - cLim g) * g)
        simp only [sub_mul, Finset.sum_sub_distrib]
        abel
      rw [hsplit]
      apply (Mhat ^ n).add_mem
      · exact Ideal.pow_le_pow_right (Nat.le_add_left n n0) (csdAll n).2.1
      · exact Ideal.sum_mem _ (fun g hg => Ideal.mul_mem_right _ _
          (by
             rw [hMhat_mem_smul]
             exact SModEq.sub_mem.mp (hcLim_spec g hg n)))
    -- Phase 1: induction on K
    intro K
    induction K with
    | zero =>
      intro x hx
      rw [Nat.add_zero]
      have heval_x : (evalₐ Mi n0).toRingHom x ∈ Ideal.map (evalₐ Mi n0).toRingHom J :=
        Ideal.mem_map_of_mem _ hx
      rw [← hS_J] at heval_x
      suffices hI0_surj : Ideal.map (evalₐ Mi n0).toRingHom I₀ = Ideal.span ↑S_J by
        have heval_in : (evalₐ Mi n0).toRingHom x ∈ Ideal.map (evalₐ Mi n0).toRingHom I₀ :=
          hI0_surj ▸ heval_x
        obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_iff_of_surjective _
          (surjective_evalₐ Mi n0)).mp heval_in
        refine Submodule.mem_sup.mpr ⟨y, hy, x - y, ?_, by abel⟩
        rw [← hker_eq, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          map_sub, sub_eq_zero]
        exact hyx.symm
      apply le_antisymm
      · rw [Ideal.map_span]
        apply Ideal.span_le.mpr
        intro a ha
        simp only [Set.mem_image, Finset.coe_union, Set.mem_union, Finset.mem_coe] at ha
        obtain ⟨g, hg, rfl⟩ := ha
        rcases hg with hg | hg
        · rw [Finset.mem_image] at hg
          obtain ⟨a, ha, rfl⟩ := hg
          rw [dif_pos ha, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
          rw [hlJ_eq a ha]
          exact Ideal.subset_span ha
        · rw [Finset.mem_image] at hg
          obtain ⟨r, hr, rfl⟩ := hg
          rw [dif_pos hr, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
          have hr_pow : r ∈ Mi ^ n0 := hFN_le n0 (hS_F ▸ Ideal.subset_span hr)
          have : (evalₐ Mi n0) (lF r hr) =
            Ideal.Quotient.factorPow Mi (Nat.le_succ n0) (evalₐ Mi (n0 + 1) (lF r hr)) :=
            (factorPow_comp_evalₐ_noeth Mi (Nat.le_succ n0) (lF r hr)).symm
          rw [this, hlF_eq r hr]
          have hfp_eq : Ideal.Quotient.factorPow Mi (Nat.le_succ n0) =
            Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n0)) := rfl
          rw [hfp_eq, Ideal.Quotient.factor_mk,
            Ideal.Quotient.eq_zero_iff_mem.mpr hr_pow]
          exact Ideal.zero_mem _
      · apply Ideal.span_le.mpr
        intro a ha
        have ha_fin : a ∈ S_J := ha
        exact (Ideal.mem_map_iff_of_surjective _ (surjective_evalₐ Mi n0)).mpr
          ⟨if h : a ∈ S_J then lJ a h else 0, hgenJ_sub a ha_fin, by
            rw [dif_pos ha_fin]
            exact hlJ_eq a ha_fin⟩
    | succ K ih =>
      intro x hx
      obtain ⟨y, hy, e, he, hxye⟩ := Submodule.mem_sup.mp (ih x hx)
      have he_sub : e = x - y := by rw [← hxye, add_sub_cancel_left]
      have heJ : e ∈ J := he_sub ▸ J.sub_mem hx (hI0_le_J hy)
      obtain ⟨r, hr_in_smul, hr_eq⟩ := extract_filtration_rep R Mi J FN n0 K
        hFN_def (F_filt.N n0) (fun K => (hn0_pow K).symm) Mhat hker_eq e he heJ
      obtain ⟨δ, hδI, hδeq⟩ := smul_lift_of_filtration R Mi n0 K (FN n0) S_F
        hS_F I₀ hlift_span r hr_in_smul
      have hsum : (y + δ) + (e - δ) = x := by
        rw [show y + δ + (e - δ) = y + e from by abel]
        exact hxye
      have hmem_ker : e - δ ∈ Mhat ^ (n0 + (K + 1)) := by
        rw [show n0 + (K + 1) = n0 + K + 1 from by omega, ← hker_eq,
          RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          map_sub, hδeq, ← hr_eq, sub_self]
      exact Submodule.mem_sup.mpr ⟨y + δ, I₀.add_mem hy hδI, e - δ, hmem_ker, hsum⟩
⟩

private lemma adicCompletion_ideal_fg :
    ∀ J : Ideal (AdicCompletion (IsLocalRing.maximalIdeal R) R), J.FG := by
  exact
    (adicCompletion_ideal_fg_proof
      R
    ).down
/-- The adic completion of a Noetherian local ring is Noetherian. -/
instance adicCompletion_isNoetherianRing :
    IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
  (isNoetherianRing_iff_ideal_fg _).mpr (adicCompletion_ideal_fg R)

end Main
