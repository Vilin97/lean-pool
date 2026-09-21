/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import LeanPool.NashEmbedding.NashEmbedding.Torus.Basic

/-!
# NashEmbedding: Realizable Metrics — Theorems

Closure properties, injective realization, flat torus, positive-definite metric closure,
and stability under perturbation.
-/

open scoped BigOperators ContDiff
open Matrix NashEmbedding.Sobolev

noncomputable section

namespace NashEmbedding

/-- Bridge lemma for the Mathlib v4.31 pin, where `Matrix` is a `def` (no longer `abbrev`).
`rw`'s syntactic matching no longer sees through Matrix, but `apply`/`exact`/`refine`
unify up to defeq — so a term-mode bridge closes the gap. Mirrors `continuous_matrix`. -/
@[fun_prop]
theorem contDiff_matrix {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ i j, ContDiff ℝ ∞ fun x => g x i j) : ContDiff ℝ ∞ g :=
  contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => h i j

/-! ## Closure properties of realizable metrics (Lemma 1.4) -/

/-
(i) Sum: if `g₁, g₂` are realizable, so is `g₁ + g₂`.
-/
theorem realizable_sum {n : ℕ}
    {g₁ g₂ : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (h₁ : IsRealizable g₁) (h₂ : IsRealizable g₂) :
    IsRealizable (g₁ + g₂) := by
      obtain ⟨ N₁, u₁, hsp₁, hreal₁ ⟩ := h₁

      obtain ⟨ N₂, u₂, hsp₂, hreal₂ ⟩ := h₂;
      refine' ⟨ N₁ + N₂, fun x => Fin.append ( u₁ x ) ( u₂ x ), _, _ ⟩;
      · constructor;
        · rw [ contDiff_pi ] at *;
          intro i; refine' Fin.addCases _ _ i <;> simp +decide [ * ] ;
          · exact fun i => contDiff_pi.1 hsp₁.smooth i;
          · exact fun i => hsp₂.smooth.comp ( contDiff_id ) |> ContDiff.comp ( contDiff_pi.1 contDiff_id i );
        · intro x k; have := hsp₁.periodic x k; have := hsp₂.periodic x k; aesop;
      · intro x i j;
        show _ = (g₁ x + g₂ x) i j
        rw [Matrix.add_apply]
        convert congr_arg₂ ( · + · ) ( hreal₁ x i j ) ( hreal₂ x i j ) using 1;
        unfold partialDeriv;
        rw [ fderiv_pi ];
        · simp +decide [ dotProduct, Fin.sum_univ_add ];
          rw [ fderiv_pi, fderiv_pi ];
          · congr! 2;
          · exact fun i => DifferentiableAt.comp x ( differentiableAt_pi.1 ( hsp₂.smooth.contDiffAt.differentiableAt ( by norm_num ) ) i ) ( differentiableAt_id );
          · exact fun i => DifferentiableAt.comp x ( differentiableAt_pi.1 ( hsp₁.smooth.contDiffAt.differentiableAt ( by norm_num ) ) i ) ( differentiableAt_id );
        · intro i; cases i using Fin.addCases <;> simp +decide [ *, Fin.append ] ;
          · exact DifferentiableAt.comp x ( differentiableAt_pi.1 ( hsp₁.smooth.contDiffAt.differentiableAt ( by norm_num ) ) _ ) ( differentiableAt_id );
          · exact DifferentiableAt.comp x ( differentiableAt_pi.1 ( hsp₂.smooth.contDiffAt.differentiableAt ( by norm_num ) ) _ ) ( differentiableAt_id )

/-
(ii) Non-negative scaling: if `g` is realizable and `t ≥ 0`, then `t • g` is realizable.
-/
theorem realizable_nonneg_smul {n : ℕ}
    {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hg : IsRealizable g) (ht : 0 ≤ t) :
    IsRealizable (t • g) := by
      -- Given `IsRealizable g` and `t ≥ 0`, obtain `N, u, hsp, hreal`. We claim `(fun x => Real.sqrt t • u x)` realizes `t • g`.
      obtain ⟨N, u, hsp, hreal⟩ := hg
      use N, fun x => Real.sqrt t • u x;
      constructor;
      · exact ⟨ by simpa using hsp.smooth.const_smul ( Real.sqrt t ), fun x k => by simp +decide [ hsp.periodic x k ] ⟩;
      · intro x i j; simp +decide [ Realizes, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, mul_comm, ht ] ;
        -- By definition of partial derivative, we have:
        have h_partial_deriv : ∀ i x, partialDeriv i (fun x => Real.sqrt t • u x) x = Real.sqrt t • partialDeriv i u x := by
          unfold partialDeriv;
          intro i x; erw [ fderiv_pi ] ; norm_num [ hsp.smooth.contDiffAt.differentiableAt ] ;
          · ext j; erw [ fderiv_mul ] <;> norm_num [ hsp.smooth.contDiffAt.differentiableAt ] ;
            · rw [ fderiv_pi ] ; aesop;
              exact fun i => DifferentiableAt.comp x ( differentiableAt_pi.1 ( hsp.smooth.contDiffAt.differentiableAt ( by norm_num ) ) i ) ( differentiableAt_id );
            · exact DifferentiableAt.comp x ( differentiableAt_pi.1 ( hsp.smooth.contDiffAt.differentiableAt ( by norm_num ) ) j ) ( differentiableAt_id );
          · exact fun i => DifferentiableAt.mul ( differentiableAt_const _ ) ( differentiableAt_pi.1 ( hsp.smooth.contDiffAt.differentiableAt ( by norm_num ) ) i );
        simp_all +decide [ Realizes, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, mul_comm, ht ];
        simp +decide only [← mul_assoc, Real.mul_self_sqrt ht, ← hreal, Finset.mul_sum _ _ _]

/-
(iii) Translation: if `g` is realizable and `y ∈ ℝⁿ`, then `τ_y g` is realizable.
-/
theorem realizable_translate {n : ℕ}
    {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {y : Fin n → ℝ}
    (hg : IsRealizable g) :
    IsRealizable (translate y g) := by
      obtain ⟨ N, u, hu, h ⟩ := hg;
      refine' ⟨ N, fun x => u ( x - y ), _, _ ⟩;
      · constructor;
        · exact hu.1.comp ( contDiff_id.sub contDiff_const );
        · intro x k; have := hu.2 ( x - y ) k; simp_all +decide [ sub_eq_add_neg, add_assoc ] ;
          simpa only [ add_comm, add_left_comm, add_assoc ] using this;
      · intro x i j;
        change _ = g (x - y) i j
        convert h ( x - y ) i j using 1;
        unfold partialDeriv;
        erw [ fderiv_comp ] <;> norm_num [ hu.smooth.contDiffAt.differentiableAt ];
        erw [ fderiv_sub_const ] ; norm_num

/-
(iv) Finite positive combinations of translates.
-/
theorem realizable_finComb {n M : ℕ}
    {g : Fin M → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {t : Fin M → ℝ} {y : Fin M → (Fin n → ℝ)}
    (hg : ∀ α, IsRealizable (g α))
    (ht : ∀ α, 0 ≤ t α) :
    IsRealizable (∑ α : Fin M, t α • translate (y α) (g α)) := by
      induction' M with M ih <;> simp_all +decide [ Fin.sum_univ_castSucc ];
      · use 0
        use fun _ => 0
        simp [Realizes];
        constructor <;> norm_num [ IsPeriodic2Pi ];
        exact contDiff_const;
      · exact realizable_sum ( ih ( fun α => hg _ ) ( fun α => ht _ ) ) ( realizable_nonneg_smul ( realizable_translate ( hg _ ) ) ( ht _ ) )

/-! ## Injective realization theorems -/

/-
Injective realization forces positive definiteness (Lemma 1.7).
-/
theorem injRealizable_posDef {n : ℕ}
    {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : IsInjRealizable g) : IsPosDefSmoothMetric g := by
      obtain ⟨ N, u, hu, hu' ⟩ := hg;
      constructor;
      · have := hu.smoothPeriodic.smooth;
        constructor;
        · have h_smooth : ∀ i j, ContDiff ℝ ∞ (fun x => dotProduct (partialDeriv i u x) (partialDeriv j u x)) := by
            intro i j;
            have h_smooth : ContDiff ℝ ∞ (fun x => fderiv ℝ u x (Pi.single i 1)) ∧ ContDiff ℝ ∞ (fun x => fderiv ℝ u x (Pi.single j 1)) := by
              have h_smooth : ContDiff ℝ ∞ (fun x => fderiv ℝ u x) := by
                fun_prop;
              exact ⟨ h_smooth.clm_apply ( contDiff_const ), h_smooth.clm_apply ( contDiff_const ) ⟩;
            exact ContDiff.sum fun _ _ => ContDiff.mul ( h_smooth.1.comp ( contDiff_id ) |> ContDiff.comp ( contDiff_pi.1 contDiff_id _ ) ) ( h_smooth.2.comp ( contDiff_id ) |> ContDiff.comp ( contDiff_pi.1 contDiff_id _ ) );
          apply contDiff_matrix
          intro i j
          have eq : (fun x => g x i j) = fun x => dotProduct (partialDeriv i u x) (partialDeriv j u x) :=
            funext fun x => (hu' x i j).symm
          rw [eq]
          exact h_smooth i j
        · intro x k; ext i j; have := hu.smoothPeriodic.periodic x k; simp_all +decide [ Realizes ] ;
          rw [ ← hu' ( x + periodicShift n k ) i j, ← hu' x i j ];
          have h_periodic_deriv : ∀ i, fderiv ℝ u (x + periodicShift n k) (Pi.single i 1) = fderiv ℝ u x (Pi.single i 1) := by
            have h_periodic_deriv : ∀ i, fderiv ℝ u (x + periodicShift n k) (Pi.single i 1) = fderiv ℝ (fun y => u (y + periodicShift n k)) x (Pi.single i 1) := by
              intro i; erw [ fderiv_comp x ] <;> norm_num [ this, hu.smoothPeriodic.smooth.contDiffAt.differentiableAt ] ;
            have h_periodic_deriv : ∀ i, fderiv ℝ (fun y => u (y + periodicShift n k)) x (Pi.single i 1) = fderiv ℝ u x (Pi.single i 1) := by
              intro i; rw [ show ( fun y => u ( y + periodicShift n k ) ) = u from funext fun y => hu.smoothPeriodic.periodic y k ] ;
            aesop;
          exact congr_arg₂ _ ( h_periodic_deriv i ) ( h_periodic_deriv j );
      · intro x
        have h_pos_def : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * v j * (g x) i j := by
          intro v hv_ne_zero
          have h_sum : ∑ i, ∑ j, v i * v j * g x i j = ∑ k, (∑ i, v i * partialDeriv i u x k) ^ 2 := by
            simp +decide only [← hu' x, dotProduct, Finset.mul_sum _ _ _, pow_two, mul_comm, mul_left_comm];
            exact Eq.symm ( by rw [ Finset.sum_comm ] ; exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
          -- Since $v \neq 0$, there exists some $k$ such that $\sum_{i} v_i \partial_i u(x)_k \neq 0$.
          obtain ⟨k, hk⟩ : ∃ k, ∑ i, v i * partialDeriv i u x k ≠ 0 := by
            have := hu.fullRank x;
            rw [ Fintype.linearIndependent_iff ] at this;
            contrapose! this;
            exact ⟨ v, by ext k; simpa [ mul_comm ] using this k, Function.ne_iff.mp hv_ne_zero ⟩;
          exact h_sum.symm ▸ lt_of_lt_of_le ( by positivity ) ( Finset.single_le_sum ( fun k _ => sq_nonneg ( ∑ i, v i * partialDeriv i u x k ) ) ( Finset.mem_univ k ) );
        constructor;
        · ext i j; have := hu' x i j; have := hu' x j i; simp_all +decide [ dotProduct, mul_comm ] ;
        · intro v hv; specialize h_pos_def v; simp_all +decide [ Finsupp.sum_fintype, mul_assoc, mul_comm, mul_left_comm ] ;

/-
Helper: partial derivative of concat projects to partial derivative of first component.
-/
lemma partialDeriv_concat_castAdd {n N₁ N₂ : ℕ}
    {u₁ : (Fin n → ℝ) → (Fin N₁ → ℝ)} {u₂ : (Fin n → ℝ) → (Fin N₂ → ℝ)}
    (hd₁ : ContDiff ℝ ∞ u₁) (hd₂ : ContDiff ℝ ∞ u₂)
    (i : Fin n) (x : Fin n → ℝ) (j : Fin N₁) :
    partialDeriv i (fun x => Fin.append (u₁ x) (u₂ x)) x (Fin.castAdd N₂ j) =
    partialDeriv i u₁ x j := by
      unfold partialDeriv;
      rw [ fderiv_pi, fderiv_pi ];
      · simp +decide [ Fin.append ];
      · exact fun i => DifferentiableAt.comp x ( differentiableAt_pi.1 ( hd₁.contDiffAt.differentiableAt ( by norm_num ) ) i ) ( differentiableAt_id );
      · intro i; refine' Fin.addCases _ _ i <;> simp +decide [ *, Fin.append ] ;
        · exact fun i => DifferentiableAt.comp x ( differentiableAt_pi.1 ( hd₁.contDiffAt.differentiableAt ( by norm_num ) ) i ) ( differentiableAt_id );
        · exact fun i => DifferentiableAt.comp x ( differentiableAt_pi.1 ( hd₂.contDiffAt.differentiableAt ( by norm_num ) ) i ) ( differentiableAt_id )

/-
Helper: linear independence is preserved by Fin.append (projecting to first component).
-/
lemma linearIndependent_of_append_proj {n N₁ N₂ : ℕ}
    {f₁ : Fin n → Fin N₁ → ℝ} {f₂ : Fin n → Fin N₂ → ℝ}
    (hli : LinearIndependent ℝ f₁) :
    LinearIndependent ℝ (fun i => Fin.append (f₁ i) (f₂ i)) := by
      convert Fintype.linearIndependent_iff.mpr _;
      exact Fin.fintype n;
      intro g hg i;
      rw [ Fintype.linearIndependent_iff ] at hli;
      exact hli g ( by ext j; simpa using congr_fun hg ( Fin.castAdd N₂ j ) ) i

/-
Helper: partial derivative of concat equals Fin.append of partial derivatives.
-/
lemma partialDeriv_concat {n N₁ N₂ : ℕ}
    {u₁ : (Fin n → ℝ) → (Fin N₁ → ℝ)} {u₂ : (Fin n → ℝ) → (Fin N₂ → ℝ)}
    (hd₁ : ContDiff ℝ ∞ u₁) (hd₂ : ContDiff ℝ ∞ u₂)
    (i : Fin n) (x : Fin n → ℝ) :
    partialDeriv i (fun x => Fin.append (u₁ x) (u₂ x)) x =
    Fin.append (partialDeriv i u₁ x) (partialDeriv i u₂ x) := by
      unfold partialDeriv;
      rw [ fderiv_pi ];
      · ext j;
        refine' Fin.addCases _ _ j <;> simp +decide [ Fin.append ];
        · intro k; rw [ fderiv_pi ] ; aesop;
          exact fun i => DifferentiableAt.comp x ( differentiableAt_pi.1 ( hd₁.contDiffAt.differentiableAt ( by norm_num ) ) i ) ( differentiableAt_id );
        · intro k; rw [ fderiv_pi ] ; aesop;
          exact fun i => DifferentiableAt.comp x ( differentiableAt_pi.1 ( hd₂.contDiffAt.differentiableAt ( by norm_num ) ) i ) ( differentiableAt_id );
      · intro k; refine' Fin.addCases _ _ k <;> simp +decide [ *, Fin.append ] ;
        · exact fun i => DifferentiableAt.comp x ( differentiableAt_pi.1 ( hd₁.contDiffAt.differentiableAt ( by norm_num ) ) i ) ( differentiableAt_id );
        · exact fun i => DifferentiableAt.comp x ( differentiableAt_pi.1 ( hd₂.contDiffAt.differentiableAt ( by norm_num ) ) i ) ( differentiableAt_id )

/-
Promotion lemma (Lemma 1.8): if `g₁` is injectively realizable and `g₂`
  is realizable, then `g₁ + g₂` is injectively realizable.
-/
theorem injRealizable_promotion {n : ℕ}
    {g₁ g₂ : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (h₁ : IsInjRealizable g₁) (h₂ : IsRealizable g₂) :
    IsInjRealizable (g₁ + g₂) := by
      -- Obtain `N₁, u₁, ⟨hsp₁, hinj₁, hfr₁⟩, hreal₁` from `h₁` and `N₂, u₂, hsp₂, hreal₂` from `h₂`.
      obtain ⟨N₁, u₁, ⟨hsp₁, hinj₁, hfr₁⟩, hreal₁⟩ := h₁
      obtain ⟨N₂, u₂, hsp₂, hreal₂⟩ := h₂
      use N₁ + N₂, fun x => Fin.append (u₁ x) (u₂ x);
      refine' ⟨ ⟨ _, _, _ ⟩, _ ⟩;
      · constructor;
        · have := hsp₁.smooth;
          have := hsp₂.smooth;
          rw [ contDiff_pi ] at *;
          intro i; refine' Fin.addCases _ _ i <;> simp +decide [ * ] ;
        · intro x k; simp +decide [ hsp₁.periodic, hsp₂.periodic ] ;
          rw [ hsp₁.periodic, hsp₂.periodic ];
      · intro x y hxy; specialize hinj₁ x y; simp_all +decide [ funext_iff, Fin.append ] ;
        exact hinj₁ fun i => by simpa using hxy ( Fin.castAdd N₂ i ) ;
      · intro x;
        convert linearIndependent_of_append_proj ( hfr₁ x ) using 1;
        exact funext fun i => partialDeriv_concat hsp₁.smooth hsp₂.smooth i x;
      · intro x i j;
        show _ = (g₁ x + g₂ x) i j
        rw [Matrix.add_apply]
        convert congr_arg₂ ( · + · ) ( hreal₁ x i j ) ( hreal₂ x i j ) using 1;
        rw [ partialDeriv_concat, partialDeriv_concat ];
        · simp +decide [ Fin.sum_univ_add, dotProduct ];
        · exact hsp₁.smooth;
        · exact hsp₂.smooth;
        · exact hsp₁.smooth;
        · exact hsp₂.smooth

/-! ## The flat-torus embedding (Lemma 1.10) -/

/-
The flat metric is a positive-definite smooth metric.
-/
theorem flatMetric_isPosDefSmoothMetric {n : ℕ} :
    IsPosDefSmoothMetric (flatMetric n) := by
      constructor;
      · constructor;
        · exact contDiff_const;
        · exact fun _ _ => rfl;
      · exact fun x => Matrix.PosDef.one

/-
The flat-torus embedding is smooth and 2πℤⁿ-periodic.
-/
theorem flatTorusEmb_smoothPeriodic {n : ℕ} :
    SmoothPeriodic (flatTorusEmb n) := by
      constructor;
      · refine' contDiff_pi.mpr _;
        intro i
        simp [flatTorusEmb];
        split_ifs <;> [ exact ContDiff.cos ( contDiff_pi.1 contDiff_id _ ) ; exact ContDiff.sin ( contDiff_pi.1 contDiff_id _ ) ];
      · intro x k;
        ext i; unfold flatTorusEmb; simp +decide [ periodicShift ] ;
        split_ifs <;> simp +decide [ mul_comm ( 2 * Real.pi ) ]

/-
The flat-torus embedding is an injective embedding.
-/
theorem flatTorusEmb_isInjectiveEmbedding {n : ℕ} :
    IsInjectiveEmbedding (flatTorusEmb n) := by
      refine' ⟨ flatTorusEmb_smoothPeriodic, _, _ ⟩;
      · intro x y hxy
        have h_cos_sin : ∀ i : Fin n, Real.cos (x i) = Real.cos (y i) ∧ Real.sin (x i) = Real.sin (y i) := by
          intro i
          have h_cos : Real.cos (x i) = Real.cos (y i) := by
            convert congr_fun hxy ( Fin.mk ( 2 * i ) ( by linarith [ Fin.is_lt i ] ) ) using 1 <;> norm_num [ flatTorusEmb ]
          have h_sin : Real.sin (x i) = Real.sin (y i) := by
            have := congr_fun hxy ⟨ 2 * i + 1, by linarith [ Fin.is_lt i ] ⟩ ; simp_all +decide [ flatTorusEmb ] ;
            convert this using 2 <;> norm_num [ Nat.add_div ]
          exact ⟨h_cos, h_sin⟩
        have h_eq : ∀ i : Fin n, ∃ k : ℤ, x i - y i = 2 * Real.pi * k := by
          intro i
          have h_eq : Real.cos (x i - y i) = 1 ∧ Real.sin (x i - y i) = 0 := by
            simp_all +decide [ Real.cos_sub, Real.sin_sub ];
            exact ⟨ by rw [ ← sq, ← sq, Real.cos_sq_add_sin_sq ], by ring ⟩
          generalize_proofs at *;
          rw [ Real.cos_eq_one_iff, Real.sin_eq_zero_iff ] at h_eq; obtain ⟨ k₁, hk₁ ⟩ := h_eq.1; obtain ⟨ k₂, hk₂ ⟩ := h_eq.2; exact ⟨ k₁, by linarith ⟩ ;
        generalize_proofs at *;
        choose k hk using h_eq; use k; ext i; simp +decide [ hk, periodicShift ] ;
      · intro x
        have h_deriv : ∀ i : Fin n, partialDeriv i (flatTorusEmb n) x = fun k => if k.val = 2 * i.val then -Real.sin (x i) else if k.val = 2 * i.val + 1 then Real.cos (x i) else 0 := by
          unfold partialDeriv
          generalize_proofs at *;
          intro i
          have h_deriv : ∀ k : Fin (2 * n), (fderiv ℝ (fun x => flatTorusEmb n x k) x) (Pi.single i 1) = if k.val = 2 * i.val then -Real.sin (x i) else if k.val = 2 * i.val + 1 then Real.cos (x i) else 0 := by
            intro k
            have h_deriv : (fderiv ℝ (fun x => flatTorusEmb n x k) x) (Pi.single i 1) = deriv (fun t => flatTorusEmb n (x + Pi.single i t) k) 0 := by
              rw [ deriv ];
              rw [ show ( fun t => flatTorusEmb n ( x + Pi.single i t ) k ) = ( fun x => flatTorusEmb n x k ) ∘ ( fun t => x + Pi.single i t ) by ext; rfl, fderiv_comp ] <;> norm_num [ fderiv_apply_one_eq_deriv ];
              · rw [ deriv_pi ] <;> norm_num [ Finset.sum_apply, Pi.single_apply ];
                · congr ; ext j ; aesop;
                · exact fun j => by split_ifs <;> norm_num;
              · unfold flatTorusEmb; norm_num [ Real.differentiableAt_sin, Real.differentiableAt_cos ] ;
                split_ifs <;> [ exact DifferentiableAt.cos ( differentiableAt_pi.1 differentiableAt_id _ ) ; exact DifferentiableAt.sin ( differentiableAt_pi.1 differentiableAt_id _ ) ];
              · intro j; by_cases h : j = i <;> simp +decide [ h, Pi.single_apply ] ;
            generalize_proofs at *;
            split_ifs <;> simp_all +decide [ flatTorusEmb ];
            · norm_num [ Real.cos_add ];
            · norm_num [ Nat.add_div, Pi.single_apply ];
              norm_num [ add_comm ];
            · simp_all +decide [ Fin.ext_iff, Pi.single_apply ];
              split_ifs <;> norm_num [ Nat.add_mod, Nat.mul_mod ] at * <;> omega
          generalize_proofs at *;
          rw [ fderiv_pi ];
          · exact funext fun k => h_deriv k ▸ rfl;
          · intro k; unfold flatTorusEmb; split_ifs <;> norm_num [ Real.differentiableAt_sin, Real.differentiableAt_cos ] ;
            · fun_prop (disch := norm_num);
            · fun_prop (disch := norm_num)
        generalize_proofs at *;
        refine' Fintype.linearIndependent_iff.2 _;
        intro g hg i; have := congr_fun hg ⟨ 2 * i, by linarith [ Fin.is_lt i ] ⟩ ; have := congr_fun hg ⟨ 2 * i + 1, by linarith [ Fin.is_lt i ] ⟩ ; simp_all +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ] ;
        simp_all +decide [ Finset.sum_filter, Fin.val_inj ];
        simp_all +decide [ Finset.sum_ite, Fin.val_inj, ne_of_apply_ne ( fun x => x % 2 ), Nat.add_mod, Nat.mul_mod ];
        cases this <;> cases ‹g i = 0 ∨ Real.sin ( x i ) = 0› <;> nlinarith [ Real.sin_sq_add_cos_sq ( x i ) ]

/-
The flat-torus embedding injectively realizes the flat metric.
-/
theorem flatTorusEmb_injRealizes {n : ℕ} :
    IsInjRealizable (flatMetric n) := by
      exact ⟨ _, _, flatTorusEmb_isInjectiveEmbedding, fun x i j => by
        unfold partialDeriv flatMetric flatTorusEmb;
        rw [ fderiv_pi ];
        · simp +decide [ Matrix.one_apply, dotProduct ];
          rw [ Finset.sum_eq_add ( ⟨ 2 * i, by linarith [ Fin.is_lt i ] ⟩ : Fin ( 2 * n ) ) ( ⟨ 2 * i + 1, by linarith [ Fin.is_lt i ] ⟩ : Fin ( 2 * n ) ) ] <;> norm_num;
          · erw [ fderiv_cos, fderiv_sin ] <;> norm_num;
            · erw [ HasFDerivAt.fderiv ( hasFDerivAt_apply _ _ ), HasFDerivAt.fderiv ( hasFDerivAt_apply _ _ ) ] ; norm_num;
              norm_num [ Nat.add_div, Pi.single_apply ];
              split_ifs <;> simp +decide [ *, ← sq ];
            · fun_prop;
            · exact differentiableAt_pi.1 differentiableAt_id _;
          · intro c hc₁ hc₂; split_ifs ;
            · erw [ fderiv_cos ] <;> norm_num;
              · erw [ HasFDerivAt.fderiv ( hasFDerivAt_apply _ _ ) ] ; norm_num;
                grind;
              · fun_prop;
            · erw [ fderiv_sin ] <;> norm_num;
              · erw [ HasFDerivAt.fderiv ( hasFDerivAt_apply _ _ ) ] ; norm_num [ Pi.single_apply ];
                grind;
              · fun_prop;
        · intro i; split_ifs <;> [ exact DifferentiableAt.cos ( differentiableAt_pi.1 differentiableAt_id _ ) ; exact DifferentiableAt.sin ( differentiableAt_pi.1 differentiableAt_id _ ) ] ; ⟩

/-! ## Closure of positive-definite metrics (Lemma 1.11) -/

/-
(i) Sum of positive-definite smooth metrics is positive-definite.
-/
theorem posDefSmoothMetric_add {n : ℕ}
    {g g' : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : IsPosDefSmoothMetric g) (hg' : IsPosDefSmoothMetric g') :
    IsPosDefSmoothMetric (g + g') := by
      constructor;
      · constructor;
        · apply contDiff_matrix
          intro i j
          have h1 : ContDiff ℝ ∞ fun x => g x i j :=
            contDiff_pi.1 (contDiff_pi.1 hg.smoothPeriodic.smooth i) j
          have h2 : ContDiff ℝ ∞ fun x => g' x i j :=
            contDiff_pi.1 (contDiff_pi.1 hg'.smoothPeriodic.smooth i) j
          have eq : (fun x => (g + g') x i j) = fun x => g x i j + g' x i j := by
            funext x; simp [Matrix.add_apply]
          rw [eq]
          exact h1.add h2
        · exact fun x k => by simp +decide [ hg.smoothPeriodic.periodic x k, hg'.smoothPeriodic.periodic x k ] ;
      · exact fun x => Matrix.PosDef.add ( hg.posDef x ) ( hg'.posDef x )

/-
(ii) Positive scaling of positive-definite smooth metric is positive-definite.
-/
theorem posDefSmoothMetric_pos_smul {n : ℕ}
    {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hg : IsPosDefSmoothMetric g) (ht : 0 < t) :
    IsPosDefSmoothMetric (t • g) := by
      constructor;
      · obtain ⟨ hg₁, hg₂ ⟩ := hg;
        constructor;
        · obtain ⟨ hg₁, hg₂ ⟩ := hg₁;
          apply contDiff_matrix
          intro i j
          have hg_ij : ContDiff ℝ ∞ fun x => g x i j :=
            contDiff_pi.1 (contDiff_pi.1 hg₁ i) j
          have eq : (fun x => (t • g) x i j) = fun x => t * g x i j := by
            funext x; simp [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
          rw [eq]
          exact contDiff_const.mul hg_ij
        · exact fun x k => by simp +decide [ hg₁.periodic x k ] ;
      · intro x;
        show (t • g x).PosDef
        exact Matrix.PosDef.smul ( hg.posDef x ) ht

/-! ## Stability of positive-definite metrics (Lemma 1.12) -/

/-
Stability under C⁰ perturbation (Lemma 1.12).
  Note: `h` takes values in symmetric matrices (`IsHermitian`), matching the LaTeX
  statement `h : ℝⁿ → Sym_n(ℝ)`.
-/
theorem posDefSmoothMetric_stability {n : ℕ}
    {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : IsPosDefSmoothMetric g) :
    ∃ η > 0, ∀ (h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ),
      Continuous h → IsPeriodic2Pi h →
      (∀ x, (h x).IsHermitian) →
      (∀ x, matOpNorm (h x) < η) →
      ∀ x, (g x + h x).PosDef := by
        -- Since $g$ is continuous and periodic, and values in the finite-dimensional matrix space, consider the image of $g$ restricted to $[0, 2\pi]^n$. By compactness, this is a compact set $K$ of PD matrices.
        obtain ⟨K, hK⟩ : ∃ K > 0, ∀ x : Fin n → ℝ, ∀ v : Fin n → ℝ, v ≠ 0 → K * ‖v‖ ^ 2 ≤ dotProduct v (Matrix.mulVec (g x) v) := by
          -- Since $g$ is continuous and periodic, and values in the finite-dimensional matrix space, consider the image of $g$ restricted to $[0, 2\pi]^n$. By compactness, this is a compact set $K$ of PD matrices. There exists $K > 0$ such that for all $x \in [0, 2\pi]^n$ and $v \neq 0$, $K * ‖v‖^2 ≤ dotProduct v (Matrix.mulVec (g x) v)$.
          have h_compact : ∃ K > 0, ∀ x ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi), ∀ v : Fin n → ℝ, v ≠ 0 → K * ‖v‖ ^ 2 ≤ dotProduct v (Matrix.mulVec (g x) v) := by
            -- By definition of $IsPosDefSmoothMetric$, $g(x)$ is positive definite for all $x$.
            have h_pos_def : ∀ x ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi), ∀ v : Fin n → ℝ, v ≠ 0 → 0 < dotProduct v (Matrix.mulVec (g x) v) := by
              have := hg.posDef;
              intro x hx v hv; specialize this x; have := this.2; simp_all +decide [ Matrix.IsHermitian, Matrix.mulVec ] ;
              convert this ( show ( Finsupp.equivFunOnFinite.symm v ) ≠ 0 from by simpa [ Finsupp.ext_iff, funext_iff ] using hv ) using 1
              · rfl
              · simp +decide [ dotProduct, Matrix.mulVec, Finsupp.sum_fintype, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm ]
                exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
            -- By definition of $IsPosDefSmoothMetric$, $g(x)$ is positive definite for all $x$, so we can apply the continuity of the quadratic form.
            have h_cont : ContinuousOn (fun (p : (Fin n → ℝ) × (Fin n → ℝ)) => dotProduct p.2 (Matrix.mulVec (g p.1) p.2) / ‖p.2‖ ^ 2) (Set.Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi) ×ˢ {v : Fin n → ℝ | ‖v‖ = 1}) := by
              refine' ContinuousOn.div _ _ _;
              · refine' Continuous.continuousOn _;
                have := hg.smoothPeriodic.smooth.continuous;
                fun_prop;
              · fun_prop;
              · aesop;
            by_cases hn : n = 0;
            · subst hn; exact ⟨ 1, by norm_num, by simp +decide [ funext_iff ] ⟩ ;
            · -- By definition of $IsPosDefSmoothMetric$, $g(x)$ is positive definite for all $x$, so we can apply the extreme value theorem to the continuous function on the compact set.
              obtain ⟨K, hK⟩ : ∃ K > 0, ∀ p ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi) ×ˢ {v : Fin n → ℝ | ‖v‖ = 1}, K ≤ dotProduct p.2 (Matrix.mulVec (g p.1) p.2) / ‖p.2‖ ^ 2 := by
                have h_extreme_value : ∃ p ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi) ×ˢ {v : Fin n → ℝ | ‖v‖ = 1}, ∀ q ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi) ×ˢ {v : Fin n → ℝ | ‖v‖ = 1}, dotProduct p.2 (Matrix.mulVec (g p.1) p.2) / ‖p.2‖ ^ 2 ≤ dotProduct q.2 (Matrix.mulVec (g q.1) q.2) / ‖q.2‖ ^ 2 := by
                  have h_compact : IsCompact (Set.Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi) ×ˢ {v : Fin n → ℝ | ‖v‖ = 1}) := by
                    exact isCompact_Icc.prod ( isCompact_sphere 0 1 |> fun h => h.of_isClosed_subset ( isClosed_eq continuous_norm continuous_const ) fun x hx => by simpa using hx );
                  have := h_compact.exists_isMinOn ⟨ ⟨ 0, fun _ => 1 ⟩, by
                    norm_num [ Norm.norm ];
                    exact ⟨ fun _ => by positivity, by exact le_antisymm ( Finset.sup_le fun _ _ => le_rfl ) ( Finset.le_sup ( f := fun _ => 1 ) ( Finset.mem_univ ⟨ 0, Nat.pos_of_ne_zero hn ⟩ ) ) ⟩ ⟩ h_cont
                  generalize_proofs at *;
                  exact ⟨ this.choose, this.choose_spec.1, fun q hq => this.choose_spec.2 hq ⟩;
                obtain ⟨ p, hp₁, hp₂ ⟩ := h_extreme_value;
                exact ⟨ p.2 ⬝ᵥ g p.1 *ᵥ p.2 / ‖p.2‖ ^ 2, div_pos ( h_pos_def p.1 hp₁.1 p.2 ( by rintro h; simpa [ h ] using hp₁.2 ) ) ( sq_pos_of_pos ( norm_pos_iff.mpr ( by rintro h; simpa [ h ] using hp₁.2 ) ) ), hp₂ ⟩;
              refine' ⟨ K, hK.1, fun x hx v hv => _ ⟩;
              have := hK.2 ( x, ‖v‖⁻¹ • v ) ⟨ hx, by simp +decide [ norm_smul, hv ] ⟩ ; simp_all +decide [ div_le_iff₀, norm_smul ] ;
              simp_all +decide [ Matrix.mulVec_smul, dotProduct_smul, mul_assoc, mul_comm, mul_left_comm, sq, norm_smul ];
              convert mul_le_mul_of_nonneg_right this ( mul_self_nonneg ‖v‖ ) using 1
              · rfl
              · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
                field_simp
          obtain ⟨ K, hK₀, hK ⟩ := h_compact; use K, hK₀; intro x v hv; specialize hK ( fun i => x i - ⌊x i / ( 2 * Real.pi ) ⌋ * ( 2 * Real.pi ) ) ?_ v hv <;> simp_all +decide [ Matrix.mulVec, dotProduct ] ;
          · exact ⟨ fun i => sub_nonneg.2 <| by nlinarith [ Int.floor_le ( x i / ( 2 * Real.pi ) ), Real.pi_pos, mul_div_cancel₀ ( x i ) ( by positivity : ( 2 * Real.pi ) ≠ 0 ) ], fun i => sub_le_iff_le_add'.2 <| by nlinarith [ Int.lt_floor_add_one ( x i / ( 2 * Real.pi ) ), Real.pi_pos, mul_div_cancel₀ ( x i ) ( by positivity : ( 2 * Real.pi ) ≠ 0 ) ] ⟩;
          · have := hg.smoothPeriodic.2; simp_all +decide [ IsPeriodic2Pi ] ;
            convert hK using 3;
            rw [ ← this ];
            swap;
            exact fun i => -⌊x i / ( 2 * Real.pi ) ⌋;
            unfold periodicShift; norm_num [ sub_eq_add_neg ] ;
            exact Finset.sum_congr rfl fun _ _ => by congr; ext; ring;
        refine' ⟨ K / ( n + 1 ), div_pos hK.1 _, fun h h_cont h_period h_herm h_norm x => ⟨ _, _ ⟩ ⟩;
        · positivity;
        · simp_all +decide [ Matrix.IsHermitian, Matrix.transpose_add ];
          exact hg.smoothPeriodic.periodic |> fun h => by have := hg.posDef x; exact this.1;
        · intro v hv_ne_zero
          have h_pos : ∀ v : Fin n → ℝ, v ≠ 0 → K * ‖v‖ ^ 2 - (n + 1) * matOpNorm (h x) * ‖v‖ ^ 2 ≤ dotProduct v (Matrix.mulVec (g x + h x) v) := by
            intros v hv_ne_zero
            have h_pos : |dotProduct v (Matrix.mulVec (h x) v)| ≤ (n + 1) * matOpNorm (h x) * ‖v‖ ^ 2 := by
              have h_pos : ∀ i : Fin n, |(h x).mulVec v i| ≤ matOpNorm (h x) * ‖v‖ := by
                intro i
                have h_pos : ‖(h x).mulVec v‖ ≤ matOpNorm (h x) * ‖v‖ := by
                  unfold matOpNorm
                  have := ContinuousLinearMap.le_opNorm ( h x |> Matrix.toLin' |> LinearMap.toContinuousLinearMap ) v
                  simpa [LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply] using this
                exact le_trans ( norm_le_pi_norm ( h x *ᵥ v ) i ) h_pos;
              have h_pos : |dotProduct v (Matrix.mulVec (h x) v)| ≤ ∑ i : Fin n, |v i| * |(h x).mulVec v i| := by
                simpa only [ ← abs_mul, dotProduct ] using Finset.abs_sum_le_sum_abs _ _;
              have h_pos : ∑ i : Fin n, |v i| * |(h x).mulVec v i| ≤ ∑ i : Fin n, ‖v‖ * (matOpNorm (h x) * ‖v‖) := by
                exact Finset.sum_le_sum fun i _ => mul_le_mul ( norm_le_pi_norm v i ) ( by solve_by_elim ) ( by positivity ) ( by positivity );
              norm_num at *; nlinarith [ show 0 ≤ matOpNorm ( h x ) * ‖v‖ ^ 2 by exact mul_nonneg ( by exact ContinuousLinearMap.opNorm_nonneg _ ) ( sq_nonneg _ ) ] ;
            simp_all +decide [ Matrix.add_mulVec, dotProduct_add ];
            linarith [ hK.2 x v hv_ne_zero, abs_le.mp h_pos ];
          convert lt_of_lt_of_le _ ( h_pos ( v : Fin n → ℝ ) _ ) using 1;
          · simp +decide [ Matrix.mulVec, dotProduct, Finsupp.sum_fintype ];
            simp +decide only [mul_assoc, Finset.mul_sum _ _ _];
          · have := h_norm x;
            rw [ lt_div_iff₀ ] at this <;> nlinarith [ show 0 < ‖ ( v : Fin n → ℝ )‖ ^ 2 by exact sq_pos_of_pos <| norm_pos_iff.mpr <| by simpa [ Finsupp.ext_iff ] using hv_ne_zero ];
          · exact fun h => hv_ne_zero <| Finsupp.ext fun i => by simpa using congr_fun h i;

end NashEmbedding

end
