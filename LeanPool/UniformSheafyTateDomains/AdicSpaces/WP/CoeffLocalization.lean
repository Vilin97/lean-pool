/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.Tail
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.Perturbation
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.Evaluation
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.KoszulStrictClosed
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetFunctoriality

/-!
# Coefficientwise localization ([WP] §6.4, prop:coefficientwise-localization)

The technical heart of the campaign.  For a rational datum `α` with entries in the
head `𝒜_N`, the completed rational localization of `𝒜` is computed coefficientwise
through the `c₀`-tail:

  `𝒜_α ≅ ⊕̂^{c₀}_μ P e_μ`,  `P = (𝒜_N)_α`   ([WP] eq:coefficientwise-localization)

Both sides are mediated by the graph model.  On the head, `P` is the quotient of
`𝒜_N⟨T_1,…,T_m⟩` by the (closed, by strong noetherianity + [WP] lem:koszul degree 0)
graph ideal — `QHead` below, a genuine normed ring; the bridge
`presheafValue ≃ QHead` is the `chartFwd`/`chartRev` pattern with the generic
evaluation gadget of `WP/Evaluation.lean`.  Over `𝒜`, the graph differential acts
coefficientwise, its image is closed BECAUSE of the norm-bounded lifts at the head
(`FiniteJet.GraphKoszul.exists_d1_lift_pow`, [WP]: "there is a constant `C` such that
every `y ∈ I` has a lift `x ∈ R^m` with `‖x‖ ≤ C‖y‖`"), and the quotient is the
twisted `c₀`-sum `TailC0` of `WP/Tail.lean` ([WP] eq:c0-quotient).

`cor:finite-head-presentation` then combines this with density of the heads and the
small perturbation lemma: EVERY rational localization of `𝒜` is a `TailC0` over a
head localization (`nonempty_headModelData`).
-/

@[expose] public section


namespace WeightedParity

open ValuationSpectrum FiniteJetOver FiniteJet.GraphKoszul

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (w : ℕ → ℕ) (N : ℕ)

/-! ### Coefficientwise transport of `TailC0` -/

section Map

variable {P Q : Type*} [NormedCommRing P] [IsUltrametricDist P]
  [NormedCommRing Q] [IsUltrametricDist Q] {ρ : TwistElem P} {ρ' : TwistElem Q}
  {w' : ℕ → ℕ} {N' : ℕ}

/-- The underlying coefficientwise transport. -/
noncomputable def TailC0.mapFun (φ : P →+* Q) (hφ : ∀ p, ‖φ p‖ ≤ ‖p‖)
    (x : TailC0 w' N' P ρ) : TailC0 w' N' Q ρ' :=
  ⟨fun μ => φ (x.1 μ), by
    refine .squeeze tendsto_const_nhds (by simpa using x.2)
      (fun μ => norm_nonneg _) fun μ => hφ (x.1 μ)⟩

theorem TailC0.mapFun_val (φ : P →+* Q) (hφ : ∀ p, ‖φ p‖ ≤ ‖p‖)
    (x : TailC0 w' N' P ρ) (μ : TailIdx N') :
    (TailC0.mapFun (ρ' := ρ') φ hφ x).1 μ = φ (x.1 μ) := rfl

theorem TailC0.mapFun_one (φ : P →+* Q) (hφ : ∀ p, ‖φ p‖ ≤ ‖p‖) :
    TailC0.mapFun (w' := w') (N' := N') (ρ := ρ) (ρ' := ρ') φ hφ 1 = 1 := by
  refine Subtype.ext (funext fun μ => ?_)
  rw [TailC0.mapFun_val, TailC0.one_val, TailC0.one_val]
  split_ifs
  · exact map_one φ
  · exact map_zero φ

theorem TailC0.mapFun_zero (φ : P →+* Q) (hφ : ∀ p, ‖φ p‖ ≤ ‖p‖) :
    TailC0.mapFun (w' := w') (N' := N') (ρ := ρ) (ρ' := ρ') φ hφ 0 = 0 := by
  refine Subtype.ext (funext fun μ => ?_)
  rw [TailC0.mapFun_val, show ((0 : TailC0 w' N' P ρ)).1 μ = 0 from rfl,
    show ((0 : TailC0 w' N' Q ρ')).1 μ = 0 from rfl]
  exact map_zero φ

theorem TailC0.mapFun_add (φ : P →+* Q) (hφ : ∀ p, ‖φ p‖ ≤ ‖p‖)
    (x y : TailC0 w' N' P ρ) :
    TailC0.mapFun (ρ' := ρ') φ hφ (x + y) =
      TailC0.mapFun (ρ' := ρ') φ hφ x + TailC0.mapFun (ρ' := ρ') φ hφ y := by
  refine Subtype.ext (funext fun μ => ?_)
  rw [TailC0.mapFun_val, show ((x + y) : TailC0 w' N' P ρ).1 μ = x.1 μ + y.1 μ
    from rfl]
  rw [show ((TailC0.mapFun (ρ' := ρ') φ hφ x + TailC0.mapFun (ρ' := ρ') φ hφ y :
      TailC0 w' N' Q ρ')).1 μ =
    (TailC0.mapFun (ρ' := ρ') φ hφ x).1 μ + (TailC0.mapFun (ρ' := ρ') φ hφ y).1 μ
    from rfl, TailC0.mapFun_val, TailC0.mapFun_val]
  exact map_add φ _ _

theorem TailC0.mapFun_mul (φ : P →+* Q) (hφ : ∀ p, ‖φ p‖ ≤ ‖p‖)
    (hρ : φ ρ.val = ρ'.val) (x y : TailC0 w' N' P ρ) :
    TailC0.mapFun (ρ' := ρ') φ hφ (x * y) =
      TailC0.mapFun (ρ' := ρ') φ hφ x * TailC0.mapFun (ρ' := ρ') φ hφ y := by
  classical
  refine Subtype.ext (funext fun τ => ?_)
  rw [TailC0.mapFun_val, TailC0.mul_val, TailC0.mul_val, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_mul, map_mul, map_pow, hρ, TailC0.mapFun_val, TailC0.mapFun_val]

/-- Coefficientwise functoriality of the twisted `c₀`-sum along a bounded twist-
compatible homomorphism ([WP] eq:coefficientwise-restriction: "the induced restriction
sends `∑ p_μ e_μ ↦ ∑ (p_μ|_Q) e_μ`"). -/
noncomputable def TailC0.map (φ : P →+* Q) (hφ : ∀ p, ‖φ p‖ ≤ ‖p‖)
    (hρ : φ ρ.val = ρ'.val) :
    TailC0 w' N' P ρ →+* TailC0 w' N' Q ρ' where
  toFun := TailC0.mapFun (ρ' := ρ') φ hφ
  map_one' := TailC0.mapFun_one φ hφ
  map_mul' := TailC0.mapFun_mul φ hφ hρ
  map_zero' := TailC0.mapFun_zero φ hφ
  map_add' := TailC0.mapFun_add φ hφ

@[simp] theorem TailC0.coeff_map (φ : P →+* Q) (hφ : ∀ p, ‖φ p‖ ≤ ‖p‖)
    (hρ : φ ρ.val = ρ'.val) (x : TailC0 w' N' P ρ) (μ : TailIdx N') :
    TailC0.coeff μ (TailC0.map φ hφ hρ x) = φ (TailC0.coeff μ x) := rfl

theorem TailC0.map_continuous (φ : P →+* Q) (hφ : ∀ p, ‖φ p‖ ≤ ‖p‖)
    (hρ : φ ρ.val = ρ'.val) :
    Continuous (TailC0.map (w' := w') (N' := N') φ hφ hρ) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun x y => ?_).continuous
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  rw [show TailC0.map (w' := w') (N' := N') φ hφ hρ x -
      TailC0.map (w' := w') (N' := N') φ hφ hρ y =
    TailC0.map (w' := w') (N' := N') φ hφ hρ (x - y) from (map_sub _ _ _).symm]
  rw [TailC0.norm_def, TailC0.norm_def]
  refine ciSup_le fun μ => ?_
  refine le_trans (hφ _) ?_
  exact TailC0.norm_coeff_le _ μ

end Map

/-! ### The tail convolution formula ([WP] eq:tail-multiplication, full form) -/

section TailConv

variable {K w N}

theorem tailCoeff_neg (μ : TailIdx N) (f : WPA K w) :
    tailCoeff K w N μ (-f) = -tailCoeff K w N μ f := by
  have h := (tailCoeff_add K w N μ f (-f)).symm
  rw [add_neg_cancel, tailCoeff_zero_map] at h
  exact eq_neg_of_add_eq_zero_left (by rwa [add_comm] at h)

theorem tailCoeff_sub (μ : TailIdx N) (f g : WPA K w) :
    tailCoeff K w N μ (f - g) = tailCoeff K w N μ f - tailCoeff K w N μ g := by
  rw [sub_eq_add_neg, tailCoeff_add, tailCoeff_neg, sub_eq_add_neg]

/-- Finite tail truncation: the partial sum of the isometric decomposition
`𝒜 ≅ ⊕̂ 𝒜_N e_μ` over a finite set of tail indices. -/
noncomputable def tailTrunc (S : Finset (TailIdx N)) (f : WPA K w) : WPA K w :=
  ∑ μ ∈ S, headIncl K w N (tailCoeff K w N μ f) * eTail K w N μ

open scoped Classical in
theorem tailCoeff_tailTrunc (S : Finset (TailIdx N)) (f : WPA K w) (ν : TailIdx N) :
    tailCoeff K w N ν (tailTrunc S f) =
      if ν ∈ S then tailCoeff K w N ν f else 0 := by
  classical
  unfold tailTrunc
  induction S using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, tailCoeff_zero_map, if_neg (Finset.notMem_empty ν)]
  | insert μ S hμS ih =>
    rw [Finset.sum_insert hμS, tailCoeff_add, ih, tailCoeff_headIncl_mul_eTail]
    by_cases hν : ν = μ
    · subst hν
      rw [if_pos rfl, if_neg hμS, add_zero, if_pos (Finset.mem_insert_self ν S)]
    · rw [if_neg hν, zero_add]
      by_cases hνS : ν ∈ S
      · rw [if_pos hνS, if_pos (Finset.mem_insert_of_mem hνS)]
      · rw [if_neg hνS, if_neg (by
          intro hmem
          rcases Finset.mem_insert.mp hmem with h | h
          · exact hν h
          · exact hνS h)]

theorem norm_sub_tailTrunc_le (S : Finset (TailIdx N)) (f : WPA K w) {ε : ℝ}
    (hε : 0 ≤ ε) (hS : ∀ ν ∉ S, ‖tailCoeff K w N ν f‖ ≤ ε) :
    ‖f - tailTrunc S f‖ ≤ ε := by
  classical
  rw [norm_eq_iSup_tailCoeff]
  refine ciSup_le fun ν => ?_
  rw [tailCoeff_sub, tailCoeff_tailTrunc]
  by_cases hν : ν ∈ S
  · rw [if_pos hν, sub_self, norm_zero]
    exact hε
  · rw [if_neg hν, sub_zero]
    exact hS ν hν

theorem exists_tailTrunc_close (f : WPA K w) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset (TailIdx N), ‖f - tailTrunc S f‖ ≤ ε := by
  classical
  have h := tendsto_norm_tailCoeff_cofinite K w N f
  rw [Metric.tendsto_nhds] at h
  have h1 := h ε hε
  rw [Filter.eventually_cofinite] at h1
  refine ⟨h1.toFinset, norm_sub_tailTrunc_le _ f hε.le fun ν hν => ?_⟩
  by_contra hgt
  push_neg at hgt
  refine hν ?_
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Real.dist_eq, sub_zero,
    abs_of_nonneg (norm_nonneg _), not_lt]
  exact hgt.le

theorem norm_tailTrunc_le (S : Finset (TailIdx N)) (f : WPA K w) :
    ‖tailTrunc S f‖ ≤ ‖f‖ := by
  classical
  rw [norm_eq_iSup_tailCoeff]
  refine ciSup_le fun ν => ?_
  rw [tailCoeff_tailTrunc]
  by_cases hν : ν ∈ S
  · rw [if_pos hν]
    exact norm_tailCoeff_le K w N ν f
  · rw [if_neg hν, norm_zero]
    exact norm_nonneg f

/-- The bundled additive tail coefficient. -/
noncomputable def tailCoeffHom (μ : TailIdx N) : WPA K w →+ WPHead K w N where
  toFun := tailCoeff K w N μ
  map_zero' := tailCoeff_zero_map K w N μ
  map_add' := tailCoeff_add K w N μ

theorem tailCoeffHom_apply (μ : TailIdx N) (f : WPA K w) :
    tailCoeffHom μ f = tailCoeff K w N μ f := rfl

/-- Product of two decomposition summands ([WP] eq:tail-multiplication as an
identity of `𝒜`-elements). -/
theorem headIncl_eTail_mul (x y : WPHead K w N) (ν lam : TailIdx N) :
    (headIncl K w N x * eTail K w N ν) * (headIncl K w N y * eTail K w N lam) =
      headIncl K w N (WaHead K w N ^
          (wpWeight w ν.1 + wpWeight w lam.1 - wpWeight w (ν + lam).1) * (x * y)) *
        eTail K w N (ν + lam) := by
  have h1 : (headIncl K w N x * eTail K w N ν) *
      (headIncl K w N y * eTail K w N lam) =
      headIncl K w N (x * y) * (eTail K w N ν * eTail K w N lam) := by
    rw [map_mul]
    ring
  have h2 : headIncl K w N (WaHead K w N ^
      (wpWeight w ν.1 + wpWeight w lam.1 - wpWeight w (ν + lam).1) * (x * y)) =
      headIncl K w N (WaHead K w N ^
        (wpWeight w ν.1 + wpWeight w lam.1 - wpWeight w (ν + lam).1)) *
        (headIncl K w N x * headIncl K w N y) := by
    rw [map_mul, map_mul]
  have h3 : headIncl K w N (x * y) = headIncl K w N x * headIncl K w N y :=
    map_mul _ _ _
  rw [h1, eTail_mul, h2, h3]
  ring

open scoped Classical in
/-- The finite-truncation convolution formula. -/
theorem tailCoeff_tailTrunc_mul (S T : Finset (TailIdx N)) (f g : WPA K w)
    (μ : TailIdx N) :
    tailCoeff K w N μ (tailTrunc S f * tailTrunc T g) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal μ,
        WaHead K w N ^ (wpWeight w p.1.1 + wpWeight w p.2.1 - wpWeight w μ.1) *
          ((if p.1 ∈ S then tailCoeff K w N p.1 f else 0) *
            (if p.2 ∈ T then tailCoeff K w N p.2 g else 0)) := by
  classical
  unfold tailTrunc
  rw [Finset.sum_mul_sum]
  rw [show tailCoeff K w N μ (∑ ν ∈ S, ∑ lam ∈ T,
      (headIncl K w N (tailCoeff K w N ν f) * eTail K w N ν) *
        (headIncl K w N (tailCoeff K w N lam g) * eTail K w N lam)) =
    tailCoeffHom μ (∑ ν ∈ S, ∑ lam ∈ T,
      (headIncl K w N (tailCoeff K w N ν f) * eTail K w N ν) *
        (headIncl K w N (tailCoeff K w N lam g) * eTail K w N lam)) from rfl]
  rw [map_sum]
  have hterm : ∀ ν ∈ S, tailCoeffHom μ (∑ lam ∈ T,
      (headIncl K w N (tailCoeff K w N ν f) * eTail K w N ν) *
        (headIncl K w N (tailCoeff K w N lam g) * eTail K w N lam)) =
      ∑ lam ∈ T, if μ = ν + lam then
        WaHead K w N ^
            (wpWeight w ν.1 + wpWeight w lam.1 - wpWeight w (ν + lam).1) *
          (tailCoeff K w N ν f * tailCoeff K w N lam g) else 0 := by
    intro ν _
    rw [map_sum]
    refine Finset.sum_congr rfl fun lam _ => ?_
    rw [tailCoeffHom_apply, headIncl_eTail_mul, tailCoeff_headIncl_mul_eTail]
  rw [Finset.sum_congr rfl hterm]
  -- both sides as sums over the filtered pair set
  rw [← Finset.sum_product']
  rw [← Finset.sum_filter (s := S ×ˢ T)
    (p := fun q : TailIdx N × TailIdx N => μ = q.1 + q.2)]
  have hrhs : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal μ,
      WaHead K w N ^ (wpWeight w p.1.1 + wpWeight w p.2.1 - wpWeight w μ.1) *
        ((if p.1 ∈ S then tailCoeff K w N p.1 f else 0) *
          (if p.2 ∈ T then tailCoeff K w N p.2 g else 0)) =
      ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal μ).filter
          (fun p : TailIdx N × TailIdx N => p.1 ∈ S ∧ p.2 ∈ T),
        WaHead K w N ^ (wpWeight w p.1.1 + wpWeight w p.2.1 - wpWeight w μ.1) *
          (tailCoeff K w N p.1 f * tailCoeff K w N p.2 g) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h1 : p.1 ∈ S
    · by_cases h2 : p.2 ∈ T
      · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
      · rw [if_pos h1, if_neg h2,
          if_neg (show ¬(p.1 ∈ S ∧ p.2 ∈ T) from fun hc => h2 hc.2),
          mul_zero, mul_zero]
    · rw [if_neg h1,
        if_neg (show ¬(p.1 ∈ S ∧ p.2 ∈ T) from fun hc => h1 hc.1),
        zero_mul, mul_zero]
  rw [hrhs]
  have hsets : (S ×ˢ T).filter (fun q : TailIdx N × TailIdx N => μ = q.1 + q.2) =
      (Finset.HasAntidiagonal.antidiagonal μ).filter
        (fun p : TailIdx N × TailIdx N => p.1 ∈ S ∧ p.2 ∈ T) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_product,
      Finset.HasAntidiagonal.mem_antidiagonal]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h3.symm, h1, h2⟩
    · rintro ⟨h3, h1, h2⟩
      exact ⟨⟨h1, h2⟩, h3.symm⟩
  rw [hsets]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [hp.1]

/-- The norm of `W` in the head is `1`. -/
theorem norm_WaHead : ‖WaHead K w N‖ = 1 := by
  rw [← norm_headIncl K w N (WaHead K w N), headIncl_WaHead]
  show ‖wpMonomial K w (wpMem_single_zero w 1) 1‖ = 1
  rw [norm_wpMonomial, norm_one]

theorem norm_WaHead_pow_le_one (e : ℕ) : ‖WaHead K w N ^ e‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [pow_zero]
    exact le_of_eq norm_one
  · refine le_trans (norm_pow_le' _ he) ?_
    rw [norm_WaHead, one_pow]

open scoped Classical in
/-- **The tail convolution formula** ([WP] eq:tail-multiplication in full):
the tail coefficients of a product are the `W`-twisted convolution of the tail
coefficients.  Proved from the finite-truncation case by density of the
isometric decomposition. -/
theorem tailCoeff_mul (f g : WPA K w) (μ : TailIdx N) :
    tailCoeff K w N μ (f * g) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal μ,
        WaHead K w N ^ (wpWeight w p.1.1 + wpWeight w p.2.1 - wpWeight w μ.1) *
          (tailCoeff K w N p.1 f * tailCoeff K w N p.2 g) := by
  classical
  refine eq_of_forall_dist_le fun ε hε => ?_
  rw [dist_eq_norm]
  set M := max (max ‖f‖ ‖g‖) 1 with hMdef
  have hM1 : (1 : ℝ) ≤ M := le_max_right _ _
  have hMf : ‖f‖ ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hMg : ‖g‖ ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM1
  obtain ⟨S, hS⟩ := exists_tailTrunc_close (N := N) f (div_pos hε hM0)
  obtain ⟨T, hT⟩ := exists_tailTrunc_close (N := N) g (div_pos hε hM0)
  set F := tailTrunc S f with hFdef
  set G := tailTrunc T g with hGdef
  have hFn : ‖F‖ ≤ M := le_trans (norm_tailTrunc_le S f) hMf
  have hGn : ‖G‖ ≤ M := le_trans (norm_tailTrunc_le T g) hMg
  have hdivM : ε / M * M = ε := div_mul_cancel₀ ε hM0.ne'
  -- middle identity: the finite formula with gates folded into truncations
  have hmid : tailCoeff K w N μ (F * G) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal μ,
        WaHead K w N ^ (wpWeight w p.1.1 + wpWeight w p.2.1 - wpWeight w μ.1) *
          (tailCoeff K w N p.1 F * tailCoeff K w N p.2 G) := by
    rw [tailCoeff_tailTrunc_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [tailCoeff_tailTrunc, tailCoeff_tailTrunc]
  -- error term A: the product moves by at most ε
  have hA : ‖tailCoeff K w N μ (f * g) - tailCoeff K w N μ (F * G)‖ ≤ ε := by
    rw [← tailCoeff_sub]
    refine le_trans (norm_tailCoeff_le K w N μ _) ?_
    have hsplit : f * g - F * G = (f - F) * g + F * (g - G) := by ring
    rw [hsplit]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) ?_
    refine max_le ?_ ?_
    · refine le_trans (norm_mul_le _ _) ?_
      calc ‖f - F‖ * ‖g‖ ≤ ε / M * M :=
            mul_le_mul hS hMg (norm_nonneg _) (div_pos hε hM0).le
        _ = ε := hdivM
    · refine le_trans (norm_mul_le _ _) ?_
      calc ‖F‖ * ‖g - G‖ ≤ M * (ε / M) :=
            mul_le_mul hFn hT (norm_nonneg _) (le_trans (norm_nonneg _) hFn)
        _ = ε := by rw [mul_comm]; exact hdivM
  -- error term B: each summand moves by at most ε
  have hB : ‖(∑ p ∈ Finset.HasAntidiagonal.antidiagonal μ,
      WaHead K w N ^ (wpWeight w p.1.1 + wpWeight w p.2.1 - wpWeight w μ.1) *
        (tailCoeff K w N p.1 F * tailCoeff K w N p.2 G)) -
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal μ,
        WaHead K w N ^ (wpWeight w p.1.1 + wpWeight w p.2.1 - wpWeight w μ.1) *
          (tailCoeff K w N p.1 f * tailCoeff K w N p.2 g)‖ ≤ ε := by
    rw [← Finset.sum_sub_distrib]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε.le
      fun p _ => ?_
    rw [← mul_sub]
    refine le_trans (norm_mul_le _ _) ?_
    refine le_trans (mul_le_mul_of_nonneg_right (norm_WaHead_pow_le_one _)
      (norm_nonneg _)) ?_
    rw [one_mul]
    have hsplit : tailCoeff K w N p.1 F * tailCoeff K w N p.2 G -
        tailCoeff K w N p.1 f * tailCoeff K w N p.2 g =
        (tailCoeff K w N p.1 F - tailCoeff K w N p.1 f) * tailCoeff K w N p.2 G +
          tailCoeff K w N p.1 f *
            (tailCoeff K w N p.2 G - tailCoeff K w N p.2 g) := by ring
    rw [hsplit]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) ?_
    refine max_le ?_ ?_
    · refine le_trans (norm_mul_le _ _) ?_
      calc ‖tailCoeff K w N p.1 F - tailCoeff K w N p.1 f‖ *
            ‖tailCoeff K w N p.2 G‖
          ≤ ε / M * M := by
            refine mul_le_mul ?_ (le_trans (norm_tailCoeff_le K w N p.2 G) hGn)
              (norm_nonneg _) (div_pos hε hM0).le
            rw [← tailCoeff_sub]
            exact le_trans (norm_tailCoeff_le K w N p.1 _)
              (by rw [norm_sub_rev]; exact hS)
        _ = ε := hdivM
    · refine le_trans (norm_mul_le _ _) ?_
      calc ‖tailCoeff K w N p.1 f‖ *
            ‖tailCoeff K w N p.2 G - tailCoeff K w N p.2 g‖
          ≤ M * (ε / M) := by
            refine mul_le_mul (le_trans (norm_tailCoeff_le K w N p.1 f) hMf) ?_
              (norm_nonneg _) hM0.le
            rw [← tailCoeff_sub]
            exact le_trans (norm_tailCoeff_le K w N p.2 _)
              (by rw [norm_sub_rev]; exact hT)
        _ = ε := by rw [mul_comm]; exact hdivM
  -- assemble
  have hdecomp : tailCoeff K w N μ (f * g) -
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal μ,
        WaHead K w N ^ (wpWeight w p.1.1 + wpWeight w p.2.1 - wpWeight w μ.1) *
          (tailCoeff K w N p.1 f * tailCoeff K w N p.2 g) =
      (tailCoeff K w N μ (f * g) - tailCoeff K w N μ (F * G)) +
        ((∑ p ∈ Finset.HasAntidiagonal.antidiagonal μ,
          WaHead K w N ^ (wpWeight w p.1.1 + wpWeight w p.2.1 - wpWeight w μ.1) *
            (tailCoeff K w N p.1 F * tailCoeff K w N p.2 G)) -
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal μ,
            WaHead K w N ^ (wpWeight w p.1.1 + wpWeight w p.2.1 -
              wpWeight w μ.1) *
              (tailCoeff K w N p.1 f * tailCoeff K w N p.2 g)) := by
    rw [hmid]
    ring
  rw [hdecomp]
  refine le_trans (IsUltrametricDist.norm_add_le_max _ _) ?_
  exact max_le hA hB

theorem tailCoeff_continuous (μ : TailIdx N) :
    Continuous (tailCoeff K w N μ : WPA K w → WPHead K w N) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun f g => ?_).continuous
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← tailCoeff_sub]
  exact norm_tailCoeff_le K w N μ _

theorem tailCoeff_tsum {ι : Type*} (f : ι → WPA K w) (hf : Summable f)
    (μ : TailIdx N) :
    tailCoeff K w N μ (∑' i, f i) = ∑' i, tailCoeff K w N μ (f i) :=
  ((hf.hasSum.map (tailCoeffHom μ) (tailCoeff_continuous μ)).tsum_eq).symm

/-- The head twist of `𝒜`: the variable `W`, of norm `1`. -/
noncomputable def waTwist : TwistElem (WPHead K w N) :=
  ⟨WaHead K w N, le_of_eq norm_WaHead⟩

/-- The decomposition series of a null coefficient family is summable. -/
theorem summable_headIncl_eTail
    (x : TailC0 w N (WPHead K w N) (waTwist (K := K) (w := w) (N := N))) :
    Summable (fun μ : TailIdx N => headIncl K w N (x.1 μ) * eTail K w N μ) := by
  apply summable_of_tendsto_cofinite_nonarch
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine .squeeze tendsto_const_nhds (by simpa using x.2) (fun μ => norm_nonneg _)
    fun μ => ?_
  refine le_trans (norm_mul_le _ _) ?_
  have h1 : ‖eTail K w N μ‖ ≤ 1 := by
    rw [show eTail K w N μ = wpMonomial K w (wpMem_tailShift w μ) 1 from rfl,
      norm_wpMonomial, norm_one]
  calc ‖headIncl K w N (x.1 μ)‖ * ‖eTail K w N μ‖
      ≤ ‖x.1 μ‖ * 1 := by
        rw [norm_headIncl]
        exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖x.1 μ‖ := mul_one _

open scoped Classical in
/-- Coefficient recovery for decomposition series. -/
theorem tailCoeff_tsum_headIncl_eTail
    (x : TailC0 w N (WPHead K w N) (waTwist (K := K) (w := w) (N := N)))
    (ν : TailIdx N) :
    tailCoeff K w N ν (∑' μ : TailIdx N, headIncl K w N (x.1 μ) * eTail K w N μ) =
      x.1 ν := by
  rw [tailCoeff_tsum _ (summable_headIncl_eTail x)]
  rw [show (fun μ : TailIdx N =>
      tailCoeff K w N ν (headIncl K w N (x.1 μ) * eTail K w N μ)) =
    fun μ : TailIdx N => if ν = μ then x.1 μ else 0 from
    funext fun μ => tailCoeff_headIncl_mul_eTail K w N μ ν (x.1 μ)]
  rw [tsum_eq_single ν ?_]
  · rw [if_pos rfl]
  · intro μ hμ
    rw [if_neg (fun h => hμ h.symm)]

/-- **The isometric tail decomposition of `𝒜`** ([WP] eq:tail-decomposition), as a
ring equivalence onto the `W`-twisted `c₀`-sum over the head. -/
noncomputable def wpaTailEquiv :
    WPA K w ≃+* TailC0 w N (WPHead K w N) (waTwist (K := K) (w := w) (N := N)) where
  toFun f := ⟨fun μ => tailCoeff K w N μ f, tendsto_norm_tailCoeff_cofinite K w N f⟩
  invFun x := ∑' μ : TailIdx N, headIncl K w N (x.1 μ) * eTail K w N μ
  left_inv f := by
    apply tailCoeff_injective K w N
    funext ν
    show tailCoeff K w N ν _ = tailCoeff K w N ν f
    exact tailCoeff_tsum_headIncl_eTail _ ν
  right_inv x := by
    refine Subtype.ext (funext fun ν => ?_)
    show tailCoeff K w N ν _ = x.1 ν
    exact tailCoeff_tsum_headIncl_eTail x ν
  map_add' f g := Subtype.ext (funext fun μ => tailCoeff_add K w N μ f g)
  map_mul' f g := by
    refine Subtype.ext (funext fun μ => ?_)
    have hR := TailC0.mul_val (w := w) (N := N)
      (ρ := waTwist (K := K) (w := w) (N := N))
      (⟨fun μ => tailCoeff K w N μ f, tendsto_norm_tailCoeff_cofinite K w N f⟩ :
        TailC0 w N (WPHead K w N) (waTwist (K := K) (w := w) (N := N)))
      ⟨fun μ => tailCoeff K w N μ g, tendsto_norm_tailCoeff_cofinite K w N g⟩ μ
    show tailCoeff K w N μ (f * g) = _
    rw [hR, tailCoeff_mul f g μ]
    rfl

theorem wpaTailEquiv_apply_val (f : WPA K w) (μ : TailIdx N) :
    ((wpaTailEquiv (K := K) (w := w) (N := N)) f).1 μ = tailCoeff K w N μ f := rfl

theorem wpaTailEquiv_headIncl (x : WPHead K w N) :
    (wpaTailEquiv (K := K) (w := w) (N := N)) (headIncl K w N x) =
      TailC0.ofHead x := by
  refine Subtype.ext (funext fun μ => ?_)
  show tailCoeff K w N μ (headIncl K w N x) = (TailC0.ofHead x).1 μ
  rw [show (TailC0.ofHead x : TailC0 w N (WPHead K w N) _).1 μ =
    if μ = 0 then x else 0 from rfl]
  by_cases hμ : μ = 0
  · subst hμ
    rw [if_pos rfl]
    have h := rhoHead_headIncl K w N x
    rw [rhoHead_apply] at h
    exact h
  · rw [if_neg hμ]
    have h1 : headIncl K w N x = headIncl K w N x * eTail K w N 0 := by
      rw [show eTail K w N 0 = wpMonomial K w (wpMem_tailShift w 0) 1 from rfl]
      rw [show (wpMonomial K w (wpMem_tailShift w (0 : TailIdx N)) 1 : WPA K w) =
        1 from ?_]
      · rw [mul_one]
      · refine Subtype.ext (Subtype.ext ?_)
        show MvPowerSeries.monomial (tailShift w (0 : TailIdx N)) (1 : K) = 1
        rw [tailShift_zero]
        exact MvPowerSeries.monomial_zero_one
    rw [h1, tailCoeff_headIncl_mul_eTail, if_neg hμ]

end TailConv

/-! ### The head graph model `QHead` -/

variable {K w N} in
/-- A chosen enumeration of the entries of a head rational datum. -/
noncomputable def datumEnum (DH : RationalLocData (WPHead K w N)) :
    Fin DH.T.card ≃ ↥DH.T :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe DH.T)).symm

variable {K w N} in
/-- The graph relations `s·T_i − t_i` of a head datum in `𝒜_N⟨T_1,…,T_m⟩`
([WP] eq:graph-ideal-definition). -/
noncomputable def headGraphRel (DH : RationalLocData (WPHead K w N)) :
    Fin DH.T.card → P (WPHead K w N) DH.T.card := fun i =>
  polyToP (MvPolynomial.C DH.s * MvPolynomial.X i -
    MvPolynomial.C ((datumEnum DH i : ↥DH.T) : WPHead K w N))

variable {K w N} in
/-- The graph ideal of a head datum, taken CLOSED: the topological closure of the
span of the graph relations.  Under strong noetherianity of the head
([WP] lem:koszul, via `hK₀`) the span is already closed and the closure collapses
(`FiniteJet.GraphKoszul.isClosed_graphIdeal` + `Ideal.closure_eq_of_isClosed`);
quotienting by the closure keeps the quotient norm a genuine norm without carrying
`hK₀` in the instance layer. -/
noncomputable def headGraphIdeal (DH : RationalLocData (WPHead K w N)) :
    Ideal (P (WPHead K w N) DH.T.card) :=
  (Ideal.span (Set.range (headGraphRel DH))).closure

variable {K w N} in
/-- The head graph-model quotient `Q = 𝒜_N⟨T⟩/(sT_i − t_i)` ([WP] eq:graph-model;
the ideal is closed by [WP] lem:koszul at the strongly noetherian head — the
`headGraphIdeal` closure is cosmetic there). -/
noncomputable def QHead (DH : RationalLocData (WPHead K w N)) : Type _ :=
  P (WPHead K w N) DH.T.card ⧸ headGraphIdeal DH

variable {K w N} in
noncomputable instance instCommRingQHead {DH : RationalLocData (WPHead K w N)} :
    CommRing (QHead DH) :=
  inferInstanceAs (CommRing (P (WPHead K w N) DH.T.card ⧸ headGraphIdeal DH))

variable {K w N} in
theorem isClosed_headGraphIdeal (DH : RationalLocData (WPHead K w N)) :
    IsClosed ((headGraphIdeal DH : Ideal (P (WPHead K w N) DH.T.card)) :
      Set (P (WPHead K w N) DH.T.card)) :=
  isClosed_closure

variable {K w N} in
/-- The quotient norm makes `QHead` a normed ring (the graph ideal is closed:
[WP] lem:koszul clause 3 / `FiniteJet.GraphKoszul.isClosed_graphIdeal`). -/
noncomputable instance instNormedCommRingQHead {DH : RationalLocData (WPHead K w N)} :
    NormedCommRing (QHead DH) :=
  haveI : IsClosed ((headGraphIdeal DH : Ideal (P (WPHead K w N) DH.T.card)) :
      Set (P (WPHead K w N) DH.T.card)) := isClosed_headGraphIdeal DH
  inferInstanceAs
    (NormedCommRing (P (WPHead K w N) DH.T.card ⧸ headGraphIdeal DH))

variable {K w N} in
instance instUltraQHead {DH : RationalLocData (WPHead K w N)} :
    IsUltrametricDist (QHead DH) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    fun x y => ?_
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨a, ha, han⟩ := Ideal.Quotient.norm_mk_lt x hε
  obtain ⟨b, hb, hbn⟩ := Ideal.Quotient.norm_mk_lt y hε
  have hxy : x + y = Ideal.Quotient.mk (headGraphIdeal DH) (a + b) := by
    rw [map_add, ha, hb]
    rfl
  rw [hxy]
  refine le_trans (Ideal.Quotient.norm_mk_le _ _) ?_
  refine le_trans (IsUltrametricDist.norm_add_le_max a b) ?_
  calc max ‖a‖ ‖b‖ ≤ max (‖x‖ + ε) (‖y‖ + ε) := max_le_max han.le hbn.le
    _ = max ‖x‖ ‖y‖ + ε := max_add_add_right _ _ _

variable {K w N} in
instance instCompleteQHead {DH : RationalLocData (WPHead K w N)} :
    CompleteSpace (QHead DH) :=
  QuotientAddGroup.completeSpace_left (P (WPHead K w N) DH.T.card)
    (headGraphIdeal DH).toAddSubgroup

variable {K w N} in
/-- The constant embedding of the head into its Tate algebra sends `C x` to the
constant series (the W8 `hCP` fact, packaged). -/
theorem polyToP_C_val (x : WPHead K w N) {m : ℕ} :
    ((polyToP (MvPolynomial.C x) : P (WPHead K w N) m)).1 =
      MvPowerSeries.C x := by
  classical
  refine MvPowerSeries.ext fun t => ?_
  rw [coeff_polyToP, MvPowerSeries.coeff_C, MvPolynomial.coeff_C]
  rcases eq_or_ne t 0 with rfl | ht
  · rfl
  · rw [if_neg (fun h => ht h.symm), if_neg ht]

variable {K w N} in
/-- The twist element of the head model: the image of `W` (norm `≤ 1` since the
quotient map is norm-nonincreasing). -/
noncomputable def rhoQ (DH : RationalLocData (WPHead K w N)) : TwistElem (QHead DH) where
  val := Ideal.Quotient.mk (headGraphIdeal DH)
    (polyToP (MvPolynomial.C (WaHead K w N)))
  norm_le_one := by
    classical
    refine le_trans (Ideal.Quotient.norm_mk_le _ _) ?_
    rw [MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
    refine Real.iSup_le (fun t => ?_) zero_le_one
    rw [FiniteJet.finsupp_prod_one, mul_one, polyToP_C_val, MvPowerSeries.coeff_C]
    split_ifs
    · rw [norm_WaHead]
    · rw [norm_zero]
      exact zero_le_one

variable {K w N} in
/-- The constant map into the head graph model. -/
noncomputable def headConst (DH : RationalLocData (WPHead K w N)) :
    WPHead K w N →+* QHead DH :=
  (Ideal.Quotient.mk (headGraphIdeal DH)).comp
    ((polyToP (E := WPHead K w N) (m := DH.T.card)).comp
      (MvPolynomial.C : WPHead K w N →+* MvPolynomial (Fin DH.T.card) (WPHead K w N)))

variable {K w N} in
theorem norm_headConst_le (DH : RationalLocData (WPHead K w N)) (x : WPHead K w N) :
    ‖headConst DH x‖ ≤ ‖x‖ := by
  classical
  show ‖(Ideal.Quotient.mk (headGraphIdeal DH) (polyToP (MvPolynomial.C x)) :
    QHead DH)‖ ≤ ‖x‖
  refine le_trans (Ideal.Quotient.norm_mk_le _ _) ?_
  rw [MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
  refine Real.iSup_le (fun t => ?_) (norm_nonneg x)
  rw [FiniteJet.finsupp_prod_one, mul_one, polyToP_C_val, MvPowerSeries.coeff_C]
  split_ifs
  · exact le_refl _
  · rw [norm_zero]
    exact norm_nonneg x

variable {K w N} in
theorem headConst_continuous (DH : RationalLocData (WPHead K w N)) :
    Continuous (headConst DH) :=
  AddMonoidHomClass.continuous_of_bound (headConst DH) 1 fun x => by
    rw [one_mul]
    exact norm_headConst_le DH x

variable {K w N} in
/-- The image of the `i`-th Tate variable in the head graph model. -/
noncomputable def qX (DH : RationalLocData (WPHead K w N)) (i : Fin DH.T.card) :
    QHead DH :=
  Ideal.Quotient.mk (headGraphIdeal DH) (polyToP (MvPolynomial.X i))

variable {K w N} in
/-- The defining relation of the graph model: `headConst t = headConst s · mk(X i)`
for the `i`-th entry. -/
theorem headConst_datumEnum (DH : RationalLocData (WPHead K w N))
    (i : Fin DH.T.card) :
    headConst DH ((datumEnum DH i : ↥DH.T) : WPHead K w N) =
      headConst DH DH.s * qX DH i := by
  have hrel : Ideal.Quotient.mk (headGraphIdeal DH) (headGraphRel DH i) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    show headGraphRel DH i ∈ headGraphIdeal DH
    rw [headGraphIdeal, ← SetLike.mem_coe, Ideal.coe_closure]
    exact subset_closure (Ideal.subset_span ⟨i, rfl⟩)
  rw [headGraphRel, map_sub, map_sub, sub_eq_zero] at hrel
  rw [show headConst DH ((datumEnum DH i : ↥DH.T) : WPHead K w N) =
    Ideal.Quotient.mk (headGraphIdeal DH)
      (polyToP (MvPolynomial.C ((datumEnum DH i : ↥DH.T) : WPHead K w N))) from rfl]
  rw [← hrel, map_mul, map_mul]
  rfl

variable {K w N} in
/-- `s` is a unit in the head graph model ([WP] lem:koszul's Bezout trick:
`t^ℓ = s·(∑ a_i T_i)` mod the graph ideal, and `t` is a unit). -/
theorem isUnit_headConst_s (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    IsUnit (headConst DH DH.s) := by
  classical
  obtain ⟨ℓ, a, ha1, hbez⟩ := exists_integral_bezout' (piHead ϖ) (isUnit_piHead ϖ)
    (norm_piHead_lt_one ϖ) (norm_piHead_pos ϖ) (norm_piHead_mul ϖ) DH hDH
  have hmap : headConst DH (piHead ϖ) ^ ℓ =
      headConst DH DH.s * ∑ i : Fin DH.T.card,
        headConst DH (a ((datumEnum DH i : ↥DH.T) : WPHead K w N)) * qX DH i := by
    rw [← map_pow, ← hbez, map_sum]
    rw [← Finset.sum_coe_sort DH.T
      (fun x => headConst DH (a x * x))]
    rw [← Equiv.sum_comp (datumEnum DH)
      (fun y : ↥DH.T => headConst DH (a (y : WPHead K w N) * (y : WPHead K w N)))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, headConst_datumEnum]
    ring
  have htu : IsUnit (headConst DH (piHead ϖ) ^ ℓ) :=
    ((isUnit_piHead ϖ).map (headConst DH)).pow ℓ
  rw [hmap] at htu
  exact isUnit_of_mul_isUnit_left htu

variable {K w N} in
/-- The Gauss norm of a Tate variable in the head model is at most `1`. -/
theorem norm_qX_le_one (DH : RationalLocData (WPHead K w N)) (i : Fin DH.T.card) :
    ‖qX DH i‖ ≤ 1 := by
  classical
  refine le_trans (Ideal.Quotient.norm_mk_le _ _) ?_
  rw [MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
  refine Real.iSup_le (fun t => ?_) zero_le_one
  rw [FiniteJet.finsupp_prod_one, mul_one, coeff_polyToP, MvPolynomial.coeff_X']
  split_ifs
  · exact le_of_eq norm_one
  · rw [norm_zero]
    exact zero_le_one

variable {K w N} in
/-- The algebraic forward map of the head bridge: `IsLocalization.Away.lift` along
the graph-model Bezout unit. -/
noncomputable def headLocFwdAlg (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    Localization.Away DH.s →+* QHead DH :=
  IsLocalization.Away.lift DH.s (isUnit_headConst_s ϖ DH hDH)

variable {K w N} in
theorem headLocFwdAlg_algebraMap (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) (x : WPHead K w N) :
    headLocFwdAlg ϖ DH hDH (algebraMap (WPHead K w N) (Localization.Away DH.s) x) =
      headConst DH x :=
  IsLocalization.Away.lift_eq _ _ x

variable {K w N} in
/-- The forward map sends `t/s` to the corresponding Tate variable. -/
theorem headLocFwdAlg_divByS (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    {t : WPHead K w N} (ht : t ∈ DH.T) :
    headLocFwdAlg ϖ DH hDH (divByS t DH.s) =
      qX DH ((datumEnum DH).symm ⟨t, ht⟩) := by
  have hu := isUnit_headConst_s ϖ DH hDH
  refine hu.mul_right_cancel ?_
  have hspec : headLocFwdAlg ϖ DH hDH (divByS t DH.s) * headConst DH DH.s =
      headConst DH t := by
    have h1 : divByS t DH.s *
        algebraMap (WPHead K w N) (Localization.Away DH.s) DH.s =
        algebraMap (WPHead K w N) (Localization.Away DH.s) t := by
      rw [divByS]
      exact IsLocalization.mk'_spec _ _ _
    calc headLocFwdAlg ϖ DH hDH (divByS t DH.s) * headConst DH DH.s
        = headLocFwdAlg ϖ DH hDH (divByS t DH.s) *
            headLocFwdAlg ϖ DH hDH
              (algebraMap (WPHead K w N) (Localization.Away DH.s) DH.s) := by
          rw [headLocFwdAlg_algebraMap]
      _ = headLocFwdAlg ϖ DH hDH (divByS t DH.s *
            algebraMap (WPHead K w N) (Localization.Away DH.s) DH.s) :=
          (map_mul _ _ _).symm
      _ = headLocFwdAlg ϖ DH hDH
            (algebraMap (WPHead K w N) (Localization.Away DH.s) t) := by rw [h1]
      _ = headConst DH t := headLocFwdAlg_algebraMap ϖ DH hDH t
  rw [hspec]
  have henum : ((datumEnum DH ((datumEnum DH).symm ⟨t, ht⟩) : ↥DH.T) :
      WPHead K w N) = t := by
    rw [Equiv.apply_symm_apply]
  calc headConst DH t
      = headConst DH ((datumEnum DH ((datumEnum DH).symm ⟨t, ht⟩) : ↥DH.T) :
          WPHead K w N) := by rw [henum]
    _ = headConst DH DH.s * qX DH ((datumEnum DH).symm ⟨t, ht⟩) :=
        headConst_datumEnum DH _
    _ = qX DH ((datumEnum DH).symm ⟨t, ht⟩) * headConst DH DH.s := mul_comm _ _

variable {K w N} in
theorem headLocFwdAlg_continuous (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    @Continuous _ _ DH.topology _ (headLocFwdAlg ϖ DH hDH) := by
  refine locTopology_continuous_lift DH.P DH.T DH.s DH.hopen _ ?_ ?_
  · have h_eq : (headLocFwdAlg ϖ DH hDH).comp
        (algebraMap (WPHead K w N) (Localization.Away DH.s)) = headConst DH :=
      RingHom.ext fun x => headLocFwdAlg_algebraMap ϖ DH hDH x
    rw [show ⇑((headLocFwdAlg ϖ DH hDH).comp
        (algebraMap (WPHead K w N) (Localization.Away DH.s))) = ⇑(headConst DH)
      from congrArg _ h_eq]
    exact headConst_continuous DH
  · intro t ht
    rw [headLocFwdAlg_divByS ϖ DH hDH ht]
    exact FiniteJet.isPowerBounded_of_norm_le_one (norm_qX_le_one DH _)

variable {K w N} in
/-- The evaluation targets of the reverse bridge: the `T/s`-fractions in the
completed localization. -/
noncomputable def revB (DH : RationalLocData (WPHead K w N)) (i : Fin DH.T.card) :
    presheafValue DH :=
  DH.coeRingHom (divByS ((datumEnum DH i : ↥DH.T) : WPHead K w N) DH.s)

variable {K w N} in
theorem isPowerBounded_revB (DH : RationalLocData (WPHead K w N))
    (i : Fin DH.T.card) : TopologicalRing.IsPowerBounded (revB DH i) := by
  have hmem : divByS ((datumEnum DH i : ↥DH.T) : WPHead K w N) DH.s ∈
      locSubring DH.P DH.T DH.s :=
    divByS_mem_locSubring _ _ _ (datumEnum DH i).2
  refine (CompletionLocalization.coeRingHom_image_locSubring_isBounded DH).subset ?_
  rintro _ ⟨n, rfl⟩
  refine ⟨divByS ((datumEnum DH i : ↥DH.T) : WPHead K w N) DH.s ^ n,
    pow_mem hmem n, ?_⟩
  rw [map_pow]
  rfl

variable {K w N} in
/-- The reverse bridge at the Tate-algebra level: `restrictedEval` at the
`T/s`-fractions (the `chartEval` pattern, done generically by `WP/Evaluation`). -/
noncomputable def headLocRevP (DH : RationalLocData (WPHead K w N)) :
    P (WPHead K w N) DH.T.card →+* presheafValue DH :=
  restrictedEval DH.canonicalMap (canonicalMap_continuous DH) (revB DH)
    (fun i => isPowerBounded_revB DH i)

variable {K w N} in
theorem headLocRevP_continuous (DH : RationalLocData (WPHead K w N)) :
    Continuous (headLocRevP DH) :=
  restrictedEval_continuous DH.canonicalMap (canonicalMap_continuous DH) (revB DH)
    (fun i => isPowerBounded_revB DH i)

variable {K w N} in
theorem headLocRevP_C (DH : RationalLocData (WPHead K w N)) (x : WPHead K w N) :
    headLocRevP DH (polyToP (MvPolynomial.C x)) = DH.canonicalMap x := by
  unfold headLocRevP
  exact restrictedEval_C _ _ _ _ x

variable {K w N} in
theorem headLocRevP_X (DH : RationalLocData (WPHead K w N)) (i : Fin DH.T.card) :
    headLocRevP DH (polyToP (MvPolynomial.X i)) = revB DH i := by
  unfold headLocRevP
  exact restrictedEval_X _ _ _ _ i

variable {K w N} in
/-- The graph relations die in the completed localization: `s·(t/s) = t`. -/
theorem headLocRevP_graphRel (DH : RationalLocData (WPHead K w N))
    (i : Fin DH.T.card) : headLocRevP DH (headGraphRel DH i) = 0 := by
  have hsplit : headGraphRel DH i =
      polyToP (MvPolynomial.C DH.s) * polyToP (MvPolynomial.X i) -
        polyToP (MvPolynomial.C ((datumEnum DH i : ↥DH.T) : WPHead K w N)) := by
    rw [headGraphRel, map_sub, map_mul]
  rw [hsplit, map_sub, map_mul, headLocRevP_C, headLocRevP_X, headLocRevP_C]
  have hloc : algebraMap (WPHead K w N) (Localization.Away DH.s) DH.s *
      divByS ((datumEnum DH i : ↥DH.T) : WPHead K w N) DH.s =
      algebraMap (WPHead K w N) (Localization.Away DH.s)
        ((datumEnum DH i : ↥DH.T) : WPHead K w N) := by
    rw [mul_comm, divByS]
    exact IsLocalization.mk'_spec _ _ _
  have hprod : DH.canonicalMap DH.s * revB DH i =
      DH.coeRingHom (algebraMap (WPHead K w N) (Localization.Away DH.s) DH.s *
        divByS ((datumEnum DH i : ↥DH.T) : WPHead K w N) DH.s) := by
    rw [map_mul]
    rfl
  rw [hprod, hloc]
  have hcan : DH.coeRingHom (algebraMap (WPHead K w N) (Localization.Away DH.s)
      ((datumEnum DH i : ↥DH.T) : WPHead K w N)) =
      DH.canonicalMap ((datumEnum DH i : ↥DH.T) : WPHead K w N) := rfl
  rw [hcan]
  exact sub_self _

variable {K w N} in
theorem headGraphIdeal_le_ker (DH : RationalLocData (WPHead K w N)) :
    headGraphIdeal DH ≤ RingHom.ker (headLocRevP DH) := by
  have hker_closed : IsClosed ((RingHom.ker (headLocRevP DH) :
      Ideal (P (WPHead K w N) DH.T.card)) : Set (P (WPHead K w N) DH.T.card)) := by
    have hset : ((RingHom.ker (headLocRevP DH) :
        Ideal (P (WPHead K w N) DH.T.card)) : Set (P (WPHead K w N) DH.T.card)) =
        headLocRevP DH ⁻¹' {0} := by
      ext y
      simp [RingHom.mem_ker]
    rw [hset]
    exact IsClosed.preimage (headLocRevP_continuous DH) isClosed_singleton
  have hspan : (Ideal.span (Set.range (headGraphRel DH)) :
      Set (P (WPHead K w N) DH.T.card)) ⊆
      ((RingHom.ker (headLocRevP DH) : Ideal _) : Set _) := by
    have h1 : Ideal.span (Set.range (headGraphRel DH)) ≤
        RingHom.ker (headLocRevP DH) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact RingHom.mem_ker.mpr (headLocRevP_graphRel DH i)
    exact fun x hx => h1 hx
  intro x hx
  have hx' : x ∈ closure ((Ideal.span (Set.range (headGraphRel DH)) : Ideal _) :
      Set (P (WPHead K w N) DH.T.card)) := by
    rw [← Ideal.coe_closure]
    exact hx
  exact closure_minimal hspan hker_closed hx'

variable {K w N} in
/-- The reverse bridge, descended to the graph model. -/
noncomputable def headLocRev (DH : RationalLocData (WPHead K w N)) :
    QHead DH →+* presheafValue DH :=
  Ideal.Quotient.lift (headGraphIdeal DH) (headLocRevP DH)
    (fun a ha => RingHom.mem_ker.mp (headGraphIdeal_le_ker DH ha))

variable {K w N} in
theorem headLocRev_mk (DH : RationalLocData (WPHead K w N))
    (G : P (WPHead K w N) DH.T.card) :
    headLocRev DH (Ideal.Quotient.mk (headGraphIdeal DH) G) = headLocRevP DH G :=
  Ideal.Quotient.lift_mk _ _ _

variable {K w N} in
theorem headLocRev_continuous (DH : RationalLocData (WPHead K w N)) :
    Continuous (headLocRev DH) := by
  refine continuous_of_continuousAt_zero (headLocRev DH).toAddMonoidHom ?_
  show Filter.Tendsto _ (nhds 0) (nhds _)
  rw [show (headLocRev DH).toAddMonoidHom (0 : QHead DH) = 0 from map_zero _]
  refine Filter.tendsto_def.mpr fun U hU => ?_
  have hrevP := (headLocRevP_continuous DH).tendsto 0
  rw [show headLocRevP DH 0 = 0 from map_zero _] at hrevP
  obtain ⟨δ, hδ0, hball⟩ := Metric.mem_nhds_iff.mp (hrevP hU)
  refine Filter.mem_of_superset (Metric.ball_mem_nhds 0 hδ0) fun q hq => ?_
  rw [Set.mem_preimage]
  rw [Metric.mem_ball, dist_zero_right] at hq
  obtain ⟨G, hG, hGn⟩ := Ideal.Quotient.norm_mk_lt q
    (show (0 : ℝ) < δ - ‖q‖ by linarith)
  have hq' : headLocRev DH q = headLocRevP DH G := by
    rw [← hG, headLocRev_mk]
  show headLocRev DH q ∈ U
  rw [hq']
  refine hball ?_
  rw [Metric.mem_ball, dist_zero_right]
  calc ‖G‖ < ‖q‖ + (δ - ‖q‖) := hGn
    _ = δ := by rw [add_sub_cancel]

/-! ### The head bridge `presheafValue ≃ QHead` -/

variable {K w N} in
/-- The forward bridge on the completion. -/
noncomputable def headLocFwd (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    presheafValue DH →+* QHead DH := by
  letI := DH.uniformSpace
  letI : IsTopologicalRing (Localization.Away DH.s) := DH.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away DH.s) := DH.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom (headLocFwdAlg ϖ DH hDH)
    (headLocFwdAlg_continuous ϖ DH hDH)

variable {K w N} in
theorem headLocFwd_coe (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    (a : Localization.Away DH.s) :
    headLocFwd ϖ DH hDH (DH.coeRingHom a) = headLocFwdAlg ϖ DH hDH a := by
  letI := DH.uniformSpace
  letI : IsTopologicalRing (Localization.Away DH.s) := DH.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away DH.s) := DH.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe (headLocFwdAlg ϖ DH hDH)
    (headLocFwdAlg_continuous ϖ DH hDH) a

variable {K w N} in
theorem headLocFwd_continuous (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    Continuous (headLocFwd ϖ DH hDH) := by
  letI := DH.uniformSpace
  exact UniformSpace.Completion.continuous_extension

variable {K w N} in
theorem continuous_mk_headGraphIdeal (DH : RationalLocData (WPHead K w N)) :
    Continuous (Ideal.Quotient.mk (headGraphIdeal DH)) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun a b => ?_).continuous
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
  exact Ideal.Quotient.norm_mk_le _ _

variable {K w N} in
/-- The composite `rev ∘ fwdAlg` is the completion map (agreement on the
localization generators). -/
theorem headLocRev_comp_fwdAlg (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    (headLocRev DH).comp (headLocFwdAlg ϖ DH hDH) = DH.coeRingHom := by
  refine IsLocalization.ringHom_ext (Submonoid.powers DH.s) ?_
  ext x
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
    headLocFwdAlg_algebraMap]
  rw [show headConst DH x =
    Ideal.Quotient.mk (headGraphIdeal DH) (polyToP (MvPolynomial.C x)) from rfl]
  rw [headLocRev_mk, headLocRevP_C]
  rfl

variable {K w N} in
theorem headLocRev_headLocFwd (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    (x : presheafValue DH) :
    headLocRev DH (headLocFwd ϖ DH hDH x) = x := by
  letI := DH.uniformSpace
  have hdense : DenseRange (⇑DH.coeRingHom) :=
    @UniformSpace.Completion.denseRange_coe _ DH.uniformSpace
  have hfun : ⇑(headLocRev DH) ∘ ⇑(headLocFwd ϖ DH hDH) =
      (id : presheafValue DH → presheafValue DH) := by
    refine hdense.equalizer
      ((headLocRev_continuous DH).comp (headLocFwd_continuous ϖ DH hDH))
      continuous_id ?_
    funext l
    show headLocRev DH (headLocFwd ϖ DH hDH (DH.coeRingHom l)) = DH.coeRingHom l
    rw [headLocFwd_coe]
    exact RingHom.congr_fun (headLocRev_comp_fwdAlg ϖ DH hDH) l
  exact congrFun hfun x

variable {K w N} in
/-- The forward bridge sends the `T/s`-fraction to the corresponding variable. -/
theorem headLocFwd_revB (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    (i : Fin DH.T.card) :
    headLocFwd ϖ DH hDH (revB DH i) = qX DH i := by
  rw [revB, headLocFwd_coe, headLocFwdAlg_divByS ϖ DH hDH (datumEnum DH i).2]
  congr 1
  rw [show (⟨((datumEnum DH i : ↥DH.T) : WPHead K w N), (datumEnum DH i).2⟩ :
    ↥DH.T) = datumEnum DH i from Subtype.coe_eta _ _]
  exact Equiv.symm_apply_apply _ _

variable {K w N} in
theorem headLocFwd_headLocRev (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) (q : QHead DH) :
    headLocFwd ϖ DH hDH (headLocRev DH q) = q := by
  obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective (I := headGraphIdeal DH) q
  rw [headLocRev_mk]
  have hpoly : ∀ Q : MvPolynomial (Fin DH.T.card) (WPHead K w N),
      headLocFwd ϖ DH hDH (headLocRevP DH (polyToP Q)) =
        Ideal.Quotient.mk (headGraphIdeal DH) (polyToP Q) := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C x =>
      rw [headLocRevP_C,
        show DH.canonicalMap x = DH.coeRingHom
          (algebraMap (WPHead K w N) (Localization.Away DH.s) x) from rfl,
        headLocFwd_coe, headLocFwdAlg_algebraMap]
      rfl
    | add p q hp hq =>
      rw [map_add, map_add, map_add, map_add, hp, hq]
      rfl
    | mul_X p i hp =>
      rw [map_mul, map_mul, map_mul, map_mul, hp, headLocRevP_X,
        headLocFwd_revB]
      rfl
  have h1 : ⇑((headLocFwd ϖ DH hDH).comp (headLocRevP DH)) =
      ⇑(Ideal.Quotient.mk (headGraphIdeal DH)) := by
    refine denseRange_polyToP.equalizer
      ((headLocFwd_continuous ϖ DH hDH).comp (headLocRevP_continuous DH))
      (continuous_mk_headGraphIdeal DH) ?_
    funext Q
    exact hpoly Q
  exact congrFun h1 G

variable {K w N} in
/-- **The head graph-model bridge**: the completed rational localization of the
strongly noetherian head is its graph quotient ([WP] eq:graph-model
`E_α ≅ P_E/J̄_{E,α}`; forward via `IsLocalization.Away.lift` — `s` is a unit in the
quotient by the Bezout trick of [WP] lem:koszul's proof — and back via the evaluation
gadget `restrictedEval` at the power-bounded tuple `T_i ↦ t_i/s`). -/
noncomputable def headLocEquiv (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    presheafValue DH ≃+* QHead DH :=
  { toFun := headLocFwd ϖ DH hDH
    invFun := headLocRev DH
    left_inv := headLocRev_headLocFwd ϖ DH hDH
    right_inv := headLocFwd_headLocRev ϖ DH hDH
    map_mul' := map_mul _
    map_add' := map_add _ }

variable {K w N} in
theorem headLocEquiv_continuous (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    Continuous (headLocEquiv ϖ hK₀ DH hDH) :=
  headLocFwd_continuous ϖ DH hDH

variable {K w N} in
theorem headLocEquiv_symm_continuous (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    Continuous (headLocEquiv ϖ hK₀ DH hDH).symm :=
  headLocRev_continuous DH

/-! ### The lifted datum and the coefficientwise model over `𝒜` -/

/-- The unit-ball pair of definition of `𝒜`, at a norm-window constant of `K`
(`exists_norm_window'` — unconditional for a nontrivially normed field). -/
noncomputable def wpaPod : PairOfDefinition (WPA K w) :=
  FiniteJet.unitBallPod (constA K w (Classical.choose (exists_norm_window' K)))
    ((Classical.choose_spec (exists_norm_window' K)).1.map (constA K w))
    (by rw [norm_constA]
        exact (Classical.choose_spec (exists_norm_window' K)).2.1)
    (by rw [norm_constA]
        exact (Classical.choose_spec (exists_norm_window' K)).2.2)
    (fun x => by
      rw [norm_constA]
      exact norm_constA_mul K w (Classical.choose (exists_norm_window' K)) x)

variable {K w N} in
open scoped Classical in
/-- Rationality lifts along `headIncl`: the unit ideal is generated by the lifted
entries. -/
theorem span_image_headIncl_eq_top (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) :
    Ideal.span ((DH.T.image (headIncl K w N) : Finset (WPA K w)) : Set (WPA K w)) =
      ⊤ := by
  classical
  have hspan := hDH.span_eq_top
  rw [Finset.coe_image, ← Ideal.map_span (headIncl K w N), hspan, Ideal.map_top]

variable {K w N} in
open scoped Classical in
/-- The lift of a head rational datum to `𝒜` (entries via `headIncl`, unit-ball pair
of definition; [WP] §6.4: the datum "lies in the finite head").  (2026-07-29: the
rationality hypothesis was added to the signature — the lifted `hopen` field is the
span-openness of the lifted entries, which needs `DH` rational; [WP]'s corollary
only ever lifts rational data.) -/
noncomputable def liftDatum (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) : RationalLocData (WPA K w) :=
  genPieceDatum (wpaPod K w) (DH.T.image (headIncl K w N)) (headIncl K w N DH.s)
    (span_image_headIncl_eq_top DH hDH)

variable {K w N} in
open scoped Classical in
theorem liftDatum_T (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    (liftDatum DH hDH).T = DH.T.image (headIncl K w N) := rfl

variable {K w N} in
theorem liftDatum_s (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    (liftDatum DH hDH).s = headIncl K w N DH.s := rfl

variable {K w N} in
theorem liftDatum_isRational (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) : (liftDatum DH hDH).IsRational :=
  RationalLocData.isRational_of_span_eq_top
    (span_image_headIncl_eq_top DH hDH)

variable {K w N} in
theorem TailC0.map_ofHead {P Q : Type*} [NormedCommRing P] [IsUltrametricDist P]
    [NormedCommRing Q] [IsUltrametricDist Q] {ρ : TwistElem P} {ρ' : TwistElem Q}
    {w' : ℕ → ℕ} {N' : ℕ} (φ : P →+* Q) (hφ : ∀ p, ‖φ p‖ ≤ ‖p‖)
    (hρ : φ ρ.val = ρ'.val) (p : P) :
    TailC0.map (w' := w') (N' := N') φ hφ hρ (TailC0.ofHead p) =
      TailC0.ofHead (φ p) := by
  refine Subtype.ext (funext fun μ => ?_)
  show φ ((TailC0.ofHead p : TailC0 w' N' P ρ).1 μ) =
    (TailC0.ofHead (φ p) : TailC0 w' N' Q ρ').1 μ
  rw [show (TailC0.ofHead p : TailC0 w' N' P ρ).1 μ = if μ = 0 then p else 0
      from rfl,
    show (TailC0.ofHead (φ p) : TailC0 w' N' Q ρ').1 μ = if μ = 0 then φ p else 0
      from rfl]
  split_ifs
  · rfl
  · exact map_zero φ

variable {K w N} in
theorem headConst_WaHead (DH : RationalLocData (WPHead K w N)) :
    headConst DH (WaHead K w N) = (rhoQ DH).val := rfl

variable {K w N} in
theorem wpaTailEquiv_isometry (f g : WPA K w) :
    dist ((wpaTailEquiv (K := K) (w := w) (N := N)) f)
      ((wpaTailEquiv (K := K) (w := w) (N := N)) g) = dist f g := by
  rw [dist_eq_norm, dist_eq_norm,
    show (wpaTailEquiv (K := K) (w := w) (N := N)) f -
        (wpaTailEquiv (K := K) (w := w) (N := N)) g =
      (wpaTailEquiv (K := K) (w := w) (N := N)) (f - g) from (map_sub _ _ _).symm]
  rw [show ‖(wpaTailEquiv (K := K) (w := w) (N := N)) (f - g)‖ =
    ⨆ μ : TailIdx N, ‖tailCoeff K w N μ (f - g)‖ from rfl]
  exact (norm_eq_iSup_tailCoeff K w N (f - g)).symm

variable {K w N} in
theorem wpaTailEquiv_continuous :
    Continuous (wpaTailEquiv (K := K) (w := w) (N := N)) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun f g => ?_).continuous
  rw [NNReal.coe_one, one_mul, wpaTailEquiv_isometry]

variable {K w N} in
/-- The coefficientwise base homomorphism `𝒜 → ⊕̂ Q e_μ`. -/
noncomputable def coeffBase (DH : RationalLocData (WPHead K w N)) :
    WPA K w →+* TailC0 w N (QHead DH) (rhoQ DH) :=
  (TailC0.map (headConst DH) (norm_headConst_le DH)
      (headConst_WaHead DH)).comp
    (wpaTailEquiv (K := K) (w := w) (N := N) : WPA K w ≃+* _).toRingHom

variable {K w N} in
theorem coeffBase_continuous (DH : RationalLocData (WPHead K w N)) :
    Continuous (coeffBase DH) := by
  rw [coeffBase, RingHom.coe_comp]
  exact (TailC0.map_continuous (headConst DH) (norm_headConst_le DH)
    (headConst_WaHead DH)).comp
    (by exact wpaTailEquiv_continuous (K := K) (w := w) (N := N))

variable {K w N} in
theorem coeffBase_headIncl (DH : RationalLocData (WPHead K w N)) (x : WPHead K w N) :
    coeffBase DH (headIncl K w N x) = TailC0.ofHead (headConst DH x) := by
  rw [coeffBase, RingHom.comp_apply]
  rw [show ((wpaTailEquiv (K := K) (w := w) (N := N) : WPA K w ≃+* _).toRingHom
      (headIncl K w N x)) =
    (wpaTailEquiv (K := K) (w := w) (N := N)) (headIncl K w N x) from rfl]
  rw [wpaTailEquiv_headIncl]
  exact TailC0.map_ofHead (headConst DH) (norm_headConst_le DH)
    (headConst_WaHead DH) x

variable {K w N} in
theorem isUnit_coeffBase_s (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    IsUnit (coeffBase DH (headIncl K w N DH.s)) := by
  rw [coeffBase_headIncl]
  exact (isUnit_headConst_s ϖ DH hDH).map
    (TailC0.ofHead (w := w) (N := N) (ρ := rhoQ DH) :
      QHead DH →+* TailC0 w N (QHead DH) (rhoQ DH))

variable {K w N} in
/-- The algebraic forward map of the coefficientwise bridge. -/
noncomputable def coeffFwdAlg (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    Localization.Away (liftDatum DH hDH).s →+*
      TailC0 w N (QHead DH) (rhoQ DH) :=
  IsLocalization.Away.lift (liftDatum DH hDH).s
    (show IsUnit (coeffBase DH (liftDatum DH hDH).s) from
      isUnit_coeffBase_s ϖ DH hDH)

variable {K w N} in
theorem coeffFwdAlg_algebraMap (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) (f : WPA K w) :
    coeffFwdAlg ϖ DH hDH
      (algebraMap (WPA K w) (Localization.Away (liftDatum DH hDH).s) f) =
      coeffBase DH f :=
  IsLocalization.Away.lift_eq _ _ f

variable {K w N} in
/-- The forward map sends the lifted `t/s`-fraction to `ofHead` of the
corresponding graph variable. -/
theorem coeffFwdAlg_divByS (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    {t₀ : WPHead K w N} (ht₀ : t₀ ∈ DH.T) :
    coeffFwdAlg ϖ DH hDH (divByS (headIncl K w N t₀) (liftDatum DH hDH).s) =
      TailC0.ofHead (qX DH ((datumEnum DH).symm ⟨t₀, ht₀⟩)) := by
  have hu : IsUnit (coeffBase DH (liftDatum DH hDH).s) :=
    isUnit_coeffBase_s ϖ DH hDH
  refine hu.mul_right_cancel ?_
  have h1 : divByS (headIncl K w N t₀) (liftDatum DH hDH).s *
      algebraMap (WPA K w) (Localization.Away (liftDatum DH hDH).s)
        (liftDatum DH hDH).s =
      algebraMap (WPA K w) (Localization.Away (liftDatum DH hDH).s)
        (headIncl K w N t₀) := by
    rw [divByS]
    exact IsLocalization.mk'_spec _ _ _
  rw [← coeffFwdAlg_algebraMap ϖ DH hDH (liftDatum DH hDH).s, ← map_mul, h1,
    coeffFwdAlg_algebraMap]
  have henum : coeffBase DH (headIncl K w N t₀) =
      TailC0.ofHead (headConst DH DH.s) *
        TailC0.ofHead (qX DH ((datumEnum DH).symm ⟨t₀, ht₀⟩)) := by
    rw [coeffBase_headIncl]
    have h2 := headConst_datumEnum DH ((datumEnum DH).symm ⟨t₀, ht₀⟩)
    rw [Equiv.apply_symm_apply] at h2
    rw [show ((⟨t₀, ht₀⟩ : ↥DH.T) : WPHead K w N) = t₀ from rfl] at h2
    rw [h2, map_mul]
  have hcs : coeffBase DH (liftDatum DH hDH).s =
      TailC0.ofHead (headConst DH DH.s) := coeffBase_headIncl DH DH.s
  rw [henum, coeffFwdAlg_algebraMap, hcs]
  exact mul_comm _ _

variable {K w N} in
theorem coeffFwdAlg_continuous (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    @Continuous _ _ (liftDatum DH hDH).topology _ (coeffFwdAlg ϖ DH hDH) := by
  classical
  refine locTopology_continuous_lift (liftDatum DH hDH).P (liftDatum DH hDH).T
    (liftDatum DH hDH).s (liftDatum DH hDH).hopen _ ?_ ?_
  · have h_eq : (coeffFwdAlg ϖ DH hDH).comp
        (algebraMap (WPA K w) (Localization.Away (liftDatum DH hDH).s)) =
        coeffBase DH :=
      RingHom.ext fun f => coeffFwdAlg_algebraMap ϖ DH hDH f
    rw [show ⇑((coeffFwdAlg ϖ DH hDH).comp
        (algebraMap (WPA K w) (Localization.Away (liftDatum DH hDH).s))) =
      ⇑(coeffBase DH) from congrArg _ h_eq]
    exact coeffBase_continuous DH
  · intro t ht
    rw [show (liftDatum DH hDH).T = DH.T.image (headIncl K w N) from rfl] at ht
    obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
    rw [coeffFwdAlg_divByS ϖ DH hDH ht₀]
    refine FiniteJet.isPowerBounded_of_norm_le_one ?_
    rw [TailC0.norm_ofHead]
    exact norm_qX_le_one DH _

variable {K w N} in
/-- The forward coefficientwise bridge on the completion. -/
noncomputable def coeffFwd (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    presheafValue (liftDatum DH hDH) →+* TailC0 w N (QHead DH) (rhoQ DH) := by
  letI := (liftDatum DH hDH).uniformSpace
  letI : IsTopologicalRing (Localization.Away (liftDatum DH hDH).s) :=
    (liftDatum DH hDH).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (liftDatum DH hDH).s) :=
    (liftDatum DH hDH).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom (coeffFwdAlg ϖ DH hDH)
    (coeffFwdAlg_continuous ϖ DH hDH)

variable {K w N} in
theorem coeffFwd_coe (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    (a : Localization.Away (liftDatum DH hDH).s) :
    coeffFwd ϖ DH hDH ((liftDatum DH hDH).coeRingHom a) =
      coeffFwdAlg ϖ DH hDH a := by
  letI := (liftDatum DH hDH).uniformSpace
  letI : IsTopologicalRing (Localization.Away (liftDatum DH hDH).s) :=
    (liftDatum DH hDH).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (liftDatum DH hDH).s) :=
    (liftDatum DH hDH).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe (coeffFwdAlg ϖ DH hDH)
    (coeffFwdAlg_continuous ϖ DH hDH) a

variable {K w N} in
theorem coeffFwd_continuous (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    Continuous (coeffFwd ϖ DH hDH) := by
  letI := (liftDatum DH hDH).uniformSpace
  exact UniformSpace.Completion.continuous_extension

variable {K w N} in
/-- The base of the head-to-lifted-presheaf comparison: constants of the head into
the completed lifted localization. -/
noncomputable def liftConst (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) : WPHead K w N →+* presheafValue (liftDatum DH hDH) :=
  ((liftDatum DH hDH).canonicalMap).comp (headIncl K w N : WPHead K w N →+* WPA K w)

variable {K w N} in
theorem liftConst_continuous (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) : Continuous (liftConst DH hDH) := by
  rw [liftConst, RingHom.coe_comp]
  refine (canonicalMap_continuous (liftDatum DH hDH)).comp ?_
  refine AddMonoidHomClass.continuous_of_bound
    (headIncl K w N : WPHead K w N →+* WPA K w) 1 fun x => ?_
  rw [one_mul, norm_headIncl]

variable {K w N} in
theorem isUnit_liftConst_s (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) : IsUnit (liftConst DH hDH DH.s) :=
  isUnit_s_in_presheafValue (liftDatum DH hDH)

variable {K w N} in
/-- The algebraic head-to-lifted comparison. -/
noncomputable def headToLiftAlg (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) :
    Localization.Away DH.s →+* presheafValue (liftDatum DH hDH) :=
  IsLocalization.Away.lift DH.s (isUnit_liftConst_s DH hDH)

variable {K w N} in
theorem headToLiftAlg_algebraMap (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) (x : WPHead K w N) :
    headToLiftAlg DH hDH
      (algebraMap (WPHead K w N) (Localization.Away DH.s) x) =
      liftConst DH hDH x :=
  IsLocalization.Away.lift_eq _ _ x

variable {K w N} in
/-- The comparison sends head fractions to lifted fractions. -/
theorem headToLiftAlg_divByS (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) {t₀ : WPHead K w N} (ht₀ : t₀ ∈ DH.T) :
    headToLiftAlg DH hDH (divByS t₀ DH.s) =
      (liftDatum DH hDH).coeRingHom
        (divByS (headIncl K w N t₀) (liftDatum DH hDH).s) := by
  have hu := isUnit_liftConst_s DH hDH
  refine hu.mul_right_cancel ?_
  have h1 : divByS t₀ DH.s *
      algebraMap (WPHead K w N) (Localization.Away DH.s) DH.s =
      algebraMap (WPHead K w N) (Localization.Away DH.s) t₀ := by
    rw [divByS]
    exact IsLocalization.mk'_spec _ _ _
  rw [← headToLiftAlg_algebraMap DH hDH DH.s, ← map_mul, h1,
    headToLiftAlg_algebraMap, headToLiftAlg_algebraMap]
  have h2 : divByS (headIncl K w N t₀) (liftDatum DH hDH).s *
      algebraMap (WPA K w) (Localization.Away (liftDatum DH hDH).s)
        (liftDatum DH hDH).s =
      algebraMap (WPA K w) (Localization.Away (liftDatum DH hDH).s)
        (headIncl K w N t₀) := by
    rw [divByS]
    exact IsLocalization.mk'_spec _ _ _
  have h3 : liftConst DH hDH DH.s =
      (liftDatum DH hDH).coeRingHom
        (algebraMap (WPA K w) (Localization.Away (liftDatum DH hDH).s)
          (liftDatum DH hDH).s) := rfl
  have h4 : liftConst DH hDH t₀ = (liftDatum DH hDH).coeRingHom
      (algebraMap (WPA K w) (Localization.Away (liftDatum DH hDH).s)
        (headIncl K w N t₀)) := rfl
  rw [h4, h3, ← map_mul, h2]

variable {K w N} in
theorem headToLiftAlg_continuous (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) :
    @Continuous _ _ DH.topology _ (headToLiftAlg DH hDH) := by
  classical
  refine locTopology_continuous_lift DH.P DH.T DH.s DH.hopen _ ?_ ?_
  · have h_eq : (headToLiftAlg DH hDH).comp
        (algebraMap (WPHead K w N) (Localization.Away DH.s)) =
        liftConst DH hDH :=
      RingHom.ext fun x => headToLiftAlg_algebraMap DH hDH x
    rw [show ⇑((headToLiftAlg DH hDH).comp
        (algebraMap (WPHead K w N) (Localization.Away DH.s))) =
      ⇑(liftConst DH hDH) from congrArg _ h_eq]
    exact liftConst_continuous DH hDH
  · intro t ht
    rw [headToLiftAlg_divByS DH hDH ht]
    have hmem : divByS (headIncl K w N t) (liftDatum DH hDH).s ∈
        locSubring (liftDatum DH hDH).P (liftDatum DH hDH).T
          (liftDatum DH hDH).s := by
      refine divByS_mem_locSubring _ _ _ ?_
      rw [show (liftDatum DH hDH).T = DH.T.image (headIncl K w N) from rfl]
      exact Finset.mem_image_of_mem _ ht
    refine (CompletionLocalization.coeRingHom_image_locSubring_isBounded
      (liftDatum DH hDH)).subset ?_
    rintro _ ⟨n, rfl⟩
    refine ⟨divByS (headIncl K w N t) (liftDatum DH hDH).s ^ n,
      pow_mem hmem n, ?_⟩
    rw [map_pow]

variable {K w N} in
/-- The head-to-lifted-presheaf comparison on completions. -/
noncomputable def headToLift (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) :
    presheafValue DH →+* presheafValue (liftDatum DH hDH) := by
  letI := DH.uniformSpace
  letI : IsTopologicalRing (Localization.Away DH.s) := DH.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away DH.s) := DH.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom (headToLiftAlg DH hDH)
    (headToLiftAlg_continuous DH hDH)

variable {K w N} in
theorem headToLift_coe (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) (a : Localization.Away DH.s) :
    headToLift DH hDH (DH.coeRingHom a) = headToLiftAlg DH hDH a := by
  letI := DH.uniformSpace
  letI : IsTopologicalRing (Localization.Away DH.s) := DH.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away DH.s) := DH.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe (headToLiftAlg DH hDH)
    (headToLiftAlg_continuous DH hDH) a

variable {K w N} in
theorem headToLift_continuous (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) : Continuous (headToLift DH hDH) := by
  letI := DH.uniformSpace
  exact UniformSpace.Completion.continuous_extension

variable {K w N} in
/-- The per-coefficient reverse hom `Q → 𝒪(lifted)`. -/
noncomputable def qToLift (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) : QHead DH →+* presheafValue (liftDatum DH hDH) :=
  (headToLift DH hDH).comp (headLocRev DH)

variable {K w N} in
theorem qToLift_continuous (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) : Continuous (qToLift DH hDH) := by
  rw [qToLift, RingHom.coe_comp]
  exact (headToLift_continuous DH hDH).comp (headLocRev_continuous DH)

variable {K w N} in
/-- The decomposition monomials in the completed lifted localization. -/
noncomputable def liftE (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) (μ : TailIdx N) : presheafValue (liftDatum DH hDH) :=
  (liftDatum DH hDH).canonicalMap (eTail K w N μ)

variable {K w N} in
theorem liftE_zero (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    liftE DH hDH 0 = 1 := by
  rw [liftE, show eTail K w N 0 = 1 from ?_, map_one]
  refine Subtype.ext (Subtype.ext ?_)
  show MvPowerSeries.monomial (tailShift w (0 : TailIdx N)) (1 : K) = 1
  rw [tailShift_zero]
  exact MvPowerSeries.monomial_zero_one

variable {K w N} in
theorem isBounded_range_liftE (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) :
    TopologicalRing.IsBounded (Set.range (liftE DH hDH)) := by
  refine (CompletionLocalization.coeRingHom_image_locSubring_isBounded
    (liftDatum DH hDH)).subset ?_
  rintro _ ⟨μ, rfl⟩
  refine ⟨algebraMap (WPA K w) (Localization.Away (liftDatum DH hDH).s)
    (eTail K w N μ), ?_, rfl⟩
  refine algebraMap_A₀_subset_locSubring _ _ _ ⟨eTail K w N μ, ?_, rfl⟩
  show eTail K w N μ ∈ (wpaPod K w).A₀
  show eTail K w N μ ∈ FiniteJet.unitBall (WPA K w)
  rw [FiniteJet.mem_unitBall_iff]
  rw [show eTail K w N μ = wpMonomial K w (wpMem_tailShift w μ) 1 from rfl,
    norm_wpMonomial, norm_one]

variable {K w N} in
theorem summable_revFamily (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) (x : TailC0 w N (QHead DH) (rhoQ DH)) :
    Summable (fun μ : TailIdx N => qToLift DH hDH (x.1 μ) * liftE DH hDH μ) := by
  apply summable_of_tendsto_cofinite_nonarch
  have hq : Filter.Tendsto (fun μ : TailIdx N => qToLift DH hDH (x.1 μ))
      Filter.cofinite (nhds 0) := by
    have h1 := (qToLift_continuous DH hDH).tendsto 0
    rw [map_zero] at h1
    exact h1.comp (tendsto_zero_iff_norm_tendsto_zero.mpr x.2)
  refine Filter.tendsto_def.mpr fun U hU => ?_
  obtain ⟨V, hV, hMV⟩ := isBounded_range_liftE DH hDH U hU
  refine Filter.mem_of_superset (Filter.tendsto_def.mp hq V hV) fun μ hμ => ?_
  rw [Set.mem_preimage] at hμ ⊢
  rw [mul_comm]
  exact hMV (Set.mul_mem_mul ⟨μ, rfl⟩ hμ)

variable {K w N} in
/-- The reverse coefficientwise bridge: summation of the decomposition series. -/
noncomputable def coeffRevFun (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) (x : TailC0 w N (QHead DH) (rhoQ DH)) :
    presheafValue (liftDatum DH hDH) :=
  ∑' μ : TailIdx N, qToLift DH hDH (x.1 μ) * liftE DH hDH μ

variable {K w N} in
/-- `qToLift` sends head constants to lifted constants. -/
theorem qToLift_headConst (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) (y : WPHead K w N) :
    qToLift DH hDH (headConst DH y) = liftConst DH hDH y := by
  rw [qToLift, RingHom.comp_apply]
  rw [show headConst DH y =
    Ideal.Quotient.mk (headGraphIdeal DH) (polyToP (MvPolynomial.C y)) from rfl]
  rw [headLocRev_mk, headLocRevP_C]
  rw [show DH.canonicalMap y = DH.coeRingHom
    (algebraMap (WPHead K w N) (Localization.Away DH.s) y) from rfl]
  rw [headToLift_coe, headToLiftAlg_algebraMap]

variable {K w N} in
/-- The twist goes to the lifted `W`. -/
theorem qToLift_rhoQ (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    qToLift DH hDH (rhoQ DH).val = liftConst DH hDH (WaHead K w N) := by
  rw [show (rhoQ DH).val = headConst DH (WaHead K w N) from rfl]
  exact qToLift_headConst DH hDH (WaHead K w N)

variable {K w N} in
/-- The lifted monomials obey the twisted multiplication rule. -/
theorem liftE_mul (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    (μ ν : TailIdx N) :
    liftE DH hDH μ * liftE DH hDH ν =
      liftConst DH hDH (WaHead K w N ^
        (wpWeight w μ.1 + wpWeight w ν.1 - wpWeight w (μ + ν).1)) *
        liftE DH hDH (μ + ν) := by
  rw [liftE, liftE, liftE, ← map_mul, eTail_mul]
  rw [show liftConst DH hDH (WaHead K w N ^
      (wpWeight w μ.1 + wpWeight w ν.1 - wpWeight w (μ + ν).1)) =
    (liftDatum DH hDH).canonicalMap (headIncl K w N (WaHead K w N ^
      (wpWeight w μ.1 + wpWeight w ν.1 - wpWeight w (μ + ν).1))) from rfl]
  rw [← map_mul]

/-- The sigma-antidiagonal parametrization of pairs of tail indices. -/
noncomputable def sigmaTailAntidiagEquiv (N : ℕ) :
    (Σ τ : TailIdx N, ↥(Finset.HasAntidiagonal.antidiagonal τ)) ≃
      (TailIdx N × TailIdx N) where
  toFun x := x.2.1
  invFun p := ⟨p.1 + p.2, ⟨p, Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl⟩⟩
  left_inv x := by
    obtain ⟨τ, ⟨p, hp⟩⟩ := x
    have ht : p.1 + p.2 = τ := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    subst ht
    rfl
  right_inv p := rfl

variable {K w N} in
theorem coeffRevFun_apply (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) (x : TailC0 w N (QHead DH) (rhoQ DH)) :
    coeffRevFun DH hDH x =
      ∑' μ : TailIdx N, qToLift DH hDH (x.1 μ) * liftE DH hDH μ := rfl

variable {K w N} in
/-- Multiplicativity of the reverse bridge (the Cauchy product matches the
twisted convolution). -/
theorem coeffRevFun_mul (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) (x y : TailC0 w N (QHead DH) (rhoQ DH)) :
    coeffRevFun DH hDH (x * y) = coeffRevFun DH hDH x * coeffRevFun DH hDH y := by
  classical
  rw [coeffRevFun_apply DH hDH (x * y), coeffRevFun_apply DH hDH x,
    coeffRevFun_apply DH hDH y]
  rw [tsum_mul_tsum_of_nonarchimedean (summable_revFamily DH hDH x)
    (summable_revFamily DH hDH y)]
  have hterm : ∀ τ : TailIdx N,
      qToLift DH hDH ((x * y).1 τ) * liftE DH hDH τ =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal τ,
        (qToLift DH hDH (x.1 p.1) * liftE DH hDH p.1) *
          (qToLift DH hDH (y.1 p.2) * liftE DH hDH p.2) := by
    intro τ
    calc qToLift DH hDH ((x * y).1 τ) * liftE DH hDH τ
        = (∑ p ∈ Finset.HasAntidiagonal.antidiagonal τ, qToLift DH hDH
            ((rhoQ DH).val ^ (wpWeight w p.1.1 + wpWeight w p.2.1 - wpWeight w τ.1) *
              (x.1 p.1 * y.1 p.2))) * liftE DH hDH τ := by
          rw [TailC0.mul_val, map_sum]
      _ = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal τ, qToLift DH hDH
            ((rhoQ DH).val ^ (wpWeight w p.1.1 + wpWeight w p.2.1 - wpWeight w τ.1) *
              (x.1 p.1 * y.1 p.2)) * liftE DH hDH τ := Finset.sum_mul _ _ _
      _ = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal τ,
            (qToLift DH hDH (x.1 p.1) * liftE DH hDH p.1) *
              (qToLift DH hDH (y.1 p.2) * liftE DH hDH p.2) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          have hpt : p.1 + p.2 = τ := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
          rw [map_mul, map_mul, map_pow, qToLift_rhoQ]
          have hE := liftE_mul DH hDH p.1 p.2
          rw [hpt] at hE
          rw [show (qToLift DH hDH (x.1 p.1) * liftE DH hDH p.1) *
              (qToLift DH hDH (y.1 p.2) * liftE DH hDH p.2) =
            (qToLift DH hDH (x.1 p.1) * qToLift DH hDH (y.1 p.2)) *
              (liftE DH hDH p.1 * liftE DH hDH p.2) from by ring]
          rw [hE, ← map_pow]
          ring
  rw [tsum_congr hterm]
  have hsum := (summable_revFamily DH hDH x).mul_of_nonarchimedean
    (summable_revFamily DH hDH y)
  have h1 := Equiv.tsum_eq (sigmaTailAntidiagEquiv N)
    (fun p : TailIdx N × TailIdx N =>
      (qToLift DH hDH (x.1 p.1) * liftE DH hDH p.1) *
        (qToLift DH hDH (y.1 p.2) * liftE DH hDH p.2))
  have h2 := Summable.tsum_sigma
    ((Equiv.summable_iff (sigmaTailAntidiagEquiv N)).mpr hsum)
  exact Eq.trans (tsum_congr fun τ => (Finset.tsum_subtype
    (Finset.HasAntidiagonal.antidiagonal τ)
    (fun p : TailIdx N × TailIdx N =>
      (qToLift DH hDH (x.1 p.1) * liftE DH hDH p.1) *
        (qToLift DH hDH (y.1 p.2) * liftE DH hDH p.2))).symm)
    (h1.symm.trans h2).symm

variable {K w N} in
theorem coeffRevFun_one (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) : coeffRevFun DH hDH 1 = 1 := by
  classical
  rw [coeffRevFun_apply, tsum_eq_single (0 : TailIdx N) ?_]
  · rw [show ((1 : TailC0 w N (QHead DH) (rhoQ DH))).1 0 = 1 from by
      rw [TailC0.one_val, if_pos rfl], map_one, one_mul, liftE_zero]
  · intro μ hμ
    rw [show ((1 : TailC0 w N (QHead DH) (rhoQ DH))).1 μ = 0 from by
      rw [TailC0.one_val, if_neg hμ], map_zero, zero_mul]

variable {K w N} in
theorem coeffRevFun_add (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) (x y : TailC0 w N (QHead DH) (rhoQ DH)) :
    coeffRevFun DH hDH (x + y) =
      coeffRevFun DH hDH x + coeffRevFun DH hDH y := by
  have h : HasSum (fun μ : TailIdx N =>
      qToLift DH hDH ((x + y).1 μ) * liftE DH hDH μ)
      (coeffRevFun DH hDH x + coeffRevFun DH hDH y) := by
    have h0 := ((summable_revFamily DH hDH x).hasSum).add
      ((summable_revFamily DH hDH y).hasSum)
    rw [show (fun μ : TailIdx N =>
        qToLift DH hDH ((x + y).1 μ) * liftE DH hDH μ) =
      (fun μ : TailIdx N => qToLift DH hDH (x.1 μ) * liftE DH hDH μ +
        qToLift DH hDH (y.1 μ) * liftE DH hDH μ) from funext fun μ => by
          rw [show (x + y).1 μ = x.1 μ + y.1 μ from rfl, map_add, add_mul]]
    exact h0
  exact h.tsum_eq

variable {K w N} in
/-- The reverse coefficientwise bridge as a ring homomorphism. -/
noncomputable def coeffRev (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) :
    TailC0 w N (QHead DH) (rhoQ DH) →+* presheafValue (liftDatum DH hDH) :=
  RingHom.mk' ⟨⟨coeffRevFun DH hDH, coeffRevFun_one DH hDH⟩,
    coeffRevFun_mul DH hDH⟩ (coeffRevFun_add DH hDH)

variable {K w N} in
theorem coeffRev_apply (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) (x : TailC0 w N (QHead DH) (rhoQ DH)) :
    coeffRev DH hDH x = coeffRevFun DH hDH x := rfl

variable {K w N} in
theorem coeffRev_continuous (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) : Continuous (coeffRev DH hDH) := by
  classical
  refine continuous_of_continuousAt_zero (coeffRev DH hDH).toAddMonoidHom ?_
  show Filter.Tendsto _ (nhds 0) (nhds _)
  rw [show (coeffRev DH hDH).toAddMonoidHom
    (0 : TailC0 w N (QHead DH) (rhoQ DH)) = 0 from map_zero _]
  refine Filter.tendsto_def.mpr fun U hU => ?_
  obtain ⟨U₀, hU₀⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  obtain ⟨V₁, hV₁, hMV₁⟩ := isBounded_range_liftE DH hDH U₀
    (U₀.isOpen.mem_nhds U₀.zero_mem)
  have hpre : ⇑(qToLift DH hDH) ⁻¹' V₁ ∈ nhds (0 : QHead DH) := by
    have h1 := (qToLift_continuous DH hDH).tendsto 0
    rw [map_zero] at h1
    exact h1 hV₁
  obtain ⟨δ, hδ0, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine Filter.mem_of_superset (Metric.ball_mem_nhds 0 hδ0) fun x hx => ?_
  rw [Set.mem_preimage]
  refine hU₀ ?_
  have hxnorm : ‖x‖ < δ := by rwa [Metric.mem_ball, dist_zero_right] at hx
  have hterm : ∀ μ : TailIdx N, qToLift DH hDH (x.1 μ) * liftE DH hDH μ ∈
      (U₀ : Set (presheafValue (liftDatum DH hDH))) := by
    intro μ
    have hc : qToLift DH hDH (x.1 μ) ∈ V₁ := hball (by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt (TailC0.norm_coeff_le x μ) hxnorm)
    have hin := hMV₁ (Set.mul_mem_mul ⟨μ, rfl⟩ hc)
    rwa [mul_comm] at hin
  have hHasSum := (summable_revFamily DH hDH x).hasSum
  exact U₀.isClosed.mem_of_tendsto hHasSum
    (Filter.Eventually.of_forall fun s => sum_mem fun μ _ => hterm μ)

variable {K w N} in
theorem TailC0.map_single {P Q : Type*} [NormedCommRing P] [IsUltrametricDist P]
    [NormedCommRing Q] [IsUltrametricDist Q] {ρ : TwistElem P} {ρ' : TwistElem Q}
    {w' : ℕ → ℕ} {N' : ℕ} (φ : P →+* Q) (hφ : ∀ p, ‖φ p‖ ≤ ‖p‖)
    (hρ : φ ρ.val = ρ'.val) (μ : TailIdx N') (p : P) :
    TailC0.map (w' := w') (N' := N') φ hφ hρ (TailC0.single μ p) =
      TailC0.single μ (φ p) := by
  refine Subtype.ext (funext fun ν => ?_)
  show φ ((TailC0.single μ p : TailC0 w' N' P ρ).1 ν) =
    (TailC0.single μ (φ p) : TailC0 w' N' Q ρ').1 ν
  rw [TailC0.single_val, TailC0.single_val]
  split_ifs
  · rfl
  · exact map_zero φ

variable {K w N} in
/-- `wpaTailEquiv` sends the decomposition monomial `e_μ` to the single at `μ`. -/
theorem wpaTailEquiv_eTail (μ : TailIdx N) :
    wpaTailEquiv (K := K) (w := w) (N := N) (eTail K w N μ) =
      TailC0.single μ (1 : WPHead K w N) := by
  refine Subtype.ext (funext fun ν => ?_)
  show tailCoeff K w N ν (eTail K w N μ) =
    (TailC0.single μ (1 : WPHead K w N) :
      TailC0 w N (WPHead K w N) (waTwist (K := K) (w := w) (N := N))).1 ν
  rw [TailC0.single_val,
    show eTail K w N μ = headIncl K w N 1 * eTail K w N μ from by
      rw [map_one, one_mul]]
  exact tailCoeff_headIncl_mul_eTail (K := K) (w := w) (N := N) μ ν 1

variable {K w N} in
/-- The forward bridge sends lifted decomposition monomials to singles. -/
theorem coeffFwd_liftE (ϖ : Uniformizer K) (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) (μ : TailIdx N) :
    coeffFwd ϖ DH hDH (liftE DH hDH μ) = TailC0.single μ (1 : QHead DH) := by
  rw [liftE, show (liftDatum DH hDH).canonicalMap (eTail K w N μ) =
    (liftDatum DH hDH).coeRingHom (algebraMap (WPA K w)
      (Localization.Away (liftDatum DH hDH).s) (eTail K w N μ)) from rfl,
    coeffFwd_coe, coeffFwdAlg_algebraMap]
  rw [coeffBase, RingHom.comp_apply]
  rw [show ((wpaTailEquiv (K := K) (w := w) (N := N) : WPA K w ≃+* _).toRingHom
      (eTail K w N μ)) =
    (wpaTailEquiv (K := K) (w := w) (N := N)) (eTail K w N μ) from rfl]
  rw [wpaTailEquiv_eTail]
  refine Subtype.ext (funext fun ν => ?_)
  show headConst DH ((TailC0.single (w := w)
      (ρ := waTwist (K := K) (w := w) (N := N)) μ (1 : WPHead K w N)).1 ν) =
    (TailC0.single (w := w) (ρ := rhoQ DH) μ (1 : QHead DH)).1 ν
  rw [TailC0.single_val, TailC0.single_val]
  split_ifs
  · exact map_one _
  · exact map_zero _

variable {K w N} in
/-- **Forward-inverts-reverse at the coefficient level**: `coeffFwd ∘ qToLift` is the
head inclusion `ofHead` (polynomial-density chase mirroring `headLocFwd_headLocRev`). -/
theorem coeffFwd_qToLift (ϖ : Uniformizer K) (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) (q : QHead DH) :
    coeffFwd ϖ DH hDH (qToLift DH hDH q) = TailC0.ofHead q := by
  obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective (I := headGraphIdeal DH) q
  rw [show qToLift DH hDH (Ideal.Quotient.mk (headGraphIdeal DH) G) =
    headToLift DH hDH (headLocRev DH (Ideal.Quotient.mk (headGraphIdeal DH) G))
    from rfl, headLocRev_mk]
  have hpoly : ∀ Q : MvPolynomial (Fin DH.T.card) (WPHead K w N),
      coeffFwd ϖ DH hDH (headToLift DH hDH (headLocRevP DH (polyToP Q))) =
        (TailC0.ofHead (w := w) (N := N) (ρ := rhoQ DH) :
          QHead DH →+* TailC0 w N (QHead DH) (rhoQ DH))
          (Ideal.Quotient.mk (headGraphIdeal DH) (polyToP Q)) := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C x =>
      rw [headLocRevP_C,
        show DH.canonicalMap x = DH.coeRingHom
          (algebraMap (WPHead K w N) (Localization.Away DH.s) x) from rfl,
        headToLift_coe, headToLiftAlg_algebraMap,
        show liftConst DH hDH x = (liftDatum DH hDH).coeRingHom
          (algebraMap (WPA K w) (Localization.Away (liftDatum DH hDH).s)
            (headIncl K w N x)) from rfl,
        coeffFwd_coe, coeffFwdAlg_algebraMap, coeffBase_headIncl]
      rfl
    | add p q hp hq =>
      simp only [map_add, hp, hq]
      exact (map_add (TailC0.ofHead (w := w) (N := N) (ρ := rhoQ DH) :
        QHead DH →+* TailC0 w N (QHead DH) (rhoQ DH)) _ _).symm
    | mul_X p i hp =>
      simp only [map_mul, hp, headLocRevP_X]
      rw [show revB DH i = DH.coeRingHom (divByS
          ((datumEnum DH i : ↥DH.T) : WPHead K w N) DH.s) from rfl,
        headToLift_coe, headToLiftAlg_divByS DH hDH (datumEnum DH i).2,
        coeffFwd_coe, coeffFwdAlg_divByS ϖ DH hDH (datumEnum DH i).2]
      rw [show (⟨((datumEnum DH i : ↥DH.T) : WPHead K w N),
        (datumEnum DH i).2⟩ : ↥DH.T) = datumEnum DH i from Subtype.coe_eta _ _,
        Equiv.symm_apply_apply]
      exact (map_mul (TailC0.ofHead (w := w) (N := N) (ρ := rhoQ DH) :
        QHead DH →+* TailC0 w N (QHead DH) (rhoQ DH)) _ _).symm
  have h1 : ⇑((coeffFwd ϖ DH hDH).comp ((headToLift DH hDH).comp
      (headLocRevP DH))) =
      ⇑((TailC0.ofHead (w := w) (N := N) (ρ := rhoQ DH) :
          QHead DH →+* TailC0 w N (QHead DH) (rhoQ DH)).comp
        (Ideal.Quotient.mk (headGraphIdeal DH))) := by
    refine denseRange_polyToP.equalizer
      ((coeffFwd_continuous ϖ DH hDH).comp ((headToLift_continuous DH hDH).comp
        (headLocRevP_continuous DH)))
      ((AddMonoidHomClass.continuous_of_bound
        (TailC0.ofHead (w := w) (N := N) (ρ := rhoQ DH) :
          QHead DH →+* TailC0 w N (QHead DH) (rhoQ DH)) 1 fun p => by
            rw [one_mul]
            exact le_of_eq (TailC0.norm_ofHead p)).comp
        (continuous_mk_headGraphIdeal DH)) ?_
    funext Q
    exact hpoly Q
  exact congrFun h1 G

variable {K w N} in
theorem coeffRevFun_single (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) (μ : TailIdx N) (q : QHead DH) :
    coeffRevFun DH hDH (TailC0.single μ q) =
      qToLift DH hDH q * liftE DH hDH μ := by
  classical
  rw [coeffRevFun_apply, tsum_eq_single μ ?_]
  · rw [TailC0.single_val, if_pos rfl]
  · intro ν hν
    rw [TailC0.single_val, if_neg hν, map_zero, zero_mul]

/-- Every null family is the sum of its singles ([WP] eq:coefficient-family). -/
theorem TailC0.hasSum_single {P : Type*} [NormedCommRing P] [IsUltrametricDist P]
    {ρ : TwistElem P} {w' : ℕ → ℕ} {N' : ℕ} (x : TailC0 w' N' P ρ) :
    HasSum (fun μ : TailIdx N' => TailC0.single (w := w') (ρ := ρ) μ (x.1 μ)) x := by
  classical
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hε2 : 0 < ε / 2 := by linarith
  have hfin : {μ : TailIdx N' | ¬ dist ‖x.1 μ‖ (0 : ℝ) < ε / 2}.Finite := by
    have h1 := Metric.tendsto_nhds.mp x.2 (ε / 2) hε2
    rwa [Filter.eventually_cofinite] at h1
  refine Filter.eventually_atTop.mpr ⟨hfin.toFinset, fun F hF => ?_⟩
  rw [dist_eq_norm]
  have hcoeff : ∀ ν : TailIdx N',
      ((∑ μ ∈ F, TailC0.single (w := w') (ρ := ρ) μ (x.1 μ)) - x).1 ν =
      (if ν ∈ F then x.1 ν else 0) - x.1 ν := by
    intro ν
    rw [show ((∑ μ ∈ F, TailC0.single (w := w') (ρ := ρ) μ (x.1 μ)) - x).1 ν =
      (∑ μ ∈ F, TailC0.single (w := w') (ρ := ρ) μ (x.1 μ)).1 ν - x.1 ν from rfl]
    congr 1
    rw [show (∑ μ ∈ F, TailC0.single (w := w') (ρ := ρ) μ (x.1 μ)).1 ν =
      ∑ μ ∈ F, (TailC0.single (w := w') (ρ := ρ) μ (x.1 μ)).1 ν from
        map_sum (⟨⟨fun y : TailC0 w' N' P ρ => y.1 ν, rfl⟩,
          fun a b => rfl⟩ : TailC0 w' N' P ρ →+ P) _ F]
    rw [show (∑ μ ∈ F, (TailC0.single (w := w') (ρ := ρ) μ (x.1 μ)).1 ν) =
      ∑ μ ∈ F, if ν = μ then x.1 μ else 0 from
        Finset.sum_congr rfl fun μ _ => TailC0.single_val μ (x.1 μ) ν]
    exact Finset.sum_ite_eq F ν fun μ => x.1 μ
  refine lt_of_le_of_lt (show _ ≤ ε / 2 from ?_) (by linarith)
  rw [TailC0.norm_eq_iSup_coeff]
  refine ciSup_le fun ν => ?_
  rw [show TailC0.coeff ν ((∑ μ ∈ F, TailC0.single (w := w') (ρ := ρ) μ (x.1 μ))
    - x) = ((∑ μ ∈ F, TailC0.single (w := w') (ρ := ρ) μ (x.1 μ)) - x).1 ν
    from rfl, hcoeff ν]
  by_cases hν : ν ∈ F
  · rw [if_pos hν, sub_self, norm_zero]
    exact hε2.le
  · rw [if_neg hν, zero_sub, norm_neg]
    have hν0 : ν ∉ hfin.toFinset := fun hc => hν (hF hc)
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hν0
    rw [dist_zero_right] at hν0
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _)
      (by rwa [Real.norm_eq_abs] at hν0))

variable {K w N} in
/-- Forward-after-reverse is the identity on the abstract model. -/
theorem coeffFwd_coeffRev (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    (x : TailC0 w N (QHead DH) (rhoQ DH)) :
    coeffFwd ϖ DH hDH (coeffRev DH hDH x) = x := by
  have hmap := ((summable_revFamily DH hDH x).hasSum).map
    (coeffFwd ϖ DH hDH) (coeffFwd_continuous ϖ DH hDH)
  have hfun : (⇑(coeffFwd ϖ DH hDH) ∘ fun μ : TailIdx N =>
      qToLift DH hDH (x.1 μ) * liftE DH hDH μ) =
      (fun μ : TailIdx N => TailC0.single (w := w) (ρ := rhoQ DH) μ (x.1 μ)) := by
    funext μ
    show coeffFwd ϖ DH hDH (qToLift DH hDH (x.1 μ) * liftE DH hDH μ) = _
    rw [map_mul, coeffFwd_qToLift, coeffFwd_liftE]
    rw [show (TailC0.ofHead (x.1 μ) : TailC0 w N (QHead DH) (rhoQ DH)) =
      TailC0.single 0 (x.1 μ) from rfl, TailC0.single_mul_single]
    simp only [zero_add, TailIdx.zero_val, wpWeight_zero, Nat.sub_self,
      pow_zero, one_mul, mul_one]
  rw [hfun] at hmap
  exact hmap.unique (TailC0.hasSum_single x)

variable {K w N} in
/-- The reverse bridge undoes the coefficientwise base map. -/
theorem coeffRev_coeffBase (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) (f : WPA K w) :
    coeffRev DH hDH (coeffBase DH f) = (liftDatum DH hDH).canonicalMap f := by
  have hf : (∑' μ : TailIdx N, headIncl K w N
      ((wpaTailEquiv (K := K) (w := w) (N := N) f).1 μ) * eTail K w N μ) = f :=
    (wpaTailEquiv (K := K) (w := w) (N := N)).symm_apply_apply f
  have hmap := ((summable_headIncl_eTail
      (wpaTailEquiv (K := K) (w := w) (N := N) f)).hasSum).map
    ((liftDatum DH hDH).canonicalMap) (canonicalMap_continuous (liftDatum DH hDH))
  rw [hf] at hmap
  have hfun : (⇑((liftDatum DH hDH).canonicalMap) ∘ fun μ : TailIdx N =>
      headIncl K w N ((wpaTailEquiv (K := K) (w := w) (N := N) f).1 μ) *
        eTail K w N μ) =
      (fun μ : TailIdx N => qToLift DH hDH ((coeffBase DH f).1 μ) *
        liftE DH hDH μ) := by
    funext μ
    show (liftDatum DH hDH).canonicalMap (headIncl K w N
      ((wpaTailEquiv (K := K) (w := w) (N := N) f).1 μ) * eTail K w N μ) = _
    rw [map_mul]
    rw [show (liftDatum DH hDH).canonicalMap (headIncl K w N
        ((wpaTailEquiv (K := K) (w := w) (N := N) f).1 μ)) =
      liftConst DH hDH ((wpaTailEquiv (K := K) (w := w) (N := N) f).1 μ)
        from rfl]
    rw [show (liftDatum DH hDH).canonicalMap (eTail K w N μ) = liftE DH hDH μ
      from rfl]
    rw [← qToLift_headConst DH hDH]
    rfl
  rw [hfun] at hmap
  exact ((summable_revFamily DH hDH (coeffBase DH f)).hasSum).unique hmap

variable {K w N} in
theorem coeffRev_comp_fwdAlg (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    (coeffRev DH hDH).comp (coeffFwdAlg ϖ DH hDH) =
      (liftDatum DH hDH).coeRingHom := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (liftDatum DH hDH).s) ?_
  ext f
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
    coeffFwdAlg_algebraMap]
  exact coeffRev_coeffBase DH hDH f

variable {K w N} in
/-- Reverse-after-forward is the identity on the completed localization. -/
theorem coeffRev_coeffFwd (ϖ : Uniformizer K)
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    (a : presheafValue (liftDatum DH hDH)) :
    coeffRev DH hDH (coeffFwd ϖ DH hDH a) = a := by
  letI := (liftDatum DH hDH).uniformSpace
  have hdense : DenseRange (⇑(liftDatum DH hDH).coeRingHom) :=
    @UniformSpace.Completion.denseRange_coe _ (liftDatum DH hDH).uniformSpace
  have hfun : ⇑(coeffRev DH hDH) ∘ ⇑(coeffFwd ϖ DH hDH) =
      (id : presheafValue (liftDatum DH hDH) →
        presheafValue (liftDatum DH hDH)) := by
    refine hdense.equalizer
      ((coeffRev_continuous DH hDH).comp (coeffFwd_continuous ϖ DH hDH))
      continuous_id ?_
    funext l
    show coeffRev DH hDH (coeffFwd ϖ DH hDH
      ((liftDatum DH hDH).coeRingHom l)) = (liftDatum DH hDH).coeRingHom l
    rw [coeffFwd_coe]
    exact RingHom.congr_fun (coeffRev_comp_fwdAlg ϖ DH hDH) l
  exact congrFun hfun a

variable {K w N} in
/-- **Coefficientwise localization** ([WP] prop:coefficientwise-localization:
"There is a canonical topological algebra isomorphism `𝒜_α ≅ ⊕̂^{c₀}_μ P e_μ`").
The proof route: the graph ideal over `𝒜` is closed and computed coefficientwise via
the norm-bounded head lifts (`exists_d1_lift_pow`); the quotient is `TailC0`;
forward/backward maps by `IsLocalization.Away.lift` + `restrictedEval`. -/
noncomputable def coeffLocEquiv (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    presheafValue (liftDatum DH hDH) ≃+* TailC0 w N (QHead DH) (rhoQ DH) :=
  { toFun := coeffFwd ϖ DH hDH
    invFun := coeffRev DH hDH
    left_inv := coeffRev_coeffFwd ϖ DH hDH
    right_inv := coeffFwd_coeffRev ϖ DH hDH
    map_mul' := map_mul _
    map_add' := map_add _ }

variable {K w N} in
theorem coeffLocEquiv_continuous (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    Continuous (coeffLocEquiv ϖ hK₀ DH hDH) :=
  coeffFwd_continuous ϖ DH hDH

variable {K w N} in
theorem coeffLocEquiv_symm_continuous (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    Continuous (coeffLocEquiv ϖ hK₀ DH hDH).symm :=
  coeffRev_continuous DH hDH

variable {K w N} in
/-- Compatibility of the two bridges on canonical images of head elements: the
`𝒜`-model of `ρ(headIncl x)` is the `μ = 0` family at the head model of `ρ(x)`. -/
theorem coeffLocEquiv_canonicalMap_headIncl (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) (x : WPHead K w N) :
    coeffLocEquiv ϖ hK₀ DH hDH
      ((liftDatum DH hDH).canonicalMap (headIncl K w N x)) =
      TailC0.ofHead (headLocEquiv ϖ hK₀ DH hDH (DH.canonicalMap x)) := by
  rw [show coeffLocEquiv ϖ hK₀ DH hDH
      ((liftDatum DH hDH).canonicalMap (headIncl K w N x)) =
    coeffFwd ϖ DH hDH ((liftDatum DH hDH).canonicalMap (headIncl K w N x))
      from rfl]
  rw [show (liftDatum DH hDH).canonicalMap (headIncl K w N x) =
    (liftDatum DH hDH).coeRingHom (algebraMap (WPA K w)
      (Localization.Away (liftDatum DH hDH).s) (headIncl K w N x)) from rfl,
    coeffFwd_coe, coeffFwdAlg_algebraMap, coeffBase_headIncl]
  congr 1
  rw [show headLocEquiv ϖ hK₀ DH hDH (DH.canonicalMap x) =
    headLocFwd ϖ DH hDH (DH.canonicalMap x) from rfl,
    show DH.canonicalMap x = DH.coeRingHom (algebraMap (WPHead K w N)
      (Localization.Away DH.s) x) from rfl,
    headLocFwd_coe, headLocFwdAlg_algebraMap]

/-! ### Every rational localization of `𝒜` is of finite-head form
([WP] cor:finite-head-presentation) -/

variable {K w} in
/-- A finite-head model of a rational localization of `𝒜`
([WP] cor:finite-head-presentation / eq:arbitrary-finite-head-presentation). -/
structure HeadModelData (D : RationalLocData (WPA K w)) : Type _ where
  /-- The head stage. -/
  N : ℕ
  /-- The head datum. -/
  DH : RationalLocData (WPHead K w N)
  /-- The head datum is rational. -/
  hDH : DH.IsRational
  /-- The lifted datum cuts the same rational subset as `D`. -/
  hopen : rationalOpen (liftDatum DH hDH).T (liftDatum DH hDH).s =
    rationalOpen D.T D.s
  /-- The model isomorphism. -/
  e : presheafValue D ≃+* TailC0 w N (QHead DH) (rhoQ DH)
  /-- Forward continuity. -/
  he : Continuous e
  /-- Backward continuity. -/
  he' : Continuous e.symm

variable {K w} in
/-- Uniform head approximation of a finite set at a common stage
(`exists_head_approx` + `wpHeadSupport_mono` upcasting). -/
theorem exists_head_approx_finset (ϖ : Uniformizer K) (S : Finset (WPA K w))
    (m : ℕ) (hS1 : ∀ x ∈ S, ‖x‖ ≤ 1) :
    ∃ (N : ℕ) (g : WPA K w → WPHead K w N),
      ∀ x ∈ S, ‖x - headIncl K w N (g x)‖ ≤ ‖ϖ.val‖ ^ m := by
  classical
  have hex : ∀ x : WPA K w, ∃ (N : ℕ) (g : WPHead K w N),
      ‖x - headIncl K w N g‖ ≤ ‖ϖ.val‖ ^ m * ‖x‖ := fun x =>
    exists_head_approx ϖ x m
  choose Nf gf hgf using hex
  refine ⟨S.sup Nf, fun x => if hx : x ∈ S then
    Subring.inclusion (wpHeadSupport_mono (K := K) (w := w) (Finset.le_sup hx))
      (gf x) else 0, fun x hx => ?_⟩
  simp only [dif_pos hx]
  rw [show headIncl K w (S.sup Nf)
      (Subring.inclusion (wpHeadSupport_mono (K := K) (w := w)
        (Finset.le_sup hx)) (gf x)) = headIncl K w (Nf x) (gf x) from rfl]
  calc ‖x - headIncl K w (Nf x) (gf x)‖ ≤ ‖ϖ.val‖ ^ m * ‖x‖ := hgf x
    _ ≤ ‖ϖ.val‖ ^ m * 1 :=
        mul_le_mul_of_nonneg_left (hS1 x hx) (pow_nonneg (norm_nonneg _) m)
    _ = ‖ϖ.val‖ ^ m := mul_one _

variable {K w} in
/-- Uniform head approximation at every sufficiently large stage (the
`wpHeadSupport_mono` upcast of `exists_head_approx_finset`; shared W21/W22
infrastructure — a finite cover needs ONE common stage). -/
theorem exists_head_approx_finset_all (ϖ : Uniformizer K)
    (S : Finset (WPA K w)) (m : ℕ) (hS1 : ∀ x ∈ S, ‖x‖ ≤ 1) :
    ∃ N₀ : ℕ, ∀ M : ℕ, N₀ ≤ M → ∃ g : WPA K w → WPHead K w M,
      ∀ x ∈ S, ‖x - headIncl K w M (g x)‖ ≤ ‖ϖ.val‖ ^ m := by
  obtain ⟨N, g, hg⟩ := exists_head_approx_finset ϖ S m hS1
  refine ⟨N, fun M hM => ⟨fun x =>
    Subring.inclusion (wpHeadSupport_mono (K := K) (w := w) hM) (g x),
    fun x hx => ?_⟩⟩
  rw [show headIncl K w M (Subring.inclusion
      (wpHeadSupport_mono (K := K) (w := w) hM) (g x)) =
    headIncl K w N (g x) from rfl]
  exact hg x hx

variable {K w} in
/-- **Finite-head presentation of every rational localization**
([WP] cor:finite-head-presentation: perturb the datum into a head via density of the
heads and lem:small-perturbation; the retracted Bezout relation makes the perturbed
datum rational in the head; conclude by prop:coefficientwise-localization). -/
theorem nonempty_headModelData_all (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (D : RationalLocData (WPA K w)) (hD : D.IsRational) :
    ∃ N₁ : ℕ, ∀ M₀ : ℕ, N₁ ≤ M₀ →
      ∃ (DH : RationalLocData (WPHead K w M₀)) (hDH : DH.IsRational),
        rationalOpen (liftDatum DH hDH).T (liftDatum DH hDH).s =
          rationalOpen D.T D.s := by
  classical
  -- the window scaling element, matching `wpaPod`'s choice
  set c : K := Classical.choose (exists_norm_window' K) with hc_def
  have hcspec := Classical.choose_spec (exists_norm_window' K)
  set t : WPA K w := constA K w c with ht_def
  have htu : IsUnit t := hcspec.1.map (constA K w)
  have ht1 : ‖t‖ < 1 := by rw [ht_def, norm_constA]; exact hcspec.2.1
  have ht0 : 0 < ‖t‖ := by rw [ht_def, norm_constA]; exact hcspec.2.2
  have hscale : ∀ f : WPA K w, ‖t * f‖ = ‖t‖ * ‖f‖ := fun f => by
    rw [ht_def, norm_constA_mul, norm_constA]
  have htkscale : ∀ (k : ℕ) (f : WPA K w), ‖t ^ k * f‖ = ‖t‖ ^ k * ‖f‖ :=
    fun k f => FiniteJet.norm_pow_mul_of_scale hscale k f
  -- scale everything into the unit ball
  set T₀ : Finset (WPA K w) := insert D.s D.T with hT₀_def
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ∀ x ∈ T₀, ‖t ^ k * x‖ ≤ 1 := by
    set M : ℝ := ∑ x ∈ T₀, ‖x‖ with hM_def
    have hM0 : 0 ≤ M := Finset.sum_nonneg fun x _ => norm_nonneg _
    have hMx : ∀ x ∈ T₀, ‖x‖ ≤ M := fun x hx =>
      Finset.single_le_sum (fun y _ => norm_nonneg y) hx
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖t‖ ^ k * M ≤ 1 := by
      rcases eq_or_lt_of_le hM0 with h0 | hMpos
      · exact ⟨0, by rw [← h0, mul_zero]; exact zero_le_one⟩
      · obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos one_pos hMpos) ht1
        exact ⟨k, ((lt_div_iff₀ hMpos).mp hk).le⟩
    refine ⟨k, fun x hx => ?_⟩
    rw [htkscale]
    calc ‖t‖ ^ k * ‖x‖ ≤ ‖t‖ ^ k * M :=
          mul_le_mul_of_nonneg_left (hMx x hx) (pow_nonneg ht0.le k)
      _ ≤ 1 := hk
  set T₁ : Finset (WPA K w) := T₀.image (t ^ k * ·) with hT₁_def
  have hspan₁ : Ideal.span (T₁ : Set (WPA K w)) = ⊤ := by
    have hsT0 : Ideal.span (T₀ : Set (WPA K w)) = ⊤ := by
      refine top_le_iff.mp ?_
      rw [← hD.span_eq_top]
      refine Ideal.span_mono ?_
      rw [hT₀_def, Finset.coe_insert]
      exact Set.subset_insert _ _
    have h1 : (1 : WPA K w) ∈ Ideal.span (T₀ : Set (WPA K w)) := by
      rw [hsT0]; trivial
    obtain ⟨cf, -, hcf⟩ := Submodule.mem_span_finset.mp h1
    have hmem : t ^ k ∈ Ideal.span (T₁ : Set (WPA K w)) := by
      have hkey : t ^ k = ∑ x ∈ T₀, cf x * (t ^ k * x) := by
        rw [Finset.sum_congr rfl fun x _ =>
          show cf x * (t ^ k * x) = t ^ k * (cf x * x) from by ring,
          ← Finset.mul_sum, show (∑ x ∈ T₀, cf x * x) = 1 from hcf, mul_one]
      rw [hkey]
      refine Ideal.sum_mem _ fun x hx =>
        Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)
      rw [hT₁_def]
      exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx)
    exact Ideal.eq_top_of_isUnit_mem _ hmem (htu.pow k)
  set D₁ : RationalLocData (WPA K w) :=
    genPieceDatum (wpaPod K w) T₁ (t ^ k * D.s) hspan₁ with hD₁_def
  have hropen₁ : rationalOpen D₁.T D₁.s = rationalOpen D.T D.s := by
    rw [show D₁.T = T₁ from rfl, show D₁.s = t ^ k * D.s from rfl, hT₁_def,
      hT₀_def, rationalOpen_unitSMul (t ^ k) (htu.pow k)]
    exact rationalOpen_insert_self D.T D.s
  have hD₁rat : D₁.IsRational :=
    RationalLocData.isRational_of_span_eq_top
      (by rw [show D₁.T = T₁ from rfl]; exact hspan₁)
  obtain ⟨ℓ, a, ha1, hbez⟩ :=
    exists_integral_bezout' t htu ht1 ht0 hscale D₁ hD₁rat
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ‖ϖ.val‖ ^ m ≤ ‖t‖ ^ (ℓ + 1) := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (pow_pos ht0 (ℓ + 1))
      ϖ.norm_val_lt_one
    exact ⟨m, hm.le⟩
  have hT₁1 : ∀ x ∈ T₁, ‖x‖ ≤ 1 := by
    intro x hx
    rw [hT₁_def] at hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact hk y hy
  obtain ⟨Nthr, hall⟩ := exists_head_approx_finset_all ϖ T₁ m hT₁1
  refine ⟨Nthr, fun M₀ hM₀ => ?_⟩
  set N : ℕ := M₀ with hN_def
  obtain ⟨g, hg⟩ := hall N (by rw [hN_def]; exact hM₀)
  -- the perturbation setup: perturb the scaled datum into the `N`-th head
  set S : PerturbSetup (WPA K w) :=
    { t := t, htu := htu, ht1 := ht1, ht0 := ht0, hscale := hscale
      D := D₁
      hsT := by
        rw [show D₁.T = T₁ from rfl, show D₁.s = t ^ k * D.s from rfl, hT₁_def,
          hT₀_def]
        exact Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _)
      hT1 := by rw [show D₁.T = T₁ from rfl]; exact hT₁1
      ℓ := ℓ, a := a, ha1 := ha1
      hbez := hbez
      pert := fun x => if x ∈ T₁ then headIncl K w N (g x) else x
      hpert1 := by
        intro x hx
        rw [show D₁.T = T₁ from rfl] at hx
        rw [if_pos hx]
        calc ‖headIncl K w N (g x)‖
            = ‖x + (headIncl K w N (g x) - x)‖ := by
              rw [show x + (headIncl K w N (g x) - x) = headIncl K w N (g x)
                from by ring]
          _ ≤ max ‖x‖ ‖headIncl K w N (g x) - x‖ :=
              IsUltrametricDist.norm_add_le_max _ _
          _ ≤ 1 := by
              refine max_le (hT₁1 x hx) ?_
              rw [norm_sub_rev]
              exact le_trans (hg x hx) (le_trans hm
                (pow_le_one₀ ht0.le ht1.le))
      hpert := by
        intro x hx
        rw [show D₁.T = T₁ from rfl] at hx
        rw [if_pos hx, norm_sub_rev]
        exact le_trans (hg x hx) hm
      hplus := fun y hy => FiniteJet.isPowerBounded_of_norm_le_one hy }
    with hS_def
  obtain ⟨h, hh1, hpbez⟩ := PerturbSetup.exists_perturbed_bezout S
  -- the head datum: retract the primed Bezout along `rhoHead`
  set TH : Finset (WPHead K w N) := T₁.image g with hTH_def
  have hretract : ∑ x ∈ T₁, rhoHead K w N (a x) * g x =
      constHead K w N c ^ ℓ *
        (1 + constHead K w N c * rhoHead K w N h) := by
    have h1 := congrArg (rhoHead K w N) hpbez
    rw [map_sum] at h1
    rw [Finset.sum_congr rfl fun x hx => show
        rhoHead K w N (a x * S.pert x) = rhoHead K w N (a x) * g x from by
      rw [map_mul, show S.pert x =
          if x ∈ T₁ then headIncl K w N (g x) else x from rfl,
        if_pos (show x ∈ T₁ from hx), rhoHead_headIncl]] at h1
    rw [map_mul, map_pow, map_add, map_one, map_mul] at h1
    rw [show rhoHead K w N t = constHead K w N c from by
      rw [ht_def, ← headIncl_constHead, rhoHead_headIncl]] at h1
    exact h1
  have hspanH : Ideal.span (TH : Set (WPHead K w N)) = ⊤ := by
    have hmem : constHead K w N c ^ ℓ *
        (1 + constHead K w N c * rhoHead K w N h) ∈
        Ideal.span (TH : Set (WPHead K w N)) := by
      rw [← hretract]
      refine Ideal.sum_mem _ fun x hx =>
        Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)
      rw [hTH_def]
      exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx)
    refine Ideal.eq_top_of_isUnit_mem _ hmem
      (IsUnit.mul ((hcspec.1.map (constHead K w N)).pow ℓ) ?_)
    have hnorm : ‖-(constHead K w N c * rhoHead K w N h)‖ < 1 := by
      rw [norm_neg]
      calc ‖constHead K w N c * rhoHead K w N h‖
          = ‖c‖ * ‖rhoHead K w N h‖ := by rw [norm_constHead_mul]
        _ ≤ ‖c‖ * 1 := mul_le_mul_of_nonneg_left
            (le_trans (norm_rhoHead_le (K := K) (w := w) (N := N) h) hh1)
            (norm_nonneg _)
        _ = ‖c‖ := mul_one _
        _ < 1 := hcspec.2.1
    have hu : IsUnit (1 - -(constHead K w N c * rhoHead K w N h)) :=
      (Units.oneSub _ hnorm).isUnit
    rwa [sub_neg_eq_add] at hu
  set DH : RationalLocData (WPHead K w N) := genPieceDatum
    (FiniteJet.unitBallPod (constHead K w N c)
      (hcspec.1.map (constHead K w N))
      (by rw [norm_constHead]; exact hcspec.2.1)
      (by rw [norm_constHead]; exact hcspec.2.2)
      (fun f => by rw [norm_constHead_mul, norm_constHead]))
    TH (g (t ^ k * D.s)) hspanH with hDH_def
  have hDHrat : DH.IsRational :=
    RationalLocData.isRational_of_span_eq_top
      (by rw [show DH.T = TH from rfl]; exact hspanH)
  -- the lifted datum agrees with the perturbed datum
  have hmatch : liftDatum DH hDHrat = S.datum := by
    refine RationalLocData.ext_of_fields rfl ?_ ?_
    · rw [show (liftDatum DH hDHrat).T = DH.T.image (headIncl K w N) from rfl,
        PerturbSetup.datum_T, show DH.T = TH from rfl, hTH_def,
        Finset.image_image, show S.D.T = T₁ from rfl]
      refine (Finset.image_congr fun x hx => ?_).symm
      rw [show S.pert x = if x ∈ T₁ then headIncl K w N (g x) else x from rfl,
        if_pos (show x ∈ T₁ from hx)]
      rfl
    · rw [show (liftDatum DH hDHrat).s = headIncl K w N DH.s from rfl,
        PerturbSetup.datum_s, show DH.s = g (t ^ k * D.s) from rfl,
        show S.D.s = t ^ k * D.s from rfl,
        show S.pert (t ^ k * D.s) =
          if t ^ k * D.s ∈ T₁ then headIncl K w N (g (t ^ k * D.s))
          else t ^ k * D.s from rfl]
      rw [if_pos]
      rw [hT₁_def, hT₀_def]
      exact Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _)
  have hopen : rationalOpen (liftDatum DH hDHrat).T (liftDatum DH hDHrat).s =
      rationalOpen D.T D.s := by
    rw [hmatch, PerturbSetup.rationalOpen_datum S]
    exact hropen₁
  exact ⟨DH, hDHrat, hopen⟩

variable {K w} in
/-- **Finite-head presentation of every rational localization**
([WP] cor:finite-head-presentation) — the stage-free record form (the model
equivalence assembled from `hopen` by `restrictionEquiv` + `coeffLocEquiv`). -/
theorem nonempty_headModelData (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (D : RationalLocData (WPA K w)) (hD : D.IsRational) :
    Nonempty (HeadModelData D) := by
  obtain ⟨N₁, hall⟩ := nonempty_headModelData_all ϖ hK₀ D hD
  obtain ⟨DH, hDHrat, hopen⟩ := hall N₁ (le_refl _)
  exact ⟨⟨N₁, DH, hDHrat, hopen,
    (restrictionEquiv D (liftDatum DH hDHrat) hopen).trans
      (coeffLocEquiv ϖ hK₀ DH hDHrat),
    by
      rw [RingEquiv.coe_trans]
      exact (coeffLocEquiv_continuous ϖ hK₀ DH hDHrat).comp
        (restrictionEquiv_continuous D (liftDatum DH hDHrat) hopen),
    by
      rw [RingEquiv.symm_trans]
      rw [RingEquiv.coe_trans]
      exact (restrictionEquiv_symm_continuous D (liftDatum DH hDHrat)
        hopen).comp (coeffLocEquiv_symm_continuous ϖ hK₀ DH hDHrat)⟩⟩

end WeightedParity
