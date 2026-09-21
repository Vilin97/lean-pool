/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.Algebra

/-!
# `𝒜` is not noetherian ([WP] prop:parity-nonnoetherian)

For each `m` the paper builds a bounded homomorphism `ψ_m : 𝒜 → k⟨T⟩` killing
`W, Y_j, Z_j (j ≠ m+1)` and sending `Z_{m+1} ↦ T`, and concludes that the ideals
`I_m = (Z_1,…,Z_m)` form a strictly increasing chain.

Source ([WP] lines 817–834): "There is a compatible family of norm-nonincreasing maps
on the finite stages, and hence a bounded homomorphism `ψ_m : 𝒜 → k⟨T⟩`, which sends
`W` and every `Y_j` to zero, sends `Z_{m+1}` to `T`, and sends every other `Z_j` to
zero. … The map `ψ_m` kills `I_m` but not `Z_{m+1}`.  Therefore `I_1 ⊊ I_2 ⊊ ⋯`, so
`𝒜` is not noetherian."

Route note (support model, documented divergence): `ψ_m` is defined directly on the
support algebra — the monomial `W^a U^ν` maps to `T^q` when `(a,ν) = (0, 2q·δ_{m+1})`
and to `0` otherwise; multiplicativity holds because a pair of allowed exponents
summing to `2q·δ_{m+1}` must consist of two EVEN pure-`U_{m+1}` exponents (an odd
`U_{m+1}`-exponent forces `W`-content `≥ w (m+1) ≥ 1` inside `S`, whence the weight
hypothesis `hw`).  The presentation-preservation step of the paper disappears.
-/

@[expose] public section

namespace WeightedParity

open Filter Topology

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (w : ℕ → ℕ)

/-- Allowed exponents that are single-index at `m+1` are even; equivalently, an odd
pure `U_{m+1}`-monomial is not in `S` (its parity weight is `w (m+1) ≥ 1 > 0`). -/
theorem not_wpMem_single_odd (hw : ∀ n, 1 ≤ n → 1 ≤ w n) (m : ℕ) {i : ℕ}
    (hi : i % 2 = 1) : ¬ WPMem w (Finsupp.single (m + 1) i) := by
  intro h
  unfold WPMem at h
  rw [wpWeight_single] at h
  have hne : (m + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero m
  rw [if_pos ⟨hi, hne⟩] at h
  have h0 : (Finsupp.single (m + 1) i) 0 = 0 := by
    rw [Finsupp.single_apply, if_neg (by omega : ¬ (m + 1 : ℕ) = 0)]
  rw [h0] at h
  exact absurd (le_antisymm h (Nat.zero_le _)) (by
    have := hw (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
    omega)

/-- The coefficient family of `ψ_m f`: the pure even `U_{m+1}`-coefficients of `f`. -/
noncomputable def psiCoeff (m : ℕ) (f : WPA K w) : ℕ → K := fun q =>
  coeffA K w (Finsupp.single (m + 1) (2 * q)) f

/-- The coefficientwise character `ψ_m : 𝒜 → k⟨T⟩` ([WP] prop:parity-nonnoetherian):
pure even powers `U_{m+1}^{2q} ↦ T^q`, all other allowed monomials `↦ 0`.  Requires
positive weights (`hw`) so that odd `U_{m+1}`-exponents force `W`-content. -/
noncomputable def psiHom (m : ℕ) (hw : ∀ n, 1 ≤ n → 1 ≤ w n) :
    WPA K w →+* PowerSeries.Restricted K (1 : ℝ) where
  toFun f :=
    ⟨PowerSeries.mk (psiCoeff K w m f), by
      show PowerSeries.IsRestricted (1 : ℝ) (PowerSeries.mk (psiCoeff K w m f))
      rw [Restricted.isRestricted_iff_cofinite]
      have hinj : Function.Injective
          (fun q : ℕ => Finsupp.single (m + 1) (2 * q)) := by
        intro a b hab
        have := congrArg (fun t : ℕ →₀ ℕ => t (m + 1)) hab
        simpa [Finsupp.single_apply] using this
      have hnull : Tendsto
          (fun t : ℕ →₀ ℕ => ‖coeffA K w t f‖) cofinite (𝓝 0) := by
        have h2 : Tendsto (fun t : ℕ →₀ ℕ =>
            ‖MvPowerSeries.coeff t f.1.1‖ *
              t.prod ((fun _ : ℕ => (1 : ℝ)) · ^ ·)) cofinite (𝓝 0) := f.1.2
        refine h2.congr fun t => ?_
        rw [prod_one_weights, mul_one]
        rfl
      have := hnull.comp (hinj.tendsto_cofinite)
      refine this.congr fun q => ?_
      simp only [Function.comp_apply, PowerSeries.coeff_mk, one_pow, mul_one]
      rfl⟩
  map_zero' := Subtype.ext (by
    ext q
    show PowerSeries.coeff q (PowerSeries.mk (psiCoeff K w m 0)) =
      PowerSeries.coeff q (0 : PowerSeries K)
    rw [PowerSeries.coeff_mk, psiCoeff]
    show MvPowerSeries.coeff _ (0 : MvPowerSeries ℕ K) = _
    simp)
  map_one' := Subtype.ext (by
    classical
    ext q
    show PowerSeries.coeff q (PowerSeries.mk (psiCoeff K w m 1)) =
      PowerSeries.coeff q 1
    rw [PowerSeries.coeff_mk, psiCoeff]
    show MvPowerSeries.coeff (Finsupp.single (m + 1) (2 * q))
      (1 : MvPowerSeries ℕ K) = _
    rcases eq_or_ne q 0 with rfl | hq
    · simp
    · have hne2 : ¬ Finsupp.single (m + 1) (2 * q) = 0 := by
        intro h
        have h5 := congrArg (fun t : ℕ →₀ ℕ => t (m + 1)) h
        simp [Finsupp.single_apply] at h5
        omega
      rw [MvPowerSeries.coeff_one, if_neg hne2, PowerSeries.coeff_one, if_neg hq])
  map_add' f g := Subtype.ext (by
    ext q
    show PowerSeries.coeff q (PowerSeries.mk (psiCoeff K w m (f + g))) = _
    rw [PowerSeries.coeff_mk, psiCoeff]
    show MvPowerSeries.coeff (Finsupp.single (m + 1) (2 * q)) (f.1.1 + g.1.1) =
      PowerSeries.coeff q ((PowerSeries.mk (psiCoeff K w m f)) +
        (PowerSeries.mk (psiCoeff K w m g)))
    rw [map_add, map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    rfl)
  map_mul' f g := Subtype.ext (by
    classical
    ext q
    show PowerSeries.coeff q (PowerSeries.mk (psiCoeff K w m (f * g))) =
      PowerSeries.coeff q
        ((PowerSeries.mk (psiCoeff K w m f)) * (PowerSeries.mk (psiCoeff K w m g)))
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, psiCoeff]
    show MvPowerSeries.coeff (Finsupp.single (m + 1) (2 * q)) (f.1.1 * g.1.1) = _
    rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single]
    rw [Finset.sum_map]
    -- the ℕ-antidiagonal of `2q`; odd first components die by support
    have hvanish : ∀ p : ℕ × ℕ, p ∈ Finset.HasAntidiagonal.antidiagonal (2 * q) → p.1 % 2 = 1 →
        MvPowerSeries.coeff (Finsupp.single (m + 1) p.1) f.1.1 *
          MvPowerSeries.coeff (Finsupp.single (m + 1) p.2) g.1.1 = 0 := by
      intro p _ hodd
      rw [show MvPowerSeries.coeff (Finsupp.single (m + 1) p.1) f.1.1 =
          coeffA K w (Finsupp.single (m + 1) p.1) f from rfl,
        coeffA_of_not_wpMem K w (not_wpMem_single_odd w hw m hodd) f, zero_mul]
    -- reindex the surviving even pairs by halving
    rw [← Finset.sum_filter_of_ne (p := fun p : ℕ × ℕ => p.1 % 2 = 0)
      (by
        intro p hp hne
        rcases Nat.mod_two_eq_zero_or_one p.1 with h | h
        · exact h
        · exact absurd (hvanish p hp h) hne)]
    refine (Finset.sum_nbij' (i := fun p : ℕ × ℕ => (2 * p.1, 2 * p.2))
      (j := fun p : ℕ × ℕ => (p.1 / 2, p.2 / 2)) ?_ ?_ ?_ ?_ ?_).symm
    · intro p hp
      rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal]
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      omega
    · intro p hp
      rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
      omega
    · intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      simp
    · intro p hp
      rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp
      have h1 : p.1 % 2 = 0 := hp.2
      have h2 : p.2 % 2 = 0 := by omega
      ext
      · show 2 * (p.1 / 2) = p.1
        omega
      · show 2 * (p.2 / 2) = p.2
        omega
    · intro p _
      simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk,
        Prod.map_apply, PowerSeries.coeff_mk]
      rfl)

theorem psiHom_apply_coeff (m : ℕ) (hw : ∀ n, 1 ≤ n → 1 ≤ w n) (f : WPA K w) (q : ℕ) :
    PowerSeries.coeff q (psiHom K w m hw f).1 =
      coeffA K w (Finsupp.single (m + 1) (2 * q)) f := by
  show PowerSeries.coeff q (PowerSeries.mk (psiCoeff K w m f)) = _
  rw [PowerSeries.coeff_mk]
  rfl

theorem two_nsmul_single_eq (a : ℕ) : (2 : ℕ) • Finsupp.single a 1 =
    Finsupp.single a 2 := by
  rw [two_nsmul, ← Finsupp.single_add]

theorem psiHom_Za_succ_ne_zero (m : ℕ) (hw : ∀ n, 1 ≤ n → 1 ≤ w n) :
    psiHom K w m hw (Za K w (m + 1)) ≠ 0 := by
  classical
  intro h
  have h1 := congrArg (fun x : PowerSeries.Restricted K (1 : ℝ) =>
    PowerSeries.coeff 1 x.1) h
  rw [psiHom_apply_coeff] at h1
  have h2 : coeffA K w (Finsupp.single (m + 1) (2 * 1)) (Za K w (m + 1)) = 1 := by
    unfold Za
    rw [coeffA_wpMonomial, if_pos (by rw [two_nsmul_single_eq])]
  rw [h2] at h1
  have h3 : PowerSeries.coeff 1 ((0 : PowerSeries.Restricted K (1 : ℝ))).1 =
      (0 : K) := by
    show PowerSeries.coeff 1 (0 : PowerSeries K) = 0
    simp
  rw [h3] at h1
  exact one_ne_zero h1

theorem psiHom_Za_of_le (m : ℕ) (hw : ∀ n, 1 ≤ n → 1 ≤ w n) {j : ℕ}
    (hj : j ≤ m) : psiHom K w m hw (Za K w j) = 0 := by
  classical
  refine Subtype.ext ?_
  ext q
  show PowerSeries.coeff q (psiHom K w m hw (Za K w j)).1 =
    PowerSeries.coeff q (0 : PowerSeries K)
  rw [psiHom_apply_coeff]
  unfold Za
  rw [coeffA_wpMonomial, if_neg, map_zero]
  intro h
  rw [two_nsmul_single_eq] at h
  have h6 := congrArg (fun t : ℕ →₀ ℕ => t j) h
  simp only [Finsupp.single_apply] at h6
  rw [if_neg (by omega : ¬ m + 1 = j)] at h6
  simp at h6

/-- `Z_{m+1}` is not in the ideal generated by `Z_1, …, Z_m`
([WP]: "The map `ψ_m` kills `I_m` but not `Z_{m+1}`"). -/
theorem Za_succ_notMem_span (m : ℕ) (hw : ∀ n, 1 ≤ n → 1 ≤ w n) :
    Za K w (m + 1) ∉ Ideal.span ((fun j => Za K w j) '' {j | 1 ≤ j ∧ j ≤ m}) := by
  intro hmem
  have hmap := Ideal.mem_map_of_mem (psiHom K w m hw) hmem
  rw [Ideal.map_span] at hmap
  have himg : (psiHom K w m hw) '' ((fun j => Za K w j) '' {j | 1 ≤ j ∧ j ≤ m}) ⊆
      {0} := by
    rintro x ⟨y, ⟨j, hj, rfl⟩, rfl⟩
    exact psiHom_Za_of_le K w m hw hj.2
  have hspan : Ideal.span ((psiHom K w m hw) ''
      ((fun j => Za K w j) '' {j | 1 ≤ j ∧ j ≤ m})) ≤ ⊥ := by
    rw [← Ideal.span_singleton_eq_bot.mpr rfl]
    exact Ideal.span_mono (by simpa using himg)
  have := hspan hmap
  rw [Ideal.mem_bot] at this
  exact psiHom_Za_succ_ne_zero K w m hw this

/-- The stage ideals are monotone. -/
theorem stage_ideal_mono {M M' : ℕ} (h : M ≤ M') :
    Ideal.span ((fun j => Za K w j) '' {j | 1 ≤ j ∧ j ≤ M}) ≤
      Ideal.span ((fun j => Za K w j) '' {j | 1 ≤ j ∧ j ≤ M'}) :=
  Ideal.span_mono (Set.image_mono fun j hj => ⟨hj.1, hj.2.trans h⟩)

/-- **`𝒜` is not noetherian** ([WP] prop:parity-nonnoetherian / thm 6.2(1)). -/
theorem not_isNoetherianRing_WPA (hw : ∀ n, 1 ≤ n → 1 ≤ w n) :
    ¬ IsNoetherianRing (WPA K w) := by
  intro hN
  classical
  set S : Set (WPA K w) := (fun j => Za K w j) '' {j | 1 ≤ j} with hS
  -- every element of the big span lies in a finite stage
  have hstage : ∀ t ∈ Ideal.span S, ∃ M : ℕ,
      t ∈ Ideal.span ((fun j => Za K w j) '' {j | 1 ≤ j ∧ j ≤ M}) := by
    intro t ht
    obtain ⟨F₀, hsub, hmem⟩ := Submodule.mem_span_finite_of_mem_span ht
    have hchoice : ∀ x : ↥F₀, ∃ j, 1 ≤ j ∧ x.1 = Za K w j := fun x => by
      obtain ⟨j, hj, hxe⟩ := hsub (Finset.mem_coe.mpr x.2)
      exact ⟨j, hj, hxe.symm⟩
    choose jdx hj1 hje using hchoice
    obtain ⟨M, hM⟩ := (Set.finite_range jdx).bddAbove
    refine ⟨M, Ideal.span_le.mpr ?_ hmem⟩
    intro x hx
    have hxF : x ∈ F₀ := Finset.mem_coe.mp hx
    refine Ideal.subset_span ?_
    exact ⟨jdx ⟨x, hxF⟩, ⟨hj1 ⟨x, hxF⟩, hM ⟨⟨x, hxF⟩, rfl⟩⟩, (hje ⟨x, hxF⟩).symm⟩
  -- the big span is finitely generated
  have hfg : (Ideal.span S).FG := (isNoetherian_def.mp hN) (Ideal.span S)
  obtain ⟨T, hT⟩ := hfg
  -- bound the stages of the generators
  have hTmem : ∀ t ∈ T, t ∈ Ideal.span S := fun t ht => by
    rw [← hT]
    exact Ideal.subset_span ht
  choose Mt hMt using fun (t : ↥(T : Finset (WPA K w))) => hstage t.1 (hTmem t.1 t.2)
  obtain ⟨Mtot, hMtot⟩ := (Set.finite_range Mt).bddAbove
  -- the whole span sits inside stage `Mtot`
  have hspan_le : Ideal.span S ≤
      Ideal.span ((fun j => Za K w j) '' {j | 1 ≤ j ∧ j ≤ Mtot}) := by
    rw [← hT, Ideal.span_le]
    intro t ht
    exact stage_ideal_mono K w (hMtot ⟨⟨t, ht⟩, rfl⟩) (hMt ⟨t, ht⟩)
  have hZM : Za K w (Mtot + 1) ∈ Ideal.span S :=
    Ideal.subset_span ⟨Mtot + 1, Nat.succ_le_succ (Nat.zero_le Mtot), rfl⟩
  exact Za_succ_notMem_span K w Mtot hw (hspan_le hZM)

end WeightedParity
