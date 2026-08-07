/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Abel.LinkData
import LeanPool.JacobianDiffgeo.Abel.Sufficiency
import LeanPool.JacobianDiffgeo.Path

/-!
# abel-theorem: the weak-solution-upgrade discharge (design §4.1 steps 5-7, assembled)

Unit: abel-theorem. Namespace `RS.Abel`.

**The discharge of `WeakSolutionUpgrade`/`WeakSolutionUpgradeFinset` modulo the single
`serre-duality-tails` gate.** The core (`exists_mero_of_sum_pathIntegral_eq_zero`): given
finitely many paths `δ i : Path (A i) (B i)` whose TOTAL integral against every holomorphic
`1`-form vanishes, there is a global meromorphic `F` with `ord_z F = ∑ i ([z = B i] - [z = A i])`.

Proof shape (Forster 20.5/20.7(a), dissection-free):
* chop each path by `RS.exists_chartChain`; build one `exists_link` piece per chain link
  (`LinkData.lean`), giving piece functions `f_l` and packaged `(0,1)`-forms `η_l`;
* `pairing PU (∑ η_l) θ = π ∑ᵢ ∫_{δ i} θ = 0` — per link the residue identity evaluates the
  pairing at chart primitives, and `pathIntegral_eq_sum_chartChain` telescopes them back into
  the path integrals (the SAME primitives, from `DifferentiableOn.isExactOn_ball`);
* the Serre-functional bridge `exists_dbar_of_forall_pairing_eq_zero` (gated on
  `Function.Surjective (tailToH1 0)`) yields `u` with `dbaru = ∑ η_l`;
* `F₀ := exp (-u) · ∏ f_l` is `dbar`-closed off the divisor points
  (`wirtingerDbar_exp_neg_mul_eq_zero` + the per-link `dbar log`-matching + the `dbar` product
  rule), hence holomorphic there (`contMDiffOn_omega_of_isDbarOn_zero`), and the per-link
  factor limits multiply into the promotion lemma `meromorphicAt_of_tendsto_factor` at EVERY
  point — meromorphy plus the exact order `∑ linkOrd` in one stroke, no rechart bookkeeping.

Consumers: `weakSolutionUpgrade_of_surjective` and `weakSolutionUpgradeFinset_of_surjective` —
design §4.1 steps 5-7 discharged, gated ONLY on `serre-duality-tails`'s single remaining
external fact (the same gate as `DolbeaultBridge.lean`; the weak-solution hypotheses of the
`WeakSolutionUpgrade` shapes are simply not needed: the construction builds its own pieces).
-/

open scoped ContDiff Manifold
open IsManifold Metric Set MeasureTheory Filter Topology


noncomputable section

namespace RS.Abel

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Small algebra helpers -/

omit [T2Space X] [CompactSpace X] in
theorem pairing_zero_left (PU : SurfPoU X) (θ : RS.Form1 X) :
    pairing PU (0 : RS.Form01 X) θ = 0 := by
  rw [show (0 : RS.Form01 X) = (0 : ℂ) • (0 : RS.Form01 X) from (zero_smul ℂ _).symm,
    pairing_smul_left, zero_mul]

omit [T2Space X] in
theorem pairing_finsetSum_left (PU : SurfPoU X) {ι : Type*} (s : Finset ι)
    (F : ι → RS.Form01 X) (θ : RS.Form1 X) :
    pairing PU (∑ i ∈ s, F i) θ = ∑ i ∈ s, pairing PU (F i) θ := by
  induction s using Finset.cons_induction with
  | empty => simpa using pairing_zero_left PU θ
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, pairing_add_left, ih]

theorem zpow_finset_sum {ι : Type*} {a : ℂ} (ha : a ≠ 0) (s : Finset ι) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons b s hb ih => rw [Finset.sum_cons, Finset.prod_cons, zpow_add₀ ha, ih]

omit [T2Space X] [CompactSpace X] in
/-- Real-smooth multiplication on the surface, through the preferred chart (no
`ContMDiffMul 𝓘(ℝ, ℂ) ∞ ℂ` instance exists — the `AbelWeak` compat route). -/
theorem contMDiffAt_mul_real' {f g : X → ℂ} {x : X}
    (hf : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f x) (hg : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ g x) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun y => f y * g y) x := by
  rw [RS.contMDiffAt_real_iff_contDiffAt] at hf hg ⊢
  exact hf.mul hg

/-! ## The core discharge -/

omit [CompactSpace X] in
/-- The exp-corrected product has vanishing `dbar` off the divisor set. Split out of
`exists_mero_of_sum_pathIntegral_eq_zero` for the 200-line proof size we hold ourselves to; the
`ηT`/`fT`/`F₀` abbreviations are rebuilt here so the body reads as it did inline. -/
private theorem isDbarOn_exp_neg_mul_prod {Λ : Type*} [Fintype Λ]
    {f : Λ → X → ℂ} {η : Λ → RS.Form01 X} {lA lB : Λ → X} {S : Set X}
    (hsmooth : ∀ l, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (f l) {lA l}ᶜ)
    (hne : ∀ l, ∀ x, x ≠ lA l → x ≠ lB l → f l x ≠ 0)
    (hdlog : ∀ l, ∀ x, x ≠ lA l → x ≠ lB l →
      RS.wirtingerDbar (f l ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) =
        (η l).coeffAt x (chartAt ℂ x x) * f l x)
    (u : RS.SmoothC X) (hu : RS.dbar u = ∑ l : Λ, η l)
    (hmemSc : ∀ x ∈ Sᶜ, ∀ l : Λ, x ≠ lA l ∧ x ≠ lB l) :
    RS.IsDbarOn (fun x => Complex.exp (-(u x)) * ∏ l : Λ, f l x) 0 Sᶜ := by
  classical
  set ηT : RS.Form01 X := ∑ l : Λ, η l with hηT_def
  set fT : X → ℂ := fun x => ∏ l : Λ, f l x with hfT_def
  set F₀ : X → ℂ := fun x => Complex.exp (-(u x)) * fT x with hF₀_def
  change RS.IsDbarOn F₀ 0 Sᶜ
  intro x hx
  -- chart representatives
  have hdiffs : ∀ l : Λ, DifferentiableAt ℝ (f l ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) := by
    intro l
    have h1 : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (f l) x :=
      (hsmooth l).contMDiffAt (isOpen_compl_singleton.mem_nhds (hmemSc x hx l).1)
    exact (RS.contMDiffAt_real_iff_contDiffAt.mp h1).differentiableAt (by norm_num)
  have hfTd : DifferentiableAt ℝ (fT ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) := by
    have := differentiableAt_finset_prod (f := fun l => f l ∘ ⇑(chartAt ℂ x).symm)
      Finset.univ (fun l _ => hdiffs l)
    exact this
  have hud : DifferentiableAt ℝ (⇑u ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
    u.differentiableAt_comp_chartAt_symm x (mem_chart_target ℂ x)
  -- the dbar log identity for the product
  have hfT_ne : fT x ≠ 0 := by
    rw [hfT_def]
    refine Finset.prod_ne_zero_iff.mpr (fun l _ => ?_)
    exact hne l x (hmemSc x hx l).1 (hmemSc x hx l).2
  have hprod_dlog : RS.wirtingerDbar (fT ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)
      = ηT.coeffAt x (chartAt ℂ x x) * fT x := by
    have hrule := wirtingerDbar_finset_prod (f := fun l => f l ∘ ⇑(chartAt ℂ x).symm)
      Finset.univ (fun l _ => hdiffs l)
    have hshape : (fT ∘ ⇑(chartAt ℂ x).symm)
        = fun w => ∏ l : Λ, (f l ∘ ⇑(chartAt ℂ x).symm) w := by
      funext w
      simp [hfT_def, Function.comp]
    rw [hshape, hrule]
    have hcoeff : ηT.coeffAt x (chartAt ℂ x x) = ∑ l : Λ, (η l).coeffAt x (chartAt ℂ x x) := by
      rw [hηT_def]
      exact Form01.coeffAt_finsetSum Finset.univ η x (chartAt ℂ x x)
    rw [hcoeff, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hval : ∀ j : Λ, (f j ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) = f j x := by
      intro j
      simp [Function.comp, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
    calc RS.wirtingerDbar (f l ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) *
          ∏ j ∈ Finset.univ.erase l, (f j ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)
        = ((η l).coeffAt x (chartAt ℂ x x) * f l x) *
          ∏ j ∈ Finset.univ.erase l, f j x := by
          rw [hdlog l x (hmemSc x hx l).1 (hmemSc x hx l).2,
            Finset.prod_congr rfl (fun j _ => hval j)]
      _ = (η l).coeffAt x (chartAt ℂ x x) *
          (f l x * ∏ j ∈ Finset.univ.erase l, f j x) := by ring
      _ = (η l).coeffAt x (chartAt ℂ x x) * fT x := by
          rw [Finset.mul_prod_erase Finset.univ (fun j => f j x) (Finset.mem_univ l)]
  -- the dbar equation for `u`
  have hux : RS.wirtingerDbar (⇑u ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)
      = ηT.coeffAt x (chartAt ℂ x x) := by
    have h1 : RS.IsDbarOn (⇑u) ηT Set.univ := RS.dbar_eq_iff.mp hu
    exact h1 x (Set.mem_univ x)
  -- combine
  change RS.wirtingerDbar (F₀ ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)
    = (0 : RS.Form01 X).coeffAt x (chartAt ℂ x x)
  rw [RS.Form01.coeffAt_zero]
  have hkey : RS.wirtingerDbar (⇑u ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)
      = RS.wirtingerDbar (fT ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)
        / (fT ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) := by
    have hval : (fT ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) = fT x := by
      simp [Function.comp, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
    rw [hux, hprod_dlog, hval, mul_div_cancel_right₀ _ hfT_ne]
  have hval : (fT ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) = fT x := by
    simp [Function.comp, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  have hfT_ne' : (fT ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) ≠ 0 := by
    rw [hval]
    exact hfT_ne
  exact RS.Abel.wirtingerDbar_exp_neg_mul_eq_zero hud hfTd hkey hfT_ne'

/-- **The Abel sufficiency engine** (Forster 20.5 + 20.7(a), assembled; gated only on
`serre-duality-tails`'s remaining external fact): finitely many paths with vanishing total
period produce a global meromorphic function whose divisor is exactly the endpoint divisor. -/
theorem exists_mero_of_sum_pathIntegral_eq_zero {ι : Type*} [Fintype ι] [ConnectedSpace X]
    [DecidableEq X]
    (hsurj : Function.Surjective (RS.LaurentTail.tailToH1 (0 : RS.Divisor X)))
    {A B : ι → X} (δ : (i : ι) → Path (A i) (B i))
    (hper : ∀ θ : RS.Form1 X, ∑ i, RS.pathIntegral (δ i) θ = 0) :
    ∃ F : RS.Mero X, F ≠ 0 ∧ ∀ z : X,
      F.ord z = ((∑ i, linkOrd (A i) (B i) z : ℤ) : WithTop ℤ) := by
  classical
  obtain ⟨PU⟩ := SurfPoU.nonempty (X := X)
  -- the chart chains
  have hC : ∀ i, Nonempty (RS.ChartChain (δ i)) := fun i => RS.exists_chartChain (δ i)
  set C : (i : ι) → RS.ChartChain (δ i) := fun i => (hC i).some with hC_def
  -- the link index and endpoint data
  set Λ : Type _ := (i : ι) × Fin (C i).n with hΛ_def
  set lA : Λ → X := fun l => (δ l.1).extend ((C l.1).t l.2) with hlA_def
  set lB : Λ → X := fun l => (δ l.1).extend ((C l.1).t (l.2 + 1)) with hlB_def
  -- link data from the chain
  have hmemA : ∀ l : Λ, lA l ∈ ((C l.1).e l.2).source ∧
      (C l.1).e l.2 (lA l) ∈ ball ((C l.1).c l.2) ((C l.1).r l.2) := fun l =>
    (C l.1).maps l.2 ((C l.1).t l.2) ⟨le_rfl, (C l.1).mono (Nat.le_succ l.2)⟩
  have hmemB : ∀ l : Λ, lB l ∈ ((C l.1).e l.2).source ∧
      (C l.1).e l.2 (lB l) ∈ ball ((C l.1).c l.2) ((C l.1).r l.2) := fun l =>
    (C l.1).maps l.2 ((C l.1).t (l.2 + 1)) ⟨(C l.1).mono (Nat.le_succ l.2), le_rfl⟩
  -- the per-link pieces
  choose f η hsmooth hne hdlog hfactor hpairing using fun l : Λ =>
    exists_link (A := lA l) (B := lB l) ((C l.1).he l.2) (hmemA l).1 (hmemB l).1
      ((C l.1).ball_subset l.2) (hmemA l).2 (hmemB l).2
  -- the total form and total piece
  set ηT : RS.Form01 X := ∑ l : Λ, η l with hηT_def
  set fT : X → ℂ := fun x => ∏ l : Λ, f l x with hfT_def
  -- STEP 1: the total pairing vanishes
  have hpair_total : ∀ θ : RS.Form1 X, pairing PU ηT θ = 0 := by
    intro θ
    rw [hηT_def, pairing_finsetSum_left]
    -- primitives per chain chart
    have hex : ∀ (i : ι) (k : ℕ), ∃ G : ℂ → ℂ,
        ∀ z ∈ ball ((C i).c k) ((C i).r k), HasDerivAt G (RS.coeffIn ((C i).e k) θ z) z := by
      intro i k
      have hdiff : DifferentiableOn ℂ (RS.coeffIn ((C i).e k) θ)
          (ball ((C i).c k) ((C i).r k)) := fun z hz =>
        ((θ.analyticAt_coeffIn ((C i).he k) ((C i).ball_subset k hz)).differentiableAt
          ).differentiableWithinAt
      exact hdiff.isExactOn_ball
    choose G hG using hex
    -- per-link evaluation and telescoping
    have hsum : ∑ l : Λ, pairing PU (η l) θ
        = ∑ i : ι, (Real.pi : ℂ) * RS.pathIntegral (δ i) θ := by
      rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hpath := RS.AbelWeak.pathIntegral_eq_sum_chartChain (C i) θ (G i)
        (fun k _ z hz => hG i k z hz)
      rw [hpath, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range
        (fun k => (Real.pi : ℂ) * (G i k ((C i).e k ((δ i).extend ((C i).t (k + 1))))
          - G i k ((C i).e k ((δ i).extend ((C i).t k))))) (C i).n]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact hpairing ⟨i, k⟩ PU θ (G i k) (hG i k)
    rw [hsum, ← Finset.mul_sum, hper θ, mul_zero]
  -- STEP 2: solve dbaru = ηT
  obtain ⟨u, hu⟩ := exists_dbar_of_forall_pairing_eq_zero PU hsurj hpair_total
  -- STEP 3: the corrected function
  set F₀ : X → ℂ := fun x => Complex.exp (-(u x)) * fT x with hF₀_def
  -- the divisor set
  set S : Set X := Set.range lA ∪ Set.range lB with hS_def
  have hSfin : S.Finite := (Set.finite_range _).union (Set.finite_range _)
  have hSc_open : IsOpen Sᶜ := hSfin.isClosed.isOpen_compl
  have hmemSc : ∀ x ∈ Sᶜ, ∀ l : Λ, x ≠ lA l ∧ x ≠ lB l := by
    intro x hx l
    constructor
    · intro heq
      exact hx (Or.inl ⟨l, heq.symm⟩)
    · intro heq
      exact hx (Or.inr ⟨l, heq.symm⟩)
  -- real smoothness of `F₀` off `S`
  have hexp_smooth : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun x => Complex.exp (-(u x))) := by
    have h1 : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun x : X => -(u x)) := u.contMDiff.neg
    have h2 : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (Complex.exp) :=
      contMDiff_iff_contDiff.mpr (Complex.contDiff_exp (𝕜 := ℝ))
    exact h2.comp h1
  have hfT_smooth : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ fT Sᶜ := by
    rw [hfT_def]
    refine RS.AbelWeak.contMDiffOn_finsetProd_real hSc_open (fun l _ => ?_)
    refine (hsmooth l).mono (fun x hx => ?_)
    exact (hmemSc x hx l).1
  have hF₀_smooth : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F₀ Sᶜ := by
    intro x hx
    exact (contMDiffAt_mul_real' (hexp_smooth.contMDiffAt)
      ((hfT_smooth x hx).contMDiffAt (hSc_open.mem_nhds hx))).contMDiffWithinAt
  -- the dbar-closure of `F₀` off `S`
  have hdbar_zero := isDbarOn_exp_neg_mul_prod hsmooth hne hdlog u hu hmemSc
  -- holomorphy off `S`
  have hholo : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω F₀ Sᶜ :=
    RS.contMDiffOn_omega_of_isDbarOn_zero hSc_open hF₀_smooth hdbar_zero
  -- STEP 4: meromorphy and orders at every point, via the promotion lemma
  have hmero_ord : ∀ x : X, RS.MeromorphicAtX F₀ x ∧
      RS.ordAtX F₀ x = ((∑ l : Λ, linkOrd (lA l) (lB l) x : ℤ) : WithTop ℤ) := by
    intro x
    set z₀ : ℂ := chartAt ℂ x x with hz₀_def
    -- the punctured-holomorphy neighborhood
    set V : Set ℂ := (chartAt ℂ x).target ∩ ⇑(chartAt ℂ x).symm ⁻¹' ((S \ {x})ᶜ) with hV_def
    have hVopen : IsOpen V := by
      have h1 : IsOpen ((S \ {x})ᶜ) := ((hSfin.subset Set.sdiff_subset).isClosed).isOpen_compl
      have hthis := (chartAt ℂ x).symm.isOpen_inter_preimage h1
      rw [hV_def]
      exact hthis
    have hz₀V : z₀ ∈ V := by
      constructor
      · exact mem_chart_target ℂ x
      · rw [Set.mem_preimage, hz₀_def, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
        intro hmem
        exact hmem.2 rfl
    have hVmem : V ∈ nhds z₀ := hVopen.mem_nhds hz₀V
    have hVsub : V \ {z₀} ⊆ (chartAt ℂ x).target ∩ ⇑(chartAt ℂ x).symm ⁻¹' Sᶜ := by
      rintro w ⟨⟨hw1, hw2⟩, hw3⟩
      refine ⟨hw1, ?_⟩
      rw [Set.mem_preimage] at hw2 ⊢
      intro hmem
      refine hw2 ⟨hmem, fun heq => ?_⟩
      rw [Set.mem_singleton_iff] at heq
      apply hw3
      rw [Set.mem_singleton_iff, hz₀_def]
      calc w = chartAt ℂ x ((chartAt ℂ x).symm w) := ((chartAt ℂ x).right_inv hw1).symm
        _ = chartAt ℂ x x := by rw [heq]
    -- punctured differentiability of the chart representative
    have hdiffV : DifferentiableOn ℂ (F₀ ∘ ⇑(chartAt ℂ x).symm) (V \ {z₀}) := by
      have hsymm : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (⇑(chartAt ℂ x).symm) (chartAt ℂ x).target :=
        contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
      have hcomp : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (F₀ ∘ ⇑(chartAt ℂ x).symm)
          ((chartAt ℂ x).target ∩ ⇑(chartAt ℂ x).symm ⁻¹' Sᶜ) :=
        hholo.comp (hsymm.mono inter_subset_left) (fun w hw => hw.2)
      have hcd : ContDiffOn ℂ ω (F₀ ∘ ⇑(chartAt ℂ x).symm)
          ((chartAt ℂ x).target ∩ ⇑(chartAt ℂ x).symm ⁻¹' Sᶜ) :=
        contMDiffOn_iff_contDiffOn.mp hcomp
      exact (hcd.differentiableOn (by simp)).mono hVsub
    -- the factor limit
    obtain ⟨Cs, hCs_ne, hCs⟩ : ∃ Cs : Λ → ℂ, (∀ l, Cs l ≠ 0) ∧ ∀ l : Λ, Tendsto
        (fun z => f l ((chartAt ℂ x).symm z) * (z - z₀) ^ (-(linkOrd (lA l) (lB l) x)))
        (nhdsWithin z₀ {z₀}ᶜ) (nhds (Cs l)) := by
      choose Cs h1 h2 using fun l : Λ => hfactor l x
      exact ⟨Cs, h1, h2⟩
    have hexp_t : Tendsto (fun z => Complex.exp (-(u ((chartAt ℂ x).symm z))))
        (nhdsWithin z₀ {z₀}ᶜ) (nhds (Complex.exp (-(u x)))) := by
      have hcont : ContinuousAt (fun z => Complex.exp (-(u ((chartAt ℂ x).symm z)))) z₀ := by
        have h1 : ContinuousAt (⇑u ∘ ⇑(chartAt ℂ x).symm) z₀ :=
          (u.differentiableAt_comp_chartAt_symm x (mem_chart_target ℂ x)).continuousAt
        exact (Complex.continuous_exp.continuousAt).comp (h1.neg)
      have hval : Complex.exp (-(u ((chartAt ℂ x).symm z₀))) = Complex.exp (-(u x)) := by
        rw [hz₀_def, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
      have := hcont.tendsto
      rw [hval] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hprod_t : Tendsto (fun z => ∏ l : Λ,
        (f l ((chartAt ℂ x).symm z) * (z - z₀) ^ (-(linkOrd (lA l) (lB l) x))))
        (nhdsWithin z₀ {z₀}ᶜ) (nhds (∏ l : Λ, Cs l)) :=
      tendsto_finsetProd Finset.univ (fun l _ => hCs l)
    have hCtot_ne : Complex.exp (-(u x)) * ∏ l : Λ, Cs l ≠ 0 :=
      mul_ne_zero (Complex.exp_ne_zero _)
        (Finset.prod_ne_zero_iff.mpr (fun l _ => hCs_ne l))
    have hfactor_tot : Tendsto (fun z => (F₀ ∘ ⇑(chartAt ℂ x).symm) z *
        (z - z₀) ^ (-(∑ l : Λ, linkOrd (lA l) (lB l) x)))
        (nhdsWithin z₀ {z₀}ᶜ) (nhds (Complex.exp (-(u x)) * ∏ l : Λ, Cs l)) := by
      refine (hexp_t.mul hprod_t).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hzz : z - z₀ ≠ 0 := sub_ne_zero.mpr (by simpa using hz)
      have hzpow : (z - z₀) ^ (-(∑ l : Λ, linkOrd (lA l) (lB l) x))
          = ∏ l : Λ, (z - z₀) ^ (-(linkOrd (lA l) (lB l) x)) := by
        rw [← zpow_finset_sum hzz, ← Finset.sum_neg_distrib]
      change Complex.exp (-(u ((chartAt ℂ x).symm z))) *
          ∏ l : Λ, (f l ((chartAt ℂ x).symm z) * (z - z₀) ^ (-(linkOrd (lA l) (lB l) x)))
        = (F₀ ∘ ⇑(chartAt ℂ x).symm) z *
          (z - z₀) ^ (-(∑ l : Λ, linkOrd (lA l) (lB l) x))
      rw [hzpow, Finset.prod_mul_distrib]
      change Complex.exp (-(u ((chartAt ℂ x).symm z))) *
          ((∏ l : Λ, f l ((chartAt ℂ x).symm z)) *
            ∏ l : Λ, (z - z₀) ^ (-(linkOrd (lA l) (lB l) x)))
        = Complex.exp (-(u ((chartAt ℂ x).symm z))) * fT ((chartAt ℂ x).symm z) *
          ∏ l : Λ, (z - z₀) ^ (-(linkOrd (lA l) (lB l) x))
      rw [hfT_def]
      ring
    exact meromorphicAt_of_tendsto_factor hVmem hdiffV hCtot_ne hfactor_tot
  -- STEP 5: package as a `Mero` and read off orders
  have hmero : RS.MeromorphicOnX F₀ (Set.univ : Set X) := fun x _ => (hmero_ord x).1
  set F : RS.Mero X := RS.MeroGermOn.mk F₀ hmero with hF_def
  have hord : ∀ z : X, F.ord z = ((∑ l : Λ, linkOrd (lA l) (lB l) z : ℤ) : WithTop ℤ) := by
    intro z
    rw [hF_def, RS.MeroGermOn.ord_mk isOpen_univ (Set.mem_univ z)]
    exact (hmero_ord z).2
  -- telescope the link orders back to endpoint orders
  have htel : ∀ z : X, ∑ l : Λ, linkOrd (lA l) (lB l) z = ∑ i, linkOrd (A i) (B i) z := by
    intro z
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hstep : ∀ k : ℕ, linkOrd ((δ i).extend ((C i).t k)) ((δ i).extend ((C i).t (k + 1))) z
        = (if z = (δ i).extend ((C i).t (k + 1)) then (1 : ℤ) else 0)
          - (if z = (δ i).extend ((C i).t k) then (1 : ℤ) else 0) := fun k => rfl
    calc ∑ k : Fin (C i).n, linkOrd (lA ⟨i, k⟩) (lB ⟨i, k⟩) z
        = ∑ k ∈ Finset.range (C i).n,
          ((if z = (δ i).extend ((C i).t (k + 1)) then (1 : ℤ) else 0)
            - (if z = (δ i).extend ((C i).t k) then (1 : ℤ) else 0)) := by
          rw [← Fin.sum_univ_eq_sum_range (fun k =>
            (if z = (δ i).extend ((C i).t (k + 1)) then (1 : ℤ) else 0)
              - (if z = (δ i).extend ((C i).t k) then (1 : ℤ) else 0)) (C i).n]
          exact Finset.sum_congr rfl (fun k _ => rfl)
      _ = (if z = (δ i).extend ((C i).t (C i).n) then (1 : ℤ) else 0)
          - (if z = (δ i).extend ((C i).t 0) then (1 : ℤ) else 0) :=
          Finset.sum_range_sub (fun k => if z = (δ i).extend ((C i).t k) then (1 : ℤ) else 0)
            (C i).n
      _ = linkOrd (A i) (B i) z := by
          rw [(C i).ht0, (C i).ht1 (C i).n le_rfl, Path.extend_zero, Path.extend_one]
          rfl
  -- non-vanishing
  have hF_ne : F ≠ 0 := by
    intro heq
    have hx₀ := hord (Classical.arbitrary X)
    rw [heq] at hx₀
    rw [RS.MeroGermOn.ord_zero] at hx₀
    rw [if_pos ⟨isOpen_univ, Set.mem_univ _⟩] at hx₀
    exact absurd hx₀.symm WithTop.coe_ne_top
  refine ⟨F, hF_ne, fun z => ?_⟩
  rw [hord z, htel z]

/-! ## The gated discharges of the two isolated hypotheses -/

variable [ConnectedSpace X] [DecidableEq X]

/-- **Design §4.1 steps 5-7, DISCHARGED** modulo `serre-duality-tails`'s single remaining
external fact: `WeakSolutionUpgrade X` holds. (The weak-solution argument of the hypothesis is
not needed — the construction builds its own chain pieces along the given zero-period path.) -/
theorem weakSolutionUpgrade_of_surjective
    (hsurj : Function.Surjective (RS.LaurentTail.tailToH1 (0 : RS.Divisor X))) :
    WeakSolutionUpgrade X := by
  intro f P Q hPQ δ hf hper
  obtain ⟨F, hF0, hord⟩ := exists_mero_of_sum_pathIntegral_eq_zero (ι := Fin 1) hsurj
    (A := fun _ => Q) (B := fun _ => P) (fun _ => δ) (fun θ => by simpa using hper θ)
  refine ⟨F, hF0, ?_, ?_, ?_⟩
  · rw [hord P]
    have h1 : (∑ _i : Fin 1, linkOrd Q P P) = 1 := by
      simp [linkOrd, if_neg (fun h : P = Q => hPQ h.symm)]
    rw [h1]
    rfl
  · rw [hord Q]
    have h1 : (∑ _i : Fin 1, linkOrd Q P Q) = -1 := by
      simp [linkOrd, if_neg (fun h : Q = P => hPQ h)]
    rw [h1]
    rfl
  · intro z hzQ hzP
    rw [hord z]
    have h1 : (∑ _i : Fin 1, linkOrd Q P z) = 0 := by
      simp [linkOrd, if_neg hzP, if_neg hzQ]
    rw [h1]
    rfl

/-- **The `k`-point discharge** (design §4.1, the shape `period-lattice-rank`'s Thm 21.4(b)
consumes), same single gate. -/
theorem weakSolutionUpgradeFinset_of_surjective {ι : Type*} [Fintype ι]
    (hsurj : Function.Surjective (RS.LaurentTail.tailToH1 (0 : RS.Divisor X))) :
    WeakSolutionUpgradeFinset X ι := by
  classical
  intro f a x ha hx hax γ hf hper
  obtain ⟨F, hF0, hord⟩ := exists_mero_of_sum_pathIntegral_eq_zero (ι := ι) hsurj
    (A := a) (B := x) γ hper
  have hzero_at : ∀ z : X, (∀ i, z ≠ a i) → (∀ i, z ≠ x i) →
      (∑ j, linkOrd (a j) (x j) z) = 0 := by
    intro z hza hzx
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [linkOrd, if_neg (hzx j), if_neg (hza j), sub_self]
  refine ⟨F, hF0, ?_, ?_, ?_⟩
  · intro i
    rw [hord (x i)]
    have h1 : (∑ j, linkOrd (a j) (x j) (x i)) = 1 := by
      have hsplit : ∀ j, linkOrd (a j) (x j) (x i)
          = (if i = j then (1 : ℤ) else 0) := by
        intro j
        rw [linkOrd, if_neg (show ¬(x i = a j) from fun h => hax j i h.symm)]
        by_cases h : i = j
        · rw [if_pos (congrArg x h), if_pos h, sub_zero]
        · rw [if_neg (fun hh => h (hx hh)), if_neg h, sub_zero]
      rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_ite_eq]
      simp
    rw [h1]
    rfl
  · intro i
    rw [hord (a i)]
    have h1 : (∑ j, linkOrd (a j) (x j) (a i)) = -1 := by
      have hsplit : ∀ j, linkOrd (a j) (x j) (a i)
          = -(if i = j then (1 : ℤ) else 0) := by
        intro j
        rw [linkOrd, if_neg (hax i j)]
        by_cases h : i = j
        · rw [if_pos (congrArg a h), if_pos h, zero_sub]
        · rw [if_neg (fun hh => h (ha hh)), if_neg h, zero_sub, neg_zero]
      rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_neg_distrib,
        Finset.sum_ite_eq]
      simp
    rw [h1]
    rfl
  · intro z hza hzx
    rw [hord z, hzero_at z hza hzx]
    rfl

end RS.Abel

end
