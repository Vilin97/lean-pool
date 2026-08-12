/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.CanonicalForms.OneDimensional

/-!
# `Ω(D)`, the `L(D+K)` bridge, holomorphic forms, and ML form data (D11/D12/D13)

Unit: canonical-forms (`docs/design/canonical-forms.md` §2 D11–D13, §4.5, proof plan §5 P6).

* `MForm.OmegaSpace D : Submodule ℂ (MForm X)` (Miranda's `L⁽¹⁾(D)`/Forster's `Γ(X,Ω_D)`):
  meromorphic 1-forms with `-D ≤` order everywhere, defined order-wise on the QUOTIENT (mirrors
  `LinSys`'s primary definition); `MForm.i D` (index of speciality). Instance-free (the order-wise
  carrier needs no topology), strictly more general than the design's listing.
* **D11** `ΩIsoLinSys : OmegaSpace D ≃ₗ[ℂ] LinSys (D + canonicalDivisorOf θ₀)` (Forster 17.4 /
  Miranda `Ω_D ≅ O_{D+K}`), via D8's one-dimensionality (`LinearEquiv.ofBijective` of
  `h ↦ h • θ₀`, membership transported by the pointwise `smul_mem_omegaSpace_iff` dictionary);
  `i_eq_l_add_canonicalDivisorOf`.
* **D12** `holomorphicMFormsEquiv : Form1 X ≃ₗ[ℂ] OmegaSpace (0 : Divisor X)`: forward is
  `Form1.toMForm` (analytic coefficients have `0 ≤ ord`); injectivity is continuity at chart
  centers; surjectivity REPAIRS a representative via the mero unit's canonical `holoRepr` pattern
  — for a class with `0 ≤ ord` everywhere, the chart-local coefficient germs
  `MeroGermOn.mk (θ.coeffAt x ∘ chartAt ℂ x)` have honest analytic `holoRepr`s
  (`ord_eq_meromorphicOrderAt_of_mem_source` bridges center-orders to target-orders), whose
  chart reads assemble into a `Form1CoeffData` and a genuine `Form1` via `Form1.ofCoeffs`.
  Needs NO topological instances (the design's `[T1][T2][Compact]` are unnecessary here).
  Corollary `genus_eq_finrank_omegaSpace_zero` (the cech-h1-genus/riemann-roch export).
* **D13** `MLFormData`/`Realizes` (against `MForm.laurentCoeffAt`, on classes)/`totalRes`/
  `Realizes.resAt_eq`: a thin `X`-level wrapper around residue-calculus's `PrincipalPartData`.
-/

open scoped ContDiff Manifold
open Set IsManifold Filter Topology

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Order arithmetic (junk-robust; data layer, then descended) -/

namespace MFormData

theorem ord_add (θ η : MFormData X) (x : X) : min (θ.ord x) (η.ord x) ≤ (θ + η).ord x := by
  have hf : (θ + η).coeffAt x = θ.coeffAt x + η.coeffAt x := funext fun z => coeffAt_add θ η x z
  change min (θ.ord x) (η.ord x) ≤ meromorphicOrderAt ((θ + η).coeffAt x) (chartAt ℂ x x)
  rw [hf]
  exact meromorphicOrderAt_add (θ.meromorphicAt_coeffAt x) (η.meromorphicAt_coeffAt x)

theorem ord_smul {c : ℂ} (hc : c ≠ 0) (θ : MFormData X) (x : X) : (c • θ).ord x = θ.ord x := by
  have hf : (c • θ).coeffAt x = c • θ.coeffAt x := funext fun z => by
    rw [coeffAt_smul]; rfl
  change meromorphicOrderAt ((c • θ).coeffAt x) (chartAt ℂ x x) = θ.ord x
  rw [hf]
  exact meromorphicOrderAt_smul_of_ne_zero analyticAt_const hc

end MFormData

namespace MForm

theorem ord_add (Θ H : MForm X) (x : X) : min (Θ.ord x) (H.ord x) ≤ (Θ + H).ord x :=
  Quotient.inductionOn₂ Θ H fun θ η => MFormData.ord_add θ η x

theorem ord_smul {c : ℂ} (hc : c ≠ 0) (Θ : MForm X) (x : X) : (c • Θ).ord x = Θ.ord x := by
  obtain ⟨θ, rfl⟩ := exists_rep Θ
  exact MFormData.ord_smul hc θ x

/-! ### `MForm.OmegaSpace` (D11) -/

/-- Meromorphic 1-forms with divisor `≥ -D` (Miranda's `L⁽¹⁾(D)`/Forster's `Γ(X, Ω_D)`), defined
order-wise on the quotient (mirrors `LinSys`'s own primary definition). -/
def OmegaSpace (D : Divisor X) : Submodule ℂ (MForm X) where
  carrier := {Θ | ∀ x, ((-(D x) : ℤ) : WithTop ℤ) ≤ Θ.ord x}
  zero_mem' := fun x => by rw [ord_zero]; exact le_top
  add_mem' := by
    intro Θ H hΘ hH x
    exact le_trans (le_min (hΘ x) (hH x)) (ord_add Θ H x)
  smul_mem' := by
    intro c Θ hΘ x
    rcases eq_or_ne c 0 with rfl | hc
    · rw [zero_smul, ord_zero]; exact le_top
    · rw [ord_smul hc]; exact hΘ x

theorem mem_omegaSpace_iff {D : Divisor X} {Θ : MForm X} :
    Θ ∈ OmegaSpace D ↔ ∀ x, ((-(D x) : ℤ) : WithTop ℤ) ≤ Θ.ord x := Iff.rfl

/-- Index of speciality: `dim Ω(D)`. -/
noncomputable def i (D : Divisor X) : ℕ := Module.finrank ℂ (OmegaSpace D)

end MForm

/-! ### D11: the `Ω(D) ≅ L(D+K)` bridge -/

section OmegaLinSys

variable [T1Space X] [T2Space X] [CompactSpace X] [ConnectedSpace X]

omit [T2Space X] [CompactSpace X] in
/-- The pointwise membership dictionary (Forster 17.4's computation): `h • θ₀` has order `≥ -D`
everywhere iff `h ∈ L(D + K)`, `K := canonicalDivisorOf θ₀`. -/
theorem MForm.smul_mem_omegaSpace_iff {Θ₀ : MForm X} (h₀ : Θ₀ ≠ 0) {h : ℳ X} {D : Divisor X} :
    h • Θ₀ ∈ MForm.OmegaSpace D ↔ h ∈ LinSys (D + canonicalDivisorOf Θ₀) := by
  simp only [MForm.mem_omegaSpace_iff, mem_linSys_iff]
  refine forall_congr' fun x => ?_
  rw [MForm.ord_smul_mero, Divisor.add_apply]
  have hKx : ((canonicalDivisorOf Θ₀ x : ℤ) : WithTop ℤ) = Θ₀.ord x := by
    rw [MForm.divisor_apply]
    exact WithTop.coe_untop₀_of_ne_top (MForm.ord_ne_top h₀ x)
  rcases eq_or_ne (h.ord x) ⊤ with htop | hne
  · rw [htop, top_add]
    exact iff_of_true le_top le_top
  · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hne
    rw [← ha, ← hKx, ← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
    omega

/-- The forward leg of the D11 bridge: multiplication by `θ₀`, `L(D+K) →ₗ Ω(D)`. -/
noncomputable def linSysToOmega {Θ₀ : MForm X} (h₀ : Θ₀ ≠ 0) (D : Divisor X) :
    LinSys (D + canonicalDivisorOf Θ₀) →ₗ[ℂ] MForm.OmegaSpace D where
  toFun h := ⟨h.1 • Θ₀, (MForm.smul_mem_omegaSpace_iff h₀).2 h.2⟩
  map_add' a b := Subtype.ext (add_smul a.1 b.1 Θ₀)
  map_smul' c a := Subtype.ext (smul_assoc c a.1 Θ₀)

/-- **D11 (Forster 17.4 / Miranda `Ω_D ≅ O_{D+K}`)**: multiplication by a fixed nonzero
reference `θ₀` (with `K := canonicalDivisorOf θ₀`) is a linear equivalence `Ω(D) ≅ L(D+K)`. -/
noncomputable def ΩIsoLinSys {Θ₀ : MForm X} (h₀ : Θ₀ ≠ 0) (D : Divisor X) :
    MForm.OmegaSpace D ≃ₗ[ℂ] LinSys (D + canonicalDivisorOf Θ₀) :=
  (LinearEquiv.ofBijective (linSysToOmega h₀ D)
    ⟨fun a b hab =>
      Subtype.ext (MForm.smul_left_injective h₀ (congrArg Subtype.val hab)),
     fun t => by
      obtain ⟨h, hh⟩ := MForm.exists_smul_eq h₀ t.1
      exact ⟨⟨h, (MForm.smul_mem_omegaSpace_iff h₀).1 (hh ▸ t.2)⟩, Subtype.ext hh.symm⟩⟩).symm

omit [CompactSpace X] in
/-- D11's dimension dictionary: `i(D) = l(D + K)`. -/
theorem i_eq_l_add_canonicalDivisorOf {Θ₀ : MForm X} (h₀ : Θ₀ ≠ 0) (D : Divisor X) :
    MForm.i D = l (D + canonicalDivisorOf Θ₀) :=
  (ΩIsoLinSys h₀ D).finrank_eq

end OmegaLinSys

/-! ### D12: `Form1 ≃ₗ Ω(0)` (the holomorphic forms bridge) -/

/-- The forward leg of D12: a holomorphic 1-form as an element of `Ω(0)`. -/
noncomputable def form1ToOmega : Form1 X →ₗ[ℂ] MForm.OmegaSpace (0 : Divisor X) where
  toFun η := ⟨MForm.ofForm1 η, fun x => by
    have h0 : ((0 : Divisor X) x) = 0 := rfl
    rw [h0]
    simpa using MForm.ofForm1_ord_nonneg η x⟩
  map_add' η η' := Subtype.ext (congrArg MForm.mk (MFormData.ofForm1_add η η'))
  map_smul' c η := Subtype.ext (congrArg MForm.mk (MFormData.ofForm1_smul c η))

open scoped Classical in
/-- D12 surjectivity: any class of `0 ≤ ord` everywhere is `ofForm1` of a genuine `Form1` — the
representative is REPAIRED chart-by-chart through the mero unit's canonical `holoRepr`. -/
theorem form1ToOmega_surjective :
    Function.Surjective (form1ToOmega : Form1 X → MForm.OmegaSpace (0 : Divisor X)) := by
  rintro ⟨Θ, hmem⟩
  obtain ⟨θ, hθ⟩ := MForm.exists_rep Θ
  -- `0 ≤ ord` everywhere, transported to the representative
  have hord : ∀ p : X, 0 ≤ θ.ord p := by
    intro p
    have h1 := hmem p
    rw [← hθ] at h1
    simpa using h1
  -- the chart-local coefficient as an X-level function
  set g : X → X → ℂ := fun x w => θ.coeffAt x (chartAt ℂ x w) with hg_def
  -- meromorphy on the chart source
  have hmero : ∀ x : X, MeromorphicOnX (g x) (chartAt ℂ x).source := by
    intro x p hp
    rw [meromorphicAtX_iff_of_mem_source (chart_mem_maximalAtlas x) hp]
    have hzt : chartAt ℂ x p ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hp
    have heq : θ.coeffAt x =ᶠ[𝓝[≠] (chartAt ℂ x p)] (g x) ∘ ⇑(chartAt ℂ x).symm := by
      have hev : ∀ᶠ z in 𝓝 (chartAt ℂ x p), z ∈ (chartAt ℂ x).target :=
        (chartAt ℂ x).open_target.mem_nhds hzt
      filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with z hz
      change θ.coeffAt x z = θ.coeffAt x (chartAt ℂ x ((chartAt ℂ x).symm z))
      rw [(chartAt ℂ x).right_inv hz]
    exact (θ.meromorphicOn_coeffAt x _ hzt).congr heq
  -- cross-point order bridge: `ordAtX (g x) p = θ.ord p` for `p` in the chart source
  have hbridge : ∀ x : X, ∀ p ∈ (chartAt ℂ x).source, ordAtX (g x) p = θ.ord p := by
    intro x p hp
    obtain ⟨hσ, hσ'⟩ := analyticAt_transition (chart_mem_maximalAtlas p)
      (chart_mem_maximalAtlas x) (mem_chart_source ℂ p) hp
    have h1 : ordAtX (g x) p =
        meromorphicOrderAt (θ.coeffAt x ∘ (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ p).symm))
          (chartAt ℂ p p) := rfl
    rw [h1, meromorphicOrderAt_comp_of_deriv_ne_zero hσ hσ',
      θ.ord_eq_meromorphicOrderAt_of_mem_source hp]
    congr 1
    change chartAt ℂ x ((chartAt ℂ p).symm (chartAt ℂ p p)) = chartAt ℂ x p
    rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
  -- the germ class per chart, and its repaired representative
  set φ : ∀ x : X, MeroGermOn X (chartAt ℂ x).source :=
    fun x => MeroGermOn.mk (g x) (hmero x) with hφ_def
  have hordφ : ∀ x : X, ∀ p ∈ (chartAt ℂ x).source, 0 ≤ (φ x).ord p := by
    intro x p hp
    rw [hφ_def, MeroGermOn.ord_mk (chartAt ℂ x).open_source hp, hbridge x p hp]
    exact hord p
  have hcm : ∀ x : X, ∀ p ∈ (chartAt ℂ x).source,
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (φ x).holoRepr p :=
    fun x p hp => MeroGermOn.holoRepr_contMDiffAt (chartAt ℂ x).open_source hp (hordφ x p hp)
  -- the repaired chart coefficients are honestly analytic on the whole target
  have hanalytic : ∀ x : X,
      AnalyticOnNhd ℂ ((φ x).holoRepr ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x).target := by
    intro x z hz
    have hp : (chartAt ℂ x).symm z ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
    have h2 := (contMDiffAt_iff_analyticAt_of_mem_source (chart_mem_atlas ℂ x) hp).1
      (hcm x _ hp)
    rwa [(chartAt ℂ x).right_inv hz] at h2
  -- the repaired coefficients satisfy Form1's compat, pointwise (via evalAt limits)
  have hcompat : ∀ x y : X, ∀ p ∈ (chartAt ℂ x).source ∩ (chartAt ℂ y).source,
      ((φ y).holoRepr ∘ ⇑(chartAt ℂ y).symm) (chartAt ℂ y p) =
        deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) (chartAt ℂ y p) *
          ((φ x).holoRepr ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x p) := by
    intro x y p hp
    obtain ⟨hσ, hσ'⟩ := analyticAt_transition (chart_mem_maximalAtlas y)
      (chart_mem_maximalAtlas x) hp.2 hp.1
    have hty := MeroGermOn.tendsto_evalAt (chartAt ℂ y).open_source hp.2 (φ y)
      (hordφ y p hp.2) rfl
    have htx := MeroGermOn.tendsto_evalAt (chartAt ℂ x).open_source hp.1 (φ x)
      (hordφ x p hp.1) rfl
    have hev : g y =ᶠ[𝓝[≠] p] fun w =>
        deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) (chartAt ℂ y w) * g x w := by
      have hmemo : ∀ᶠ w in 𝓝 p, w ∈ (chartAt ℂ x).source ∩ (chartAt ℂ y).source :=
        ((chartAt ℂ x).open_source.inter (chartAt ℂ y).open_source).mem_nhds hp
      filter_upwards [hmemo.filter_mono nhdsWithin_le_nhds] with w hw
      have hli : (chartAt ℂ y).symm (chartAt ℂ y w) = w := (chartAt ℂ y).left_inv hw.2
      have hc := θ.compat x y (chartAt ℂ y w) ⟨w, hw, rfl⟩
      rw [hli] at hc
      exact hc
    have hcont : ContinuousAt
        (fun w => deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) (chartAt ℂ y w)) p :=
      hσ.deriv.continuousAt.comp ((chartAt ℂ y).continuousAt hp.2)
    have htmul : Tendsto
        (fun w => deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) (chartAt ℂ y w) * g x w)
        (𝓝[≠] p)
        (𝓝 (deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) (chartAt ℂ y p) *
          (φ x).evalAt p)) :=
      (hcont.tendsto.mono_left nhdsWithin_le_nhds).mul htx
    have hlim := tendsto_nhds_unique (hty.congr' hev) htmul
    -- rewrite both sides to `evalAt p`
    have hliy : (chartAt ℂ y).symm (chartAt ℂ y p) = p := (chartAt ℂ y).left_inv hp.2
    have hlix : (chartAt ℂ x).symm (chartAt ℂ x p) = p := (chartAt ℂ x).left_inv hp.1
    change (φ y).holoRepr ((chartAt ℂ y).symm (chartAt ℂ y p)) =
      deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) (chartAt ℂ y p) *
        (φ x).holoRepr ((chartAt ℂ x).symm (chartAt ℂ x p))
    rw [hliy, hlix]
    exact hlim
  -- assemble the Form1
  set Dcoeff : Form1CoeffData X X :=
    { chart := fun x => chartAt ℂ x
      mem_maximalAtlas := fun x => chart_mem_maximalAtlas x
      exists_mem := fun x => ⟨x, mem_chart_source ℂ x⟩
      coeff := fun x => (φ x).holoRepr ∘ ⇑(chartAt ℂ x).symm
      analyticOnNhd := hanalytic
      compat := hcompat } with hD_def
  refine ⟨Form1.ofCoeffs Dcoeff, Subtype.ext ?_⟩
  change MForm.ofForm1 (Form1.ofCoeffs Dcoeff) = Θ
  rw [← hθ]
  refine MForm.sound fun x => ?_
  have htarget : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x), z ∈ (chartAt ℂ x).target :=
    eventually_nhdsWithin_of_eventually_nhds
      ((chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x))
  have hhol : ((φ x).holoRepr ∘ ⇑(chartAt ℂ x).symm) =ᶠ[𝓝[≠] (chartAt ℂ x x)]
      ((g x) ∘ ⇑(chartAt ℂ x).symm) :=
    eventuallyEq_nhdsNE_comp_chart_iff.mp
      (MeroGermOn.holoRepr_eventuallyEq_nhdsNE (chartAt ℂ x).open_source
        (mem_chart_source ℂ x) (φ x) rfl)
  filter_upwards [htarget, hhol] with z hz hzh
  change (if z ∈ (chartAt ℂ x).target then coeffIn (chartAt ℂ x) (Form1.ofCoeffs Dcoeff) z else 0)
      = θ.coeffAt x z
  rw [ite_eq_left hz, Form1.coeffIn_ofCoeffs Dcoeff x hz]
  change ((φ x).holoRepr ∘ ⇑(chartAt ℂ x).symm) z = θ.coeffAt x z
  rw [hzh]
  change θ.coeffAt x (chartAt ℂ x ((chartAt ℂ x).symm z)) = θ.coeffAt x z
  rw [(chartAt ℂ x).right_inv hz]

/-- **D12**: holomorphic 1-forms ARE the meromorphic 1-forms of nonnegative divisor. (No
topological instances needed — strictly more general than the design's listing.) -/
noncomputable def holomorphicMFormsEquiv : Form1 X ≃ₗ[ℂ] MForm.OmegaSpace (0 : Divisor X) :=
  LinearEquiv.ofBijective form1ToOmega
    ⟨fun _ _ h => MForm.ofForm1_injective (congrArg Subtype.val h), form1ToOmega_surjective⟩

/-- The genus counts meromorphic 1-forms of nonnegative divisor (the cech-h1-genus/riemann-roch
export; `l(K) = g` becomes a one-line corollary of this + `i_eq_l_add_canonicalDivisorOf` once
Serre duality lands downstream). -/
theorem genus_eq_finrank_omegaSpace_zero :
    genus X = Module.finrank ℂ ↥(MForm.OmegaSpace (0 : Divisor X)) :=
  (holomorphicMFormsEquiv (X := X)).finrank_eq

/-! ### `MLFormData` (D13, Forster §17.1–17.2) -/

/-- A form-level Mittag-Leffler datum: at finitely many points of `X`, a principal part read in
the preferred chart. A thin wrapper around residue-calculus's already-built `PrincipalPartData`. -/
structure MLFormData (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] where
  /-- The finite set of points carrying prescribed principal parts. -/
  pts : Finset X
  /-- The principal part prescribed at each marked point, read in that point's chart. -/
  data : ∀ x ∈ pts, PrincipalPartData (chartAt ℂ x).target

/-- `μ` realizes the principal parts of `Θ` at every point of `μ.pts` (read in each point's own
preferred chart; stated on classes via the lifted `MForm.laurentCoeffAt`). -/
def MLFormData.Realizes (μ : MLFormData X) (Θ : MForm X) : Prop :=
  ∀ x (hx : x ∈ μ.pts), ∀ k < 0,
    Θ.laurentCoeffAt x k = (μ.data x hx).coeff (chartAt ℂ x x) k

/-- The total residue prescribed by the datum. -/
noncomputable def MLFormData.totalRes (μ : MLFormData X) : ℂ :=
  ∑ x ∈ μ.pts.attach, (μ.data x.1 x.2).coeff (chartAt ℂ x.1 x.1) (-1)

theorem MLFormData.Realizes.resAt_eq {μ : MLFormData X} {Θ : MForm X} (h : μ.Realizes Θ)
    {x : X} (hx : x ∈ μ.pts) : Θ.resAt x = (μ.data x hx).coeff (chartAt ℂ x x) (-1) := by
  rw [Θ.resAt_eq_laurentCoeffAt x]
  exact h x hx (-1) (by norm_num)

end RS
