/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.LaurentTail.Truncation

/-!
# `truncT`/`singleT`/`mulInto`/`nuL`: the truncation and multiplication kit (serre-duality-tails)

Unit: serre-duality-tails (`docs/design/serre-duality-tails.md` §3 D1/D3, §5.1, §6 P1).

* `truncAt`/`truncT`: Miranda's truncation lattice `t^{D₁}_{D₂} : T[D₁] → T[D₂]` for `D₁ ≤ D₂`
  (coarser quotient; surjective), and its compatibility with `alphaL` (Miranda Problem C).
* `singleT`: the test-vector tail at a single point (used by the injectivity/Lemma-3.6 witnesses).
* `mulIntoAt`/`mulInto`: Miranda's `t ∘ μ_f` as ONE uniform map `T D →ₗ[ℂ] T E`, linear in `f`
  (no `f ≠ 0` needed), surjective when `f ≠ 0` (Problem B: compatibility with `alphaL`).
* `nuL`: the packaging `↥(LinSys C) →ₗ[ℂ] (T (A - C) →ₗ[ℂ] T A)` Lemma 3.4's pair map is built from,
  plus the `μ_{1/f}` inversion identity `nuL_mulInto_inv` the surjectivity endgame needs.
-/

open scoped ContDiff Manifold
open Set TopologicalSpace
open RS RS.LaurentTail

namespace RS.TailDuality

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### `ordGe` monotonicity (the engine behind `truncAt`/`mulIntoAt`'s well-definedness) -/

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem ordGe_mono (p : X) {m₁ m₂ : ℤ} (h : m₂ ≤ m₁) :
    RS.Cech.ordGe p m₁ ≤ RS.Cech.ordGe p m₂ := by
  intro ψ hψ
  rw [RS.Cech.mem_ordGe_iff] at hψ ⊢
  exact le_trans (by exact_mod_cast h) hψ

/-! ### `truncAt`/`truncT` (D1) -/

/-- Miranda's `t^{D₁}_{D₂}` at a single point: the coarsening `TailAt p D₁ →ₗ TailAt p D₂`. -/
noncomputable def truncAt (p : X) {D₁ D₂ : RS.Divisor X} (h : D₁ ≤ D₂) :
    TailAt p D₁ →ₗ[ℂ] TailAt p D₂ :=
  Submodule.mapQ _ _ LinearMap.id (by
    rw [Submodule.comap_id]
    exact ordGe_mono p (neg_le_neg (Function.locallyFinsuppWithin.le_def.1 h p)))

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
@[simp] theorem truncAt_mk (p : X) {D₁ D₂ : RS.Divisor X} (h : D₁ ≤ D₂)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    truncAt p h (TailAt.mk p D₁ ψ) = TailAt.mk p D₂ ψ :=
  Submodule.mapQ_apply _ _ _ ψ

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem truncAt_surjective (p : X) {D₁ D₂ : RS.Divisor X} (h : D₁ ≤ D₂) :
    Function.Surjective (truncAt p h) := by
  intro z
  obtain ⟨ψ, rfl⟩ := TailAt.mk_surjective p D₂ z
  exact ⟨TailAt.mk p D₁ ψ, truncAt_mk p h ψ⟩

variable [DecidableEq X]

/-- Miranda's `t^{D₁}_{D₂} : T[D₁] → T[D₂]`, assembled pointwise. -/
noncomputable def truncT {D₁ D₂ : RS.Divisor X} (h : D₁ ≤ D₂) : T D₁ →ₗ[ℂ] T D₂ where
  toFun τ := DFinsupp.mapRange (fun p => truncAt p h) (fun _ => map_zero _) τ
  map_add' τ σ := by
    apply DFinsupp.ext
    intro p
    simp only [DFinsupp.add_apply, DFinsupp.mapRange_apply, map_add]
  map_smul' c τ := by
    apply DFinsupp.ext
    intro p
    simp only [DFinsupp.smul_apply, DFinsupp.mapRange_apply, map_smul, RingHom.id_apply]

omit [DecidableEq X] [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem truncT_apply {D₁ D₂ : RS.Divisor X} (h : D₁ ≤ D₂) (τ : T D₁) (p : X) :
    truncT h τ p = truncAt p h (τ p) :=
  DFinsupp.mapRange_apply (fun p => truncAt p h) (fun _ => map_zero _) τ p

omit [DecidableEq X] [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem truncT_surjective {D₁ D₂ : RS.Divisor X} (h : D₁ ≤ D₂) :
    Function.Surjective (truncT h) :=
  (DFinsupp.mapRange_surjective (fun p => truncAt p h) (fun _ => map_zero _)).mpr
    (fun p => truncAt_surjective p h)

theorem truncT_alpha [CompactSpace X] [ConnectedSpace X] {D₁ D₂ : RS.Divisor X}
    (h : D₁ ≤ D₂) (f : RS.Mero X) : truncT h (alphaL D₁ f) = alphaL D₂ f := by
  apply DFinsupp.ext
  intro p
  rw [truncT_apply]
  change truncAt p h (alpha D₁ f p) = alpha D₂ f p
  rw [alpha_apply, truncAt_mk, alpha_apply]

/-! ### `singleT` (the test-vector tails) -/

/-- A single-point test tail: the class of `ψ` at `p`, zero elsewhere. -/
noncomputable def singleT (p : X) (D : RS.Divisor X)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) : T D :=
  DFinsupp.single p (TailAt.mk p D ψ)

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
@[simp] theorem singleT_apply_self (p : X) (D : RS.Divisor X)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) : singleT p D ψ p = TailAt.mk p D ψ :=
  DFinsupp.single_eq_same

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem singleT_apply_of_ne {p q : X} (hqp : q ≠ p) (D : RS.Divisor X)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) : singleT p D ψ q = 0 :=
  DFinsupp.single_eq_of_ne hqp

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem singleT_eq_zero_iff (p : X) (D : RS.Divisor X)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    singleT p D ψ = 0 ↔ (-(D p) : WithTop ℤ) ≤ ψ.ord p := by
  rw [singleT, DFinsupp.single_eq_zero, TailAt.mk_eq_zero_iff]

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
@[simp] theorem truncT_singleT {D₁ D₂ : RS.Divisor X} (h : D₁ ≤ D₂) (p : X)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    truncT h (singleT p D₁ ψ) = singleT p D₂ ψ := by
  apply DFinsupp.ext
  intro q
  rw [truncT_apply]
  rcases eq_or_ne q p with rfl | hqp
  · rw [singleT_apply_self, truncAt_mk, singleT_apply_self]
  · rw [singleT_apply_of_ne hqp, singleT_apply_of_ne hqp, map_zero]

/-! ### `mulIntoAt`/`mulInto` (D3): Miranda's `t ∘ μ_f`, uniform in `f` -/

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [DecidableEq X] in
theorem mulIntoAt_bound_computation (p : X) (f : RS.Mero X) {D E : RS.Divisor X}
    (hf : ((D p - E p : ℤ) : WithTop ℤ) ≤ f.ord p)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) (hψ : ((-(D p) : ℤ) : WithTop ℤ) ≤ ψ.ord p) :
    ((-(E p) : ℤ) : WithTop ℤ) ≤
      (RS.MeroGermOn.restrict (Set.subset_univ (chartAt ℂ p).source) f * ψ).ord p := by
  rw [RS.MeroGermOn.ord_mul (chartAt ℂ p).open_source (mem_chart_source ℂ p),
    RS.MeroGermOn.ord_restrict (Set.subset_univ _) (chartAt ℂ p).open_source isOpen_univ
      (mem_chart_source ℂ p)]
  calc ((-(E p) : ℤ) : WithTop ℤ) = (((D p - E p) + -(D p) : ℤ) : WithTop ℤ) := by
        congr 1; ring
    _ = ((D p - E p : ℤ) : WithTop ℤ) + ((-(D p) : ℤ) : WithTop ℤ) :=
          WithTop.coe_add (D p - E p) (-(D p))
    _ ≤ f.ord p + ψ.ord p := add_le_add hf hψ

/-- Miranda's `μ_f` composed with truncation, at a single point: `TailAt p D →ₗ TailAt p E` for
`f` whose order at `p` is bounded below by `D p - E p`. -/
noncomputable def mulIntoAt (f : RS.Mero X) (p : X) {D E : RS.Divisor X}
    (hf : ((D p - E p : ℤ) : WithTop ℤ) ≤ f.ord p) : TailAt p D →ₗ[ℂ] TailAt p E :=
  Submodule.mapQ _ _ (LinearMap.mulLeft ℂ (RS.MeroGermOn.restrict (Set.subset_univ _) f)) (by
    intro ψ hψ
    rw [RS.Cech.mem_ordGe_iff] at hψ
    rw [Submodule.mem_comap, RS.Cech.mem_ordGe_iff, LinearMap.mulLeft_apply]
    exact mulIntoAt_bound_computation p f hf ψ hψ)

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [DecidableEq X] in
@[simp] theorem mulIntoAt_mk (f : RS.Mero X) (p : X) {D E : RS.Divisor X}
    (hf : ((D p - E p : ℤ) : WithTop ℤ) ≤ f.ord p) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    mulIntoAt f p hf (TailAt.mk p D ψ) =
      TailAt.mk p E (RS.MeroGermOn.restrict (Set.subset_univ _) f * ψ) :=
  Submodule.mapQ_apply _ _ _ ψ

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [DecidableEq X] in
theorem mulIntoAt_surjective {f : RS.Mero X} (hf0 : f ≠ 0) [ConnectedSpace X] (p : X)
    {D E : RS.Divisor X} (hf : ((D p - E p : ℤ) : WithTop ℤ) ≤ f.ord p) :
    Function.Surjective (mulIntoAt f p hf) := by
  intro z
  obtain ⟨ψ', rfl⟩ := TailAt.mk_surjective p E z
  refine ⟨TailAt.mk p D (RS.MeroGermOn.restrict (Set.subset_univ _) f⁻¹ * ψ'), ?_⟩
  rw [mulIntoAt_mk, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hf0, map_one, one_mul]

/-- Miranda's `t ∘ μ_f : T D →ₗ T E`, uniform in `f` (linear in `f`, §3 D3). -/
noncomputable def mulInto (f : RS.Mero X) {D E : RS.Divisor X}
    (hf : ∀ p, ((D p - E p : ℤ) : WithTop ℤ) ≤ f.ord p) : T D →ₗ[ℂ] T E where
  toFun τ := DFinsupp.mapRange (fun p => mulIntoAt f p (hf p)) (fun _ => map_zero _) τ
  map_add' τ σ := by
    apply DFinsupp.ext
    intro p
    simp only [DFinsupp.add_apply, DFinsupp.mapRange_apply, map_add]
  map_smul' c τ := by
    apply DFinsupp.ext
    intro p
    simp only [DFinsupp.smul_apply, DFinsupp.mapRange_apply, map_smul, RingHom.id_apply]

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [DecidableEq X] in
theorem mulInto_apply (f : RS.Mero X) {D E : RS.Divisor X}
    (hf : ∀ p, ((D p - E p : ℤ) : WithTop ℤ) ≤ f.ord p) (τ : T D) (p : X) :
    mulInto f hf τ p = mulIntoAt f p (hf p) (τ p) :=
  DFinsupp.mapRange_apply (fun p => mulIntoAt f p (hf p)) (fun _ => map_zero _) τ p

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [DecidableEq X] in
theorem mulInto_add (f g : RS.Mero X) {D E : RS.Divisor X}
    (hf : ∀ p, ((D p - E p : ℤ) : WithTop ℤ) ≤ f.ord p)
    (hg : ∀ p, ((D p - E p : ℤ) : WithTop ℤ) ≤ g.ord p)
    (hfg : ∀ p, ((D p - E p : ℤ) : WithTop ℤ) ≤ (f + g).ord p) :
    mulInto (f + g) hfg = mulInto f hf + mulInto g hg := by
  apply LinearMap.ext
  intro τ
  apply DFinsupp.ext
  intro p
  simp only [LinearMap.add_apply, DFinsupp.add_apply, mulInto_apply]
  obtain ⟨ψ, hψ⟩ := TailAt.mk_surjective p D (τ p)
  rw [← hψ, mulIntoAt_mk, mulIntoAt_mk, mulIntoAt_mk,
    show RS.MeroGermOn.restrict (Set.subset_univ (chartAt ℂ p).source) (f + g)
        = RS.MeroGermOn.restrict (Set.subset_univ _) f + RS.MeroGermOn.restrict
            (Set.subset_univ _) g
      from map_add _ f g,
    add_mul, map_add]

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [DecidableEq X] in
theorem mulInto_smul (c : ℂ) (f : RS.Mero X) {D E : RS.Divisor X}
    (hf : ∀ p, ((D p - E p : ℤ) : WithTop ℤ) ≤ f.ord p)
    (hcf : ∀ p, ((D p - E p : ℤ) : WithTop ℤ) ≤ (c • f).ord p) :
    mulInto (c • f) hcf = c • mulInto f hf := by
  apply LinearMap.ext
  intro τ
  apply DFinsupp.ext
  intro p
  simp only [LinearMap.smul_apply, DFinsupp.smul_apply, mulInto_apply]
  obtain ⟨ψ, hψ⟩ := TailAt.mk_surjective p D (τ p)
  rw [← hψ, mulIntoAt_mk, mulIntoAt_mk,
    show RS.MeroGermOn.restrict (Set.subset_univ (chartAt ℂ p).source) (c • f)
        = c • RS.MeroGermOn.restrict (Set.subset_univ _) f from map_smul _ c f,
    smul_mul_assoc, map_smul]

theorem mulInto_alpha [CompactSpace X] [ConnectedSpace X] (f : RS.Mero X)
    {D E : RS.Divisor X} (hf : ∀ p, ((D p - E p : ℤ) : WithTop ℤ) ≤ f.ord p) (g : RS.Mero X) :
    mulInto f hf (alphaL D g) = alphaL E (f * g) := by
  apply DFinsupp.ext
  intro p
  rw [mulInto_apply]
  change mulIntoAt f p (hf p) (alpha D g p) = alpha E (f * g) p
  rw [alpha_apply, mulIntoAt_mk, ← map_mul, alpha_apply]

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [DecidableEq X] in
theorem mulInto_surjective {f : RS.Mero X} (hf0 : f ≠ 0) [ConnectedSpace X] {D E : RS.Divisor X}
    (hf : ∀ p, ((D p - E p : ℤ) : WithTop ℤ) ≤ f.ord p) :
    Function.Surjective (mulInto f hf) :=
  (DFinsupp.mapRange_surjective (fun p => mulIntoAt f p (hf p)) (fun _ => map_zero _)).mpr
    (fun p => mulIntoAt_surjective hf0 p (hf p))

/-! ### `LinSys`/`Mero.ord` bookkeeping helpers -/

omit [DecidableEq X] in
theorem LinSys.divisor_ge [ConnectedSpace X] {C : RS.Divisor X} {f : RS.Mero X}
    (hf : f ∈ RS.LinSys C) (hf0 : f ≠ 0) (p : X) : -(C p) ≤ RS.divisor f p := by
  have h := RS.mem_linSys_iff.mp hf p
  rw [RS.divisor_apply]
  exact WithTop.untop₀_le_untop₀ (Mero.ord_ne_top hf0 p) h

omit [DecidableEq X] in
theorem Mero.ord_eq_divisor [ConnectedSpace X] {f : RS.Mero X} (hf : f ≠ 0) (p : X) :
    f.ord p = ((RS.divisor f p : ℤ) : WithTop ℤ) := by
  rw [RS.divisor_apply, WithTop.coe_untop₀_of_ne_top (Mero.ord_ne_top hf p)]

/-! ### `nuL` -/

omit [T2Space X] [IsManifold 𝓘(ℂ, ℂ) ω X] [DecidableEq X] in
theorem nu_bound (A C : RS.Divisor X) (f : ↥(RS.LinSys C)) (p : X) :
    (((A - C) p - A p : ℤ) : WithTop ℤ) ≤ (f : RS.Mero X).ord p := by
  have h := RS.mem_linSys_iff.mp f.2 p
  have heq : (A - C) p - A p = -(C p) := by rw [RS.Divisor.sub_apply]; ring
  rw [heq]
  exact h

/-- Miranda's `μ_f` packaged uniformly across `f ∈ L(C)` into the FIXED target `T A`
(the key linearity-restoring trick, §3 D3). -/
noncomputable def nuL (A C : RS.Divisor X) [ConnectedSpace X] :
    ↥(RS.LinSys C) →ₗ[ℂ] (T (A - C) →ₗ[ℂ] T A) where
  toFun f := mulInto (f : RS.Mero X) (nu_bound A C f)
  map_add' f g := mulInto_add (f : RS.Mero X) (g : RS.Mero X) (nu_bound A C f) (nu_bound A C g)
    (nu_bound A C (f + g))
  map_smul' c f := mulInto_smul c (f : RS.Mero X) (nu_bound A C f) (nu_bound A C (c • f))

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [DecidableEq X] in
theorem nuL_apply (A C : RS.Divisor X) [ConnectedSpace X]
    (f : ↥(RS.LinSys C)) : nuL A C f = mulInto (f : RS.Mero X) (nu_bound A C f) := rfl

theorem nuL_alpha (A C : RS.Divisor X) [CompactSpace X] [ConnectedSpace X]
    (f : ↥(RS.LinSys C)) (g : RS.Mero X) :
    nuL A C f (alphaL (A - C) g) = alphaL A ((f : RS.Mero X) * g) := by
  rw [nuL_apply, mulInto_alpha]

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [DecidableEq X] in
theorem nuL_surjective (A C : RS.Divisor X) [ConnectedSpace X]
    {f : ↥(RS.LinSys C)} (hf0 : (f : RS.Mero X) ≠ 0) : Function.Surjective (nuL A C f) := by
  rw [nuL_apply]
  exact mulInto_surjective hf0 (nu_bound A C f)

omit [DecidableEq X] in
theorem sub_divisor_le (A C : RS.Divisor X) [ConnectedSpace X]
    {f : ↥(RS.LinSys C)} (hf0 : (f : RS.Mero X) ≠ 0) :
    A - C - RS.divisor (f : RS.Mero X) ≤ A := by
  rw [Function.locallyFinsuppWithin.le_def]
  intro p
  rw [RS.Divisor.sub_apply, RS.Divisor.sub_apply]
  -- Routed through a divisor-free arithmetic helper: `omega` was observed to desync its atom
  -- detection when a fact about `RS.divisor (f:ℳX) p` derived via a separate `have`/lemma call is
  -- combined directly with a freshly-elaborated occurrence of the same term in the goal (both
  -- correct and defeq, but not syntactically merged by `omega`'s atom collection under
  -- `[DecidableEq X]` + `open scoped Classical`, confirmed by a targeted spike). `apply` unifies
  -- `d` against the goal's OWN term instead of retyping it, sidestepping the desync.
  have key : ∀ d : ℤ, -(C p) ≤ d → A p - C p - d ≤ A p := fun d hd => by omega
  apply key
  have h := RS.mem_linSys_iff.mp f.2 p
  rw [RS.divisor_apply]
  exact WithTop.untop₀_le_untop₀ (RS.Mero.ord_ne_top hf0 p) h

omit [DecidableEq X] in
/-- The `μ_{1/f}` inversion identity (endgame step): inverting `f` and truncating recovers the
plain truncation. -/
theorem nuL_mulInto_inv (A C : RS.Divisor X) [ConnectedSpace X]
    {f : ↥(RS.LinSys C)} (hf0 : (f : RS.Mero X) ≠ 0)
    (hinv : ∀ p, (((A - C - RS.divisor (f : RS.Mero X)) p - (A - C) p : ℤ) : WithTop ℤ)
      ≤ (f : RS.Mero X)⁻¹.ord p)
    (τ' : T (A - C - RS.divisor (f : RS.Mero X))) :
    nuL A C f (mulInto (f : RS.Mero X)⁻¹ hinv τ') =
      truncT (sub_divisor_le A C hf0 : A - C - RS.divisor (f : RS.Mero X) ≤ A) τ' := by
  apply DFinsupp.ext
  intro p
  rw [nuL_apply, mulInto_apply, mulInto_apply, truncT_apply]
  obtain ⟨ψ, hψ⟩ := TailAt.mk_surjective p (A - C - RS.divisor (f : RS.Mero X)) (τ' p)
  rw [← hψ, mulIntoAt_mk, mulIntoAt_mk, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hf0, map_one,
    one_mul, truncAt_mk]

end RS.TailDuality
