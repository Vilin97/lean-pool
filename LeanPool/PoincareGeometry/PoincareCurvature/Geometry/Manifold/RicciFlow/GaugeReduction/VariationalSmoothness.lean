/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

/-
Smoothness building blocks for the variational/flow-regularity bootstrap toward
smooth dependence of ODE flows on the initial condition (roadmap point 4, Item 2).

The flow `Φ` of a `C^{n}` field `f` has spatial Jacobian `DΦ` solving the
*variational equation*, whose vector field is `w(z) = (f z.1, (Df z.1).comp z.2)`
on the augmented space `V × (V →L[ℝ] V)`. Since `Df = fderiv f` is `C^{n-1}`, the
variational field is `C^{n-1}`; applying the first-order smooth-dependence result to
it raises the flow's regularity by one. Iterating bootstraps `C¹ → C³`.

These lemmas supply the smoothness facts that drive that recursion:

* `contDiff_clm_comp` — the composition of two `C^n` operator-valued maps is `C^n`;
* `contDiff_variationalField` — the variational field inherits `C^n` from `f` and `Df`;
* `contDiff_fderiv_of_contDiff_succ` — the regularity drop `f ∈ C^{n+1} ⟹ fderiv f ∈ C^n`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Operator.Prod

/-! # Variational Smoothness -/

open scoped Topology
open Set

namespace PoincareCurvature.VariationalSmoothness

/-- The composition of two `C^n` continuous-linear-map-valued maps is `C^n`. This is
the load-bearing smoothness fact for the variational field's linear second
component. -/
theorem contDiff_clm_comp {𝕜 X U V W : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    {n : WithTop ℕ∞} {g : X → (V →L[𝕜] W)} {h : X → (U →L[𝕜] V)}
    (hg : ContDiff 𝕜 n g) (hh : ContDiff 𝕜 n h) :
    ContDiff 𝕜 n (fun x => (g x).comp (h x)) :=
  hg.clm_comp hh

/-- **The variational vector field inherits `C^n` smoothness.** The augmented field
`z ↦ (f z.1, (Df z.1).comp z.2)` on `V × (V →L[ℝ] V)` is `C^n` whenever `f` and `Df`
are. In the flow bootstrap one applies this with `Df = fderiv f` (which is `C^{n-1}`
when `f` is `C^n`), so the variational field is `C^{n-1}`. -/
theorem contDiff_variationalField {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : WithTop ℕ∞} {f : V → V} {Df : V → (V →L[ℝ] V)}
    (hf : ContDiff ℝ n f) (hDf : ContDiff ℝ n Df) :
    ContDiff ℝ n (fun z : V × (V →L[ℝ] V) => (f z.1, (Df z.1).comp z.2)) := by
  refine ContDiff.prodMk ?_ ?_
  · exact hf.comp contDiff_fst
  · exact (hDf.comp contDiff_fst).clm_comp contDiff_snd

/-- **Regularity drop.** The Fréchet derivative of a `C^{n+1}` map is `C^n`. This is
what makes `Df = fderiv f` available at level `n-1` when `f` is `C^n`, supplying the
input to `contDiff_variationalField` at each rung of the bootstrap. -/
theorem contDiff_fderiv_of_contDiff_succ {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} {f : V → V} (hf : ContDiff ℝ (n + 1 : ℕ) f) :
    ContDiff ℝ (n : ℕ) (fun x => fderiv ℝ f x) := by
  have hf' : ContDiff ℝ ((n : WithTop ℕ∞) + 1) f := by
    rwa [show ((n : WithTop ℕ∞) + 1) = ((n + 1 : ℕ) : WithTop ℕ∞) by push_cast; ring]
  exact (contDiff_succ_iff_fderiv.mp hf').2.2

/-- The variational field built from `f` and its own derivative `fderiv f` is `C^n`
when `f` is `C^{n+1}` — the precise per-rung statement of the bootstrap recursion. -/
theorem contDiff_variationalField_fderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} {f : V → V} (hf : ContDiff ℝ (n + 1 : ℕ) f) :
    ContDiff ℝ (n : ℕ) (fun z : V × (V →L[ℝ] V) => (f z.1, (fderiv ℝ f z.1).comp z.2)) :=
  contDiff_variationalField (hf.of_le (by exact_mod_cast Nat.le_succ n))
    (contDiff_fderiv_of_contDiff_succ hf)

/-- **Spatial differentiability of the prolongation field.** The variational
(prolongation) vector field `w(a, B) = (f a, (Df a) ∘ B)` on the augmented space
`V × (V →L[ℝ] V)` is Fréchet-differentiable at `(a, B)` whenever `f` is differentiable
at `a` (with derivative `Df a`) and `Df` is itself differentiable at `a` (with
derivative `D2f a`). The augmented Picard-Lindelöf construction at the next bootstrap
rung needs precisely this — that the prolonged field has a spatial derivative — and
mathlib has no lemma for it. Only existence is exposed; the operator is synthesised by
`prodMk`/`clm_comp`. -/
theorem hasFDerivAt_prolongationField {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → V} {Df : V → (V →L[ℝ] V)} {D2f : V → (V →L[ℝ] (V →L[ℝ] V))}
    {a : V} {B : V →L[ℝ] V}
    (hf : HasFDerivAt f (Df a) a) (hDf : HasFDerivAt Df (D2f a) a) :
    ∃ D : (V × (V →L[ℝ] V)) →L[ℝ] (V × (V →L[ℝ] V)),
      HasFDerivAt
        (fun z : V × (V →L[ℝ] V) => (f z.1, (Df z.1).comp z.2)) D (a, B) := by
  have h1 : HasFDerivAt (fun z : V × (V →L[ℝ] V) => f z.1)
      ((Df a).comp (ContinuousLinearMap.fst ℝ V (V →L[ℝ] V))) (a, B) :=
    HasFDerivAt.comp (a, B) hf hasFDerivAt_fst
  have hg : HasFDerivAt (fun z : V × (V →L[ℝ] V) => Df z.1)
      ((D2f a).comp (ContinuousLinearMap.fst ℝ V (V →L[ℝ] V))) (a, B) :=
    HasFDerivAt.comp (a, B) hDf hasFDerivAt_fst
  have hh : HasFDerivAt (fun z : V × (V →L[ℝ] V) => z.2)
      (ContinuousLinearMap.snd ℝ V (V →L[ℝ] V)) (a, B) :=
    hasFDerivAt_snd
  exact ⟨_, HasFDerivAt.prodMk h1 (HasFDerivAt.clm_comp hg hh)⟩

/-! ### The smooth-dependence bootstrap engine

These lemmas assemble into the recursion that proves the ODE flow map is spatially
`C^k`. The structure: the base flow paired with its Jacobian is the flow of the
augmented variational field on `V × (V →L V)`; if that augmented flow is `C^n`, its
second-component projection (the Jacobian) is `C^n`, and a flow that is differentiable
everywhere with a `C^n` Jacobian is `C^{n+1}`. Recursing from the `C¹` base case
(the variational equation, supplied by the project's variational layer) bootstraps to
any finite order. -/

/-- **C¹ packaging.** A map that is Fréchet-differentiable everywhere with a
*continuous* derivative is `C¹`. This is precisely the bridge from the project's
existing `HasFDerivAt`-of-the-flow-slice + continuous-tangent results to a `ContDiff 1`
statement the induction can consume. -/
theorem contDiff_one_of_hasFDerivAt_continuous {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : V → W} {g' : V → (V →L[ℝ] W)}
    (hderiv : ∀ x, HasFDerivAt g (g' x) x) (hcont : Continuous g') :
    ContDiff ℝ 1 g := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (hderiv x).differentiableAt, ?_⟩
  have hfd : fderiv ℝ g = g' := funext fun x => (hderiv x).fderiv
  rw [hfd]
  exact hcont

/-- The Jacobian (second component of the augmented flow from initial data `(x, 1)`)
inherits the augmented flow's `C^n` smoothness. -/
theorem jacobian_contDiff_of_augmented_flow_contDiff {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    {n : WithTop ℕ∞} {Ψ : (V × (V →L[ℝ] V)) → ℝ → (V × (V →L[ℝ] V))} {t : ℝ}
    (hΨ : ContDiff ℝ n (fun z : V × (V →L[ℝ] V) => Ψ z t)) :
    ContDiff ℝ n (fun x : V => (Ψ (x, (1 : V →L[ℝ] V)) t).2) :=
  contDiff_snd.comp (hΨ.comp (ContDiff.prodMk contDiff_id contDiff_const))

/-- The base flow (first component of the augmented flow from initial data `(x, 1)`)
inherits the augmented flow's `C^n` smoothness. -/
theorem baseFlow_contDiff_of_augmented_flow_contDiff {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    {n : WithTop ℕ∞} {Ψ : (V × (V →L[ℝ] V)) → ℝ → (V × (V →L[ℝ] V))} {t : ℝ}
    (hΨ : ContDiff ℝ n (fun z : V × (V →L[ℝ] V) => Ψ z t)) :
    ContDiff ℝ n (fun x : V => (Ψ (x, (1 : V →L[ℝ] V)) t).1) :=
  contDiff_fst.comp (hΨ.comp (ContDiff.prodMk contDiff_id contDiff_const))

/-- **The bootstrap inductive step.** A map that is Fréchet-differentiable everywhere
with a `C^n` derivative is `C^{n+1}`. Applied with `g = x ↦ Φ_t x` and `Dg = ` the
variational Jacobian (which is `C^n` by the augmented-flow recursion), this raises the
flow's spatial regularity by one — the reusable engine of the smooth-dependence
bootstrap. -/
theorem flow_contDiff_succ_of_jacobian_contDiff {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    {n : ℕ} {g : V → V} {Dg : V → (V →L[ℝ] V)}
    (hderiv : ∀ x, HasFDerivAt g (Dg x) x)
    (hjac : ContDiff ℝ (n : WithTop ℕ∞) Dg) :
    ContDiff ℝ ((n : WithTop ℕ∞) + 1) g := by
  have hdiff : Differentiable ℝ g := fun x => (hderiv x).differentiableAt
  have hfd : fderiv ℝ g = Dg := by funext x; exact (hderiv x).fderiv
  rw [contDiff_succ_iff_fderiv]
  refine ⟨hdiff, ?_, ?_⟩
  · intro hω; exact absurd hω (by exact_mod_cast (WithTop.natCast_ne_top n))
  · rw [hfd]; exact hjac

/-- **The full bootstrap step, assembled.** If the base flow `g` is differentiable
everywhere with Jacobian `Dg` equal to the second-component projection of a `C^n`
augmented flow `Ψ`, then `g` is `C^{n+1}`. This composes the projection lemma with the
inductive step: it reduces "flow `C^{n+1}`" to "augmented flow `C^n`", which the next
rung of the recursion (or the `C¹` base case) supplies. -/
theorem flow_contDiff_succ_of_augmented_flow_contDiff {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    {n : ℕ} {g : V → V} {Ψ : (V × (V →L[ℝ] V)) → ℝ → (V × (V →L[ℝ] V))} {t : ℝ}
    (hderiv : ∀ x, HasFDerivAt g ((Ψ (x, (1 : V →L[ℝ] V)) t).2) x)
    (hΨ : ContDiff ℝ (n : WithTop ℕ∞) (fun z : V × (V →L[ℝ] V) => Ψ z t)) :
    ContDiff ℝ ((n : WithTop ℕ∞) + 1) g :=
  flow_contDiff_succ_of_jacobian_contDiff hderiv
    (jacobian_contDiff_of_augmented_flow_contDiff hΨ)

/-! ### Local (`ContDiffOn`) bootstrap on open sets

The project's ODE flow is regular only on a Picard cylinder (a closed ball in space
times a time interval), so its variational outputs are *local*: `HasFDerivAt` at
points of a ball with a `ContinuousOn` tangent. These `ContDiffOn`/open-set versions
of the bootstrap engine match that exactly, so they are the forms that wire the
abstract recursion into `ModelGaugeFlowODE`'s ball-local results. -/

/-- **Local C¹ packaging on an open set.** A map with `HasFDerivAt` at every point of
an open set `s` and a `ContinuousOn` derivative is `ContDiffOn 1` on `s`. -/
theorem contDiffOn_one_of_hasFDerivAt_continuousOn_isOpen {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : V → W} {g' : V → (V →L[ℝ] W)} {s : Set V} (hs : IsOpen s)
    (hderiv : ∀ x ∈ s, HasFDerivAt g (g' x) x) (hcont : ContinuousOn g' s) :
    ContDiffOn ℝ 1 g s := by
  have hfeq : ∀ x ∈ s, fderiv ℝ g x = g' x := fun x hx => (hderiv x hx).fderiv
  have hone : (1 : WithTop ℕ∞) = (0 : WithTop ℕ∞) + 1 := by norm_num
  rw [hone, contDiffOn_succ_iff_fderiv_of_isOpen hs]
  refine ⟨fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · intro h
    exact absurd h (by simp)
  · rw [contDiffOn_zero]
    exact hcont.congr hfeq

/-- **Local inductive step on an open set.** A map with `HasFDerivAt` at every point of
an open set `s` and a `ContDiffOn n` Jacobian is `ContDiffOn (n+1)` on `s`. -/
theorem contDiffOn_succ_of_jacobian_contDiffOn_isOpen {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    {n : ℕ} {g : V → V} {Dg : V → (V →L[ℝ] V)} {s : Set V} (hs : IsOpen s)
    (hderiv : ∀ x ∈ s, HasFDerivAt g (Dg x) x)
    (hjac : ContDiffOn ℝ (n : WithTop ℕ∞) Dg s) :
    ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) g s := by
  rw [contDiffOn_succ_iff_fderiv_of_isOpen hs]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact ((hderiv x hx).differentiableAt).differentiableWithinAt
  · intro htop
    exact absurd htop (WithTop.natCast_ne_top n)
  · refine hjac.congr ?_
    intro x hx
    exact (hderiv x hx).fderiv

/-- **Local Jacobian projection.** If the augmented flow's time-`t` slice is
`ContDiffOn n` on `S` and the embedding `x ↦ (x, 1)` maps `s` into `S`, then the
Jacobian `x ↦ (Ψ (x,1) t).2` is `ContDiffOn n` on `s`. -/
theorem jacobian_contDiffOn_of_augmented_flow_contDiffOn {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    {n : WithTop ℕ∞} {Ψ : (V × (V →L[ℝ] V)) → ℝ → (V × (V →L[ℝ] V))} {t : ℝ}
    {S : Set (V × (V →L[ℝ] V))} {s : Set V}
    (hΨ : ContDiffOn ℝ n (fun z : V × (V →L[ℝ] V) => Ψ z t) S)
    (hmaps : MapsTo (fun x : V => (x, (1 : V →L[ℝ] V))) s S) :
    ContDiffOn ℝ n (fun x : V => (Ψ (x, (1 : V →L[ℝ] V)) t).2) s := by
  have he : ContDiff ℝ n (fun x : V => (x, (1 : V →L[ℝ] V))) :=
    contDiff_id.prodMk contDiff_const
  have hcomp : ContDiffOn ℝ n (fun x : V => Ψ (x, (1 : V →L[ℝ] V)) t) s :=
    hΨ.comp (he.contDiffOn) hmaps
  exact contDiff_snd.comp_contDiffOn hcomp

/-- **The assembled local bootstrap step.** On an open set `s`, if the base flow `g`
has `HasFDerivAt` everywhere with Jacobian the second-component projection of a
`ContDiffOn n` augmented flow `Ψ` (whose embedding maps `s` into `S`), then `g` is
`ContDiffOn (n+1)` on `s`. This is the wiring-ready form: it reduces local "flow
`C^{n+1}`" to local "augmented flow `C^n`". -/
theorem contDiffOn_succ_of_augmented_flow_contDiffOn_isOpen {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    {n : ℕ} {g : V → V} {Ψ : (V × (V →L[ℝ] V)) → ℝ → (V × (V →L[ℝ] V))} {t : ℝ}
    {S : Set (V × (V →L[ℝ] V))} {s : Set V} (hs : IsOpen s)
    (hderiv : ∀ x ∈ s, HasFDerivAt g ((Ψ (x, (1 : V →L[ℝ] V)) t).2) x)
    (hmaps : MapsTo (fun x : V => (x, (1 : V →L[ℝ] V))) s S)
    (hΨ : ContDiffOn ℝ (n : WithTop ℕ∞) (fun z : V × (V →L[ℝ] V) => Ψ z t) S) :
    ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) g s :=
  contDiffOn_succ_of_jacobian_contDiffOn_isOpen hs hderiv
    (jacobian_contDiffOn_of_augmented_flow_contDiffOn hΨ hmaps)

/-- **Full augmented-flow `ContDiffOn` from its two projections.** A flow valued in a
product `P × Q` is `ContDiffOn n` exactly when both component projections are. This is the
bridge that lets a bootstrap recursion track the *full* augmented flow `(base, tangent)`
through the tower (rather than just the base projection): the smoothness of the whole is
the `prodMk` of the smoothness of its parts. -/
theorem contDiffOn_prod_of_components {X P Q : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {n : WithTop ℕ∞} {F : X → P × Q} {s : Set X}
    (h1 : ContDiffOn ℝ n (fun z => (F z).1) s)
    (h2 : ContDiffOn ℝ n (fun z => (F z).2) s) :
    ContDiffOn ℝ n F s := by
  have := h1.prodMk h2
  simpa using this

/-- **The spatial-`C³` capstone.** Point 4 needs the gauge flow to be spatially `C³`,
which is exactly *two* rungs of the augmented-flow bootstrap above the `C¹` base case.

Concretely: the base flow `g0` (on `s0`) has Jacobian the second projection of the
level-0 augmented flow `Ψ0` (on `S0`); `Ψ0`'s own slice has Jacobian the second
projection of the level-1 augmented flow `Ψ1` (on `S1`); and `Ψ1`'s slice is `C¹`
(the variational base case). Applying the local rung lemma twice — first lifting the
`C¹` base of `Ψ1` to a `C²` slice of `Ψ0`, then lifting that to a `C³` `g0` — yields
spatial `C³`. The rung lemma is generic in the model space, so it instantiates cleanly
at both augmented levels. -/
theorem contDiffOn_three_of_augmented_tower {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    {t : ℝ} {g0 : V → V}
    {Ψ0 : (V × (V →L[ℝ] V)) → ℝ → (V × (V →L[ℝ] V))}
    {Ψ1 : ((V × (V →L[ℝ] V)) × ((V × (V →L[ℝ] V)) →L[ℝ] (V × (V →L[ℝ] V)))) → ℝ →
      ((V × (V →L[ℝ] V)) × ((V × (V →L[ℝ] V)) →L[ℝ] (V × (V →L[ℝ] V))))}
    {s0 : Set V} {S0 : Set (V × (V →L[ℝ] V))}
    {S1 : Set ((V × (V →L[ℝ] V)) × ((V × (V →L[ℝ] V)) →L[ℝ] (V × (V →L[ℝ] V))))}
    (hs0 : IsOpen s0) (hS0 : IsOpen S0)
    (hderiv0 : ∀ x ∈ s0, HasFDerivAt g0 ((Ψ0 (x, (1 : V →L[ℝ] V)) t).2) x)
    (hmaps0 : MapsTo (fun x : V => (x, (1 : V →L[ℝ] V))) s0 S0)
    (hderiv1 : ∀ z ∈ S0,
      HasFDerivAt (fun w : V × (V →L[ℝ] V) => Ψ0 w t)
        ((Ψ1 (z, (1 : (V × (V →L[ℝ] V)) →L[ℝ] (V × (V →L[ℝ] V)))) t).2) z)
    (hmaps1 : MapsTo
      (fun z : V × (V →L[ℝ] V) =>
        (z, (1 : (V × (V →L[ℝ] V)) →L[ℝ] (V × (V →L[ℝ] V))))) S0 S1)
    (hbase : ContDiffOn ℝ 1 (fun w => Ψ1 w t) S1) :
    ContDiffOn ℝ 3 g0 s0 := by
  have h2 : ContDiffOn ℝ ((1 : ℕ) + 1) (fun w : V × (V →L[ℝ] V) => Ψ0 w t) S0 := by
    have hbase' : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞) (fun w => Ψ1 w t) S1 := by
      simpa using hbase
    exact contDiffOn_succ_of_augmented_flow_contDiffOn_isOpen hS0 hderiv1 hmaps1 hbase'
  have h2' : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) (fun w : V × (V →L[ℝ] V) => Ψ0 w t) S0 := by
    convert h2 using 1 <;> norm_num
  have h3 : ContDiffOn ℝ ((2 : ℕ) + 1) g0 s0 :=
    contDiffOn_succ_of_augmented_flow_contDiffOn_isOpen hs0 hderiv0 hmaps0 h2'
  convert h3 using 1 <;> norm_num

end PoincareCurvature.VariationalSmoothness
