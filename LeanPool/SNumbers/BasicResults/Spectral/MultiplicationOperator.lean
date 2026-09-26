/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The multiplication operator `M_f` on `L²`

For an essentially bounded measurable scalar function `f : α → 𝕜` (i.e.
`MemLp f ⊤ μ`), pointwise multiplication `g ↦ f • g` is a bounded linear
operator on `L²(μ)`, the **multiplication operator** `M_f`. Its operator
norm is at most the essential supremum `‖f‖∞`.

*Why this file is here:* it is the seed of the **multiplication-operator** route to the spectral
theorem (Pietsch, *Operator Ideals*, §11.3 — represent `S*S` as `M_f` after a unitary change of
variables, and read off the spectral projection as `M_{𝟙}`). That route is **not** used by the
current development: the spectral projection is instead built directly via the continuous
functional calculus (`Projection`) and complexification (`RealProjection`). This file is kept as a
self-contained, independently useful building block for a possible future multiplication-form
representation; nothing in the `s`-numbers chain depends on it.

## Main definitions

* `MeasureTheory.mulL2 f hf` — the multiplication operator
  `M_f : L²(μ) →L[𝕜] L²(μ)`, `g ↦ f • g`, for `hf : MemLp f ⊤ μ`.

## Main results

* `MeasureTheory.mulL2_coeFn` — `⇑(M_f g) =ᵐ[μ] f • ⇑g`, the defining a.e.
  identity (the workhorse for all algebraic properties).
* `MeasureTheory.mulL2_opNorm_le` — `‖M_f‖ ≤ (eLpNorm f ⊤ μ).toReal`.
* `MeasureTheory.mulL2_mul` — `M_f ∘ M_g = M_{f g}` (multiplicativity).
* `MeasureTheory.mulL2_one` — `M_1 = id` (unitality).
* `MeasureTheory.mulL2_isSelfAdjoint` — `M_f` is self-adjoint when `f` is
  real-valued; with `mulL2_mul` this makes an indicator multiplier `M_𝟙` an
  orthogonal projection.

Mathlib reuse: Hölder's inequality for `L^∞ · L²`
(`eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm`), the `MemLp.toLp` /
`MemLp.coeFn_toLp` interface to `Lp`, and `LinearMap.mkContinuous`.
-/

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory

namespace MeasureTheory

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The pointwise product `f • g` of an essentially bounded `f` with an
`L²` function `g` is again in `L²` (Hölder's inequality with exponents
`⊤, 2, 2`). -/
theorem memLp_mul_left {f : α → 𝕜} (hf : MemLp f ⊤ μ) (g : Lp 𝕜 2 μ) :
    MemLp (f • ⇑g) 2 μ :=
  lt_of_le_of_lt
      (eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm_of_pos 2 (by norm_num))
      (ENNReal.mul_lt_top hf (Lp.memLp g))

/-- The **multiplication operator** `M_f : L²(μ) →L[𝕜] L²(μ)`, `g ↦ f • g`,
for an essentially bounded measurable scalar function `f` (`hf : MemLp f ⊤ μ`). -/
noncomputable def mulL2 (f : α → 𝕜) (hf : MemLp f ⊤ μ) : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun g => (memLp_mul_left hf g).toLp (f • ⇑g)
      map_add' := fun g₁ g₂ => by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp (memLp_mul_left hf (g₁ + g₂)),
          Lp.coeFn_add ((memLp_mul_left hf g₁).toLp (f • ⇑g₁))
            ((memLp_mul_left hf g₂).toLp (f • ⇑g₂)),
          MemLp.coeFn_toLp (memLp_mul_left hf g₁),
          MemLp.coeFn_toLp (memLp_mul_left hf g₂),
          Lp.coeFn_add g₁ g₂] with x h1 h2 h3 h4 h5
        simp only [h1, h2, h3, h4, h5, Pi.smul_apply', Pi.add_apply, smul_add]
      map_smul' := fun c g => by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp (memLp_mul_left hf (c • g)),
          Lp.coeFn_smul c ((memLp_mul_left hf g).toLp (f • ⇑g)),
          MemLp.coeFn_toLp (memLp_mul_left hf g),
          Lp.coeFn_smul c g] with x h1 h2 h3 h4
        simp only [h1, h2, h3, h4, RingHom.id_apply, Pi.smul_apply, Pi.smul_apply']
        exact smul_comm (f x) c _ }
    ((eLpNorm f ⊤ μ).toReal)
    (fun g => by
      change ‖(memLp_mul_left hf g).toLp (f • ⇑g)‖ ≤ (eLpNorm f ⊤ μ).toReal * ‖g‖
      rw [Lp.norm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp (memLp_mul_left hf g))]
      calc (eLpNorm (f • ⇑g) 2 μ).toReal
          ≤ (eLpNorm f ⊤ μ * eLpNorm (⇑g) 2 μ).toReal :=
            ENNReal.toReal_mono (ENNReal.mul_lt_top hf (Lp.memLp g)).ne
              (eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm_of_pos 2 (by norm_num))
        _ = (eLpNorm f ⊤ μ).toReal * (eLpNorm (⇑g) 2 μ).toReal := ENNReal.toReal_mul
        _ = (eLpNorm f ⊤ μ).toReal * ‖g‖ := by rw [← Lp.norm_def])

/-- **Defining identity.** As an a.e. function, `M_f g` is `f • g`. -/
theorem mulL2_coeFn (f : α → 𝕜) (hf : MemLp f ⊤ μ) (g : Lp 𝕜 2 μ) :
    ⇑(mulL2 f hf g) =ᵐ[μ] f • ⇑g :=
  MemLp.coeFn_toLp (memLp_mul_left hf g)

/-- **Operator-norm bound.** `‖M_f‖ ≤ ‖f‖∞` (the essential supremum of `f`). -/
theorem mulL2_opNorm_le (f : α → 𝕜) (hf : MemLp f ⊤ μ) :
    ‖mulL2 f hf‖ ≤ (eLpNorm f ⊤ μ).toReal :=
  LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _

/-- The product of two essentially bounded functions is essentially bounded. -/
theorem memLp_mul_top {f g : α → 𝕜} (hf : MemLp f ⊤ μ) (hg : MemLp g ⊤ μ) :
    MemLp (f * g) ⊤ μ :=
  MemLp.mul hf hg

/-- **Multiplicativity.** `M_f ∘ M_g = M_{f g}`: multiplication operators
compose by multiplying their symbols. -/
theorem mulL2_mul (f g : α → 𝕜) (hf : MemLp f ⊤ μ) (hg : MemLp g ⊤ μ) :
    (mulL2 f hf).comp (mulL2 g hg) = mulL2 (f * g) (memLp_mul_top hf hg) := by
  refine ContinuousLinearMap.ext fun x => Lp.ext ?_
  simp only [ContinuousLinearMap.comp_apply]
  filter_upwards [mulL2_coeFn f hf (mulL2 g hg x), mulL2_coeFn g hg x,
    mulL2_coeFn (f * g) (memLp_mul_top hf hg) x] with a h1 h2 h3
  rw [h1, h3]
  simp only [Pi.smul_apply', Pi.mul_apply, h2, mul_smul]

/-- **Unitality.** `M_1` is the identity operator. -/
theorem mulL2_one (h1 : MemLp (1 : α → 𝕜) ⊤ μ) :
    mulL2 (1 : α → 𝕜) h1 = ContinuousLinearMap.id 𝕜 (Lp 𝕜 2 μ) := by
  refine ContinuousLinearMap.ext fun x => Lp.ext ?_
  filter_upwards [mulL2_coeFn (1 : α → 𝕜) h1 x] with a ha
  rw [ha]
  simp only [Pi.smul_apply', Pi.one_apply, one_smul, ContinuousLinearMap.id_apply]

/-- **Self-adjointness.** If the symbol `f` is real-valued (a.e. fixed by
complex conjugation), then `M_f` is self-adjoint. In particular an indicator
symbol gives a self-adjoint operator; together with `mulL2_mul`
(`M_𝟙 ∘ M_𝟙 = M_{𝟙·𝟙} = M_𝟙`) this makes `M_𝟙` an orthogonal projection.

The proof is the pointwise Hölder identity for the `L²` inner product:
`⟪f • x, y⟫ = ∫ conj(f) ⟪x, y⟫` and `⟪x, f • y⟫ = ∫ f ⟪x, y⟫`, equal when
`conj f = f`. -/
theorem mulL2_isSelfAdjoint (f : α → 𝕜) (hf : MemLp f ⊤ μ)
    (hreal : ∀ᵐ a ∂μ, (starRingEnd 𝕜) (f a) = f a) :
    IsSelfAdjoint (mulL2 f hf) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulL2_coeFn f hf x, mulL2_coeFn f hf y, hreal] with a hx hy hr
  rw [hx, hy]
  simp only [Pi.smul_apply']
  rw [inner_smul_left, inner_smul_right, hr]

end MeasureTheory

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
