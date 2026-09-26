/-
Copyright (c) 2026 Petr Girg, Petr Nečesal, Martin Dvořák, Jakub Psutka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Petr Girg, Petr Nečesal, Martin Dvořák, Jakub Psutka
-/

module

public import LeanPool.NemytskiiLebesgue.Caratheodory

/-!
# Nemytskii operators: Closure

Adapted from `madvorak/nemytskii-lebesgue` (Apache-2.0).
-/

public section

namespace NemytskiiLebesgue

open scoped NemytskiiLebesgue

open MeasureTheory _root_.Filter

theorem IsCaratheodory.const
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    (c : F) :
    IsCaratheodory (fun _ : Ω => fun _ : D => c) μ where
  isStronglyMeasurable _ := stronglyMeasurable_const
  ae_continuous := Eventually.of_forall ↓continuous_const

theorem IsCaratheodory.of_stronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {f : Ω → F} (hf : StronglyMeasurable f) :
    IsCaratheodory (fun ω : Ω => fun _ : D => f ω) μ where
  isStronglyMeasurable _ := hf
  ae_continuous := Eventually.of_forall ↓continuous_const

theorem IsCaratheodory.of_continuous
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {f : D → F} (hf : Continuous f) :
    IsCaratheodory (fun _ : Ω => fun x : D => f x) μ where
  isStronglyMeasurable _ := stronglyMeasurable_const
  ae_continuous := Eventually.of_forall ↓hf

theorem IsCaratheodory.add
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Add F] [ContinuousAdd F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : Ω → D → F} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f + g) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).add (hg.isStronglyMeasurable x)
  ae_continuous := by
    filter_upwards [hf.ae_continuous, hg.ae_continuous] with ω hfω hgω
    exact hfω.add hgω

theorem IsCaratheodory.real_add
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ^k} (hf : IsCaratheodory f μ)
    {g : Ω → D → ℝ^k} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f + g) μ :=
  hf.add hg

theorem IsCaratheodory.neg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Neg F] [ContinuousNeg F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ) :
    IsCaratheodory (-f) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).neg
  ae_continuous := by
    filter_upwards [hf.ae_continuous] with ω hω
    exact hω.neg

theorem IsCaratheodory.sub
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Sub F] [ContinuousSub F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : Ω → D → F} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f - g) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).sub (hg.isStronglyMeasurable x)
  ae_continuous := by
    filter_upwards [hf.ae_continuous, hg.ae_continuous] with ω hfω hgω
    exact hfω.sub hgω

theorem IsCaratheodory.real_sub
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ^k} (hf : IsCaratheodory f μ)
    {g : Ω → D → ℝ^k} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f - g) μ :=
  hf.sub hg

theorem IsCaratheodory.mul
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Mul F] [ContinuousMul F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : Ω → D → F} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f * g) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).mul (hg.isStronglyMeasurable x)
  ae_continuous := by
    filter_upwards [hf.ae_continuous, hg.ae_continuous] with ω hfω hgω
    exact hfω.mul hgω

theorem IsCaratheodory.real_mul
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ} (hf : IsCaratheodory f μ)
    {g : Ω → D → ℝ} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f * g) μ :=
  hf.mul hg

theorem IsCaratheodory.smul
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D] {M : Type*} [TopologicalSpace M]
    {F : Type*} [TopologicalSpace F]
    [SMul M F] [ContinuousSMul M F]
    {f : Ω → D → M} (hf : IsCaratheodory f μ)
    {g : Ω → D → F} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f • g) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).smul (hg.isStronglyMeasurable x)
  ae_continuous := by
    filter_upwards [hf.ae_continuous, hg.ae_continuous] with ω hfω hgω
    exact hfω.smul hgω

theorem IsCaratheodory.const_smul
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D] {M : Type*}
    {F : Type*} [TopologicalSpace F]
    [SMul M F] [ContinuousConstSMul M F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ) (c : M) :
    IsCaratheodory (c • f) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).const_smul c
  ae_continuous := by
    filter_upwards [hf.ae_continuous] with ω hω
    exact hω.const_smul c

theorem IsCaratheodory.inv
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Inv F] [ContinuousInv F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ) :
    IsCaratheodory (f⁻¹) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).inv
  ae_continuous := by
    filter_upwards [hf.ae_continuous] with ω hω
    exact hω.inv

theorem IsCaratheodory.div
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Div F] [ContinuousDiv F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : Ω → D → F} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f / g) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).div' (hg.isStronglyMeasurable x)
  ae_continuous := by
    filter_upwards [hf.ae_continuous, hg.ae_continuous] with ω hfω hgω
    exact hfω.div' hgω

theorem IsCaratheodory.real_div
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ} (hf : IsCaratheodory f μ)
    {g : Ω → D → ℝ} (hg : IsCaratheodory g μ)
    (hg0 : ∀ᵐ ω ∂μ, ∀ x : D, g ω x ≠ 0) :
    IsCaratheodory (f / g) μ where
  isStronglyMeasurable x :=
    ((hf.isStronglyMeasurable x).measurable.div
      (hg.isStronglyMeasurable x).measurable).stronglyMeasurable
  ae_continuous := by
    filter_upwards [hf.ae_continuous, hg.ae_continuous, hg0] with ω hcf hcg hne
    exact hcf.div hcg hne

theorem IsCaratheodory.pow_nat
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Monoid F] [ContinuousMul F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ) (n : ℕ) :
    IsCaratheodory (f ^ n) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).pow n
  ae_continuous := by
    filter_upwards [hf.ae_continuous] with ω hω
    exact hω.pow n

theorem IsCaratheodory.real_pow_nat
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ} (hf : IsCaratheodory f μ) (n : ℕ) :
    IsCaratheodory (f ^ n) μ :=
  hf.pow_nat n

theorem IsCaratheodory.sup
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Max F] [ContinuousSup F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : Ω → D → F} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f ⊔ g) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).sup (hg.isStronglyMeasurable x)
  ae_continuous := by
    filter_upwards [hf.ae_continuous, hg.ae_continuous] with ω hfω hgω
    exact hfω.sup hgω

theorem IsCaratheodory.real_sup
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ} (hf : IsCaratheodory f μ)
    {g : Ω → D → ℝ} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f ⊔ g) μ :=
  hf.sup hg

theorem IsCaratheodory.inf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    [Min F] [ContinuousInf F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : Ω → D → F} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f ⊓ g) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).inf (hg.isStronglyMeasurable x)
  ae_continuous := by
    filter_upwards [hf.ae_continuous, hg.ae_continuous] with ω hfω hgω
    exact hfω.inf hgω

theorem IsCaratheodory.real_inf
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ} {D : Set ℝ^m}
    {f : Ω → D → ℝ} (hf : IsCaratheodory f μ)
    {g : Ω → D → ℝ} (hg : IsCaratheodory g μ) :
    IsCaratheodory (f ⊓ g) μ :=
  hf.inf hg

theorem IsCaratheodory.comp_continuous
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {G : Type*} [TopologicalSpace G]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : F → G} (hg : Continuous g) :
    IsCaratheodory (g <| f · ·) μ where
  isStronglyMeasurable x :=
    hg.comp_stronglyMeasurable (hf.isStronglyMeasurable x)
  ae_continuous := by
    filter_upwards [hf.ae_continuous] with ω hω
    exact hg.comp hω

theorem IsCaratheodory.comp_measurePreserving
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {μ' : Measure Ω'}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : Ω' → Ω} (hg : MeasurePreserving g μ' μ) :
    IsCaratheodory (f ∘ g) μ' where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).comp_measurable hg.measurable
  ae_continuous :=
    hg.quasiMeasurePreserving.ae hf.ae_continuous

theorem IsCaratheodory.norm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ) :
    IsCaratheodory (‖f · ·‖) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).norm
  ae_continuous := by
    filter_upwards [hf.ae_continuous] with ω hω
    exact hω.norm

theorem IsCaratheodory.nnnorm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ) :
    IsCaratheodory (‖f · ·‖₊) μ where
  isStronglyMeasurable x :=
    (hf.isStronglyMeasurable x).nnnorm
  ae_continuous := by
    filter_upwards [hf.ae_continuous] with ω hω
    exact hω.nnnorm

theorem IsCaratheodory.prod
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {G : Type*} [TopologicalSpace G]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {g : Ω → D → G} (hg : IsCaratheodory g μ) :
    IsCaratheodory (fun ω : Ω => fun x : D => (f ω x, g ω x)) μ where
  isStronglyMeasurable x :=
    StronglyMeasurable.prodMk
      (hf.isStronglyMeasurable x)
      (hg.isStronglyMeasurable x)
  ae_continuous := by
    filter_upwards [hf.ae_continuous, hg.ae_continuous] with ω hfω hgω
    exact Continuous.prodMk hfω hgω

theorem IsCaratheodory.fst
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {G : Type*} [TopologicalSpace G]
    {f : Ω → D → F × G} (hf : IsCaratheodory f μ) :
    IsCaratheodory (fun ω : Ω => fun x : D => (f ω x).fst) μ :=
  hf.comp_continuous continuous_fst

theorem IsCaratheodory.snd
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F]
    {G : Type*} [TopologicalSpace G]
    {f : Ω → D → F × G} (hf : IsCaratheodory f μ) :
    IsCaratheodory (fun ω : Ω => fun x : D => (f ω x).snd) μ :=
  hf.comp_continuous continuous_snd

end NemytskiiLebesgue
