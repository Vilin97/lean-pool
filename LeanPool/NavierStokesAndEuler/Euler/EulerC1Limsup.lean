/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerC1Breakdown
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Order.Filter.ENNReal

@[expose] public section

/-! Exact infinite upper limits at the maximal time. The endpoint filter
is the pullback of the ordinary left-neighborhood filter, so its meaning
does not depend on a chosen sequence of sampling times. -/

noncomputable section

namespace EulerOrdinarySobolev.FiniteLifespan

open Set Filter EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
open scoped Topology ENNReal

variable {A : SmoothL2Field Space} (L : FiniteLifespan A)

def endpointFilter : Filter L.Time :=
  Filter.comap (fun t : L.Time => (t : ℝ)) (𝓝[<] L.duration)

theorem endpointFilter_eq_atTop : L.endpointFilter=(atTop : Filter L.Time) :=
  comap_coe_nhdsLT_of_Ioo_subset (fun _ ht => ht.2)
    (fun _ => ⟨0,L.duration_pos,fun _ ht => ⟨ht.1.le,ht.2⟩⟩)

theorem map_time_atTop :
    Filter.map (fun t : L.Time => (t : ℝ)) atTop=𝓝[<] L.duration :=
  map_coe_atTop_of_Ioo_subset (fun _ ht => ht.2)
    (fun _ _ => ⟨0,L.duration_pos,fun _ ht => ⟨ht.1.le,ht.2⟩⟩)

theorem endpointFilter_neBot : L.endpointFilter.NeBot := by
  let : Nonempty L.Time := ⟨L.initialTime⟩
  rw [L.endpointFilter_eq_atTop]
  infer_instance

theorem time_tendsto_endpoint :
    Tendsto (fun t : L.Time => (t : ℝ)) atTop (𝓝[<] L.duration) :=
  L.map_time_atTop.le

/-- Arbitrarily large values in every terminal interval force the actual
extended nonnegative upper limit to be infinity. -/
theorem ofReal_limsup_eq_top_of_unbounded (f : L.Time → ℝ)
    (hf : ∀ τ : ℝ, τ < L.duration → ∀ K : ℝ, ∃ t : L.Time, τ < t ∧ K < f t) :
    Filter.limsup (fun t => ENNReal.ofReal (f t)) L.endpointFilter=⊤ := by
  let : Nonempty L.Time := ⟨L.initialTime⟩
  rw [L.endpointFilter_eq_atTop]
  apply top_unique
  apply (Filter.le_limsup_iff).2
  intro b hb
  apply frequently_atTop.mpr
  intro s
  obtain ⟨t,ht,hft⟩ := hf s s.property.2 b.toReal
  exact ⟨t,ht.le,(ENNReal.lt_ofReal_iff_toReal_lt (ne_of_lt hb)).mpr hft⟩

theorem maximalGradientNorm_limsup :
    Filter.limsup (fun t : L.Time => ENNReal.ofReal (L.maximalGradientNorm t))
      L.endpointFilter=⊤ :=
  L.ofReal_limsup_eq_top_of_unbounded L.maximalGradientNorm
    (fun τ hτ K => L.maximalGradientNorm_unbounded_near_endpoint τ K hτ)

theorem maximalC1Norm_limsup :
    Filter.limsup (fun t : L.Time => ENNReal.ofReal (L.maximalC1Norm t))
      L.endpointFilter=⊤ :=
  L.ofReal_limsup_eq_top_of_unbounded L.maximalC1Norm
    (fun τ hτ K => L.maximalC1Norm_unbounded_near_endpoint τ K hτ)

theorem maximalC1Norm_limsup_atTop :
    Filter.limsup (fun t : L.Time => ENNReal.ofReal (L.maximalC1Norm t)) atTop=⊤ := by
  rw [← L.endpointFilter_eq_atTop]
  exact L.maximalC1Norm_limsup

end EulerOrdinarySobolev.FiniteLifespan

namespace EulerPacketInduction

open Filter
open scoped Topology ENNReal

theorem maximalTime_map_atTop :
    Filter.map (fun t : MaximalTime => (t : ℝ)) atTop=𝓝[<] lifespan.duration :=
  lifespan.map_time_atTop

theorem maximalGradientNorm_limsup :
    Filter.limsup (fun t : MaximalTime => ENNReal.ofReal (maximalGradientNorm t))
      (Filter.comap (fun t : MaximalTime => (t : ℝ)) (𝓝[<] lifespan.duration))=⊤ :=
  lifespan.maximalGradientNorm_limsup

theorem maximalC1Norm_limsup :
    Filter.limsup (fun t : MaximalTime => ENNReal.ofReal (maximalC1Norm t))
      (Filter.comap (fun t : MaximalTime => (t : ℝ)) (𝓝[<] lifespan.duration))=⊤ :=
  lifespan.maximalC1Norm_limsup

end EulerPacketInduction
