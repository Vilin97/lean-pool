/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredNormie3Contract
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TJetsDatum
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesCutoff
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTiny
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTwistie1
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredTwistie4
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredTwistie5
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.MeanZero
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.R46Source

/-! # Closing datum source producers with the proved T jets -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section5.Contracts
open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration

/-- Exact datum producer, with every jet input discharged. -/
theorem cutoff1Source_datum_closed_contract (β Ccut : ℝ) :
    ∃ C C₁ : ℝ, OnA7Instances β Ccut C₁
      (fun I _Φ hΦ κ M _R θ₀ m _θprev T =>
        Cutoff1SourceContract I hΦ m (I.kappaSeq κ M m) T C
          (Real.sqrt (l2NormSq θ₀))) := by
  obtain ⟨A, Cj, hA, hjets⟩ := tJets_datum_contract β Ccut
  obtain ⟨C, _, Cs, hsource⟩ := cutoff1Source_contract β Ccut A (zero_le_one.trans hA)
  refine ⟨C, max Cj Cs, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θprev T hθ hT
  have hj := hjets I hz hx hh ((le_max_left _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp
      hmean ha m hm hmM θprev T hθ hT
  exact hsource I hz hx hh ((le_max_right _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean
      ha m hm hmM θprev T hθ hT
    (Real.sqrt (l2NormSq θ₀)) (Real.sqrt_nonneg _) hj.1

/-- Exact datum producer, with every jet input discharged. -/
theorem twistie3Source_datum_closed_contract (β Ccut : ℝ) :
    ∃ C C₁ : ℝ, OnA7Instances β Ccut C₁
      (fun I _Φ hΦ κ M _R θ₀ m _θprev T =>
        Twistie3SourceContract I hΦ m (I.kappaSeq κ M m) T C
          (Real.sqrt (l2NormSq θ₀))) := by
  obtain ⟨A, Cj, hA, hjets⟩ := tJets_datum_contract β Ccut
  obtain ⟨C, _, Cs, hsource⟩ := twistie3Source_contract β Ccut A (zero_le_one.trans hA)
  refine ⟨C, max Cj Cs, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θprev T hθ hT
  have hj := hjets I hz hx hh ((le_max_left _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp
      hmean ha m hm hmM θprev T hθ hT
  exact hsource I hz hx hh ((le_max_right _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean
      ha m hm hmM θprev T hθ hT
    (Real.sqrt (l2NormSq θ₀)) (Real.sqrt_nonneg _) hj.1

/-- Exact datum producer, with every jet input discharged. -/
theorem normie1Source_datum_closed_contract (β Ccut : ℝ) :
    ∃ C C₁ : ℝ, OnA7Instances β Ccut C₁
      (fun I _Φ hΦ κ M _R θ₀ m _θprev T =>
        Normie1SourceContract I hΦ m (I.kappaSeq κ M m) T C
          (Real.sqrt (l2NormSq θ₀))) := by
  obtain ⟨A, Cj, hA, hjets⟩ := tJets_datum_contract β Ccut
  obtain ⟨C, _, Cs, hsource⟩ := normie1Source_contract β Ccut A (zero_le_one.trans hA)
  refine ⟨C, max Cj Cs, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θprev T hθ hT
  have hj := hjets I hz hx hh ((le_max_left _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp
      hmean ha m hm hmM θprev T hθ hT
  exact hsource I hz hx hh ((le_max_right _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean
      ha m hm hmM θprev T hθ hT
    (Real.sqrt (l2NormSq θ₀)) (Real.sqrt_nonneg _) hj.2.2.1 hj.1

/-- Exact datum producer, with every jet input discharged. -/
theorem twistie4CenteredSource_datum_closed_contract (β Ccut : ℝ) :
    ∃ C C₁ : ℝ, OnA7Instances β Ccut C₁
      (fun I _Φ hΦ κ M _R θ₀ m _θprev T =>
        Twistie4CenteredSourceContract I hΦ m (I.kappaSeq κ M m) T C
          (Real.sqrt (l2NormSq θ₀))) := by
  obtain ⟨A, Cj, hA, hjets⟩ := tJets_datum_contract β Ccut
  obtain ⟨C, _, Cs, hsource⟩ := twistie4CenteredSource_contract β Ccut A (zero_le_one.trans hA)
  refine ⟨C, max Cj Cs, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θprev T hθ hT
  have hj := hjets I hz hx hh ((le_max_left _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp
      hmean ha m hm hmM θprev T hθ hT
  exact hsource I hz hx hh ((le_max_right _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean
      ha m hm hmM θprev T hθ hT
    (Real.sqrt (l2NormSq θ₀)) (Real.sqrt_nonneg _) hj.2.1 hj.1 hj.2.2.1

/-- Exact datum producer, with every jet input discharged. -/
theorem twistie5CenteredSource_datum_closed_contract (β Ccut : ℝ) :
    ∃ C C₁ : ℝ, OnA7Instances β Ccut C₁
      (fun I _Φ hΦ κ M _R θ₀ m _θprev T =>
        Twistie5CenteredSourceContract I hΦ m (I.kappaSeq κ M m) T C
          (Real.sqrt (l2NormSq θ₀))) := by
  obtain ⟨A, Cj, hA, hjets⟩ := tJets_datum_contract β Ccut
  obtain ⟨C, _, Cs, hsource⟩ := twistie5CenteredSource_contract β Ccut A (zero_le_one.trans hA)
  refine ⟨C, max Cj Cs, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θprev T hθ hT
  have hj := hjets I hz hx hh ((le_max_left _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp
      hmean ha m hm hmM θprev T hθ hT
  exact hsource I hz hx hh ((le_max_right _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean
      ha m hm hmM θprev T hθ hT
    (Real.sqrt (l2NormSq θ₀)) (Real.sqrt_nonneg _) hj.2.1 hj.1 hj.2.2.1

/-- Exact datum producer, with every jet input discharged. -/
theorem twistie1HMinusSource_datum_closed_contract (β Ccut : ℝ) :
    ∃ C C₁ : ℝ, OnA7Instances β Ccut C₁
      (fun I _Φ hΦ κ M _R θ₀ m _θprev T =>
        Twistie1HMinusSourceContract I hΦ m (I.kappaSeq κ M m) T C
          (Real.sqrt (l2NormSq θ₀))) := by
  obtain ⟨A, Cj, hA, hjets⟩ := tJets_datum_contract β Ccut
  obtain ⟨C, _, Cs, hsource⟩ := twistie1HMinusSource_contract β Ccut A (zero_le_one.trans hA)
  obtain ⟨Cz, hzero⟩ := twistie1MeanZero_contract β Ccut
  refine ⟨C, max Cj (max Cs Cz), ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θprev T hθ hT
  have hj := hjets I hz hx hh ((le_max_left _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp
      hmean ha m hm hmM θprev T hθ hT
  have hmz := hzero I hz hx hh ((le_max_right _ _).trans ((le_max_right _ _).trans hΛ)) Φ hΦ κ hκ
      M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θprev T hθ hT
  exact hsource I hz hx hh ((le_max_left _ _).trans ((le_max_right _ _).trans hΛ)) Φ hΦ κ hκ M hM
      hperm R hR θ₀ hs hp hmean ha m hm hmM θprev T hθ hT
    (Real.sqrt (l2NormSq θ₀)) (Real.sqrt_nonneg _) hj.2.1 hj.1 hj.2.2.1 hj.2.2.2 hmz

/-- Exact datum producer of the `normie3` centered contract, with every jet input discharged. -/
theorem normie3CenteredSource_datum_closed_contract (β Ccut : ℝ) :
    ∃ C C₁ : ℝ, OnA7Instances β Ccut C₁
      (fun I _Φ hΦ κ M _R θ₀ m _θprev T =>
        Normie3CenteredSourceContract I hΦ m (I.kappaSeq κ M m) T C
          (Real.sqrt (l2NormSq θ₀))) := by
  obtain ⟨A, Cj, hA, hjets⟩ := tJets_datum_contract β Ccut
  obtain ⟨C, _, Cs, hsource⟩ := normie3CenteredSource_contract β Ccut A (zero_le_one.trans hA)
  refine ⟨C, max Cj Cs, ?_⟩
  intro I hz hx hh hΛ Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean ha m hm hmM θprev T hθ hT
  have hj := hjets I hz hx hh ((le_max_left _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp
      hmean ha m hm hmM θprev T hθ hT
  exact hsource I hz hx hh ((le_max_right _ _).trans hΛ) Φ hΦ κ hκ M hM hperm R hR θ₀ hs hp hmean
      ha m hm hmM θprev T hθ hT
    (Real.sqrt (l2NormSq θ₀)) (Real.sqrt_nonneg _) hj.2.1 hj.1 hj.2.2.1

end AVenhance.Infra.Section5.Contracts
