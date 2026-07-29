/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.PrimeIdealLogDerivSummability

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Ideal IsDedekindDomain
open scoped Topology

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem logDeriv_dedekindZeta_eq_tsum_primeIdeal {s : ℂ} (hs : 1 < s.re) :
    logDeriv (dedekindZeta K) s =
      ∑' P : HeightOneSpectrum (𝓞 K),
        logDeriv (primeIdealFactor K P) s := by
  have hs_mem : s ∈ dedekindZetaHalfPlane := hs
  have hprod :=
    logDeriv_tprod_eq_tsum
      (isOpen_dedekindZetaHalfPlane)
      hs_mem
      (f := primeIdealFactor K)
      (fun P ↦ primeIdealFactor_ne_zero K P (zero_lt_one.trans hs))
      (fun P z hz ↦
        (hasDerivAt_localFactor (one_lt_primeIdealNorm K P)
          (zero_lt_one.trans hz)).differentiableAt.differentiableWithinAt)
      (summable_logDeriv_primeIdealFactor K hs)
      (multipliableLocallyUniformlyOn_primeIdealFactor K)
      (tprod_primeIdealFactor_ne_zero K hs)
  rw [← hprod]
  have heq :
      (fun z : ℂ ↦
        ∏' P : HeightOneSpectrum (𝓞 K), primeIdealFactor K P z) =ᶠ[𝓝 s]
          dedekindZeta K := by
    filter_upwards [(isOpen_dedekindZetaHalfPlane.mem_nhds hs_mem)]
      with z hz
    exact dedekindZeta_primeIdeal_eulerProduct_tprod K hz
  rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq,
    dedekindZeta_primeIdeal_eulerProduct_tprod K hs]

theorem neg_logDeriv_dedekindZeta_eq_tsum_primeIdeal {s : ℂ}
    (hs : 1 < s.re) :
    -logDeriv (dedekindZeta K) s =
      ∑' P : HeightOneSpectrum (𝓞 K),
        -logDeriv (primeIdealFactor K P) s := by
  rw [logDeriv_dedekindZeta_eq_tsum_primeIdeal K hs,
    tsum_neg]

end NumberField.Odlyzko
