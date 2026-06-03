/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/

import LeanPool.RlTheoryInLean.Analysis
import LeanPool.RlTheoryInLean.Data
import LeanPool.RlTheoryInLean.Defs
import LeanPool.RlTheoryInLean.MeasureTheory
import LeanPool.RlTheoryInLean.Order
import LeanPool.RlTheoryInLean.Probability
import LeanPool.RlTheoryInLean.StochasticApproximation

/-!
# RL Theory in Lean

Source: arxiv:2511.03618
Authors: Shangtong Zhang
Status: verified
Main declarations: `StochasticMatrix.stationary_distribution_exists`
Tags: probability, reinforcement-learning, stochastic-matrices
MSC: 62L20, 60J10
-/

/-!
## Provenance

Imported from <https://github.com/ShangtongZhang/rl-theory-in-lean> (MIT-licensed
upstream; relicensed into Lean Pool under Apache 2.0 with the upstream author's
copyright preserved). Accompanies the paper *Towards Formalizing Reinforcement
Learning Theory* (arXiv:2511.03618). Ported from Lean `v4.28.0-rc1` to Lean Pool's
`v4.30.0-rc2`. This Lean Pool import keeps the warning-clean core infrastructure.

## Mathematical overview

The project mirrors Mathlib's directory layout and develops stochastic
row-stochastic matrices, Doeblin minorization and geometric mixing for finite
chains, finite Markov-chain kernels and trajectory measures, measure/kernel helper
lemmas, and discrete Gronwall inequalities used in stochastic approximation.
-/

alias Aperiodic := StochasticMatrix.Aperiodic
alias DoeblinMinorization := StochasticMatrix.DoeblinMinorization
alias GeometricMixing := StochasticMatrix.GeometricMixing
alias RowStochastic := StochasticMatrix.RowStochastic
alias Stationary := StochasticMatrix.Stationary
alias cesaroAverage := StochasticMatrix.cesaroAverage
alias cesaro_average_almost_invariant := StochasticMatrix.cesaro_average_almost_invariant
alias cesaro_average_is_svec := StochasticMatrix.cesaro_average_is_svec
alias chapman_kolmogorov_eq_ge := StochasticMatrix.chapman_kolmogorov_eq_ge
alias eventually_positive := StochasticMatrix.eventually_positive
alias multi_step_stationary := StochasticMatrix.multi_step_stationary
alias pos_of_stationary := StochasticMatrix.pos_of_stationary
alias returnTimes := StochasticMatrix.returnTimes
alias return_times_add_mem := StochasticMatrix.return_times_add_mem
alias smatAsOperator := StochasticMatrix.smatAsOperator
alias smat_as_operator_iter := StochasticMatrix.smat_as_operator_iter
alias smat_contraction_in_simplex := StochasticMatrix.smat_contraction_in_simplex
alias smat_minorizable_with_large_pow := StochasticMatrix.smat_minorizable_with_large_pow
alias smat_mul_smat_is_smat := StochasticMatrix.smat_mul_smat_is_smat
alias smat_nonexpansive_in_l1 := StochasticMatrix.smat_nonexpansive_in_l1
alias smat_pow_is_smat := StochasticMatrix.smat_pow_is_smat
alias smat_pow_nonexpansive_in_l1 := StochasticMatrix.smat_pow_nonexpansive_in_l1
alias stationary_distribution_exists := StochasticMatrix.stationary_distribution_exists
alias stationary_distribution_uniquely_exists :=
  StochasticMatrix.stationary_distribution_uniquely_exists
alias sum_svec_mul_smat_eq_one := StochasticMatrix.sum_svec_mul_smat_eq_one
alias svec_mul_smat_is_svec := StochasticMatrix.svec_mul_smat_is_svec
alias uniformDistribution := StochasticMatrix.uniformDistribution

namespace StochasticVec

alias le_one := StochasticMatrix.StochasticVec.le_one

end StochasticVec

namespace ContinuousLinearMap

alias condExp_comp := MeasureTheory.ContinuousLinearMap.condExp_comp

end ContinuousLinearMap

namespace Integrable

alias finset_sum := MeasureTheory.Integrable.finset_sum

end Integrable

namespace EventuallyEq

alias finset_sum := Filter.EventuallyEq.finset_sum

end EventuallyEq

namespace Kernel

alias iter := ProbabilityTheory.MarkovChain.Kernel.iter

end Kernel
