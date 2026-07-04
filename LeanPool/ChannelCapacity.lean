/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import LeanPool.ChannelCapacity.Basic
import LeanPool.ChannelCapacity.KernelCompositionKullbackLeibler
import LeanPool.ChannelCapacity.ChainRule
import LeanPool.ChannelCapacity.NonDegeneracy
import LeanPool.ChannelCapacity.StrictConcavity
import LeanPool.ChannelCapacity.Capacity
import LeanPool.ChannelCapacity.Finite
import LeanPool.ChannelCapacity.Discharged
import LeanPool.ChannelCapacity.DischargedExample
import LeanPool.ChannelCapacity.Counterexample

/-!
# Uniqueness of Shannon Capacity-Achieving Priors

Source: url:https://github.com/abenenson/channel-capacity
Authors: Adam Benenson
Status: verified
Main declarations: `ChannelCapacity.exists_unique_capacity_achieving_prior_of_finite`
Tags: information-theory, channel-capacity, mutual-information, kullback-leibler, markov-kernel
MSC: 94A17, 94A15, 60A10
-/
