/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeanPool.ChannelCapacity.Basic
public import LeanPool.ChannelCapacity.KernelCompositionKullbackLeibler
public import LeanPool.ChannelCapacity.ChainRule
public import LeanPool.ChannelCapacity.NonDegeneracy
public import LeanPool.ChannelCapacity.StrictConcavity
public import LeanPool.ChannelCapacity.Capacity
public import LeanPool.ChannelCapacity.Finite
public import LeanPool.ChannelCapacity.Discharged
public import LeanPool.ChannelCapacity.DischargedExample
public import LeanPool.ChannelCapacity.Counterexample

/-!
# Uniqueness of Shannon Capacity-Achieving Priors

Source: doi:10.1002/047174882X
Authors: Adam Benenson
Status: verified
Main declarations: `ChannelCapacity.exists_unique_capacity_achieving_prior_of_finite`
Tags: information-theory, channel-capacity, mutual-information, kullback-leibler, markov-kernel
MSC: 94A17, 94A15, 60A10
-/

@[expose] public section
