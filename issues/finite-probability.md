---
title: Finitely supported distributions and expectation as a state
status: open
labels: [stdlib,mathematics,probability]
area: mathematics
milestone: [ml-gaussian-states]
created: 2026-10-21
updated: 2026-10-22
---

The constructive first layer of probability: distributions with finite
support and weights in an ordered field (rational weights compute),
expectation as a linear state, independence and products, variance, and
Markov/Chebyshev at this level. Customers: SGD over a finite dataset with
uniform sampling, sampling in inference, stochastic rounding in the float
library, and the state interface of [[ml-gaussian-states]]
(`docs/wick-survey.md` §3.4, §4.1).

Continuous distributions and measure come later (roadmap mathematics item
4); this layer should be stated so a measure-theoretic expectation can later
be shown to be a state of the same interface.

## Log
