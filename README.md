# Introduction

This directory includes:

- README.md: this file
- Paper.lean: Lean4 file with all the examples from the paper
- Makefile: configuration file for compiling the examples and dumping compilation information for the examples
- relative.py: script that helps Makefile normalize file paths
- run_term_experiment.py: Python3 script to compare variants of `evalNat` on two different types of tower
- Dockerfile: instructions to build a Docker image that can run the experiments.
- run.sh: bash script for running experiments inside Docker

# EvalNat experiments

We compare several different variants of `evalNat` on
1. `tower`: a single (perfect-shared) tower
2. `twoTowers`: two disjoint towers added together

The variants we evaluate are collected at the bottom of Paper.lean.
We reproduce them here for convenience:

1. evalNatNoCache: naive traversal without caching
2. evalNatCacheSlowEqSlowHash: traversal with caching and slow equality and slow hashing.
3. evalNatCacheSlowEqFastHash: traversal with caching and slow equality and fast hashing.
4. evalNatCacheFastEqSlowHash: traversal with caching and fast equality and slow hashing.
5. evalNatCacheFastEqFastHash: traversal with caching and fast equality and fast hashing.
6. evalNatCacheFastEqFastHashRobust: traversal with caching and fast eq, fast hash, preceeded by a `shareCommon` step
7. evalNatPtrCache: traversal with pointer-caching (fixed number of buckets) and pointer comparisons within the buckets
8. evalNatPtrCacheRobust: same as `evalNatPtrCache` but preceeded by `shareCommon`

Conclusions:

1. On `tower`, (1-4) are exponential, (5-8) are linear.
2. On `twoTowers`, (1-5) are exponential and (6-8) are linear.

# Running experiments with Docker

Simply execute `run.sh`. This will do the following inside:

1. Compile `Paper.lean`, and store the output at `Paper.out`.
2. Emit the C code generated for the examples in `Paper.lean` into `Paper.c`.
3. Run the `evalNat` experiments, storing pngs of the results at `tower.png` and `twoTowers.png`.
4. Copy all four files to the local directory for inspection.
