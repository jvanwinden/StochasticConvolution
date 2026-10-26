# Discontinuity of stochastic convolutions

A Lean 4 formalization of a corollary of Theorem 1.2 from [1].

The main result is `discontinuous_stochastic_convolution`: a stochastic 
convolution of a predictable integrand with uniformly bounded $L^2$-norm 
with a $C_0$-semigroup on a Hilbert space might not have a continuous modification.

Since Mathlib does not have a definition for the stochastic integral, 
the Challenge file additionally contains a characterization of the 
stochastic integral in terms of the predicate `IsItoIntegral`.

The important files are the following:
- [`Challenge.lean`](Challenge.lean) contains the necessary definitions and statement of the main theorem.
- [`Solution.lean`](Solution.lean) contains the proof of the theorem, using results from the `StochasticConvolution` module.

## Verification
To audit the theorem statement, examine `Challenge.lean` (which imports only Mathlib).

To verify the proof, first run `lake exe cache get` (optional, to fetch the Mathlib cache) and then 
```
lake comparator
```
which should output 
```
Your solution is okay!
```

The project is pinned to Lean and Mathlib version `v4.35.0`.
This work was supported in part by a grant of access to OpenAI models 
through the ChatGPT for Academic Researchers program.

[1]. M. Veraar and J. van Winden, "No free lunch for continuity of stochastic convolutions", [arXiv:2609.12688](https://arxiv.org/abs/2609.12688).