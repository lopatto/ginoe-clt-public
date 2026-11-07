# Real Ginibre counting CLT

This package advertises **`Paper.principalTheorem`**, the main CLT
(Theorem 1.3) of the local manuscript associated with
[Goel–Lopatto–Xie, arXiv:2306.10243v2](https://arxiv.org/abs/2306.10243v2).

For a nonempty connected open set $A$ with Lipschitz boundary and closure in
the open upper unit disk, the eigenvalue count of a real iid standard Gaussian
matrix scaled by $N^{-1/2}$, centered by its exact expectation and divided by
$N^{1/4}$, converges in distribution to a centered Gaussian of variance
$\mathcal H^1(\partial A)/(2\pi^{3/2})$.
Eigenvalues retain algebraic multiplicity, and the limit runs through every
positive matrix size, including both parities. Boundary length is finite,
positive and measured with Euclidean length-normalized Hausdorff measure.

Only the main CLT is advertised. Its complete model, hypotheses and conclusion
are in `Challenge.lean`; `Solution.lean` exports the proof without importing
Challenge. Solution's proof closure has no additional mathematical assumptions or admissions.
The explicit graph-chart presentation and source/review disclosures are recorded
in [formalization.yaml](formalization.yaml).

## Build

Lean and all Lake dependencies are pinned. Obtain the exact Lean version in
`lean-toolchain`, then run:

~~~sh
lake exe cache get
LEAN_NUM_THREADS=1 lake --wfail build GinoeClt Solution StatementChecks
LEAN_NUM_THREADS=1 lake build Challenge
~~~

Challenge has one deliberate statement hole, permitted for the advertised
comparison. It is outside Solution's import closure. StatementChecks independently
checks the principal type and central definitions and is also outside that closure.

`comparator.json` compares `Paper.principalTheorem` and its transitive ordinary
definition bodies; no definition-body holes are configured. The permitted axioms
are `propext`, `Quot.sound` and `Classical.choice`.
Protected Comparator and independent kernel replay are **UNRUN** in the local
macOS environment; Palomar's mandatory verifier remains required. No registration,
acceptance or independent human review is claimed.

## Attribution

Human author and maintainer: Patrick Lopatto. Substantial development and automated
review used OpenAI Codex; see the metadata for disclosure. New code is Apache-2.0.
Existing compatible port notices and attribution are retained in source.
