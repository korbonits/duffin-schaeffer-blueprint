# Duffin–Schaeffer blueprint — working notes

A `leanblueprint` for Koukoulopoulos–Maynard, *On the Duffin-Schaeffer conjecture*,
Annals of Math 192 (1) 2020 (arXiv:1907.04593). Terminal nodes are AnnalsChallenge's
sorried statements.

## State (2026-09-08)

`lake build` clean, no `sorry`, no project axiom; `scripts/check_axioms.py` checks 37
declarations, all standard. 11 `proof_wanted` remain. Tracks mathlib `master` on Lean
`v4.34.0-rc2`.

Proved: Chapter 2 (setup) entire; Chapter 3 (zero–one law) apart from a mathlib TODO that
is off the critical path; Chapter 4 (second moment) entire, including Chung–Erdős and a
Cauchy–Schwarz for `lintegral` that mathlib lacks; Theorem 2(a); the divisor bound; the
average order of φ; the first reduction toward Mertens.

Open and genuinely blocked: `exists_quasi_independent_subsets` / Propositions 5.4 and 6.3
(the paper, §§7–14); `setA_of_large_values` and `pollington_vaughan` (both external
citations to Pollington–Vaughan 1990); Mertens 1 and 2 (need Stirling and Abel summation,
both in mathlib); `corollary_3` (out of scope).

## Conventions

- Unproved nodes are `proof_wanted` (from `Batteries.Util.ProofWanted`), never `sorry`.
  They elaborate to private placeholders, so they do **not** get a `\lean{}` reference in
  `blueprint/src/content.tex` — mark them `\notready` and name them in `\texttt{}` instead.
  Only real `def`s and `structure`s carry `\lean{}`.
- A node marked **TRANSCRIBE** must not be given a Lean statement until someone has the
  cited source open. This is not caution for its own sake. Every TRANSCRIBE mark that has
  since been checked against the paper was covering a genuine error: the §5 reduction
  (restriction split, not `min`), Pollington–Vaughan (threshold, factors, and a missing
  indicator), and Definition 6.1 (wrong in six ways, including that the graphs are
  bipartite and carry a measure).
- The constant `C` in the overlap estimates is never computed anywhere. Gallagher's
  zero-one law turns any positive lower bound into `1`; that is why every estimate in
  the project can be stated with an unspecified constant.
- Run `scripts/check_axioms.py` *before* writing a commit message that quotes the
  declaration count.

## Local build notes

- `leanblueprint web` needs `plastex` on PATH:
  `export PATH="$HOME/.local/share/uv/tools/leanblueprint/bin:$PATH"`.
- An undefined LaTeX environment makes xelatex **block for terminal input**, so a hung
  blueprint build looks like a slow one. Killing it leaves a truncated `blueprint/print/print.aux`
  that poisons later runs; delete it.
- CI treats warnings as errors, including deprecation and linter warnings.

## Mathlib audit (September 2026)

Present: Gallagher (`AddCircle.addWellApproximable_ae_empty_or_univ`), both
Borel–Cantelli lemmas, `dimH` and `μH[d]`, `Nat.totient`, `Nat.primesBelow`,
Vitali/density, `Chebyshev.psi`/`theta` with explicit bounds, `AbelSummation`,
`vonMangoldt_sum`, Stirling.

Absent, verified by grep: Cauchy–Schwarz for measure-theoretic integrals (now proved
here), Chung–Erdős, Paley–Zygmund; Mertens; mass transference.

## Scope

Theorems 1 and 2(a),(b) only. Corollary 3 needs the Beresnevich–Velani mass
transference principle — an independent project of comparable size. `Hausdorff.lean`
states it and stops.
