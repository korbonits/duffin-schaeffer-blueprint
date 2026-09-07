# Duffin–Schaeffer blueprint — working notes

A `leanblueprint` for Koukoulopoulos–Maynard, *On the Duffin-Schaeffer conjecture*,
Annals of Math 192 (1) 2020. Terminal nodes are AnnalsChallenge's sorried statements.

## State (2026-09-06)

Skeleton. `lake build` clean, no `sorry`, no project axiom; `scripts/check_axioms.py`
checks 9 declarations, all standard. Every mathematical node is `proof_wanted`.
Tracks mathlib `master` on Lean `v4.34.0-rc2`.

## Conventions

- Unproved nodes are `proof_wanted` (from `Batteries.Util.ProofWanted`), never `sorry`.
  They elaborate to private placeholders, so they do **not** get a `\lean{}` reference in
  `blueprint/src/content.tex` — mark them `\notready` and name them in `\texttt{}` instead.
  Only real `def`s and `structure`s carry `\lean{}`.
- A node marked **TRANSCRIBE** must not be given a Lean statement until someone has the
  cited source open. Reconstructing a constant from memory is the one failure mode that
  stays invisible until the whole chapter is built on it.
- The constant `C` in the overlap estimates is never computed anywhere. Gallagher's
  zero-one law turns any positive lower bound into `1`; that is why every estimate in
  the project can be stated with an unspecified constant.

## Mathlib audit (September 2026)

Present: Gallagher (`AddCircle.addWellApproximable_ae_empty_or_univ`), both
Borel–Cantelli lemmas, `dimH` and `μH[d]`, `Nat.totient`, `Nat.primesBelow`,
Vitali/density.

Absent, verified by grep: Chung–Erdős, Paley–Zygmund, any `second_moment`; Mertens
(only an unrelated Dedekind–Mertens TODO); the divisor bound; mass transference
(`beresnevich`, `massTransference` — nothing).

## Scope

Theorems 1 and 2(a),(b) only. Corollary 3 needs the Beresnevich–Velani mass
transference principle — an independent project of comparable size. `Hausdorff.lean`
states it and stops.
