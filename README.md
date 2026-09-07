# duffin-schaeffer-blueprint

A [`leanblueprint`](https://github.com/PatrickMassot/leanblueprint) for the
Duffin–Schaeffer conjecture, proved by Koukoulopoulos and Maynard in
*Annals of Mathematics* **192** (2020), 251–307.

**Status: skeleton.** Every mathematical node is a `proof_wanted`. The project
builds clean, contains no `sorry`, and declares no axiom.

## What this is

Mathlib already contains the first reduction. `Mathlib/NumberTheory/WellApproximable.lean`
(Oliver Nash, 2022) proves Gallagher's ergodic theorem, and its own docstring says:

> Given a particular `δ`, the Duffin-Schaeffer conjecture (now a theorem) gives a criterion
> for deciding which of the two cases in the conclusion of Gallagher's theorem actually
> occurs. […] We do *not* include a formalisation of the Koukoulopoulos-Maynard result here.

This project is that criterion.

The terminal nodes (`theorem_1`, `theorem_2_a`, `theorem_2_b`) are transcribed from
[`ImperialCollegeLondon/AnnalsChallenge`](https://github.com/ImperialCollegeLondon/AnnalsChallenge),
file `AnnalsChallenge/AnnalsOfMathematics/2020-192-1-DuffinSchaefferConjecture.lean`
(Katerina Hristova and Kevin Buzzard, Apache 2.0), where they stand as `sorry`.
Discharging them here discharges them there.

## Layout

| File | Contents |
| --- | --- |
| `Basic.lean` | The sets `setAq`, `setA`, `setK`, the majorant `psiStar`, and their measure-theoretic basics |
| `Gallagher.lean` | Transfer to `AddCircle`, and the reduction "positive measure suffices" |
| `ChungErdos.lean` | Chung–Erdős and the quasi-independent divergence Borel–Cantelli lemma |
| `Anatomy.lean` | Mertens, the divisor bound, the average order of `φ` — all missing from Mathlib |
| `GCDGraph.lean` | The `GCDGraph` structure. Quality and the iteration are deliberately not stated; see the file header |
| `Overlap.lean` | The interface the second-moment argument consumes |
| `Main.lean` | Theorems 1, 2(a), 2(b) |
| `Hausdorff.lean` | Corollary 3, and why it is out of scope |

## Where to start

Three independent entry points, in increasing order of commitment:

1. **`Anatomy.lean`** — Mertens' theorems and the divisor bound depend on nothing else
   here and belong in Mathlib on their own merits.
2. **`chung_erdos`** — a Cauchy–Schwarz argument; also belongs upstream.
3. **`theorem_2_a`** — the convergence half of Theorem 2. First Borel–Cantelli applied to
   a majorant; needs none of the GCD-graph machinery. The first node whose proof is
   genuinely about Duffin–Schaeffer.

`addWellApproximable_ae_empty_or_univ_of_nonneg` is a fourth: it is a TODO recorded in
Mathlib's own source, and closing it is a Mathlib contribution independent of this project.

## Marked gaps

Nodes carrying **TRANSCRIBE** in the blueprint involve explicit exponents, normalisations
or thresholds that must be copied from the source rather than reconstructed. They have no
Lean statement on purpose: a plausible-looking statement with a wrong constant is worse
than a visible gap. These are the quality function and the graph iteration
(paper §§3, 5–10) and the Pollington–Vaughan overlap estimate (Pollington and Vaughan,
*Mathematika* 37 (1990), 190–200).

## Building

```console
lake exe cache get
lake build
python3 scripts/check_axioms.py
```

Blueprint:

```console
pip install leanblueprint
leanblueprint pdf && leanblueprint web && leanblueprint checkdecls
```
