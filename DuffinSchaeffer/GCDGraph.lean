/- GCD graphs: the machinery of Koukoulopoulos-Maynard.

   This is the heart of the paper and the only part of the project with no precedent in
   Mathlib or anywhere else. Sections 6-14 of the paper -- an earlier draft of this file
   guessed 3-10, which is wrong: section 3 is the proof outline, section 5 the
   preliminaries, and the graphs themselves do not appear until section 6.

   The idea. The overlap `μ(A_q ∩ A_r)` exceeds the independent prediction
   `μ(A_q) μ(A_r)` by a factor governed by the small primes dividing `qr/gcd(q,r)²`.
   Bounding the double sum therefore means controlling how often a set of denominators
   can be pairwise "entangled" in this sense. Koukoulopoulos and Maynard encode the
   entanglement as a weighted graph whose vertices are denominators and whose edges
   carry the p-adic data of the gcd, attach to such a graph a numerical *quality*, and
   show that a graph which is bad for the overlap estimate can always be modified so
   as to strictly increase its quality. Since quality is bounded above, iterating
   terminates, and the terminal graphs are exactly the ones for which the estimate
   holds.

   What is here. The `GCDGraph` structure below records the data and the divisibility
   constraints; that shape is stable and safe to fix now. The quality function, the
   catalogue of graph operations and the iteration are NOT stated here, deliberately.

   TRANSCRIBE. The quality function (paper §6, where the graphs are *bipartite* -- another
   thing this file did not anticipate) and each operation in the iteration (§7 reduction to
   a good GCD subgraph, §8 reduction to three iterative propositions, §§9-14 their proofs)
   must be copied from the paper before anything in this file can be used;
   they involve explicit exponents and normalisations that must not be reconstructed
   from memory. Until then they live in the blueprint's LaTeX only, as
   `\notready` nodes with their section references. Writing a plausible-looking
   `quality` here would be worse than leaving the gap visible. -/
import DuffinSchaeffer.Basic

open scoped BigOperators

namespace DuffinSchaeffer

/-- A **GCD graph**: a finite set of denominators, a symmetric irreflexive edge
relation on them, a finite set of distinguished primes `P`, and for each `p ∈ P` the
exact power `f p` of `p` dividing every vertex and the exact power `g p` of `p`
dividing the gcd along every edge.

Fixing the p-adic valuations along `P` is what makes the vertex set homogeneous
enough for the quality bookkeeping; the iteration proceeds by enlarging `P` and
refining `f` and `g`. -/
structure GCDGraph where
  /-- The vertices: a finite set of denominators. -/
  V : Finset ℕ+
  /-- The edges. -/
  E : Finset (ℕ+ × ℕ+)
  /-- The distinguished primes along which valuations are pinned. -/
  P : Finset ℕ
  /-- `f p` is the exact power of `p` dividing every vertex. -/
  f : ℕ → ℕ
  /-- `g p` is the exact power of `p` dividing the gcd of the endpoints of every edge. -/
  g : ℕ → ℕ
  P_prime : ∀ p ∈ P, Nat.Prime p
  E_symm : ∀ e ∈ E, (e.2, e.1) ∈ E
  E_irrefl : ∀ e ∈ E, e.1 ≠ e.2
  E_subset : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V
  f_spec : ∀ p ∈ P, ∀ v ∈ V, p ^ f p ∣ (v : ℕ) ∧ ¬ p ^ (f p + 1) ∣ (v : ℕ)
  g_spec : ∀ p ∈ P, ∀ e ∈ E,
    p ^ g p ∣ Nat.gcd (e.1 : ℕ) (e.2 : ℕ) ∧ ¬ p ^ (g p + 1) ∣ Nat.gcd (e.1 : ℕ) (e.2 : ℕ)
  g_le_f : ∀ p ∈ P, g p ≤ f p

end DuffinSchaeffer
