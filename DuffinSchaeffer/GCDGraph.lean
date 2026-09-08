/- Bipartite GCD graphs: the machinery of Koukoulopoulos-Maynard, section 6.

   Transcribed from the paper (arXiv:1907.04593), Definitions 6.1, 6.2 and 6.4 and
   Proposition 6.3.

   ## What the earlier guess got wrong

   The first draft of this file carried a `GCDGraph` structure written from memory. Every
   substantive feature of it was wrong, which is why it was marked TRANSCRIBE:

   * the graphs are **bipartite** -- two vertex sets `V`, `W` and edges in `V × W`. The
     guess had a single vertex set with a symmetric irreflexive edge relation, so its
     `E_symm` and `E_irrefl` fields do not correspond to anything;
   * a **measure** `μ` is part of the data. The guess had none, and the whole argument is
     about the weighted edge density `μ(E)`;
   * condition (i) is **divisibility**, `p ^ f p ∣ v`, not exact divisibility. The guess
     demanded exactness everywhere;
   * condition (ii) is about `min (f p) (g p)` exactly dividing `gcd (v, w)`, not `g p`;
   * condition (iii) -- exactness of `p ^ f p ∥ v` and `p ^ g p ∥ w`, but **only when
     `f p ≠ g p`** -- was absent from the guess entirely;
   * the guess imposed `g p ≤ f p`, which the paper does not.

   Had the earlier structure been used, everything built on it would have been unsound in
   a way invisible until someone opened the paper. -/
import DuffinSchaeffer.Basic

open scoped BigOperators NNReal

namespace DuffinSchaeffer

/-- `ExactPow p k n` is the paper's `p ^ k ‖ n`: the exact power of `p` dividing `n`. -/
def ExactPow (p k n : ℕ) : Prop := p ^ k ∣ n ∧ ¬ p ^ (k + 1) ∣ n

/-- **Definition 6.1**: a bipartite GCD graph.

The septuple `(μ, V, W, E, P, f, g)` of the paper. `f` and `g` are given here as total
functions `ℕ → ℕ`, constrained only on `P`, which is the usual way to model a function
defined on `P` alone. -/
structure GCDGraph where
  /-- The measure on the vertices; `μ` of a set of pairs is `∑ μ(n₁)μ(n₂)`. -/
  μ : ℕ → ℝ≥0
  /-- The left vertex set. -/
  V : Finset ℕ
  /-- The right vertex set. -/
  W : Finset ℕ
  /-- The edges, a subset of `V × W`. -/
  E : Finset (ℕ × ℕ)
  /-- The distinguished set of primes. -/
  P : Finset ℕ
  /-- `f p` is the exponent attached to `p` on the left. -/
  f : ℕ → ℕ
  /-- `g p` is the exponent attached to `p` on the right. -/
  g : ℕ → ℕ
  V_pos : ∀ v ∈ V, 0 < v
  W_pos : ∀ w ∈ W, 0 < w
  E_subset : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ W
  P_prime : ∀ p ∈ P, Nat.Prime p
  /-- (e)(i), left: `p ^ f p ∣ v`. Divisibility, not exactness. -/
  f_dvd : ∀ p ∈ P, ∀ v ∈ V, p ^ f p ∣ v
  /-- (e)(i), right: `p ^ g p ∣ w`. -/
  g_dvd : ∀ p ∈ P, ∀ w ∈ W, p ^ g p ∣ w
  /-- (e)(ii): along an edge, `p ^ min (f p) (g p)` **exactly** divides the gcd. -/
  edge_gcd : ∀ p ∈ P, ∀ e ∈ E, ExactPow p (min (f p) (g p)) (Nat.gcd e.1 e.2)
  /-- (e)(iii), left: exactness on `V`, but only when `f p ≠ g p`. -/
  f_exact : ∀ p ∈ P, f p ≠ g p → ∀ v ∈ V, ExactPow p (f p) v
  /-- (e)(iii), right: exactness on `W`, but only when `f p ≠ g p`. -/
  g_exact : ∀ p ∈ P, f p ≠ g p → ∀ w ∈ W, ExactPow p (g p) w

namespace GCDGraph

/-- The measure of a finite set of pairs: `μ(N) = ∑_{(n₁,n₂) ∈ N} μ(n₁)μ(n₂)`. -/
noncomputable def measurePairs (G : GCDGraph) (N : Finset (ℕ × ℕ)) : ℝ≥0 :=
  ∑ e ∈ N, G.μ e.1 * G.μ e.2

/-- The weighted edge density, `μ(E)`. -/
noncomputable def edgeMeasure (G : GCDGraph) : ℝ≥0 := G.measurePairs G.E

/-- **Definition 6.2**: `G` is non-trivial when `μ(E) > 0`. -/
def Nontrivial (G : GCDGraph) : Prop := 0 < G.edgeMeasure

/-- **Definition 6.4**: `G' ≼ G`, a GCD subgraph. Same measure, smaller vertex and edge
sets, a **larger** set of primes, and exponent data extending that of `G`. -/
def IsSubgraph (G' G : GCDGraph) : Prop :=
  G'.μ = G.μ ∧ G'.V ⊆ G.V ∧ G'.W ⊆ G.W ∧ G'.E ⊆ G.E ∧ G.P ⊆ G'.P ∧
    (∀ p ∈ G.P, G'.f p = G.f p) ∧ (∀ p ∈ G.P, G'.g p = G.g p)

theorem isSubgraph_refl (G : GCDGraph) : G.IsSubgraph G :=
  ⟨rfl, Finset.Subset.refl _, Finset.Subset.refl _, Finset.Subset.refl _,
    Finset.Subset.refl _, fun _ _ => rfl, fun _ _ => rfl⟩

theorem isSubgraph_trans {G₁ G₂ G₃ : GCDGraph} (h₁ : G₁.IsSubgraph G₂)
    (h₂ : G₂.IsSubgraph G₃) : G₁.IsSubgraph G₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1, h₁.2.2.2.1.trans h₂.2.2.2.1,
    h₂.2.2.2.2.1.trans h₁.2.2.2.2.1,
    fun p hp => (h₁.2.2.2.2.2.1 p (h₂.2.2.2.2.1 hp)).trans (h₂.2.2.2.2.2.1 p hp),
    fun p hp => (h₁.2.2.2.2.2.2 p (h₂.2.2.2.2.1 hp)).trans (h₂.2.2.2.2.2.2 p hp)⟩

end GCDGraph

/-- **Proposition 6.3** (edge set bound), the form in which the whole paper is stated.

`TRANSCRIBE` is discharged for the *definitions*; this statement is the paper's, but the
set `Eₜ` it refers to is defined in Proposition 5.4 and depends on `L_t` and `M`, which
this development has not yet written down. Sections 7-14 prove it. -/
proof_wanted edge_measure_le (G : GCDGraph) (t : ℝ) (ht : 1 ≤ t)
    (htrivial : G.P = ∅) (hV : G.V = G.W) :
    ∃ C : ℝ, ∀ _ : G.Nontrivial, (G.edgeMeasure : ℝ) ≤ C / t

end DuffinSchaeffer
