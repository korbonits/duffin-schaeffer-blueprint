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

/-- `ab / gcd(a,b)²`: what is left of `ab` after the common factor is removed twice. -/
def coprimePart (a b : ℕ) : ℕ := (a * b) / (Nat.gcd a b) ^ 2

open Classical in
/-- `L_t(a,b) = ∑_{p ∣ ab/gcd(a,b)², p ≥ t} 1/p`. Paper (5.1). -/
noncomputable def LSum (t : ℝ) (a b : ℕ) : ℝ :=
  ∑ p ∈ (coprimePart a b).primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)), (1 : ℝ) / p

/-- `v` with its `P`-part removed: `v / ∏_{p ∈ P} p^{e p}`. Proposition 7.1(d)(ii) writes
`v = v' ∏_{p ∈ P'} p^{f'(p)}`; this is `v'`. -/
def stripPrimes (v : ℕ) (P : Finset ℕ) (e : ℕ → ℕ) : ℕ := v / ∏ p ∈ P, p ^ e p

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

/-! ### Definition 6.5: subgraphs cut out by prime-power divisibility -/

namespace GCDGraph

open Classical in
/-- `V_{p^k}`: the members of a set whose `p`-adic valuation is exactly `k`. Note that
`V_{2^0}` and `V_{3^0}` are different sets. Paper, Definition 6.5(a). -/
noncomputable def powPart (S : Finset ℕ) (p k : ℕ) : Finset ℕ := {v ∈ S | ExactPow p k v}

open Classical in
/-- `E(V', W') = E ∩ (V' × W')`. Paper, Definition 6.5(b). -/
noncomputable def edgesOn (G : GCDGraph) (V' W' : Finset ℕ) : Finset (ℕ × ℕ) :=
  {e ∈ G.E | e.1 ∈ V' ∧ e.2 ∈ W'}

/-! ### Definition 6.6: the quantities attached to a GCD graph -/

/-- `μ(S) = ∑_{v ∈ S} μ(v)`. -/
noncomputable def measureSet (G : GCDGraph) (S : Finset ℕ) : ℝ≥0 := ∑ v ∈ S, G.μ v

/-- The edge density `δ(G) = μ(E) / (μ(V)μ(W))`. Division by zero in `ℝ≥0` is zero, so
this already agrees with the paper's convention that `δ = 0` when `μ(V)` or `μ(W)`
vanishes. Paper, Definition 6.6(a). -/
noncomputable def edgeDensity (G : GCDGraph) : ℝ≥0 :=
  G.edgeMeasure / (G.measureSet G.V * G.measureSet G.W)

open Classical in
/-- `Γ_G(v) = {w ∈ W : (v,w) ∈ E}`. Paper, Definition 6.6(b). -/
noncomputable def neighborsV (G : GCDGraph) (v : ℕ) : Finset ℕ := {w ∈ G.W | (v, w) ∈ G.E}

open Classical in
/-- `Γ_G(w) = {v ∈ V : (v,w) ∈ E}`. Paper, Definition 6.6(b). -/
noncomputable def neighborsW (G : GCDGraph) (w : ℕ) : Finset ℕ := {v ∈ G.V | (v, w) ∈ G.E}

/-- `R(G)`: the primes dividing some gcd along an edge that `P` has not yet accounted for.
Paper, Definition 6.6(c). The paper writes `{p ∉ P : ...}`; primality is left implicit
there and made explicit here. -/
def R (G : GCDGraph) : Set ℕ :=
  {p | Nat.Prime p ∧ p ∉ G.P ∧ ∃ e ∈ G.E, p ∣ Nat.gcd e.1 e.2}

/-- `R♯(G)`: those `p ∈ R(G)` for which some single `p`-adic valuation already carries
almost all of the mass on both sides. Paper, Definition 6.6(c). -/
noncomputable def Rsharp (G : GCDGraph) : Set ℕ :=
  {p ∈ G.R | ∃ k : ℕ,
    1 - (10 : ℝ) ^ (40 : ℕ) / p ≤ (G.measureSet (powPart G.V p k) : ℝ) / (G.measureSet G.V : ℝ) ∧
    1 - (10 : ℝ) ^ (40 : ℕ) / p ≤ (G.measureSet (powPart G.W p k) : ℝ) / (G.measureSet G.W : ℝ)}

/-- `R♭(G) = R(G) \ R♯(G)`. Paper, Definition 6.6(c). -/
noncomputable def Rflat (G : GCDGraph) : Set ℕ := G.R \ G.Rsharp

open Classical in
/-- **The quality** (paper, Definition 6.6(d)):

  `q(G) = δ¹⁰ μ(V) μ(W) ∏_{p ∈ P} p^{|f(p)-g(p)|} /
            ((1 - 1[f(p) = g(p) ≥ 1]/p)² (1 - p^{-31/30})¹⁰)`.

The indicator is on `f(p) = g(p) ≥ 1`, not merely on `f(p) = g(p)`. That distinction is
invisible in the published PDF's extracted text and was read off the arXiv LaTeX source;
guessing it would have been a coin flip, and the paper's remark ties this exact factor to
the `φ(q)/q` weighting of the vertices, so it is load-bearing rather than cosmetic.

The exponent is written `(f p - g p) + (g p - f p)`, which is `|f p - g p|` in `ℕ` with
truncated subtraction: one of the two summands is always zero. -/
noncomputable def quality (G : GCDGraph) : ℝ :=
  (G.edgeDensity : ℝ) ^ (10 : ℕ) * (G.measureSet G.V : ℝ) * (G.measureSet G.W : ℝ) *
    ∏ p ∈ G.P,
      (p : ℝ) ^ ((G.f p - G.g p) + (G.g p - G.f p)) /
        ((1 - (if G.f p = G.g p ∧ 1 ≤ G.f p then (1 : ℝ) else 0) / (p : ℝ)) ^ (2 : ℕ) *
          (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ (10 : ℕ))

end GCDGraph

/-- **Proposition 7.1** (existence of a good GCD subgraph).

The hinge of the whole argument: from a GCD graph with trivial prime set, every edge
sharing many primes above `t`, and `t` large relative to the edge density, one extracts a
subgraph that is *structured* -- no unaccounted primes, both sides of the bipartition
almost regular -- while either gaining a factor `δ t⁵⁰` in quality, or gaining a constant
factor and leaving the edges still sharing many primes after the `P'`-part is stripped.

Sections 8-14 prove it, and Proposition 6.3 follows from it (section 7).

The implied constant is absolute, so it is quantified outermost. In particular the `δ`
in (d)(i) *multiplies*: the published PDF renders that clause as `q(G')≫δt50q(G)`, which
reads naturally as `≫_δ`, a constant depending on `δ`. The arXiv source says
`\gg \delta t^{50}`. Two very different statements, and the weaker reading would have
silently thrown away the density gain the compression argument exists to produce. -/
proof_wanted exists_good_subgraph :
    ∃ c : ℝ, 0 < c ∧ ∀ (G : GCDGraph) (t : ℝ),
      G.P = ∅ →
      0 < G.edgeDensity →
      (∀ e ∈ G.E, 10 ≤ LSum t e.1 e.2) →
      10 * ((G.edgeDensity : ℝ)) ^ (-(1 : ℝ) / 50) ≤ t →
      (10 : ℝ) ^ (2000 : ℕ) < t →
      ∃ G' : GCDGraph, G'.IsSubgraph G ∧ 0 < G'.edgeDensity ∧ G'.R = ∅ ∧
        (∀ v ∈ G'.V, 9 * (G'.edgeDensity : ℝ) / 10 * (G'.measureSet G'.W : ℝ)
          ≤ (G'.measureSet (G'.neighborsV v) : ℝ)) ∧
        (∀ w ∈ G'.W, 9 * (G'.edgeDensity : ℝ) / 10 * (G'.measureSet G'.V : ℝ)
          ≤ (G'.measureSet (G'.neighborsW w) : ℝ)) ∧
        (c * (G.edgeDensity : ℝ) * t ^ (50 : ℕ) * G.quality ≤ G'.quality ∨
          (c * G.quality ≤ G'.quality ∧
            ∀ e ∈ G'.E, 4 ≤ LSum t (stripPrimes e.1 G'.P G'.f) (stripPrimes e.2 G'.P G'.g)))

/-- **Proposition 6.3** (edge set bound), the form in which the whole paper is stated.

`TRANSCRIBE` is discharged for the *definitions*; this statement is the paper's, but the
set `Eₜ` it refers to is defined in Proposition 5.4 and depends on `L_t` and `M`, which
this development has not yet written down. Sections 7-14 prove it. -/
proof_wanted edge_measure_le (G : GCDGraph) (t : ℝ) (ht : 1 ≤ t)
    (htrivial : G.P = ∅) (hV : G.V = G.W) :
    ∃ C : ℝ, ∀ _ : G.Nontrivial, (G.edgeMeasure : ℝ) ≤ C / t

end DuffinSchaeffer
