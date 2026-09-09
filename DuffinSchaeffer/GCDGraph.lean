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

theorem exactPow_iff_factorization {p k n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ExactPow p k n ↔ n.factorization p = k := by
  constructor
  · rintro ⟨h1, h2⟩
    have hle : k ≤ n.factorization p := (Nat.Prime.pow_dvd_iff_le_factorization hp hn).mp h1
    have hlt : ¬ (k + 1 ≤ n.factorization p) := fun h =>
      h2 ((Nat.Prime.pow_dvd_iff_le_factorization hp hn).mpr h)
    omega
  · intro h
    refine ⟨(Nat.Prime.pow_dvd_iff_le_factorization hp hn).mpr (by omega), fun hc => ?_⟩
    have := (Nat.Prime.pow_dvd_iff_le_factorization hp hn).mp hc
    omega

/-- If `p^k ‖ v` and `p^ℓ ‖ w` then `p^{min(k,ℓ)} ‖ gcd(v,w)`. This is the one real
obligation in Definition 6.5(c): condition (ii) of Definition 6.1 for the newly added
prime. -/
theorem ExactPow.gcd {p k l v w : ℕ} (hp : p.Prime) (hv0 : v ≠ 0) (hw0 : w ≠ 0)
    (hv : ExactPow p k v) (hw : ExactPow p l w) :
    ExactPow p (min k l) (Nat.gcd v w) := by
  have hg0 : Nat.gcd v w ≠ 0 := Nat.gcd_ne_zero_left hv0
  rw [exactPow_iff_factorization hp hg0, Nat.factorization_gcd hv0 hw0]
  simp only [Finsupp.inf_apply]
  rw [(exactPow_iff_factorization hp hv0).mp hv, (exactPow_iff_factorization hp hw0).mp hw]

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

open Classical in
/-- `L_t` with the primes of a given set removed. Lemma 8.4 needs `L_t` restricted away
from `R(G)`. -/
noncomputable def LSumAvoiding (t : ℝ) (S : Set ℕ) (a b : ℕ) : ℝ :=
  ∑ p ∈ (coprimePart a b).primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ) ∧ p ∉ S), (1 : ℝ) / p

namespace GCDGraph

open Classical in
/-- The GCD subgraph induced on `V' ⊆ V` and `W' ⊆ W`, keeping the multiplicative data.
Every lemma of section 11 produces a subgraph of exactly this shape, so it is worth having
once: all seven conditions of Definition 6.1 are universally quantified over the vertex
and edge sets, hence inherited by any restriction. -/
noncomputable def induced (G : GCDGraph) (V' W' : Finset ℕ) (hV : V' ⊆ G.V)
    (hW : W' ⊆ G.W) : GCDGraph where
  μ := G.μ
  V := V'
  W := W'
  E := G.edgesOn V' W'
  P := G.P
  f := G.f
  g := G.g
  V_pos := fun v hv => G.V_pos v (hV hv)
  W_pos := fun w hw => G.W_pos w (hW hw)
  E_subset := fun e he => by
    simp only [edgesOn, Finset.mem_filter] at he
    exact ⟨he.2.1, he.2.2⟩
  P_prime := G.P_prime
  f_dvd := fun p hp v hv => G.f_dvd p hp v (hV hv)
  g_dvd := fun p hp w hw => G.g_dvd p hp w (hW hw)
  edge_gcd := fun p hp e he => by
    simp only [edgesOn, Finset.mem_filter] at he
    exact G.edge_gcd p hp e he.1
  f_exact := fun p hp hne v hv => G.f_exact p hp hne v (hV hv)
  g_exact := fun p hp hne w hw => G.g_exact p hp hne w (hW hw)

open Classical in
/-- **Definition 6.5(c)**: the special GCD subgraph `G_{p^k, p^ℓ}`, for a prime `p` not
already in `P`.

Unlike `induced` this *adds* a prime, so three conditions of Definition 6.1 must be checked
for it rather than inherited. Two are immediate from `powPart`; the third, condition (ii),
is `ExactPow.gcd`. -/
noncomputable def special (G : GCDGraph) (p k l : ℕ) (hp : p.Prime) (hpP : p ∉ G.P) :
    GCDGraph where
  μ := G.μ
  V := powPart G.V p k
  W := powPart G.W p l
  E := G.edgesOn (powPart G.V p k) (powPart G.W p l)
  P := insert p G.P
  f := Function.update G.f p k
  g := Function.update G.g p l
  V_pos := fun v hv => G.V_pos v (Finset.mem_filter.mp hv).1
  W_pos := fun w hw => G.W_pos w (Finset.mem_filter.mp hw).1
  E_subset := fun e he => by
    simp only [edgesOn, Finset.mem_filter] at he
    exact ⟨he.2.1, he.2.2⟩
  P_prime := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hqP
    · exact hp
    · exact G.P_prime q hqP
  f_dvd := by
    intro q hq v hv
    rcases Finset.mem_insert.mp hq with rfl | hqP
    · rw [Function.update_self]
      exact (Finset.mem_filter.mp hv).2.1
    · rw [Function.update_of_ne (by rintro rfl; exact hpP hqP)]
      exact G.f_dvd q hqP v (Finset.mem_filter.mp hv).1
  g_dvd := by
    intro q hq w hw
    rcases Finset.mem_insert.mp hq with rfl | hqP
    · rw [Function.update_self]
      exact (Finset.mem_filter.mp hw).2.1
    · rw [Function.update_of_ne (by rintro rfl; exact hpP hqP)]
      exact G.g_dvd q hqP w (Finset.mem_filter.mp hw).1
  edge_gcd := by
    intro q hq e he
    simp only [edgesOn, Finset.mem_filter] at he
    rcases Finset.mem_insert.mp hq with rfl | hqP
    · rw [Function.update_self, Function.update_self]
      have hv := Finset.mem_filter.mp he.2.1
      have hw := Finset.mem_filter.mp he.2.2
      exact ExactPow.gcd hp (G.V_pos _ hv.1).ne' (G.W_pos _ hw.1).ne' hv.2 hw.2
    · rw [Function.update_of_ne (by rintro rfl; exact hpP hqP),
        Function.update_of_ne (by rintro rfl; exact hpP hqP)]
      exact G.edge_gcd q hqP e he.1
  f_exact := by
    intro q hq hne v hv
    rcases Finset.mem_insert.mp hq with rfl | hqP
    · rw [Function.update_self]
      exact (Finset.mem_filter.mp hv).2
    · rw [Function.update_of_ne (by rintro rfl; exact hpP hqP)] at hne ⊢
      rw [Function.update_of_ne (by rintro rfl; exact hpP hqP)] at hne
      exact G.f_exact q hqP hne v (Finset.mem_filter.mp hv).1
  g_exact := by
    intro q hq hne w hw
    rcases Finset.mem_insert.mp hq with rfl | hqP
    · rw [Function.update_self]
      exact (Finset.mem_filter.mp hw).2
    · rw [Function.update_of_ne (by rintro rfl; exact hpP hqP)] at hne ⊢
      rw [Function.update_of_ne (by rintro rfl; exact hpP hqP)] at hne
      exact G.g_exact q hqP hne w (Finset.mem_filter.mp hw).1

open Classical in
theorem special_isSubgraph (G : GCDGraph) (p k l : ℕ) (hp : p.Prime) (hpP : p ∉ G.P) :
    (G.special p k l hp hpP).IsSubgraph G := by
  refine ⟨rfl, fun v hv => (Finset.mem_filter.mp hv).1,
    fun w hw => (Finset.mem_filter.mp hw).1, ?_, Finset.subset_insert _ _, ?_, ?_⟩
  · intro e he
    simp only [special, edgesOn, Finset.mem_filter] at he
    exact he.1
  · intro q hq
    exact Function.update_of_ne (by rintro rfl; exact hpP hq) _ _
  · intro q hq
    exact Function.update_of_ne (by rintro rfl; exact hpP hq) _ _

theorem induced_isSubgraph (G : GCDGraph) (V' W' : Finset ℕ) (hV : V' ⊆ G.V)
    (hW : W' ⊆ G.W) : (G.induced V' W' hV hW).IsSubgraph G := by
  refine ⟨rfl, hV, hW, ?_, Finset.Subset.refl _, fun _ _ => rfl, fun _ _ => rfl⟩
  intro e he
  simp only [induced, edgesOn, Finset.mem_filter] at he
  exact he.1

end GCDGraph

/-! ### Section 11: preparatory lemmas on GCD graphs

The six results §§12-14 draw on. `induced` above is the constructor they all use. -/

/-- **Lemma 11.1** (quality variation for special GCD subgraphs).

An exact identity for the quality ratio of `G_{p^k,p^ℓ}`. The paper calls it immediate
from the definitions; in Lean that means unfolding `quality` on both sides, and the work is
that the `P`-products differ by exactly the new prime's factor.

Statable at last, now that `special` exists. -/
proof_wanted quality_special (G : GCDGraph) (p k l : ℕ) (hp : p.Prime) (hpP : p ∉ G.P)
    (hnt : G.Nontrivial)
    (hV : 0 < G.measureSet (GCDGraph.powPart G.V p k))
    (hW : 0 < G.measureSet (GCDGraph.powPart G.W p l)) :
    (G.special p k l hp hpP).quality / G.quality =
      ((G.measurePairs
          (G.edgesOn (GCDGraph.powPart G.V p k) (GCDGraph.powPart G.W p l)) : ℝ)
        / (G.edgeMeasure : ℝ)) ^ (10 : ℕ) *
      ((G.measureSet G.V : ℝ)
        / (G.measureSet (GCDGraph.powPart G.V p k) : ℝ)) ^ (9 : ℕ) *
      ((G.measureSet G.W : ℝ)
        / (G.measureSet (GCDGraph.powPart G.W p l) : ℝ)) ^ (9 : ℕ) *
      ((p : ℝ) ^ ((k - l) + (l - k)) /
        ((1 - (if k = l ∧ 1 ≤ k then (1 : ℝ) else 0) / (p : ℝ)) ^ (2 : ℕ) *
          (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ (10 : ℕ)))

/-- **Lemma 11.2** (one subgraph must have limited quality loss). Pigeonhole across a
product of partitions: some cell keeps a `(IJ)⁻¹⁰` share of the quality and a `(IJ)⁻¹`
share of the density. -/
proof_wanted pigeonhole_subgraph (G : GCDGraph) (hδ : 0 < G.edgeDensity)
    {I J : ℕ} (Vs : Fin I → Finset ℕ) (Ws : Fin J → Finset ℕ)
    (hVpart : G.V = Finset.univ.biUnion Vs)
    (hWpart : G.W = Finset.univ.biUnion Ws) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ 0 < G'.edgeDensity ∧
      (∃ i, G'.V = Vs i) ∧ (∃ j, G'.W = Ws j) ∧
      G.quality / ((I * J : ℕ) : ℝ) ^ (10 : ℕ) ≤ G'.quality ∧
      (G.edgeDensity : ℝ) / ((I * J : ℕ) : ℝ) ≤ (G'.edgeDensity : ℝ)

/-- **Lemma 11.5** (few edges between small sets). Either small sets carry few edges, or
there is a quality-increasing subgraph on strictly smaller vertex sets. -/
proof_wanted few_edges_between_small_sets (G : GCDGraph) (hδ : 0 < G.edgeDensity)
    (η : ℝ) (hη : η ∈ Set.Ioo (0 : ℝ) 1) :
    (∀ A ⊆ G.V, ∀ B ⊆ G.W,
        (G.measureSet A : ℝ) ≤ η * (G.measureSet G.V : ℝ) →
        (G.measureSet B : ℝ) ≤ η * (G.measureSet G.W : ℝ) →
        (G.measurePairs (G.edgesOn A B) : ℝ) ≤ η ^ ((9 : ℝ) / 5) * (G.edgeMeasure : ℝ))
      ∨ ∃ G' : GCDGraph, G'.IsSubgraph G ∧ G.quality < G'.quality ∧
          G'.V ⊂ G.V ∧ G'.W ⊂ G.W

/-- **Lemma 11.6** (subgraph with few edges between all small sets). Lemma 11.5 iterated;
it terminates because the vertex sets strictly shrink. -/
proof_wanted no_small_set_edges (G : GCDGraph) (hδ : 0 < G.edgeDensity)
    (η : ℝ) (hη : η ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ 0 < G'.edgeDensity ∧
      G.quality ≤ G'.quality ∧ 0 < G.quality ∧
      ∀ A ⊆ G'.V, ∀ B ⊆ G'.W,
        (G'.measureSet A : ℝ) ≤ η * (G'.measureSet G'.V : ℝ) →
        (G'.measureSet B : ℝ) ≤ η * (G'.measureSet G'.W : ℝ) →
        (G'.measurePairs (G'.edgesOn A B) : ℝ) ≤ η ^ ((9 : ℝ) / 5) * (G'.edgeMeasure : ℝ)

/-! ### Section 8: the three iterative propositions

Proposition 7.1 is reduced in §8 to Propositions 8.1-8.3 together with Lemmas 8.4 and
8.5. Sections 12-14 prove the propositions, §§9-10 the lemmas, §11 the preparatory
material. All five are transcribed below; none is proved. -/

/-- **Proposition 8.1** (iteration when `R♭(G) ≠ ∅`). Adding a prime of `R♭(G)` to `P`
buys a factor `2ᴺ`, where `N` counts the added primes at which `f` and `g` differ. -/
proof_wanted iteration_of_Rflat_nonempty (G : GCDGraph) (hδ : 0 < G.edgeDensity)
    (hR : ∀ p ∈ G.R, (10 : ℝ) ^ (2000 : ℕ) < p) (hflat : G.Rflat.Nonempty) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ 0 < G'.edgeDensity ∧
      G.P ⊂ G'.P ∧ ↑G'.P ⊆ ↑G.P ∪ G.R ∧ G'.R ⊂ G.R ∧
      (2 : ℝ) ^ ((G'.P \ G.P).filter (fun p => G'.f p ≠ G'.g p)).card
        ≤ min 1 ((G'.edgeDensity : ℝ) / (G.edgeDensity : ℝ)) * (G'.quality / G.quality)

/-- **Proposition 8.2** (iteration when `R♭(G) = ∅`). Here one only asks that the quality
not decrease. -/
proof_wanted iteration_of_Rflat_empty (G : GCDGraph) (hδ : 0 < G.edgeDensity)
    (hR : ∀ p ∈ G.R, (10 : ℝ) ^ (2000 : ℕ) < p) (hflat : G.Rflat = ∅)
    (hsharp : G.Rsharp.Nonempty) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧
      G.P ⊂ G'.P ∧ ↑G'.P ⊆ ↑G.P ∪ G.R ∧ G'.R ⊂ G.R ∧ G.quality ≤ G'.quality

/-- **Proposition 8.3** (bounded quality loss for small primes). The small primes are
dealt with once and for all, at a cost that is enormous but absolute. -/
proof_wanted quality_loss_small_primes (G : GCDGraph) (hP : G.P = ∅)
    (hδ : 0 < G.edgeDensity) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ 0 < G'.edgeDensity ∧
      (∀ p ∈ G'.P, (p : ℝ) ≤ (10 : ℝ) ^ (2000 : ℕ)) ∧
      (∀ p ∈ G'.R, (10 : ℝ) ^ (2000 : ℕ) < p) ∧
      (10 : ℝ) ^ (-((10 : ℝ) ^ (3000 : ℕ)))
        ≤ min 1 ((G'.edgeDensity : ℝ) / (G.edgeDensity : ℝ)) * (G'.quality / G.quality)

/-- **Lemma 8.4** (removing the effect of `R(G)` from `L_t`). Strengthens
`L_t(v,w) ≥ 10` to a bound over primes outside `R(G)`, at the cost of half the quality. -/
proof_wanted cosmetic_lemma (G : GCDGraph) (t : ℝ) (ht : 300 ≤ t)
    (hδ : 0 < G.edgeDensity) (hflat : G.Rflat = ∅)
    (hδt : (10 / t) ^ (50 : ℕ) ≤ (G.edgeDensity : ℝ))
    (hE : ∀ e ∈ G.E, 10 ≤ LSum t e.1 e.2) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ G'.V = G.V ∧ G'.W = G.W ∧ G'.P = G.P ∧
      G.quality / 2 ≤ G'.quality ∧ 0 < G.quality ∧
      ∀ e ∈ G'.E, 5 ≤ LSumAvoiding t G.R e.1 e.2

/-- **Lemma 8.5** (subgraph with high-degree vertices). Regularises both sides without
losing quality or density, which is how conclusions (b) and (c) of Proposition 7.1 are
obtained from (a) and (d) alone. -/
proof_wanted high_degree_subgraph (G : GCDGraph) (hδ : 0 < G.edgeDensity) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ 0 < G'.edgeDensity ∧ G'.P = G.P ∧
      G.quality ≤ G'.quality ∧ G.edgeDensity ≤ G'.edgeDensity ∧
      (∀ v ∈ G'.V, 9 * (G'.edgeDensity : ℝ) / 10 * (G'.measureSet G'.W : ℝ)
        ≤ (G'.measureSet (G'.neighborsV v) : ℝ)) ∧
      (∀ w ∈ G'.W, 9 * (G'.edgeDensity : ℝ) / 10 * (G'.measureSet G'.V : ℝ)
        ≤ (G'.measureSet (G'.neighborsW w) : ℝ))

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
