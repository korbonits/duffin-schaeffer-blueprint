/- Overlap estimates: from pair correlations to a usable subsequence.

   Two things happen in this chapter.

   The first is classical and is not due to Koukoulopoulos-Maynard: the Pollington-Vaughan
   estimate, quoted there as Lemma 5.3 and attributed to [Pollington-Vaughan, Mathematika
   37 (1990), pp. 195-196]. With `M(q,r) := max(r ψ(q), q ψ(r))` it reads, for `q ≠ r`,

     λ(A_q ∩ A_r) / (λ(A_q) λ(A_r))  ≪  1[M(q,r) ≥ gcd(q,r)] ·
        ∏ over p | qr/gcd(q,r)^2 with p > M(q,r)/gcd(q,r)  of  (1 + 1/p).

   Note what an earlier draft of this file got wrong by guessing: the threshold is
   `M(q,r)/gcd(q,r)`, not a `ψ`-dependent quantity pulled from memory; the product is of
   `(1 + 1/p)`, not `(1 - 1/p)⁻¹`; and there is an indicator, so the two sets are simply
   disjoint unless `M(q,r) ≥ gcd(q,r)`.

   The second is the interface the rest of the project consumes, and it *is* stated here.
   The paper's own form is sharper and concrete (Proposition 5.4): writing

     L_t(a,b) := ∑ over p | ab/gcd(a,b)^2 with p ≥ t  of  1/p            (paper (5.1))
     E_t := {(v,w) ∈ (Z ∩ [X,Y])^2 : gcd(v,w) ≥ M(v,w)/t and L_t(v,w) ≥ 10},

   it asserts that for `Y ≥ X ≥ 1` with `∑_{X ≤ q ≤ Y} ψ(q)φ(q)/q ∈ [1,2]`,

     ∑ over (v,w) ∈ E_t  of  (φ(v)ψ(v)/v)(φ(w)ψ(w)/w)  ≪  1/t.

   The denominators are therefore taken from a window `[X, Y]` with `X → ∞` and `Y`
   minimal making the first moment lie in `[1,2]`, and the conclusion needed is
   `λ(⋃_{X ≤ q ≤ Y} A_q) ≫ 1` uniformly in `X`. In particular the index sets do escape
   every initial segment, which settles a question raised earlier in this development --
   though `measure_infinite_pos_of_overlap` no longer needs that. -/
import DuffinSchaeffer.GCDGraph
import DuffinSchaeffer.Anatomy

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators

namespace DuffinSchaeffer

/-- **The technical core of Koukoulopoulos-Maynard**, in the form the second-moment
argument consumes. Everything in the paper from §2 to the end goes into proving this.

The constant `C` is never computed: by `measure_infinite_pos_of_overlap` it yields a
lower bound `C⁻¹ > 0` on the measure, and Gallagher's zero-one law then upgrades that
to `1`.

No hypothesis beyond what is stated here is needed downstream. An earlier version of
this file asked whether the `S n` could be taken to escape every initial segment, since
the second-moment lemma was at that point proved only in that form; that is now moot --
`measure_infinite_pos_of_overlap` drops the escape hypothesis, so nothing in this
development rests on an unverified reading of the paper's construction. -/
proof_wanted exists_quasi_independent_subsets (ψ : ℕ+ → ℝ≥0)
    (hψ : ∀ q, (ψ q : ℝ) ≤ 1 / 2)
    (hdiv : ∑' q : ℕ+, volume (setAq ψ q) = ⊤) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧ ∃ S : ℕ → Finset ℕ+,
      Tendsto (fun n ↦ ∑ q ∈ S n, volume (setAq ψ q)) atTop atTop ∧
        ∀ n, ∑ q ∈ S n, ∑ r ∈ S n, volume (setAq ψ q ∩ setAq ψ r)
          ≤ C * (∑ q ∈ S n, volume (setAq ψ q)) ^ 2

end DuffinSchaeffer
