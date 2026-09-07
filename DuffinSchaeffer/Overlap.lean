/- Overlap estimates: from pair correlations to a usable subsequence.

   Two things happen in this chapter.

   The first is classical and is not due to Koukoulopoulos-Maynard: the
   Pollington-Vaughan estimate bounding `μ(A_q ∩ A_r)` in terms of
   `μ(A_q) μ(A_r)` and a product over the primes dividing `qr/gcd(q,r)²` above a
   threshold depending on `q`, `r` and `ψ`. It is charted in the blueprint as a
   `\notready` node rather than stated in Lean, because the threshold carries
   normalisations that must be transcribed from the source (Pollington and Vaughan,
   Mathematika 37 (1990), 190-200; quoted in the paper's §2) and a Lean statement got
   slightly wrong would be worse than a visible gap.

   The second is the interface the rest of the project consumes, and it *is* stated
   here. Note carefully what it does and does not claim. It does not say the
   denominators are quasi-independent -- over all finite sets that is false, and its
   failure is the difficulty of the conjecture. It says that when the series
   diverges one can *select* a sequence of finite sets of denominators, still carrying
   divergent mass, on which the pair correlations are bounded by a constant times the
   square of the first moment. Producing that selection is what the GCD graph
   iteration is for. -/
import DuffinSchaeffer.GCDGraph
import DuffinSchaeffer.Anatomy

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators

namespace DuffinSchaeffer

/-- **The technical core of Koukoulopoulos-Maynard**, in the form the second-moment
argument consumes. Everything in the paper from §2 to the end goes into proving this.

The constant `C` is never computed: by `measure_infinite_pos_of_overlap` it yields a
lower bound `C⁻¹ > 0` on the measure, and Gallagher's zero-one law then upgrades that
to `1`. -/
proof_wanted exists_quasi_independent_subsets (ψ : ℕ+ → ℝ≥0)
    (hψ : ∀ q, (ψ q : ℝ) ≤ 1 / 2)
    (hdiv : ∑' q : ℕ+, volume (setAq ψ q) = ⊤) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧ ∃ S : ℕ → Finset ℕ+,
      Tendsto (fun n ↦ ∑ q ∈ S n, volume (setAq ψ q)) atTop atTop ∧
        ∀ n, ∑ q ∈ S n, ∑ r ∈ S n, volume (setAq ψ q ∩ setAq ψ r)
          ≤ C * (∑ q ∈ S n, volume (setAq ψ q)) ^ 2

end DuffinSchaeffer
