/- The terminal nodes.

   These three statements are transcribed from
   ImperialCollegeLondon/AnnalsChallenge, file
   `AnnalsChallenge/AnnalsOfMathematics/2020-192-1-DuffinSchaefferConjecture.lean`
   (Katerina Hristova and Kevin Buzzard, Apache 2.0), where they stand as `sorry`.
   Proving them here proves them there.

   Theorem 1 is the conjecture. Theorem 2(a) is the easy convergence half: the first
   Borel-Cantelli lemma applied to the majorant `ψ⋆`, and it needs none of the GCD
   graph machinery -- it is the right place to start writing actual proofs. Theorem
   2(b) is the divergence half and reduces to Theorem 1.

   Corollary 3 of the paper is *not* here; see `Hausdorff.lean` for why. -/
import DuffinSchaeffer.Gallagher
import DuffinSchaeffer.ChungErdos
import DuffinSchaeffer.Overlap

open MeasureTheory Set Filter
open scoped ENNReal NNReal Nat

namespace DuffinSchaeffer

/-- **The Duffin-Schaeffer conjecture** (Koukoulopoulos-Maynard, Theorem 1).
If `∑ ψ(q) φ(q) / q` diverges then almost every `α ∈ [0,1]` has infinitely many
coprime solutions to `|α - a/q| ≤ ψ(q)/q`. -/
proof_wanted theorem_1 (ψ : ℕ+ → ℝ≥0)
    (hdiv : ¬ Summable fun q : ℕ+ ↦ (ψ q : ℝ) * (φ (q : ℕ) : ℝ) / (q : ℝ)) :
    MeasurableSet (setA ψ) ∧ volume (setA ψ) = 1

/-- Theorem 2(a): the convergence half, without coprimality. First Borel-Cantelli. -/
proof_wanted theorem_2_a (ψ : ℕ+ → ℝ≥0) (hψ : ∑' q : ℕ+, psiStar ψ q < ⊤) :
    MeasurableSet (setK ψ) ∧ volume (setK ψ) = 0

/-- Theorem 2(b): the divergence half, without coprimality. Reduces to Theorem 1 by
applying it to a function built from `ψ⋆`. -/
proof_wanted theorem_2_b (ψ : ℕ+ → ℝ≥0) (hψ : ∑' q : ℕ+, psiStar ψ q = ⊤) :
    MeasurableSet (setK ψ) ∧ volume (setK ψ) = 1

end DuffinSchaeffer
