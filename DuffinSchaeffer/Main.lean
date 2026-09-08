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
import DuffinSchaeffer.Convergence

open MeasureTheory Set Filter
open scoped ENNReal NNReal Nat

namespace DuffinSchaeffer

/-- **TRANSCRIBE** -- paper §1. The reduction of Theorem 1 to `ψ ≤ 1/2`, in the case
where the truncated series converges.

This gap was hidden inside the prose of Theorem 1's proof until the surrounding nodes
were closed, so it is recorded here as a node of its own rather than left as a sentence.

The reduction one wants is: given `∑ ψ(q)φ(q)/q = ∞`, put `ψ' = min(ψ, 1/2)`; since
`setA ψ' ⊆ setA ψ` (`setA_mono`), it is enough to run the main argument on `ψ'`. That
works whenever `∑ ψ'(q)φ(q)/q = ∞`, and then nothing further is needed.

It can fail. Write `S = {q : ψ(q) > 1/2}`. If `∑ ψ'(q)φ(q)/q < ∞` then on `S` we have
`ψ' = 1/2`, so `∑_{q ∈ S} φ(q)/q < ∞`, while off `S` we have `ψ' = ψ`, so the divergence
must come entirely from `S`:

  `∑_{q ∈ S} ψ(q)φ(q)/q = ∞`  and  `∑_{q ∈ S} φ(q)/q < ∞`.

So `ψ` is unbounded along `S` in a weighted sense, and the truncated series carries none
of the divergence. Whether `setA ψ` is full in that regime is not something the rest of
this development settles: `ψ(q) ≥ q` infinitely often would give it immediately, since
then `setAq ψ q = [0,1]`, but `ψ(q)` can be large without `ψ(q)/q` being large, and the
counting bound `#(numerators q) = φ(q)` does not force a cover -- at `q = 6` the balls
around `1/6` and `5/6` cover `[0,1]` only once `ψ(6) ≥ 2`.

The paper handles this; do not reconstruct it from memory. -/
proof_wanted volume_setA_eq_one_of_untruncated (ψ : ℕ+ → ℝ≥0)
    (hdiv : ¬ Summable fun q : ℕ+ ↦ (ψ q : ℝ) * (φ (q : ℕ) : ℝ) / (q : ℝ))
    (hconv : Summable fun q : ℕ+ ↦
      ((min (ψ q) (1 / 2) : ℝ≥0) : ℝ) * (φ (q : ℕ) : ℝ) / (q : ℝ)) :
    volume (setA ψ) = 1

/-- **The Duffin-Schaeffer conjecture** (Koukoulopoulos-Maynard, Theorem 1).
If `∑ ψ(q) φ(q) / q` diverges then almost every `α ∈ [0,1]` has infinitely many
coprime solutions to `|α - a/q| ≤ ψ(q)/q`. -/
proof_wanted theorem_1 (ψ : ℕ+ → ℝ≥0)
    (hdiv : ¬ Summable fun q : ℕ+ ↦ (ψ q : ℝ) * (φ (q : ℕ) : ℝ) / (q : ℝ)) :
    MeasurableSet (setA ψ) ∧ volume (setA ψ) = 1

/-- **Theorem 2(a)**: the convergence half, without coprimality. Proved; see
`DuffinSchaeffer/Convergence.lean`. -/
theorem theorem_2_a (ψ : ℕ+ → ℝ≥0) (hψ : ∑' q : ℕ+, psiStar ψ q < ⊤) :
    MeasurableSet (setK ψ) ∧ volume (setK ψ) = 0 :=
  ⟨measurableSet_setK ψ, volume_setK_eq_zero ψ hψ⟩

/-- Theorem 2(b): the divergence half, without coprimality. Reduces to Theorem 1 by
applying it to a function built from `ψ⋆`. -/
proof_wanted theorem_2_b (ψ : ℕ+ → ℝ≥0) (hψ : ∑' q : ℕ+, psiStar ψ q = ⊤) :
    MeasurableSet (setK ψ) ∧ volume (setK ψ) = 1

end DuffinSchaeffer
