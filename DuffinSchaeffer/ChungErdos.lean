/- The second-moment method.

   Gallagher reduces the conjecture to a positive-measure statement, and positive
   measure for a `limsup` comes from the divergence Borel-Cantelli lemma in its
   quasi-independent form. Mathlib has both Borel-Cantelli lemmas
   (`MeasureTheory.measure_limsup_cofinite_eq_zero`,
   `ProbabilityTheory.measure_limsup_eq_one`) but the second assumes genuine
   independence, which the sets `setAq` do not have.

   What is needed instead is the Chung-Erdos inequality and the corollary drawn from
   it. Mathlib has neither: searching the library for `chung`, `paley` or
   `second_moment` returns nothing. Both are short, classical, and belong upstream;
   they are the smallest self-contained piece of this project and a reasonable first
   commit.

   Note the shape of the corollary. It does not ask for quasi-independence over every
   finite set of denominators -- that is false, and its failure is the whole
   difficulty of the conjecture. It asks only for a *sequence* of finite sets carrying
   divergent mass on which the pair correlations are bounded. Producing that sequence
   is what Chapters `Overlap` and `GCDGraph` do. -/
import DuffinSchaeffer.Basic

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

namespace DuffinSchaeffer

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The Chung-Erdos inequality.** For finitely many events,
`(∑ μ Aᵢ)² ≤ μ (⋃ Aᵢ) · ∑ᵢⱼ μ (Aᵢ ∩ Aⱼ)`.

Cauchy-Schwarz applied to the pair `1_{⋃ Aᵢ}` and `∑ 1_{Aᵢ}`. -/
proof_wanted chung_erdos (μ : Measure Ω) [IsFiniteMeasure μ] {ι : Type*} (s : Finset ι)
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    (∑ i ∈ s, μ (A i)) ^ 2 ≤ μ (⋃ i ∈ s, A i) * ∑ i ∈ s, ∑ j ∈ s, μ (A i ∩ A j)

/-- **Divergence Borel-Cantelli, quasi-independent form.** Given a sequence of finite
index sets carrying divergent mass, on each of which the pair correlations are at most
`C` times the square of the first moment, the set of points lying in infinitely many
`A i` has measure at least `C⁻¹`.

This is the only place the constant `C` from the overlap analysis is used, and it is
why a bound with *some* constant suffices: Gallagher upgrades any positive lower bound
to `1`, so `C` never has to be computed. -/
proof_wanted measure_infinite_pos_of_overlap {ι : Type*} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (C : ℝ≥0∞) (hC : C ≠ 0) (hC' : C ≠ ⊤) (S : ℕ → Finset ι)
    (hdiv : Tendsto (fun n ↦ ∑ q ∈ S n, μ (A q)) atTop atTop)
    (hoverlap : ∀ n, ∑ q ∈ S n, ∑ r ∈ S n, μ (A q ∩ A r) ≤ C * (∑ q ∈ S n, μ (A q)) ^ 2) :
    C⁻¹ ≤ μ {x | {i | x ∈ A i}.Infinite}

end DuffinSchaeffer
