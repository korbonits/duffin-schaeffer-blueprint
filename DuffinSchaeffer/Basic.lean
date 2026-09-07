/- The approximation sets, and the statements to be proved.

   Koukoulopoulos and Maynard, "On the Duffin-Schaeffer conjecture",
   Annals of Mathematics 192 (2020), 251-307.

   The definitions `Approximates`, `setA`, `setK` and `psiStar` are transcribed
   from the statement-only formalisation in ImperialCollegeLondon/AnnalsChallenge
   (`AnnalsChallenge/AnnalsOfMathematics/2020-192-1-DuffinSchaefferConjecture.lean`,
   Katerina Hristova and Kevin Buzzard, Apache 2.0), so that the terminal nodes of
   this blueprint are literally that repository's sorried statements. Discharging
   them here discharges them there.

   Nothing in this file is proved: every node is a `proof_wanted`, so the project
   contains no `sorry` and declares no axiom. -/
import Mathlib.NumberTheory.WellApproximable
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Batteries.Util.ProofWanted

open MeasureTheory Set Filter
open scoped NNReal ENNReal Nat

namespace DuffinSchaeffer

/-- Inequality (1.7): `|α - a / q| ≤ ψ q / q`. -/
def Approximates (ψ : ℕ+ → ℝ≥0) (α : ℝ) (a : ℕ) (q : ℕ+) : Prop :=
  |α - a / q| ≤ ψ q / q

/-- The set of `α ∈ [0,1]` approximable to within `ψ q / q` by a reduced fraction of
denominator exactly `q`. This is the `q`-th set whose `limsup` the conjecture is about. -/
def setAq (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : Set ℝ :=
  {α ∈ Set.Icc (0 : ℝ) 1 | ∃ a : ℕ, Nat.Coprime a q ∧ Approximates ψ α a q}

/-- The set `𝒜` of Theorem 1: those `α ∈ [0,1]` admitting infinitely many coprime
solutions to (1.7). -/
def setA (ψ : ℕ+ → ℝ≥0) : Set ℝ :=
  {α ∈ Set.Icc (0 : ℝ) 1 | {(a, q) : ℕ × ℕ+ | Nat.Coprime a q ∧ Approximates ψ α a q}.Infinite}

/-- The set `𝒦` of Theorem 2: as `setA`, but without the coprimality constraint and with
the numerator confined to `0 ≤ a ≤ q`. -/
def setK (ψ : ℕ+ → ℝ≥0) : Set ℝ :=
  {α ∈ Set.Icc (0 : ℝ) 1 | {(a, q) : ℕ × ℕ+ | a ≤ q ∧ Approximates ψ α a q}.Infinite}

/-- `ψ⋆ q = φ(q) · sup {ψ n / n : q ∣ n}`, the majorant of Theorem 2. -/
noncomputable def psiStar (ψ : ℕ+ → ℝ≥0) : ℕ+ → ℝ≥0∞ :=
  fun q ↦ φ q * sSup {r : ℝ≥0∞ | ∃ n : ℕ+, q ∣ n ∧ r = ψ n / n}

/-- The measure-theoretic size of a single `setAq`. Each of the `φ(q)` admissible
numerators contributes an interval of length `2 ψ(q) / q`, and for `ψ q ≤ 1/2` those
intervals are disjoint, so the bound below is an equality. -/
proof_wanted measurableSet_setAq (ψ : ℕ+ → ℝ≥0) (q : ℕ+) :
    MeasurableSet (setAq ψ q)

proof_wanted volume_setAq_le (ψ : ℕ+ → ℝ≥0) (q : ℕ+) :
    volume (setAq ψ q) ≤ ENNReal.ofReal (2 * (ψ q : ℝ) * (φ (q : ℕ) : ℝ) / (q : ℝ))

proof_wanted volume_setAq (ψ : ℕ+ → ℝ≥0) (q : ℕ+) (hψ : (ψ q : ℝ) ≤ 1 / 2) :
    volume (setAq ψ q) = ENNReal.ofReal (2 * (ψ q : ℝ) * (φ (q : ℕ) : ℝ) / (q : ℝ))

/-- `setA` is the `limsup` of the `setAq`. The hypothesis `ψ ≤ 1/2` is what confines the
numerator of a solution to `0 ≤ a ≤ q`, which is why `setA` counts pairs while `setAq`
counts denominators. -/
proof_wanted mem_setA_iff (ψ : ℕ+ → ℝ≥0) (hψ : ∀ q, (ψ q : ℝ) ≤ 1 / 2) (α : ℝ) :
    α ∈ setA ψ ↔ α ∈ Set.Icc (0 : ℝ) 1 ∧ {q : ℕ+ | α ∈ setAq ψ q}.Infinite

proof_wanted measurableSet_setA (ψ : ℕ+ → ℝ≥0) :
    MeasurableSet (setA ψ)

proof_wanted measurableSet_setK (ψ : ℕ+ → ℝ≥0) :
    MeasurableSet (setK ψ)

/-- The divergence hypothesis of Theorem 1, in the form the second-moment argument
consumes: the measures of the `setAq` are not summable. -/
proof_wanted not_summable_volume_setAq (ψ : ℕ+ → ℝ≥0) (hψ : ∀ q, (ψ q : ℝ) ≤ 1 / 2)
    (hdiv : ¬ Summable fun q : ℕ+ ↦ (ψ q : ℝ) * (φ (q : ℕ) : ℝ) / (q : ℝ)) :
    ∑' q : ℕ+, volume (setAq ψ q) = ⊤

/-- Reduction to `ψ ≤ 1/2`. If `ψ q > 1/2` for infinitely many `q` the conclusion of
Theorem 1 is immediate, since a single such `q` already covers `[0,1]`; so the
truncation `min ψ (1/2)` loses nothing. -/
proof_wanted setA_truncate (ψ : ℕ+ → ℝ≥0) :
    volume (setA ψ) = 1 ∨ volume (setA fun q ↦ min (ψ q) (1 / 2)) = volume (setA ψ)

end DuffinSchaeffer
