/- Corollary 3, and why it is out of scope.

   Corollary 3 of the paper computes the Hausdorff dimension of `setA ψ` as
   `min(s, 1)`, where `s` is the critical exponent of `∑ φ(q) (ψ(q)/q)^β`. It does not
   follow from Theorem 1 by soft arguments: the passage from "full Lebesgue measure"
   to "full Hausdorff dimension" runs through the mass transference principle of
   Beresnevich and Velani (Annals 164 (2006), 971-992), which Mathlib does not have --
   searching the library for `massTransference` or `beresnevich` returns nothing.

   That principle is a substantial standalone formalisation with its own prerequisite
   stack (Hausdorff content, a Cantor-set construction, the ubiquity framework). It is
   a separate project that happens to share a statement file, and folding it into the
   critical path would roughly double the work while adding nothing to the conjecture
   itself.

   So this file states the two nodes and stops. Mathlib does have `dimH` and the
   Hausdorff measures `μH[d]` with a usable API
   (`Mathlib/Topology/MetricSpace/HausdorffDimension.lean`,
   `Mathlib/MeasureTheory/Measure/Hausdorff.lean`), so the landing site exists. -/
import DuffinSchaeffer.Main

open MeasureTheory Set
open scoped NNReal ENNReal

namespace DuffinSchaeffer

/-- The critical exponent of Corollary 3. -/
noncomputable def critExp (ψ : ℕ+ → ℝ≥0) : ℝ≥0 :=
  sInf {β : ℝ≥0 | Summable fun q : ℕ+ ↦ (Nat.totient (q : ℕ) : ℝ) * ((ψ q : ℝ) / (q : ℝ)) ^ (β : ℝ)}

/-- Corollary 3: the Hausdorff dimension of `setA ψ`. -/
proof_wanted corollary_3 (ψ : ℕ+ → ℝ≥0) (hψ : ∀ n, (ψ n : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    dimH (setA ψ) = min (critExp ψ : ℝ≥0∞) 1

end DuffinSchaeffer
