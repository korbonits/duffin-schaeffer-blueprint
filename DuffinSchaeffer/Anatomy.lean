/- Anatomy of integers: the analytic number theory Mathlib is missing.

   None of this is due to Koukoulopoulos-Maynard; it is the standard toolkit their
   argument assumes. Mathlib has `Nat.totient` with its multiplicativity API and
   `Nat.primesBelow`, but no Mertens theorems (searching for `mertens` finds only an
   unrelated Dedekind-Mertens TODO in a polynomial file) and no divisor-function
   bound. Every node here is upstreamable on its own and none of it depends on the
   rest of this project, so this file is the natural place for a second contributor
   to start. -/
import DuffinSchaeffer.Basic
import Mathlib.NumberTheory.SmoothNumbers

open Filter Asymptotics
open scoped BigOperators

namespace DuffinSchaeffer

/-- **Mertens' second theorem.** `∑_{p < n} 1/p = log log n + M + O(1/log n)`. -/
proof_wanted mertens_second :
    ∃ M : ℝ, (fun n : ℕ ↦ (∑ p ∈ Nat.primesBelow n, (1 : ℝ) / p)
        - Real.log (Real.log n) - M) =O[atTop] fun n : ℕ ↦ 1 / Real.log n

/-- **Mertens' third theorem**, in the two-sided form the overlap estimates use:
`∏_{p < n} (1 - 1/p)⁻¹ ≍ log n`. The sharp constant `e^γ` is not needed anywhere. -/
proof_wanted mertens_third :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
      c * Real.log n ≤ ∏ p ∈ Nat.primesBelow n, (1 - (1 : ℝ) / p)⁻¹ ∧
        ∏ p ∈ Nat.primesBelow n, (1 - (1 : ℝ) / p)⁻¹ ≤ C * Real.log n

/-- The divisor bound `d(n) = O_ε(n^ε)`. -/
proof_wanted divisor_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n : ℕ, 0 < n → ((n : ℕ).divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε

/-- `∑_{q ≤ n} φ(q)/q ≍ n`: the totient is of average order `q · 6/π²`, and in
particular `φ(q)/q` is bounded below on a positive proportion of `q`. Only the
two-sided bound is used. -/
proof_wanted sum_totient_div_self :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      c * n ≤ ∑ q ∈ Finset.Icc 1 n, (Nat.totient q : ℝ) / q ∧
        ∑ q ∈ Finset.Icc 1 n, (Nat.totient q : ℝ) / q ≤ C * n

end DuffinSchaeffer
