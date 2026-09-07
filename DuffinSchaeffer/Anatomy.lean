/- Anatomy of integers: the analytic number theory Mathlib is missing.

   None of this is due to Koukoulopoulos-Maynard; it is the standard toolkit their
   argument assumes. Mathlib has `Nat.totient` with its multiplicativity API and
   `Nat.primesBelow`, but no Mertens theorems (searching for `mertens` finds only an
   unrelated Dedekind-Mertens TODO in a polynomial file) and no divisor-function
   bound. Every node here is upstreamable on its own and none of it depends on the
   rest of this project. -/
import DuffinSchaeffer.Basic
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Data.Nat.Factorization.Basic

open Filter Asymptotics Finset
open scoped BigOperators Nat

namespace DuffinSchaeffer

/-! ### The Dirichlet hyperbola swap

Summing an arithmetic function over the divisors of every `q ≤ n` counts each `d ≤ n`
exactly `⌊n/d⌋` times. This is the one combinatorial identity the average-order
results below rest on. -/

/-- The divisors of `q` are exactly the `d ≤ n` dividing `q`, when `0 < q ≤ n`. -/
theorem divisors_eq_filter {q n : ℕ} (hq : 0 < q) (hqn : q ≤ n) :
    q.divisors = {d ∈ Ioc 0 n | d ∣ q} := by
  ext d
  simp only [Nat.mem_divisors, mem_filter, mem_Ioc]
  constructor
  · rintro ⟨hd, -⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd hq, (Nat.le_of_dvd hq hd).trans hqn⟩, hd⟩
  · rintro ⟨-, hd⟩
    exact ⟨hd, hq.ne'⟩

/-- **Dirichlet swap.** `∑_{q ≤ n} ∑_{d ∣ q} f d = ∑_{d ≤ n} ⌊n/d⌋ · f d`. -/
theorem sum_sum_divisors (n : ℕ) (f : ℕ → ℝ) :
    ∑ q ∈ Ioc 0 n, ∑ d ∈ q.divisors, f d = ∑ d ∈ Ioc 0 n, ((n / d : ℕ) : ℝ) * f d := by
  rw [Finset.sum_congr rfl fun q hq => by
    rw [divisors_eq_filter (mem_Ioc.mp hq).1 (mem_Ioc.mp hq).2]]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul]

/-! ### Average order of the totient -/

/-- The upper half of Lemma `sum_totient_div_self`: `φ(q)/q ≤ 1` termwise. -/
theorem sum_totient_div_self_le (n : ℕ) :
    ∑ q ∈ Icc 1 n, (φ q : ℝ) / q ≤ n := by
  calc ∑ q ∈ Icc 1 n, (φ q : ℝ) / q ≤ ∑ _q ∈ Icc 1 n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun q hq => ?_
        have hq0 : 0 < q := (mem_Icc.mp hq).1
        rw [div_le_one (by exact_mod_cast hq0)]
        exact_mod_cast Nat.totient_le q
    _ = n := by simp

/-- Gauss' formula in the shape the swap produces. -/
theorem sum_Ioc_cast (n : ℕ) : ∑ q ∈ Ioc 0 n, (q : ℝ) = (n : ℝ) * (((n : ℝ) + 1) / 2) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le _), ih]
    push_cast
    ring

/-- The lower half: `∑_{q ≤ n} φ(q)/q ≥ (n+1)/2`.

The proof is the Dirichlet swap applied to `Nat.sum_totient`. Summing `∑_{d ∣ q} φ d = q`
over `q ≤ n` gives `n(n+1)/2` on the left; the swap turns the same quantity into
`∑_{d ≤ n} ⌊n/d⌋ φ(d) ≤ n ∑_{d ≤ n} φ(d)/d`. Dividing by `n` is the whole argument, and
the constant `1/2` falls out with no analysis at all -- no Moebius function, no Basel
problem, no `1/ζ(2)`. -/
theorem le_sum_totient_div_self {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) + 1) / 2 ≤ ∑ q ∈ Icc 1 n, (φ q : ℝ) / q := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hIcc : Icc 1 n = Ioc 0 n := by ext d; simp [Nat.succ_le_iff]
  have h1 : ∑ q ∈ Ioc 0 n, ∑ d ∈ q.divisors, (φ d : ℝ)
      = (n : ℝ) * (((n : ℝ) + 1) / 2) := by
    rw [← sum_Ioc_cast n]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Nat.cast_sum, Nat.sum_totient]
  have h2 : ∑ d ∈ Ioc 0 n, ((n / d : ℕ) : ℝ) * (φ d : ℝ)
      ≤ (n : ℝ) * ∑ d ∈ Ioc 0 n, (φ d : ℝ) / d := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d _ => ?_
    calc ((n / d : ℕ) : ℝ) * (φ d : ℝ)
        ≤ ((n : ℝ) / (d : ℝ)) * (φ d : ℝ) :=
          mul_le_mul_of_nonneg_right (Nat.cast_div_le) (by positivity)
      _ = (n : ℝ) * ((φ d : ℝ) / d) := by ring
  rw [hIcc]
  refine le_of_mul_le_mul_left ?_ hn0
  calc (n : ℝ) * (((n : ℝ) + 1) / 2)
      = ∑ d ∈ Ioc 0 n, ((n / d : ℕ) : ℝ) * (φ d : ℝ) := by
        rw [← sum_sum_divisors n (fun d => (φ d : ℝ)), h1]
    _ ≤ (n : ℝ) * ∑ d ∈ Ioc 0 n, (φ d : ℝ) / d := h2

/-- **Average order of the totient**, both bounds, with explicit constants
`c = 1/2` and `C = 1`. -/
theorem sum_totient_div_self :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      c * n ≤ ∑ q ∈ Finset.Icc 1 n, (Nat.totient q : ℝ) / q ∧
        ∑ q ∈ Finset.Icc 1 n, (Nat.totient q : ℝ) / q ≤ C * n := by
  refine ⟨1 / 2, 1, by norm_num, by norm_num, fun n hn => ⟨?_, ?_⟩⟩
  · refine le_trans ?_ (le_sum_totient_div_self hn)
    linarith
  · simpa using sum_totient_div_self_le n

/-! ### Still open -/

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

end DuffinSchaeffer
