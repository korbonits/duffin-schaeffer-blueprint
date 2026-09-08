/- Anatomy of integers: the analytic number theory Mathlib is missing.

   None of this is due to Koukoulopoulos-Maynard; it is the standard toolkit their
   argument assumes. Mathlib has `Nat.totient` with its multiplicativity API and
   `Nat.primesBelow`, but no Mertens theorems (searching for `mertens` finds only an
   unrelated Dedekind-Mertens TODO in a polynomial file) and no divisor-function
   bound. Every node here is upstreamable on its own and none of it depends on the
   rest of this project. -/
import DuffinSchaeffer.Basic
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.ArithmeticFunction.Misc
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

/-- Linear is dominated by exponential, with an explicit constant. The engine of the
divisor bound: applied with `r = 2^ε` it bounds `a + 1` against `2^{aε}`, uniformly in
the prime. -/
theorem exists_linear_le_pow {r : ℝ} (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℕ, ((a : ℝ) + 1) ≤ C * r ^ a := by
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) / r ^ n) atTop (nhds 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 1 hr
  have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / r ^ n) atTop (nhds 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 0 hr
  have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / r ^ n) atTop (nhds 0) := by
    have hsum := h1.add h2
    simp only [add_zero] at hsum
    refine hsum.congr fun n => ?_
    rw [add_div]
  obtain ⟨C, hC⟩ := h.bddAbove_range
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun a => ?_⟩
  have hra : (0 : ℝ) < r ^ a := pow_pos hr0 a
  have hle : ((a : ℝ) + 1) / r ^ a ≤ max C 1 :=
    le_trans (hC (Set.mem_range_self a)) (le_max_left _ _)
  calc ((a : ℝ) + 1) = (((a : ℝ) + 1) / r ^ a) * r ^ a := by field_simp
    _ ≤ max C 1 * r ^ a := by gcongr

theorem add_one_le_two_pow (a : ℕ) : ((a : ℝ) + 1) ≤ 2 ^ a := by
  induction a with
  | zero => norm_num
  | succ k ih =>
    have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    push_cast
    calc ((k : ℝ) + 1 + 1) ≤ 2 ^ k + 1 := by linarith
      _ ≤ 2 ^ k + 2 ^ k := by linarith
      _ = 2 ^ (k + 1) := by ring

theorem rpow_pow_comm {x : ℝ} (hx : 0 ≤ x) (a : ℕ) (ε : ℝ) :
    ((x ^ a : ℝ)) ^ ε = (x ^ ε) ^ a := by
  rw [← Real.rpow_natCast x a, ← Real.rpow_mul hx, ← Real.rpow_natCast (x ^ ε) a,
    ← Real.rpow_mul hx, mul_comm]

/-- **The divisor bound** `d(n) = O_ε(n^ε)`.

The prime-by-prime bound is `a + 1 ≤ w(p) · (p^a)^ε`, where `w(p) = 1` once `p^ε ≥ 2` --
because then `a + 1 ≤ 2^a ≤ (p^ε)^a` -- and `w(p) = C_ε` otherwise, with `C_ε` the
constant of `exists_linear_le_pow` at `r = 2^ε`. Only the primes below a threshold
depending on `ε` contribute a factor, and there are at most `P` of them, so the constant
is `C_ε^P`. -/
theorem divisor_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n : ℕ, 0 < n → ((n : ℕ).divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  classical
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hr : (1 : ℝ) < (2 : ℝ) ^ ε :=
    (Real.one_lt_rpow_iff_of_pos h2).mpr (Or.inl ⟨by norm_num, hε⟩)
  obtain ⟨Cε, hCε0, hCε⟩ := exists_linear_le_pow hr
  set D : ℝ := max Cε 1 with hDdef
  have hD1 : (1 : ℝ) ≤ D := le_max_right _ _
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hD1
  -- primes at least `P` satisfy `p ^ ε ≥ 2`
  obtain ⟨P, hP⟩ : ∃ P : ℕ, ∀ p : ℕ, P ≤ p → (2 : ℝ) ≤ (p : ℝ) ^ ε := by
    obtain ⟨P, hP⟩ := exists_nat_gt ((2 : ℝ) ^ (1 / ε))
    refine ⟨P, fun p hp => ?_⟩
    have hpP : (2 : ℝ) ^ (1 / ε) ≤ (p : ℝ) := le_trans hP.le (by exact_mod_cast hp)
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (1 / ε) := Real.rpow_pos_of_pos h2 _
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
          rw [← Real.rpow_mul (le_of_lt h2), one_div, inv_mul_cancel₀ (ne_of_gt hε),
            Real.rpow_one]
      _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (le_of_lt hpos) hpP (le_of_lt hε)
  refine ⟨D ^ P, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := hn.ne'
  set w : ℕ → ℝ := fun p => if p < P then D else 1 with hwdef
  -- prime-by-prime bound
  have hpt : ∀ p ∈ n.primeFactors,
      ((n.factorization p : ℝ) + 1) ≤ w p * (((p : ℝ) ^ n.factorization p) ^ ε) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
    set a := n.factorization p
    rw [rpow_pow_comm hp0 a ε]
    by_cases hlt : p < P
    · have hwp : w p = D := by simp [hwdef, hlt]
      rw [hwp]
      refine le_trans (hCε a) ?_
      have hbase : (0 : ℝ) ≤ (2 : ℝ) ^ ε := le_of_lt (Real.rpow_pos_of_pos h2 ε)
      have hmono : ((2 : ℝ) ^ ε) ≤ ((p : ℝ) ^ ε) :=
        Real.rpow_le_rpow (le_of_lt h2) hp2 (le_of_lt hε)
      calc Cε * ((2 : ℝ) ^ ε) ^ a ≤ D * ((2 : ℝ) ^ ε) ^ a := by
            gcongr; exact le_max_left _ _
        _ ≤ D * ((p : ℝ) ^ ε) ^ a := by gcongr
    · have hwp : w p = 1 := by simp [hwdef, hlt]
      rw [hwp, one_mul]
      have hpe : (2 : ℝ) ≤ (p : ℝ) ^ ε := hP p (by omega)
      calc ((a : ℝ) + 1) ≤ 2 ^ a := add_one_le_two_pow a
        _ ≤ ((p : ℝ) ^ ε) ^ a := by gcongr
  -- assemble the product bounds
  have hcard : ((n.divisors.card : ℕ) : ℝ)
      = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
    rw [Nat.card_divisors hn0]
    push_cast
    rfl
  have hnpow : (n : ℝ) ^ ε = ∏ p ∈ n.primeFactors, (((p : ℝ) ^ n.factorization p) ^ ε) := by
    rw [Real.finsetProd_rpow _ _ (fun p _ => by positivity) ε]
    congr 1
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hn0
  have hprod : ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ (∏ p ∈ n.primeFactors, w p) * ((n : ℝ) ^ ε) := by
    rw [hnpow, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun p _ => by positivity) (fun p hp => hpt p hp)
  have hw : ∏ p ∈ n.primeFactors, w p ≤ D ^ P := by
    have h1 : ∏ p ∈ n.primeFactors, w p = ∏ _p ∈ n.primeFactors.filter (· < P), D := by
      rw [← Finset.prod_filter_mul_prod_filter_not n.primeFactors (· < P) w]
      have hone : ∏ p ∈ n.primeFactors.filter (fun p => ¬ p < P), w p = 1 :=
        Finset.prod_eq_one fun p hp => by simp [hwdef, (Finset.mem_filter.mp hp).2]
      rw [hone, mul_one]
      exact Finset.prod_congr rfl fun p hp => by simp [hwdef, (Finset.mem_filter.mp hp).2]
    rw [h1, Finset.prod_const]
    refine pow_le_pow_right₀ hD1 ?_
    calc (n.primeFactors.filter (· < P)).card ≤ (Finset.range P).card :=
          Finset.card_le_card fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      _ = P := Finset.card_range P
  rw [hcard]
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ (∏ p ∈ n.primeFactors, w p) * ((n : ℝ) ^ ε) := hprod
    _ ≤ D ^ P * ((n : ℝ) ^ ε) := by gcongr

end DuffinSchaeffer
