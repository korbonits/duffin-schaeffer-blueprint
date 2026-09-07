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
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

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

/-- `Ψ(q) = sup {ψ n / n : q ∣ n}`, the radius attached to a denominator `q` after
reduction to lowest terms. Split out of `psiStar` because every use of the majorant
needs the supremum on its own. -/
noncomputable def psiSup (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : ℝ≥0∞ :=
  sSup {r : ℝ≥0∞ | ∃ n : ℕ+, q ∣ n ∧ r = ψ n / n}

/-- `ψ⋆ q = φ(q) · Ψ(q)`, the majorant of Theorem 2. -/
noncomputable def psiStar (ψ : ℕ+ → ℝ≥0) : ℕ+ → ℝ≥0∞ :=
  fun q ↦ φ q * psiSup ψ q

theorem psiStar_eq (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : psiStar ψ q = φ (q : ℕ) * psiSup ψ q := rfl

theorem le_psiSup (ψ : ℕ+ → ℝ≥0) {q n : ℕ+} (h : q ∣ n) :
    (ψ n : ℝ≥0∞) / n ≤ psiSup ψ q :=
  le_sSup ⟨n, h, rfl⟩

theorem self_div_le_psiSup (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : (ψ q : ℝ≥0∞) / q ≤ psiSup ψ q :=
  le_psiSup ψ dvd_rfl

theorem one_le_totient (q : ℕ+) : (1 : ℝ≥0∞) ≤ (φ (q : ℕ) : ℝ≥0∞) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.totient_pos.mpr q.pos).ne'

/-- `Ψ ≤ ψ⋆` pointwise, because `φ(q) ≥ 1`. So the convergence hypothesis of Theorem 2
controls the radii as well as the weighted radii -- which is what makes the covering
argument work at all. -/
theorem psiSup_le_psiStar (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : psiSup ψ q ≤ psiStar ψ q :=
  le_mul_of_one_le_left (by simp) (one_le_totient q)

theorem tsum_psiSup_lt_top (ψ : ℕ+ → ℝ≥0) (h : ∑' q : ℕ+, psiStar ψ q < ⊤) :
    ∑' q : ℕ+, psiSup ψ q < ⊤ :=
  lt_of_le_of_lt (ENNReal.tsum_le_tsum (psiSup_le_psiStar ψ)) h

/-! ### The measure of a single `setAq`

Each of the `φ(q)` admissible numerators contributes an interval of length `2 ψ(q) / q`,
and for `ψ q ≤ 1/2` those intervals are disjoint and contained in `[0,1]`. -/

/-- `setAq` as an explicit union of closed balls: `α` is within `ψ(q)/q` of a reduced
fraction with denominator `q`. -/
theorem setAq_eq (ψ : ℕ+ → ℝ≥0) (q : ℕ+) :
    setAq ψ q = Set.Icc 0 1 ∩
      ⋃ a ∈ {a : ℕ | Nat.Coprime a q}, Metric.closedBall ((a : ℝ) / q) ((ψ q : ℝ) / q) := by
  ext α
  simp only [setAq, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iUnion, Metric.mem_closedBall,
    Real.dist_eq, exists_prop, Approximates]

theorem measurableSet_setAq (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : MeasurableSet (setAq ψ q) := by
  rw [setAq_eq]
  exact measurableSet_Icc.inter
    (MeasurableSet.biUnion (Set.to_countable _) fun a _ => measurableSet_closedBall)

/-- The admissible numerators. Under `ψ q ≤ 1/2` no numerator outside `0 ≤ a ≤ q` can
put a point of `[0,1]` within `ψ(q)/q` of `a/q`. -/
noncomputable def numerators (q : ℕ+) : Finset ℕ :=
  {a ∈ Finset.range ((q : ℕ) + 1) | Nat.Coprime a q}

/-- Under `ψ q ≤ 1/2`, a solution with `α ∈ [0,1]` has numerator at most `q`. This is the
one place the truncation hypothesis does real work, and both the covering bound and the
pair-versus-denominator count below rest on it. -/
theorem le_of_approximates {ψ : ℕ+ → ℝ≥0} {α : ℝ} {a : ℕ} {q : ℕ+}
    (hψ : (ψ q : ℝ) ≤ 1 / 2) (hα : α ∈ Set.Icc (0 : ℝ) 1) (h : Approximates ψ α a q) :
    a ≤ (q : ℕ) := by
  have hq0 : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.pos
  have e1 : (a : ℝ) / ((q : ℕ) : ℝ) * ((q : ℕ) : ℝ) = a := div_mul_cancel₀ _ (ne_of_gt hq0)
  have e2 : (ψ q : ℝ) / ((q : ℕ) : ℝ) * ((q : ℕ) : ℝ) = (ψ q : ℝ) :=
    div_mul_cancel₀ _ (ne_of_gt hq0)
  have h3 := mul_le_mul_of_nonneg_right (abs_le.mp h).1 hq0.le
  rw [neg_mul, e2, sub_mul, e1] at h3
  have h4 : α * ((q : ℕ) : ℝ) ≤ 1 * ((q : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hα.2 hq0.le
  have ha : (a : ℝ) < ((q : ℕ) : ℝ) + 1 := by nlinarith
  have : a < (q : ℕ) + 1 := by exact_mod_cast ha
  omega

theorem setAq_subset (ψ : ℕ+ → ℝ≥0) (q : ℕ+) (hψ : (ψ q : ℝ) ≤ 1 / 2) :
    setAq ψ q ⊆ ⋃ a ∈ numerators q, Metric.closedBall ((a : ℝ) / q) ((ψ q : ℝ) / q) := by
  intro α hα
  rw [setAq_eq] at hα
  obtain ⟨hα01, hu⟩ := hα
  simp only [Set.mem_iUnion, Metric.mem_closedBall, Real.dist_eq, exists_prop,
    Set.mem_ofPred_eq] at hu
  obtain ⟨a, hcop, hball⟩ := hu
  simp only [Set.mem_iUnion, numerators, Finset.mem_filter, Finset.mem_range, exists_prop,
    Metric.mem_closedBall, Real.dist_eq]
  exact ⟨a, ⟨Nat.lt_succ_of_le (le_of_approximates hψ hα01 hball), hcop⟩, hball⟩

/-- For `q ≥ 2` the admissible numerators are exactly the `φ(q)` residues counted by the
totient: `a = 0` and `a = q` are both excluded by coprimality. -/
theorem card_numerators {q : ℕ+} (hq : 2 ≤ (q : ℕ)) : (numerators q).card = φ (q : ℕ) := by
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext a
  simp only [numerators, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨ha, hcop⟩
    refine ⟨?_, Nat.coprime_comm.mp hcop⟩
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp ha) with h | h
    · exact h
    · exfalso
      rw [h] at hcop
      have : (q : ℕ) = 1 := by simpa [Nat.Coprime] using hcop
      omega
  · rintro ⟨ha, hcop⟩
    exact ⟨Nat.lt_succ_of_lt ha, Nat.coprime_comm.mp hcop⟩

/-- The `q = 1` case, where the two intervals meeting `[0,1]` are the truncated halves
around `0` and `1`; together they have length exactly `2 ψ(1) = 2 ψ(1) φ(1) / 1`, so the
general bound holds but the counting argument for `q ≥ 2` does not apply. -/
theorem volume_setAq_le_one (ψ : ℕ+ → ℝ≥0) (hψ : (ψ 1 : ℝ) ≤ 1 / 2) :
    volume (setAq ψ 1) ≤ ENNReal.ofReal (2 * (ψ 1 : ℝ)) := by
  have hsub : setAq ψ 1 ⊆ Set.Icc 0 (ψ 1 : ℝ) ∪ Set.Icc (1 - (ψ 1 : ℝ)) 1 := by
    intro α hα
    rw [setAq_eq] at hα
    obtain ⟨hα01, hu⟩ := hα
    simp only [Set.mem_iUnion, Metric.mem_closedBall, Real.dist_eq, exists_prop,
      Set.mem_ofPred_eq, PNat.one_coe, Nat.cast_one, div_one] at hu
    obtain ⟨a, -, hball⟩ := hu
    have hb := abs_le.mp hball
    match a with
    | 0 => exact Or.inl ⟨hα01.1, by simpa using hb.2⟩
    | 1 => exact Or.inr ⟨by push_cast at hb ⊢; linarith [hb.1], hα01.2⟩
    | (n + 2) =>
      exfalso
      have : ((n : ℝ) + 2) ≤ α + (ψ 1 : ℝ) := by push_cast at hb ⊢; linarith [hb.1]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith [hα01.2]
  calc volume (setAq ψ 1) ≤ volume (Set.Icc 0 (ψ 1 : ℝ) ∪ Set.Icc (1 - (ψ 1 : ℝ)) 1) :=
        measure_mono hsub
    _ ≤ volume (Set.Icc (0 : ℝ) (ψ 1 : ℝ)) + volume (Set.Icc (1 - (ψ 1 : ℝ)) 1) :=
        measure_union_le _ _
    _ = ENNReal.ofReal (2 * (ψ 1 : ℝ)) := by
        rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_add (by simp) (by simp)]
        congr 1
        ring

/-- **The measure of a single `setAq`.**

Note the hypothesis. The bound was originally stated with no constraint on `ψ`, but the
counting argument needs one: for large `ψ(q)` the numerators `a > q` also put mass in
`[0,1]`, and at `q = 1` the numerators `0` and `1` are both coprime to `1` while
`φ(1) = 1`, so `#(numerators q) = φ(q)` fails there. Under `ψ q ≤ 1/2` -- which is what
`setA_truncate` supplies, and which every statement downstream of it assumes anyway --
both problems disappear. -/
theorem volume_setAq_le (ψ : ℕ+ → ℝ≥0) (q : ℕ+) (hψ : (ψ q : ℝ) ≤ 1 / 2) :
    volume (setAq ψ q) ≤ ENNReal.ofReal (2 * (ψ q : ℝ) * (φ (q : ℕ) : ℝ) / ((q : ℕ) : ℝ)) := by
  have hq0 : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.pos
  by_cases hq1 : q = 1
  · -- `q = 1`
    subst hq1
    simpa using volume_setAq_le_one ψ hψ
  · -- `q ≥ 2`
    have hq2 : 2 ≤ (q : ℕ) := by
      have h1 : (q : ℕ) ≠ 1 := fun h => hq1 (PNat.coe_eq_one_iff.mp h)
      have := q.pos
      omega
    have hnn : (0 : ℝ) ≤ 2 * (ψ q : ℝ) / ((q : ℕ) : ℝ) := by positivity
    calc volume (setAq ψ q)
        ≤ volume (⋃ a ∈ numerators q,
            Metric.closedBall ((a : ℝ) / (q : ℕ)) ((ψ q : ℝ) / (q : ℕ))) :=
          measure_mono (setAq_subset ψ q hψ)
      _ ≤ ∑ a ∈ numerators q,
            volume (Metric.closedBall ((a : ℝ) / (q : ℕ)) ((ψ q : ℝ) / (q : ℕ))) :=
          measure_biUnion_finset_le _ _
      _ = (numerators q).card • ENNReal.ofReal (2 * ((ψ q : ℝ) / (q : ℕ))) := by
          simp [Real.volume_closedBall]
      _ = ENNReal.ofReal (2 * (ψ q : ℝ) * (φ (q : ℕ) : ℝ) / ((q : ℕ) : ℝ)) := by
          rw [card_numerators hq2, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1
          field_simp

/-- Closed balls of radius `r` about centres at distance at least `2r` meet in a null set.
They can genuinely meet -- at `ψ q = 1/2` consecutive intervals share an endpoint -- so
this is stated as a null intersection rather than as disjointness. -/
theorem volume_closedBall_inter {x y r : ℝ} (h : 2 * r ≤ |x - y|) :
    volume (Metric.closedBall x r ∩ Metric.closedBall y r) = 0 := by
  rw [Real.closedBall_eq_Icc, Real.closedBall_eq_Icc, Set.Icc_inter_Icc, Real.volume_Icc,
    ENNReal.ofReal_eq_zero]
  rcases abs_cases (x - y) with ⟨he, -⟩ | ⟨he, -⟩ <;>
    simp only [min_def, max_def] <;> split_ifs <;> linarith [he]

/-- For `q ≥ 2` and `ψ q ≤ 1/2` every admissible ball lies inside `[0,1]`, so `setAq` is
exactly the union of the `φ(q)` balls rather than merely contained in it. -/
theorem setAq_eq_biUnion {ψ : ℕ+ → ℝ≥0} {q : ℕ+} (hq : 2 ≤ (q : ℕ))
    (hψ : (ψ q : ℝ) ≤ 1 / 2) :
    setAq ψ q =
      ⋃ b ∈ numerators q, Metric.closedBall ((b : ℝ) / ((q : ℕ) : ℝ)) ((ψ q : ℝ) / ((q : ℕ) : ℝ)) := by
  refine Set.Subset.antisymm (setAq_subset ψ q hψ) ?_
  have hq0 : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.pos
  intro α hα
  simp only [Set.mem_iUnion, Metric.mem_closedBall, Real.dist_eq, exists_prop] at hα
  obtain ⟨b, hb, hball⟩ := hα
  simp only [numerators, Finset.mem_filter, Finset.mem_range] at hb
  obtain ⟨hblt, hbcop⟩ := hb
  -- coprimality forces `1 ≤ b ≤ q - 1`
  have hb0 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · subst h
      simp only [Nat.Coprime, Nat.gcd_zero_left] at hbcop
      omega
    · exact h
  have hbq : b + 1 ≤ (q : ℕ) := by
    rcases Nat.lt_or_ge b (q : ℕ) with h | h
    · omega
    · exfalso
      have hbq' : b = (q : ℕ) := by omega
      rw [hbq'] at hbcop
      have : (q : ℕ) = 1 := by simpa [Nat.Coprime] using hbcop
      omega
  have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb0
  have hbqR : (b : ℝ) + 1 ≤ ((q : ℕ) : ℝ) := by exact_mod_cast hbq
  have hb' := abs_le.mp hball
  have eb : (b : ℝ) / ((q : ℕ) : ℝ) * ((q : ℕ) : ℝ) = b := div_mul_cancel₀ _ hq0.ne'
  have eψ : (ψ q : ℝ) / ((q : ℕ) : ℝ) * ((q : ℕ) : ℝ) = (ψ q : ℝ) := div_mul_cancel₀ _ hq0.ne'
  have hmul1 := mul_le_mul_of_nonneg_right hb'.1 hq0.le
  have hmul2 := mul_le_mul_of_nonneg_right hb'.2 hq0.le
  rw [neg_mul, eψ, sub_mul, eb] at hmul1
  rw [sub_mul, eb, eψ] at hmul2
  refine ⟨⟨?_, ?_⟩, b, hbcop, hball⟩
  · by_contra hneg
    push Not at hneg
    nlinarith [mul_neg_of_neg_of_pos hneg hq0]
  · by_contra hbig
    push Not at hbig
    nlinarith [mul_lt_mul_of_pos_right hbig hq0]

theorem volume_setAq_of_two_le {ψ : ℕ+ → ℝ≥0} {q : ℕ+} (hq : 2 ≤ (q : ℕ))
    (hψ : (ψ q : ℝ) ≤ 1 / 2) :
    volume (setAq ψ q) = ENNReal.ofReal (2 * (ψ q : ℝ) * (φ (q : ℕ) : ℝ) / ((q : ℕ) : ℝ)) := by
  have hq0 : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.pos
  rw [setAq_eq_biUnion hq hψ, measure_biUnion_finset₀ ?disj ?meas]
  case meas => exact fun b _ => measurableSet_closedBall.nullMeasurableSet
  case disj =>
    intro b hb c hc hbc
    refine volume_closedBall_inter ?_
    have h1 : (1 : ℝ) ≤ |(b : ℝ) - (c : ℝ)| := by
      rcases Nat.lt_or_ge b c with h | h
      · have hR : (b : ℝ) + 1 ≤ (c : ℝ) := by exact_mod_cast h
        rw [abs_of_neg (by linarith)]
        linarith
      · have hcb : c < b := by omega
        have hR : (c : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hcb
        rw [abs_of_pos (by linarith)]
        linarith
    rw [div_sub_div_same, abs_div, abs_of_pos hq0]
    rw [le_div_iff₀ hq0]
    calc 2 * ((ψ q : ℝ) / ((q : ℕ) : ℝ)) * ((q : ℕ) : ℝ)
        = 2 * (ψ q : ℝ) := by field_simp
      _ ≤ 1 := by linarith
      _ ≤ |(b : ℝ) - (c : ℝ)| := h1
  rw [Finset.sum_congr rfl fun b _ => Real.volume_closedBall _ _, Finset.sum_const,
    card_numerators hq, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  field_simp

/-- `setA` is the `limsup` of the `setAq`: for `ψ ≤ 1/2`, infinitely many solution
*pairs* is the same as infinitely many *denominators*.

The hypothesis is essential and not cosmetic. It is what bounds the numerator of a
solution by `q` (`le_of_approximates`), which makes the fibre over each denominator
finite. Without it a single denominator could carry infinitely many pairs and the two
sides would differ. -/
theorem mem_setA_iff (ψ : ℕ+ → ℝ≥0) (hψ : ∀ q, (ψ q : ℝ) ≤ 1 / 2) (α : ℝ) :
    α ∈ setA ψ ↔ α ∈ Set.Icc (0 : ℝ) 1 ∧ {q : ℕ+ | α ∈ setAq ψ q}.Infinite := by
  constructor
  · rintro ⟨hα01, hinf⟩
    refine ⟨hα01, ?_⟩
    by_contra hfin
    rw [Set.not_infinite] at hfin
    refine hinf (Set.Finite.subset (hfin.biUnion (t := fun q : ℕ+ =>
      (fun a : ℕ => (a, q)) '' Set.Iic (q : ℕ)) fun q _ => (Set.finite_Iic _).image _) ?_)
    rintro ⟨a, q⟩ ⟨hcop, happ⟩
    have haq : a ≤ (q : ℕ) := le_of_approximates (hψ q) hα01 happ
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_Iic, exists_prop]
    exact ⟨q, ⟨hα01, a, hcop, happ⟩, a, haq, rfl⟩
  · rintro ⟨hα01, hinf⟩
    refine ⟨hα01, ?_⟩
    have hex : ∀ q ∈ {q : ℕ+ | α ∈ setAq ψ q},
        ∃ a : ℕ, Nat.Coprime a q ∧ Approximates ψ α a q := fun q hq => hq.2
    choose! g hg1 hg2 using hex
    have himg : ((fun q : ℕ+ => (g q, q)) '' {q : ℕ+ | α ∈ setAq ψ q}).Infinite :=
      hinf.image fun _ _ _ _ h => congrArg Prod.snd h
    refine himg.mono ?_
    rintro p ⟨q, hq, rfl⟩
    exact ⟨hg1 q hq, hg2 q hq⟩

/-- A `limsup` over any countable index is measurable: the set of points lying in
infinitely many `B i` is `⋂_t ⋃_{i ∉ t} B i`, a countable intersection of countable
unions, because `Finset ι` is countable when `ι` is.

Both `setA` and `setK` are of this shape -- over pairs `(a, q)` -- so this is stated once
and used twice. -/
theorem measurableSet_setOf_infinite {ι : Type*} [Countable ι] {B : ι → Set ℝ}
    (hB : ∀ i, MeasurableSet (B i)) : MeasurableSet {α : ℝ | {i | α ∈ B i}.Infinite} := by
  have key : {α : ℝ | {i | α ∈ B i}.Infinite} = ⋂ t : Finset ι, ⋃ i, ⋃ _ : i ∉ t, B i := by
    ext α
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, exists_prop]
    constructor
    · intro h t
      obtain ⟨i, hi, hit⟩ := h.exists_notMem_finset t
      exact ⟨i, hit, hi⟩
    · intro h
      by_contra hfin
      rw [Set.not_infinite] at hfin
      obtain ⟨i, hit, hi⟩ := h hfin.toFinset
      exact hit (hfin.mem_toFinset.mpr hi)
  rw [key]
  exact MeasurableSet.iInter fun t =>
    MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hB i

/-- The set cut out by a single pair `(a, q)`: a closed ball, or empty when the side
condition on the pair fails. -/
theorem measurableSet_approxPair (ψ : ℕ+ → ℝ≥0) (P : ℕ → ℕ+ → Prop) (a : ℕ) (q : ℕ+) :
    MeasurableSet {α : ℝ | P a q ∧ Approximates ψ α a q} := by
  by_cases h : P a q
  · have : {α : ℝ | P a q ∧ Approximates ψ α a q}
        = Metric.closedBall ((a : ℝ) / q) ((ψ q : ℝ) / q) := by
      ext α
      simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, Real.dist_eq, Approximates, h,
        true_and]
    rw [this]
    exact measurableSet_closedBall
  · have : {α : ℝ | P a q ∧ Approximates ψ α a q} = ∅ := by
      ext α; simp [h]
    rw [this]
    exact MeasurableSet.empty

theorem measurableSet_setA (ψ : ℕ+ → ℝ≥0) : MeasurableSet (setA ψ) := by
  have h : setA ψ = Set.Icc 0 1 ∩
      {α : ℝ | Set.Infinite {p : ℕ × ℕ+ | Nat.Coprime p.1 p.2 ∧ Approximates ψ α p.1 p.2}} := by
    ext α
    simp only [setA, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [h]
  refine measurableSet_Icc.inter (measurableSet_setOf_infinite (B := fun p : ℕ × ℕ+ =>
    {β : ℝ | Nat.Coprime p.1 p.2 ∧ Approximates ψ β p.1 p.2}) fun p => ?_)
  exact measurableSet_approxPair ψ (fun a q => Nat.Coprime a q) p.1 p.2

theorem measurableSet_setK (ψ : ℕ+ → ℝ≥0) : MeasurableSet (setK ψ) := by
  have h : setK ψ = Set.Icc 0 1 ∩
      {α : ℝ | Set.Infinite {p : ℕ × ℕ+ | p.1 ≤ (p.2 : ℕ) ∧ Approximates ψ α p.1 p.2}} := by
    ext α
    simp only [setK, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [h]
  refine measurableSet_Icc.inter (measurableSet_setOf_infinite (B := fun p : ℕ × ℕ+ =>
    {β : ℝ | p.1 ≤ (p.2 : ℕ) ∧ Approximates ψ β p.1 p.2}) fun p => ?_)
  exact measurableSet_approxPair ψ (fun a q => a ≤ (q : ℕ)) p.1 p.2

/-- A non-summable non-negative real series has infinite `ℝ≥0∞` sum. -/
theorem tsum_ofReal_eq_top {ι : Type*} {g : ι → ℝ} (hg : ∀ i, 0 ≤ g i) (h : ¬ Summable g) :
    ∑' i, ENNReal.ofReal (g i) = ⊤ := by
  by_contra hc
  refine h ?_
  have hne : ∑' i, ((g i).toNNReal : ℝ≥0∞) ≠ ⊤ := by simpa [ENNReal.ofReal] using hc
  refine ((ENNReal.tsum_coe_ne_top_iff_summable.mp hne).map NNReal.toRealHom
    (by continuity)).congr fun i => ?_
  simp [Real.coe_toNNReal _ (hg i)]

/-- The divergence hypothesis of Theorem 1, in the form the second-moment argument
consumes: the measures of the `setAq` are not summable.

The `q = 1` term is handled by absorbing it rather than by computing it: the equality
`volume_setAq_of_two_le` holds for `q ≥ 2`, and a single finite term cannot rescue a
divergent series. -/
theorem not_summable_volume_setAq (ψ : ℕ+ → ℝ≥0) (hψ : ∀ q, (ψ q : ℝ) ≤ 1 / 2)
    (hdiv : ¬ Summable fun q : ℕ+ ↦ (ψ q : ℝ) * (φ (q : ℕ) : ℝ) / (q : ℝ)) :
    ∑' q : ℕ+, volume (setAq ψ q) = ⊤ := by
  set F : ℕ+ → ℝ≥0∞ :=
    fun q => ENNReal.ofReal (2 * (ψ q : ℝ) * (φ (q : ℕ) : ℝ) / ((q : ℕ) : ℝ)) with hFdef
  have hFtop : ∑' q : ℕ+, F q = ⊤ := by
    refine tsum_ofReal_eq_top (fun q => by positivity) fun hs => hdiv ?_
    have := hs.div_const (2 : ℝ)
    refine this.congr fun q => ?_
    field_simp
  by_contra hc
  refine absurd hFtop ?_
  have hle : ∀ q : ℕ+, F q ≤ volume (setAq ψ q) + (if q = 1 then F 1 else 0) := by
    intro q
    by_cases hq1 : q = 1
    · subst hq1; simp
    · have hq2 : 2 ≤ (q : ℕ) := by
        have h1 : (q : ℕ) ≠ 1 := fun h => hq1 (PNat.coe_eq_one_iff.mp h)
        have := q.pos
        omega
      simp [hq1, volume_setAq_of_two_le hq2 (hψ q), hFdef]
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
  rw [ENNReal.tsum_add, tsum_ite_eq]
  exact ENNReal.add_ne_top.mpr ⟨hc, by simp only [hFdef]; exact ENNReal.ofReal_ne_top⟩

/-- `setA` is monotone in `ψ`: enlarging the tolerance can only add solutions. -/
theorem setA_mono {ψ ψ' : ℕ+ → ℝ≥0} (h : ∀ q, ψ q ≤ ψ' q) : setA ψ ⊆ setA ψ' := by
  rintro α ⟨hα01, hinf⟩
  refine ⟨hα01, hinf.mono ?_⟩
  rintro ⟨a, q⟩ ⟨hcop, happ⟩
  refine ⟨hcop, le_trans happ ?_⟩
  have hq0 : (0 : ℝ) ≤ ((q : ℕ) : ℝ) := by positivity
  have hψ : (ψ q : ℝ) ≤ (ψ' q : ℝ) := by exact_mod_cast h q
  gcongr

/-- Reduction to `ψ ≤ 1/2`.

**This is not a Chapter 2 result**, and stating it as one was a mistake in the first
draft of this development. Either disjunct requires knowing that `setA ψ` cannot have
intermediate measure, and that is exactly Gallagher's zero-one law -- a Chapter 3 input.
It is not circular: every Chapter 3 statement carries the hypothesis `ψ ≤ 1/2` and none
of them uses this lemma. But the dependency is real, so the zero-one law is taken here
as an explicit hypothesis rather than hidden.

The tempting elementary route does not work. One would like to say that if `ψ(q) > 1/2`
for infinitely many `q` then `setA ψ` is full outright, but that is false: at `q = 6`
only `b = 1, 5` are coprime to `6`, so the balls around `1/6` and `5/6` of radius
`ψ(6)/6` do not cover `[0,1]` unless `ψ(6) ≥ 2`. Nothing weaker than the zero-one law
closes the gap. -/
theorem setA_truncate (ψ : ℕ+ → ℝ≥0)
    (hzo : volume (setA ψ) = 0 ∨ volume (setA ψ) = 1) :
    volume (setA ψ) = 1 ∨ volume (setA fun q ↦ min (ψ q) (1 / 2)) = volume (setA ψ) := by
  rcases hzo with h | h
  · refine Or.inr ?_
    rw [h]
    exact le_antisymm (h ▸ measure_mono (setA_mono fun q => min_le_left _ _)) (by simp)
  · exact Or.inl h

end DuffinSchaeffer
