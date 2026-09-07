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

theorem setAq_subset (ψ : ℕ+ → ℝ≥0) (q : ℕ+) (hψ : (ψ q : ℝ) ≤ 1 / 2) :
    setAq ψ q ⊆ ⋃ a ∈ numerators q, Metric.closedBall ((a : ℝ) / q) ((ψ q : ℝ) / q) := by
  have hq0 : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.pos
  intro α hα
  rw [setAq_eq] at hα
  obtain ⟨hα01, hu⟩ := hα
  simp only [Set.mem_iUnion, Metric.mem_closedBall, Real.dist_eq, exists_prop,
    Set.mem_ofPred_eq] at hu
  obtain ⟨a, hcop, hball⟩ := hu
  have e1 : (a : ℝ) / (q : ℕ) * (q : ℕ) = a := div_mul_cancel₀ _ (ne_of_gt hq0)
  have e2 : (ψ q : ℝ) / (q : ℕ) * (q : ℕ) = (ψ q : ℝ) := div_mul_cancel₀ _ (ne_of_gt hq0)
  have h3 := mul_le_mul_of_nonneg_right (abs_le.mp hball).1 hq0.le
  rw [neg_mul, e2, sub_mul, e1] at h3
  have h4 : α * (q : ℕ) ≤ 1 * (q : ℕ) := mul_le_mul_of_nonneg_right hα01.2 hq0.le
  have ha : (a : ℝ) < (q : ℕ) + 1 := by nlinarith
  have ha' : a < (q : ℕ) + 1 := by exact_mod_cast ha
  simp only [Set.mem_iUnion, numerators, Finset.mem_filter, Finset.mem_range, exists_prop,
    Metric.mem_closedBall, Real.dist_eq]
  exact ⟨a, ⟨ha', hcop⟩, hball⟩

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

/-- The bound of `volume_setAq_le` is in fact an equality under the same hypothesis: for
`ψ q ≤ 1/2` the `φ(q)` intervals are pairwise disjoint and contained in `[0,1]`. Only the
upper bound is used downstream, so this is left open. -/
proof_wanted volume_setAq (ψ : ℕ+ → ℝ≥0) (q : ℕ+) (hψ : (ψ q : ℝ) ≤ 1 / 2) :
    volume (setAq ψ q) = ENNReal.ofReal (2 * (ψ q : ℝ) * (φ (q : ℕ) : ℝ) / ((q : ℕ) : ℝ))

/-- `setA` is the `limsup` of the `setAq`. The hypothesis `ψ ≤ 1/2` is what confines the
numerator of a solution to `0 ≤ a ≤ q`, which is why `setA` counts pairs while `setAq`
counts denominators. -/
proof_wanted mem_setA_iff (ψ : ℕ+ → ℝ≥0) (hψ : ∀ q, (ψ q : ℝ) ≤ 1 / 2) (α : ℝ) :
    α ∈ setA ψ ↔ α ∈ Set.Icc (0 : ℝ) 1 ∧ {q : ℕ+ | α ∈ setAq ψ q}.Infinite

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
