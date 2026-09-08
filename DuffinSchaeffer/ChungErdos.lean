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
import Mathlib.Data.PNat.Interval

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

namespace DuffinSchaeffer

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Cauchy-Schwarz for `lintegral`

Mathlib has no Cauchy-Schwarz inequality for measure-theoretic integrals: searching
`MeasureTheory` and `Probability` for `cauchy_schwarz` returns nothing. The nearest thing
is `ENNReal.lintegral_mul_le_Lp_mul_Lq`, Hölder with real exponents, whose `p = q = 2`
case is Cauchy-Schwarz but stated through `ENNReal.rpow`. The squared form below is what
an application actually wants, and is independently upstreamable. -/

/-- **Cauchy-Schwarz for `lintegral`.** -/
theorem lintegral_mul_sq_le (μ : Measure Ω) {f g : Ω → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) :
    (∫⁻ ω, f ω * g ω ∂μ) ^ 2 ≤ (∫⁻ ω, f ω ^ 2 ∂μ) * (∫⁻ ω, g ω ^ 2 ∂μ) := by
  have hpq : Real.HolderConjugate 2 2 := by constructor <;> norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf hg
  simp only [Pi.mul_apply] at h
  have hsq : ∀ x : ℝ≥0∞, x ^ (2 : ℝ) = x ^ (2 : ℕ) := fun x => by
    rw [← ENNReal.rpow_natCast x 2]; norm_num
  simp only [hsq] at h
  calc (∫⁻ ω, f ω * g ω ∂μ) ^ 2
      ≤ ((∫⁻ ω, f ω ^ (2 : ℕ) ∂μ) ^ (1 / (2 : ℝ))
          * (∫⁻ ω, g ω ^ (2 : ℕ) ∂μ) ^ (1 / (2 : ℝ))) ^ 2 := by gcongr
    _ = (∫⁻ ω, f ω ^ (2 : ℕ) ∂μ) * (∫⁻ ω, g ω ^ (2 : ℕ) ∂μ) := by
        rw [← ENNReal.rpow_natCast _ 2, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

/-- **The Chung-Erdos inequality.** For finitely many events,
`(∑ μ Aᵢ)² ≤ μ (⋃ Aᵢ) · ∑ᵢⱼ μ (Aᵢ ∩ Aⱼ)`.

Cauchy-Schwarz applied to the pair `1_{⋃ Aᵢ}` and the counting function `∑ 1_{Aᵢ}`. -/
theorem chung_erdos (μ : Measure Ω) {ι : Type*} (s : Finset ι) (A : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) :
    (∑ i ∈ s, μ (A i)) ^ 2 ≤ μ (⋃ i ∈ s, A i) * ∑ i ∈ s, ∑ j ∈ s, μ (A i ∩ A j) := by
  classical
  set U := ⋃ i ∈ s, A i with hUdef
  set F : Ω → ℝ≥0∞ := fun ω => ∑ i ∈ s, (A i).indicator 1 ω with hFdef
  have hUmeas : MeasurableSet U := Finset.measurableSet_biUnion _ fun i _ => hA i
  have hind : ∀ i, Measurable ((A i).indicator (1 : Ω → ℝ≥0∞)) := fun i =>
    measurable_one.indicator (hA i)
  have hFmeas : Measurable F := Finset.measurable_sum _ fun i _ => hind i
  have h1 : ∫⁻ ω, F ω ∂μ = ∑ i ∈ s, μ (A i) := by
    rw [hFdef, lintegral_finsetSum _ fun i _ => hind i]
    exact Finset.sum_congr rfl fun i _ => by rw [lintegral_indicator (hA i)]; simp
  have h2 : ∫⁻ ω, F ω ^ 2 ∂μ = ∑ i ∈ s, ∑ j ∈ s, μ (A i ∩ A j) := by
    have hpt : ∀ ω, F ω ^ 2 = ∑ i ∈ s, ∑ j ∈ s, (A i ∩ A j).indicator 1 ω := by
      intro ω
      rw [hFdef, sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      by_cases hi : ω ∈ A i <;> by_cases hj : ω ∈ A j <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hi, hj]
    simp_rw [hpt]
    rw [lintegral_finsetSum _ fun i _ =>
      Finset.measurable_sum _ fun j _ => measurable_one.indicator ((hA i).inter (hA j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_finsetSum _ fun j _ => measurable_one.indicator ((hA i).inter (hA j))]
    exact Finset.sum_congr rfl fun j _ => by
      rw [lintegral_indicator ((hA i).inter (hA j))]; simp
  have h3 : ∀ ω, F ω = U.indicator 1 ω * F ω := by
    intro ω
    by_cases hω : ω ∈ U
    · simp [Set.indicator_of_mem hω]
    · have hz : F ω = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        exact Set.indicator_of_notMem (fun h => hω (Set.mem_biUnion hi h)) _
      simp [hz]
  have hsqind : ∀ ω, (U.indicator (1 : Ω → ℝ≥0∞) ω) ^ 2 = U.indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ U <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
  calc (∑ i ∈ s, μ (A i)) ^ 2
      = (∫⁻ ω, U.indicator 1 ω * F ω ∂μ) ^ 2 := by rw [← h1]; simp_rw [← h3]
    _ ≤ (∫⁻ ω, (U.indicator (1 : Ω → ℝ≥0∞) ω) ^ 2 ∂μ) * (∫⁻ ω, F ω ^ 2 ∂μ) :=
        lintegral_mul_sq_le μ (measurable_one.indicator hUmeas).aemeasurable hFmeas.aemeasurable
    _ = μ U * ∑ i ∈ s, ∑ j ∈ s, μ (A i ∩ A j) := by
        rw [h2]
        congr 1
        simp_rw [hsqind]
        rw [lintegral_indicator hUmeas]
        simp

/-- **Divergence Borel-Cantelli, quasi-independent form**, for index sets that escape to
infinity: every `S n` beyond a point consists of indices exceeding any fixed `k`.

This is the version the second-moment argument actually uses, and it is where the
constant `C` finally becomes a lower bound on the measure. Chung-Erdős on `S n` gives
`1 ≤ μ(⋃_{i ∈ S n} A i) · C` after cancelling the (finite, nonzero) first moment; the
escape hypothesis places that union inside the tail `⋃_{i > k} A i`; and continuity from
above along the tails gives the conclusion. -/
theorem measure_infinite_pos_of_escaping (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ+ → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (C : ℝ≥0∞) (hC : C ≠ 0) (hC' : C ≠ ⊤)
    (S : ℕ → Finset ℕ+)
    (hesc : ∀ k : ℕ+, ∃ n, (∀ i ∈ S n, k < i) ∧ 0 < ∑ q ∈ S n, μ (A q))
    (hoverlap : ∀ n, ∑ q ∈ S n, ∑ r ∈ S n, μ (A q ∩ A r) ≤ C * (∑ q ∈ S n, μ (A q)) ^ 2) :
    C⁻¹ ≤ μ {x | {i : ℕ+ | x ∈ A i}.Infinite} := by
  set X : ℕ+ → Set Ω := fun k => ⋃ i, ⋃ (_ : k < i), A i with hXdef
  have hXmeas : ∀ k, MeasurableSet (X k) := fun k =>
    MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hA i
  have hXanti : Antitone X := by
    intro k l hkl x hx
    simp only [hXdef, Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi, hxi⟩ := hx
    exact ⟨i, lt_of_le_of_lt hkl hi, hxi⟩
  have hXint : (⋂ k, X k) = {x | {i : ℕ+ | x ∈ A i}.Infinite} := by
    ext x
    simp only [Set.mem_iInter, hXdef, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · exact fun h => Set.infinite_of_forall_exists_gt fun k => by
        obtain ⟨i, hi, hxi⟩ := h k; exact ⟨i, hxi, hi⟩
    · intro h k
      obtain ⟨i, hxi, hi⟩ := h.exists_gt k
      exact ⟨i, hi, hxi⟩
  -- every tail carries measure at least `C⁻¹`
  have hXge : ∀ k, C⁻¹ ≤ μ (X k) := by
    intro k
    obtain ⟨n, hSn, hpos⟩ := hesc k
    set a := ∑ q ∈ S n, μ (A q) with hadef
    have hane : a ≠ 0 := hpos.ne'
    have hatop : a ≠ ⊤ := by
      refine (ENNReal.sum_lt_top.mpr fun q _ => ?_).ne
      exact measure_lt_top μ _
    have hsub : (⋃ i ∈ S n, A i) ⊆ X k := by
      intro x hx
      simp only [Set.mem_iUnion, exists_prop] at hx
      obtain ⟨i, hiS, hxi⟩ := hx
      simp only [hXdef, Set.mem_iUnion]
      exact ⟨i, hSn i hiS, hxi⟩
    have hce := chung_erdos μ (S n) A hA
    have hkey : 1 * a ^ 2 ≤ (μ (X k) * C) * a ^ 2 := by
      rw [one_mul]
      calc a ^ 2 ≤ μ (⋃ i ∈ S n, A i) * ∑ q ∈ S n, ∑ r ∈ S n, μ (A q ∩ A r) := hce
        _ ≤ μ (X k) * (C * a ^ 2) := mul_le_mul' (measure_mono hsub) (hoverlap n)
        _ = (μ (X k) * C) * a ^ 2 := by ring
    have h1 : (1 : ℝ≥0∞) ≤ μ (X k) * C :=
      (ENNReal.mul_le_mul_iff_left (pow_ne_zero 2 hane) (by simpa using hatop)).mp hkey
    calc C⁻¹ = 1 * C⁻¹ := (one_mul _).symm
      _ ≤ (μ (X k) * C) * C⁻¹ := by gcongr
      _ = μ (X k) := by rw [mul_assoc, ENNReal.mul_inv_cancel hC hC', mul_one]
  rw [← hXint]
  exact ge_of_tendsto'
    (tendsto_measure_iInter_atTop (fun k => (hXmeas k).nullMeasurableSet) hXanti
      ⟨1, measure_ne_top _ _⟩) hXge

theorem sum_le_sum_sdiff_add_sum {ι : Type*} [DecidableEq ι] (s t : Finset ι)
    (f : ι → ℝ≥0∞) : ∑ i ∈ s, f i ≤ ∑ i ∈ s \ t, f i + ∑ i ∈ t, f i := by
  rw [← Finset.sum_filter_add_sum_filter_not s (fun i => i ∈ t) f, add_comm]
  refine add_le_add (le_of_eq (Finset.sum_congr (Finset.sdiff_eq_filter s t).symm
    fun _ _ => rfl)) ?_
  exact Finset.sum_le_sum_of_subset fun x hx => (Finset.mem_filter.mp hx).2

/-- **Divergence Borel-Cantelli, quasi-independent form**, with no escape hypothesis.

Note the conclusion. `measure_infinite_pos_of_escaping` gives the sharp constant `C⁻¹`;
here the bound degrades to `(4C)⁻¹`, so the statement is phrased as positivity, which is
all any consumer needs -- Gallagher's zero-one law turns any positive lower bound into
`1`, and the whole development is arranged so that no constant is ever computed.

That weakening is what makes the proof elementary. The sharp version wants
`x²  ≤ M C (x + K)²` with `x → ∞`, hence a ratio and a limit, both awkward in `ℝ≥0∞`.
Settling for a factor of `4` removes them: choose `n` with the first moment over `S n` at
least twice the fixed mass sitting on the discarded initial segment, and the discarded
part can then be absorbed by a factor of `2` before squaring. -/
theorem measure_infinite_pos_of_overlap (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ+ → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (C : ℝ≥0∞) (hC : C ≠ 0) (hC' : C ≠ ⊤)
    (S : ℕ → Finset ℕ+)
    (hdiv : Tendsto (fun n ↦ ∑ q ∈ S n, μ (A q)) atTop atTop)
    (hoverlap : ∀ n, ∑ q ∈ S n, ∑ r ∈ S n, μ (A q ∩ A r) ≤ C * (∑ q ∈ S n, μ (A q)) ^ 2) :
    0 < μ {x | {i : ℕ+ | x ∈ A i}.Infinite} := by
  classical
  set X : ℕ+ → Set Ω := fun k => ⋃ i, ⋃ (_ : k < i), A i with hXdef
  have hXmeas : ∀ k, MeasurableSet (X k) := fun k =>
    MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hA i
  have hXanti : Antitone X := by
    intro k l hkl x hx
    simp only [hXdef, Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi, hxi⟩ := hx
    exact ⟨i, lt_of_le_of_lt hkl hi, hxi⟩
  have hXint : (⋂ k, X k) = {x | {i : ℕ+ | x ∈ A i}.Infinite} := by
    ext x
    simp only [Set.mem_iInter, hXdef, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · exact fun h => Set.infinite_of_forall_exists_gt fun k => by
        obtain ⟨i, hi, hxi⟩ := h k; exact ⟨i, hxi, hi⟩
    · intro h k
      obtain ⟨i, hxi, hi⟩ := h.exists_gt k
      exact ⟨i, hi, hxi⟩
  have hCfour : (4 : ℝ≥0∞) * C ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hC'
  have hXge : ∀ k, ((4 : ℝ≥0∞) * C)⁻¹ ≤ μ (X k) := by
    intro k
    set t : Finset ℕ+ := Finset.Iic k with htdef
    set K : ℝ≥0∞ := ∑ i ∈ t, μ (A i) with hKdef
    have hKtop : K ≠ ⊤ := (ENNReal.sum_lt_top.mpr fun q _ => measure_lt_top μ _).ne
    -- pick `n` with the first moment at least `2K + 1`
    obtain ⟨n, hn⟩ := (hdiv.eventually_ge_atTop (2 * K + 1)).exists
    set y := ∑ q ∈ S n, μ (A q) with hydef
    set x := ∑ q ∈ S n \ t, μ (A q) with hxdef
    have hytop : y ≠ ⊤ := (ENNReal.sum_lt_top.mpr fun q _ => measure_lt_top μ _).ne
    have hxtop : x ≠ ⊤ := (ENNReal.sum_lt_top.mpr fun q _ => measure_lt_top μ _).ne
    have hyx : y ≤ x + K := sum_le_sum_sdiff_add_sum _ _ _
    have hy2K : 2 * K + 1 ≤ y := hn
    -- hence `y ≤ 2x`
    have hy2x : y ≤ 2 * x := by
      have hKy : K + K ≤ x + K + K := by gcongr; exact le_add_self
      have : y + K ≤ x + K + K := by
        calc y + K ≤ (x + K) + K := by gcongr
          _ = x + K + K := rfl
      -- from `2K + 1 ≤ y` and `y ≤ x + K` we get `K + 1 ≤ x`, so `y ≤ x + K ≤ 2x`
      have hKx : K ≤ x := by
        by_contra hlt
        push Not at hlt
        have : y < 2 * K + 1 := by
          calc y ≤ x + K := hyx
            _ < K + K := by gcongr
            _ ≤ 2 * K + 1 := by rw [two_mul]; exact le_self_add
        exact absurd hy2K (not_le.mpr this)
      calc y ≤ x + K := hyx
        _ ≤ x + x := by gcongr
        _ = 2 * x := (two_mul x).symm
    have hxpos : x ≠ 0 := by
      intro h
      rw [h] at hy2x
      simp only [mul_zero, nonpos_iff_eq_zero] at hy2x
      rw [hy2x] at hy2K
      simp only [nonpos_iff_eq_zero, add_eq_zero, one_ne_zero, and_false] at hy2K
    have hsub : (⋃ i ∈ S n \ t, A i) ⊆ X k := by
      intro z hz
      simp only [Set.mem_iUnion, exists_prop] at hz
      obtain ⟨i, hiS, hzi⟩ := hz
      simp only [hXdef, Set.mem_iUnion]
      exact ⟨i, by simpa [htdef] using (Finset.mem_sdiff.mp hiS).2, hzi⟩
    have hce := chung_erdos μ (S n \ t) A hA
    have hkey : 1 * x ^ 2 ≤ (4 * (μ (X k) * C)) * x ^ 2 := by
      rw [one_mul]
      calc x ^ 2 ≤ μ (⋃ i ∈ S n \ t, A i) * ∑ q ∈ S n \ t, ∑ r ∈ S n \ t, μ (A q ∩ A r) := hce
        _ ≤ μ (X k) * (C * y ^ 2) := by
            refine mul_le_mul' (measure_mono hsub) (le_trans ?_ (hoverlap n))
            calc ∑ q ∈ S n \ t, ∑ r ∈ S n \ t, μ (A q ∩ A r)
                ≤ ∑ q ∈ S n \ t, ∑ r ∈ S n, μ (A q ∩ A r) :=
                  Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset Finset.sdiff_subset
              _ ≤ ∑ q ∈ S n, ∑ r ∈ S n, μ (A q ∩ A r) :=
                  Finset.sum_le_sum_of_subset Finset.sdiff_subset
        _ ≤ μ (X k) * (C * (2 * x) ^ 2) := by gcongr
        _ = (4 * (μ (X k) * C)) * x ^ 2 := by ring
    have h1 : (1 : ℝ≥0∞) ≤ 4 * (μ (X k) * C) :=
      (ENNReal.mul_le_mul_iff_left (pow_ne_zero 2 hxpos) (by simpa using hxtop)).mp hkey
    calc ((4 : ℝ≥0∞) * C)⁻¹ = 1 * (4 * C)⁻¹ := (one_mul _).symm
      _ ≤ (4 * (μ (X k) * C)) * (4 * C)⁻¹ := by gcongr
      _ = μ (X k) * ((4 * C) * (4 * C)⁻¹) := by ring
      _ = μ (X k) := by
          rw [ENNReal.mul_inv_cancel (by simp [hC]) hCfour, mul_one]
  have hlim := ge_of_tendsto'
    (tendsto_measure_iInter_atTop (fun k => (hXmeas k).nullMeasurableSet) hXanti
      ⟨1, measure_ne_top _ _⟩) hXge
  rw [← hXint]
  exact lt_of_lt_of_le (ENNReal.inv_pos.mpr hCfour) hlim

end DuffinSchaeffer
