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
