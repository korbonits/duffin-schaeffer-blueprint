/- Theorem 2(a): the convergence half.

   If `∑ ψ⋆(q) < ∞` then `𝒦(ψ)` is null. This is the easy direction of Theorem 2 and
   needs nothing from the overlap or GCD-graph chapters -- only the first Borel-Cantelli
   lemma, which Mathlib has.

   The argument reduces `a/q` to lowest terms `b/d` and covers `𝒦(ψ)` by the sets
   `E_d = ⋃_{b ≤ d, gcd(b,d)=1} closedBall(b/d, Ψ(d))`, whose measures are summable.

   The step that needs care is that infinitely many *pairs* give infinitely many
   *denominators* `d`. That is false as stated -- at `α = 0` every pair `(0,q)` reduces
   to `0/1` -- so the rationals are discarded first (they are countable, hence null), and
   for irrational `α` each reduced fraction `b/d` absorbs only finitely many `q`, because
   summability forces `ψ(q)/q → 0` while `|α - b/d| > 0` is a fixed positive number. -/
import DuffinSchaeffer.Basic
import Mathlib.NumberTheory.Real.Irrational

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Nat BigOperators

namespace DuffinSchaeffer

/-- A set is infinite as soon as it escapes every finite subset. -/
theorem infinite_of_forall_exists_notMem_finset {ι : Type*} {s : Set ι}
    (h : ∀ t : Finset ι, ∃ i ∈ s, i ∉ t) : s.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨i, hi, hit⟩ := h hfin.toFinset
  exact hit (hfin.mem_toFinset.mpr hi)

/-! ### Reduction to lowest terms -/

/-- The numerator of `a/q` in lowest terms. -/
def redNum (a : ℕ) (q : ℕ+) : ℕ := a / Nat.gcd a q

/-- The denominator of `a/q` in lowest terms. -/
def redDen (a : ℕ) (q : ℕ+) : ℕ+ :=
  ⟨(q : ℕ) / Nat.gcd a q,
    Nat.div_pos (Nat.le_of_dvd q.pos (Nat.gcd_dvd_right a q)) (Nat.gcd_pos_of_pos_right a q.pos)⟩

theorem redDen_dvd (a : ℕ) (q : ℕ+) : redDen a q ∣ q :=
  PNat.dvd_iff.mpr (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right a q))

theorem coprime_redNum_redDen (a : ℕ) (q : ℕ+) : Nat.Coprime (redNum a q) (redDen a q) :=
  Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right a q.pos)

theorem redNum_mem_numerators {a : ℕ} {q : ℕ+} (h : a ≤ (q : ℕ)) :
    redNum a q ∈ numerators (redDen a q) := by
  simp only [numerators, Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le (Nat.div_le_div_right h), coprime_redNum_redDen a q⟩

theorem redNum_div_redDen (a : ℕ) (q : ℕ+) :
    (redNum a q : ℝ) / ((redDen a q : ℕ) : ℝ) = (a : ℝ) / ((q : ℕ) : ℝ) := by
  have hg : 0 < Nat.gcd a q := Nat.gcd_pos_of_pos_right a q.pos
  have hgR : ((Nat.gcd a q : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hg.ne'
  have hq : ((q : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.pos.ne'
  have h1 : ((redNum a q : ℕ) : ℝ) = (a : ℝ) / ((Nat.gcd a q : ℕ) : ℝ) :=
    Nat.cast_div (Nat.gcd_dvd_left a q) hgR
  have h2 : (((redDen a q : ℕ+) : ℕ) : ℝ) = ((q : ℕ) : ℝ) / ((Nat.gcd a q : ℕ) : ℝ) :=
    Nat.cast_div (Nat.gcd_dvd_right a q) hgR
  rw [h1, h2]
  field_simp

/-! ### The covering sets -/

/-- The radius attached to a reduced denominator `d`, as a real number. -/
noncomputable def radius (ψ : ℕ+ → ℝ≥0) (d : ℕ+) : ℝ := (psiSup ψ d).toReal

/-- `E_d`: the union of the balls of radius `Ψ(d)` around the reduced fractions with
denominator `d`. -/
noncomputable def coverE (ψ : ℕ+ → ℝ≥0) (d : ℕ+) : Set ℝ :=
  ⋃ b ∈ numerators d, closedBall ((b : ℝ) / ((d : ℕ) : ℝ)) (radius ψ d)

theorem measurableSet_coverE (ψ : ℕ+ → ℝ≥0) (d : ℕ+) : MeasurableSet (coverE ψ d) :=
  Finset.measurableSet_biUnion _ fun _ _ => measurableSet_closedBall

/-- At most `φ(d) + 1` numerators: exactly `φ(d)` for `d ≥ 2`, and the two values `0, 1`
when `d = 1`. -/
theorem card_numerators_le (d : ℕ+) : (numerators d).card ≤ φ (d : ℕ) + 1 := by
  by_cases hd : d = 1
  · subst hd
    decide
  · have hd2 : 2 ≤ (d : ℕ) := by
      have h1 : (d : ℕ) ≠ 1 := fun h => hd (PNat.coe_eq_one_iff.mp h)
      have := d.pos
      omega
    exact le_trans (le_of_eq (card_numerators hd2)) (Nat.le_succ _)

/-- Each covering set has measure at most `4 ψ⋆(d)`. -/
theorem volume_coverE_le (ψ : ℕ+ → ℝ≥0) (d : ℕ+) (hd : psiSup ψ d ≠ ⊤) :
    volume (coverE ψ d) ≤ 4 * psiStar ψ d := by
  have hrad : ENNReal.ofReal (2 * radius ψ d) = 2 * psiSup ψ d := by
    rw [radius, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hd]
    norm_num
  have hcard : (φ (d : ℕ) + 1) ≤ 2 * φ (d : ℕ) := by
    have := Nat.totient_pos.mpr d.pos
    omega
  calc volume (coverE ψ d)
      ≤ ∑ b ∈ numerators d, volume (closedBall ((b : ℝ) / ((d : ℕ) : ℝ)) (radius ψ d)) :=
        measure_biUnion_finset_le _ _
    _ = (numerators d).card • ENNReal.ofReal (2 * radius ψ d) := by
        simp [Real.volume_closedBall]
    _ = ((numerators d).card : ℝ≥0∞) * (2 * psiSup ψ d) := by rw [nsmul_eq_mul, hrad]
    _ ≤ ((2 * φ (d : ℕ) : ℕ) : ℝ≥0∞) * (2 * psiSup ψ d) := by
        gcongr
        exact_mod_cast le_trans (card_numerators_le d) hcard
    _ = 4 * psiStar ψ d := by
        rw [psiStar_eq]
        push_cast
        ring

theorem psiSup_ne_top (ψ : ℕ+ → ℝ≥0) (hψ : ∑' q : ℕ+, psiStar ψ q < ⊤) (d : ℕ+) :
    psiSup ψ d ≠ ⊤ := by
  intro h
  refine ENNReal.ne_top_of_tsum_ne_top hψ.ne d ?_
  rw [psiStar_eq, h, ENNReal.mul_top]
  exact_mod_cast (Nat.totient_pos.mpr d.pos).ne'

theorem tsum_volume_coverE_ne_top (ψ : ℕ+ → ℝ≥0) (hψ : ∑' q : ℕ+, psiStar ψ q < ⊤) :
    ∑' d : ℕ+, volume (coverE ψ d) ≠ ⊤ := by
  have : ∑' d : ℕ+, volume (coverE ψ d) ≤ 4 * ∑' d : ℕ+, psiStar ψ d := by
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun d => volume_coverE_le ψ d (psiSup_ne_top ψ hψ d)
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) hψ.ne) this

/-! ### Summability of the radii -/

theorem ratio_toReal (ψ : ℕ+ → ℝ≥0) (q : ℕ+) :
    ((ψ q : ℝ≥0∞) / (q : ℝ≥0∞)).toReal = (ψ q : ℝ) / ((q : ℕ) : ℝ) := by
  rw [ENNReal.toReal_div]
  simp

theorem tsum_ratio_ne_top (ψ : ℕ+ → ℝ≥0) (hψ : ∑' q : ℕ+, psiStar ψ q < ⊤) :
    ∑' q : ℕ+, (ψ q : ℝ≥0∞) / (q : ℝ≥0∞) ≠ ⊤ :=
  ne_top_of_le_ne_top hψ.ne
    (ENNReal.tsum_le_tsum fun q => le_trans (self_div_le_psiSup ψ q) (psiSup_le_psiStar ψ q))

theorem ratio_ne_top (ψ : ℕ+ → ℝ≥0) (hψ : ∑' q : ℕ+, psiStar ψ q < ⊤) (q : ℕ+) :
    (ψ q : ℝ≥0∞) / (q : ℝ≥0∞) ≠ ⊤ :=
  ENNReal.ne_top_of_tsum_ne_top (tsum_ratio_ne_top ψ hψ) q

/-- **Summability forces `ψ(q)/q → 0`**, in the form used below: only finitely many `q`
have `ψ(q)/q` above a fixed positive threshold. This is what makes each reduced fraction
absorb only finitely many denominators. -/
theorem finite_ratio_ge (ψ : ℕ+ → ℝ≥0) (hψ : ∑' q : ℕ+, psiStar ψ q < ⊤) {δ : ℝ} (hδ : 0 < δ) :
    {q : ℕ+ | δ ≤ (ψ q : ℝ) / ((q : ℕ) : ℝ)}.Finite := by
  refine Set.Finite.subset (ENNReal.finite_const_le_of_tsum_ne_top
    (a := fun q : ℕ+ => (ψ q : ℝ≥0∞) / (q : ℝ≥0∞)) (ε := ENNReal.ofReal δ)
    (tsum_ratio_ne_top ψ hψ) (ENNReal.ofReal_ne_zero_iff.mpr hδ)) fun q hq => ?_
  simp only [Set.mem_ofPred_eq] at hq ⊢
  rw [← ratio_toReal ψ q] at hq
  exact ENNReal.ofReal_le_of_le_toReal hq

/-- `ψ(q)/q ≤ Ψ(d)` whenever `d ∣ q`, in real form. -/
theorem ratio_le_radius (ψ : ℕ+ → ℝ≥0) (hψ : ∑' q : ℕ+, psiStar ψ q < ⊤) {d q : ℕ+}
    (h : d ∣ q) : (ψ q : ℝ) / ((q : ℕ) : ℝ) ≤ radius ψ d := by
  rw [← ratio_toReal ψ q, radius]
  exact ENNReal.toReal_mono (psiSup_ne_top ψ hψ d) (le_psiSup ψ h)

/-! ### The covering -/

/-- Any irrational point of `𝒦(ψ)` lies in infinitely many `E_d`. -/
theorem infinite_coverE_of_mem {ψ : ℕ+ → ℝ≥0} (hψ : ∑' q : ℕ+, psiStar ψ q < ⊤) {α : ℝ}
    (hα : α ∈ setK ψ) (hirr : Irrational α) : {d : ℕ+ | α ∈ coverE ψ d}.Infinite := by
  -- the pairs realising `α ∈ 𝒦(ψ)`
  set P : Set (ℕ × ℕ+) := {p : ℕ × ℕ+ | p.1 ≤ (p.2 : ℕ) ∧ Approximates ψ α p.1 p.2} with hP
  have hPinf : P.Infinite := hα.2
  -- infinitely many denominators, since each `q` admits only finitely many numerators
  set Q : Set ℕ+ := {q : ℕ+ | ∃ a ≤ (q : ℕ), Approximates ψ α a q} with hQ
  have hQinf : Q.Infinite := by
    by_contra hfin
    rw [Set.not_infinite] at hfin
    refine hPinf (Set.Finite.subset (hfin.biUnion (t := fun q : ℕ+ =>
      (fun a : ℕ => (a, q)) '' Set.Iic (q : ℕ))
      fun q _ => (Set.finite_Iic _).image _) fun p hp => ?_)
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_Iic, exists_prop]
    exact ⟨p.2, ⟨p.1, hp.1, hp.2⟩, p.1, hp.1, rfl⟩
  -- for a fixed finite set of reduced denominators, only finitely many `q` can reduce into it
  have hbad : ∀ t : Finset ℕ+,
      {q : ℕ+ | ∃ d ∈ t, ∃ b ∈ numerators d,
        |α - (b : ℝ) / ((d : ℕ) : ℝ)| ≤ (ψ q : ℝ) / ((q : ℕ) : ℝ)}.Finite := by
    intro t
    refine Set.Finite.subset (Set.Finite.biUnion t.finite_toSet fun d _ =>
      Set.Finite.biUnion (numerators d).finite_toSet fun b _ =>
        finite_ratio_ge ψ hψ (δ := |α - (b : ℝ) / ((d : ℕ) : ℝ)|) ?_) ?_
    · exact abs_pos.mpr (sub_ne_zero.mpr (by
        simpa using (hirr.ne_rat ((b : ℚ) / ((d : ℕ) : ℚ)))))
    · intro q hq
      obtain ⟨d, hd, b, hb, hball⟩ := hq
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨d, hd, b, hb, hball⟩
  -- escape every finite set
  refine infinite_of_forall_exists_notMem_finset fun t => ?_
  obtain ⟨q, hqQ, hqbad⟩ := (hQinf.sdiff (hbad t)).nonempty
  obtain ⟨a, haq, happ⟩ := hqQ
  have hcover : α ∈ coverE ψ (redDen a q) := by
    simp only [coverE, Set.mem_iUnion, Metric.mem_closedBall, Real.dist_eq, exists_prop]
    refine ⟨redNum a q, redNum_mem_numerators haq, ?_⟩
    rw [redNum_div_redDen]
    exact le_trans happ (ratio_le_radius ψ hψ (redDen_dvd a q))
  refine ⟨redDen a q, hcover, fun hmem => hqbad ⟨redDen a q, hmem, redNum a q,
    redNum_mem_numerators haq, ?_⟩⟩
  rw [redNum_div_redDen]
  exact happ

/-! ### Theorem 2(a) -/

/-- **Theorem 2(a).** If `∑ ψ⋆(q) < ∞` then `𝒦(ψ)` is null. -/
theorem volume_setK_eq_zero (ψ : ℕ+ → ℝ≥0) (hψ : ∑' q : ℕ+, psiStar ψ q < ⊤) :
    volume (setK ψ) = 0 := by
  have hsub : setK ψ ⊆
      Set.range ((↑) : ℚ → ℝ) ∪ {α : ℝ | {d : ℕ+ | α ∈ coverE ψ d}.Infinite} := by
    intro α hα
    by_cases h : Irrational α
    · exact Or.inr (infinite_coverE_of_mem hψ hα h)
    · exact Or.inl (not_not.mp h)
  refine measure_mono_null hsub (measure_union_null ((Set.countable_range _).measure_zero _) ?_)
  rw [← Filter.cofinite.limsup_set_eq]
  exact measure_limsup_cofinite_eq_zero (tsum_volume_coverE_ne_top ψ hψ)

end DuffinSchaeffer
