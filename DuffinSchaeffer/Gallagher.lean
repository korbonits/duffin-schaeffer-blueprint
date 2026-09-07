/- The zero-one law, and the transfer between `[0,1]` and the circle.

   This chapter is the one place where Mathlib has already done the work.
   `AddCircle.addWellApproximable_ae_empty_or_univ` (Oliver Nash, 2022,
   `Mathlib/NumberTheory/WellApproximable.lean`) is Gallagher's ergodic theorem:
   for any sequence of distances the well-approximable set is null or co-null.
   That file's own docstring names Koukoulopoulos-Maynard as the missing criterion
   deciding which case occurs, and says it is not formalised there. This project is
   that criterion.

   Two things remain to be done here.

   1. Transfer. Mathlib works on `AddCircle T`; the Annals statement works on
      `[0,1] ⊆ ℝ`. The quotient `ℝ → ℝ/ℤ` is measure-preserving on `[0,1)`, so this
      is bookkeeping, but it is bookkeeping that has to happen before Gallagher can
      be applied to `setA`.

   2. Dropping the `Tendsto δ atTop (𝓝 0)` hypothesis. Mathlib's Gallagher assumes
      the distances tend to zero; the Duffin-Schaeffer hypothesis does not give
      that. Mathlib's own TODO already records the fix ("An elementary
      (non-measure-theoretic) argument shows that if `¬ hδ` holds then
      `addWellApproximable 𝕊 δ = univ`"). This is a self-contained contribution
      that belongs upstream rather than here. -/
import DuffinSchaeffer.Basic

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace DuffinSchaeffer

/-- The sequence of distances attached to `ψ`, in the shape Mathlib's
`addWellApproximable` expects: `δ n = ψ n / n`, extended by `0` at `n = 0`. -/
noncomputable def distSeq (ψ : ℕ+ → ℝ≥0) : ℕ → ℝ :=
  fun n ↦ if h : 0 < n then (ψ ⟨n, h⟩ : ℝ) / (n : ℝ) else 0

/-! ### The strict form

Mathlib's `addWellApproximable` uses a strict inequality `‖x - m/n‖ < δ n`, while (1.7)
and hence `setA` use `≤`. The two differ, but only on a null set, and pinning that down
is the one step of the transfer where an error would not be visible: everything else is
bookkeeping about the quotient map. -/

/-- (1.7) with a strict inequality. -/
def ApproximatesStrict (ψ : ℕ+ → ℝ≥0) (α : ℝ) (a : ℕ) (q : ℕ+) : Prop :=
  |α - a / q| < ψ q / q

/-- The strict-inequality analogue of `setA`, which is the shape Mathlib's
`addWellApproximable` takes. -/
def setAStrict (ψ : ℕ+ → ℝ≥0) : Set ℝ :=
  {α ∈ Set.Icc (0 : ℝ) 1 |
    {(a, q) : ℕ × ℕ+ | Nat.Coprime a q ∧ ApproximatesStrict ψ α a q}.Infinite}

theorem setAStrict_subset (ψ : ℕ+ → ℝ≥0) : setAStrict ψ ⊆ setA ψ := by
  rintro α ⟨hα01, hinf⟩
  exact ⟨hα01, hinf.mono fun p hp => ⟨hp.1, le_of_lt hp.2⟩⟩

/-- The endpoints: the countably many reals sitting exactly on the boundary of some
approximation interval. -/
def endpoints (ψ : ℕ+ → ℝ≥0) : Set ℝ :=
  (Set.range fun p : ℕ × ℕ+ => (p.1 : ℝ) / p.2 + (ψ p.2 : ℝ) / p.2) ∪
    (Set.range fun p : ℕ × ℕ+ => (p.1 : ℝ) / p.2 - (ψ p.2 : ℝ) / p.2)

theorem countable_endpoints (ψ : ℕ+ → ℝ≥0) : (endpoints ψ).Countable :=
  (Set.countable_range _).union (Set.countable_range _)

/-- Off the endpoints, `≤` and `<` define the same set. -/
theorem setA_sdiff_subset_endpoints (ψ : ℕ+ → ℝ≥0) :
    setA ψ \ setAStrict ψ ⊆ endpoints ψ := by
  rintro α ⟨⟨hα01, hinf⟩, hnot⟩
  by_contra hE
  refine hnot ⟨hα01, hinf.mono fun p hp => ⟨hp.1, ?_⟩⟩
  rcases lt_or_eq_of_le hp.2 with h | h
  · exact h
  · exfalso
    -- equality puts `α` at an endpoint
    have hnn : (0 : ℝ) ≤ (ψ p.2 : ℝ) / p.2 := by positivity
    rcases (abs_eq hnn).mp h with h' | h'
    · exact hE (Or.inl ⟨p, by linarith⟩)
    · exact hE (Or.inr ⟨p, by linarith⟩)

/-- `setA` and its strict form agree almost everywhere. -/
theorem setA_ae_eq_setAStrict (ψ : ℕ+ → ℝ≥0) : setA ψ =ᵐ[volume] setAStrict ψ := by
  rw [MeasureTheory.ae_eq_set]
  refine ⟨measure_mono_null (setA_sdiff_subset_endpoints ψ) ?_, ?_⟩
  · exact (countable_endpoints ψ).measure_zero _
  · simp [Set.sdiff_eq_empty.mpr (setAStrict_subset ψ)]

/-! ### Denominators for the strict form -/

/-- The strict analogue of `setAq`. -/
def setAqStrict (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : Set ℝ :=
  {α ∈ Set.Icc (0 : ℝ) 1 | ∃ a : ℕ, Nat.Coprime a q ∧ ApproximatesStrict ψ α a q}

theorem distSeq_coe (ψ : ℕ+ → ℝ≥0) (q : ℕ+) :
    distSeq ψ (q : ℕ) = (ψ q : ℝ) / ((q : ℕ) : ℝ) := by
  have hq : (⟨(q : ℕ), q.pos⟩ : ℕ+) = q := rfl
  simp [distSeq, q.pos, hq]

/-- The strict analogue of `mem_setA_iff`: infinitely many pairs is infinitely many
denominators. Same proof, and it rests on the same numerator bound. -/
theorem mem_setAStrict_iff (ψ : ℕ+ → ℝ≥0) (hψ : ∀ q, (ψ q : ℝ) ≤ 1 / 2) (α : ℝ) :
    α ∈ setAStrict ψ ↔ α ∈ Set.Icc (0 : ℝ) 1 ∧ {q : ℕ+ | α ∈ setAqStrict ψ q}.Infinite := by
  constructor
  · rintro ⟨hα01, hinf⟩
    refine ⟨hα01, ?_⟩
    by_contra hfin
    rw [Set.not_infinite] at hfin
    refine hinf (Set.Finite.subset (hfin.biUnion (t := fun q : ℕ+ =>
      (fun a : ℕ => (a, q)) '' Set.Iic (q : ℕ)) fun q _ => (Set.finite_Iic _).image _) ?_)
    rintro ⟨a, q⟩ ⟨hcop, happ⟩
    have haq : a ≤ (q : ℕ) := le_of_approximates (hψ q) hα01 (le_of_lt happ)
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_Iic, exists_prop]
    exact ⟨q, ⟨hα01, a, hcop, happ⟩, a, haq, rfl⟩
  · rintro ⟨hα01, hinf⟩
    refine ⟨hα01, ?_⟩
    have hex : ∀ q ∈ {q : ℕ+ | α ∈ setAqStrict ψ q},
        ∃ a : ℕ, Nat.Coprime a q ∧ ApproximatesStrict ψ α a q := fun q hq => hq.2
    choose! g hg1 hg2 using hex
    have himg : ((fun q : ℕ+ => (g q, q)) '' {q : ℕ+ | α ∈ setAqStrict ψ q}).Infinite :=
      hinf.image fun _ _ _ _ h => congrArg Prod.snd h
    refine himg.mono ?_
    rintro p ⟨q, hq, rfl⟩
    exact ⟨hg1 q hq, hg2 q hq⟩

/-! ### The circle norm against the absolute value

Mathlib states well-approximability with the quotient norm on `ℝ/ℤ`; (1.7) uses `|·|` on
`ℝ`. On `[0,1]` these agree wherever it matters, but not everywhere: `α = 0.9` and
`m/n = 0.1` are at circle distance `0.2` and real distance `0.8`. The point of the
lemmas below is that under `ψ ≤ 1/2` the discrepant case never produces a solution. -/

theorem norm_coe_eq_abs {x : ℝ} (h : |x| ≤ 1 / 2) : ‖(x : UnitAddCircle)‖ = |x| :=
  (AddCircle.norm_coe_eq_abs_iff 1 (by norm_num)).mpr (by simpa using h)

theorem norm_coe_of_gt {x : ℝ} (h1 : (1 : ℝ) / 2 < x) (h2 : x ≤ 1) :
    ‖(x : UnitAddCircle)‖ = 1 - x := by
  rw [AddCircle.norm_eq]
  have hr : round ((1 : ℝ)⁻¹ * x) = 1 := by
    rw [round_eq, inv_one, one_mul, Int.floor_eq_iff]
    constructor <;> push_cast <;> linarith
  rw [hr]
  push_cast
  rw [abs_of_nonpos (by linarith)]
  ring

theorem norm_coe_of_lt {x : ℝ} (h1 : x < -(1 / 2)) (h2 : -1 ≤ x) :
    ‖(x : UnitAddCircle)‖ = 1 + x := by
  rw [AddCircle.norm_eq]
  have hr : round ((1 : ℝ)⁻¹ * x) = -1 := by
    rw [round_eq, inv_one, one_mul, Int.floor_eq_iff]
    constructor <;> push_cast <;> linarith
  rw [hr]
  push_cast
  rw [abs_of_nonneg (by linarith)]
  ring

/-- **The circle and real conditions agree.** For `n ≥ 2` and `1 ≤ m ≤ n - 1`, a point of
`[0,1]` is within `δ ≤ 1/(2n)` of `m/n` on the circle exactly when it is on the line.

The far case is excluded by counting: `|α - m/n| ≤ 1 - 1/n`, so if the real distance
exceeds `1/2` then the circle distance is `1 - |α - m/n| ≥ 1/n > δ`, and neither side
holds. This is where the truncation `ψ ≤ 1/2` pays for itself a second time. -/
theorem norm_lt_iff_abs_lt {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) {m n : ℕ} (hn : 2 ≤ n)
    (hm : 1 ≤ m) (hmn : m + 1 ≤ n) {δ : ℝ} (hδ : δ ≤ 1 / (2 * n)) :
    ‖((α - (m : ℝ) / n : ℝ) : UnitAddCircle)‖ < δ ↔ |α - (m : ℝ) / n| < δ := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmnR : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
  have hlow : 1 / (n : ℝ) ≤ (m : ℝ) / n := by
    rw [div_le_div_iff_of_pos_right hn0]; exact hmR
  have hhigh : (m : ℝ) / n ≤ 1 - 1 / n := by
    rw [div_le_iff₀ hn0]
    have : (1 : ℝ) - 1 / n = ((n : ℝ) - 1) / n := by field_simp
    rw [this, div_mul_cancel₀ _ hn0.ne']
    linarith
  have hxub : α - (m : ℝ) / n ≤ 1 - 1 / n := by linarith [hα.2, hlow]
  have hxlb : -(1 - 1 / (n : ℝ)) ≤ α - (m : ℝ) / n := by linarith [hα.1, hhigh]
  have habs : |α - (m : ℝ) / n| ≤ 1 - 1 / n := abs_le.mpr ⟨hxlb, hxub⟩
  have hdn : δ ≤ 1 / (2 * (n : ℝ)) := hδ
  have hinvpos : (0 : ℝ) < 1 / n := by positivity
  have hinv : 1 / (2 * (n : ℝ)) < 1 / (n : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity) hn0]; linarith
  by_cases hc : |α - (m : ℝ) / n| ≤ 1 / 2
  · rw [norm_coe_eq_abs hc]
  · push Not at hc
    have hnorm : ‖((α - (m : ℝ) / n : ℝ) : UnitAddCircle)‖ = 1 - |α - (m : ℝ) / n| := by
      rcases abs_cases (α - (m : ℝ) / n) with ⟨he, _⟩ | ⟨he, _⟩
      · rw [norm_coe_of_gt (by linarith) (by linarith)]; linarith
      · rw [norm_coe_of_lt (by linarith) (by linarith)]; linarith
    constructor
    · intro h
      exfalso
      rw [hnorm] at h
      have : 1 / (n : ℝ) ≤ 1 - |α - (m : ℝ) / n| := by linarith
      linarith
    · intro h
      exfalso
      linarith

/-- At each denominator, the strict real condition matches Mathlib's circle condition.

Three separate mismatches are reconciled here: the numerator range (`m < q` against
coprime `a` with no bound), the norm (Lemma `norm_lt_iff_abs_lt`), and `q = 1`, where
Mathlib's only admissible numerator is `m = 0` while the real condition also allows
`a = 1`. They agree because `0/1` and `1/1` are the same point of the circle. -/
theorem mem_setAqStrict_iff_circle (ψ : ℕ+ → ℝ≥0) (hψ : ∀ q, (ψ q : ℝ) ≤ 1 / 2) {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (q : ℕ+) :
    α ∈ setAqStrict ψ q ↔
      ∃ m < (q : ℕ), gcd m (q : ℕ) = 1 ∧
        ‖(α : UnitAddCircle) - (((m : ℝ) / ((q : ℕ) : ℝ) : ℝ) : UnitAddCircle)‖
          < distSeq ψ (q : ℕ) := by
  have hq0 : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.pos
  have hδ : (ψ q : ℝ) / ((q : ℕ) : ℝ) ≤ 1 / (2 * ((q : ℕ) : ℝ)) := by
    rw [div_le_div_iff₀ hq0 (by positivity)]
    nlinarith [hψ q, hq0]
  simp only [distSeq_coe, ← AddCircle.coe_sub]
  by_cases hq1 : q = 1
  · -- `q = 1`: Mathlib allows only `m = 0`, the real condition also `a = 1`; same point.
    subst hq1
    have hψ1 : (ψ 1 : ℝ) ≤ 1 / 2 := hψ 1
    simp only [PNat.one_coe, Nat.cast_one, div_one]
    constructor
    · rintro ⟨-, a, -, happ⟩
      simp only [ApproximatesStrict, PNat.one_coe, Nat.cast_one, div_one] at happ
      have hab := abs_lt.mp happ
      have ha2 : (a : ℝ) < 2 := by linarith [hα.1, hα.2]
      have ha2' : a < 2 := by exact_mod_cast ha2
      refine ⟨0, by norm_num, by norm_num, ?_⟩
      simp only [Nat.cast_zero, sub_zero]
      interval_cases a
      · push_cast at hab happ
        rw [norm_coe_eq_abs (by rw [abs_of_nonneg hα.1]; linarith)]
        simpa using happ
      · push_cast at hab
        rw [norm_coe_of_gt (by linarith) hα.2]
        linarith
    · rintro ⟨m, hm, -, hnorm⟩
      have hm0 : m = 0 := by omega
      subst hm0
      simp only [Nat.cast_zero, sub_zero] at hnorm
      refine ⟨hα, ?_⟩
      by_cases hhalf : α ≤ 1 / 2
      · refine ⟨0, by simp, ?_⟩
        rw [norm_coe_eq_abs (by rw [abs_of_nonneg hα.1]; linarith)] at hnorm
        simpa [ApproximatesStrict] using hnorm
      · push Not at hhalf
        refine ⟨1, by simp, ?_⟩
        rw [norm_coe_of_gt hhalf hα.2] at hnorm
        simp only [ApproximatesStrict, PNat.one_coe, Nat.cast_one, div_one]
        rw [abs_of_nonpos (by linarith [hα.2])]
        linarith
  · -- `q ≥ 2`: coprimality confines the numerator to `1 ≤ a ≤ q - 1`.
    have hq2 : 2 ≤ (q : ℕ) := by
      have h1 : (q : ℕ) ≠ 1 := fun h => hq1 (PNat.coe_eq_one_iff.mp h)
      have := q.pos
      omega
    constructor
    · rintro ⟨-, a, hcop, happ⟩
      have haq : a ≤ (q : ℕ) := le_of_approximates (hψ q) hα (le_of_lt happ)
      have ha0 : 1 ≤ a := by
        rcases Nat.eq_zero_or_pos a with rfl | h
        · exact absurd (by simpa [Nat.Coprime] using hcop) (by omega)
        · exact h
      have haq' : a + 1 ≤ (q : ℕ) := by
        rcases Nat.lt_or_ge a (q : ℕ) with h | h
        · omega
        · exact absurd (by simpa [Nat.Coprime, show a = (q : ℕ) by omega] using hcop) (by omega)
      exact ⟨a, by omega, hcop, (norm_lt_iff_abs_lt hα hq2 ha0 haq' hδ).mpr happ⟩
    · rintro ⟨m, hm, hcop, hnorm⟩
      have hm0 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · exact absurd (by simpa using hcop) (by omega)
        · exact h
      exact ⟨hα, m, hcop, (norm_lt_iff_abs_lt hα hq2 hm0 (by omega) hδ).mp hnorm⟩

/-- The strict form is *exactly* the preimage: no null sets involved once
`mem_setAqStrict_iff_circle` has matched the two conditions denominator by denominator. -/
theorem setAStrict_eq_preimage (ψ : ℕ+ → ℝ≥0) (hψ : ∀ q, (ψ q : ℝ) ≤ 1 / 2) :
    setAStrict ψ = Set.Icc (0 : ℝ) 1 ∩
      (fun x : ℝ ↦ (x : UnitAddCircle)) ⁻¹' addWellApproximable UnitAddCircle (distSeq ψ) := by
  ext α
  simp only [Set.mem_inter_iff, Set.mem_preimage, UnitAddCircle.mem_addWellApproximable_iff]
  rw [mem_setAStrict_iff ψ hψ]
  refine and_congr_right fun hα => ?_
  have hset : {n : ℕ | ∃ m < n, gcd m n = 1 ∧
      ‖(α : UnitAddCircle) - (((m : ℝ) / (n : ℝ) : ℝ) : UnitAddCircle)‖ < distSeq ψ n}
      = (fun q : ℕ+ => (q : ℕ)) '' {q : ℕ+ | α ∈ setAqStrict ψ q} := by
    ext n
    constructor
    · rintro ⟨m, hmn, hcop, hnorm⟩
      have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le m) hmn
      exact ⟨⟨n, hn⟩, (mem_setAqStrict_iff_circle ψ hψ hα ⟨n, hn⟩).mpr
        ⟨m, hmn, hcop, hnorm⟩, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact (mem_setAqStrict_iff_circle ψ hψ hα q).mp hq
  rw [hset]
  exact (Set.infinite_image_iff fun _ _ _ _ h => PNat.coe_injective h).symm

/-- Transfer: `setA ψ` is, modulo a null set, the preimage of Mathlib's well-approximable
set under `ℝ → ℝ/ℤ`.

The null set is `setA_ae_eq_setAStrict`'s countable set of endpoints; everything else is
an exact equality. -/
theorem setA_eq_preimage_addWellApproximable (ψ : ℕ+ → ℝ≥0)
    (hψ : ∀ q, (ψ q : ℝ) ≤ 1 / 2) :
    setA ψ =ᵐ[volume]
      (Set.Icc (0 : ℝ) 1 ∩
        (fun x : ℝ ↦ (x : UnitAddCircle)) ⁻¹' addWellApproximable UnitAddCircle (distSeq ψ)) := by
  rw [← setAStrict_eq_preimage ψ hψ]
  exact setA_ae_eq_setAStrict ψ

/-- Gallagher's theorem without the vanishing hypothesis. Mathlib's TODO. -/
proof_wanted addWellApproximable_ae_empty_or_univ_of_nonneg (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) :
    (∀ᵐ x : UnitAddCircle, ¬ addWellApproximable UnitAddCircle δ x) ∨
      ∀ᵐ x : UnitAddCircle, addWellApproximable UnitAddCircle δ x

theorem measurableSet_addWellApproximable (δ : ℕ → ℝ) :
    MeasurableSet (addWellApproximable UnitAddCircle δ) := by
  unfold addWellApproximable
  rw [Filter.blimsup_eq_iInf_biSup_of_nat]
  exact MeasurableSet.iInter fun n => MeasurableSet.biUnion (Set.to_countable _)
    fun i _ => Metric.isOpen_thickening.measurableSet

/-- Under the truncation the distances tend to zero, so Mathlib's Gallagher applies as
stated and the mathlib TODO `addWellApproximable_ae_empty_or_univ_of_nonneg` is not
needed on this path. -/
theorem tendsto_distSeq (ψ : ℕ+ → ℝ≥0) (hψ : ∀ q, (ψ q : ℝ) ≤ 1 / 2) :
    Tendsto (distSeq ψ) atTop (nhds 0) := by
  refine squeeze_zero (fun n => ?_) (fun n => ?_) tendsto_one_div_atTop_nhds_zero_nat
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [distSeq]
    · have hd : distSeq ψ n = (ψ ⟨n, hn⟩ : ℝ) / n := by simp [distSeq, hn]
      rw [hd]; positivity
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [distSeq]
    · have hd : distSeq ψ n = (ψ ⟨n, hn⟩ : ℝ) / n := by simp [distSeq, hn]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [hd, div_le_div_iff_of_pos_right hn0]
      linarith [hψ ⟨n, hn⟩]

/-- The reduction the rest of the project rests on: it suffices to prove that `setA ψ`
has *positive* measure. Everything after this chapter is devoted to that. -/
theorem volume_setA_eq_one_of_pos (ψ : ℕ+ → ℝ≥0) (hψ : ∀ q, (ψ q : ℝ) ≤ 1 / 2)
    (hpos : 0 < volume (setA ψ)) :
    volume (setA ψ) = 1 := by
  set W := addWellApproximable UnitAddCircle (distSeq ψ) with hWdef
  have hWmeas : MeasurableSet W := measurableSet_addWellApproximable _
  set P : Set ℝ := Set.Icc (0 : ℝ) 1 ∩ (fun x : ℝ => (x : UnitAddCircle)) ⁻¹' W with hPdef
  have hae : volume (setA ψ) = volume P :=
    measure_congr (setA_eq_preimage_addWellApproximable ψ hψ)
  have hproj : volume W = volume ((QuotientAddGroup.mk ⁻¹' W) ∩ Set.Ioc (0 : ℝ) 1) := by
    have h := AddCircle.add_projection_respects_measure (1 : ℝ) 0 hWmeas
    simpa using h
  rcases AddCircle.addWellApproximable_ae_empty_or_univ (T := (1 : ℝ)) (distSeq ψ)
    (tendsto_distSeq ψ hψ) with h | h
  · exfalso
    have hW0 : volume W = 0 := by rw [MeasureTheory.ae_iff] at h; simpa using h
    have hPnull : volume P = 0 := by
      refine measure_mono_null
        (?_ : P ⊆ {(0 : ℝ)} ∪ ((QuotientAddGroup.mk ⁻¹' W) ∩ Set.Ioc (0 : ℝ) 1)) ?_
      · rintro x ⟨hx01, hxW⟩
        rcases eq_or_lt_of_le hx01.1 with heq | hlt
        · exact Or.inl heq.symm
        · exact Or.inr ⟨hxW, hlt, hx01.2⟩
      · exact measure_union_null (by simp) (by rw [← hproj, hW0])
    rw [hae, hPnull] at hpos
    exact lt_irrefl 0 hpos
  · have hWuniv : volume W = 1 := by
      have hc : volume Wᶜ = 0 := by rw [MeasureTheory.ae_iff] at h; exact h
      have hsum := measure_add_measure_compl (μ := (volume : Measure UnitAddCircle)) hWmeas
      rw [hc, add_zero] at hsum
      rw [hsum, AddCircle.measure_univ]
      simp
    have hge : (1 : ℝ≥0∞) ≤ volume P := by
      calc (1 : ℝ≥0∞) = volume W := hWuniv.symm
        _ = volume ((QuotientAddGroup.mk ⁻¹' W) ∩ Set.Ioc (0 : ℝ) 1) := hproj
        _ ≤ volume P := measure_mono (by
            rintro x ⟨hxW, hx⟩
            exact ⟨⟨le_of_lt hx.1, hx.2⟩, hxW⟩)
    have hle : volume P ≤ 1 := by
      calc volume P ≤ volume (Set.Icc (0 : ℝ) 1) := measure_mono Set.inter_subset_left
        _ = 1 := by simp
    rw [hae]
    exact le_antisymm hle hge

end DuffinSchaeffer


