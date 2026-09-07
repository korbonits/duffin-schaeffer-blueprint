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

/-- Transfer: `setA ψ` is, modulo a null set, the preimage of Mathlib's well-approximable
set under `ℝ → ℝ/ℤ`.

The null set is no longer the open question: `setA_ae_eq_setAStrict` disposes of the
`≤` versus `<` mismatch, which was the one step here where an error could hide. What
remains is bookkeeping about the quotient, and it is genuinely fiddly rather than deep:
`UnitAddCircle.mem_addWellApproximable_iff` describes membership as
`∃ m < n, gcd m n = 1 ∧ ‖x - m/n‖ < δ n`, so one has to match `m < n` against coprime
`a ≤ q` (they agree: `a = q` forces `q = 1`, and `1/1 ≡ 0/1` on the circle), and match
the quotient norm `‖·‖` against `|·|`, which for `α ∈ [0,1]` and radius at most `1/(2q)`
means checking that only the representatives `a/q` and `a/q ± 1` can be nearest. -/
proof_wanted setA_eq_preimage_addWellApproximable (ψ : ℕ+ → ℝ≥0)
    (hψ : ∀ q, (ψ q : ℝ) ≤ 1 / 2) :
    setA ψ =ᵐ[volume]
      (Set.Icc (0 : ℝ) 1 ∩
        (fun x : ℝ ↦ (x : UnitAddCircle)) ⁻¹' addWellApproximable UnitAddCircle (distSeq ψ))

/-- Gallagher's theorem without the vanishing hypothesis. Mathlib's TODO. -/
proof_wanted addWellApproximable_ae_empty_or_univ_of_nonneg (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) :
    (∀ᵐ x : UnitAddCircle, ¬ addWellApproximable UnitAddCircle δ x) ∨
      ∀ᵐ x : UnitAddCircle, addWellApproximable UnitAddCircle δ x

/-- The reduction the rest of the project rests on: it suffices to prove that `setA ψ`
has *positive* measure. Everything after this chapter is devoted to that. -/
proof_wanted volume_setA_eq_one_of_pos (ψ : ℕ+ → ℝ≥0) (hψ : ∀ q, (ψ q : ℝ) ≤ 1 / 2)
    (hpos : 0 < volume (setA ψ)) :
    volume (setA ψ) = 1

end DuffinSchaeffer
