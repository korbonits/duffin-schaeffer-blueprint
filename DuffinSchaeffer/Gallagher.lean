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

/-- Transfer: `setA ψ` is, modulo the null set of endpoints, the preimage of Mathlib's
well-approximable set under `ℝ → ℝ/ℤ`. -/
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
