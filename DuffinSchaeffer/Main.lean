/- The terminal nodes.

   These three statements are transcribed from
   ImperialCollegeLondon/AnnalsChallenge, file
   `AnnalsChallenge/AnnalsOfMathematics/2020-192-1-DuffinSchaefferConjecture.lean`
   (Katerina Hristova and Kevin Buzzard, Apache 2.0), where they stand as `sorry`.
   Proving them here proves them there.

   Theorem 1 is the conjecture. Theorem 2(a) is the easy convergence half: the first
   Borel-Cantelli lemma applied to the majorant `ψ⋆`, and it needs none of the GCD
   graph machinery -- it is the right place to start writing actual proofs. Theorem
   2(b) is the divergence half and reduces to Theorem 1.

   Corollary 3 of the paper is *not* here; see `Hausdorff.lean` for why. -/
import DuffinSchaeffer.Gallagher
import DuffinSchaeffer.ChungErdos
import DuffinSchaeffer.Overlap
import DuffinSchaeffer.Convergence

open MeasureTheory Set Filter
open scoped ENNReal NNReal Nat

namespace DuffinSchaeffer

/-! ### The reduction to `ψ ≤ 1/2`

Transcribed from the paper, §5 (the proof of Theorem 1 assuming Proposition 5.4). An
earlier version of this file guessed the reduction and guessed wrong: it used the
truncation `min(ψ, 1/2)`. The paper splits `ψ` *additively by restriction* instead,

  `ψ = ψ₁ + ψ₂`,  `ψ₁ = ψ · 1[ψ > 1/2]`,  `ψ₂ = ψ · 1[ψ ≤ 1/2]`,

which is a different function: where `ψ(q) = 5`, the truncation gives `1/2` but `ψ₂`
gives `0`. That matters, because the two cases are then genuinely disjoint and the large
one is a known theorem rather than something to be reconstructed. -/

/-- `ψ` restricted to where it exceeds `1/2`. -/
noncomputable def psiLarge (ψ : ℕ+ → ℝ≥0) : ℕ+ → ℝ≥0 := fun q => if 1 / 2 < ψ q then ψ q else 0

/-- `ψ` restricted to where it is at most `1/2`. -/
noncomputable def psiSmall (ψ : ℕ+ → ℝ≥0) : ℕ+ → ℝ≥0 := fun q => if ψ q ≤ 1 / 2 then ψ q else 0

theorem psiLarge_add_psiSmall (ψ : ℕ+ → ℝ≥0) (q : ℕ+) :
    psiLarge ψ q + psiSmall ψ q = ψ q := by
  simp only [psiLarge, psiSmall]
  split_ifs with h1 h2 h2
  · exact absurd h2 (not_le.mpr h1)
  · exact add_zero _
  · exact zero_add _
  · exact absurd (not_lt.mp h1) h2

theorem psiLarge_le (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : psiLarge ψ q ≤ ψ q := by
  simp only [psiLarge]; split_ifs; exacts [le_rfl, zero_le]

theorem psiSmall_le (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : psiSmall ψ q ≤ ψ q := by
  simp only [psiSmall]; split_ifs; exacts [le_rfl, zero_le]

theorem psiSmall_le_half (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : ((psiSmall ψ q : ℝ≥0) : ℝ) ≤ 1 / 2 := by
  simp only [psiSmall]
  split_ifs with h
  · exact_mod_cast h
  · norm_num

/-- **The Duffin-Schaeffer conjecture when `ψ` takes only large values**
(paper, Lemma 5.2).

This is an *external* input, not something the paper proves: it is deduced there from
Theorem 2 of Pollington and Vaughan, *The k-dimensional Duffin and Schaeffer conjecture*,
Mathematika 37 (1990), 190-200. Formalizing it means formalizing that paper's Theorem 2,
which is a separate project.

Isolating it is the point. What used to be a vague "the truncation reduction is not
valid as stated" is now one provable reduction (`volume_setA_eq_one_of_untruncated`
below) plus this one clearly-attributed citation. -/
proof_wanted setA_of_large_values (ψ : ℕ+ → ℝ≥0)
    (hlarge : ∀ q, ψ q = 0 ∨ (1 : ℝ) / 2 ≤ ψ q)
    (hdiv : ¬ Summable fun q : ℕ+ ↦ (ψ q : ℝ) * (φ (q : ℕ) : ℝ) / (q : ℝ)) :
    volume (setA ψ) = 1

/-- **The reduction to `ψ ≤ 1/2`** (paper §5), in the case where the divergence comes
from the large values.

Proved, taking Lemma 5.2 as an explicit hypothesis rather than smuggling it in -- the
same pattern as `setA_truncate` with the zero-one law. Given Lemma 5.2 the argument is
two lines: `ψ₁` satisfies its hypothesis by construction, and `ψ₁ ≤ ψ` gives
`setA ψ₁ ⊆ setA ψ`.

So the case analysis of §5 is now fully accounted for. If the divergence survives
restriction to `ψ ≤ 1/2` the main argument applies; otherwise it lives on `ψ₁` and this
lemma applies. Nothing is left vague. -/
theorem volume_setA_eq_one_of_psiLarge_diverges (ψ : ℕ+ → ℝ≥0)
    (hLemma52 : ∀ ψ' : ℕ+ → ℝ≥0, (∀ q, ψ' q = 0 ∨ (1 : ℝ) / 2 ≤ (ψ' q : ℝ)) →
      (¬ Summable fun q : ℕ+ ↦ (ψ' q : ℝ) * (φ (q : ℕ) : ℝ) / (q : ℝ)) →
      volume (setA ψ') = 1)
    (hdiv : ¬ Summable fun q : ℕ+ ↦
      ((psiLarge ψ q : ℝ≥0) : ℝ) * (φ (q : ℕ) : ℝ) / (q : ℝ)) :
    volume (setA ψ) = 1 := by
  have hcond : ∀ q, psiLarge ψ q = 0 ∨ (1 : ℝ) / 2 ≤ ((psiLarge ψ q : ℝ≥0) : ℝ) := by
    intro q
    simp only [psiLarge]
    split_ifs with h
    · exact Or.inr (le_of_lt (by exact_mod_cast h))
    · exact Or.inl rfl
  have h1 := hLemma52 (psiLarge ψ) hcond hdiv
  refine le_antisymm ?_ ?_
  · calc volume (setA ψ) ≤ volume (Set.Icc (0 : ℝ) 1) :=
          measure_mono fun x hx => hx.1
      _ = 1 := by simp
  · rw [← h1]
    exact measure_mono (setA_mono (psiLarge_le ψ))

/-- **The Duffin-Schaeffer conjecture** (Koukoulopoulos-Maynard, Theorem 1).
If `∑ ψ(q) φ(q) / q` diverges then almost every `α ∈ [0,1]` has infinitely many
coprime solutions to `|α - a/q| ≤ ψ(q)/q`. -/
proof_wanted theorem_1 (ψ : ℕ+ → ℝ≥0)
    (hdiv : ¬ Summable fun q : ℕ+ ↦ (ψ q : ℝ) * (φ (q : ℕ) : ℝ) / (q : ℝ)) :
    MeasurableSet (setA ψ) ∧ volume (setA ψ) = 1

/-- **Theorem 2(a)**: the convergence half, without coprimality. Proved; see
`DuffinSchaeffer/Convergence.lean`. -/
theorem theorem_2_a (ψ : ℕ+ → ℝ≥0) (hψ : ∑' q : ℕ+, psiStar ψ q < ⊤) :
    MeasurableSet (setK ψ) ∧ volume (setK ψ) = 0 :=
  ⟨measurableSet_setK ψ, volume_setK_eq_zero ψ hψ⟩

/-- Theorem 2(b): the divergence half, without coprimality. Reduces to Theorem 1 by
applying it to a function built from `ψ⋆`. -/
proof_wanted theorem_2_b (ψ : ℕ+ → ℝ≥0) (hψ : ∑' q : ℕ+, psiStar ψ q = ⊤) :
    MeasurableSet (setK ψ) ∧ volume (setK ψ) = 1

end DuffinSchaeffer
