import LOOConcentrationManuscript.Frozen.Definitions.EmpiricalMean
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Moments.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem empiricalMean_memLp_two_of_coordinates
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (r : ℕ) (X : Fin (r + 1) → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) :
    MemLp (fun ω => empiricalMean r (WithLp.toLp 2 (fun i => X i ω))) 2 P := by
  have hsum : MemLp (fun ω => ∑ i : Fin (r + 1), X i ω) 2 P := by
    simpa using (memLp_finsetSum (s := Finset.univ) (f := X)
      (fun i _ => hX i))
  simpa only [empiricalMean] using
    hsum.const_mul (((r + 1 : ℕ) : ℝ)⁻¹)

theorem empiricalMean_quadraticLoss_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (r : ℕ) (X : Fin (r + 1) → Ω → ℝ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) P μ)
    (z : ℝ) :
    Integrable
      (fun ω => (empiricalMean r (WithLp.toLp 2 (fun i => X i ω)) - z) ^ 2) P := by
  have hIdLp : MemLp (id : ℝ → ℝ) 2 μ := by
    exact (memLp_two_iff_integrable_sq
      (measurable_id.aestronglyMeasurable)).2 hSecond
  have hXLp : ∀ i, MemLp (X i) 2 P := by
    intro i
    exact (hLaw i).memLp_iff.mpr hIdLp
  have hMeanLp := empiricalMean_memLp_two_of_coordinates P r X hXLp
  have hCenteredLp : MemLp
      (fun ω => empiricalMean r (WithLp.toLp 2 (fun i => X i ω)) - z) 2 P :=
    hMeanLp.sub (memLp_const z)
  exact hCenteredLp.integrable_sq

theorem empiricalMean_deleteAndFull_quadraticLoss_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (n : ℕ) (X : Fin (n + 3) → Ω → ℝ)
    (hLaw : ∀ j, IdentDistrib (X j) (id : ℝ → ℝ) P μ) :
    ∀ i : Fin (n + 2),
      Integrable
        (fun ω => (empiricalMean n (WithLp.toLp 2
          (fun j : Fin (n + 1) => X ((i.succAbove j).castSucc) ω)) -
          X i.castSucc ω) ^ 2) P ∧
      Integrable
        (fun ω => (empiricalMean (n + 1) (WithLp.toLp 2
          (fun j : Fin (n + 2) => X j.castSucc ω)) -
          X (Fin.last (n + 2)) ω) ^ 2) P := by
  have hIdLp : MemLp (id : ℝ → ℝ) 2 μ := by
    exact (memLp_two_iff_integrable_sq
      (measurable_id.aestronglyMeasurable)).2 hSecond
  have hXLp : ∀ j, MemLp (X j) 2 P := by
    intro j
    exact (hLaw j).memLp_iff.mpr hIdLp
  intro i
  have hDeletedMean : MemLp
      (fun ω => empiricalMean n (WithLp.toLp 2
        (fun j : Fin (n + 1) => X ((i.succAbove j).castSucc) ω)) ) 2 P := by
    apply empiricalMean_memLp_two_of_coordinates
    intro j
    exact hXLp ((i.succAbove j).castSucc)
  have hDeletedContrast : MemLp
      (fun ω => empiricalMean n (WithLp.toLp 2
        (fun j : Fin (n + 1) => X ((i.succAbove j).castSucc) ω)) -
        X i.castSucc ω) 2 P :=
    hDeletedMean.sub (hXLp i.castSucc)
  have hFullMean : MemLp
      (fun ω => empiricalMean (n + 1) (WithLp.toLp 2
        (fun j : Fin (n + 2) => X j.castSucc ω))) 2 P := by
    apply empiricalMean_memLp_two_of_coordinates
    intro j
    exact hXLp j.castSucc
  have hFullContrast : MemLp
      (fun ω => empiricalMean (n + 1) (WithLp.toLp 2
        (fun j : Fin (n + 2) => X j.castSucc ω)) -
        X (Fin.last (n + 2)) ω) 2 P :=
    hFullMean.sub (hXLp (Fin.last (n + 2)))
  exact ⟨hDeletedContrast.integrable_sq, hFullContrast.integrable_sq⟩

end LOOConcentration.Manuscript.Internal
