import LOOConcentrationRevision.Probability.DiracConsumer
import LOOConcentrationRevision.Geometry.CoordinateTransport
import LOOConcentrationRevision.FunctionalInequalities.LogSobolevConstant

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory
open scoped ENNReal

/-- A probability measure on a singleton carrier is its Dirac law. -/
theorem probabilityMeasure_eq_dirac_of_subsingleton {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] [Subsingleton α]
    (μ : Measure α) [IsProbabilityMeasure μ] (a : α) : μ = Measure.dirac a := by
  classical
  apply Measure.ext
  intro s hs
  by_cases ha : a ∈ s
  · have heq : s = Set.univ := by
      ext x
      simp only [Set.mem_univ, iff_true]
      simpa only [Subsingleton.elim x a] using ha
    rw [heq, measure_univ, measure_univ]
  · have heq : s = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      simpa only [Subsingleton.elim x a] using ha
    rw [heq, measure_empty, measure_empty]

/-- Empty coordinate types are covered without a positive-energy witness. -/
theorem squareEntropy_zero_of_empty_coordinates {ι : Type*}
    [Fintype ι] [DecidableEq ι] [IsEmpty ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (f : Lp ℝ 2 μ) : squareEntropy μ f = 0 := by
  have hm : μ = Measure.dirac (0 : EuclideanSpace ℝ ι) :=
    probabilityMeasure_eq_dirac_of_subsingleton μ 0
  subst μ
  exact squareEntropy_dirac 0 f

/-- The empty gradient carrier has only the zero vector. -/
theorem gradient_eq_zero_of_empty_coordinates {ι : Type*}
    [Fintype ι] [DecidableEq ι] [IsEmpty ι]
    (F : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) : gradient F x = 0 :=
  Subsingleton.elim _ _

/-- Empty coordinates force retained gradient energy to vanish. -/
theorem sobolevEnergy_eq_zero_of_empty_coordinates {ι : Type*}
    [Fintype ι] [DecidableEq ι] [IsEmpty ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (u : SobolevPair μ) : sobolevEnergy μ u = 0 := by
  apply (sobolevEnergy_eq_zero_iff u).mpr
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  exact Filter.Eventually.of_forall fun x => Subsingleton.elim _ _

/-- With no positive-energy pairs, the frozen supremum is zero. -/
theorem logSobolevConstant_eq_zero_of_empty_coordinates {ι : Type*}
    [Fintype ι] [DecidableEq ι] [IsEmpty ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    logSobolevConstant μ = 0 := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro u
  apply iSup_le
  intro hpos
  rw [sobolevEnergy_eq_zero_of_empty_coordinates μ u] at hpos
  exact False.elim (lt_irrefl _ hpos)

/-- The all-pairs inequality holds directly on the singleton carrier. -/
theorem logSobolev_inequality_of_empty_coordinates {ι : Type*}
    [Fintype ι] [DecidableEq ι] [IsEmpty ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (u : SobolevPair μ) : squareEntropy μ (WithLp.ofLp u.val).1 ≤
      2 * logSobolevConstant μ * sobolevEnergy μ u := by
  rw [squareEntropy_zero_of_empty_coordinates]
  exact bot_le

/-- The zero-dimensional observation law supplies the Dirac-product premise internally. -/
theorem zeroDimensional_observation_product_statistic
    (μ : Measure (Observation 0 0)) [IsProbabilityMeasure μ]
    (r : ℕ) (H : Dataset (Observation 0 0) r → ℝ) (hH : Measurable H) :
    (fun x => H x - ∫ y, H y ∂Measure.pi fun _ : Fin r => μ)
      =ᵐ[Measure.pi fun _ : Fin r => μ] (fun _ => 0) := by
  let a : Observation 0 0 := (fun _ => 0, fun _ => 0)
  have hm := probabilityMeasure_eq_dirac_of_subsingleton μ a
  subst μ
  exact product_dirac_centered_statistic_ae_eq_zero a H hH

end LOOConcentration.Revision
