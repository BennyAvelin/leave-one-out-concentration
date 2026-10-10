module

public import Mathlib

@[expose] public section

set_option autoImplicit false

namespace LOOConcentration.Revision

/-- Keep the jointly measurable loss on a measurable set of data sections, and set every
exceptional section to zero. -/
noncomputable def sectionCutoff {E α : Type*} (Z : Set α) (F : E × α → ℝ) : E × α → ℝ := by
  classical
  exact fun p => if p.2 ∈ Z then F p else 0

/-- The cutoff remains jointly measurable when the section set is measurable. -/
theorem sectionCutoff_measurable {E α : Type*} [MeasurableSpace E] [MeasurableSpace α]
    {Z : Set α} {F : E × α → ℝ}
    (hZ : MeasurableSet Z) (hF : Measurable F) : Measurable (sectionCutoff Z F) := by
  classical
  unfold sectionCutoff
  apply Measurable.ite
  · exact hZ.preimage measurable_snd
  · exact hF
  · exact measurable_const

/-- Every section of the cutoff is locally Lipschitz if its retained sections are. -/
theorem sectionCutoff_locallyLipschitz {E α : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Z : Set α} {F : E × α → ℝ}
    (hZ : ∀ z ∈ Z, LocallyLipschitz (fun x : E => F (x, z))) :
    ∀ z, LocallyLipschitz (fun x : E => sectionCutoff Z F (x, z)) := by
  classical
  intro z
  by_cases hz : z ∈ Z
  · simpa [sectionCutoff, hz] using hZ z hz
  · simpa [sectionCutoff, hz] using
      (LocallyLipschitz.const (0 : ℝ) : LocallyLipschitz (fun _ : E => (0 : ℝ)))

/-- Every cutoff section is continuous whenever every retained section is locally Lipschitz. -/
theorem sectionCutoff_continuous {E α : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Z : Set α} {F : E × α → ℝ}
    (hZ : ∀ z ∈ Z, LocallyLipschitz (fun x : E => F (x, z))) :
    ∀ z, Continuous (fun x : E => sectionCutoff Z F (x, z)) := by
  intro z
  exact (sectionCutoff_locallyLipschitz hZ z).continuous

/-- On every retained section, the cutoff agrees as a function with the original section. -/
theorem sectionCutoff_eq_on_good {E α : Type*} {Z : Set α} {F : E × α → ℝ} {z : α}
    (hz : z ∈ Z) :
    (fun x : E => sectionCutoff Z F (x, z)) = fun x => F (x, z) := by
  classical
  funext x
  simp [sectionCutoff, hz]

/-- The derivative-existence predicate is preserved on a retained section by function equality. -/
theorem sectionCutoff_differentiableAt_iff {E α : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    {Z : Set α} {F : E × α → ℝ} {z : α} (hz : z ∈ Z) (x : E) :
    DifferentiableAt ℝ (fun y : E => sectionCutoff Z F (y, z)) x ↔
      DifferentiableAt ℝ (fun y : E => F (y, z)) x := by
  rw [sectionCutoff_eq_on_good hz]

open scoped Gradient

/-- The native Euclidean gradient is unchanged on every retained section. -/
theorem sectionCutoff_gradient_eq {ι : Type*} [Fintype ι]
    {α : Type*} {Z : Set α} {F : EuclideanSpace ℝ ι × α → ℝ} {z : α}
    (hz : z ∈ Z) (x : EuclideanSpace ℝ ι) :
    gradient (fun y : EuclideanSpace ℝ ι => sectionCutoff Z F (y, z)) x =
      gradient (fun y : EuclideanSpace ℝ ι => F (y, z)) x := by
  rw [sectionCutoff_eq_on_good hz]

/-- From joint measurability and an almost-everywhere locally Lipschitz section hypothesis,
choose a measurable full-measure section set whose complement contains the entire exceptional
locus. The cutoff has locally Lipschitz continuous sections everywhere and agrees with the
original loss on the chosen set. -/
theorem exists_measurable_full_sectionCutoff {E α : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} (F : E × α → ℝ) (hF : Measurable F)
    (hLocallyLipschitz : ∀ᵐ z ∂μ,
      LocallyLipschitz (fun x : E => F (x, z))) :
    ∃ Z : Set α, MeasurableSet Z ∧
      (∀ᵐ z ∂μ, z ∈ Z) ∧
      (∀ z ∈ Z, LocallyLipschitz (fun x : E => F (x, z))) ∧
      Measurable (sectionCutoff Z F) ∧
      (∀ z, LocallyLipschitz (fun x : E => sectionCutoff Z F (x, z))) ∧
      (∀ z, Continuous (fun x : E => sectionCutoff Z F (x, z))) ∧
      (∀ z, z ∈ Z →
        (fun x : E => sectionCutoff Z F (x, z)) = fun x => F (x, z)) := by
  classical
  let bad : Set α := {z | ¬ LocallyLipschitz (fun x : E => F (x, z))}
  have hbad : μ bad = 0 := by
    simpa [bad] using (MeasureTheory.ae_iff.mp hLocallyLipschitz)
  obtain ⟨N, hbadN, hNmeas, hNzero⟩ :=
    MeasureTheory.exists_measurable_superset_of_null hbad
  let Z : Set α := Nᶜ
  have hZmeas : MeasurableSet Z := by
    dsimp [Z]
    exact hNmeas.compl
  have hZfull : ∀ᵐ z ∂μ, z ∈ Z := by
    rw [MeasureTheory.ae_iff]
    simpa [Z] using hNzero
  have hZvalid : ∀ z ∈ Z, LocallyLipschitz (fun x : E => F (x, z)) := by
    intro z hz
    by_contra hnot
    apply hz
    exact hbadN (by simpa [bad] using hnot)
  have hCutoffMeasurable : Measurable (sectionCutoff Z F) :=
    sectionCutoff_measurable hZmeas hF
  have hCutoffLocallyLipschitz :
      ∀ z, LocallyLipschitz (fun x : E => sectionCutoff Z F (x, z)) :=
    sectionCutoff_locallyLipschitz hZvalid
  have hCutoffContinuous :
      ∀ z, Continuous (fun x : E => sectionCutoff Z F (x, z)) :=
    sectionCutoff_continuous hZvalid
  have hSectionEq : ∀ z, z ∈ Z →
      (fun x : E => sectionCutoff Z F (x, z)) = fun x => F (x, z) := by
    intro z hz
    exact sectionCutoff_eq_on_good hz
  exact ⟨Z, hZmeas, hZfull, hZvalid, hCutoffMeasurable,
    hCutoffLocallyLipschitz, hCutoffContinuous, hSectionEq⟩

end LOOConcentration.Revision
