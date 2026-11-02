import AcceleratedLogConcave.Root.ClockCoefficientMeasurability
import AcceleratedLogConcave.Oracle.RecursiveExecutableParameterMeasurability

/-! Measurability of the two literal public table blocks appended by the
retained root: the Gaussian assembly and the final retained correction.
The recursive child blocks are handled separately. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.ClockRetainedPublicTablesMeasurability
open Oracle Oracle.AffineLowering Oracle.RecursiveExecutableParameterMeasurability
open ClockCoefficientMeasurability ClockRetainedFinalSplice
open scoped MatrixOrder Matrix.Norms.L2Operator

variable (P : SourceSchedule)

theorem measurable_coefficient :
    Measurable (ClockRetainedFinalSplice.coefficient P) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_weight P i).neg

theorem measurable_assembly_table :
    Measurable (fun clock : ClockLaw.Clock =>
      MeanGaussianSetup.table (coefficient P clock)) :=
  measurable_meanAssemblyTable _ (measurable_coefficient P)

theorem measurable_correction_table :
    Measurable (fun clock : ClockLaw.Clock =>
      RetainedMeanCorrection.table 1 (correctionWeight P clock) (width P clock)) := by
  apply measurable_retainedCorrectionTable
  · exact measurable_const
  · exact measurable_pi_iff.mpr (fun i => measurable_correctionWeight P i)
  · exact measurable_pi_iff.mpr (fun i => measurable_width P i)

end AcceleratedLogConcave.Root.ClockRetainedPublicTablesMeasurability
