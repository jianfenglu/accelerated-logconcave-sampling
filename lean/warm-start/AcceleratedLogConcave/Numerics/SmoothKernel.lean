import AcceleratedLogConcave.Conditional.Flow.ExtendedLp
import AcceleratedLogConcave.Conditional.Flow.ExtendedAgreement
import AcceleratedLogConcave.Numerics.KernelFlowLp

/-! Actual smooth L² extension of the transported kernel on a larger
positive-variance slab, agreeing with the original canonical source lift. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.KernelFlowLp
open Conditional Analysis.PositiveVarianceSlab
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def smoothData (d : Data ι) : PositiveVarianceFlowData E :=
  ⟨d.F, d.hF, d.ell, d.hell, d.hlo, d.hup, d.x, d.r, d.hr, d.b, d.hb, d.hb1⟩

def smoothExtensionLp (d : Data ι) : ℝ → Lp E 2 (seedMeasure d) :=
  (smoothData d).kernelLp

theorem contDiffOn_smoothExtensionLp (d : Data ι) (n : ℕ) :
    ContDiffOn ℝ n (smoothExtensionLp d) (Ioo (left d.b) (right d.b)) :=
  (smoothData d).contDiffOn_kernelLp n

/-- Equality is on the closed source slab, including both endpoints. -/
theorem smoothExtensionLp_eq (d : Data ι) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    smoothExtensionLp d t = extensionLp d t := by
  rw [smoothExtensionLp, PositiveVarianceFlowData.kernelLp, ← extension_toLp]
  change ((smoothData d).momentumJet_memLp 0 t).toLp ((smoothData d).momentumJet 0 t) -
    ((smoothData d).momentumJet_memLp 0 d.b).toLp ((smoothData d).momentumJet 0 d.b) = _
  rw [← MemLp.toLp_sub]
  apply MemLp.toLp_congr
  filter_upwards [] with z
  have htime : ((smoothData d).jet 0 t z.fst).snd =
      transportedJacobian d.hF d.hell d.hlo d.hup d.x d.hr d.hb d.hb1 t z.fst :=
    (smoothData d).jet_zero_snd_eq_source ht z.fst
  have href : ((smoothData d).jet 0 d.b z.fst).snd = ContinuousLinearMap.id ℝ E :=
    (smoothData d).jet_zero_snd_reference z.fst
  change ((smoothData d).jet 0 t z.fst).snd z.snd -
    ((smoothData d).jet 0 d.b z.fst).snd z.snd = extension d t z
  rw [htime, href, ContinuousLinearMap.id_apply, extension_eq_jacobian d ht]
  simp only [sub_apply, ContinuousLinearMap.id_apply]

end AcceleratedLogConcave.Numerics.KernelFlowLp
