import AcceleratedLogConcave.Oracle.MeanInitialComparison
import AcceleratedLogConcave.Oracle.MeanJointReference

/-! The static coarse mean benchmark uses the retained private REFERENCE
position, the actual original-input Gaussian assembly, and the actual incoming
flow draws. No main-child designated draw is used as a returned reference. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.MeanChronologicalHost
open Numerics.AffineGraph AffineLowering TapeLowering SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
variable {m n a h d : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData) (N : ℕ)
local instance : MeasurableSpace
    (Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N)) := prefixSpace d _

def raw (p : Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))
    (i : Fin (m+1)) : Point d := (p.2.2.2.2.1 i).1

theorem raw_measurable : Measurable (raw (d := d) M nodes anchors seeds main final sampling N) := by
  apply Measurable.of_eval
  intro i
  exact ((measurable_pi_apply i).comp measurable_snd.snd.snd.snd.fst).fst

def flowSeeds (p : Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))
    (j : Fin m) (k : M.Kernel) : Point d := (p.2.2.2.2.2.2.1 (seeds.symm (j,k))).1

theorem flowSeeds_measurable : Measurable (flowSeeds (d := d) M nodes anchors seeds main final sampling N) := by
  apply Measurable.of_eval
  intro j
  apply Measurable.of_eval
  intro k
  exact ((measurable_pi_apply (seeds.symm (j,k))).comp
    measurable_snd.snd.snd.snd.snd.snd.fst).fst

variable {A : Type*} [MeasurableSpace A]
  (x P referencePosition : A → Point d) (hx : Measurable x) (hP : Measurable P)
  (hreference : Measurable referencePosition)

def phaseInput (z : MeanInitialComparison.Coarse (d := d) M nodes anchors seeds main final sampling N A) :
    Point d × MeanJointReference.Host (d := d) M :=
  (x z.1,((referencePosition z.1,
    Conditional.GaussianAssembly.active (assembly M) (P z.1)
      (raw M nodes anchors seeds main final sampling N z.2) 0),
    flowSeeds M nodes anchors seeds main final sampling N z.2))

include hx hP hreference in
theorem phaseInput_measurable :
    Measurable (phaseInput M nodes anchors seeds main final sampling N x P referencePosition) := by
  have hr := (raw_measurable (d := d) M nodes anchors seeds main final sampling N).comp
    (measurable_snd : Measurable (Prod.snd : MeanInitialComparison.Coarse (d := d) M nodes anchors seeds main final sampling N A → _))
  have hs : Measurable (fun z : MeanInitialComparison.Coarse (d := d) M nodes anchors seeds main final sampling N A =>
      Conditional.GaussianAssembly.active (assembly M) (P z.1)
        (raw M nodes anchors seeds main final sampling N z.2) 0) := by
    unfold Conditional.GaussianAssembly.active Conditional.GaussianAssembly.noiseSum
    fun_prop
  exact (hx.comp measurable_fst).prodMk
    (((hreference.comp measurable_fst).prodMk hs).prodMk
      ((flowSeeds_measurable (d := d) M nodes anchors seeds main final sampling N).comp measurable_snd))

variable {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (r σ : ℝ) (hr : 0<r) (hσ : 0<σ) (hsmall : r^2*ell≤1/2)

def center (i : Fin n) (z : MeanInitialComparison.Coarse (d := d) M nodes anchors seeds main final sampling N A) : Point d :=
  MeanJointReference.reference M hF hell hlo hup r σ hr hσ hsmall (nodes i)
    (phaseInput M nodes anchors seeds main final sampling N x P referencePosition z)

include hx hP hreference in
theorem center_measurable (i : Fin n) :
    Measurable (center M nodes anchors seeds main final sampling N x P referencePosition
      hF hell hlo hup r σ hr hσ hsmall i) :=
  (MeanJointReference.continuous_reference M hF hell hlo hup r σ hr hσ hsmall (nodes i)).measurable.comp
    (phaseInput_measurable M nodes anchors seeds main final sampling N x P referencePosition hx hP hreference)
end AcceleratedLogConcave.Oracle.MeanChronologicalHost
