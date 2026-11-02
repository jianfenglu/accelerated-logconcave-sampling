import AcceleratedLogConcave.Numerics.CenteringFlowLp
import AcceleratedLogConcave.Conditional.Centering.CenterMeanSecondJet

/-! Exact first and second mean jets of the original centering source.
No regularity or moment certificate is a field of the input Data. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "P" => Centering.Phase E

def K (d : Data ι) := transportedSteinKernelTranspose
  d.hF d.hell d.hlo d.hup d.x d.hr d.hb d.hb1
def M (d : Data ι) := conditionalMean d.F d.x d.r d.b

omit [DecidableEq ι] in
theorem smooth_M (d : Data ι) : ContDiff ℝ ∞ (M d) := by
  have hh := (contDiffOn_conditionalMean d.hF d.hlo d.hup d.x d.r).comp
    (contDiff_const.prodMk contDiff_id).contDiffOn (s := Set.univ)
    (fun _ _ => And.intro (by linarith [d.hb] : -1 < d.b) d.hb1)
  exact contDiffOn_univ.mp hh

def first (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) (z : P) : E :=
  Centering.meanFirstJet (K d) (M d) s (position d s hs t z) (momentum d s hs t z)
def second (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) (z : P) : E :=
  Centering.meanSecondJet (K d) (M d) (meanOffset d) s
    (position d s hs t z) (momentum d s hs t z)

theorem hasDerivAt_centeredMean (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) (z : P) :
    HasDerivAt (fun a => centeredMean d s hs a z) (first d s hs t z) t := by
  have hM := (smooth_M d).differentiable (by simp) (position d s hs t z)
  have h := (hM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_position d s hs t z)).sub_const
    (meanOffset d)
  convert h using 1
  · rfl
  · simp only [first, Centering.meanFirstJet, map_smul]
    rfl

theorem hasDerivAt_first (d : Data ι) (s : ℝ) (hs : 0 < s) (t : ℝ) (z : P) :
    HasDerivAt (fun a => first d s hs a z) (second d s hs t z) t := by
  have hK := (Centering.sourceKernel_contDiff_one d.hF d.hell d.hlo d.hup
    d.x d.hr d.hb d.hb1 d.hsmall).differentiable (by norm_num) (position d s hs t z)
  have hM := ((smooth_M d).fderiv_right (m := 1) (by simp)).differentiable
    (by norm_num) (position d s hs t z)
  exact Centering.hasDerivAt_meanFirstJet_along hK hM
    (hasDerivAt_position d s hs t z) (hasDerivAt_momentum d s hs t z)

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
