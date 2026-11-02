import AcceleratedLogConcave.Root.OuterRootExactTapePath
import AcceleratedLogConcave.Root.OuterRootStrongJetLp
import AcceleratedLogConcave.Numerics.SmoothConditionalReplacement

/-! Source-only exact primitive-score/Jet1 identity. No freely chosen score,
initial-law substitution, or division by the stopping clock. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace AcceleratedLogConcave.Root.OuterRootLiteralScore
open Numerics Numerics.ConditionalSmoothing Analysis.PositiveVarianceSlab
variable {ι : Type*} [Fintype ι]

theorem jet_one_eq_primitiveMean (d : SamplingCenterLp.Data ι)
    (x z : EuclideanSpace ℝ ι) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    (jet d 1 t (x,z)).2 = (-d.r) • Gibbs.primitiveMean d.F
      (x+(d.r*t) • SamplingCenterLp.path d x t z) (d.r*Real.sqrt (1-t^2)) := by
  have hs := source_subset d.hb d.hb1 ht
  have htime := time_eq d ⟨hs.1.le,hs.2.le⟩
  rw [jet_one]
  simp only [openVelocity,htime,jointPath_fst,jointPath_snd_eq_source d x z ht]
  congr 1
  exact AffineFlowIdentities.conditionalMean_eq_primitiveMean d.hF d.hell d.hlo d.hup
    x d.hr (construction_subset d.hb d.hb1 ⟨hs.1.le,hs.2.le⟩).1
      (construction_subset d.hb d.hb1 ⟨hs.1.le,hs.2.le⟩).2 _

variable {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V) {h : ℝ} (hh : 0 < h)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖^2)

theorem path_eq_rawY (x z : EuclideanSpace ℝ ι) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) (1/2)) :
    SamplingCenterLp.path (OuterRootOriginalData.data hV hh hlo hup) x t z =
      OuterRootPhysicalPath.rawY hV hh hlo hup x z t := by
  simp only [SamplingCenterLp.path,SamplingFlowLp.sourcePath, OuterRootPhysicalPath.rawY]
  erw [SamplingFlowLp.sourceTime_eq (show 0 ≤ (1/2:ℝ) by norm_num) ht]

/-- Actual primitive target, at the actual normalized parent path and radius. -/
def score (x z : EuclideanSpace ℝ ι) (t : ℝ) : EuclideanSpace ℝ ι :=
  Gibbs.primitiveMean (OuterRootOriginalData.potential V h)
    (x+(Real.sqrt (2*h)*t) • OuterRootPhysicalPath.rawY hV hh hlo hup x z t)
    (Real.sqrt (2*h)*Real.sqrt (1-t^2))

theorem jet_one_eq_score (x z : EuclideanSpace ℝ ι) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) (1/2)) :
    (jet (OuterRootOriginalData.data hV hh hlo hup) 1 t (x,z)).2 =
      (-Real.sqrt (2*h)) • score hV hh hlo hup x z t := by
  have H := jet_one_eq_primitiveMean (OuterRootOriginalData.data hV hh hlo hup) x z ht
  rw [path_eq_rawY hV hh hlo hup x z ht] at H
  exact H

end AcceleratedLogConcave.Root.OuterRootLiteralScore
