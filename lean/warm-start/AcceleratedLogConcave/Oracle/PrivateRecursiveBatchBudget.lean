import AcceleratedLogConcave.Oracle.RecursiveExecutableShiftBudget
import AcceleratedLogConcave.Conditional.SourceParameterDomain

/-! The actual recursive private batch has its covariance-domain guards paid
by the manuscript's public support-height budget. In particular the shift sum
is proved for the constructed lower mean programs, not supplied by a caller. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.PrivateRecursiveBatchBudget
open Numerics.AffineGraph TapeLowering CovarianceSetup Precision ChildAbsorption
open RecursiveExecutable RecursiveExecutableDomain

variable (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (mesh : IntervalMesh 0 (samplingEnd (M.R/backwardEnd M.R)))
  (snodes : Fin ns ≃ mesh.Source m)
  (Ds δ t w : ℝ) (layers : ℕ) (ht : 0 < t) (htq : t ≤ 1/4)
  (scale r q : ℝ)

/-- Exactly the main children constructed in the private branch of meanCore. -/
def main : Fin ns → ExecutableData := fun i =>
  mean M nodes anchors seeds Ds δ t w ht htq layers mesh snodes scale
    ((privateGeometry M mesh).radius r (snodes i))
    (RecursiveMeanPublicTable.mainWidth ns r M.R Ds (r^2)) (q-1/4)

/-- Exactly the final children constructed in that same private branch. -/
def final : Fin ns → ExecutableData := fun i =>
  mean M nodes anchors seeds Ds δ t w ht htq layers mesh snodes scale
    ((privateGeometry M mesh).radius r (snodes i))
    (SourceExecutableTables.samplingFinalWidth (privateGeometry M mesh) r) (q-1/4)

variable (K : ℝ) (hDs : 0 < Ds) (hpsi : M.psi ≤ M.R^4)
  (inventory Hs : ℕ) (hcount : n+ns ≤ inventory) (hK : (1/2:ℝ) < K)
  (hHs : 8*K+4 ≤ (Hs:ℝ))
  (hbudget : sourceShiftBase layers inventory ^ (Hs+1) ≤ Ds)

include hDs hpsi hcount hK hHs hbudget

/-- The global public source budget pays any actual lower mean's entire shift
sum, including terminal lower calls. -/
theorem lower_queryShift_and_mass (r' σ' q' : ℝ) (hr' : 0 < r') (hq' : q' ≤ K) :
    let data := mean M nodes anchors seeds Ds δ t w ht htq layers mesh snodes scale r' σ' q'
    ChildAbsorption.QueryShift data.program data.enumeration data.coefficient r' data.shiftVector ∧
      shiftSq data.shiftVector ≤ Ds^2 := by
  have h := source_mean_queryShift_and_mass M nodes anchors seeds mesh snodes Ds δ t w layers
    ht htq K scale hDs hpsi inventory Hs hcount hK hHs hbudget r' σ' q' hr' hq'
  refine ⟨h.1,h.2.trans ?_⟩
  exact (pow_le_pow_right₀ (shiftBase_ge_one layers n ns)
    (precisionRank_mono (by norm_num : (0:ℝ)<1/4) hq')).trans
      (source_shift_budget hcount hK hHs hbudget)

theorem main_queryShift_and_mass (hr : 0 < r) (hq : q ≤ K) (i : Fin ns) :
    let data := main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q i
    ChildAbsorption.QueryShift data.program data.enumeration data.coefficient
      ((privateGeometry M mesh).radius r (snodes i)) data.shiftVector ∧
      shiftSq data.shiftVector ≤ Ds^2 :=
  lower_queryShift_and_mass M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale
    K hDs hpsi inventory Hs hcount hK hHs hbudget _ _ _
    ((privateGeometry M mesh).radius_pos r hr (snodes i)) (by linarith)

theorem final_queryShift_and_mass (hr : 0 < r) (hq : q ≤ K) (i : Fin ns) :
    let data := final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q i
    ChildAbsorption.QueryShift data.program data.enumeration data.coefficient
      ((privateGeometry M mesh).radius r (snodes i)) data.shiftVector ∧
      shiftSq data.shiftVector ≤ Ds^2 :=
  lower_queryShift_and_mass M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale
    K hDs hpsi inventory Hs hcount hK hHs hbudget _ _ _
    ((privateGeometry M mesh).radius_pos r hr (snodes i)) (by linarith)

/-- The concrete five covariance guards for every actual private main child.
There is no shift-mass certificate or parent accuracy premise. -/
theorem main_admissible (hr : 0 < r) (hq : q ≤ K) (i : Fin ns) :
    Admissible (SourceExecutableTables.samplingNoise (privateGeometry M mesh) r Ds)
      ((privateGeometry M mesh).radius r (snodes i)) Ds
      (main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q i).shiftVector :=
  sampling_admissible (privateGeometry M mesh) r Ds hr hDs (snodes i) _
    (main_queryShift_and_mass M nodes anchors seeds mesh snodes Ds δ t w layers ht htq
      scale r q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq i).2

theorem final_admissible (hr : 0 < r) (hq : q ≤ K) (i : Fin ns) :
    Admissible (SourceExecutableTables.samplingNoise (privateGeometry M mesh) r Ds)
      ((privateGeometry M mesh).radius r (snodes i)) Ds
      (final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale r q i).shiftVector :=
  sampling_admissible (privateGeometry M mesh) r Ds hr hDs (snodes i) _
    (final_queryShift_and_mass M nodes anchors seeds mesh snodes Ds δ t w layers ht htq
      scale r q K hDs hpsi inventory Hs hcount hK hHs hbudget hr hq i).2

end AcceleratedLogConcave.Oracle.PrivateRecursiveBatchBudget

namespace AcceleratedLogConcave.Oracle.PrivateRecursiveBatchBudget
open Numerics.AffineGraph RecursiveExecutable RecursiveExecutableDomain

/-- Sampling children do not increase the physical radius. -/
theorem sampling_radius_le (S : SamplingGeometry m) (r : ℝ) (hr : 0 ≤ r) (i : S.Node) :
    S.radius r i ≤ r := by
  have hs : Real.sqrt (1-(S.mesh.location m i)^2) ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt
      (show 1-(S.mesh.location m i)^2 ≤ 1 by nlinarith [sq_nonneg (S.mesh.location m i)])
  simpa only [SamplingGeometry.radius, mul_one] using mul_le_mul_of_nonneg_left hs hr

/-- Applicable curvature-radius constraint at every actual sampling node. -/
theorem sampling_radius_curvature (S : SamplingGeometry m) (r ell : ℝ)
    (hr : 0 < r) (hell : 0 ≤ ell) (hcurvature : r^2*ell ≤ 1/2) (i : S.Node) :
    (S.radius r i)^2*ell ≤ 1/2 := by
  have hs : (S.radius r i)^2 ≤ r^2 :=
    (sq_le_sq₀ (S.radius_pos r hr i).le hr.le).2 (sampling_radius_le S r hr.le i)
  exact (mul_le_mul_of_nonneg_right hs hell).trans hcurvature

variable {d m n : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
    (r Ds ell : ℝ) (hm : 0 < m) (hr : 0 < r) (hDs : 0 < Ds)
    (hell : 0 ≤ ell) (hcurvature : r^2*ell ≤ 1/2)

/-- Actual lower main reference parameters. In particular these positive
width/radius proofs remain available when the lower call is terminal. -/
def mainParameters (i : Fin n) (x : Point d) : Conditional.SourceParameters (Point d) ell :=
  ⟨(x,S.radius r (e i),RecursiveMeanPublicTable.mainWidth n r S.R Ds (r^2)),
    S.radius_pos r hr (e i), sampling_main_width_pos S e r Ds hm hr hDs,
    sampling_radius_curvature S r ell hr hell hcurvature (e i)⟩

/-- Actual lower final reference parameters at the same child radius and
literal private final width. -/
def finalParameters (i : Fin n) (x : Point d) : Conditional.SourceParameters (Point d) ell :=
  ⟨(x,S.radius r (e i),SourceExecutableTables.samplingFinalWidth S r),
    S.radius_pos r hr (e i), sampling_final_width_pos S r hr,
    sampling_radius_curvature S r ell hr hell hcurvature (e i)⟩

@[simp] theorem mainParameters_center (i : Fin n) (x : Point d) :
    (mainParameters S e r Ds ell hm hr hDs hell hcurvature i x).center = x := rfl

@[simp] theorem mainParameters_radius (i : Fin n) (x : Point d) :
    (mainParameters S e r Ds ell hm hr hDs hell hcurvature i x).radius = S.radius r (e i) := rfl

@[simp] theorem mainParameters_width (i : Fin n) (x : Point d) :
    (mainParameters S e r Ds ell hm hr hDs hell hcurvature i x).width =
      RecursiveMeanPublicTable.mainWidth n r S.R Ds (r^2) := rfl

@[simp] theorem finalParameters_center (i : Fin n) (x : Point d) :
    (finalParameters S e r ell hr hell hcurvature i x).center = x := rfl

@[simp] theorem finalParameters_radius (i : Fin n) (x : Point d) :
    (finalParameters S e r ell hr hell hcurvature i x).radius = S.radius r (e i) := rfl

@[simp] theorem finalParameters_width (i : Fin n) (x : Point d) :
    (finalParameters S e r ell hr hell hcurvature i x).width =
      SourceExecutableTables.samplingFinalWidth S r := rfl

theorem continuous_mainParameters (i : Fin n) :
    Continuous (fun x : Point d => mainParameters S e r Ds ell hm hr hDs hell hcurvature i x) := by
  apply Continuous.subtype_mk
  exact continuous_id.prodMk (continuous_const.prodMk continuous_const)

theorem continuous_finalParameters (i : Fin n) :
    Continuous (fun x : Point d => finalParameters S e r ell hr hell hcurvature i x) := by
  apply Continuous.subtype_mk
  exact continuous_id.prodMk (continuous_const.prodMk continuous_const)

end AcceleratedLogConcave.Oracle.PrivateRecursiveBatchBudget
