import AcceleratedLogConcave.Root.Innovation
import AcceleratedLogConcave.Root.RecursiveRadiusFamily
import AcceleratedLogConcave.Root.PhysicalPosteriorScaling
import AcceleratedLogConcave.Conditional.RecursiveReferencePosteriorBound

/-! Directional innovation of the normalized root with the actual constructed
recursive references. Every child moment is identified with its standalone
retained pair before its posterior budget is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set MeasureTheory ProbabilityTheory Filter
open scoped ContDiff ENNReal RealInnerProductSpace
namespace AcceleratedLogConcave.Root.RecursiveInnovation
open Conditional Conditional.MeanReferenceLayer Conditional.RecursiveReference
open Numerics Numerics.AffineGraph
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The actual root child increment retains its old input through the split. -/
theorem child_second_moment_transfer {N : ℕ} (d : RetainedLaw.Data ι N) (v : E) (i : Fin N) :
    (∫ z, ⟪v,RetainedLaw.childIncrement d i z⟫^2 ∂RetainedLaw.averagedJoint d) =
      ∫ p : E, ∫ p' : E, ⟪v,p'-p⟫^2 ∂d.child i p ∂stdGaussian E := by
  let : IsMarkovKernel (d.child i) := d.markov i
  let π := RetainedLaw.noiseLaw (ι := ι) (m := N)
  let ν := (stdGaussian E).prod π
  let f : (E × (Fin N → E)) × (Fin N → E) → ℝ := fun z ↦ ⟪v,z.2 i-z.1.2 i⟫^2
  have hf : StronglyMeasurable f := by dsimp [f]; fun_prop
  have hp := RetainedLaw.splitExecution_preserving d
  have hint : Integrable f (ν ⊗ₘ RetainedLaw.stateChildren d) := by
    apply (hp.integrable_comp hf.aestronglyMeasurable).mp
    have hi := (RetainedLaw.increment_memLp d i).const_inner (𝕜 := ℝ) v
    simpa only [f,RetainedLaw.split,RetainedLaw.childIncrement,Function.comp_def]
      using hi.integrable_sq
  have hinter : Integrable (fun z : E × (Fin N → E) ↦
      ∫ q, f (z,q) ∂RetainedLaw.stateChildren d z) ν := by
    simpa only [Kernel.const_apply,Kernel.prodMkLeft_apply] using hint.integral_compProd
  change (∫ z, f (RetainedLaw.split d z.1,z.2) ∂RetainedLaw.averagedJoint d) = _
  rw [← integral_map_of_stronglyMeasurable hp.measurable hf,hp.map_eq,
    Measure.integral_compProd hint,integral_prod _ hinter]
  have he (g : E) (p : Fin N → E) :
      (∫ q, f ((g,p),q) ∂RetainedLaw.stateChildren d (g,p)) =
        ∫ p', ⟪v,p'-p i⟫^2 ∂d.child i (p i) := by
    dsimp only [f]
    rw [RetainedLaw.stateChildren_apply]
    let : ∀ j, IsProbabilityMeasure (d.child j (p j)) :=
      fun j ↦ by let := d.markov j; infer_instance
    have hh := measurePreserving_eval (fun j ↦ d.child j (p j)) i
    simpa only [hh.map_eq] using
      (integral_map_of_stronglyMeasurable (μ := Measure.pi (fun j ↦ d.child j (p j))) hh.measurable
        (show StronglyMeasurable (fun x : E ↦ ⟪v,x-p i⟫^2) by fun_prop)).symm
  simp_rw [he]
  have hsm : StronglyMeasurable (fun p : E ↦ ∫ p', ⟪v,p'-p⟫^2 ∂d.child i p) :=
    (show StronglyMeasurable (fun z : E × E ↦ ⟪v,z.2-z.1⟫^2) by
      fun_prop).integral_kernel_prod_right'
  have hh := measurePreserving_eval (fun _ : Fin N ↦ stdGaussian E) i
  have heval := (integral_map_of_stronglyMeasurable (μ := π) hh.measurable hsm).symm
  rw [show π.map (fun p ↦ p i) = stdGaussian E from hh.map_eq] at heval
  change (∫ _ : E, ∫ p : Fin N → E, _ ∂π ∂stdGaussian E) = _
  simp only [heval,integral_const,probReal_univ,one_smul]

section Source
variable [DecidableEq ι] {m : ℕ}
variable {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2)
    {F : EuclideanSpace ℝ ι → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ h * ‖a‖^2)
    (G : MeanGeometry m) (hm : 0 < m) (t : ℝ) (ht : 0 < t) (K : ℕ)
    (P : Analysis.Poisson.ReferencePoissonFamily (EuclideanSpace ℝ ι) 0 (1/2))
local notation "N" => ClockSchedule.sourceCells h * ClockSchedule.sourceOrder K

/-- Actual fixed-parent root data from the clock supplier and the constructed
recursive radius family, with the prescribed source widths and precision K. -/
def sourceData (clock : ClockLaw.Clock) (parent : E × E) : RetainedLaw.Data ι N :=
  ConditionalLaw.atParent
    (ClockBackwardKernel.data P (Real.sqrt (2*h^2)) _ _
      (ClockSchedule.sourceCells_pos hh) (ClockSchedule.sourceOrder_pos K) (Real.sqrt h)⁻¹
      (ClockBackwardKernel.sourceClockChildren h hh K
        (RecursiveRadiusFamily.radiusChildren hh hhalf hF hlo hup G hm t ht K)))
    (clock,parent)

/-- Each child uses its actual source radius, backward physical center, fixed
final width and precision K. -/
def sourceChildParameters (clock : ClockLaw.Clock) (parent : E × E) (i : Fin N) :
    SourceParameters E h :=
  RecursiveRadiusFamily.parameters hh hhalf (ClockBackwardKernel.radiusParameter h hh K i clock)
    ((Real.sqrt h)⁻¹ • ClockBackwardKernel.center P (Real.sqrt (2*h^2)) _ _
      (ClockSchedule.sourceCells_pos hh) i (clock,parent))

theorem sourceData_child_apply (clock : ClockLaw.Clock) (parent : E × E) (i : Fin N) (p : E) :
    (sourceData hh hhalf hF hlo hup G hm t ht K P clock parent).child i p =
      (referenceFamily hF hh.le hlo hup G hm t ht (K : ℝ)).kernel
        (sourceChildParameters hh hhalf K P clock parent i,p) := rfl

/-- Exact root innovation recurrence with every child moment already
identified with the actual recursive retained reference. -/
theorem source_innovation_second_moment (clock : ClockLaw.Clock) (parent : E × E) (v : E) :
    let d := sourceData hh hhalf hF hlo hup G hm t ht K P clock parent
    (∫ z, ⟪v,RetainedLaw.output d z-z.1.1⟫^2 ∂RetainedLaw.averagedJoint d) =
      ∑ i, (ClockSchedule.weight (ClockSchedule.sourceCells h) (ClockSchedule.sourceOrder K) clock i)^2 *
        directionalMoment (referenceFamily hF hh.le hlo hup G hm t ht (K : ℝ))
          (sourceChildParameters hh hhalf K P clock parent i) v := by
  dsimp only
  rw [RetainedLaw.innovation_second_moment]
  apply Finset.sum_congr rfl
  intro i _
  rw [child_second_moment_transfer]
  rfl

/-- The root's actual recursive child posterior budget, conditional on every
fixed exact parent path. There is no child-variance assumption in this theorem. -/
theorem source_innovation_posterior_bound (clock : ClockLaw.Clock) (parent : E × E) (v : E) :
    let d := sourceData hh hhalf hF hlo hup G hm t ht K P clock parent
    (ClockBackwardKernel.sourceWidth h)^2 *
      (∫ z, ⟪v,RetainedLaw.output d z-z.1.1⟫^2 ∂RetainedLaw.averagedJoint d) ≤
      ∑ i, (ClockSchedule.weight (ClockSchedule.sourceCells h) (ClockSchedule.sourceOrder K) clock i)^2 *
        posteriorBudget (F := F) (sourceChildParameters hh hhalf K P clock parent i) v := by
  dsimp only
  rw [source_innovation_second_moment hh hhalf hF hlo hup G hm t ht K P]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact referenceFamily_posterior_bound hF hh.le hlo hup G hm t ht (K : ℝ)
    (sourceChildParameters hh hhalf K P clock parent i) v


/-- The fixed-parent law in the innovation theorem is the exact section of
the actual jointly measurable source root kernel. -/
theorem sourceData_kernel_section (clock : ClockLaw.Clock) (parent : E × E) :
    (ClockBackwardKernel.sourceKernelFromRadiusFamily P h hh K
      (RecursiveRadiusFamily.radiusChildren hh hhalf hF hlo hup G hm t ht K)).comap
        (fun p ↦ (clock,(parent,p))) (by fun_prop) =
      RetainedLaw.rootKernel (sourceData hh hhalf hF hlo hup G hm t ht K P clock parent) := by
  ext p : 1
  exact congrArg (fun k : Kernel E E ↦ k p)
    (ConditionalLaw.rootKernel_section _ (clock,parent))

end Source

/-- Literal physical source radius squared, including a stopping clock of zero. -/
theorem sourceRadius_sq {h : ℝ} (hh : 0 < h) (K : ℕ)
    (i : Fin (ClockSchedule.sourceCells h * ClockSchedule.sourceOrder K)) (clock : ClockLaw.Clock) :
    (ClockBackwardKernel.sourceRadius h hh K i clock)^2 =
      2*h*(1-(ClockSchedule.node (ClockSchedule.sourceCells h) (ClockSchedule.sourceOrder K)
        (ClockSchedule.sourceCells_pos hh) clock i : ℝ)^2) := by
  let u := ClockSchedule.node (ClockSchedule.sourceCells h) (ClockSchedule.sourceOrder K)
    (ClockSchedule.sourceCells_pos hh) clock i
  have hu : 0 ≤ 1-(u : ℝ)^2 := by nlinarith [u.2.1,u.2.2]
  change (Real.sqrt (2*h) * Real.sqrt (1-(u : ℝ)^2))^2 = _
  rw [mul_pow,Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2*h),Real.sq_sqrt hu]

/-- The final width has the source normalization n²/s²r_F². -/
theorem sourceWidth_sq_mul {h : ℝ} (hh : 0 < h) :
    (ClockBackwardKernel.sourceWidth h)^2 * (h/2) = 3/4 := by
  rw [RecursiveRadiusFamily.sourceWidth_eq,div_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2*h)]
  field_simp
  ring

section Physical
variable [DecidableEq ι] {m : ℕ}
variable {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2)
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)
    (G : MeanGeometry m) (hm : 0 < m) (t : ℝ) (ht : 0 < t) (K : ℕ)
    (P : Analysis.Poisson.ReferencePoissonFamily (EuclideanSpace ℝ ι) 0 (1/2))
local notation "N" => ClockSchedule.sourceCells h * ClockSchedule.sourceOrder K

/-- The source root uses the actual scaled original potential. -/
def physicalSourceData (clock : ClockLaw.Clock) (parent : E × E) : RetainedLaw.Data ι N :=
  sourceData hh hhalf (RecursiveRadiusFamily.physicalPotential_C2 hV h)
    (RecursiveRadiusFamily.physicalPotential_hessian_nonneg hV hlo hh.le)
    (RecursiveRadiusFamily.physicalPotential_hessian_upper hV hup hh.le) G hm t ht K P clock parent

/-- Actual inverse-flow physical center, on the same exact parent path. -/
def physicalCenter (clock : ClockLaw.Clock) (parent : E × E) (i : Fin N) : E :=
  ClockBackwardKernel.center P (Real.sqrt (2*h^2)) _ _ (ClockSchedule.sourceCells_pos hh)
    i (clock,parent)

omit [DecidableEq ι] in
theorem sourceChildParameters_center_scale (clock : ClockLaw.Clock) (parent : E × E) (i : Fin N) :
    Real.sqrt h • (sourceChildParameters hh hhalf K P clock parent i).center =
      physicalCenter hh K P clock parent i := by
  change Real.sqrt h • ((Real.sqrt h)⁻¹ • _) = _
  rw [smul_smul,mul_inv_cancel₀ (Real.sqrt_pos.mpr hh).ne',one_smul]
  rfl

include hV hlo hup in
omit [DecidableEq ι] in
/-- Actual child posterior curvature at the original potential's physical
center and actual heat time, conditional on the exact parent. -/
theorem physical_child_budget_le (clock : ClockLaw.Clock) (parent : E × E) (v : E) (i : Fin N) :
    posteriorBudget (F := RecursiveRadiusFamily.physicalPotential V h)
      (sourceChildParameters hh hhalf K P clock parent i) v ≤
      2*h^2*(ClockBackwardKernel.sourceRadius h hh K i clock)^2 *
        fderiv ℝ (fderiv ℝ (Gibbs.heatPotential V
          (h*(ClockBackwardKernel.sourceRadius h hh K i clock)^2)))
          (physicalCenter hh K P clock parent i) v v := by
  let theta := sourceChildParameters hh hhalf K P clock parent i
  change posteriorBudget (F := RecursiveRadiusFamily.physicalPotential V h) theta v ≤ _
  rw [posteriorBudget,RecursiveReferenceCovariance.primitive_budget_eq_variance
    (RecursiveRadiusFamily.physicalPotential_C2 hV h) hh.le
    (RecursiveRadiusFamily.physicalPotential_hessian_nonneg hV hlo hh.le)
    (RecursiveRadiusFamily.physicalPotential_hessian_upper hV hup hh.le)
    theta.center theta.radius_pos v]
  have hb := PhysicalPosteriorScaling.score_variance_le_curvature hV hlo hup hh theta.radius_pos
    (show h*theta.radius^2 ≤ 1/2 by nlinarith [theta.small]) theta.center v
  dsimp only [theta] at hb
  rw [sourceChildParameters_center_scale hh hhalf K P clock parent i] at hb
  exact hb

/-- Curvature-weighted innovation of the actual normalized root. Here n²=3/4,
s²=1/4 and a=2h², so the coefficient 2h⁴ is exactly 2s²a². The clock may be zero;
all centers are the actual inverse-flow centers of the fixed parent path. -/
theorem physical_source_innovation_bound (clock : ClockLaw.Clock) (parent : E × E) (v : E) :
    let d := physicalSourceData hh hhalf hV hlo hup G hm t ht K P clock parent
    (3/4 : ℝ) * (∫ z, ⟪v,RetainedLaw.output d z-z.1.1⟫^2 ∂RetainedLaw.averagedJoint d) ≤
      2*h^4 * ∑ i, (ClockSchedule.weight (ClockSchedule.sourceCells h) (ClockSchedule.sourceOrder K) clock i)^2 *
        (1-(ClockSchedule.node (ClockSchedule.sourceCells h) (ClockSchedule.sourceOrder K)
          (ClockSchedule.sourceCells_pos hh) clock i : ℝ)^2) *
        fderiv ℝ (fderiv ℝ (Gibbs.heatPotential V
          (2*h^2*(1-(ClockSchedule.node (ClockSchedule.sourceCells h) (ClockSchedule.sourceOrder K)
            (ClockSchedule.sourceCells_pos hh) clock i : ℝ)^2))))
          (physicalCenter hh K P clock parent i) v v := by
  have hp := source_innovation_posterior_bound hh hhalf
    (RecursiveRadiusFamily.physicalPotential_C2 hV h)
    (RecursiveRadiusFamily.physicalPotential_hessian_nonneg hV hlo hh.le)
    (RecursiveRadiusFamily.physicalPotential_hessian_upper hV hup hh.le)
    G hm t ht K P clock parent v
  dsimp only at hp ⊢
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦
    mul_le_mul_of_nonneg_left (physical_child_budget_le hh hhalf hV hlo hup K P clock parent v i)
      (sq_nonneg (ClockSchedule.weight (ClockSchedule.sourceCells h) (ClockSchedule.sourceOrder K) clock i)))
  have hh' := mul_le_mul_of_nonneg_left (hp.trans hb) (show 0 ≤ h/2 by positivity)
  rw [← mul_assoc,mul_comm (h/2) ((ClockBackwardKernel.sourceWidth h)^2),sourceWidth_sq_mul hh] at hh'
  apply hh'.trans_eq
  simp_rw [Finset.mul_sum,sourceRadius_sq hh K]
  apply Finset.sum_congr rfl
  intro i _
  have htime (a : ℝ) : h*(2*h*(1-a^2)) = 2*h^2*(1-a^2) := by ring
  simp_rw [htime]
  ring

end Physical
end AcceleratedLogConcave.Root.RecursiveInnovation
