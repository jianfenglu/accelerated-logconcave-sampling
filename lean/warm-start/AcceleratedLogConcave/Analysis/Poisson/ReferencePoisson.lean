import AcceleratedLogConcave.Analysis.Poisson.ReferenceFamily
import AcceleratedLogConcave.Analysis.Poisson.ReferenceMatrixIdentity
import AcceleratedLogConcave.Analysis.Poisson.TransportedBochner
import AcceleratedLogConcave.Analysis.Poisson.ReferenceStrongMultiplier
import AcceleratedLogConcave.Analysis.MovingPoisson

/-!
# The actual moving weighted Poisson inverse

This family packages only the classical potential/density hypotheses. Its
flow, transported laws, closed common domain, and weak inverses are constructed.
No inverse, transport map, common-domain equality, or derivative is family data.
-/
noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory InnerProductSpace Set Function
open scoped Topology ContDiff NNReal RealInnerProductSpace
namespace AcceleratedLogConcave.Analysis.Poisson
open WeightedGradient

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Classical data on a compact source interval. The time extensions in this
interface require only spatial C2 and joint continuity of gradient/Hessian. -/
structure ReferencePoissonFamily (a b : ℝ) where
  ordered : a ≤ b
  potential : ℝ → E → ℝ
  scale : ℝ → ℝ
  potential_C2 : ∀ t, ContDiff ℝ 2 (potential t)
  gradient_continuous : Continuous (uncurry (fun t => gradient (potential t)))
  hessian_continuous : Continuous (uncurry (fun t => hessianOperator (potential t)))
  scale_continuous : Continuous scale
  scaleBound : ℝ≥0
  scale_bounded : ∀ t ∈ Icc a b, |scale t| ≤ scaleBound
  lower : ℝ → ℝ
  lower_pos : ∀ t ∈ Icc a b, 0 < lower t
  hessian_lower : ∀ t ∈ Icc a b, ∀ x v,
    lower t * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (potential t)) x v v
  hessian_upper : ∀ t ∈ Icc a b, ∀ x v,
    fderiv ℝ (fderiv ℝ (potential t)) x v v ≤ ‖v‖ ^ 2
  law : ℝ → Measure E
  probability : ∀ t, IsProbabilityMeasure (law t)
  integrable : ∀ t ∈ Icc a b, Integrable (fun x => Real.exp (-potential t x))
  gibbs_law : ∀ t ∈ Icc a b, law t = volume.tilted (fun x => -potential t x)
  density : ℝ → E → ℝ
  densityVelocity : ℝ → E → ℝ
  density_continuous : ContinuousOn (uncurry density) (Icc a b ×ˢ (univ : Set E))
  densityVelocity_continuous : ContinuousOn (uncurry densityVelocity) (Ioo a b ×ˢ (univ : Set E))
  density_hasDerivAt : ∀ t ∈ Ioo a b, ∀ x,
    HasDerivAt (fun s => density s x) (densityVelocity t x) t
  density_C1 : ∀ t ∈ Ioo a b, ContDiff ℝ 1 (density t)
  continuity_equation : ∀ t ∈ Ioo a b, ∀ x,
    densityVelocity t x + fluxDivergence (fun y => density t y • referenceDrift potential scale t y) x = 0
  density_law : ∀ t ∈ Icc a b, law t = volume.withDensity (fun x => ENNReal.ofReal (density t x))
  density_nonneg : ∀ t ∈ Icc a b, ∀ x, 0 ≤ density t x

namespace ReferencePoissonFamily
variable {E} {a b : ℝ} (F : ReferencePoissonFamily E a b)
instance law_probability (t : ℝ) : IsProbabilityMeasure (F.law t) := F.probability t

def leftTime : Icc a b := ⟨a, le_rfl, F.ordered⟩

theorem hessian_nonneg (t : ℝ) (ht : t ∈ Icc a b) (x v : E) :
    0 ≤ fderiv ℝ (fderiv ℝ (F.potential t)) x v v :=
  (mul_nonneg (F.lower_pos t ht).le (sq_nonneg _)).trans (F.hessian_lower t ht x v)

def flow (t : Icc a b) : E ≃ₜ E :=
  referenceFlowHomeomorph F.potential F.scale (fun t _ => F.potential_C2 t)
    F.gradient_continuous F.scale_continuous F.scaleBound F.scale_bounded
    F.hessian_nonneg F.hessian_upper F.leftTime t

theorem flow_C1 (t : Icc a b) : ContDiff ℝ 1 (F.flow t) :=
  referenceFlowHomeomorph_contDiff F.potential F.scale F.ordered F.potential_C2
    F.gradient_continuous F.hessian_continuous F.scale_continuous F.scaleBound
    F.scale_bounded F.hessian_nonneg F.hessian_upper F.leftTime t

theorem flow_symm_C1 (t : Icc a b) : ContDiff ℝ 1 (F.flow t).symm :=
  referenceFlowHomeomorph_symm_contDiff F.potential F.scale F.ordered F.potential_C2
    F.gradient_continuous F.hessian_continuous F.scale_continuous F.scaleBound
    F.scale_bounded F.hessian_nonneg F.hessian_upper F.leftTime t

def jacobianBound : ℝ := Real.exp ((F.scaleBound : ℝ) * (b - a))
theorem jacobianBound_pos : 0 < F.jacobianBound := Real.exp_pos _
theorem one_le_jacobianBound : 1 ≤ F.jacobianBound :=
  Real.one_le_exp (mul_nonneg F.scaleBound.coe_nonneg (sub_nonneg.mpr F.ordered))

theorem flow_fderiv_bound (t : Icc a b) (x : E) : ‖fderiv ℝ (F.flow t) x‖ ≤ F.jacobianBound :=
  referenceFlowHomeomorph_fderiv_bound F.potential F.scale F.potential_C2 F.gradient_continuous
    F.scale_continuous F.scaleBound F.scale_bounded F.hessian_nonneg F.hessian_upper F.leftTime t x

theorem flow_symm_fderiv_bound (t : Icc a b) (x : E) : ‖fderiv ℝ (F.flow t).symm x‖ ≤ F.jacobianBound :=
  referenceFlowHomeomorph_symm_fderiv_bound F.potential F.scale F.potential_C2 F.gradient_continuous
    F.scale_continuous F.scaleBound F.scale_bounded F.hessian_nonneg F.hessian_upper F.leftTime t x

theorem flow_measurePreserving (t : Icc a b) : MeasurePreserving (F.flow t) (F.law a) (F.law t) :=
  referenceFlowHomeomorph_measurePreserving F.potential F.scale F.ordered F.potential_C2
    F.gradient_continuous F.hessian_continuous F.scale_continuous F.scaleBound
    F.scale_bounded F.hessian_nonneg F.hessian_upper F.density F.densityVelocity
    F.density_continuous F.densityVelocity_continuous F.density_hasDerivAt F.density_C1
    F.continuity_equation F.law F.density_law F.density_nonneg t

def unitary {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K] (t : Icc a b) :
    Lp K 2 (F.law t) ≃ₗᵢ[ℝ] Lp K 2 (F.law a) :=
  pullback (F.flow t).toMeasurableEquiv (F.flow_measurePreserving t)

abbrev referenceClosedGradient : Lp ℝ 2 (F.law a) →ₗ.[ℝ] Lp E 2 (F.law a) := closedGradient (F.law a) (F.potential a)
  ((F.potential_C2 a).of_le (by norm_num)) (F.integrable a F.leftTime.property) (F.gibbs_law a F.leftTime.property)

abbrev Graph : Type _ := ↥(centeredGraph F.referenceClosedGradient (mean (F.law a)))
instance graph_complete : CompleteSpace F.Graph :=
  (centeredGraph_closed F.referenceClosedGradient
    (closedGradient_isClosed (F.law a) (F.potential a)
      ((F.potential_C2 a).of_le (by norm_num)) (F.integrable a F.leftTime.property)
      (F.gibbs_law a F.leftTime.property)) (mean (F.law a))).completeSpace_coe

def inclusion : F.Graph →L[ℝ] Lp ℝ 2 (F.law a) := referenceGraphValue F.referenceClosedGradient (mean (F.law a))
def baseGradient : F.Graph →L[ℝ] Lp E 2 (F.law a) := referenceGraphGradient F.referenceClosedGradient (mean (F.law a))

def gradientCoefficient (t : ℝ) : Lp E 2 (F.law a) →L[ℝ] Lp E 2 (F.law a) :=
  referenceGradientMultiplier F.potential F.scale F.ordered F.potential_C2
    F.gradient_continuous F.hessian_continuous F.scale_continuous F.scaleBound
    F.scale_bounded F.hessian_nonneg F.hessian_upper (F.law a) t

def movingGradient (t : ℝ) : F.Graph →L[ℝ] Lp E 2 (F.law a) :=
  (F.gradientCoefficient t).comp F.baseGradient

theorem gradientCoefficient_eq_transport (t : ℝ) (ht : t ∈ Ioo a b) :
    F.gradientCoefficient t = inverseJacobianMultiplier (F.law a)
      (F.flow ⟨t, ht.1.le, ht.2.le⟩) (F.flow_symm_C1 ⟨t, ht.1.le, ht.2.le⟩)
      F.jacobianBound (F.flow_symm_fderiv_bound ⟨t, ht.1.le, ht.2.le⟩) := by
  have heq := referenceFlow_inverseJacobianMultiplier_eq F.potential F.scale F.ordered F.potential_C2
    F.gradient_continuous F.hessian_continuous F.scale_continuous F.scaleBound
    F.scale_bounded F.hessian_nonneg F.hessian_upper (F.law a) ⟨t, ht.1.le, ht.2.le⟩
  change inverseJacobianMultiplier (F.law a) (F.flow ⟨t, ht.1.le, ht.2.le⟩)
    (F.flow_symm_C1 ⟨t, ht.1.le, ht.2.le⟩) F.jacobianBound
    (F.flow_symm_fderiv_bound ⟨t, ht.1.le, ht.2.le⟩) = _ at heq
  rw [heq]
  unfold gradientCoefficient referenceGradientMultiplier
  congr 1
  funext x
  exact extendedReferenceGradientMatrix_eq F.potential F.scale F.ordered F.potential_C2
    F.gradient_continuous F.hessian_continuous F.scale_continuous F.scaleBound
    F.scale_bounded F.hessian_nonneg F.hessian_upper t ht x

theorem gradientCoefficient_eq_id (t : ℝ) (ht : t ∉ Ioo a b) :
    F.gradientCoefficient t = ContinuousLinearMap.id ℝ (Lp E 2 (F.law a)) := by
  apply ContinuousLinearMap.ext
  intro G
  apply Lp.ext
  filter_upwards [fieldMultiplier_coe (F.law a)
    (extendedReferenceGradientMatrix F.potential F.scale F.ordered F.potential_C2
      F.gradient_continuous F.hessian_continuous F.scale_continuous F.scaleBound
      F.scale_bounded F.hessian_nonneg F.hessian_upper t)
    (extendedReferenceGradientMatrix_continuous F.potential F.scale F.ordered F.potential_C2
      F.gradient_continuous F.hessian_continuous F.scale_continuous F.scaleBound
      F.scale_bounded F.hessian_nonneg F.hessian_upper t) F.jacobianBound
    (extendedReferenceGradientMatrix_norm_le F.potential F.scale F.ordered F.potential_C2
      F.gradient_continuous F.hessian_continuous F.scale_continuous F.scaleBound
      F.scale_bounded F.hessian_nonneg F.hessian_upper t) G] with x hx
  exact hx.trans (by simp only [extendedReferenceGradientMatrix, ite_eq_right ht,
    ContinuousLinearMap.id_apply])

def coercivity : ℝ := F.lower a / (F.lower a + 1) / F.jacobianBound ^ 2

theorem coercivity_pos : 0 < F.coercivity := by
  have hm := F.lower_pos a F.leftTime.property
  have hB := F.jacobianBound_pos
  unfold coercivity
  positivity

theorem movingGradient_coercive (t : ℝ) (u : F.Graph) :
    F.coercivity * ‖u‖ ^ 2 ≤ ‖F.movingGradient t u‖ ^ 2 := by
  have hp (v : F.referenceClosedGradient.domain) (hv : mean (F.law a) v = 0) :
      F.lower a * ‖(v : Lp ℝ 2 (F.law a))‖ ^ 2 ≤ ‖F.referenceClosedGradient v‖ ^ 2 :=
    Gibbs.closedGradient_poincare (F.law a) (F.potential a) (F.potential_C2 a)
      (F.integrable a F.leftTime.property) (F.gibbs_law a F.leftTime.property)
      (F.lower a) 1 (F.lower_pos a F.leftTime.property) (F.hessian_lower a F.leftTime.property)
      (by simpa only [one_mul] using F.hessian_upper a F.leftTime.property) v
      ((mean_apply (F.law a) v).symm.trans hv)
  by_cases ht : t ∈ Ioo a b
  · unfold movingGradient
    rw [F.gradientCoefficient_eq_transport t ht]
    exact referenceGraph_multiplier_coercive _ _ (F.lower_pos a F.leftTime.property) F.jacobianBound_pos hp
      _ (jacobianAdjointMultiplier (F.law a) (F.flow ⟨t, ht.1.le, ht.2.le⟩)
        (F.flow_C1 _) F.jacobianBound (F.flow_fderiv_bound _))
      (jacobian_inverseJacobianMultiplier _ _ _ _ _ _ _ _)
      (jacobianAdjointMultiplier_norm_le _ _ _ _ _) u
  · unfold movingGradient
    rw [F.gradientCoefficient_eq_id t ht, ContinuousLinearMap.id_comp]
    exact referenceGraph_multiplier_coercive _ _ (F.lower_pos a F.leftTime.property) F.jacobianBound_pos hp
      (ContinuousLinearMap.id ℝ _) (ContinuousLinearMap.id ℝ _) (fun _ => rfl)
      (ContinuousLinearMap.norm_id_le.trans F.one_le_jacobianBound) u

/-- The constructed weak inverse on the genuine fixed graph. -/
def solution (t : ℝ) (g : Lp ℝ 2 (F.law a)) : F.Graph :=
  MovingForms.commonDomainSolution (F.movingGradient t) F.inclusion F.coercivity_pos
    (F.movingGradient_coercive t) g

/-- The actual gradient inverse in fixed reference coordinates. -/
def gradientInverse (t : ℝ) : Lp ℝ 2 (F.law a) →L[ℝ] Lp E 2 (F.law a) :=
  (F.movingGradient t).comp ((MovingForms.coerciveInverse
    (MovingForms.energyCoefficient (F.movingGradient t)) F.coercivity_pos
    (MovingForms.energyCoefficient_coercive _ (F.movingGradient_coercive t))).comp F.inclusion.adjoint)

theorem gradientInverse_apply (t : ℝ) (g : Lp ℝ 2 (F.law a)) :
    F.gradientInverse t g = F.movingGradient t (F.solution t g) := by
  have hi : F.inclusion.adjoint g = MovingForms.variationalRHS F.inclusion g := by
    apply ext_inner_right ℝ
    intro v
    rw [ContinuousLinearMap.adjoint_inner_left, MovingForms.variationalRHS_inner]
  simp only [gradientInverse, solution, MovingForms.commonDomainSolution, ContinuousLinearMap.comp_apply, hi]


def hessian (t : ℝ) (ht : t ∈ Ioo a b) : Lp E 2 (F.law a) →L[ℝ] Lp E 2 (F.law a) :=
  referenceHessianMultiplier F.potential F.scale F.ordered F.potential_C2
    F.gradient_continuous F.hessian_continuous F.scale_continuous F.scaleBound
    F.scale_bounded F.hessian_nonneg F.hessian_upper (F.law a) t ht

theorem movingGradient_continuousAt (t : ℝ) (ht : t ∈ Ioo a b) :
    ContinuousAt F.movingGradient t :=
  (referenceGradientMultiplier_continuousAt F.potential F.scale F.ordered F.potential_C2
    F.gradient_continuous F.hessian_continuous F.scale_continuous F.scaleBound
    F.scale_bounded F.hessian_nonneg F.hessian_upper (F.law a) t ht).clm_comp continuousAt_const

theorem energyCoefficient_continuousAt (t : ℝ) (ht : t ∈ Ioo a b) :
    ContinuousAt (fun s => MovingForms.energyCoefficient (F.movingGradient s)) t :=
  referenceGradientEnergyCoefficient_continuousAt F.potential F.scale F.ordered F.potential_C2
    F.gradient_continuous F.hessian_continuous F.scale_continuous F.scaleBound
    F.scale_bounded F.hessian_nonneg F.hessian_upper (F.law a) t ht F.baseGradient

theorem gradientInverse_continuousAt (t : ℝ) (ht : t ∈ Ioo a b) :
    ContinuousAt F.gradientInverse t :=
  (F.movingGradient_continuousAt t ht).clm_comp
    ((MovingForms.continuousAt_coerciveInverse
      (fun s => MovingForms.energyCoefficient (F.movingGradient s)) F.coercivity_pos
      (fun s => MovingForms.energyCoefficient_coercive _ (F.movingGradient_coercive s))
      (F.energyCoefficient_continuousAt t ht)).clm_comp continuousAt_const)

/-- The actual source reflection coefficient on the reference L2 spaces. -/
def materialOperator (t : ℝ) (ht : t ∈ Ioo a b) :
    Lp ℝ 2 (F.law a) →L[ℝ] Lp E 2 (F.law a) :=
  (F.scale t) • (gradientReflection (closedGradientRange (F.movingGradient t).toLinearMap)).toLinearIsometry.toContinuousLinearMap.comp
    ((F.hessian t ht).comp (F.gradientInverse t))

/-- Strong differentiation of the constructed actual inverse, with the source
reflection formula. Only C2 potentials and the proved flow/form calculus enter. -/
theorem gradientInverse_hasDerivAt (t : ℝ) (ht : t ∈ Ioo a b) (g : Lp ℝ 2 (F.law a)) :
    HasDerivAt (fun s => F.gradientInverse s g) (F.materialOperator t ht g) t := by
  simp only [gradientInverse_apply]
  apply hasDerivAt_commonDomainGradient F.movingGradient F.inclusion F.coercivity_pos
    F.movingGradient_coercive t (F.movingGradient_continuousAt t ht)
    (F.energyCoefficient_continuousAt t ht) g (F.scale t) (F.hessian t ht)
  · exact referenceGradientMultiplier_hasDerivAt_curvature F.potential F.scale F.ordered F.potential_C2
      F.gradient_continuous F.hessian_continuous F.scale_continuous F.scaleBound
      F.scale_bounded F.hessian_nonneg F.hessian_upper (F.law a) t ht (F.baseGradient (F.solution t g))
  · exact referenceGradientEnergyCoefficient_hasDerivAt_curvature F.potential F.scale F.ordered F.potential_C2
      F.gradient_continuous F.hessian_continuous F.scale_continuous F.scaleBound
      F.scale_bounded F.hessian_nonneg F.hessian_upper (F.law a) t ht F.baseGradient (F.solution t g)

/-- At every interior time this is exactly the genuine weighted gradient
inverse, conjugated by the proved measure-preserving reference flow. -/
theorem gradientInverse_eq_physical (t : ℝ) (ht : t ∈ Ioo a b) (g : Lp ℝ 2 (F.law a)) :
    F.gradientInverse t g = F.unitary ⟨t, ht.1.le, ht.2.le⟩
      (gradientPoissonInverse (F.law t) (F.potential t) (F.potential_C2 t)
        (F.integrable t ⟨ht.1.le, ht.2.le⟩) (F.gibbs_law t ⟨ht.1.le, ht.2.le⟩)
        (F.lower t) 1 (F.lower_pos t ⟨ht.1.le, ht.2.le⟩)
        (F.hessian_lower t ⟨ht.1.le, ht.2.le⟩)
        (by simpa only [one_mul] using F.hessian_upper t ⟨ht.1.le, ht.2.le⟩)
        ((F.unitary ⟨t, ht.1.le, ht.2.le⟩).symm g)) := by
  have heq := commonDomainSolution_gradient_eq_pullback_gradientInverse
    (F.law a) (F.law t) (F.potential a) (F.potential t)
    ((F.potential_C2 a).of_le (by norm_num)) ((F.potential_C2 t).of_le (by norm_num))
    (F.integrable a F.leftTime.property) (F.integrable t ⟨ht.1.le, ht.2.le⟩)
    (F.gibbs_law a F.leftTime.property) (F.gibbs_law t ⟨ht.1.le, ht.2.le⟩)
    (F.flow ⟨t, ht.1.le, ht.2.le⟩) (F.flow_measurePreserving ⟨t, ht.1.le, ht.2.le⟩)
    (F.flow_C1 _) (F.flow_symm_C1 _) F.jacobianBound F.jacobianBound
    (F.flow_fderiv_bound _) (F.flow_symm_fderiv_bound _) (F.potential_C2 a) (F.potential_C2 t)
    (F.lower a) 1 (F.lower t) 1 (F.lower_pos a F.leftTime.property)
    (F.lower_pos t ⟨ht.1.le, ht.2.le⟩) F.jacobianBound_pos
    (F.hessian_lower a F.leftTime.property)
    (by simpa only [one_mul] using F.hessian_upper a F.leftTime.property)
    (F.hessian_lower t ⟨ht.1.le, ht.2.le⟩)
    (by simpa only [one_mul] using F.hessian_upper t ⟨ht.1.le, ht.2.le⟩) g
  rw [F.gradientInverse_apply]
  unfold solution movingGradient
  simpa only [transportedGraphGradient, ← F.gradientCoefficient_eq_transport t ht,
    baseGradient, inclusion, unitary, coercivity] using heq


/-- The material Hessian is unitary conjugation of the genuine physical Hessian. -/
theorem hessian_eq_transport (t : ℝ) (ht : t ∈ Ioo a b) :
    F.hessian t ht = transportedHessianMultiplier (F.law a) (F.law t) (F.potential t)
      (F.potential_C2 t) (F.flow ⟨t, ht.1.le, ht.2.le⟩)
      (F.flow_measurePreserving ⟨t, ht.1.le, ht.2.le⟩) (F.lower t) 1
      (F.hessian_lower t ⟨ht.1.le, ht.2.le⟩)
      (by simpa only [one_mul] using F.hessian_upper t ⟨ht.1.le, ht.2.le⟩) := by
  apply ContinuousLinearMap.ext
  intro G
  apply Lp.ext
  exact (referenceHessianMultiplier_coe F.potential F.scale F.ordered F.potential_C2
    F.gradient_continuous F.hessian_continuous F.scale_continuous F.scaleBound
    F.scale_bounded F.hessian_nonneg F.hessian_upper (F.law a) t ht G).trans
    (transportedHessianMultiplier_coe (F.law a) (F.law t) (F.potential t) (F.potential_C2 t)
      (F.flow ⟨t, ht.1.le, ht.2.le⟩) (F.flow_measurePreserving ⟨t, ht.1.le, ht.2.le⟩)
      (F.lower t) 1 (F.hessian_lower t ⟨ht.1.le, ht.2.le⟩)
      (by simpa only [one_mul] using F.hessian_upper t ⟨ht.1.le, ht.2.le⟩) G).symm

/-- The full physical Bochner theorem supplies the sharp material curvature
bound on the actual moving solution, with no inverse-gap loss. -/
theorem hessian_gradientInverse_norm_le (t : ℝ) (ht : t ∈ Ioo a b) (g : Lp ℝ 2 (F.law a)) :
    ‖F.hessian t ht (F.gradientInverse t g)‖ ≤ ‖g‖ := by
  rw [F.hessian_eq_transport t ht, F.gradientInverse_eq_physical t ht]
  change ‖transportedHessianMultiplier _ _ _ _ _ _ _ _ _ _
    (pullback _ _ _)‖ ≤ _
  rw [transportedHessianMultiplier_pullback, LinearIsometryEquiv.norm_map]
  have hb := hessianMultiplier_comp_gradientPoissonInverse_norm_le
    (F.law t) (F.potential t) (F.potential_C2 t) (F.integrable t ⟨ht.1.le, ht.2.le⟩)
    (F.gibbs_law t ⟨ht.1.le, ht.2.le⟩) (F.lower t) (F.lower_pos t ⟨ht.1.le, ht.2.le⟩)
    (F.hessian_lower t ⟨ht.1.le, ht.2.le⟩)
    (by simpa only [one_mul] using F.hessian_upper t ⟨ht.1.le, ht.2.le⟩)
  exact (ContinuousLinearMap.le_of_opNorm_le _ hb _).trans
    (by simp only [one_mul, LinearIsometryEquiv.norm_map]; exact le_rfl)

/-- The source moving-gradient constant is exactly `|c(t)|`. -/
theorem materialOperator_norm_le (t : ℝ) (ht : t ∈ Ioo a b) :
    ‖F.materialOperator t ht‖ ≤ |F.scale t| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _)
  intro g
  simp only [materialOperator, smul_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    norm_smul, Real.norm_eq_abs, LinearIsometryEquiv.norm_map]
  exact mul_le_mul_of_nonneg_left (F.hessian_gradientInverse_norm_le t ht g) (abs_nonneg _)

theorem gradientInverse_continuousOn : ContinuousOn F.gradientInverse (Ioo a b) :=
  fun t ht => (F.gradientInverse_continuousAt t ht).continuousWithinAt

/-- Integrate the strong derivative on any compact interval strictly inside
the source window. The auxiliary identity extension is not used at its boundary. -/
theorem gradientInverse_norm_sub_le_integral {s t : ℝ}
    (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) (hst : s ≤ t) :
    ‖F.gradientInverse t - F.gradientInverse s‖ ≤ ∫ r in s..t, |F.scale r| := by
  let B (r : ℝ) := if hr : r ∈ Ioo a b then F.materialOperator r hr else 0
  have hmem (r : ℝ) (hr : r ∈ Icc s t) : r ∈ Ioo a b :=
    ⟨hs.1.trans_le hr.1, hr.2.trans_lt ht.2⟩
  apply norm_sub_le_integral_of_strong_derivative F.gradientInverse B (fun r => |F.scale r|) hst
  · intro g r hr
    exact ((F.gradientInverse_continuousAt r (hmem r hr)).clm_apply continuousAt_const).continuousWithinAt
  · intro g r hr
    have hm := hmem r ⟨hr.1.le, hr.2.le⟩
    simpa only [B, dite_eq_left hm] using F.gradientInverse_hasDerivAt r hm g
  · intro r hr
    have hm := hmem r ⟨hr.1.le, hr.2.le⟩
    simpa only [B, dite_eq_left hm] using F.materialOperator_norm_le r hm
  · exact fun r _ => abs_nonneg _
  · exact F.scale_continuous.abs.intervalIntegrable s t

end ReferencePoissonFamily
end AcceleratedLogConcave.Analysis.Poisson
