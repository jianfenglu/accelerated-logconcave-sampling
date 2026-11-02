import AcceleratedLogConcave.Analysis.ODEObservableJet
import AcceleratedLogConcave.Analysis.OrderedJacobianWords
import AcceleratedLogConcave.Conditional.Flow.ExtendedJets

/-! Actual B'=BC and its ordered ordinary derivative expansion, for the
existing enlarged-slab inverse-flow Jacobian. The terminal spatial argument
y is fixed throughout. All analytic premises are discharged under the
original C² convex bounded-Hessian flow data. -/
noncomputable section
open Set
open scoped ContDiff Topology NNReal
set_option autoImplicit false
namespace AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
open Analysis.PositiveVarianceSlab Analysis.CoupledVelocityPolynomial Analysis.ODEJet
open OAI.LogConcaveSampling.GlobalODE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (d : PositiveVarianceFlowData E)

def jacobian (t : ℝ) (y : E) : E →L[ℝ] E := (d.state t y).snd

/-- The coefficient before composition with the actual backward path. -/
def jacobianCoefficientField (p : CoupledSpaceTime E) : E →L[ℝ] E :=
  (d.r * p.1) • firstScaledJet d.F d.x d.r p.1 p.2.1

def jacobianCoefficientJet (k : ℕ) (t : ℝ) (y : E) : E →L[ℝ] E :=
  observableJet (openDomain (CoupledState E))
    (conditionalCoupledVelocity d.F d.x d.r) d.jacobianCoefficientField k (t, d.state t y)

theorem jacobianCoefficientJet_zero (t : ℝ) (y : E) :
    d.jacobianCoefficientJet 0 t y =
      (d.r * t) • firstScaledJet d.F d.x d.r t (d.state t y).fst := rfl

theorem contDiffOn_jacobianCoefficientField :
    ContDiffOn ℝ ∞ d.jacobianCoefficientField (openDomain (CoupledState E)) := by
  have hu : ContDiffOn ℝ ∞
      ((fun p : ℝ × E => firstScaledJet d.F d.x d.r p.1 p.2) ∘ timeSpaceProjection E)
      (openDomain (CoupledState E)) :=
    (contDiffOn_firstScaledJet_natural d.hF d.hlo d.hhi d.x d.r).comp_continuousLinearMap _
  exact (contDiffOn_const.mul contDiff_fst.contDiffOn).smul hu

theorem hasDerivAt_jacobianCoefficientJet (k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) (y : E) :
    HasDerivAt (fun u => d.jacobianCoefficientJet k u y)
      (d.jacobianCoefficientJet (k+1) t y) t :=
  hasDerivAt_observableJet_along (isOpen_openDomain (CoupledState E))
    (contDiffOn_conditionalCoupledVelocity d.hF d.hlo d.hhi d.x d.r)
    d.contDiffOn_jacobianCoefficientField
    (construction_subset d.hb0 d.hb1 ⟨ht.1.le, ht.2.le⟩)
    (d.hasDerivAt_state ht y) k

/-- Actual backward variational equation with the manuscript's B C order. -/
theorem hasDerivAt_jacobian {t : ℝ} (ht : t ∈ Ioo (left d.b) (right d.b)) (y : E) :
    HasDerivAt (fun u => d.jacobian u y)
      (d.jacobian t y * d.jacobianCoefficientJet 0 t y) t := by
  have hh := (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt t
    (d.hasDerivAt_state ht y)
  change HasDerivAt (fun u => (d.state u y).snd)
    ((d.r * t) • (d.state t y).snd.comp (firstScaledJet d.F d.x d.r t (d.state t y).fst)) t at hh
  simpa only [jacobian, jacobianCoefficientJet, observableJet, jacobianCoefficientField,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_smul] using hh

/-- Every C jet is the actual ordinary derivative, with fixed terminal y. -/
theorem iteratedDeriv_jacobianCoefficient (n : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) (y : E) :
    iteratedDeriv n (fun u => d.jacobianCoefficientJet 0 u y) t =
      d.jacobianCoefficientJet n t y :=
  Analysis.iteratedDeriv_eq_of_finite_ladder n (fun k u => d.jacobianCoefficientJet k u y)
    isOpen_Ioo (fun k _ _u hu => d.hasDerivAt_jacobianCoefficientJet k hu y) ht

/-- The ordered-word supplier is instantiated on the ACTUAL flow, without
new B/C smoothness, derivative, moment or expression hypotheses. -/
theorem iteratedDeriv_jacobian_eq_words (n : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) (y : E) :
    iteratedDeriv n (fun u => d.jacobian u y) t =
      d.jacobian t y * Analysis.OrderedJacobianWords.evaluateSum
        (fun k u => d.jacobianCoefficientJet k u y)
        (Analysis.OrderedJacobianWords.words n) t :=
  Analysis.OrderedJacobianWords.iteratedDeriv_eq_words n
    (fun u => d.jacobian u y) (fun k u => d.jacobianCoefficientJet k u y)
    isOpen_Ioo (fun _u hu => d.hasDerivAt_jacobian hu y)
    (fun k _ _u hu => d.hasDerivAt_jacobianCoefficientJet k hu y) ht

/-- Exact physical zeroth-order constant from the existing actual-flow
Lipschitz estimate; the enlarged construction slab has width exactly one. -/
theorem norm_jacobian_le (t : ℝ) (y : E) :
    ‖d.jacobian t y‖ ≤ Real.exp (d.r ^ 2 * d.ell) := by
  have hh := norm_flowReferenceJacobian_uniform_le d.interval_le d.continuous_clippedVelocity
    d.lipschitz_clippedVelocity d.reference t y
  change ‖d.jacobian t y‖ ≤ _ at hh
  have he : ((‖d.r‖₊ * ⟨d.r * d.ell, mul_nonneg d.hr.le d.hell⟩ : ℝ≥0) : ℝ) *
      (right d.b - left d.b) = d.r ^ 2 * d.ell := by
    change ‖d.r‖ * (d.r * d.ell) * (right d.b - left d.b) = _
    rw [Real.norm_eq_abs, abs_of_pos d.hr]
    dsimp [right, left]
    ring
  rwa [he] at hh


/-- Existing canonical state jets are exactly the ordinary Jacobian jets. -/
theorem iteratedDeriv_jacobian_eq_stateJet (n : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) (y : E) :
    iteratedDeriv n (fun u => d.jacobian u y) t = (d.jet n t y).snd := by
  have hl := Analysis.iteratedDeriv_eq_of_finite_ladder n
    (fun k u => (d.jet k u y).snd) isOpen_Ioo
    (fun k _ u hu => (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt u
      (d.hasDerivAt_jet k hu y)) ht
  have he : (fun u => d.jacobian u y) =ᶠ[𝓝 t] (fun u => (d.jet 0 u y).snd) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    simp only [jacobian, jet, stateJet, d.time_eq ⟨hu.1.le, hu.2.le⟩]
  exact ((he.iteratedDeriv n).eq_of_nhds).trans hl

/-- Pointwise algebraic join to the state jets used by the canonical L²
momentum lift. No independent candidate Jacobian is introduced. -/
theorem stateJet_snd_eq_words (n : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) (y : E) :
    (d.jet n t y).snd =
      d.jacobian t y * Analysis.OrderedJacobianWords.evaluateSum
        (fun k u => d.jacobianCoefficientJet k u y)
        (Analysis.OrderedJacobianWords.words n) t :=
  (d.iteratedDeriv_jacobian_eq_stateJet n ht y).symm.trans
    (d.iteratedDeriv_jacobian_eq_words n ht y)

end AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
