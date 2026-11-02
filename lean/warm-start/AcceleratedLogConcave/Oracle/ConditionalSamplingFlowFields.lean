import AcceleratedLogConcave.Numerics.SamplingFlowLp
import AcceleratedLogConcave.Conditional.Flow.Restriction

/-! Actual conditional Gaussian-start Phi/u suppliers. These are
NOT the original Gibbs-law reverse-heat ReferencePoissonFamily flow. Fixed
anchor x and sampling source time are retained without an initial-law swap. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
namespace AcceleratedLogConcave.Oracle.ConditionalSamplingFlowFields
open Numerics Numerics.AffineGraph SamplingFlowLp Conditional
variable {ι : Type*} [Fintype ι]
variable {F : (EuclideanSpace ℝ ι) → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)
  (x : (EuclideanSpace ℝ ι)) {r : ℝ} (hr : 0 < r) {T : ℝ} (hT : 0 ≤ T) (hT1 : T < 1)

/-- Physical position of the fixed-anchor conditional path at its actual time. -/
def Phi (t : ℝ) (zeta : (EuclideanSpace ℝ ι)) : (EuclideanSpace ℝ ι) :=
  x + (r*t) • sourcePath hF hell hlo hup x hr hT hT1 t zeta

/-- Uncentered primitive reply. The nonzero initial mean is deliberately kept. -/
def reply (t : ℝ) (zeta : (EuclideanSpace ℝ ι)) : (EuclideanSpace ℝ ι) :=
  centeredReply hF hell hlo hup x hr hT hT1 t zeta + Gibbs.primitiveMean F x r

theorem Phi_continuous (t : ℝ) : Continuous (Phi hF hell hlo hup x hr hT hT1 t) := by
  have hp : Continuous (fun z : EuclideanSpace ℝ ι => sourcePath hF hell hlo hup x hr hT hT1 t z) :=
    (continuous_sourcePath hF hell hlo hup x hr hT hT1).comp
      (show Continuous (fun z : EuclideanSpace ℝ ι => (t,z)) from continuous_const.prodMk continuous_id)
  exact (hp.const_smul (r*t)).const_add x

theorem reply_continuous (t : ℝ) : Continuous (reply hF hell hlo hup x hr hT hT1 t) :=
  ((continuous_centeredReply hF hell hlo hup x hr hT hT1).comp
    (continuous_const.prodMk continuous_id)).add continuous_const

theorem Phi_eq_actual {t : ℝ} (ht : t ∈ Icc 0 T) (zeta : (EuclideanSpace ℝ ι)) :
    Phi hF hell hlo hup x hr hT hT1 t zeta =
      x + (r*t) • convexProbabilityFlow hF hell hlo hup x hr hT
        (by norm_num) hT1 ⟨0,le_rfl,hT⟩ zeta t := by
  rw [Phi, sourcePath_eq hF hell hlo hup x hr hT hT1 ht]

theorem reply_eq_primitive {t : ℝ} (ht : t ∈ Icc 0 T) (zeta : (EuclideanSpace ℝ ι)) :
    reply hF hell hlo hup x hr hT hT1 t zeta =
      Gibbs.primitiveMean F (Phi hF hell hlo hup x hr hT hT1 t zeta)
        (r*Real.sqrt (1-t^2)) := by
  simp only [reply, centeredReply, sourceTime_eq hT ht, sub_add_cancel, Phi]

/-- At the setup endpoint the physical center is the prescribed anchor. -/
theorem Phi_zero (zeta : (EuclideanSpace ℝ ι)) : Phi hF hell hlo hup x hr hT hT1 0 zeta = x := by
  simp only [Phi, mul_zero, zero_smul, add_zero]

/-- The setup reply retains the actual primitive mean; it is not centered to zero. -/
theorem reply_zero (zeta : (EuclideanSpace ℝ ι)) :
    reply hF hell hlo hup x hr hT hT1 0 zeta = Gibbs.primitiveMean F x r := by
  rw [reply_eq_primitive hF hell hlo hup x hr hT hT1 ⟨le_rfl,hT⟩,
    Phi_zero hF hell hlo hup x hr hT hT1]
  norm_num

/-- Exact conditional marginal of the SAME chosen source path. Restriction
uniqueness, not a replacement flow, identifies the shorter endpoint theorem. -/
theorem sourcePath_preserving {t : ℝ} (ht : t ∈ Icc 0 T) :
    MeasurePreserving (sourcePath hF hell hlo hup x hr hT hT1 t)
      (stdGaussian (EuclideanSpace ℝ ι)) (interpolationLaw F x r t) := by
  classical
  have hsub : Icc 0 t ⊆ Icc 0 T := fun _ hu => ⟨hu.1,hu.2.trans ht.2⟩
  have he (zeta : (EuclideanSpace ℝ ι)) :
      convexProbabilityFlowHomeomorph hF hell hlo hup x hr ht.1
        (by norm_num) (ht.2.trans_lt hT1) ⟨0,le_rfl,ht.1⟩ ⟨t,ht.1,le_rfl⟩ zeta =
      sourcePath hF hell hlo hup x hr hT hT1 t zeta := by
    rw [convexProbabilityFlowHomeomorph_apply, sourcePath_eq hF hell hlo hup x hr hT hT1 ht]
    exact meanProbabilityFlow_eq_on_subinterval ht.1 hT hsub r
      (conditionalMean F x r)
      (continuousOn_conditionalMean hF hlo hup x r (by norm_num) (ht.2.trans_lt hT1))
      (continuousOn_conditionalMean hF hlo hup x r (by norm_num) hT1)
      (fun u hu => lipschitzWith_conditionalMean hF hell hlo hup x hr
        (by linarith [hu.1]) (hu.2.trans_lt (ht.2.trans_lt hT1)))
      (fun u hu => lipschitzWith_conditionalMean hF hell hlo hup x hr
        (by linarith [hu.1]) (hu.2.trans_lt hT1)) ⟨0,le_rfl,ht.1⟩ ⟨t,ht.1,le_rfl⟩ zeta
  have hp := convexProbabilityFlow_measurePreserving_le hF hell hlo hup x hr ht.1
    (by norm_num) (ht.2.trans_lt hT1)
  rw [interpolationLaw_zero hF hlo x r] at hp
  convert hp using 1
  exact (funext he).symm

/-- Exact physical marginal as an affine pushforward. No equality with the
original Gibbs-law reverse-heat family is asserted. -/
theorem Phi_map {t : ℝ} (ht : t ∈ Icc 0 T) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (Phi hF hell hlo hup x hr hT hT1 t) =
      (interpolationLaw F x r t).map (fun y => x+(r*t) • y) := by
  have hp := sourcePath_preserving hF hell hlo hup x hr hT hT1 ht
  rw [← hp.map_eq, Measure.map_map (by fun_prop) hp.measurable]
  rfl

/-- Literal prefix reference fields after a caller supplies only its actual
seed/residual projections. No coupling or independence premise is introduced. -/
theorem prefix_fields_measurable {H : Type*} [MeasurableSpace H]
    (t rho : ℝ) (seed residual : H → (EuclideanSpace ℝ ι)) (hseed : Measurable seed)
    (hresidual : Measurable residual) :
    Measurable (fun q => Phi hF hell hlo hup x hr hT hT1 t (seed q) + rho • residual q) ∧
    Measurable (fun q => reply hF hell hlo hup x hr hT hT1 t (seed q)) := by
  exact ⟨((Phi_continuous hF hell hlo hup x hr hT hT1 t).measurable.comp hseed).add
      (hresidual.const_smul rho),
    (reply_continuous hF hell hlo hup x hr hT hT1 t).measurable.comp hseed⟩

end AcceleratedLogConcave.Oracle.ConditionalSamplingFlowFields
