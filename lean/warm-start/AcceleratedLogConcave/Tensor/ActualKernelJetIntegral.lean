import AcceleratedLogConcave.Conditional.Transport.CompactSpatialJetIntegral
import AcceleratedLogConcave.Tensor.QuantitativeBudgetTargets

/-!

-/
noncomputable section
set_option maxHeartbeats 1000000
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff
namespace AcceleratedLogConcave.Tensor.QuantitativeKernel
open Conditional Conditional.Transport
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

/-- The literal source integrand B_t(y) composed with U_1(t,Y_t(y)). -/
def actualKernelIntegrand (d : PositiveVarianceFlowData E) (t : ℝ) :
    E → E →L[ℝ] E :=
  transportedSteinIntegrand d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 t

/-- Original data supply a single continuous representative for the entire
n-th spatial jet over the closed slab, together with its exact kernel integral.
No domination, integrability, higher-jet, or kernel-bound premise remains. -/
theorem exists_continuous_actualKernelJet_integrand
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (y : E) :
    ∃ Q : ℝ → E [×n]→L[ℝ] (E →L[ℝ] E), Continuous Q ∧
      (∀ t ∈ Icc 0 d.b, Q t = iteratedFDeriv ℝ n (actualKernelIntegrand d t) y) ∧
      iteratedFDeriv ℝ n (actualK d) y = ∫ t in 0..d.b, Q t := by
  obtain ⟨C,hC,hCeq⟩ := exists_smooth_transportedSteinIntegrand_extension
    d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 hsmall y
  let Q : ℝ → E [×n]→L[ℝ] (E →L[ℝ] E) :=
    fun t => iteratedFDeriv ℝ n (fun z => C (t,z)) y
  have hQ : Continuous Q := (contDiff_spatialJet n hC).continuous.comp
    (continuous_id.prodMk continuous_const)
  have hQeq (t : ℝ) (ht : t ∈ Icc 0 d.b) :
      Q t = iteratedFDeriv ℝ n (actualKernelIntegrand d t) y := by
    have he : (fun z => C (t,z)) =ᶠ[𝓝 y] actualKernelIntegrand d t := by
      filter_upwards [Metric.ball_mem_nhds y (by norm_num : (0:ℝ) < 1)] with z hz
      exact hCeq t ht z hz
    exact (he.iteratedFDeriv ℝ n).eq_of_nhds
  have hlocal : actualK d =ᶠ[𝓝 y] (fun z => ∫ t in 0..d.b, C (t,z)) := by
    filter_upwards [Metric.ball_mem_nhds y (by norm_num : (0:ℝ) < 1)] with z hz
    unfold actualK transportedSteinKernelTranspose
    apply intervalIntegral.integral_congr
    intro t ht
    exact (hCeq t (by simpa only [uIcc_of_le d.hb0] using ht) z hz).symm
  refine ⟨Q,hQ,hQeq,?_⟩
  rw [(hlocal.iteratedFDeriv ℝ n).eq_of_nhds]
  exact iteratedFDeriv_intervalIntegral_of_contDiff n hC d.hb0 y

/-- Actual spatial integrand jets are continuous up to both time endpoints. -/
theorem continuousOn_actualKernelIntegrand_jet
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (y : E) :
    ContinuousOn (fun t => iteratedFDeriv ℝ n (actualKernelIntegrand d t) y)
      (Icc 0 d.b) := by
  obtain ⟨Q,hQ,hQeq,_⟩ := exists_continuous_actualKernelJet_integrand d hsmall n y
  exact hQ.continuousOn.congr (fun t ht => (hQeq t ht).symm)

/-- Honest Bochner integrability, independent of a desired quantitative bound. -/
theorem intervalIntegrable_actualKernelIntegrand_jet
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (y : E) :
    IntervalIntegrable (fun t => iteratedFDeriv ℝ n (actualKernelIntegrand d t) y)
      volume 0 d.b :=
  (continuousOn_actualKernelIntegrand_jet d hsmall n y).intervalIntegrable_of_Icc d.hb0

/-- All-order differentiation under the actual Stein integral, with its exact
operator-valued multilinear codomain and without direction symmetrization. -/
theorem actualKernel_iteratedFDeriv_eq_integral
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (y : E) :
    iteratedFDeriv ℝ n (actualK d) y =
      ∫ t in 0..d.b, iteratedFDeriv ℝ n (actualKernelIntegrand d t) y := by
  obtain ⟨Q,_,hQeq,hint⟩ := exists_continuous_actualKernelJet_integrand d hsmall n y
  rw [hint]
  apply intervalIntegral.integral_congr
  intro t ht
  exact hQeq t (by simpa only [uIcc_of_le d.hb0] using ht)

/-- Retain every derivative label and both operator indices. This map is used
only for Bochner functoriality, never by taking its operator norm. -/
def operatorCoefficientMap (n : ℕ) :
    (E [×n]→L[ℝ] (E →L[ℝ] E)) →L[ℝ] Coeff (Fin n ⊕ (Unit ⊕ Unit)) D :=
  { toFun := fun (A : E [×n]→L[ℝ] (E →L[ℝ] E)) =>
      WithLp.toLp 2 (fun (a : (Fin n ⊕ (Unit ⊕ Unit)) → Fin D) => inner ℝ
        (EuclideanSpace.basisFun (Fin D) ℝ (a (.inr (.inr ()))))
        ((A (fun i => EuclideanSpace.basisFun (Fin D) ℝ (a (.inl i))))
          (EuclideanSpace.basisFun (Fin D) ℝ (a (.inr (.inl ()))))))
    map_add' := by intro A B; ext a; simp [inner_add_right]
    map_smul' := by intro c A; ext a; simp [inner_smul_right]
    cont := by
      apply (PiLp.continuous_toLp 2
        (fun _ : (Fin n ⊕ (Unit ⊕ Unit)) → Fin D => ℝ)).comp
      apply continuous_pi
      intro a
      fun_prop }

/-- Coefficient-level identity in the literal legacy slot convention. -/
theorem actualKernel_operatorJetCoeff_eq_integral
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (y : E) :
    operatorJetCoeff n (actualK d) y =
      ∫ t in 0..d.b, operatorJetCoeff n (actualKernelIntegrand d t) y := by
  change operatorCoefficientMap n (iteratedFDeriv ℝ n (actualK d) y) = _
  rw [actualKernel_iteratedFDeriv_eq_integral d hsmall n y]
  exact ((operatorCoefficientMap n).intervalIntegral_comp_comm
    (intervalIntegrable_actualKernelIntegrand_jet d hsmall n y)).symm

/-- Integrability of actual coefficient tensors follows from original data,
not from any Hilbert--Schmidt budget. -/
theorem intervalIntegrable_actualKernel_operatorJetCoeff
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (y : E) :
    IntervalIntegrable (fun t => operatorJetCoeff n (actualKernelIntegrand d t) y)
      volume 0 d.b :=
  ((operatorCoefficientMap n).continuous.comp_continuousOn
    (continuousOn_actualKernelIntegrand_jet d hsmall n y)).intervalIntegrable_of_Icc d.hb0

end AcceleratedLogConcave.Tensor.QuantitativeKernel

namespace AcceleratedLogConcave.Tensor.QuantitativeKernel
open Conditional Conditional.Transport
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

/-- For each derivative order, one constant dominates the actual spatial jet
for EVERY time in the full closed integration interval and every spatial point
in a closed half-ball. This is a local-in-space time-integral majorant, not a
claim that compactness controls the unbounded Gaussian integration variable. -/
theorem exists_actualKernelIntegrand_jet_majorant
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (y : E) :
    ∃ M : ℝ, 0 ≤ M ∧ IntervalIntegrable (fun _ : ℝ => M) volume 0 d.b ∧
      ∀ t ∈ Icc 0 d.b, ∀ z ∈ closedBall y (1/2),
        ‖iteratedFDeriv ℝ n (actualKernelIntegrand d t) z‖ ≤ M := by
  obtain ⟨C,hC,hCeq⟩ := exists_smooth_transportedSteinIntegrand_extension
    d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 hsmall y
  have hJ := (contDiff_spatialJet n hC).continuous
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod (isCompact_closedBall y (1/2))).exists_bound_of_continuousOn hJ.continuousOn
  refine ⟨|M|,abs_nonneg M,intervalIntegrable_const,?_⟩
  intro t ht z hz
  have hz' : z ∈ ball y 1 := mem_ball.mpr
    ((mem_closedBall.mp hz).trans_lt (by norm_num : (1/2:ℝ) < 1))
  have he : (fun w => C (t,w)) =ᶠ[𝓝 z] actualKernelIntegrand d t := by
    filter_upwards [isOpen_ball.mem_nhds hz'] with w hw
    exact hCeq t ht w hw
  rw [← (he.iteratedFDeriv ℝ n).eq_of_nhds]
  exact (hM (t,z) ⟨ht,hz⟩).trans (le_abs_self M)

/-- The spatial jet at probability time zero is covered by the same supplier.
This does not invoke a positive-time limit or divide by probability time. -/
theorem actualKernelIntegrand_jet_continuousWithinAt_zero
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (y : E) :
    ContinuousWithinAt (fun t => iteratedFDeriv ℝ n (actualKernelIntegrand d t) y)
      (Icc 0 d.b) 0 :=
  continuousOn_actualKernelIntegrand_jet d hsmall n y 0 ⟨le_rfl,d.hb0⟩

/-- The zero-length time integral is genuinely zero at every spatial order. -/
theorem actualKernel_iteratedFDeriv_endpoint_zero
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    (hb : d.b = 0) (n : ℕ) (y : E) :
    iteratedFDeriv ℝ n (actualK d) y = 0 := by
  rw [actualKernel_iteratedFDeriv_eq_integral d hsmall n y, hb,
    intervalIntegral.integral_same]

/-- Fixed rectangular unfolding of the retained operator jet. Its norm is
never estimated by its Hilbert--Schmidt coefficient norm. -/
def operatorJetSplitMap (n : ℕ) (S : Finset (Fin n ⊕ (Unit ⊕ Unit))) :
    (E [×n]→L[ℝ] (E →L[ℝ] E)) →L[ℝ]
      (RightHilbert D S →L[ℝ] LeftHilbert D S) :=
  ((splitOperatorEquiv D S).toLinearMap.toContinuousLinearMap).comp
    (operatorCoefficientMap n)

/-- The rectangular-cut norm commutes with the linear assembly and is bounded
by the integral of that SAME rectangular-cut norm. No dimension factor enters. -/
theorem actualKernel_splitNorm_le_integral
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (y : E) (S : Finset (Fin n ⊕ (Unit ⊕ Unit))) :
    splitNorm D S (operatorJetCoeff n (actualK d) y) ≤
      ∫ t in 0..d.b, splitNorm D S (operatorJetCoeff n (actualKernelIntegrand d t) y) := by
  have hi := intervalIntegrable_actualKernelIntegrand_jet d hsmall n y
  have hc := (operatorJetSplitMap n S).intervalIntegral_comp_comm hi
  change ‖operatorJetSplitMap n S (iteratedFDeriv ℝ n (actualK d) y)‖ ≤ _
  rw [actualKernel_iteratedFDeriv_eq_integral d hsmall n y, ← hc]
  exact intervalIntegral.norm_integral_le_integral_norm d.hb0

/-- Final compact-time integration of any legitimately established fixed-cut
integrand bound. Continuity and derivative interchange are already discharged.
The integrand bound is explicitly NOT asserted by this theorem. -/
theorem actualKernel_splitNorm_le_const_integrand
    (d : PositiveVarianceFlowData E) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (y : E) (S : Finset (Fin n ⊕ (Unit ⊕ Unit))) {C : ℝ}
    (hbound : ∀ t ∈ Icc 0 d.b,
      splitNorm D S (operatorJetCoeff n (actualKernelIntegrand d t) y) ≤ C) :
    splitNorm D S (operatorJetCoeff n (actualK d) y) ≤ C * d.b := by
  have hi := intervalIntegrable_actualKernelIntegrand_jet d hsmall n y
  have hc := (operatorJetSplitMap n S).intervalIntegral_comp_comm hi
  change ‖operatorJetSplitMap n S (iteratedFDeriv ℝ n (actualK d) y)‖ ≤ _
  rw [actualKernel_iteratedFDeriv_eq_integral d hsmall n y, ← hc]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := d.b) (C := C)
    (f := fun t => operatorJetSplitMap n S
      (iteratedFDeriv ℝ n (actualKernelIntegrand d t) y)) (fun t ht =>
        hbound t (by rw [uIoc_of_le d.hb0] at ht; exact ⟨ht.1.le,ht.2⟩))
  simpa only [sub_zero,abs_of_nonneg d.hb0] using h

end AcceleratedLogConcave.Tensor.QuantitativeKernel
