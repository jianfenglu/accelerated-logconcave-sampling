import AcceleratedLogConcave.Analysis.SpatialVolterra
import AcceleratedLogConcave.Conditional.Transport.ActualBackwardSpatialVariations
import AcceleratedLogConcave.Analysis.OrderedSpatialComposition
import AcceleratedLogConcave.Conditional.Flow.ExtendedState

/-!

-/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace AcceleratedLogConcave.Conditional.Transport.SpatialFlow
open AcceleratedLogConcave.Analysis.SpatialVariation
open AcceleratedLogConcave.Analysis.SpatialPartition
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Only abbreviation, definitionally the original backward homeomorphism. -/
abbrev actualY (d : PositiveVarianceFlowData E) (s : ℝ) : E → E :=
  backwardProbabilityTransport d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 s

/-- Every actual derivative direction is retained; n=0 is included as an identity,
not as a zero-order vector bound. No unknown higher flow identity is assumed. -/
theorem actual_iteratedFDeriv_volterra (d : PositiveVarianceFlowData E)
    (hsmall : d.r^2*d.ell ≤ 1/2) (n : ℕ) (m : Fin n → E) (y : E)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    iteratedFDeriv ℝ n (actualY d t) y m =
      iteratedFDeriv ℝ n (id : E → E) y m -
        ∫ s in t..d.b, iteratedFDeriv ℝ n
          (fun z => probabilityVelocity d.F d.x d.r s (actualY d s z)) y m := by
  obtain ⟨C,hC,hCY⟩ := exists_smooth_backward_representative
    d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 hsmall y
  have h := along_volterra_of_local_representative d.hb0 hC y hCY
    (fun s hs z _ => backward_hasDerivWithinAt
      d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 hs z) (List.ofFn m) ht
  rw [backward_spatial_terminal,
    along_ofFn_eq_iteratedFDeriv contDiff_id n m y,
    along_ofFn_eq_iteratedFDeriv
      (contDiff_backward_spatial d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 hsmall ht)
      n m y] at h
  rw [h]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.2] at hs
  have hs0 : s ∈ Icc 0 d.b := ⟨ht.1.trans hs.1,hs.2⟩
  exact along_ofFn_eq_iteratedFDeriv
    ((contDiff_probabilityVelocity_spatial d.hF d.hlo d.hhi d.x
      (r := d.r) (by linarith [hs0.1]) (hs0.2.trans_lt d.hb1)).comp
      (contDiff_backward_spatial d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 hsmall hs0)) n m y

/-- Same Volterra identity after an arbitrary fixed output readout. This directly
supplies every coordinate without any norm-equivalence or integrability premise. -/
theorem actual_iteratedFDeriv_volterra_readout (d : PositiveVarianceFlowData E)
    (hsmall : d.r^2*d.ell ≤ 1/2) (n : ℕ) (m : Fin n → E) (y : E)
    (L : E →L[ℝ] ℝ) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    L (iteratedFDeriv ℝ n (actualY d t) y m) =
      L (iteratedFDeriv ℝ n (id : E → E) y m) -
        ∫ s in t..d.b, L (iteratedFDeriv ℝ n
          (fun z => probabilityVelocity d.F d.x d.r s (actualY d s z)) y m) := by
  obtain ⟨C,hC,hCY⟩ := exists_smooth_backward_representative
    d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 hsmall y
  have h := along_volterra_readout d.hb0 hC y hCY
    (fun s hs z _ => backward_hasDerivWithinAt
      d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 hs z) L (List.ofFn m) ht
  have hY (s : ℝ) (hs : s ∈ Icc 0 d.b) := contDiff_backward_spatial
    d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 hsmall hs
  simp only [along_clm (hY t ht), along_clm (hY d.b ⟨d.hb0,le_rfl⟩),
    backward_spatial_terminal, along_ofFn_eq_iteratedFDeriv contDiff_id n m y,
    along_ofFn_eq_iteratedFDeriv (hY t ht) n m y] at h
  rw [h]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.2] at hs
  have hs0 : s ∈ Icc 0 d.b := ⟨ht.1.trans hs.1,hs.2⟩
  have hR := (contDiff_probabilityVelocity_spatial d.hF d.hlo d.hhi d.x
    (r := d.r) (by linarith [hs0.1]) (hs0.2.trans_lt d.hb1)).comp (hY s hs0)
  exact (congrFun (along_clm hR L (List.ofFn m)) y).trans
    (congrArg L (along_ofFn_eq_iteratedFDeriv hR n m y))

/-- Positive-order Volterra with the actual highest jet separated LINEARLY.
The forcing is reused verbatim from OrderedSpatialComposition, with its proved
strict-lower-block support. No inverse or product recurrence is duplicated. -/
theorem actual_iteratedFDeriv_volterra_separated (d : PositiveVarianceFlowData E)
    (hsmall : d.r^2*d.ell ≤ 1/2) (n : ℕ) (hn : 0 < n)
    (m : Fin n → E) (y : E) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    iteratedFDeriv ℝ n (actualY d t) y m =
      iteratedFDeriv ℝ n (id : E → E) y m - ∫ s in t..d.b,
        (fderiv ℝ (probabilityVelocity d.F d.x d.r s) (actualY d s y))
          (iteratedFDeriv ℝ n (actualY d s) y m) +
        spatialForcing (probabilityVelocity d.F d.x d.r s) (actualY d s) y n hn m := by
  rw [actual_iteratedFDeriv_volterra d hsmall n m y ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.2] at hs
  have hs0 : s ∈ Icc 0 d.b := ⟨ht.1.trans hs.1,hs.2⟩
  have he := iteratedFDeriv_comp_separated (x := y)
    (contDiff_probabilityVelocity_spatial d.hF d.hlo d.hhi d.x
      (r := d.r) (by linarith [hs0.1]) (hs0.2.trans_lt d.hb1)).contDiffAt
    (contDiff_backward_spatial d.hF d.hell d.hlo d.hhi d.x
      d.hr d.hb0 d.hb1 hsmall hs0).contDiffAt n hn
  exact congrArg (fun T => T m) he

end AcceleratedLogConcave.Conditional.Transport.SpatialFlow
