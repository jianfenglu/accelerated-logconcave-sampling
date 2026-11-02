import AcceleratedLogConcave.Kinetic.PhaseMomentumIBP
import AcceleratedLogConcave.Kinetic.PhaseTestSlicing
import AcceleratedLogConcave.Kinetic.ConditionalContraction.FieldChaos

/-! Actual weighted Hamiltonian integration by parts against compact C1 phase
tests, with cancellation of the unbounded score terms before any L2 estimate. -/
noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.ConditionalContraction
open Analysis.WeightedGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- One genuine closed-gradient component paired with the actual Hamiltonian
vector field. All tests are arbitrary compact C1 phase functions. -/
theorem phase_hamiltonian_component_ibp (μ : Measure E) [IsProbabilityMeasure μ]
    (V : E → ℝ) (hV : ContDiff ℝ 1 V)
    (hI : Integrable (fun x => Real.exp (-V x))) (hμ : μ = volume.tilted (fun x => -V x))
    (u : Sobolev μ V hV hI hμ) (b v : E) (s n : ℝ)
    (φ : GaussianPhase E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Integrable (fun z => (u : Lp ℝ 2 μ) z.1.1 * inner ℝ b z.1.2 *
      ((s * inner ℝ v z.1.2 - n * inner ℝ v z.2) * fderiv ℝ φ z ((v,0),0) -
        fderiv ℝ V z.1.1 v * (s * fderiv ℝ φ z ((0,v),0) - n * fderiv ℝ φ z ((0,0),v))))
      (gaussianPhaseMeasure μ) ∧
    (∫ z, (u : Lp ℝ 2 μ) z.1.1 * inner ℝ b z.1.2 *
      ((s * inner ℝ v z.1.2 - n * inner ℝ v z.2) * fderiv ℝ φ z ((v,0),0) -
        fderiv ℝ V z.1.1 v * (s * fderiv ℝ φ z ((0,v),0) - n * fderiv ℝ φ z ((0,0),v)))
      ∂gaussianPhaseMeasure μ) =
      -(∫ z, φ z * inner ℝ (closedGradient μ V hV hI hμ u z.1.1) v *
        inner ℝ b z.1.2 * (s * inner ℝ v z.1.2 - n * inner ℝ v z.2)
        ∂gaussianPhaseMeasure μ) +
      s * inner ℝ b v * ∫ z, (u : Lp ℝ 2 μ) z.1.1 * fderiv ℝ V z.1.1 v * φ z
        ∂gaussianPhaseMeasure μ := by
  let c : E → ℝ := fun x => fderiv ℝ V x v
  have hcont : Continuous c := (hV.continuous_fderiv one_ne_zero).clm_apply continuous_const
  let pL : GaussianPhase E →L[ℝ] ℝ := (innerSL ℝ v).comp
    ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.fst ℝ (E×E) E))
  let eL : GaussianPhase E →L[ℝ] ℝ := (innerSL ℝ v).comp (ContinuousLinearMap.snd ℝ (E×E) E)
  let l := s • pL - n • eL
  let ψ : GaussianPhase E → ℝ := fun z => l z * φ z
  have hψ : ContDiff ℝ 1 ψ := l.contDiff.mul hφ
  have hcψ : HasCompactSupport ψ := hc.mul_left
  have hd (z : GaussianPhase E) : fderiv ℝ ψ z ((v,0),0) =
      (s * inner ℝ v z.1.2 - n * inner ℝ v z.2) * fderiv ℝ φ z ((v,0),0) := by
    change (fderiv ℝ (⇑l * φ) z) _ = _
    rw [((l.hasFDerivAt).mul (hφ.differentiable_one z).hasFDerivAt).fderiv]
    simp [l, pL, eL]
  let S : GaussianPhase E → ℝ := fun z => (u : Lp ℝ 2 μ) z.1.1 * inner ℝ b z.1.2 *
    ((s * inner ℝ v z.1.2 - n * inner ℝ v z.2) * fderiv ℝ φ z ((v,0),0))
  let P : GaussianPhase E → ℝ := fun z => (u : Lp ℝ 2 μ) z.1.1 * c z.1.1 *
    (inner ℝ b z.1.2 * fderiv ℝ φ z ((0,v),0))
  let A : GaussianPhase E → ℝ := fun z => (u : Lp ℝ 2 μ) z.1.1 * c z.1.1 *
    (inner ℝ b z.1.2 * fderiv ℝ φ z ((0,0),v))
  let Q : GaussianPhase E → ℝ := fun z => (u : Lp ℝ 2 μ) z.1.1 * c z.1.1 *
    ((inner ℝ b z.1.2 * inner ℝ v z.1.2 - inner ℝ b v) * φ z)
  let M : GaussianPhase E → ℝ := fun z => (u : Lp ℝ 2 μ) z.1.1 * c z.1.1 *
    (inner ℝ b z.1.2 * inner ℝ v z.2 * φ z)
  let H : GaussianPhase E → ℝ := fun z => (u : Lp ℝ 2 μ) z.1.1 * c z.1.1 * φ z
  let F : GaussianPhase E → ℝ := fun z => φ z *
    inner ℝ (closedGradient μ V hV hI hμ u z.1.1) v * inner ℝ b z.1.2 *
      (s * inner ℝ v z.1.2 - n * inner ℝ v z.2)
  have hp := phase_momentum_linear_ibp μ (u : Lp ℝ 2 μ) c hcont b v φ hφ hc
  have ha := phase_auxiliary_linear_ibp μ (u : Lp ℝ 2 μ) c hcont b v φ hφ hc
  have hH : Integrable H (gaussianPhaseMeasure μ) :=
    phase_compact_position_integrable μ (u : Lp ℝ 2 μ) c hcont φ hφ.continuous hc
  have hS : Integrable S (gaussianPhaseMeasure μ) := by
    have hh := phase_compact_position_integrable μ (u : Lp ℝ 2 μ) (fun _ => 1) continuous_const
      (fun z => inner ℝ b z.1.2 * (l z * fderiv ℝ φ z ((v,0),0)))
      ((continuous_const.inner (continuous_snd.comp continuous_fst)).mul
        (l.continuous.mul ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)))
      ((hc.fderiv_apply ℝ ((v,0),0)).mul_left.mul_left)
    convert hh using 1
    funext z
    simp [S, l, pL, eL, mul_assoc]
  have hs := phase_test_weighted_ibp μ V hV hI hμ u b v ψ hψ hcψ
  have hleft : (fun z => ψ z * inner ℝ (closedGradient μ V hV hI hμ u z.1.1) v *
      inner ℝ b z.1.2) = F := by
    funext z
    simp only [ψ, F]
    simp [l, pL, eL]
    ring
  have hright : (fun z => (u : Lp ℝ 2 μ) z.1.1 * inner ℝ b z.1.2 *
      (fderiv ℝ ψ z ((v,0),0) - ψ z * fderiv ℝ V z.1.1 v)) =
      (fun z => S z - s * Q z + n * M z - (s * inner ℝ b v) * H z) := by
    funext z
    rw [hd]
    simp only [S, Q, M, H, ψ, c]
    simp [l, pL, eL]
    ring
  rw [hleft, hright] at hs
  have hs₁ := integral_sub ((hS.sub (hp.2.1.const_mul s)).add (ha.2.1.const_mul n))
    (hH.const_mul (s * inner ℝ b v))
  have hs₂ := integral_add (hS.sub (hp.2.1.const_mul s)) (ha.2.1.const_mul n)
  have hs₃ := integral_sub hS (hp.2.1.const_mul s)
  simp only [Pi.add_apply, Pi.sub_apply] at hs₁ hs₂ hs₃
  have he := hs.2.2
  rw [hs₁, hs₂, hs₃, integral_const_mul, integral_const_mul, integral_const_mul] at he
  have hw : (fun z => (u : Lp ℝ 2 μ) z.1.1 * inner ℝ b z.1.2 *
      ((s * inner ℝ v z.1.2 - n * inner ℝ v z.2) * fderiv ℝ φ z ((v,0),0) -
        fderiv ℝ V z.1.1 v * (s * fderiv ℝ φ z ((0,v),0) - n * fderiv ℝ φ z ((0,0),v)))) =
      (fun z => S z - s * P z + n * A z) := by
    funext z
    dsimp [S, P, A, c]
    ring
  rw [hw]
  refine ⟨(hS.sub (hp.1.const_mul s)).add (ha.1.const_mul n), ?_⟩
  have hwa := integral_add (hS.sub (hp.1.const_mul s)) (ha.1.const_mul n)
  have hws := integral_sub hS (hp.1.const_mul s)
  simp only [Pi.sub_apply] at hwa
  rw [hwa, hws, integral_const_mul, integral_const_mul, hp.2.2, ha.2.2]
  change (∫ z, S z ∂gaussianPhaseMeasure μ) - s * (∫ z, Q z ∂gaussianPhaseMeasure μ) +
    n * (∫ z, M z ∂gaussianPhaseMeasure μ) =
    -(∫ z, F z ∂gaussianPhaseMeasure μ) + s * inner ℝ b v * (∫ z, H z ∂gaussianPhaseMeasure μ)
  linarith

end AcceleratedLogConcave.Kinetic.ConditionalContraction
