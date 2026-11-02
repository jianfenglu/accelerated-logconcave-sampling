import AcceleratedLogConcave.Kinetic.Mixing.DiscreteAverage
import AcceleratedLogConcave.Kinetic.Mixing.CenteredOperator

/-! Actual centered discrete transition and its genuine adjoint. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson Reheating ConditionalContraction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {r : ℝ} (hr : 0 < r) (F : ReferencePoissonFamily E 0 r)
  (ell s n : ℝ) (hsn : s^2+n^2=1)
  (κ : Icc (0 : ℝ) r → Kernel (GaussianPhase E) E)
  [∀ t, IsMarkovKernel (κ t)]
  (hκ : ∀ t, ConditionallyInvariant (stdGaussian E) (κ t))
  (τ : Icc (0 : ℝ) r → ℝ) (Γ : ℝ) (hΓ : 0 ≤ Γ)
  (hreturn : ∀ t : Icc (0 : ℝ) r, heatedLaw (F.law t) (τ t) = F.law 0)

variable (hI : ∀ f, Integrable (fun t =>
    returningClockChannel F ell t s n hsn (κ t) (hκ t) (τ t) Γ hΓ (hreturn t) f)
    (boundedClockLaw r hr))


/-- The actual clock-averaged observable transition on mean-zero inputs. -/
def centeredDiscretePhaseOperator :=
  centeredOperator ((F.law 0).prod (stdGaussian E))
    (discretePhaseOperator hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI)
    (discretePhaseOperator_mean hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI)

/-- The actual density transition restricted to the same centered space. -/
def centeredDiscretePhaseDensity :=
  centeredOperator ((F.law 0).prod (stdGaussian E))
    (discretePhaseDensity hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI)
    (discretePhaseDensity_mean hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI)

theorem centeredDiscretePhaseOperator_adjoint :
    (centeredDiscretePhaseOperator hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI).adjoint =
      centeredDiscretePhaseDensity hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI :=
  centeredOperator_adjoint _ _ _ _

/-- The n-step density and observable operators have identical ordinary L2 norms. -/
theorem centeredDiscretePhase_norm_pow (k : ℕ) :
    ‖centeredDiscretePhaseDensity hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI ^ k‖ =
      ‖centeredDiscretePhaseOperator hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI ^ k‖ := by
  rw [← centeredDiscretePhaseOperator_adjoint]
  exact opNorm_adjoint_pow _ k

/-- Once the concrete one-step energy estimate is proved, both actual centered
operators inherit its iterated ordinary L2 rate. This is the final duality step,
not an independent contraction assumption for the observable operator. -/
theorem centeredDiscretePhase_mixing_of_energy
    (energy : centered ((F.law 0).prod (stdGaussian E)) → ℝ)
    (α β q : ℝ) (hα : 0 < α) (hβ : 0 ≤ β) (hq : 0 ≤ q)
    (hlow : ∀ f, α * ‖f‖^2 ≤ energy f)
    (hup : ∀ f, energy f ≤ β * ‖f‖^2)
    (hstep : ∀ f, energy
      (centeredDiscretePhaseDensity hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI f) ≤ q * energy f)
    (k : ℕ) :
    ‖centeredDiscretePhaseDensity hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI ^ k‖ ≤
      Real.sqrt ((β/α)*q^k) ∧
    ‖centeredDiscretePhaseOperator hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI ^ k‖ ≤
      Real.sqrt ((β/α)*q^k) := by
  have hd := opNorm_pow_le_of_energy
    (centeredDiscretePhaseDensity hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI)
    energy α β q hα hβ hq hlow hup hstep k
  exact ⟨hd, (centeredDiscretePhase_norm_pow hr F ell s n hsn κ hκ τ Γ hΓ hreturn hI k).symm.le.trans hd⟩

end AcceleratedLogConcave.Kinetic
