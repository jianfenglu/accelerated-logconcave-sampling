import AcceleratedLogConcave.Root.LocalRootLawWrapper
import AcceleratedLogConcave.Root.LocalRootLawAssembly

/-!

-/
noncomputable section
set_option autoImplicit false

namespace AcceleratedLogConcave.Root.LocalRootLawQuantitative
open MeasureTheory ProbabilityTheory
open Oracle Oracle.CanonicalTapeMeasurability
open ClockNoisyLayer ClockRetainedFinalSplice LocalRootLawWrapper
open scoped BigOperators

section FiniteEstimate
variable {I : Type*} [Fintype I]

/-- Weighted Cauchy, proved here by the nonnegative pairwise square. The bound
depends on total coefficient mass, not the number of final child slots. -/
theorem weighted_square (a u : I → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i * u i)^2 ≤ (∑ i, a i) * ∑ i, a i * (u i)^2 := by
  classical
  calc
    _ = ∑ i, ∑ j, (a i * u i) * (a j * u j) := by
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, ((a i * (u i)^2) * a j / 2 + a i * (a j * (u j)^2) / 2) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have h := mul_nonneg (mul_nonneg (ha i) (ha j)) (sq_nonneg (u i-u j))
      nlinarith
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_div,
        ← Finset.mul_sum, ← Finset.sum_mul]
      ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_weighted_sum_sq (c : I → ℝ) (e : I → E) :
    ‖∑ i, c i • e i‖^2 ≤ (∑ i, |c i|) * ∑ i, |c i| * ‖e i‖^2 := by
  classical
  have hnorm : ‖∑ i, c i • e i‖ ≤ ∑ i, |c i| * ‖e i‖ := by
    calc
      _ ≤ ∑ i, ‖c i • e i‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_smul, Real.norm_eq_abs]
  have hpos : 0 ≤ ∑ i, |c i| * ‖e i‖ :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (norm_nonneg _))
  exact ((sq_le_sq₀ (norm_nonneg _) hpos).mpr hnorm).trans
    (weighted_square (fun i => |c i|) (fun i => ‖e i‖) (fun i => abs_nonneg _))

theorem norm_defect_add_weighted_sum_sq (q : E) (c : I → ℝ) (e : I → E) :
    ‖q + ∑ i, c i • e i‖^2 ≤
      2 * ‖q‖^2 + 2 * (∑ i, |c i|) * ∑ i, |c i| * ‖e i‖^2 := by
  have hsum := norm_weighted_sum_sq c e
  have htri := norm_add_le q (∑ i, c i • e i)
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr htri
  nlinarith [sq_nonneg (‖q‖ - ‖∑ i, c i • e i‖)]
end FiniteEstimate

section Root
variable (P : SourceSchedule) (hR : P.R ≤ 1/2) (hc : 0 < P.csch)
  (hsmall : P.csch < 1/160) (clock : ClockLaw.Clock) {d : ℕ} (ell : ℕ)

local instance : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
  tapeSpace d (code P hR hc hsmall clock ell)

def visibleCoefficient (i : Index P) : ℝ :=
  -(ClockPublicSetup.s * ClockCollocation.rF P.delta) * weight P clock i

theorem coefficient_mass : (∑ i, |visibleCoefficient P clock i|) =
    ClockPublicSetup.s * ClockCollocation.rF P.delta * (clock : ℝ) := by
  have hs : 0 ≤ ClockPublicSetup.s * ClockCollocation.rF P.delta := by
    unfold ClockPublicSetup.s ClockCollocation.rF
    positivity
  have hw (i : Index P) : 0 ≤ weight P clock i := ClockSchedule.weight_nonneg _ _ clock i
  have habs (i : Index P) : |visibleCoefficient P clock i| =
      ClockPublicSetup.s * ClockCollocation.rF P.delta * weight P clock i := by
    simp only [visibleCoefficient, abs_mul, abs_neg, abs_of_nonneg hs, abs_of_nonneg (hw i)]
  simp_rw [habs]
  rw [← Finset.mul_sum]
  congr 1
  exact ClockSchedule.sum_weight _ _ (ClockSchedule.sourceCells_pos P.delta_pos)
    (ClockSchedule.sourceOrder_pos P.K) clock

def oldY (a : Sample P hR hc hsmall clock d ell) : Point d :=
  ClockPublicSetup.splitValues a.1.2 (initialE0 P hR hc hsmall clock ell a.2) 0

def oldH (a : Sample P hR hc hsmall clock d ell) : Point d :=
  ClockPublicSetup.splitValues a.1.2 (initialE0 P hR hc hsmall clock ell a.2) 1

/-- The same already-drawn designated active input, not a fresh copy. -/
def activeInput (a : Sample P hR hc hsmall clock d ell) : Index P → Point d :=
  activeValues P clock (oldH P hR hc hsmall clock ell a)
    (assemblyZ P hR hc hsmall clock ell a.2)

/-- The terminal branch retains its designated input, so H1=H0. -/
def terminalReference (Y : Sample P hR hc hsmall clock d ell → Point d)
    (a : Sample P hR hc hsmall clock d ell) : Point d :=
  ClockPublicSetup.s • Y a + ClockPublicSetup.noise • oldH P hR hc hsmall clock ell a

/-- Actual final reply minus its same-input width term and local mean target. -/
def localError (G : Point d → Point d)
    (g : Index P → Sample P hR hc hsmall clock d ell → Point d)
    (i : Index P) (a : Sample P hR hc hsmall clock d ell) : Point d :=
  finalReplies P hR hc hsmall clock ell G a i -
    width P clock i • activeInput P hR hc hsmall clock ell a i - g i a

/-- Only the exact parent integration/quadrature discrepancy. No executable
child value occurs in this term when g is supplied by the exact local target. -/
def quadratureDefect (Y : Sample P hR hc hsmall clock d ell → Point d)
    (g : Index P → Sample P hR hc hsmall clock d ell → Point d)
    (a : Sample P hR hc hsmall clock d ell) : Point d :=
  ClockPublicSetup.s • oldY P hR hc hsmall clock ell a +
    (∑ i, visibleCoefficient P clock i • g i a) - ClockPublicSetup.s • Y a

/-- Exact quantitative connection on every original execution tape. The
reference uses the same entering P, E0, H0 and designated active array. -/
theorem error_decomposition (G : Point d → Point d)
    (Y : Sample P hR hc hsmall clock d ell → Point d)
    (g : Index P → Sample P hR hc hsmall clock d ell → Point d)
    (a : Sample P hR hc hsmall clock d ell) :
    visible P hR hc hsmall clock ell G a - terminalReference P hR hc hsmall clock ell Y a =
      quadratureDefect P hR hc hsmall clock ell Y g a +
        ∑ i, visibleCoefficient P clock i • localError P hR hc hsmall clock ell G g i a := by
  rw [visible_eq_manuscript]
  have hp : a.1.2 = ClockPublicSetup.s • oldY P hR hc hsmall clock ell a +
      ClockPublicSetup.noise • oldH P hR hc hsmall clock ell a :=
    (split_reconstruct _ _).symm
  unfold terminalReference quadratureDefect localError activeInput oldY oldH
  simp only [smul_sub, Finset.sum_sub_distrib]
  nth_rw 1 [hp]
  unfold oldY oldH visibleCoefficient
  abel

theorem root_error_sq (G : Point d → Point d)
    (Y : Sample P hR hc hsmall clock d ell → Point d)
    (g : Index P → Sample P hR hc hsmall clock d ell → Point d)
    (a : Sample P hR hc hsmall clock d ell) :
    ‖visible P hR hc hsmall clock ell G a - terminalReference P hR hc hsmall clock ell Y a‖^2 ≤
      2 * ‖quadratureDefect P hR hc hsmall clock ell Y g a‖^2 +
      2 * (ClockPublicSetup.s * ClockCollocation.rF P.delta * (clock : ℝ)) *
        ∑ i, |visibleCoefficient P clock i| * ‖localError P hR hc hsmall clock ell G g i a‖^2 := by
  rw [error_decomposition]
  simpa only [coefficient_mass] using norm_defect_add_weighted_sum_sq
    (quadratureDefect P hR hc hsmall clock ell Y g a)
    (visibleCoefficient P clock) (fun i => localError P hR hc hsmall clock ell G g i a)

theorem terminalReference_measurable
    (Y : Sample P hR hc hsmall clock d ell → Point d) (hY : Measurable Y) :
    Measurable (terminalReference P hR hc hsmall clock ell Y) := by
  have he := (initialE0_measurable P hR hc hsmall clock ell (d := d)).comp
    (measurable_snd : Measurable (Prod.snd : Sample P hR hc hsmall clock d ell → _))
  have hh : Measurable (oldH P hR hc hsmall clock ell (d := d)) :=
    (measurable_fst.snd.const_smul ClockPublicSetup.noise).add
      (he.const_smul (-ClockPublicSetup.s))
  exact (hY.const_smul ClockPublicSetup.s).add (hh.const_smul ClockPublicSetup.noise)

/-- Second-moment assembly from LOCAL squared-error integrability. No root
accuracy or root integrability premise is required, and no independence is used.
This applies on the literal tape law or on any given common full-tape law. -/
theorem root_meanSquare_le (G : Point d → Point d) (hG : Measurable G)
    (Y : Sample P hR hc hsmall clock d ell → Point d) (hY : Measurable Y)
    (g : Index P → Sample P hR hc hsmall clock d ell → Point d)
    (μ : Measure (Sample P hR hc hsmall clock d ell))
    (hq : Integrable (fun a => ‖quadratureDefect P hR hc hsmall clock ell Y g a‖^2) μ)
    (he : ∀ i, Integrable (fun a => ‖localError P hR hc hsmall clock ell G g i a‖^2) μ) :
    (∫ a, ‖visible P hR hc hsmall clock ell G a -
      terminalReference P hR hc hsmall clock ell Y a‖^2 ∂μ) ≤
      2 * (∫ a, ‖quadratureDefect P hR hc hsmall clock ell Y g a‖^2 ∂μ) +
      2 * (ClockPublicSetup.s * ClockCollocation.rF P.delta * (clock : ℝ)) *
        ∑ i, |visibleCoefficient P clock i| *
          (∫ a, ‖localError P hR hc hsmall clock ell G g i a‖^2 ∂μ) := by
  have hw : Integrable (fun a => ∑ i, |visibleCoefficient P clock i| *
      ‖localError P hR hc hsmall clock ell G g i a‖^2) μ :=
    integrable_finsetSum _ (fun i _ => (he i).const_mul _)
  have hrhs := (hq.const_mul 2).add
    (hw.const_mul (2 * (ClockPublicSetup.s * ClockCollocation.rF P.delta * (clock : ℝ))))
  have hm := ((visible_measurable P hR hc hsmall clock ell G hG).sub
    (terminalReference_measurable P hR hc hsmall clock ell Y hY)).aestronglyMeasurable (μ := μ)
  have hi : Integrable (fun a => ‖visible P hR hc hsmall clock ell G a -
      terminalReference P hR hc hsmall clock ell Y a‖^2) μ := by
    apply hrhs.mono' (hm.norm.pow 2)
    filter_upwards [] with a
    simpa only [Pi.pow_apply, Pi.sub_apply, Pi.add_apply, Real.norm_eq_abs, abs_sq] using
      root_error_sq P hR hc hsmall clock ell G Y g a
  calc
    _ ≤ ∫ a, (2 * ‖quadratureDefect P hR hc hsmall clock ell Y g a‖^2 +
        2 * (ClockPublicSetup.s * ClockCollocation.rF P.delta * (clock : ℝ)) *
          ∑ i, |visibleCoefficient P clock i| *
            ‖localError P hR hc hsmall clock ell G g i a‖^2) ∂μ :=
      integral_mono hi hrhs (root_error_sq P hR hc hsmall clock ell G Y g)
    _ = _ := by
      rw [integral_add (hq.const_mul 2)
        (hw.const_mul (2 * (ClockPublicSetup.s * ClockCollocation.rF P.delta * (clock : ℝ)))),
        integral_const_mul, integral_const_mul,
        integral_finsetSum _ (fun i _ => (he i).const_mul _)]
      simp_rw [integral_const_mul]

/-- Insert local numerical moment bounds, not a final-error hypothesis. The
factor depends on coefficient mass s*rF*rho, even as the inventory grows. -/
theorem root_rms_le (G : Point d → Point d) (hG : Measurable G)
    (Y : Sample P hR hc hsmall clock d ell → Point d) (hY : Measurable Y)
    (g : Index P → Sample P hR hc hsmall clock d ell → Point d)
    (μ : Measure (Sample P hR hc hsmall clock d ell))
    (hq : Integrable (fun a => ‖quadratureDefect P hR hc hsmall clock ell Y g a‖^2) μ)
    (he : ∀ i, Integrable (fun a => ‖localError P hR hc hsmall clock ell G g i a‖^2) μ)
    (Q : ℝ) (E : Index P → ℝ)
    (hQ : (∫ a, ‖quadratureDefect P hR hc hsmall clock ell Y g a‖^2 ∂μ) ≤ Q^2)
    (hE : ∀ i, (∫ a, ‖localError P hR hc hsmall clock ell G g i a‖^2 ∂μ) ≤ (E i)^2) :
    Real.sqrt (∫ a, ‖visible P hR hc hsmall clock ell G a -
      terminalReference P hR hc hsmall clock ell Y a‖^2 ∂μ) ≤
      Real.sqrt (2 * Q^2 +
        2 * (ClockPublicSetup.s * ClockCollocation.rF P.delta * (clock : ℝ)) *
          ∑ i, |visibleCoefficient P clock i| * (E i)^2) := by
  have hmass : 0 ≤ 2 * (ClockPublicSetup.s * ClockCollocation.rF P.delta * (clock : ℝ)) := by
    have := clock.2.1
    unfold ClockPublicSetup.s ClockCollocation.rF
    positivity
  apply Real.sqrt_le_sqrt
  apply (root_meanSquare_le P hR hc hsmall clock ell G hG Y hY g μ hq he).trans
  apply add_le_add (mul_le_mul_of_nonneg_left hQ (by norm_num))
  apply mul_le_mul_of_nonneg_left _ hmass
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hE i) (abs_nonneg _))

/-- If the actual local supplier has error width_i * epsilon in mean-output
units, the weighted root factor is exactly n^2*rho^2*epsilon^2. There is no
inventory-size loss or division by the stopping clock, including rho=0. -/
theorem normalized_local_budget (ε : ℝ) :
    (ClockPublicSetup.s * ClockCollocation.rF P.delta * (clock : ℝ)) *
      (∑ i, |visibleCoefficient P clock i| * (width P clock i * ε)^2) =
      ClockPublicSetup.noise^2 * (clock : ℝ)^2 * ε^2 := by
  let k := ClockPublicSetup.s * ClockCollocation.rF P.delta
  let w := ClockBackwardKernel.sourceWidth P.delta
  have hw (i : Index P) : width P clock i = w := rfl
  have hk : k ≠ 0 := by
    unfold k ClockPublicSetup.s ClockCollocation.rF
    have := P.delta_pos
    positivity
  have hkw : k*w = ClockPublicSetup.noise := by
    change k * (ClockPublicSetup.noise / k) = ClockPublicSetup.noise
    field_simp [hk]
  calc
    _ = (k * (clock : ℝ)) * (∑ i, |visibleCoefficient P clock i|) * (w*ε)^2 := by
      simp_rw [hw, ← Finset.sum_mul]
      ring
    _ = (k*w)^2 * (clock : ℝ)^2 * ε^2 := by
      rw [coefficient_mass]
      change (k * (clock : ℝ)) * (k * (clock : ℝ)) * (w*ε)^2 = _
      ring
    _ = _ := by rw [hkw]

/-- The actual exact physical parent is directly admissible as Y, without
introducing another sampler or asking for an execution equality premise. -/
def exactParentY (F : Analysis.Poisson.ReferencePoissonFamily (Point d) 0 (1/2)) :
    Sample P hR hc hsmall clock d ell → Point d :=
  fun a => (LocalRootLawAssembly.exactHost P hR hc hsmall clock ell F
    (Real.sqrt (2*P.delta^2)) a).1.1.2

theorem exactParentY_measurable
    (F : Analysis.Poisson.ReferencePoissonFamily (Point d) 0 (1/2)) :
    Measurable (exactParentY P hR hc hsmall clock ell F) :=
  (LocalRootLawAssembly.exactHost_measurable P hR hc hsmall clock ell F _).fst.fst.snd

/-- Exact zero-clock accuracy fixture, with the initial exact parent value.
It imposes no hypothesis on any executed child reply or its error. -/
theorem zero_clock_error (G : Point d → Point d)
    (a : Sample P hR hc hsmall ⟨0, by norm_num⟩ d ell) :
    visible P hR hc hsmall ⟨0, by norm_num⟩ ell G a -
      terminalReference P hR hc hsmall ⟨0, by norm_num⟩ ell
        (oldY P hR hc hsmall ⟨0, by norm_num⟩ ell) a = 0 := by
  rw [visible_zero_clock]
  have hp := split_reconstruct a.1.2 (initialE0 P hR hc hsmall ⟨0, by norm_num⟩ ell a.2)
  change a.1.2 - (_ + _) = 0
  dsimp only [oldY, oldH]
  rw [hp, sub_self]

theorem dimension_zero_error (G : Point 0 → Point 0)
    (Y : Sample P hR hc hsmall clock 0 ell → Point 0)
    (a : Sample P hR hc hsmall clock 0 ell) :
    visible P hR hc hsmall clock ell G a -
      terminalReference P hR hc hsmall clock ell Y a = 0 := Subsingleton.elim _ _

end Root
end AcceleratedLogConcave.Root.LocalRootLawQuantitative
