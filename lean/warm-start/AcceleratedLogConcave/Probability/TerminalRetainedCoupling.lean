import AcceleratedLogConcave.Probability.ExecutableTerminalLaw
import AcceleratedLogConcave.Probability.ExecutableKernel

/-! The actual terminal execution and its diagonal reference, retaining the
entire standalone seed. All scalar parameters and the center vary jointly.
The structural instruction tape is kept verbatim, including its unit leaves.
This module supplies no nonterminal retained-law or conditional-law identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace AcceleratedLogConcave.Probability.TerminalRetainedCoupling
open Oracle Oracle.TapeLowering MixedResidualTape ExecutableTerminalLaw Gibbs
variable {d : ℕ}

/-- Center and original-gradient scale, followed by radius and output width. -/
abbrev Parameters (d : ℕ) := (Point d × ℝ) × (ℝ × ℝ)

/-- Original supplied Gaussian input and the complete canonical instruction tape. -/
abbrev Seed (d : ℕ) (origin : Origin) :=
  Point d × Tape d (terminalMeanProgram origin)

/-- Actual value and unchanged reference input, together with the full seed. -/
def retained (origin : Origin) (G : Point d → Point d)
    (θ : Parameters d) (pw : Seed d origin) :
    (Point d × Point d) × Seed d origin :=
  (((run (terminalMeanProgram origin) G
    (terminalMeanInputs θ.1.2 θ.2.1 θ.2.2 θ.1.1 pw.1)
    Env.empty pw.2).value, pw.1), pw)

theorem retained_reference (origin : Origin) (G : Point d → Point d)
    (θ : Parameters d) (pw : Seed d origin) :
    (retained origin G θ pw).1.2 = (retained origin G θ pw).2.1 := rfl

theorem measurable_retained (origin : Origin) {G : Point d → Point d}
    (hG : Measurable G) :
    Measurable (fun z : Parameters d × Seed d origin => retained origin G z.1 z.2) := by
  have hv : Measurable (fun z : Parameters d × Seed d origin =>
      (run (terminalMeanProgram origin) G
        (terminalMeanInputs z.1.1.2 z.1.2.1 z.1.2.2 z.1.1.1 z.2.1)
        Env.empty z.2.2).value) := by
    apply ExecutableKernel.measurable_run_value _ hG
    · intro j
      change Measurable (fun z : Parameters d × Seed d origin =>
        if j.val = 0 then z.1.2.1 else if j.val = 1 then z.1.2.2 else z.1.1.2)
      split_ifs <;> fun_prop
    · exact measurable_fst.fst.fst
    · exact measurable_snd.fst
    · intro τ r
      exact nomatch r
    · exact measurable_snd.snd
  exact (hv.prodMk measurable_snd.fst).prodMk measurable_snd

theorem measurable_retained_section (origin : Origin) {G : Point d → Point d}
    (hG : Measurable G) (θ : Parameters d) : Measurable (retained origin G θ) := by
  have hf : Measurable (fun pw : Seed d origin => (θ,pw)) :=
    measurable_const.prodMk measurable_id
  have h := (measurable_retained origin hG).comp hf
  simpa only [Function.comp_def] using h

/-- Jointly measurable deterministic coupling conditional on the full seed. -/
def seedKernel (origin : Origin) (G : Point d → Point d) (hG : Measurable G) :
    Kernel (Parameters d × Seed d origin) ((Point d × Point d) × Seed d origin) :=
  Kernel.deterministic (fun z => retained origin G z.1 z.2) (measurable_retained origin hG)

/-- The genuine standalone law is integrated only after the full seed is retained. -/
def kernel (origin : Origin) (G : Point d → Point d) :
    Kernel (Parameters d) ((Point d × Point d) × Seed d origin) :=
  ((Kernel.id : Kernel (Parameters d) (Parameters d)) ×ₖ
    Kernel.const (Parameters d) (standaloneLaw d (terminalMeanProgram origin))).map
      (fun z => retained origin G z.1 z.2)

theorem kernel_markov (origin : Origin) {G : Point d → Point d} (hG : Measurable G) :
    IsMarkovKernel (kernel origin G) :=
  Kernel.IsMarkovKernel.map _ (measurable_retained origin hG)

theorem kernel_apply (origin : Origin) {G : Point d → Point d}
    (hG : Measurable G) (θ : Parameters d) :
    kernel origin G θ = (standaloneLaw d (terminalMeanProgram origin)).map
      (retained origin G θ) := by
  rw [kernel, Kernel.map_apply _ (measurable_retained origin hG), Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (measurable_retained origin hG) measurable_prodMk_left]
  rfl

/-- Every original seed coordinate is retained with exactly its original law. -/
theorem seed_marginal (origin : Origin) {G : Point d → Point d}
    (hG : Measurable G) (θ : Parameters d) :
    (kernel origin G θ).map Prod.snd = standaloneLaw d (terminalMeanProgram origin) := by
  rw [kernel_apply origin hG, Measure.map_map measurable_snd
    (measurable_retained_section origin hG θ)]
  exact Measure.map_id

/-- The first pair is the literal standalone execution and its original P. -/
theorem actual_marginal (origin : Origin) {G : Point d → Point d}
    (hG : Continuous G) (θ : Parameters d) :
    (kernel origin G θ).map Prod.fst =
      terminalMeanActualLaw origin G θ.1.2 θ.2.1 θ.2.2 θ.1.1 := by
  rw [kernel_apply origin hG.measurable, Measure.map_map measurable_fst
    (measurable_retained_section origin hG.measurable θ)]
  exact terminal_retained_actualLaw hG origin _ _ _ _

/-- The retained reference is exactly P'=P on the full standalone law. -/
theorem reference_marginal (origin : Origin) {G : Point d → Point d}
    (hG : Measurable G) (θ : Parameters d) :
    (kernel origin G θ).map (fun z => (z.2.1, z.1.2)) =
      (stdGaussian (Point d)).map (fun P => (P,P)) := by
  rw [kernel_apply origin hG, Measure.map_map (by fun_prop)
    (measurable_retained_section origin hG θ)]
  exact terminal_retained_reference_diagonal d origin

/-- The exact reference transition is the identity kernel at every parameter. -/
theorem reference_joint_law (origin : Origin) {G : Point d → Point d}
    (hG : Measurable G) (θ : Parameters d) :
    (kernel origin G θ).map (fun z => (z.2.1, z.1.2)) =
      stdGaussian (Point d) ⊗ₘ (Kernel.id : Kernel (Point d) (Point d)) := by
  rw [reference_marginal origin hG θ]
  exact (Measure.compProd_deterministic measurable_id).symm

/-- Equality of the coupling's quadratic cost with the existing terminal
two-Gaussian formula; all structural tape coordinates remain in the coupling. -/
theorem integral_error_eq (origin : Origin) {G : Point d → Point d}
    (hG : Continuous G) (θ : Parameters d) (u : Point d) :
    (∫ z, ‖z.1.1 - (u + θ.2.2 • z.1.2)‖^2 ∂kernel origin G θ) =
      ∫ pz : Point d × Point d,
        ‖(show Point d from
            (terminalMeanRetained origin G θ.1.2 θ.2.1 θ.2.2 θ.1.1 pz.1 pz.2).1.value) -
          (u + θ.2.2 • (terminalMeanRetained origin G θ.1.2 θ.2.1 θ.2.2 θ.1.1
            pz.1 pz.2).2)‖^2 ∂terminalGaussianPairLaw d := by
  let f : Point d × Point d → ℝ := fun v => ‖v.1-(u+θ.2.2 • v.2)‖^2
  have hf : Continuous f := by fun_prop
  have hmap := actual_marginal origin hG θ
  have hleft := integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable
    (μ := kernel origin G θ)
  rw [hmap] at hleft
  rw [hleft.symm]
  unfold terminalMeanActualLaw
  rw [integral_map (measurable_terminalMeanRetained_value hG origin _ _ _ _).aemeasurable
    hf.aestronglyMeasurable]

/-- Finite second moment of the actual scaled-execution error on this same
full-seed coupling. No positive-width or precision guard is needed here. -/
theorem scaled_residual_memLp_two
    {V : Point d → ℝ} {a L : ℝ}
    (hV : ContDiff ℝ 2 V) (hL : 0 ≤ L)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ (scaledPotential V a)) y v v)
    (hup : ∀ y v,
      fderiv ℝ (fderiv ℝ (scaledPotential V a)) y v v ≤ L * ‖v‖ ^ 2)
    (origin : Origin) (r σ : ℝ) (x : Point d) :
    MemLp (fun z => z.1.1-(primitiveMean (scaledPotential V a) x r+σ • z.1.2))
      2 (kernel origin (gradient V) ((x,a),(r,σ))) := by
  have hG : Continuous (gradient V) :=
    (InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp
      (hV.continuous_fderiv (by norm_num))
  let f : Point d × Point d → Point d := fun z =>
    z.1-(primitiveMean (scaledPotential V a) x r+σ • z.2)
  have hf : Continuous f := by fun_prop
  have hbase : MemLp f 2 (terminalMeanActualLaw origin (gradient V) a r σ x) := by
    unfold terminalMeanActualLaw
    apply (memLp_map_measure_iff hf.aestronglyMeasurable
      (measurable_terminalMeanRetained_value hG origin a r σ x).aemeasurable).mpr
    exact terminalMean_scaled_residual_memLp_two hV hL hlo hup origin r σ x
  have hp : MeasurePreserving Prod.fst
      (kernel origin (gradient V) ((x,a),(r,σ)))
      (terminalMeanActualLaw origin (gradient V) a r σ x) :=
    ⟨measurable_fst, actual_marginal origin hG _⟩
  exact hbase.comp_measurePreserving hp

/-- Existing terminal accuracy lifted to the jointly measurable actual-seed
coupling, with precisely the original scalar and curvature guards. -/
theorem scaled_accuracy
    {V : Point d → ℝ} {a L r σ δ q b S : ℝ}
    (hV : ContDiff ℝ 2 V) (hL : 0 ≤ L)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ (scaledPotential V a)) y v v)
    (hup : ∀ y v,
      fderiv ℝ (fderiv ℝ (scaledPotential V a)) y v v ≤ L * ‖v‖ ^ 2)
    (hr : 0 < r) (hr1 : r ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hσ : 0 < σ)
    (hS : 0 ≤ S) (hq : q ≤ 1/2) (hb : 3/4 < b)
    (hsize : (L*r)/σ ≤ S*δ^b) (hsmall : 3*S*δ^((1:ℝ)/4) ≤ 1)
    (origin : Origin) (x : Point d) :
    Real.sqrt (∫ z,
      ‖z.1.1-(primitiveMean (scaledPotential V a) x r+σ • z.1.2)‖^2
        ∂kernel origin (gradient V) ((x,a),(r,σ))) ≤
      σ*δ^q*primitiveScale (scaledPotential V a) x := by
  have hG : Continuous (gradient V) :=
    (InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp
      (hV.continuous_fderiv (by norm_num))
  rw [integral_error_eq origin hG]
  exact terminalMean_scaled_accuracy hV hL hlo hup hr hr1 hδ hδ1 hσ hS hq hb
    hsize hsmall origin x

end AcceleratedLogConcave.Probability.TerminalRetainedCoupling
