import AcceleratedLogConcave.Oracle.Work
import AcceleratedLogConcave.Gibbs.PrimitiveMoments
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Counted terminal mean with the designated input retained

The terminal branch of `sources/warm-start.tex` (lines 2578–2582) is implemented
by closed finite instructions. The scalar adapter lowers the score of
`V(a • ·)` to one original-gradient call, at `a • (x + r • Z)`.
The reference momentum is the very same supplied input. Execution and counts
hold for every tape, zero coefficients, and dimension zero.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ContDiff ENNReal

namespace AcceleratedLogConcave.Oracle

/-- Local inputs are existing references; only the draw and gradient emit events. -/
def terminalMeanBody (origin : Origin)
    (x P : Ref Γ .point) (r σ a : Ref Γ .scalar) : Prog c Γ .point :=
  .step origin .gaussian <|
  .step origin (.pure (.smul (.there r) .here)) <|
  .step origin (.pure (.vadd (.there (.there x)) .here)) <|
  .step origin (.pure (.smul (.there (.there (.there a))) .here)) <|
  .step origin (.grad .here) <|
  .step origin (.pure (.smul (.there (.there (.there (.there (.there a))))) .here)) <|
  .step origin (.pure (.smul (.there (.there (.there (.there (.there (.there σ))))))
    (.there (.there (.there (.there (.there (.there P)))))))) <|
  .step origin (.pure (.vadd (.there .here) .here)) <|
  .ret .here

/-- An externally admissible root with public scalar slots `r, σ, a`. -/
def terminalMeanProgram (origin : Origin) : Program 3 .point :=
  .step origin .center <|
  .step origin .momentum <|
  .step origin (.pure (.publicScalar 0)) <|
  .step origin (.pure (.publicScalar 1)) <|
  .step origin (.pure (.publicScalar 2)) <|
  terminalMeanBody origin (.there (.there (.there (.there .here))))
    (.there (.there (.there .here))) (.there (.there .here)) (.there .here) .here

/-- The momentum is supplied, with no additional random draw. -/
def terminalMeanInputs (a r σ : ℝ) (x P : Point d) : Inputs d 3 where
  coefficient j := if j.val = 0 then r else if j.val = 1 then σ else a
  center := x
  momentum := P

/-- All body-tape factors except the one auxiliary point are units. -/
def terminalMeanBodyTapeEquiv (d : ℕ) (origin : Origin)
    (x P : Ref Γ .point) (r σ a : Ref Γ .scalar) :
    Point d ≃ Tape d (terminalMeanBody (c := c) origin x P r σ a) where
  toFun Z := ⟨Z, PUnit.unit, PUnit.unit, PUnit.unit, PUnit.unit,
    PUnit.unit, PUnit.unit, PUnit.unit, PUnit.unit⟩
  invFun tape := tape.1
  left_inv _ := rfl
  right_inv tape := by
    rcases tape with ⟨Z, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩
    rfl

/-- This equivalence covers every typed root tape, not just Gaussian samples. -/
def terminalMeanTapeEquiv (d : ℕ) (origin : Origin) :
    Point d ≃ Tape d (terminalMeanProgram origin) where
  toFun Z := ⟨PUnit.unit, PUnit.unit, PUnit.unit, PUnit.unit, PUnit.unit,
    terminalMeanBodyTapeEquiv d origin _ _ _ _ _ Z⟩
  invFun tape := tape.2.2.2.2.2.1
  left_inv _ := rfl
  right_inv tape := by
    rcases tape with ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩, tape⟩
    congr 1

/-- The actual interpreter, with its exact one-block tape encoding. -/
def terminalMeanRun (origin : Origin)
    (G : Point d → Point d) (a r σ : ℝ) (x P Z : Point d) : Result d .point :=
  run (terminalMeanProgram origin) G (terminalMeanInputs a r σ x P)
    Env.empty (terminalMeanTapeEquiv d origin Z)

/-- Keep the actual execution result and the unchanged reference input. -/
def terminalMeanRetained (origin : Origin)
    (G : Point d → Point d) (a r σ : ℝ) (x P Z : Point d) :
    Result d .point × Point d :=
  (terminalMeanRun origin G a r σ x P Z, P)

theorem terminalMeanBody_value (origin : Origin)
    (x P : Ref Γ .point) (r σ a : Ref Γ .scalar)
    (G : Point d → Point d) (i : Inputs d c) (ρ : Env d Γ)
    (tape : Tape d (terminalMeanBody origin x P r σ a)) :
    let A : ℝ := ρ a
    let R : ℝ := ρ r
    let S : ℝ := ρ σ
    let X : Point d := ρ x
    let PM : Point d := ρ P
    let Z : Point d := (terminalMeanBodyTapeEquiv d origin x P r σ a).symm tape
    (run (terminalMeanBody origin x P r σ a) G i ρ tape).value =
      A • G (A • (X + R • Z)) + S • PM := rfl

theorem terminalMeanBody_trace (origin : Origin)
    (x P : Ref Γ .point) (r σ a : Ref Γ .scalar)
    (G : Point d → Point d) (i : Inputs d c) (ρ : Env d Γ)
    (tape : Tape d (terminalMeanBody origin x P r σ a)) :
    let A : ℝ := ρ a
    let R : ℝ := ρ r
    let X : Point d := ρ x
    let Z : Point d := (terminalMeanBodyTapeEquiv d origin x P r σ a).symm tape
    (run (terminalMeanBody origin x P r σ a) G i ρ tape).trace =
      [Event.gaussian origin, Event.gradient origin (A • (X + R • Z))
        (G (A • (X + R • Z)))] := rfl

theorem terminalMeanRun_value (origin : Origin)
    (G : Point d → Point d) (a r σ : ℝ) (x P Z : Point d) :
    (terminalMeanRun origin G a r σ x P Z).value =
      a • G (a • (x + r • Z)) + σ • P := rfl

theorem terminalMeanRun_trace (origin : Origin)
    (G : Point d → Point d) (a r σ : ℝ) (x P Z : Point d) :
    (terminalMeanRun origin G a r σ x P Z).trace =
      [Event.gaussian origin,
        Event.gradient origin (a • (x + r • Z)) (G (a • (x + r • Z)))] := rfl

@[simp] theorem terminalMeanRetained_input (origin : Origin)
    (G : Point d → Point d) (a r σ : ℝ) (x P Z : Point d) :
    (terminalMeanRetained origin G a r σ x P Z).2 = P := rfl

theorem terminalMeanRetained_residual (origin : Origin)
    (G : Point d → Point d) (a r σ : ℝ) (x P Z u : Point d) :
    (show Point d from (terminalMeanRetained origin G a r σ x P Z).1.value) -
      (u + σ • (terminalMeanRetained origin G a r σ x P Z).2) =
        a • G (a • (x + r • Z)) - u := by
  change (show Point d from (terminalMeanRun origin G a r σ x P Z).value) - (u + σ • P) = _
  rw [terminalMeanRun_value]
  exact add_sub_add_right_eq_sub _ _ _

@[simp] theorem terminalMeanBody_counts (origin : Origin)
    (x P : Ref Γ .point) (r σ a : Ref Γ .scalar) :
    syntaxCounts (terminalMeanBody (c := c) origin x P r σ a) = ⟨1, 1, 0⟩ := rfl

@[simp] theorem terminalMeanProgram_counts (origin : Origin) :
    syntaxCounts (terminalMeanProgram origin) = ⟨1, 1, 0⟩ := rfl

theorem terminalMeanProgram_run_counts (origin : Origin)
    (G : Point d → Point d) (i : Inputs d 3)
    (tape : Tape d (terminalMeanProgram origin)) :
    traceCounts (run (terminalMeanProgram origin) G i Env.empty tape).trace =
      ⟨1, 1, 0⟩ := by
  rw [run_counts, terminalMeanProgram_counts]

@[simp] theorem terminalMeanProgram_queryCount (origin : Origin) :
    queryCount (terminalMeanProgram origin) = 1 := rfl

@[simp] theorem terminalMeanProgram_tapeShape (origin : Origin) :
    tapeShape (terminalMeanProgram origin) = ⟨1, 0⟩ := rfl

@[simp] theorem terminalMeanProgram_bookkeepingWork (origin : Origin) :
    bookkeepingWork (terminalMeanProgram origin) = 2 := rfl

/-- The concrete source potential after the public linear scale adapter. -/
def scaledPotential (V : Point d → ℝ) (a : ℝ) : Point d → ℝ :=
  fun w => V (a • w)

/-- The adapter uses the original gradient at the physically scaled query. -/
theorem gradient_scaled_potential {V : Point d → ℝ}
    (hV : ContDiff ℝ 1 V) (a : ℝ) (z : Point d) :
    gradient (scaledPotential V a) z = a • gradient V (a • z) := by
  have hh := ((hV.differentiable (by norm_num)) (a • z)).hasFDerivAt.comp z
    ((hasFDerivAt_id z).const_smul a)
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, real_inner_smul_left, inner_gradient_left]
  rw [show fderiv ℝ (scaledPotential V a) z = _ from hh.fderiv]
  simp

/-- Continuity is proved for the actual run value, without a topology on tapes. -/
theorem continuous_terminalMeanRun_value {G : Point d → Point d}
    (hG : Continuous G) (origin : Origin) (a r σ : ℝ) (x : Point d) :
    Continuous (fun pz : Point d × Point d =>
      (show Point d from (terminalMeanRun origin G a r σ x pz.1 pz.2).value)) := by
  simp_rw [terminalMeanRun_value]
  fun_prop

/-- Independent designated momentum and auxiliary Gaussian block, in that order. -/
def terminalGaussianPairLaw (d : ℕ) : Measure (Point d × Point d) :=
  (stdGaussian (Point d)).prod (stdGaussian (Point d))

instance : IsProbabilityMeasure (terminalGaussianPairLaw d) := by
  unfold terminalGaussianPairLaw
  infer_instance

theorem map_fst_terminalGaussianPairLaw :
    (terminalGaussianPairLaw d).map Prod.fst = stdGaussian (Point d) :=
  measurePreserving_fst.map_eq

/-- Both momentum slots use the very same designated Gaussian input. -/
theorem terminalMean_retained_diagonal :
    (terminalGaussianPairLaw d).map (fun pz => (pz.1, pz.1)) =
      (stdGaussian (Point d)).map (fun p => (p, p)) := by
  rw [← map_fst_terminalGaussianPairLaw, Measure.map_map (by fun_prop) measurable_fst]
  rfl

/-- The reference transition is literally the identity kernel. -/
theorem terminalMean_identityKernel_preserves :
    (Kernel.id : Kernel (Point d) (Point d)) ∘ₘ stdGaussian (Point d) =
      stdGaussian (Point d) := Measure.id_comp

/-- Actual retained execution law; the first slot is the interpreter's value. -/
def terminalMeanActualLaw (origin : Origin) (G : Point d → Point d)
    (a r σ : ℝ) (x : Point d) : Measure (Point d × Point d) :=
  (terminalGaussianPairLaw d).map (fun pz =>
    ((show Point d from (terminalMeanRetained origin G a r σ x pz.1 pz.2).1.value),
      (terminalMeanRetained origin G a r σ x pz.1 pz.2).2))

/-- The affine reference, retaining exactly the designated momentum. -/
def terminalMeanReferenceLaw (u : Point d) (σ : ℝ) : Measure (Point d × Point d) :=
  (stdGaussian (Point d)).map (fun p => (u + σ • p, p))

/-- A joint realization of the actual run and its affine reference. -/
def terminalMeanCoupling (origin : Origin) (G : Point d → Point d)
    (a r σ : ℝ) (x u : Point d) :
    Measure ((Point d × Point d) × (Point d × Point d)) :=
  (terminalGaussianPairLaw d).map (fun pz =>
    (((show Point d from (terminalMeanRetained origin G a r σ x pz.1 pz.2).1.value),
      (terminalMeanRetained origin G a r σ x pz.1 pz.2).2), (u + σ • pz.1, pz.1)))

theorem measurable_terminalMeanRetained_value {G : Point d → Point d}
    (hG : Continuous G) (origin : Origin) (a r σ : ℝ) (x : Point d) :
    Measurable (fun pz : Point d × Point d =>
      ((show Point d from (terminalMeanRetained origin G a r σ x pz.1 pz.2).1.value),
        (terminalMeanRetained origin G a r σ x pz.1 pz.2).2)) :=
  (continuous_terminalMeanRun_value hG origin a r σ x).measurable.prodMk measurable_fst

theorem measurable_terminalMeanCoupling_map {G : Point d → Point d}
    (hG : Continuous G) (origin : Origin) (a r σ : ℝ) (x u : Point d) :
    Measurable (fun pz : Point d × Point d =>
      (((show Point d from (terminalMeanRetained origin G a r σ x pz.1 pz.2).1.value),
        (terminalMeanRetained origin G a r σ x pz.1 pz.2).2),
        (u + σ • pz.1, pz.1))) :=
  (measurable_terminalMeanRetained_value hG origin a r σ x).prodMk (by fun_prop)

theorem isProbabilityMeasure_terminalMeanActualLaw {G : Point d → Point d}
    (hG : Continuous G) (origin : Origin) (a r σ : ℝ) (x : Point d) :
    IsProbabilityMeasure (terminalMeanActualLaw origin G a r σ x) := by
  unfold terminalMeanActualLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_terminalMeanRetained_value hG origin a r σ x).aemeasurable).mpr inferInstance

instance (u : Point d) (σ : ℝ) : IsProbabilityMeasure (terminalMeanReferenceLaw u σ) := by
  unfold terminalMeanReferenceLaw
  infer_instance

theorem isProbabilityMeasure_terminalMeanCoupling {G : Point d → Point d}
    (hG : Continuous G) (origin : Origin) (a r σ : ℝ) (x u : Point d) :
    IsProbabilityMeasure (terminalMeanCoupling origin G a r σ x u) := by
  unfold terminalMeanCoupling
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_terminalMeanCoupling_map hG origin a r σ x u).aemeasurable).mpr inferInstance

/-- First coupling marginal is exactly the actual retained execution law. -/
theorem map_fst_terminalMeanCoupling {G : Point d → Point d}
    (hG : Continuous G) (origin : Origin) (a r σ : ℝ) (x u : Point d) :
    (terminalMeanCoupling origin G a r σ x u).map Prod.fst =
      terminalMeanActualLaw origin G a r σ x := by
  unfold terminalMeanCoupling terminalMeanActualLaw
  rw [Measure.map_map measurable_fst
    (measurable_terminalMeanCoupling_map hG origin a r σ x u)]
  rfl

/-- Second marginal is the reference law with that same momentum retained. -/
theorem map_snd_terminalMeanCoupling {G : Point d → Point d}
    (hG : Continuous G) (origin : Origin) (a r σ : ℝ) (x u : Point d) :
    (terminalMeanCoupling origin G a r σ x u).map Prod.snd =
      terminalMeanReferenceLaw u σ := by
  unfold terminalMeanCoupling terminalMeanReferenceLaw
  rw [Measure.map_map measurable_snd
    (measurable_terminalMeanCoupling_map hG origin a r σ x u)]
  rw [← map_fst_terminalGaussianPairLaw, Measure.map_map (by fun_prop) measurable_fst]
  rfl

/-- The actual retained momentum has its original Gaussian distribution. -/
theorem map_snd_terminalMeanActualLaw {G : Point d → Point d}
    (hG : Continuous G) (origin : Origin) (a r σ : ℝ) (x : Point d) :
    (terminalMeanActualLaw origin G a r σ x).map Prod.snd = stdGaussian (Point d) := by
  unfold terminalMeanActualLaw
  rw [Measure.map_map measurable_snd
    (measurable_terminalMeanRetained_value hG origin a r σ x)]
  exact map_fst_terminalGaussianPairLaw



/-- The scalar source certificate absorbs the terminal factor three. -/
theorem terminal_coefficient_le
    {δ q b S L σ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hσ : 0 < σ)
    (hS : 0 ≤ S) (hq : q ≤ 1 / 2) (hb : 3 / 4 < b)
    (hsize : L / σ ≤ S * δ ^ b)
    (hsmall : 3 * S * δ ^ (1 / 4 : ℝ) ≤ 1) :
    3 * L ≤ σ * δ ^ q := by
  have hexp : (1 / 4 : ℝ) ≤ b - q := by linarith
  have hp := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hexp
  have hsmall' : 3 * S * δ ^ (b - q) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hp (by positivity)).trans hsmall
  have hsplit : δ ^ b = δ ^ (b - q) * δ ^ q := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have hbudget : 3 * (S * δ ^ b) ≤ δ ^ q := by
    calc
      3 * (S * δ ^ b) = δ ^ q * (3 * S * δ ^ (b - q)) := by rw [hsplit]; ring
      _ ≤ δ ^ q * 1 := mul_le_mul_of_nonneg_left hsmall'
        (Real.rpow_pos_of_pos hδ q).le
      _ = δ ^ q := mul_one _
  have hsize' := (div_le_iff₀ hσ).mp hsize
  have hbudget' := mul_le_mul_of_nonneg_right hbudget hσ.le
  nlinarith



open AcceleratedLogConcave.Gibbs

/-- The executed residual has a finite second moment for arbitrary real coefficients. -/
theorem terminalMean_residual_memLp_two
    {F : Point d → ℝ} {L : ℝ}
    (hF : ContDiff ℝ 2 F) (hL : 0 ≤ L)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ F) y v v)
    (hup : ∀ y v, fderiv ℝ (fderiv ℝ F) y v v ≤ L * ‖v‖ ^ 2)
    (origin : Origin) (r σ : ℝ) (x : Point d) :
    MemLp (fun pz : Point d × Point d =>
      (show Point d from (terminalMeanRetained origin (gradient F) 1 r σ x pz.1 pz.2).1.value) -
        (primitiveMean F x r + σ •
          (terminalMeanRetained origin (gradient F) 1 r σ x pz.1 pz.2).2))
      2 ((stdGaussian (Point d)).prod (stdGaussian (Point d))) := by
  simp_rw [terminalMeanRetained_residual, one_smul]
  exact (primitive_gaussian_score_error_memLp_two hF hL hlo hup x r).comp_measurePreserving
    measurePreserving_snd

/-- Actual retained-run RMS error under the same independent designated inputs. -/
theorem terminalMean_retained_rms_error_le
    {F : Point d → ℝ} {L r : ℝ}
    (hF : ContDiff ℝ 2 F) (hL : 0 ≤ L)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ F) y v v)
    (hup : ∀ y v, fderiv ℝ (fderiv ℝ F) y v v ≤ L * ‖v‖ ^ 2)
    (hr : 0 < r) (hr1 : r ≤ 1) (origin : Origin) (σ : ℝ) (x : Point d) :
    Real.sqrt (∫ pz : Point d × Point d,
      ‖(show Point d from (terminalMeanRetained origin (gradient F) 1 r σ x pz.1 pz.2).1.value) -
        (primitiveMean F x r + σ •
          (terminalMeanRetained origin (gradient F) 1 r σ x pz.1 pz.2).2)‖ ^ 2
      ∂((stdGaussian (Point d)).prod (stdGaussian (Point d)))) ≤
      3 * (L * r) * primitiveScale F x := by
  simp_rw [terminalMeanRetained_residual, one_smul]
  rw [integral_fun_snd (fun z : Point d => ‖gradient F (x + r • z) - primitiveMean F x r‖ ^ 2),
    probReal_univ, one_smul]
  exact primitive_gaussian_score_rms_error_le hF hL hlo hup hr hr1 x

/-- The manuscript's terminal accuracy, measured on the actual counted execution. -/
theorem terminalMean_accuracy
    {F : Point d → ℝ} {L r σ δ q b S : ℝ}
    (hF : ContDiff ℝ 2 F) (hL : 0 ≤ L)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ F) y v v)
    (hup : ∀ y v, fderiv ℝ (fderiv ℝ F) y v v ≤ L * ‖v‖ ^ 2)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hσ : 0 < σ)
    (hS : 0 ≤ S) (hq : q ≤ 1 / 2) (hb : 3 / 4 < b)
    (hsize : (L * r) / σ ≤ S * δ ^ b)
    (hsmall : 3 * S * δ ^ (1 / 4 : ℝ) ≤ 1)
    (origin : Origin) (x : Point d) :
    Real.sqrt (∫ pz : Point d × Point d,
      ‖(show Point d from (terminalMeanRetained origin (gradient F) 1 r σ x pz.1 pz.2).1.value) -
        (primitiveMean F x r + σ •
          (terminalMeanRetained origin (gradient F) 1 r σ x pz.1 pz.2).2)‖ ^ 2
      ∂((stdGaussian (Point d)).prod (stdGaussian (Point d)))) ≤
      σ * δ ^ q * primitiveScale F x := by
  exact (terminalMean_retained_rms_error_le hF hL hlo hup hr hr1 origin σ x).trans
    (mul_le_mul_of_nonneg_right (terminal_coefficient_le hδ hδ1 hσ hS hq hb hsize hsmall)
      (primitiveScale_nonneg F x))

/-- The scaled original-gradient run has the literal scaled-potential value.
Only values are compared: the physical query and unscaled reply in the trace differ. -/
theorem terminalMean_scaled_value {V : Point d → ℝ}
    (hV : ContDiff ℝ 1 V) (origin : Origin) (a r σ : ℝ) (x P Z : Point d) :
    (terminalMeanRun origin (gradient V) a r σ x P Z).value =
      (terminalMeanRun origin (gradient (scaledPotential V a)) 1 r σ x P Z).value := by
  simp only [terminalMeanRun_value, one_smul, gradient_scaled_potential hV]
  rfl

/-- Finite second moment for the residual of the original-gradient scaled execution. -/
theorem terminalMean_scaled_residual_memLp_two
    {V : Point d → ℝ} {a L : ℝ}
    (hV : ContDiff ℝ 2 V) (hL : 0 ≤ L)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ (scaledPotential V a)) y v v)
    (hup : ∀ y v,
      fderiv ℝ (fderiv ℝ (scaledPotential V a)) y v v ≤ L * ‖v‖ ^ 2)
    (origin : Origin) (r σ : ℝ) (x : Point d) :
    MemLp (fun pz : Point d × Point d =>
      (show Point d from (terminalMeanRetained origin (gradient V) a r σ x pz.1 pz.2).1.value) -
        (primitiveMean (scaledPotential V a) x r + σ •
          (terminalMeanRetained origin (gradient V) a r σ x pz.1 pz.2).2))
      2 ((stdGaussian (Point d)).prod (stdGaussian (Point d))) := by
  have hF : ContDiff ℝ 2 (scaledPotential V a) :=
    hV.comp (contDiff_id.const_smul a)
  have h := terminalMean_residual_memLp_two hF hL hlo hup origin r σ x
  simpa only [terminalMeanRetained, terminalMean_scaled_value (hV.of_le (by norm_num)),
    Prod.fst, Prod.snd] using h

/-- Source accuracy with one query to the original gradient, at the physically scaled point. -/
theorem terminalMean_scaled_accuracy
    {V : Point d → ℝ} {a L r σ δ q b S : ℝ}
    (hV : ContDiff ℝ 2 V) (hL : 0 ≤ L)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ (scaledPotential V a)) y v v)
    (hup : ∀ y v,
      fderiv ℝ (fderiv ℝ (scaledPotential V a)) y v v ≤ L * ‖v‖ ^ 2)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hσ : 0 < σ)
    (hS : 0 ≤ S) (hq : q ≤ 1 / 2) (hb : 3 / 4 < b)
    (hsize : (L * r) / σ ≤ S * δ ^ b)
    (hsmall : 3 * S * δ ^ (1 / 4 : ℝ) ≤ 1)
    (origin : Origin) (x : Point d) :
    Real.sqrt (∫ pz : Point d × Point d,
      ‖(show Point d from (terminalMeanRetained origin (gradient V) a r σ x pz.1 pz.2).1.value) -
        (primitiveMean (scaledPotential V a) x r + σ •
          (terminalMeanRetained origin (gradient V) a r σ x pz.1 pz.2).2)‖ ^ 2
      ∂((stdGaussian (Point d)).prod (stdGaussian (Point d)))) ≤
      σ * δ ^ q * primitiveScale (scaledPotential V a) x := by
  have hF : ContDiff ℝ 2 (scaledPotential V a) :=
    hV.comp (contDiff_id.const_smul a)
  have h := terminalMean_accuracy hF hL hlo hup hr hr1 hδ hδ1 hσ hS hq hb hsize hsmall origin x
  simpa only [terminalMeanRetained, terminalMean_scaled_value (hV.of_le (by norm_num)),
    Prod.fst, Prod.snd] using h

end AcceleratedLogConcave.Oracle
