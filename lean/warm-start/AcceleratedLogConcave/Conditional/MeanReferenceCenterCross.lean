import AcceleratedLogConcave.Conditional.MeanReferenceVariance

noncomputable section
open MeasureTheory ProbabilityTheory AcceleratedLogConcave
open Numerics Numerics.MeanFlowLp Conditional Conditional.MeanReferenceLayer
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Conditional.MeanReferenceVariance
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

lemma integral_comp_preserving {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {f : A → B} (hf : MeasurePreserving f μ ν)
    {g : B → ℝ} (hg : StronglyMeasurable g) :
    (∫ a, g (f a) ∂μ) = ∫ b, g b ∂ν := by
  rw [← integral_map hf.aemeasurable hg.aestronglyMeasurable, hf.map_eq]

def baseIncrement (d : Data ι m) (b : BaseState ι) : E :=
  MeanBenchmarkCoupling.endpoint d 1 b.1.1 b.1.2 - b.1.2

lemma continuous_baseIncrement (d : Data ι m) : Continuous (baseIncrement d) := by
  unfold baseIncrement MeanBenchmarkCoupling.endpoint
  have hc := CenteringFlowLp.continuous_phase (kernelData d) (d.sigma/2) (half_pos d.hsigma)
  fun_prop

lemma center_eq_base (d : Data ι m) (c : Children d) (z : Execution ι m) :
    centerIncrement d c z = baseIncrement d (splitState d c z.1).1 := rfl

lemma integral_base_mul_gaussian (d : Data ι m) (v : E) (i : Fin m) :
    (∫ z : BaseState ι × (Fin m → E),
      ⟪v, baseIncrement d z.1⟫ * ⟪v, z.2 i⟫
      ∂(MeanReferenceLayer.baseLaw d).prod (Measure.pi (fun _ : Fin m => stdGaussian E))) = 0 := by
  rw [integral_prod_mul (fun b : BaseState ι => ⟪v, baseIncrement d b⟫)
    (fun p : Fin m → E => ⟪v, p i⟫)]
  have he := integral_comp_preserving
    (measurePreserving_eval (fun _ : Fin m => stdGaussian E) i)
    (g := fun x : E => ⟪v, x⟫) (by fun_prop)
  rw [he]
  have hz : (∫ x : E, ⟪v, x⟫ ∂stdGaussian E) = 0 := by
    rw [integral_inner (𝕜 := ℝ) IsGaussian.integrable_fun_id v, integral_id_stdGaussian]
    simp
  rw [hz, mul_zero]

lemma center_child_output_cross (d : Data ι m) (c : Children d) (v : E) (i : Fin m) :
    (∫ z : Execution ι m, ⟪v, centerIncrement d c z⟫ * ⟪v, z.2 i⟫
      ∂averagedJoint d c) = 0 := by
  have hp : MeasurePreserving
      (fun z : Execution ι m => ((splitState d c z.1).1, z.2))
      (averagedJoint d c) ((MeanReferenceLayer.baseLaw d).prod (Measure.pi (fun _ : Fin m => stdGaussian E))) :=
    ⟨(((measurable_splitState d c).comp measurable_fst).fst.prodMk measurable_snd),
      updated_split_law d c⟩
  have hm : StronglyMeasurable (fun z : BaseState ι × (Fin m → E) =>
      ⟪v, baseIncrement d z.1⟫ * ⟪v, z.2 i⟫) := by
    have hc := continuous_baseIncrement d
    fun_prop
  exact (integral_comp_preserving hp hm).trans (integral_base_mul_gaussian d v i)

lemma center_child_input_cross (d : Data ι m) (c : Children d) (v : E) (i : Fin m) :
    (∫ z : Execution ι m, ⟪v, centerIncrement d c z⟫ * ⟪v, active d c z.1 (some i)⟫
      ∂averagedJoint d c) = 0 := by
  have hp : MeasurePreserving (splitState d c) ((stdGaussian E).prod (freshLaw d))
      ((MeanReferenceLayer.baseLaw d).prod (Measure.pi (fun _ : Fin m => stdGaussian E))) :=
    ⟨measurable_splitState d c, splitState_law d c⟩
  have hm : StronglyMeasurable (fun z : BaseState ι × (Fin m → E) =>
      ⟪v, baseIncrement d z.1⟫ * ⟪v, z.2 i⟫) := by
    have hc := continuous_baseIncrement d
    fun_prop
  exact (integral_comp_preserving (hp.comp (host_preserving d c)) hm).trans
    (integral_base_mul_gaussian d v i)

lemma center_child_cross (d : Data ι m) (c : Children d) (v : E) (i : Fin m) :
    (∫ z, ⟪v, centerIncrement d c z⟫ * ⟪v, childIncrement d c i z⟫
      ∂averagedJoint d c) = 0 := by
  have hc := (momentTarget d c).1.const_inner (𝕜 := ℝ) v
  have hin : MemLp (fun z : Execution ι m => ⟪v, active d c z.1 (some i)⟫) 2
      (averagedJoint d c) :=
    (IsGaussian.memLp_two_id.comp_measurePreserving (active_preserving d c (some i))).const_inner v
  have hout : MemLp (fun z : Execution ι m => ⟪v, z.2 i⟫) 2 (averagedJoint d c) :=
    (IsGaussian.memLp_two_id.comp_measurePreserving
      ((measurePreserving_eval (fun _ : Option (Option (Fin m)) => stdGaussian E)
        (some (some i))).comp (outputCoordinates_preserving d c))).const_inner v
  simp_rw [childIncrement, inner_sub_right, mul_sub]
  calc
    _ = (∫ z, ⟪v, centerIncrement d c z⟫ * ⟪v, z.2 i⟫ ∂averagedJoint d c) -
        (∫ z, ⟪v, centerIncrement d c z⟫ * ⟪v, active d c z.1 (some i)⟫ ∂averagedJoint d c) :=
      integral_sub (hc.integrable_mul hout) (hc.integrable_mul hin)
    _ = 0 := by rw [center_child_output_cross, center_child_input_cross, sub_self]
end AcceleratedLogConcave.Conditional.MeanReferenceVariance
