import AcceleratedLogConcave.Root.ClockPublicSetupTapeLaw
import AcceleratedLogConcave.Kinetic.Mixing.SourceInvariance
noncomputable section
open MeasureTheory Set
namespace AcceleratedLogConcave.Root.ClockUniformDraw

def clockOfUniform (u : Oracle.UniformValue) : ClockLaw.Clock :=
  ⟨(u : ℝ) / 2, by rcases u.property with ⟨h0, h1⟩; constructor <;> linarith⟩

theorem measurable_clockOfUniform : Measurable clockOfUniform := by
  apply Measurable.subtype_mk
  exact measurable_subtype_coe.div_const 2

theorem sourceClockLaw_map_coe :
    Kinetic.sourceClockLaw.map ((↑) : ClockLaw.Clock → ℝ) =
      Kinetic.clockLaw (1/2) := by
  unfold Kinetic.sourceClockLaw Kinetic.boundedClockLaw
  rw [Measure.map_map measurable_subtype_coe
    (Kinetic.clockTime_continuous (1/2) (by norm_num)).measurable]
  have heq : (fun x : ℝ => ((Kinetic.clockTime (1/2) (by norm_num) x : ClockLaw.Clock) : ℝ))
      =ᵐ[Kinetic.clockLaw (1/2)] (fun x => x) := by
    unfold Kinetic.clockLaw
    apply Measure.ae_smul_measure _ _
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact Kinetic.clockTime_eq (1/2) (by norm_num) x ⟨le_of_lt hx.1, hx.2⟩
  change Measure.map (fun x : ℝ => ((Kinetic.clockTime (1/2) (by norm_num) x : ClockLaw.Clock) : ℝ)) (Kinetic.clockLaw (1/2)) = _
  rw [Measure.map_congr heq]
  simp


theorem uniformScaled_map_coe :
    (volume : Measure Oracle.UniformValue).map (fun u : Oracle.UniformValue => (u : ℝ) / 2) =
      Kinetic.clockLaw (1/2) := by
  have hmap : (volume : Measure Oracle.UniformValue).map (fun u : Oracle.UniformValue => (u : ℝ) / 2) =
      ((volume : Measure ℝ).restrict (Icc (0:ℝ) 1)).map (fun x : ℝ => x / 2) := by
    rw [← MeasurableSet.map_coe_volume (s := Icc (0:ℝ) 1) measurableSet_Icc]
    have hf : Measurable (fun x : ℝ => x / 2) := measurable_id.div_const 2
    rw [Measure.map_map hf measurable_subtype_coe]
    rfl
  rw [hmap]
  have hpre : (fun x : ℝ => x / 2) ⁻¹' Icc (0:ℝ) (1/2) = Icc 0 1 := by
    ext x
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro hx <;> constructor <;> nlinarith [hx.1, hx.2]
  have hf : Measurable (fun x : ℝ => x / 2) := measurable_id.div_const 2
  rw [← hpre, ← Measure.restrict_map hf measurableSet_Icc]
  have hvol : Measure.map (fun x : ℝ => x / 2) volume =
      (ENNReal.ofReal 2) • volume := by
    have hf_eq : (fun x : ℝ => x / 2) = (fun x : ℝ => (1/2:ℝ) * x) := by
      funext x; ring
    rw [hf_eq, Real.map_volume_mul_left (a := (1/2:ℝ)) (by norm_num)]
    norm_num
  rw [hvol]
  change ((ENNReal.ofReal 2) • volume).restrict (Icc (0:ℝ) (1/2)) =
    Kinetic.clockLaw (1/2)
  rw [Kinetic.clockLaw, restrict_Ioc_eq_restrict_Icc]
  have hn : (ENNReal.ofReal (1/2:ℝ))⁻¹ = (2:ENNReal) := by
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num : 0 < (1/2:ℝ))]
    norm_num
  rw [hn]
  norm_num


/-- The literal uniform primitive, scaled by one half, has exactly the source
clock measure on its bounded interval. -/
theorem map_uniform_clock :
    (volume : Measure Oracle.UniformValue).map clockOfUniform =
      Kinetic.sourceClockLaw := by
  apply (MeasurableEmbedding.subtype_coe (s := Icc (0:ℝ) (1/2)) measurableSet_Icc).map_injective
  calc
    ((volume : Measure Oracle.UniformValue).map clockOfUniform).map
        ((↑) : ClockLaw.Clock → ℝ) =
      (volume : Measure Oracle.UniformValue).map
        (fun u : Oracle.UniformValue => (u : ℝ) / 2) := by
          rw [Measure.map_map measurable_subtype_coe measurable_clockOfUniform]
          rfl
    _ = Kinetic.clockLaw (1/2) := uniformScaled_map_coe
    _ = Kinetic.sourceClockLaw.map ((↑) : ClockLaw.Clock → ℝ) := sourceClockLaw_map_coe.symm

theorem standardLaws_clock (d : ℕ) :
    (ClockPublicSetupTapeLaw.standardLaws d).uniformDraw.map clockOfUniform =
      Kinetic.sourceClockLaw := by
  exact map_uniform_clock

end AcceleratedLogConcave.Root.ClockUniformDraw
