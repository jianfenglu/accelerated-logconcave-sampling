import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.Identification

/-! The actual compact visible-phase heat core. Momentum is retained as a
parameter, and only position is convolved. Joint continuity, uniform boundedness
and retained compact momentum support are proved from the original compact test. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson AcceleratedLogConcave.HeatCalculus
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

omit [Fintype ι] in
/-- A compact joint test has compact position slices with a common support. -/
theorem phase_position_slice_compact {f : E×E → ℝ} (hc : HasCompactSupport f) (p : E) :
    HasCompactSupport (fun x => f (x,p)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hc.image continuous_fst)
  intro x hx
  exact ⟨(x,p), subset_tsupport _ hx, rfl⟩

theorem phase_position_slice_C2 {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (p : E) :
    ContDiff ℝ 2 (fun x => f (x,p)) := hf.comp (contDiff_id.prodMk contDiff_const)

/-- The literal signed heat quotient, convolving position and retaining momentum. -/
def compactPhaseHeatQuotient {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (f : E×E → ℝ) (t : ℝ) (z : E×E) : ℝ :=
  compactHeatQuotient F (fun x => f (x,z.2)) t z.1

/-- The numerator is jointly continuous in time, position and retained momentum. -/
theorem compactPhaseHeatNumerator_continuous {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Continuous (fun z : ℝ×(E×E) => compactHeatNumerator F (fun x => f (x,z.2.2)) z.1 z.2.1) := by
  have hp := (reference_density_C2 F a ⟨le_rfl,F.ordered⟩).continuous
  have hh : Continuous (fun z : E×E => f z * F.density a z.1) := hf.mul (hp.comp continuous_fst)
  have hhc : HasCompactSupport (fun z : E×E => f z * F.density a z.1) := hc.mul_right
  obtain ⟨C,hC⟩ := hhc.exists_bound_of_continuous hh
  unfold compactHeatNumerator heatAverage
  apply continuous_of_dominated (bound := fun _ : E => C)
  · intro z
    exact (by fun_prop : Continuous (fun g : E =>
      f (z.2.1 + Real.sqrt (z.1-a) • g,z.2.2) * F.density a (z.2.1 + Real.sqrt (z.1-a) • g))).aestronglyMeasurable
  · intro z
    exact Eventually.of_forall fun g => hC _
  · exact integrable_const C
  · filter_upwards [] with g
    fun_prop

/-- The phase quotient is jointly continuous on the actual source interval. -/
theorem compactPhaseHeatQuotient_continuousOn {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    ContinuousOn (fun z : ℝ×(E×E) => compactPhaseHeatQuotient F f z.1 z.2)
      (Icc a b ×ˢ univ) := by
  have hp : ContinuousOn (fun z : ℝ×(E×E) => F.density z.1 z.2.1) (Icc a b ×ˢ univ) :=
    F.density_continuous.comp
      (show ContinuousOn (fun z : ℝ×(E×E) => (z.1,z.2.1)) (Icc a b ×ˢ univ) from
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousOn)
      (fun z hz => ⟨hz.1, mem_univ _⟩)
  exact (compactPhaseHeatNumerator_continuous F hf hc).continuousOn.div hp
    (fun z hz => (reference_density_pos F z.1 hz.1 z.2.1).ne')

theorem compactPhaseHeatQuotient_continuous {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (t : ℝ) (ht : t ∈ Icc a b) : Continuous (compactPhaseHeatQuotient F f t) :=
  (compactPhaseHeatQuotient_continuousOn F hf hc).comp_continuous
    (continuous_const.prodMk continuous_id) (fun z => ⟨ht, mem_univ z⟩)

/-- The same initial supremum controls every momentum slice and every time. -/
theorem compactPhaseHeatQuotient_norm_le {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {C : ℝ}
    (hC : ∀ z, ‖f z‖ ≤ C) (t : ℝ) (ht : t ∈ Icc a b)
    (hheat : F.law t = heatedLaw (F.law a) (t-a)) (z : E×E) :
    ‖compactPhaseHeatQuotient F f t z‖ ≤ C :=
  compactHeatQuotient_norm_le_of_norm_le F (phase_position_slice_C2 hf z.2)
    (phase_position_slice_compact hc z.2) (fun x => hC (x,z.2)) t ht hheat z.1

/-- Momentum support is retained exactly; smoothing occurs only in position. -/
theorem compactPhaseHeatQuotient_retained_support {a b : ℝ}
    (F : ReferencePoissonFamily E a b) {f : E×E → ℝ} (t : ℝ) (x p : E)
    (hp : p ∉ Prod.snd '' tsupport f) : compactPhaseHeatQuotient F f t (x,p) = 0 := by
  have hf0 (y : E) : f (y,p) = 0 := by
    by_contra hn
    exact hp ⟨(y,p), subset_tsupport _ hn, rfl⟩
  simp [compactPhaseHeatQuotient, compactHeatQuotient, compactHeatNumerator, heatAverage, hf0]

/-- The genuine phase core obeys the relative-density PDE in each position fiber. -/
theorem compactPhaseHeatQuotient_classical_heat {a b : ℝ}
    (F : ReferencePoissonFamily E a b) {f : E×E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (t : ℝ) (ht : t ∈ Ioo a b) (hscale : F.scale t = -(1/2:ℝ)) (x p : E) :
    HasDerivAt (fun s => compactPhaseHeatQuotient F f s (x,p))
      ((1/2:ℝ)*compactTestLaplacian (fun y => compactPhaseHeatQuotient F f t (y,p)) x -
        inner ℝ (gradient (F.potential t) x)
          (gradient (fun y => compactPhaseHeatQuotient F f t (y,p)) x)) t :=
  compactHeatQuotient_classical_heat F (phase_position_slice_C2 hf p)
    (phase_position_slice_compact hc p) t ht hscale x

end AcceleratedLogConcave.Kinetic.Reheating
