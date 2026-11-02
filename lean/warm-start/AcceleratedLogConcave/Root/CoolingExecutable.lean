import AcceleratedLogConcave.Probability.ExecutableKernel
import AcceleratedLogConcave.Probability.MixedResidualRouting
import AcceleratedLogConcave.Oracle.PrivateSamplingTapeProjections

/-! Literal public cooling execution. The outer sampler has tau=1, while
every lower mean call uses the existing source mean constructor, whose private
sampling geometry remains internal. Kernels retain the complete original tape.
The final reserve is its actual syntax occurrence. Its independence from the
entire pre-reserve output and the reference coupling/accuracy remain separate.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace AcceleratedLogConcave.Root.CoolingExecutable
open Oracle Oracle.TapeLowering Oracle.SourceExecutableTables
open Numerics.AffineGraph
open AcceleratedLogConcave.Probability.MixedResidualTape
open scoped BigOperators NNReal

/-- Only public geometry, enumerations, scalar data and finite loop count.
No executable, law, approximation or cost certificate is supplied. -/
structure Setup (m nm na nh ns nc : ℕ) where
  M : MeanGeometry m
  meanNodes : Fin nm ≃ M.MeanNode
  anchors : Fin na ≃ M.Anchor
  seeds : Fin nh ≃ Fin m × M.Kernel
  privateMesh : IntervalMesh 0 (samplingEnd (M.R / backwardEnd M.R))
  privateNodes : Fin ns ≃ privateMesh.Source m
  coolingMesh : IntervalMesh 0 (samplingEnd 1)
  coolingNodes : Fin nc ≃ coolingMesh.Source m
  Ds : ℝ
  δ : ℝ
  t : ℝ
  w : ℝ
  ht : 0 < t
  htq : t ≤ 1/4
  layers : ℕ

variable {m nm na nh ns nc d : ℕ} (P : Setup m nm na nh ns nc)

def outerGeometry : SamplingGeometry m where
  R := P.M.R
  R_pos := P.M.R_pos
  R_le_half := P.M.R_le_half
  τ := 1
  R_le_τ := P.M.R_le_half.trans (by norm_num)
  τ_le_one := le_rfl
  mesh := P.coolingMesh

@[simp] theorem outerGeometry_tau : (outerGeometry P).τ = 1 := rfl

def radius (h : ℝ) (v : ℝ≥0) : ℝ := Real.sqrt ((v : ℝ)/h)

theorem radius_pos {h : ℝ} {v : ℝ≥0} (hh : 0 < h) (hv : 0 < v) :
    0 < radius h v := Real.sqrt_pos.mpr (div_pos hv hh)

/-- The lower source mean retains its prescribed privateGeometry internally. -/
def meanChild (a r σ q : ℝ) : ExecutableData :=
  RecursiveExecutable.mean P.M P.meanNodes P.anchors P.seeds P.Ds P.δ P.t P.w
    P.ht P.htq P.layers P.privateMesh P.privateNodes a r σ q

def main (h : ℝ) (v : ℝ≥0) (K : ℕ) (i : Fin nc) : ExecutableData :=
  meanChild P (Real.sqrt h)
    ((outerGeometry P).radius (radius h v) (P.coolingNodes i))
    (RecursiveMeanPublicTable.mainWidth nc (radius h v) P.M.R P.Ds ((radius h v)^2))
    (K : ℝ)

def final (h : ℝ) (v : ℝ≥0) (K : ℕ) (i : Fin nc) : ExecutableData :=
  meanChild P (Real.sqrt h)
    ((outerGeometry P).radius (radius h v) (P.coolingNodes i))
    (samplingFinalWidth (outerGeometry P) (radius h v)) (K : ℝ)

/-- Literal S_1^K syntax and public table, with the prescribed lower children. -/
def data (h : ℝ) (v : ℝ≥0) (K : ℕ) : ExecutableData :=
  SamplingExecutable.build (outerGeometry P) P.coolingNodes (radius h v) P.Ds
    (main P h v K) (final P h v K) P.layers

abbrev FullTape (d : ℕ) (h : ℝ) (v : ℝ≥0) (K : ℕ) := Tape d (data P h v K).program

def input (h : ℝ) (v : ℝ≥0) (K : ℕ) (x : Point d) : Inputs d (data P h v K).size :=
  ⟨(data P h v K).coefficient, (Real.sqrt h)⁻¹ • x, 0⟩

/-- The original-gradient interpreter result, including its complete trace. -/
def execute (h : ℝ) (v : ℝ≥0) (K : ℕ) (G : Point d → Point d)
    (x : Point d) (ω : FullTape P d h v K) : Result d .point :=
  run (data P h v K).program G (input P h v K x) Env.empty ω

/-- Physical affine decoding of that same literal output. -/
def output (h : ℝ) (v : ℝ≥0) (K : ℕ) (G : Point d → Point d)
    (z : Point d × FullTape P d h v K) : Point d :=
  z.1 + (Real.sqrt (v : ℝ)/2) • (show Point d from (execute P h v K G z.1 z.2).value)

theorem execute_value_measurable (h : ℝ) (v : ℝ≥0) (K : ℕ)
    {G : Point d → Point d} (hG : Measurable G) :
    Measurable (fun z : Point d × FullTape P d h v K =>
      (show Point d from (execute P h v K G z.1 z.2).value)) := by
  unfold execute
  apply Probability.ExecutableKernel.measurable_run_value _ hG
    (input := fun z : Point d × FullTape P d h v K => input P h v K z.1)
    (env := fun _ => Env.empty) (tape := Prod.snd)
  · intro j
    exact measurable_const
  · change Measurable (fun z : Point d × FullTape P d h v K => (Real.sqrt h)⁻¹ • z.1)
    exact measurable_fst.const_smul ((Real.sqrt h)⁻¹)
  · exact measurable_const
  · intro τ r
    exact nomatch r
  · exact measurable_snd

theorem output_measurable (h : ℝ) (v : ℝ≥0) (K : ℕ)
    {G : Point d → Point d} (hG : Measurable G) : Measurable (output P h v K G) := by
  have ho := (execute_value_measurable P h v K hG).const_smul (Real.sqrt (v : ℝ)/2)
  have he : ((fun z : Point d × FullTape P d h v K => z.1) +
      (Real.sqrt (v : ℝ)/2) • (fun z => (show Point d from (execute P h v K G z.1 z.2).value))) =
      output P h v K G := by funext z; rfl
  rw [← he]
  exact measurable_fst.add ho

theorem retained_section_measurable (h : ℝ) (v : ℝ≥0) (K : ℕ)
    {G : Point d → Point d} (hG : Measurable G) (x : Point d) :
    Measurable (fun ω : FullTape P d h v K => (output P h v K G (x,ω),ω)) := by
  have hf : Measurable (fun ω : FullTape P d h v K => (x,ω)) :=
    measurable_const.prodMk measurable_id
  exact ((output_measurable P h v K hG).comp hf).prodMk measurable_id

/-- Actual physical output and complete unmodified instruction tape. -/
def retainedKernel (h : ℝ) (v : ℝ≥0) (K : ℕ) (G : Point d → Point d) :
    Kernel (Point d) (Point d × FullTape P d h v K) :=
  ((Kernel.id : Kernel (Point d) (Point d)) ×ₖ
    Kernel.const (Point d) (tapeLaw d (data P h v K).program)).map
      (fun z => (output P h v K G z,z.2))

theorem retainedKernel_markov (h : ℝ) (v : ℝ≥0) (K : ℕ)
    {G : Point d → Point d} (hG : Measurable G) :
    IsMarkovKernel (retainedKernel P h v K G) :=
  Kernel.IsMarkovKernel.map _ ((output_measurable P h v K hG).prodMk measurable_snd)

/-- The public returned kernel is produced by the literal cooling program. -/
def kernel (h : ℝ) (v : ℝ≥0) (K : ℕ) (G : Point d → Point d) :
    Kernel (Point d) (Point d) := (retainedKernel P h v K G).fst

theorem kernel_markov (h : ℝ) (v : ℝ≥0) (K : ℕ)
    {G : Point d → Point d} (hG : Measurable G) : IsMarkovKernel (kernel P h v K G) := by
  have := retainedKernel_markov P h v K hG
  unfold kernel
  infer_instance

theorem retainedKernel_apply (h : ℝ) (v : ℝ≥0) (K : ℕ)
    {G : Point d → Point d} (hG : Measurable G) (x : Point d) :
    retainedKernel P h v K G x = (tapeLaw d (data P h v K).program).map
      (fun ω => (output P h v K G (x,ω),ω)) := by
  have hm := (output_measurable P h v K hG).prodMk measurable_snd
  rw [retainedKernel, Kernel.map_apply _ hm, Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map hm measurable_prodMk_left]
  rfl

theorem kernel_apply (h : ℝ) (v : ℝ≥0) (K : ℕ)
    {G : Point d → Point d} (hG : Measurable G) (x : Point d) :
    kernel P h v K G x = (tapeLaw d (data P h v K).program).map
      (fun ω => output P h v K G (x,ω)) := by
  rw [kernel, Kernel.fst_apply, retainedKernel_apply P h v K hG]
  rw [Measure.map_map measurable_fst
    (retained_section_measurable P h v K hG x)]
  rfl

/-- Retaining the output loses no source seed coordinate or source-law mass. -/
theorem tape_marginal (h : ℝ) (v : ℝ≥0) (K : ℕ)
    {G : Point d → Point d} (hG : Measurable G) (x : Point d) :
    (retainedKernel P h v K G x).map Prod.snd = tapeLaw d (data P h v K).program := by
  rw [retainedKernel_apply P h v K hG, Measure.map_map measurable_snd
    (retained_section_measurable P h v K hG x)]
  exact Measure.map_id

/-- Arbitrary entering laws keep their correlations and the complete tape. -/
theorem retained_compProd (h : ℝ) (v : ℝ≥0) (K : ℕ)
    {G : Point d → Point d} (hG : Measurable G) (ν : Measure (Point d)) [SFinite ν] :
    ν ⊗ₘ retainedKernel P h v K G =
      (ν.prod (tapeLaw d (data P h v K).program)).map
        (fun z => (z.1,(output P h v K G z,z.2))) := by
  have := retainedKernel_markov P h v K hG
  have hm : Measurable (fun z : Point d × FullTape P d h v K =>
      (z.1,(output P h v K G z,z.2))) :=
    measurable_fst.prodMk ((output_measurable P h v K hG).prodMk measurable_snd)
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_compProd hf, lintegral_map hf hm]
  have hp := lintegral_prod (fun z : Point d × FullTape P d h v K =>
    f (z.1,(output P h v K G z,z.2))) (hf.comp hm).aemeasurable
    (μ := ν) (ν := tapeLaw d (data P h v K).program)
  rw [hp]
  apply lintegral_congr
  intro x
  rw [retainedKernel_apply P h v K hG]
  exact lintegral_map (hf.comp measurable_prodMk_left)
    (retained_section_measurable P h v K hG x)

/-- Specialization to the only permitted original-potential oracle. -/
def originalGradientKernel (h : ℝ) (v : ℝ≥0) (K : ℕ) (V : Point d → ℝ) :
    Kernel (Point d) (Point d) := kernel P h v K (gradient V)

theorem originalGradientKernel_markov (h : ℝ) (v : ℝ≥0) (K : ℕ)
    (V : Point d → ℝ) (hV : ContDiff ℝ 2 V) :
    IsMarkovKernel (originalGradientKernel P h v K V) := by
  apply kernel_markov
  exact ((InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp
    (hV.continuous_fderiv (by norm_num))).measurable

/-- Exact original-gradient queries for every input and every complete tape. -/
theorem executed_queries (h : ℝ) (v : ℝ≥0) (K : ℕ) (G : Point d → Point d)
    (x : Point d) (ω : FullTape P d h v K) :
    (traceCounts (execute P h v K G x ω).trace).queries =
      P.layers*(∑ i, syntaxCount .gradient (main P h v K i).program)+
        ∑ i, syntaxCount .gradient (final P h v K i).program := by
  rw [execute, run_counts]
  exact SamplingExecutable.queries_build (outerGeometry P) P.coolingNodes
    (radius h v) P.Ds (main P h v K) (final P h v K) P.layers

def config (h : ℝ) (v : ℝ≥0) (K : ℕ) :=
  samplingConfig (main P h v K) (final P h v K) P.layers

/-- The actual final reserve occurrence, never a newly chosen Gaussian. -/
def reserve (h : ℝ) (v : ℝ≥0) (K : ℕ) (ω : FullTape P d h v K) : Point d :=
  PrivateSamplingTapeProjections.coordinates (config P h v K) ω (.inr (.inr (.inr ())))

theorem reserve_measurable (h : ℝ) (v : ℝ≥0) (K : ℕ) :
    Measurable (reserve P h v K (d := d)) := by
  change Measurable (fun ω : FullTape P d h v K =>
    (splitTape (data P h v K).program ω).1
      (PrivateSamplingTapeProjections.slot (config P h v K) (.inr (.inr (.inr ())))))
  exact (measurable_pi_apply _).comp (measurable_splitTape d (data P h v K).program).fst

/-- The selected reserve has its true Gaussian marginal under the complete
instruction law. This alone is not independence from preReserve. -/
theorem reserve_preserving (h : ℝ) (v : ℝ≥0) (K : ℕ) :
    MeasurePreserving (reserve P h v K (d := d))
      (tapeLaw d (data P h v K).program) (stdGaussian (Point d)) := by
  let s := PrivateSamplingTapeProjections.slot (config P h v K) (.inr (.inr (.inr ())))
  have hp := (measurePreserving_eval
    (fun _ : GaussianSlot (data P h v K).program => stdGaussian (Point d)) s).comp
      (measurePreserving_fst (μ := Measure.pi
        (fun _ : GaussianSlot (data P h v K).program => stdGaussian (Point d)))
        (ν := residualLaw (data P h v K).program))
  exact hp.comp (splitTape_preserving d (data P h v K).program)

theorem reserve_coefficient (h : ℝ) (v : ℝ≥0) (K : ℕ) (x : Point d) :
    (input P h v K x).coefficient (config P h v K).reserve = 1/2 := by
  change samplingTable (outerGeometry P) P.coolingNodes (radius h v) P.Ds
    (main P h v K) (final P h v K)
    (scalarSlot _ _ (Fin.natAdd _ (Fin.natAdd _ (3 : Fin 4)))) = _
  simp [samplingScalarTable, outerGeometry]

/-- Literal final row before its final reserve, using actual final child runs
and the actual residual occurrence after the full main loop. -/
def preReserve (h : ℝ) (v : ℝ≥0) (K : ℕ) (G : Point d → Point d)
    (x : Point d) (ω : FullTape P d h v K) : Point d :=
  let cfg := config P h v K
  let inp := input P h v K x
  let z := PrivateSamplingTapeProjections.coordinates cfg ω
  inp.coefficient cfg.invEnd • z (.inl ()) +
    (∑ i, inp.coefficient (cfg.rowWeight i) •
      PrivateSamplingTapeProjections.finalValue cfg G inp ω i) +
    inp.coefficient cfg.beta • z (.inr (.inr (.inl ())))

theorem execute_value_eq_preReserve_add_reserve (h : ℝ) (v : ℝ≥0) (K : ℕ)
    (G : Point d → Point d) (x : Point d) (ω : FullTape P d h v K) :
    (show Point d from (execute P h v K G x ω).value) =
      preReserve P h v K G x ω + (1/2 : ℝ) • reserve P h v K ω := by
  have ho := PrivateSamplingTapeProjections.run_code_value (config P h v K) G
    (input P h v K x) ω
  rw [reserve_coefficient P h v K x] at ho
  exact ho.trans (by dsimp only [preReserve, reserve]; abel)

theorem preReserve_measurable (h : ℝ) (v : ℝ≥0) (K : ℕ)
    {G : Point d → Point d} (hG : Measurable G) :
    Measurable (fun z : Point d × FullTape P d h v K => preReserve P h v K G z.1 z.2) := by
  have he : (fun z : Point d × FullTape P d h v K => preReserve P h v K G z.1 z.2) =
      fun z => (show Point d from (execute P h v K G z.1 z.2).value) -
        (1/2 : ℝ) • reserve P h v K z.2 := by
    funext z
    rw [execute_value_eq_preReserve_add_reserve]
    abel
  rw [he]
  have he' : ((fun z : Point d × FullTape P d h v K =>
      (show Point d from (execute P h v K G z.1 z.2).value)) -
      (1/2 : ℝ) • (reserve P h v K ∘ Prod.snd)) =
      (fun z : Point d × FullTape P d h v K =>
        (show Point d from (execute P h v K G z.1 z.2).value) -
          (1/2 : ℝ) • reserve P h v K z.2) := by funext z; rfl
  rw [← he']
  exact (execute_value_measurable P h v K hG).sub
    (((reserve_measurable P h v K).comp measurable_snd).const_smul (1/2 : ℝ))

theorem output_eq_decode_actual_reserve (h : ℝ) (v : ℝ≥0) (K : ℕ)
    (G : Point d → Point d) (x : Point d) (ω : FullTape P d h v K) :
    output P h v K G (x,ω) = x+(Real.sqrt (v : ℝ)/2) •
      (preReserve P h v K G x ω+(1/2 : ℝ) • reserve P h v K ω) := by
  unfold output
  rw [execute_value_eq_preReserve_add_reserve]

/-- Actual pre-reserve kernel. No equality with the exact posterior law is
assumed, and no reference-output coupling is an input of this definition. -/
def preKernel (h : ℝ) (v : ℝ≥0) (K : ℕ) (G : Point d → Point d) :
    Kernel (Point d) (Point d) :=
  ((Kernel.id : Kernel (Point d) (Point d)) ×ₖ
    Kernel.const (Point d) (tapeLaw d (data P h v K).program)).map
      (fun z => preReserve P h v K G z.1 z.2)

theorem preKernel_markov (h : ℝ) (v : ℝ≥0) (K : ℕ)
    {G : Point d → Point d} (hG : Measurable G) :
    IsMarkovKernel (preKernel P h v K G) :=
  Kernel.IsMarkovKernel.map _ (preReserve_measurable P h v K hG)

/- Remaining probability seam: prove that the actual tape pushforward by
  omega |-> (preReserve P h v K G x omega, reserve P h v K omega)
is (preKernel P h v K G x).prod (stdGaussian (Point d)), for every x.
The deterministic reserve decomposition above does not establish this joint
law. That law would identify kernel with reservedDecoder preKernel v. The
exact-pre-reserve coupling and its averaged energy bound remain further work. -/

end AcceleratedLogConcave.Root.CoolingExecutable
