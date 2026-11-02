import AcceleratedLogConcave.Numerics.SourceOriginalOutput
import AcceleratedLogConcave.Numerics.SmoothInitialError

/-! Original-data L² budgets for the literal mean graph. All analytic
regularity is supplied by the existing original-data smooth receiver. The
raw graph, reference and terminal score use its unchanged common seed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped BigOperators
namespace AcceleratedLogConcave.Oracle.MeanOriginalBounds
open Numerics Numerics.MeanFlowLp Numerics.MeanResidualBridge Numerics.MeanCollocationLp
open Numerics.AffineGraph Numerics.AffineGraph.MeanGeometry
variable {D m : ℕ} (d : MeanFlowLp.Data (Fin D) m)

/-- The actual maximum of the seven explicit source row payments. -/
def residualBudget (h₀ : ℝ) : ℝ :=
  MeanCollocationLp.residualBudget d h₀ (SmoothQuantitativeAssembly.budget d)

/-- A paid bound on the actual direct-vector distance, from its one-step
defect and original position/score/noise moments. -/
def initializerBudget (h₀ : ℝ) : ℝ :=
  2*(rowMass d h₀*(d.ell*directBudget d+meanBudget d)+residualBudget d h₀)

/-- The full center quadrature payment; its factor two is retained. -/
def quadratureBudget : ℝ :=
  2*(SmoothQuantitativeAssembly.budget d).center/(m.factorial:ℝ)

def initializerError (i : d.G.MeanNode) (ω : Seed d) : Point D :=
  rawIterate d 0 i ω-rawReference d i ω

/-- Literal final mean row evaluated on the original-data reference nodes. -/
def referenceOutput (ω : Seed d) : Point D :=
  d.G.meanOutput d.sigma ω.1.snd
    ((rawGraph d ω).collect (Gibbs.primitiveMean d.F) (fun i=>rawReference d i ω))

def referenceOutputLp : H d :=
  d.G.meanOutput d.sigma (initialScore d)
    ((lpGraph d).collect (operator d) (reference d))

def quadratureError (ω : Seed d) : Point D :=
  referenceOutput d ω-rawTerminalTarget d ω

 theorem residualBudget_nonneg (h₀ : ℝ) : 0≤residualBudget d h₀ := norm_nonneg _

 theorem quadratureBudget_nonneg : 0≤quadratureBudget d := by
  unfold quadratureBudget SmoothQuantitativeAssembly.budget
  exact div_nonneg (mul_nonneg (by norm_num) (centerSourceBudget_nonneg d _ _ _ _ _))
    (Nat.cast_nonneg _)

 theorem initializer_memLp (i : d.G.MeanNode) :
    MemLp (initializerError d i) 2 (seedMeasure d) := raw_error_memLp d 0 i

 theorem initializer_norm_le (h₀ : ℝ) (hmesh : MeshConditions d h₀)
    (hhalf : contraction d h₀≤1/2) (i : d.G.MeanNode) :
    ‖(initializer_memLp d i).toLp (initializerError d i)‖≤ initializerBudget d h₀ := by
  unfold initializerError
  rw [AffineResidual.toLp_eq_of_ae _ (raw_error_ae d 0 i)]
  have hb := SmoothInitialError.initialError_le_of_half d h₀ hmesh
    _ _ (SmoothQuantitativeAssembly.left_margin d) (SmoothQuantitativeAssembly.right_margin d)
    (SmoothQuantitativeAssembly.budget d)
    (SourceOriginalOutput.original_regularity d (by have := hmesh.order; omega)) hhalf
  exact (norm_le_pi_norm (iterate d 0-reference d) i).trans hb

 theorem initializerBudget_nonneg (h₀ : ℝ) (hmesh : MeshConditions d h₀)
    (hhalf : contraction d h₀≤1/2) : 0≤ initializerBudget d h₀ := by
  have hb := SmoothInitialError.initialError_le_of_half d h₀ hmesh
    _ _ (SmoothQuantitativeAssembly.left_margin d) (SmoothQuantitativeAssembly.right_margin d)
    (SmoothQuantitativeAssembly.budget d)
    (SourceOriginalOutput.original_regularity d (by have := hmesh.order; omega)) hhalf
  exact (norm_nonneg _).trans hb

 theorem residual_memLp (i : d.G.MeanNode) :
    MemLp (rawResidual d i) 2 (seedMeasure d) :=
  rawResidual_memLp d (operator d) (primitiveLp_spec _ _) i

 theorem residual_norm_le (h₀ : ℝ) (hmesh : MeshConditions d h₀) (i : d.G.MeanNode) :
    ‖(residual_memLp d i).toLp (rawResidual d i)‖≤residualBudget d h₀ := by
  rw [AffineResidual.toLp_eq_of_ae _ (rawResidual_ae_lp d (operator d) (primitiveLp_spec _ _) i)]
  exact MeanSmoothCollocationLp.residual_bound d h₀ hmesh _ _
    (SmoothQuantitativeAssembly.left_margin d) (SmoothQuantitativeAssembly.right_margin d)
    (SmoothQuantitativeAssembly.budget d)
    (SourceOriginalOutput.original_regularity d (by have := hmesh.order; omega)) i

 theorem referenceOutput_ae : referenceOutput d =ᵐ[seedMeasure d]
    (referenceOutputLp d : Seed d → Point D) := by
  unfold referenceOutputLp
  let Q : d.G.MeanNode → H d := fun j=>operator d (reference d j) (d.G.radius d.r j)
  have hq : ∀ᵐ ω ∂seedMeasure d,∀ j,Q j ω=Gibbs.primitiveMean d.F (d.x+reference d j ω) (d.G.radius d.r j) :=
    ae_all_iff.mpr fun j=>primitiveLp_ae (primitiveData d) (seedMeasure d)
      (d.G.radius_pos d.r d.hr j) (reference d j)
  have hi : ∀ᵐ ω ∂seedMeasure d,∀ i,rawReference d i ω=d.x+reference d i ω := by
    filter_upwards [ae_all_iff.mpr (MeanResidualBridge.rawReference_ae d)] with ω hω
    intro i
    exact hω i
  have hg := (seed_score_memLp d).coeFn_toLp
  have hs := AffineResidual.coeFn_weighted_sum d.G.outputWeight Q
  have hm := Lp.coeFn_smul (d.sigma/2) (initialScore d)
  have ha := Lp.coeFn_add ((d.sigma/2) • initialScore d) (∑ j,d.G.outputWeight j • Q j)
  have ho : d.G.meanOutput d.sigma (initialScore d)
      ((lpGraph d).collect (operator d) (reference d)) =
      (d.sigma/2) • initialScore d+∑ j,d.G.outputWeight j • Q j := by
    rw [d.G.meanOutput_eq_weighted_sum]
    rfl
  rw [ho]
  filter_upwards [hq,hi,hg,hs,hm,ha] with ω hq hi hg hs hm ha
  change initialScore d ω=ω.1.snd at hg
  rw [ha]
  simp only [Pi.add_apply,hm,Pi.smul_apply,hg,hs,hq,referenceOutput,d.G.meanOutput_eq_weighted_sum,
    FiniteGraph.collect,FiniteGraph.requests,MeanCollocationLp.rawGraph,MeanGeometry.graph,hi]

 theorem quadratureError_ae : quadratureError d =ᵐ[seedMeasure d]
    ((referenceOutputLp d-terminalTarget d : H d) : Seed d → Point D) := by
  filter_upwards [referenceOutput_ae d,rawTerminalTarget_ae d,
    Lp.coeFn_sub (referenceOutputLp d) (terminalTarget d)] with ω ho ht hs
  simp only [quadratureError,ho,ht,hs,Pi.sub_apply]

 theorem quadrature_memLp : MemLp (quadratureError d) 2 (seedMeasure d) :=
  (Lp.memLp _).ae_eq (quadratureError_ae d).symm

 theorem quadrature_norm_le (hm : 2≤m) :
    ‖(quadrature_memLp d).toLp (quadratureError d)‖≤quadratureBudget d := by
  rw [AffineResidual.toLp_eq_of_ae _ (quadratureError_ae d)]
  exact MeanSmoothCollocationLp.reference_output_bound d hm _ _ (SmoothQuantitativeAssembly.budget d)
    (SourceOriginalOutput.original_regularity d (by omega))

end AcceleratedLogConcave.Oracle.MeanOriginalBounds
