import AcceleratedLogConcave.Numerics.MeanResidualBridge
import AcceleratedLogConcave.Numerics.AffineBounds
import AcceleratedLogConcave.Numerics.Collocation
/-! Literal common-seed finite mean collocation with derived actual row and residual suppliers. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory AcceleratedLogConcave
open Numerics Numerics.MeanFlowLp Numerics.MeanResidualBridge Numerics.AffineGraph
open Numerics.AffineGraph.MeanGeometry
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Numerics.MeanCollocationLp
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

def operator (d : Data ι m) : H d → ℝ → H d := primitiveLp (primitiveData d) (seedMeasure d)
def lpGraph (d : Data ι m) : FiniteGraph d.G.MeanNode (H d) :=
  d.G.graph d.r d.sigma 0 (initialPosition d) (initialScore d) (initialNoise d)
def rawGraph (d : Data ι m) (ω : Seed d) : FiniteGraph d.G.MeanNode E :=
  d.G.graph d.r d.sigma d.x ω.1.fst ω.1.snd ω.2
def reference (d : Data ι m) : d.G.MeanNode → H d := (curves d).reference d.G 0 d.r
def iterate (d : Data ι m) (N : ℕ) : d.G.MeanNode → H d := (lpGraph d).iterate (operator d) N
def rawIterate (d : Data ι m) (N : ℕ) (i : d.G.MeanNode) (ω : Seed d) : E :=
  (rawGraph d ω).iterate (Gibbs.primitiveMean d.F) N i
def output (d : Data ι m) (N : ℕ) : H d :=
  d.G.meanOutput d.sigma (initialScore d) ((lpGraph d).collect (operator d) (iterate d N))
def rawOutput (d : Data ι m) (N : ℕ) (ω : Seed d) : E :=
  d.G.meanOutput d.sigma ω.1.snd
    ((rawGraph d ω).collect (Gibbs.primitiveMean d.F) (fun i=>rawIterate d N i ω))
def terminalTarget (d : Data ι m) : H d := offsetLp d+(d.sigma/2) • scoreLp d 1
def rawTerminalTarget (d : Data ι m) (ω : Seed d) : E :=
  Gibbs.primitiveMean d.F d.x d.r+(d.sigma/2) • score d 1 ω

def rowMass (d : Data ι m) (h₀ : ℝ) : ℝ :=
  256*(m:ℝ)^5*d.r/(d.sigma*d.G.psi*h₀)+4*d.r^2
def contraction (d : Data ι m) (h₀ : ℝ) : ℝ := d.ell*rowMass d h₀
def initialError (d : Data ι m) : ℝ := ‖(lpGraph d).direct-reference d‖
def residualBudget (d : Data ι m) (h₀ : ℝ) (D : AffineResidual.Mean.DerivativeBudget d.G) : ℝ :=
  ‖D.rowError d.G d.r d.sigma h₀‖
def finiteError (d : Data ι m) (h₀ : ℝ) (D : AffineResidual.Mean.DerivativeBudget d.G) (N : ℕ) : ℝ :=
  contraction d h₀^N*initialError d+residualBudget d h₀ D*∑ j∈Finset.range N,contraction d h₀^j

structure MeshConditions (d : Data ι m) (h₀ : ℝ) : Prop where
  order : 2≤m
  psi_upper : d.G.psi≤1
  step_pos : 0<h₀
  step_upper : h₀≤1/2
  backward : d.G.backward=actualKernelInterval d.G.R h₀ d.G.R_pos d.G.R_le_half step_pos

/-- Derive both actual matrix mass and the right-endpoint-square cell inequality. -/
def MeshTarget (d : Data ι m) (h₀ : ℝ) : Prop := MeshConditions d h₀ →
  0≤contraction d h₀ ∧
  (∀ i,∑ j,|d.G.matrix d.r d.sigma i j|≤rowMass d h₀) ∧
  (∀ c,d.G.backward.length c≤2*h₀*(1-(d.G.backward.right c)^2))

/-- Initializer is literally the direct vector; every finite iterate uses the same seed. -/
def RawIterationTarget (d : Data ι m) : Prop :=
  (∀ N i,rawIterate d N i=ᵐ[seedMeasure d] (fun ω=>d.x+iterate d N i ω)) ∧
  (∀ N i,MemLp (rawIterate d N i) 2 (seedMeasure d)) ∧
  (∀ N,rawOutput d N=ᵐ[seedMeasure d] (output d N : Seed d → E)) ∧
  (∀ N,MemLp (rawOutput d N) 2 (seedMeasure d)) ∧
  rawTerminalTarget d=ᵐ[seedMeasure d] (terminalTarget d : Seed d → E)

/-- The row bound and primitive Lipschitz supplier are conclusions of earlier actual constructions. -/
def ContractionTarget (d : Data ι m) (h₀ : ℝ) : Prop := MeshConditions d h₀ →
  ∀ X Y : d.G.MeanNode → H d,∀ i,
    ‖(lpGraph d).step (operator d) X i-(lpGraph d).step (operator d) Y i‖≤
      contraction d h₀*‖X-Y‖

def Regularity (d : Data ι m) (K : Fin m → ℝ → H d) (l v : ℝ)
    (D : AffineResidual.Mean.DerivativeBudget d.G) : Prop :=
  KernelAgreement d K ∧ l<0 ∧ backwardEnd d.G.R<v ∧
    AffineResidual.Mean.Regularity d.G (curvesWithKernel d K) (operator d) 0 d.r l v D

/-- No row residual is assumed; the explicit replacement regularity supplies it. -/
def ResidualTarget (d : Data ι m) (h₀ : ℝ) : Prop := MeshConditions d h₀ →
  ∀ K l v D,Regularity d K l v D →
  ∀ i,‖(lpGraph d).step (operator d) (reference d) i-reference d i‖≤residualBudget d h₀ D

/-- Maximum is outside the L² norms. No quantitative estimate for the actual initial error is inferred. -/
def FiniteIterationTarget (d : Data ι m) (h₀ : ℝ) : Prop := MeshConditions d h₀ →
  ∀ K l v D,Regularity d K l v D →∀ N,
    ‖iterate d N-reference d‖≤finiteError d h₀ D N ∧
    (∀ i,∃ he : MemLp (fun ω=>rawIterate d N i ω-rawReference d i ω) 2 (seedMeasure d),
      ‖he.toLp (fun ω=>rawIterate d N i ω-rawReference d i ω)‖≤finiteError d h₀ D N) ∧
    (contraction d h₀<1 → ‖iterate d N-reference d‖≤
      contraction d h₀^N*initialError d+residualBudget d h₀ D/(1-contraction d h₀))

/-- Literal final mean row compared with the actual stationary-score benchmark, without a law claim. -/
def FinalOutputTarget (d : Data ι m) (h₀ : ℝ) : Prop := MeshConditions d h₀ →
  ∀ K l v D,Regularity d K l v D →∀ N,
    ‖output d N-terminalTarget d‖≤d.ell*finiteError d h₀ D N+2*D.center/(m.factorial:ℝ) ∧
    ∃ he : MemLp (fun ω=>rawOutput d N ω-rawTerminalTarget d ω) 2 (seedMeasure d),
      ‖he.toLp (fun ω=>rawOutput d N ω-rawTerminalTarget d ω)‖≤
        d.ell*finiteError d h₀ D N+2*D.center/(m.factorial:ℝ)


section Mesh
omit [DecidableEq ι]
variable (d : Data ι m) (h₀ : ℝ) (h : MeshConditions d h₀)
include h

theorem rowMass_nonneg : 0≤rowMass d h₀ := by
  have hr:=d.hr
  have hs:=d.hsigma
  have hp:=d.G.psi_pos
  have hh:=h.step_pos
  unfold rowMass
  positivity

theorem contraction_nonneg : 0≤contraction d h₀ :=
  mul_nonneg d.hell (rowMass_nonneg d h₀ h)

theorem actual_row_bound (i : d.G.MeanNode) :
    ∑ j,|d.G.matrix d.r d.sigma i j|≤rowMass d h₀ :=
  d.G.sum_abs_matrix_le_actual h.order d.r d.sigma d.hr.le d.hsigma h.psi_upper
    h₀ h.step_pos h.step_upper h.backward i

omit h in
private theorem actual_cell_bound {R h₀ : ℝ} (hR : 0<R) (hRu : R≤1/2)
    (hh : 0<h₀) (hhu : h₀≤1/2) (c : (actualKernelInterval R h₀ hR hRu hh).Cell) :
    (actualKernelInterval R h₀ hR hRu hh).length c≤
      2*h₀*(1-((actualKernelInterval R h₀ hR hRu hh).right c)^2) := by
  have hb : 0<Real.sqrt (1-R^2) := Real.sqrt_pos.mpr (by nlinarith)
  have hb1 : Real.sqrt (1-R^2)<1 := by
    apply (Real.sqrt_lt' (by norm_num : (0:ℝ)<1)).mpr
    nlinarith
  have hc := GeometricMesh.cellCount_pos hb hb1 hh
  let c' : Fin (GeometricMesh.cellCount 0 (Real.sqrt (1-R^2)) h₀) :=
    ⟨c.val,by have hi:=c.isLt;change c.val<GeometricMesh.cellCount 0 (Real.sqrt (1-R^2)) h₀-1+1 at hi;omega⟩
  exact GeometricMesh.cellLength_le_two_mul_one_sub_right_sq le_rfl hb hb1 hh hhu c'

theorem cell_bound (c : d.G.backward.Cell) :
    d.G.backward.length c≤2*h₀*(1-(d.G.backward.right c)^2) := by
  have ha : ∀ M : IntervalMesh 0 (backwardEnd d.G.R),
      M=actualKernelInterval d.G.R h₀ d.G.R_pos d.G.R_le_half h.step_pos →
      ∀ c:M.Cell,M.length c≤2*h₀*(1-(M.right c)^2) := by
    intro M he
    subst M
    exact actual_cell_bound d.G.R_pos d.G.R_le_half h.step_pos h.step_upper
  exact ha d.G.backward h.backward c
end Mesh

omit [DecidableEq ι] in
theorem mesh_target (d : Data ι m) (h₀ : ℝ) : MeshTarget d h₀ :=
  fun h=>⟨contraction_nonneg d h₀ h,actual_row_bound d h₀ h,cell_bound d h₀ h⟩

theorem contraction_target (d : Data ι m) (h₀ : ℝ) : ContractionTarget d h₀ := by
  intro h X Y i
  exact FiniteGraph.norm_step_sub_le (lpGraph d) (operator d) ⟨d.ell,d.hell⟩
    (actual_row_bound d h₀ h)
    (fun j=>primitiveLp_lipschitz (primitiveData d) (seedMeasure d) (d.G.radius_pos d.r d.hr j)) X Y i


section Raw
variable (d : Data ι m)

private theorem direct_ae (i : d.G.MeanNode) :
    (fun ω : Seed d=>(rawGraph d ω).direct i)=ᵐ[seedMeasure d]
      (fun ω=>d.x+(lpGraph d).direct i ω) := by
  let V : d.G.Anchor → H d := d.G.anchorValues (initialPosition d) (initialScore d) (initialNoise d)
  have hy := (seed_position_memLp d).coeFn_toLp
  have hg := (seed_score_memLp d).coeFn_toLp
  have hz : ∀ᵐ ω ∂seedMeasure d,∀ j k,initialNoise d j k ω=ω.2 j k :=
    ae_all_iff.mpr fun j=>ae_all_iff.mpr fun k=>(seed_noise_memLp d j k).coeFn_toLp
  have hs := AffineResidual.coeFn_weighted_sum (fun a:d.G.Anchor=>d.G.centerForm d.r d.sigma i (.inl a)) V
  have hd : (lpGraph d).direct i=∑ a,d.G.centerForm d.r d.sigma i (.inl a) • V a := by
    simp only [lpGraph,MeanGeometry.graph,MeanGeometry.direct,zero_add,V]
  rw [hd]
  filter_upwards [hy,hg,hz,hs] with ω hy hg hz hs
  have ha (a:d.G.Anchor) : V a ω=d.G.anchorValues ω.1.fst ω.1.snd ω.2 a := by
    rcases a with _ | _ | ⟨j,k⟩
    · exact hy
    · exact hg
    · exact hz j k
  rw [hs]
  simp only [ha,rawGraph,MeanGeometry.graph,MeanGeometry.direct]

private theorem step_ae (X : d.G.MeanNode → H d) (i : d.G.MeanNode) :
    (fun ω : Seed d=>(rawGraph d ω).step (Gibbs.primitiveMean d.F) (fun j=>d.x+X j ω) i)=ᵐ[seedMeasure d]
      (fun ω=>d.x+(lpGraph d).step (operator d) X i ω) := by
  let Q : d.G.MeanNode → H d := fun j=>operator d (X j) (d.G.radius d.r j)
  have hq : ∀ᵐ ω ∂seedMeasure d,∀ j,Q j ω=Gibbs.primitiveMean d.F (d.x+X j ω) (d.G.radius d.r j) :=
    ae_all_iff.mpr fun j=>primitiveLp_ae (primitiveData d) (seedMeasure d)
      (d.G.radius_pos d.r d.hr j) (X j)
  have hs := AffineResidual.coeFn_weighted_sum (d.G.matrix d.r d.sigma i) Q
  have ha := Lp.coeFn_add ((lpGraph d).direct i) (∑ j,d.G.matrix d.r d.sigma i j • Q j)
  filter_upwards [direct_ae d i,hq,hs,ha] with ω hd hq hs ha
  change _=d.x+(((lpGraph d).direct i+∑ j,d.G.matrix d.r d.sigma i j • Q j : H d) ω)
  rw [ha]
  simp only [Pi.add_apply,hs,hq,FiniteGraph.step_eq,rawGraph,MeanGeometry.graph] at ⊢
  simp only [rawGraph,MeanGeometry.graph] at hd
  rw [hd]
  exact add_assoc _ _ _

theorem rawIterate_ae (N : ℕ) (i : d.G.MeanNode) :
    rawIterate d N i=ᵐ[seedMeasure d] (fun ω=>d.x+iterate d N i ω) := by
  induction N generalizing i with
  | zero => exact direct_ae d i
  | succ N ih =>
    have hprev : ∀ᵐ ω ∂seedMeasure d,∀ j,rawIterate d N j ω=d.x+iterate d N j ω :=
      ae_all_iff.mpr ih
    filter_upwards [hprev,step_ae d (iterate d N) i] with ω hp hs
    change (rawGraph d ω).step (Gibbs.primitiveMean d.F) (fun j=>rawIterate d N j ω) i=
      d.x+((lpGraph d).step (operator d) (iterate d N) i : H d) ω
    simpa only [hp] using hs

end Raw


section RawOutput
variable (d : Data ι m)

theorem rawIterate_memLp (N : ℕ) (i : d.G.MeanNode) : MemLp (rawIterate d N i) 2 (seedMeasure d) :=
  ((memLp_const d.x).add (Lp.memLp (iterate d N i))).ae_eq (rawIterate_ae d N i).symm

theorem rawOutput_ae (N : ℕ) : rawOutput d N=ᵐ[seedMeasure d] (output d N : Seed d → E) := by
  let Q : d.G.MeanNode → H d := fun j=>operator d (iterate d N j) (d.G.radius d.r j)
  have hq : ∀ᵐ ω ∂seedMeasure d,∀ j,Q j ω=Gibbs.primitiveMean d.F (d.x+iterate d N j ω) (d.G.radius d.r j) :=
    ae_all_iff.mpr fun j=>primitiveLp_ae (primitiveData d) (seedMeasure d)
      (d.G.radius_pos d.r d.hr j) (iterate d N j)
  have hi := ae_all_iff.mpr (rawIterate_ae d N)
  have hg := (seed_score_memLp d).coeFn_toLp
  have hs := AffineResidual.coeFn_weighted_sum d.G.outputWeight Q
  have hm := Lp.coeFn_smul (d.sigma/2) (initialScore d)
  have ha := Lp.coeFn_add ((d.sigma/2) • initialScore d) (∑ j,d.G.outputWeight j • Q j)
  have ho : output d N=(d.sigma/2) • initialScore d+∑ j,d.G.outputWeight j • Q j := by
    rw [output,d.G.meanOutput_eq_weighted_sum]
    rfl
  rw [ho]
  filter_upwards [hq,hi,hg,hs,hm,ha] with ω hq hi hg hs hm ha
  change initialScore d ω=ω.1.snd at hg
  rw [ha]
  simp only [Pi.add_apply,hm,Pi.smul_apply,hg,hs,hq,rawOutput,d.G.meanOutput_eq_weighted_sum,
    FiniteGraph.collect,FiniteGraph.requests,rawGraph,MeanGeometry.graph,hi]

theorem rawOutput_memLp (N : ℕ) : MemLp (rawOutput d N) 2 (seedMeasure d) :=
  (Lp.memLp (output d N)).ae_eq (rawOutput_ae d N).symm

theorem rawTerminalTarget_ae : rawTerminalTarget d=ᵐ[seedMeasure d] (terminalTarget d : Seed d → E) := by
  have hc := (memLp_const (Gibbs.primitiveMean d.F d.x d.r) :
    MemLp (fun _ : Seed d=>Gibbs.primitiveMean d.F d.x d.r) 2 (seedMeasure d)).coeFn_toLp
  have hg := (score_memLp d 1).coeFn_toLp
  filter_upwards [hc,hg,Lp.coeFn_smul (d.sigma/2) (scoreLp d 1),
    Lp.coeFn_add (offsetLp d) ((d.sigma/2) • scoreLp d 1)] with ω hc hg hm ha
  change _=(offsetLp d+(d.sigma/2) • scoreLp d 1 : H d) ω
  rw [ha]
  simp only [Pi.add_apply,hm,Pi.smul_apply]
  change _=(_+(d.sigma/2) • (score_memLp d 1).toLp (score d 1) ω)
  rw [hg]
  exact congrArg (fun z=>z+(d.sigma/2) • score d 1 ω) hc.symm

theorem rawIteration_target : RawIterationTarget d :=
  ⟨rawIterate_ae d,rawIterate_memLp d,rawOutput_ae d,rawOutput_memLp d,rawTerminalTarget_ae d⟩
end RawOutput

section Error
variable (d : Data ι m) (h₀ : ℝ) (h : MeshConditions d h₀)
  (K : Fin m → ℝ → H d) (l v : ℝ) (D : AffineResidual.Mean.DerivativeBudget d.G)
  (hreg : Regularity d K l v D)
include h hreg

theorem residual_bound (i : d.G.MeanNode) :
    ‖(lpGraph d).step (operator d) (reference d) i-reference d i‖≤residualBudget d h₀ D := by
  have he := (kernelReplacement d (operator d) (primitiveLp_spec _ _) K hreg.1).1
  have hb := AffineResidual.Mean.meanResidual d.G h.order d.r d.sigma h₀ l v d.hr d.hsigma
    h.step_pos.le hreg.2.1 hreg.2.2.1 (cell_bound d h₀ h)
    (operator d) 0 (initialPosition d) (initialScore d) (initialNoise d)
    (curvesWithKernel d K) D he hreg.2.2.2 i
  exact hb.trans ((le_abs_self _).trans (norm_le_pi_norm (D.rowError d.G d.r d.sigma h₀) i))

theorem finite_bound (N : ℕ) : ‖iterate d N-reference d‖≤finiteError d h₀ D N := by
  have hb := Collocation.iteratePhi_error_le ((lpGraph d).step (operator d))
    (lpGraph d).direct (reference d) (contraction d h₀) (residualBudget d h₀ D) N
    (contraction_nonneg d h₀ h) (norm_nonneg _) (contraction_target d h₀ h)
    (residual_bound d h₀ h K l v D hreg)
  simpa only [Collocation.iteratePhi,← FiniteGraph.iterate_eq_function_iterate,Collocation.nodeError,
    iterate,finiteError,initialError] using hb

theorem geometric_bound (N : ℕ) (hq : contraction d h₀<1) :
    ‖iterate d N-reference d‖≤contraction d h₀^N*initialError d+
      residualBudget d h₀ D/(1-contraction d h₀) := by
  have hs : (∑ j∈Finset.range N,contraction d h₀^j)≤1/(1-contraction d h₀) := by
    simpa using geom_sum_Ico_le_of_lt_one (m:=0) (n:=N) (contraction_nonneg d h₀ h) hq
  exact (finite_bound d h₀ h K l v D hreg N).trans (by
    unfold finiteError
    simpa only [div_eq_mul_inv,one_mul,residualBudget] using
      add_le_add (le_refl (contraction d h₀^N*initialError d))
        (mul_le_mul_of_nonneg_left hs (norm_nonneg (D.rowError d.G d.r d.sigma h₀))))
end Error

theorem residual_target (d : Data ι m) (h₀ : ℝ) : ResidualTarget d h₀ :=
  fun h K l v D hreg=>residual_bound d h₀ h K l v D hreg

section RawError
variable (d : Data ι m)
theorem raw_error_ae (N : ℕ) (i : d.G.MeanNode) :
    (fun ω=>rawIterate d N i ω-rawReference d i ω)=ᵐ[seedMeasure d]
      ((iterate d N i-reference d i : H d) : Seed d → E) := by
  filter_upwards [rawIterate_ae d N i,MeanResidualBridge.rawReference_ae d i,
    Lp.coeFn_sub (iterate d N i) (reference d i)] with ω hi hr hs
  rw [hi,hr,hs]
  simp only [AffineResidual.MeanRms.rawReference,Pi.sub_apply,reference,add_sub_add_left_eq_sub]

theorem raw_error_memLp (N : ℕ) (i : d.G.MeanNode) :
    MemLp (fun ω=>rawIterate d N i ω-rawReference d i ω) 2 (seedMeasure d) :=
  (Lp.memLp (iterate d N i-reference d i)).ae_eq (raw_error_ae d N i).symm
end RawError

theorem finiteIteration_target (d : Data ι m) (h₀ : ℝ) : FiniteIterationTarget d h₀ := by
  intro h K l v D hreg N
  refine ⟨finite_bound d h₀ h K l v D hreg N,?_,geometric_bound d h₀ h K l v D hreg N⟩
  intro i
  refine ⟨raw_error_memLp d N i,?_⟩
  rw [AffineResidual.toLp_eq_of_ae _ (raw_error_ae d N i)]
  exact (norm_le_pi_norm (iterate d N-reference d) i).trans (finite_bound d h₀ h K l v D hreg N)


section Final
variable (d : Data ι m)

theorem output_lipschitz (hm : 0<m) (X Y : d.G.MeanNode → H d) :
    ‖d.G.meanOutput d.sigma (initialScore d) ((lpGraph d).collect (operator d) X)-
      d.G.meanOutput d.sigma (initialScore d) ((lpGraph d).collect (operator d) Y)‖≤d.ell*‖X-Y‖ := by
  apply (d.G.norm_meanOutput_sub_le hm d.sigma (initialScore d) _ _).trans
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg d.hell (norm_nonneg (X-Y)))).mpr
  intro i
  have hi := (primitiveLp_lipschitz (primitiveData d) (seedMeasure d)
    (d.G.radius_pos d.r d.hr i)).norm_sub_le (X i) (Y i)
  exact hi.trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm (X-Y) i) d.hell)

variable (h₀ : ℝ) (h : MeshConditions d h₀)
  (K : Fin m → ℝ → H d) (l v : ℝ) (D : AffineResidual.Mean.DerivativeBudget d.G)
  (hreg : Regularity d K l v D)
include h hreg

theorem reference_output_bound :
    ‖d.G.meanOutput d.sigma (initialScore d)
      ((lpGraph d).collect (operator d) (reference d))-terminalTarget d‖≤2*D.center/(m.factorial:ℝ) := by
  have he := (kernelReplacement d (operator d) (primitiveLp_spec _ _) K hreg.1).1
  have hb := AffineResidual.Mean.meanFinalResidual d.G h.order d.r d.sigma d.hr d.hsigma
    (operator d) 0 (initialPosition d) (initialScore d) (initialNoise d)
    (curvesWithKernel d K) D.center hreg.2.2.2.center_nonneg he
    hreg.2.2.2.center_smooth hreg.2.2.2.center_bound
  change ‖d.G.meanOutput d.sigma (initialScore d) ((lpGraph d).collect (operator d) (reference d))-
    (operator d 0 d.r+(d.sigma/2) • scoreLp d 1)‖≤_ at hb
  have ho : operator d 0 d.r=offsetLp d := MeanResidualBridge.offset_eq d _ (primitiveLp_spec _ _)
  rw [ho] at hb
  exact hb

theorem final_bound (N : ℕ) :
    ‖output d N-terminalTarget d‖≤d.ell*finiteError d h₀ D N+2*D.center/(m.factorial:ℝ) := by
  let R := d.G.meanOutput d.sigma (initialScore d) ((lpGraph d).collect (operator d) (reference d))
  have htri : ‖output d N-terminalTarget d‖≤‖output d N-R‖+‖R-terminalTarget d‖ :=
    by simpa only [dist_eq_norm] using dist_triangle (output d N) R (terminalTarget d)
  exact htri.trans (add_le_add
    ((output_lipschitz d (by have hm:=h.order;omega) (iterate d N) (reference d)).trans
      (mul_le_mul_of_nonneg_left (finite_bound d h₀ h K l v D hreg N) d.hell))
    (reference_output_bound d h₀ h K l v D hreg))
end Final

theorem finalOutput_target (d : Data ι m) (h₀ : ℝ) : FinalOutputTarget d h₀ := by
  intro h K l v D hreg N
  have he : (fun ω=>rawOutput d N ω-rawTerminalTarget d ω)=ᵐ[seedMeasure d]
      ((output d N-terminalTarget d : H d) : Seed d → E) := by
    filter_upwards [rawOutput_ae d N,rawTerminalTarget_ae d,
      Lp.coeFn_sub (output d N) (terminalTarget d)] with ω ho ht hs
    simpa only [ho,ht,Pi.sub_apply] using hs.symm
  let hm := (Lp.memLp (output d N-terminalTarget d)).ae_eq he.symm
  refine ⟨final_bound d h₀ h K l v D hreg N,hm,?_⟩
  rw [AffineResidual.toLp_eq_of_ae hm he]
  exact final_bound d h₀ h K l v D hreg N

end AcceleratedLogConcave.Numerics.MeanCollocationLp
