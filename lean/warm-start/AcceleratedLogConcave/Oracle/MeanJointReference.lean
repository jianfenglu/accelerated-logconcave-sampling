import AcceleratedLogConcave.Numerics.SourceFlowJointCenter
import AcceleratedLogConcave.Oracle.ExecutableData
import AcceleratedLogConcave.Numerics.MeanResidualBridge
import AcceleratedLogConcave.Conditional.Centering.SourceParameterRegularity

/-! The actual mean-inventory benchmark centers jointly in the external
center, retained private reference position, assembled initial score, and
literal conditional-flow seeds. Every branch is the existing source flow. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.MeanJointReference
open Numerics Numerics.AffineGraph Numerics.AffineGraph.MeanGeometry Conditional TapeLowering
variable {d m : ℕ} (M : MeanGeometry m)
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)
  (r σ : ℝ) (hr : 0<r) (hσ : 0<σ) (hsmall : r^2*ell≤1/2)

abbrev Host := (Point d × Point d) × (Fin m → M.Kernel → Point d)

def data (x : Point d) : MeanFlowLp.Data (Fin d) m :=
  ⟨F,hF,ell,hell,hlo,hup,x,r,hr,hsmall,M,σ,hσ⟩

def seed (x : Point d) (h : Host (d := d) M) : MeanFlowLp.Seed (data M hF hell hlo hup r σ hr hσ hsmall x) :=
  (WithLp.toLp 2 h.1,h.2)

def theta (x : Point d) : SourceParameters (Point d) ell :=
  ⟨(x,r,σ/2),hr,half_pos hσ,hsmall⟩

theorem continuous_theta : Continuous (theta (d := d) r σ hr hσ hsmall) := by
  apply Continuous.subtype_mk
  exact continuous_id.prodMk (continuous_const.prodMk continuous_const)

def phase (t : ℝ) (z : Point d × Host (d := d) M) : Centering.Phase (Point d) :=
  MeanFlowLp.phase (data M hF hell hlo hup r σ hr hσ hsmall z.1) t
    (seed M hF hell hlo hup r σ hr hσ hsmall z.1 z.2)

theorem continuous_phase (t : ℝ) :
    Continuous (phase M hF hell hlo hup r σ hr hσ hsmall t) := by
  have hp : Continuous (fun z : Point d × Host (d := d) M => WithLp.toLp 2 z.2.1) :=
    (WithLp.prod_continuous_toLp 2 (Point d) (Point d)).comp continuous_snd.fst
  have h := (Centering.continuous_sourceCenteringFlow_parameters hF hell hlo hup
    M.backwardEnd_pos.le M.backwardEnd_lt_one).comp
      (((continuous_theta r σ hr hσ hsmall).comp continuous_fst).prodMk
        ((continuous_const : Continuous (fun _ : Point d × Host (d := d) M => t)).prodMk hp))
  exact h

theorem continuous_position (t : ℝ) :
    Continuous (fun z : Point d × Host (d := d) M =>
      (phase M hF hell hlo hup r σ hr hσ hsmall t z).fst) :=
  (WithLp.prod_continuous_ofLp 2 (Point d) (Point d)).fst.comp
    (continuous_phase M hF hell hlo hup r σ hr hσ hsmall t)

theorem continuous_score (t : ℝ) :
    Continuous (fun z : Point d × Host (d := d) M =>
      (phase M hF hell hlo hup r σ hr hσ hsmall t z).snd) :=
  (WithLp.prod_continuous_ofLp 2 (Point d) (Point d)).snd.comp
    (continuous_phase M hF hell hlo hup r σ hr hσ hsmall t)

def transportData : SamplingCenterLp.Data (Fin d) :=
  ⟨F,hF,ell,hell,hlo,hup,r,hr,backwardEnd M.R,M.backwardEnd_pos.le,M.backwardEnd_lt_one⟩

def backward (j : Fin m) (t : ℝ) (z : Point d × Host (d := d) M) : Point d :=
  MeanFlowLp.backward (data M hF hell hlo hup r σ hr hσ hsmall z.1) j t
    (seed M hF hell hlo hup r σ hr hσ hsmall z.1 z.2)

theorem continuous_backward (j : Fin m) (t : ℝ) :
    Continuous (backward M hF hell hlo hup r σ hr hσ hsmall j t) := by
  change Continuous (fun z => backward M hF hell hlo hup r σ hr hσ hsmall j t z)
  have h := (SourceFlowJointCenter.continuous_source (transportData M hF hell hlo hup r hr)
    ⟨backwardEnd M.R,M.backwardEnd_pos.le,le_rfl⟩).comp
      ((continuous_const : Continuous (fun _ : Point d × Host (d := d) M => t)).prodMk
        (continuous_fst.prodMk (continuous_position M hF hell hlo hup r σ hr hσ hsmall (centerNode j))))
  simpa only [Function.comp_def,backward,MeanFlowLp.backward,MeanFlowLp.transportData,data,transportData,
    MeanFlowLp.position,phase] using h

def conditionalCenter (j : Fin m) (k : M.Kernel) (z : Point d × Host (d := d) M) : Point d :=
  z.1+(r*M.rho k) • backward M hF hell hlo hup r σ hr hσ hsmall j (M.rho k) z

theorem continuous_conditionalCenter (j : Fin m) (k : M.Kernel) :
    Continuous (conditionalCenter M hF hell hlo hup r σ hr hσ hsmall j k) :=
  continuous_fst.add ((continuous_backward M hF hell hlo hup r σ hr hσ hsmall j (M.rho k)).const_smul (r*M.rho k))

def conditionalData (k : M.Kernel) : SamplingCenterLp.Data (Fin d) :=
  ⟨F,hF,ell,hell,hlo,hup,r*Real.sqrt (M.variance k),
    mul_pos hr (Real.sqrt_pos.mpr (M.variance_pos k)),conditionalEnd,
    conditionalEnd_pos.le,conditionalEnd_lt_one⟩

def conditional (j : Fin m) (k : M.Kernel) (t : ℝ) (z : Point d × Host (d := d) M) : Point d :=
  MeanFlowLp.conditional (data M hF hell hlo hup r σ hr hσ hsmall z.1) j k t
    (seed M hF hell hlo hup r σ hr hσ hsmall z.1 z.2)

theorem continuous_conditional (j : Fin m) (k : M.Kernel) (t : ℝ) :
    Continuous (conditional M hF hell hlo hup r σ hr hσ hsmall j k t) := by
  change Continuous (fun z => conditional M hF hell hlo hup r σ hr hσ hsmall j k t z)
  have hz : Continuous (fun z : Point d × Host (d := d) M => z.2.2 j k) := by fun_prop
  have h := (SamplingCenterLp.continuous_path (conditionalData M hF hell hlo hup r hr k)).comp
    ((continuous_const : Continuous (fun _ : Point d × Host (d := d) M => t)).prodMk
      ((continuous_conditionalCenter M hF hell hlo hup r σ hr hσ hsmall j k).prodMk hz))
  simpa only [Function.comp_def,conditional,MeanFlowLp.conditional,MeanFlowLp.conditionalData,conditionalData,data,
    seed,conditionalCenter,MeanFlowLp.conditionalCenter,backward] using h

def rotation (j : Fin m) (k : M.Kernel) (a : ℝ) (z : Point d × Host (d := d) M) : Point d :=
  MeanFlowLp.rotation (data M hF hell hlo hup r σ hr hσ hsmall z.1) j k a
    (seed M hF hell hlo hup r σ hr hσ hsmall z.1 z.2)

theorem continuous_rotation (j : Fin m) (k : M.Kernel) (a : ℝ) :
    Continuous (rotation M hF hell hlo hup r σ hr hσ hsmall j k a) := by
  have hB := continuous_backward M hF hell hlo hup r σ hr hσ hsmall j (M.rho k)
  have hC := continuous_conditional M hF hell hlo hup r σ hr hσ hsmall j k conditionalEnd
  have hH := (hB.const_smul (M.rho k)).add (hC.const_smul (Real.sqrt (M.variance k)/conditionalEnd))
  have hmid := (hH.add (hB.const_smul (M.rho k))).const_smul (M.rho k/(1+(M.rho k)^2))
  exact (hmid.add ((hB.sub hmid).const_smul (Real.cos (a/M.rotationScale k)))).add
    ((continuous_score M hF hell hlo hup r σ hr hσ hsmall (centerNode j)).const_smul
      (M.rotationScale k*Real.sin (a/M.rotationScale k)))

def forward (j : Fin m) (k : M.Kernel) (a t : ℝ) (z : Point d × Host (d := d) M) : Point d :=
  MeanFlowLp.forward (data M hF hell hlo hup r σ hr hσ hsmall z.1) j k a t
    (seed M hF hell hlo hup r σ hr hσ hsmall z.1 z.2)

theorem continuous_forward (j : Fin m) (k : M.Kernel) (a t : ℝ) :
    Continuous (forward M hF hell hlo hup r σ hr hσ hsmall j k a t) := by
  change Continuous (fun z => forward M hF hell hlo hup r σ hr hσ hsmall j k a t z)
  have h := (SourceFlowJointCenter.continuous_source (transportData M hF hell hlo hup r hr)
    ⟨M.rho k,(M.rho_mem k).1,(M.rho_mem k).2.le⟩).comp
      ((continuous_const : Continuous (fun _ : Point d × Host (d := d) M => t)).prodMk
        (continuous_fst.prodMk (continuous_rotation M hF hell hlo hup r σ hr hσ hsmall j k a)))
  simpa only [Function.comp_def,forward,MeanFlowLp.forward,MeanFlowLp.transportData,data,transportData,rotation] using h

def reference (i : M.MeanNode) (z : Point d × Host (d := d) M) : Point d :=
  MeanResidualBridge.rawReference (data M hF hell hlo hup r σ hr hσ hsmall z.1) i
    (seed M hF hell hlo hup r σ hr hσ hsmall z.1 z.2)

/-- Every literal inventory branch is jointly continuous, including the
retained private reference position and actual assembled initial score. -/
theorem continuous_reference (i : M.MeanNode) :
    Continuous (reference M hF hell hlo hup r σ hr hσ hsmall i) := by
  rcases i with _ | j | ⟨j,k⟩ | ⟨j,k,l⟩ | ⟨j,k,a,l⟩
  · exact continuous_fst
  · exact continuous_fst.add ((continuous_position M hF hell hlo hup r σ hr hσ hsmall (centerNode j)).const_smul
      (r*backwardEnd M.R))
  · exact continuous_fst.add ((continuous_backward M hF hell hlo hup r σ hr hσ hsmall j
      (M.backward.location m k)).const_smul (r*M.backward.location m k))
  · exact (continuous_fst.add ((continuous_backward M hF hell hlo hup r σ hr hσ hsmall j (M.rho k)).const_smul
      (r*M.rho k))).add ((continuous_conditional M hF hell hlo hup r σ hr hσ hsmall j k
        ((M.conditional k).location m l)).const_smul
          (r*Real.sqrt (M.variance k)*(M.conditional k).location m l))
  · exact continuous_fst.add ((continuous_forward M hF hell hlo hup r σ hr hσ hsmall j k
      (M.angleNode a) ((M.forward k).location m l)).const_smul (r*(M.forward k).location m l))
end AcceleratedLogConcave.Oracle.MeanJointReference
