import AcceleratedLogConcave.Numerics.TransportFlowLp
/-!
# Actual common-space mean-field L² assembly

The literal product seed supplies every moment. Canonical L² fields share the
actual centering, backward, conditional, rotation and forward trajectories.
Signed integral equations, the ordinary angle derivative and the removable
singular-kernel identity are proved with derived domination. Parameters are
deterministic; no coupling law or higher-order budget is asserted.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory AcceleratedLogConcave Conditional
open Numerics Numerics.AffineGraph Numerics.AffineGraph.MeanGeometry
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Numerics.MeanFlowLp
variable {ι:Type*} [Fintype ι] [DecidableEq ι] {m:ℕ}
local notation "E" => EuclideanSpace ℝ ι
structure Data (ι:Type*) [Fintype ι] (m:ℕ) where
  F : EuclideanSpace ℝ ι → ℝ
  hF : ContDiff ℝ 2 F
  ell : ℝ
  hell : 0 ≤ ell
  hlo : ∀ z a,0 ≤ fderiv ℝ (fderiv ℝ F) z a a
  hup : ∀ z a,fderiv ℝ (fderiv ℝ F) z a a ≤ ell*‖a‖^2
  x : EuclideanSpace ℝ ι
  r : ℝ
  hr : 0 < r
  hsmall : r^2*ell ≤ 1/2
  G : MeanGeometry m
  sigma : ℝ
  hsigma : 0 < sigma

def kernelData (d:Data ι m) : KernelFlowLp.Data ι :=
  ⟨d.F,d.hF,d.ell,d.hell,d.hlo,d.hup,d.x,d.r,d.hr,backwardEnd d.G.R,
    d.G.backwardEnd_pos.le,d.G.backwardEnd_lt_one,d.hsmall⟩
def transportData (d:Data ι m) : SamplingCenterLp.Data ι :=
  ⟨d.F,d.hF,d.ell,d.hell,d.hlo,d.hup,d.r,d.hr,backwardEnd d.G.R,
    d.G.backwardEnd_pos.le,d.G.backwardEnd_lt_one⟩
def conditionalData (d:Data ι m) (k:d.G.Kernel) : SamplingCenterLp.Data ι :=
  ⟨d.F,d.hF,d.ell,d.hell,d.hlo,d.hup,d.r*Real.sqrt (d.G.variance k),
    mul_pos d.hr (Real.sqrt_pos.mpr (d.G.variance_pos k)),conditionalEnd,
    conditionalEnd_pos.le,conditionalEnd_lt_one⟩
abbrev Seed (d:Data ι m) := Centering.Phase E × (Fin m → d.G.Kernel → E)
def seedMeasure (d:Data ι m) : Measure (Seed d) :=
  (KernelFlowLp.seedMeasure (kernelData d)).prod
    (Measure.pi fun _ : Fin m => Measure.pi fun _ : d.G.Kernel => stdGaussian E)
def phase (d:Data ι m) (t:ℝ) (ω:Seed d) : Centering.Phase E :=
  CenteringFlowLp.phase (kernelData d) (d.sigma/2) (half_pos d.hsigma) t ω.1
def position (d:Data ι m) (t:ℝ) (ω:Seed d) : E := (phase d t ω).fst
def score (d:Data ι m) (t:ℝ) (ω:Seed d) : E := (phase d t ω).snd
def velocity (d:Data ι m) (t:ℝ) (ω:Seed d) : E :=
  -(d.sigma/2)⁻¹ • KernelFlowLp.kernel (kernelData d) (phase d t ω)
def backward (d:Data ι m) (j:Fin m) (t:ℝ) (ω:Seed d) : E :=
  TransportFlowLp.flow (transportData d) d.x
    ⟨backwardEnd d.G.R,d.G.backwardEnd_pos.le,le_rfl⟩ t (position d (centerNode j) ω)
def conditionalCenter (d:Data ι m) (j:Fin m) (k:d.G.Kernel) (ω:Seed d) : E :=
  d.x+(d.r*d.G.rho k) • backward d j (d.G.rho k) ω
def conditional (d:Data ι m) (j:Fin m) (k:d.G.Kernel) (t:ℝ) (ω:Seed d) : E :=
  SamplingCenterLp.path (conditionalData d k) (conditionalCenter d j k ω) t (ω.2 j k)
def rotation (d:Data ι m) (j:Fin m) (k:d.G.Kernel) (z:ℝ) (ω:Seed d) : E :=
  let B := backward d j (d.G.rho k) ω
  let H := d.G.rho k • B+(Real.sqrt (d.G.variance k)/conditionalEnd) • conditional d j k conditionalEnd ω
  let mid := (d.G.rho k/(1+(d.G.rho k)^2)) • (H+d.G.rho k • B)
  mid+Real.cos (z/d.G.rotationScale k) • (B-mid)+
    (d.G.rotationScale k*Real.sin (z/d.G.rotationScale k)) • score d (centerNode j) ω
def forward (d:Data ι m) (j:Fin m) (k:d.G.Kernel) (z t:ℝ) (ω:Seed d) : E :=
  TransportFlowLp.flow (transportData d) d.x
    ⟨d.G.rho k,(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩ t (rotation d j k z ω)
def kernel (d:Data ι m) (j:Fin m) (t:ℝ) (ω:Seed d) : E :=
  KernelFlowLp.extension (kernelData d) t (phase d (centerNode j) ω)
def centerMean (d:Data ι m) (t:ℝ) (ω:Seed d) : E :=
  Gibbs.primitiveMean d.F (d.x+(d.r*backwardEnd d.G.R) • position d t ω) (d.r*d.G.R)
def backwardMean (d:Data ι m) (j:Fin m) (t:ℝ) (ω:Seed d) : E :=
  let a := SamplingFlowLp.sourceTime d.G.backwardEnd_pos.le t
  Gibbs.primitiveMean d.F (d.x+(d.r*a) • backward d j t ω) (d.r*Real.sqrt (1-a^2))
def conditionalMean (d:Data ι m) (j:Fin m) (k:d.G.Kernel) (t:ℝ) (ω:Seed d) : E :=
  let a := SamplingFlowLp.sourceTime conditionalEnd_pos.le t
  Gibbs.primitiveMean d.F (conditionalCenter d j k ω+
    ((conditionalData d k).r*a) • conditional d j k t ω)
    ((conditionalData d k).r*Real.sqrt (1-a^2))
def forwardMean (d:Data ι m) (j:Fin m) (k:d.G.Kernel) (z t:ℝ) (ω:Seed d) : E :=
  let a := SamplingFlowLp.sourceTime d.G.backwardEnd_pos.le t
  Gibbs.primitiveMean d.F (d.x+(d.r*a) • forward d j k z t ω) (d.r*Real.sqrt (1-a^2))
def action (d:Data ι m) (j:Fin m) (k:d.G.Kernel) (z:ℝ) (ω:Seed d) : E :=
  forward d j k z (backwardEnd d.G.R) ω-rotation d j k z ω

def SeedTarget (d:Data ι m) : Prop :=
  IsProbabilityMeasure (seedMeasure d) ∧
  MeasurePreserving (fun ω : Seed d => ω.1) (seedMeasure d) (KernelFlowLp.seedMeasure (kernelData d)) ∧
  (∀ j k,MeasurePreserving (fun ω : Seed d => ω.2 j k) (seedMeasure d) (stdGaussian E))

/-- To be constructed, not supplied as a hypothesis of the assembly theorem. -/
structure Inventory (d:Data ι m) : Prop where
  seedPosition : MemLp (fun ω : Seed d => ω.1.fst) 2 (seedMeasure d)
  seedScore : MemLp (fun ω : Seed d => ω.1.snd) 2 (seedMeasure d)
  seedNoise : ∀ j k,MemLp (fun ω : Seed d => ω.2 j k) 2 (seedMeasure d)
  offset : MemLp (fun _ : Seed d => Gibbs.primitiveMean d.F d.x d.r) 2 (seedMeasure d)
  position : ∀ t,MemLp (position d t) 2 (seedMeasure d)
  score : ∀ t,MemLp (score d t) 2 (seedMeasure d)
  velocity : ∀ t,MemLp (velocity d t) 2 (seedMeasure d)
  backward : ∀ j t,MemLp (backward d j t) 2 (seedMeasure d)
  conditional : ∀ j k t,MemLp (conditional d j k t) 2 (seedMeasure d)
  rotation : ∀ j k z,MemLp (rotation d j k z) 2 (seedMeasure d)
  forward : ∀ j k z t,MemLp (forward d j k z t) 2 (seedMeasure d)
  kernel : ∀ j t,MemLp (kernel d j t) 2 (seedMeasure d)
  centerMean : ∀ t,MemLp (centerMean d t) 2 (seedMeasure d)
  backwardMean : ∀ j t,MemLp (backwardMean d j t) 2 (seedMeasure d)
  conditionalMean : ∀ j k t,MemLp (conditionalMean d j k t) 2 (seedMeasure d)
  forwardMean : ∀ j k z t,MemLp (forwardMean d j k z t) 2 (seedMeasure d)
  action : ∀ j k z,MemLp (action d j k z) 2 (seedMeasure d)

def AssemblyTarget (d:Data ι m) : Prop :=
  ∃ h : Inventory d,
  let U := h.offset.toLp (fun _ : Seed d => Gibbs.primitiveMean d.F d.x d.r)
  let Y := fun t => (h.position t).toLp (position d t)
  let G := fun t => (h.score t).toLp (score d t)
  let V := fun t => (h.velocity t).toLp (velocity d t)
  let B := fun j t => (h.backward j t).toLp (backward d j t)
  let D := fun j k t => (h.conditional j k t).toLp (conditional d j k t)
  let W := fun j k z => (h.rotation j k z).toLp (rotation d j k z)
  let F := fun j k z t => (h.forward j k z t).toLp (forward d j k z t)
  let K := fun j t => (h.kernel j t).toLp (kernel d j t)
  let MC := fun t => (h.centerMean t).toLp (centerMean d t)
  let MB := fun j t => (h.backwardMean j t).toLp (backwardMean d j t)
  let MD := fun j k t => (h.conditionalMean j k t).toLp (conditionalMean d j k t)
  let MF := fun j k z t => (h.forwardMean j k z t).toLp (forwardMean d j k z t)
  let A := fun j k z => (h.action j k z).toLp (action d j k z)
  Y 0=h.seedPosition.toLp (fun ω : Seed d => ω.1.fst) ∧
  G 0=h.seedScore.toLp (fun ω : Seed d => ω.1.snd) ∧
  (∀ j,B j (backwardEnd d.G.R)=Y (centerNode j)) ∧
  (∀ j k,D j k 0=(h.seedNoise j k).toLp (fun ω : Seed d => ω.2 j k)) ∧
  (∀ j k z,F j k z (d.G.rho k)=W j k z) ∧
  Continuous Y ∧ Continuous G ∧ Continuous V ∧ Continuous MC ∧
  (∀ j,Continuous (B j) ∧ Continuous (MB j) ∧ Continuous (K j)) ∧
  (∀ j k,Continuous (D j k) ∧ Continuous (MD j k) ∧ Continuous (W j k)) ∧
  (∀ j k z,Continuous (F j k z) ∧ Continuous (MF j k z)) ∧
  (∀ a b,Y b=Y a+∫ t in a..b,V t) ∧
  (∀ a b,G b=G a+(d.sigma/2)⁻¹ • ∫ t in a..b,(MC t-U)) ∧
  (∀ j a b,a∈Icc 0 (backwardEnd d.G.R) → b∈Icc 0 (backwardEnd d.G.R) →
    B j b=B j a-d.r • ∫t in a..b,MB j t) ∧
  (∀ j k a b,a∈Icc 0 conditionalEnd → b∈Icc 0 conditionalEnd →
    D j k b=D j k a-(conditionalData d k).r • ∫t in a..b,MD j k t) ∧
  (∀ j k z a b,a∈Icc 0 (backwardEnd d.G.R) → b∈Icc 0 (backwardEnd d.G.R) →
    F j k z b=F j k z a-d.r • ∫t in a..b,MF j k z t) ∧
  (∀ j k z,A j k z = -d.r • ∫t in d.G.rho k..backwardEnd d.G.R,MF j k z t) ∧
  (∀ j k,HasDerivAt (A j k) (K j (d.G.rho k)) 0) ∧
  (∀ j,IntervalIntegrable (fun t => t⁻¹ • deriv (K j) t) volume 0 (backwardEnd d.G.R) ∧
    V (centerNode j)=-(d.r*(d.sigma/2))⁻¹ •
      ∫t in 0..backwardEnd d.G.R,t⁻¹ • deriv (K j) t)


instance seed_probability (d : Data ι m) : IsProbabilityMeasure (seedMeasure d) := by
  unfold seedMeasure
  infer_instance

omit [DecidableEq ι] in
theorem phase_projection_preserving (d : Data ι m) :
    MeasurePreserving (fun ω : Seed d => ω.1) (seedMeasure d)
      (KernelFlowLp.seedMeasure (kernelData d)) := measurePreserving_fst

omit [DecidableEq ι] in
theorem noise_projection_preserving (d : Data ι m) (j : Fin m) (k : d.G.Kernel) :
    MeasurePreserving (fun ω : Seed d => ω.2 j k) (seedMeasure d) (stdGaussian E) :=
  (measurePreserving_eval (fun _ : d.G.Kernel => stdGaussian E) k).comp
    ((measurePreserving_eval (fun _ : Fin m => Measure.pi (fun _ : d.G.Kernel => stdGaussian E)) j).comp
      measurePreserving_snd)

omit [DecidableEq ι] in
theorem seed_target (d : Data ι m) : SeedTarget d :=
  ⟨inferInstance,phase_projection_preserving d,noise_projection_preserving d⟩

theorem seed_position_memLp (d : Data ι m) :
    MemLp (fun ω : Seed d => ω.1.fst) 2 (seedMeasure d) :=
  (CenteringFlowLp.position_initial_memLp (kernelData d)).comp_measurePreserving
    (phase_projection_preserving d)
omit [DecidableEq ι] in
theorem seed_score_memLp (d : Data ι m) :
    MemLp (fun ω : Seed d => ω.1.snd) 2 (seedMeasure d) :=
  (KernelFlowLp.momentum_memLp (kernelData d)).comp_measurePreserving (phase_projection_preserving d)
omit [DecidableEq ι] in
theorem seed_noise_memLp (d : Data ι m) (j : Fin m) (k : d.G.Kernel) :
    MemLp (fun ω : Seed d => ω.2 j k) 2 (seedMeasure d) :=
  (IsGaussian.memLp_two_id (μ := stdGaussian E)).comp_measurePreserving
    (noise_projection_preserving d j k)
theorem position_memLp (d : Data ι m) (t : ℝ) : MemLp (position d t) 2 (seedMeasure d) :=
  (CenteringFlowLp.position_memLp (kernelData d) _ _ t).comp_measurePreserving
    (phase_projection_preserving d)
theorem score_memLp (d : Data ι m) (t : ℝ) : MemLp (score d t) 2 (seedMeasure d) :=
  (CenteringFlowLp.momentum_memLp (kernelData d) _ _ t).comp_measurePreserving
    (phase_projection_preserving d)
theorem velocity_memLp (d : Data ι m) (t : ℝ) : MemLp (velocity d t) 2 (seedMeasure d) :=
  ((CenteringFlowLp.kernel_memLp (kernelData d) (d.sigma/2) (half_pos d.hsigma) t).comp_measurePreserving
    (phase_projection_preserving d)).const_smul (-(d.sigma/2)⁻¹)
theorem backward_memLp (d : Data ι m) (j : Fin m) (t : ℝ) :
    MemLp (backward d j t) 2 (seedMeasure d) :=
  TransportFlowLp.flow_memLp (transportData d) d.x _ _ (position_memLp d (centerNode j)) t

theorem conditionalCenter_memLp (d : Data ι m) (j : Fin m) (k : d.G.Kernel) :
    MemLp (conditionalCenter d j k) 2 (seedMeasure d) :=
  (memLp_const d.x).add ((backward_memLp d j (d.G.rho k)).const_smul (d.r*d.G.rho k))
theorem conditional_memLp (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (t : ℝ) :
    MemLp (conditional d j k t) 2 (seedMeasure d) :=
  SamplingCenterLp.path_memLp (conditionalData d k) _ _ (conditionalCenter_memLp d j k)
    (seed_noise_memLp d j k) t
theorem rotation_memLp (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z : ℝ) :
    MemLp (rotation d j k z) 2 (seedMeasure d) := by
  let B := backward d j (d.G.rho k)
  let H := fun ω => d.G.rho k • B ω+
    (Real.sqrt (d.G.variance k)/conditionalEnd) • conditional d j k conditionalEnd ω
  let mid := fun ω => (d.G.rho k/(1+(d.G.rho k)^2)) • (H ω+d.G.rho k • B ω)
  have hB : MemLp B 2 (seedMeasure d) := backward_memLp d j _
  have hH : MemLp H 2 (seedMeasure d) :=
    (hB.const_smul (d.G.rho k)).add ((conditional_memLp d j k conditionalEnd).const_smul (Real.sqrt (d.G.variance k)/conditionalEnd))
  have hmid : MemLp mid 2 (seedMeasure d) := (hH.add (hB.const_smul (d.G.rho k))).const_smul (d.G.rho k/(1+(d.G.rho k)^2))
  exact (hmid.add ((hB.sub hmid).const_smul (Real.cos (z/d.G.rotationScale k)))).add ((score_memLp d (centerNode j)).const_smul (d.G.rotationScale k*Real.sin (z/d.G.rotationScale k)))
theorem forward_memLp (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z t : ℝ) :
    MemLp (forward d j k z t) 2 (seedMeasure d) :=
  TransportFlowLp.flow_memLp (transportData d) d.x _ _ (rotation_memLp d j k z) t

theorem kernel_phase_preserving (d : Data ι m) (t : ℝ) :
    MeasurePreserving (phase d t) (seedMeasure d) (KernelFlowLp.seedMeasure (kernelData d)) :=
  (CenteringFlowLp.phase_preserving (kernelData d) _ _ t).comp (phase_projection_preserving d)
theorem kernel_memLp (d : Data ι m) (j : Fin m) (t : ℝ) :
    MemLp (kernel d j t) 2 (seedMeasure d) :=
  (KernelFlowLp.extension_memLp (kernelData d) t).comp_measurePreserving
    (kernel_phase_preserving d (centerNode j))

omit [DecidableEq ι] in
theorem sqrt_backward_variance (d : Data ι m) :
    Real.sqrt (1-(backwardEnd d.G.R)^2)=d.G.R := by
  have hR : 0 ≤ 1-d.G.R^2 := by nlinarith [d.G.R_pos,d.G.R_le_half]
  rw [backwardEnd,Real.sq_sqrt hR]
  rw [show 1-(1-d.G.R^2)=d.G.R^2 by ring]
  exact Real.sqrt_sq d.G.R_pos.le

theorem centerMean_eq (d : Data ι m) (t : ℝ) (ω : Seed d) :
    centerMean d t ω = CenteringFlowLp.centeredMean (kernelData d) (d.sigma/2)
      (half_pos d.hsigma) t ω.1 + Gibbs.primitiveMean d.F d.x d.r := by
  change _ = (Conditional.conditionalMean d.F d.x d.r (backwardEnd d.G.R)
    (position d t ω)-Conditional.conditionalMean d.F d.x d.r 0 0)+_
  have h0 : Conditional.conditionalMean d.F d.x d.r 0 0=Gibbs.primitiveMean d.F d.x d.r := by
    simpa using (AffineFlowIdentities.conditionalMean_eq_primitiveMean d.hF d.hell d.hlo d.hup
      d.x d.hr (t := 0) (by norm_num) (by norm_num) (0:E))
  rw [h0,sub_add_cancel]
  rw [AffineFlowIdentities.conditionalMean_eq_primitiveMean d.hF d.hell d.hlo d.hup d.x
    d.hr (by linarith [d.G.backwardEnd_pos]) d.G.backwardEnd_lt_one,
    sqrt_backward_variance d]
  rfl

theorem centerMean_memLp (d : Data ι m) (t : ℝ) :
    MemLp (centerMean d t) 2 (seedMeasure d) := by
  have h := ((CenteringFlowLp.centeredMean_memLp (kernelData d) (d.sigma/2) (half_pos d.hsigma) t).comp_measurePreserving
    (phase_projection_preserving d)).add (memLp_const (Gibbs.primitiveMean d.F d.x d.r))
  have he : centerMean d t = fun ω => CenteringFlowLp.centeredMean (kernelData d)
      (d.sigma/2) (half_pos d.hsigma) t ω.1+Gibbs.primitiveMean d.F d.x d.r :=
    funext (centerMean_eq d t)
  rw [he]
  exact h

theorem backwardMean_eq (d : Data ι m) (j : Fin m) (t : ℝ) (ω : Seed d) :
    backwardMean d j t ω = TransportFlowLp.reply (transportData d) d.x
      ⟨backwardEnd d.G.R,d.G.backwardEnd_pos.le,le_rfl⟩ t
      (position d (centerNode j) ω) + Gibbs.primitiveMean d.F d.x d.r := by
  unfold TransportFlowLp.reply
  dsimp only [transportData]
  rw [sub_add_cancel]
  rw [AffineFlowIdentities.conditionalMean_eq_primitiveMean d.hF d.hell d.hlo d.hup d.x
    d.hr (by linarith [(SamplingFlowLp.sourceTime_mem d.G.backwardEnd_pos.le t).1])
    ((SamplingFlowLp.sourceTime_mem d.G.backwardEnd_pos.le t).2.trans_lt d.G.backwardEnd_lt_one)]
  rfl

theorem backwardMean_memLp (d : Data ι m) (j : Fin m) (t : ℝ) :
    MemLp (backwardMean d j t) 2 (seedMeasure d) := by
  have h := (TransportFlowLp.reply_memLp (transportData d) d.x
    ⟨backwardEnd d.G.R,d.G.backwardEnd_pos.le,le_rfl⟩ _
    (position_memLp d (centerNode j)) t).add (memLp_const (Gibbs.primitiveMean d.F d.x d.r))
  have he := funext (backwardMean_eq d j t)
  rw [he]
  exact h

theorem conditionalMean_eq (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (t : ℝ) (ω : Seed d) :
    conditionalMean d j k t ω = SamplingCenterLp.reply (conditionalData d k)
      (conditionalCenter d j k ω) t (ω.2 j k) +
      SamplingCenterLp.initialMean (conditionalData d k) (conditionalCenter d j k ω) := by
  change _ = (_-_)+_
  unfold SamplingCenterLp.initialMean
  rw [sub_add_cancel]
  rfl

theorem conditionalMean_memLp (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (t : ℝ) :
    MemLp (conditionalMean d j k t) 2 (seedMeasure d) := by
  have h := (SamplingCenterLp.reply_memLp (conditionalData d k) _ _
    (conditionalCenter_memLp d j k) (seed_noise_memLp d j k) t).add
    (SamplingCenterLp.initialMean_memLp (conditionalData d k) _ (conditionalCenter_memLp d j k))
  rw [funext (conditionalMean_eq d j k t)]
  exact h

theorem forwardMean_eq (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z t : ℝ) (ω : Seed d) :
    forwardMean d j k z t ω = TransportFlowLp.reply (transportData d) d.x
      ⟨d.G.rho k,(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩ t
      (rotation d j k z ω) + Gibbs.primitiveMean d.F d.x d.r := by
  unfold TransportFlowLp.reply
  dsimp only [transportData]
  rw [sub_add_cancel]
  rw [AffineFlowIdentities.conditionalMean_eq_primitiveMean d.hF d.hell d.hlo d.hup d.x
    d.hr (by linarith [(SamplingFlowLp.sourceTime_mem d.G.backwardEnd_pos.le t).1])
    ((SamplingFlowLp.sourceTime_mem d.G.backwardEnd_pos.le t).2.trans_lt d.G.backwardEnd_lt_one)]
  rfl

theorem forwardMean_memLp (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z t : ℝ) :
    MemLp (forwardMean d j k z t) 2 (seedMeasure d) := by
  have h := (TransportFlowLp.reply_memLp (transportData d) d.x
    ⟨d.G.rho k,(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩ _
    (rotation_memLp d j k z) t).add (memLp_const (Gibbs.primitiveMean d.F d.x d.r))
  rw [funext (forwardMean_eq d j k z t)]
  exact h

theorem action_memLp (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z : ℝ) :
    MemLp (action d j k z) 2 (seedMeasure d) :=
  (forward_memLp d j k z _).sub (rotation_memLp d j k z)

/-- All fields are derived on the actual product seed; no moment supplier is assumed. -/
theorem inventory (d : Data ι m) : Inventory d :=
  ⟨seed_position_memLp d,seed_score_memLp d,seed_noise_memLp d,memLp_const _,
    position_memLp d,score_memLp d,velocity_memLp d,backward_memLp d,conditional_memLp d,
    rotation_memLp d,forward_memLp d,kernel_memLp d,centerMean_memLp d,backwardMean_memLp d,
    conditionalMean_memLp d,forwardMean_memLp d,action_memLp d⟩

def offsetLp (d : Data ι m) : Lp E 2 (seedMeasure d) :=
  (memLp_const (Gibbs.primitiveMean d.F d.x d.r) : MemLp _ 2 (seedMeasure d)).toLp _
def positionLp (d : Data ι m) (t : ℝ) := (position_memLp d t).toLp (position d t)
def scoreLp (d : Data ι m) (t : ℝ) := (score_memLp d t).toLp (score d t)
def velocityLp (d : Data ι m) (t : ℝ) := (velocity_memLp d t).toLp (velocity d t)
def backwardLp (d : Data ι m) (j : Fin m) (t : ℝ) := (backward_memLp d j t).toLp (backward d j t)
def conditionalLp (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (t : ℝ) :=
  (conditional_memLp d j k t).toLp (conditional d j k t)
def rotationLp (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z : ℝ) :=
  (rotation_memLp d j k z).toLp (rotation d j k z)
def forwardLp (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z t : ℝ) :=
  (forward_memLp d j k z t).toLp (forward d j k z t)
def kernelLp (d : Data ι m) (j : Fin m) (t : ℝ) := (kernel_memLp d j t).toLp (kernel d j t)
def centerMeanLp (d : Data ι m) (t : ℝ) := (centerMean_memLp d t).toLp (centerMean d t)
def backwardMeanLp (d : Data ι m) (j : Fin m) (t : ℝ) :=
  (backwardMean_memLp d j t).toLp (backwardMean d j t)
def conditionalMeanLp (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (t : ℝ) :=
  (conditionalMean_memLp d j k t).toLp (conditionalMean d j k t)
def forwardMeanLp (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z t : ℝ) :=
  (forwardMean_memLp d j k z t).toLp (forwardMean d j k z t)
def actionLp (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z : ℝ) :=
  (action_memLp d j k z).toLp (action d j k z)
def phasePullback (d : Data ι m) :
    Lp E 2 (KernelFlowLp.seedMeasure (kernelData d)) →L[ℝ] Lp E 2 (seedMeasure d) :=
  (Lp.compMeasurePreservingₗᵢ (p := 2) ℝ (fun ω : Seed d => ω.1)
    (phase_projection_preserving d)).toContinuousLinearMap
def kernelPullback (d : Data ι m) (j : Fin m) :
    Lp E 2 (KernelFlowLp.seedMeasure (kernelData d)) →L[ℝ] Lp E 2 (seedMeasure d) :=
  (Lp.compMeasurePreservingₗᵢ (p := 2) ℝ (phase d (centerNode j))
    (kernel_phase_preserving d (centerNode j))).toContinuousLinearMap

theorem positionLp_eq (d : Data ι m) (t : ℝ) :
    positionLp d t = phasePullback d (CenteringFlowLp.positionLp (kernelData d)
      (d.sigma/2) (half_pos d.hsigma) t) := rfl
theorem scoreLp_eq (d : Data ι m) (t : ℝ) :
    scoreLp d t = phasePullback d (CenteringFlowLp.momentumLp (kernelData d)
      (d.sigma/2) (half_pos d.hsigma) t) := rfl
theorem velocityLp_eq (d : Data ι m) (t : ℝ) :
    velocityLp d t = -(d.sigma/2)⁻¹ • phasePullback d
      (CenteringFlowLp.kernelLp (kernelData d) (d.sigma/2) (half_pos d.hsigma) t) := by
  exact MemLp.toLp_const_smul (-(d.sigma/2)⁻¹)
    ((CenteringFlowLp.kernel_memLp (kernelData d) (d.sigma/2) (half_pos d.hsigma) t).comp_measurePreserving
      (phase_projection_preserving d))
theorem centerMeanLp_eq (d : Data ι m) (t : ℝ) :
    centerMeanLp d t = phasePullback d (CenteringFlowLp.centeredMeanLp (kernelData d)
      (d.sigma/2) (half_pos d.hsigma) t)+offsetLp d := by
  change (centerMean_memLp d t).toLp _ = _
  rw [offsetLp]
  change _ = (((CenteringFlowLp.centeredMean_memLp (kernelData d) (d.sigma/2) (half_pos d.hsigma) t).comp_measurePreserving
    (phase_projection_preserving d)).toLp _)+_
  rw [← MemLp.toLp_add]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall (centerMean_eq d t)
theorem kernelLp_eq (d : Data ι m) (j : Fin m) (t : ℝ) :
    kernelLp d j t = kernelPullback d j (KernelFlowLp.extensionLp (kernelData d) t) := by
  rw [← KernelFlowLp.extension_toLp]
  rfl

theorem backwardLp_eq (d : Data ι m) (j : Fin m) (t : ℝ) :
    backwardLp d j t = TransportFlowLp.flowLp (transportData d) d.x
      ⟨backwardEnd d.G.R,d.G.backwardEnd_pos.le,le_rfl⟩ _
      (position_memLp d (centerNode j)) t := rfl
theorem backwardMeanLp_eq (d : Data ι m) (j : Fin m) (t : ℝ) :
    backwardMeanLp d j t = TransportFlowLp.replyLp (transportData d) d.x
      ⟨backwardEnd d.G.R,d.G.backwardEnd_pos.le,le_rfl⟩ _
      (position_memLp d (centerNode j)) t+offsetLp d := by
  unfold backwardMeanLp TransportFlowLp.replyLp offsetLp
  rw [← MemLp.toLp_add]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall (backwardMean_eq d j t)
theorem conditionalLp_eq (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (t : ℝ) :
    conditionalLp d j k t = SamplingCenterLp.pathLp (conditionalData d k) _ _
      (conditionalCenter_memLp d j k) (seed_noise_memLp d j k) t := rfl
theorem conditionalMeanLp_eq (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (t : ℝ) :
    conditionalMeanLp d j k t = SamplingCenterLp.replyLp (conditionalData d k) _ _
      (conditionalCenter_memLp d j k) (seed_noise_memLp d j k) t +
      SamplingCenterLp.initialMeanLp (conditionalData d k) _ (conditionalCenter_memLp d j k) := by
  unfold conditionalMeanLp SamplingCenterLp.replyLp SamplingCenterLp.initialMeanLp
  rw [← MemLp.toLp_add]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall (conditionalMean_eq d j k t)
theorem forwardLp_eq (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z t : ℝ) :
    forwardLp d j k z t = TransportFlowLp.flowLp (transportData d) d.x
      ⟨d.G.rho k,(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩ _ (rotation_memLp d j k z) t := rfl
theorem forwardMeanLp_eq (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z t : ℝ) :
    forwardMeanLp d j k z t = TransportFlowLp.replyLp (transportData d) d.x
      ⟨d.G.rho k,(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩ _ (rotation_memLp d j k z) t+offsetLp d := by
  unfold forwardMeanLp TransportFlowLp.replyLp offsetLp
  rw [← MemLp.toLp_add]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall (forwardMean_eq d j k z t)
theorem actionLp_eq (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z : ℝ) :
    actionLp d j k z = forwardLp d j k z (backwardEnd d.G.R)-rotationLp d j k z :=
  MemLp.toLp_sub _ _

theorem continuous_positionLp (d : Data ι m) : Continuous (positionLp d) := by
  change Continuous (fun t => positionLp d t)
  simp_rw [positionLp_eq]
  exact (phasePullback d).continuous.comp (CenteringFlowLp.continuous_positionLp _ _ _)
theorem continuous_scoreLp (d : Data ι m) : Continuous (scoreLp d) := by
  change Continuous (fun t => scoreLp d t)
  simp_rw [scoreLp_eq]
  exact (phasePullback d).continuous.comp (CenteringFlowLp.continuous_momentumLp _ _ _)
theorem continuous_velocityLp (d : Data ι m) : Continuous (velocityLp d) := by
  change Continuous (fun t => velocityLp d t)
  simp_rw [velocityLp_eq]
  exact ((phasePullback d).continuous.comp (CenteringFlowLp.continuous_kernelLp _ _ _)).const_smul (-(d.sigma/2)⁻¹)
theorem continuous_centerMeanLp (d : Data ι m) : Continuous (centerMeanLp d) := by
  change Continuous (fun t => centerMeanLp d t)
  simp_rw [centerMeanLp_eq]
  exact ((phasePullback d).continuous.comp (CenteringFlowLp.continuous_centeredMeanLp _ _ _)).add continuous_const
theorem continuous_kernelLp (d : Data ι m) (j : Fin m) : Continuous (kernelLp d j) := by
  change Continuous (fun t => kernelLp d j t)
  simp_rw [kernelLp_eq]
  exact (kernelPullback d j).continuous.comp (KernelFlowLp.continuous_extensionLp _)
theorem continuous_backwardLp (d : Data ι m) (j : Fin m) : Continuous (backwardLp d j) := by
  change Continuous (fun t => backwardLp d j t)
  simp_rw [backwardLp_eq]
  exact TransportFlowLp.continuous_flowLp _ _ _ _ _
theorem continuous_backwardMeanLp (d : Data ι m) (j : Fin m) : Continuous (backwardMeanLp d j) := by
  change Continuous (fun t => backwardMeanLp d j t)
  simp_rw [backwardMeanLp_eq]
  exact (TransportFlowLp.continuous_replyLp _ _ _ _ _).add continuous_const
theorem continuous_conditionalLp (d : Data ι m) (j : Fin m) (k : d.G.Kernel) :
    Continuous (conditionalLp d j k) := by
  change Continuous (fun t => conditionalLp d j k t)
  simp_rw [conditionalLp_eq]
  exact SamplingCenterLp.continuous_pathLp _ _ _ _ _
theorem continuous_conditionalMeanLp (d : Data ι m) (j : Fin m) (k : d.G.Kernel) :
    Continuous (conditionalMeanLp d j k) := by
  change Continuous (fun t => conditionalMeanLp d j k t)
  simp_rw [conditionalMeanLp_eq]
  exact (SamplingCenterLp.continuous_replyLp _ _ _ _ _).add continuous_const

theorem rotationLp_eq (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z : ℝ) :
    rotationLp d j k z =
    let B := backwardLp d j (d.G.rho k)
    let H := d.G.rho k • B+(Real.sqrt (d.G.variance k)/conditionalEnd) • conditionalLp d j k conditionalEnd
    let mid := (d.G.rho k/(1+(d.G.rho k)^2)) • (H+d.G.rho k • B)
    mid+Real.cos (z/d.G.rotationScale k) • (B-mid)+
      (d.G.rotationScale k*Real.sin (z/d.G.rotationScale k)) • scoreLp d (centerNode j) := by
  dsimp only
  unfold rotationLp backwardLp conditionalLp scoreLp
  simp only [← MemLp.toLp_const_smul, ← MemLp.toLp_add, ← MemLp.toLp_sub]
  rfl

theorem continuous_rotationLp (d : Data ι m) (j : Fin m) (k : d.G.Kernel) :
    Continuous (rotationLp d j k) := by
  change Continuous (fun t => rotationLp d j k t)
  simp_rw [rotationLp_eq]
  apply Continuous.add
  · exact continuous_const.add ((Real.continuous_cos.comp (continuous_id.div_const _)).smul continuous_const)
  · exact (continuous_const.mul (Real.continuous_sin.comp (continuous_id.div_const _))).smul continuous_const

theorem continuous_forwardLp (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z : ℝ) :
    Continuous (forwardLp d j k z) := by
  change Continuous (fun t => forwardLp d j k z t)
  simp_rw [forwardLp_eq]
  exact TransportFlowLp.continuous_flowLp _ _ _ _ _
theorem continuous_forwardMeanLp (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z : ℝ) :
    Continuous (forwardMeanLp d j k z) := by
  change Continuous (fun t => forwardMeanLp d j k z t)
  simp_rw [forwardMeanLp_eq]
  exact (TransportFlowLp.continuous_replyLp _ _ _ _ _).add continuous_const

theorem positionLp_initial (d : Data ι m) :
    positionLp d 0 = (seed_position_memLp d).toLp (fun ω : Seed d => ω.1.fst) := by
  apply MemLp.toLp_congr
  filter_upwards [] with ω
  exact congrArg (fun q : Centering.Phase E => q.fst)
    (CenteringFlowLp.phase_initial (kernelData d) _ _ ω.1)
theorem scoreLp_initial (d : Data ι m) :
    scoreLp d 0 = (seed_score_memLp d).toLp (fun ω : Seed d => ω.1.snd) := by
  apply MemLp.toLp_congr
  filter_upwards [] with ω
  exact congrArg (fun q : Centering.Phase E => q.snd)
    (CenteringFlowLp.phase_initial (kernelData d) _ _ ω.1)
theorem backwardLp_initial (d : Data ι m) (j : Fin m) :
    backwardLp d j (backwardEnd d.G.R)=positionLp d (centerNode j) :=
  TransportFlowLp.flowLp_initial _ _ _ _ _
theorem conditionalLp_initial (d : Data ι m) (j : Fin m) (k : d.G.Kernel) :
    conditionalLp d j k 0 = (seed_noise_memLp d j k).toLp (fun ω : Seed d => ω.2 j k) := by
  apply MemLp.toLp_congr
  filter_upwards [] with ω
  change SamplingCenterLp.path (conditionalData d k) (conditionalCenter d j k ω) 0 (ω.2 j k)=ω.2 j k
  rw [← TransportFlowLp.flow_zero_start]
  exact TransportFlowLp.flow_initial (conditionalData d k) (conditionalCenter d j k ω)
    ⟨0,le_rfl,conditionalEnd_pos.le⟩ (ω.2 j k)
theorem forwardLp_initial (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z : ℝ) :
    forwardLp d j k z (d.G.rho k)=rotationLp d j k z :=
  TransportFlowLp.flowLp_initial _ _ _ _ _

theorem positionLp_equation (d : Data ι m) (a b : ℝ) :
    positionLp d b=positionLp d a+∫t in a..b,velocityLp d t := by
  have hh := congrArg (phasePullback d)
    (CenteringFlowLp.positionLp_sub (kernelData d) (d.sigma/2) (half_pos d.hsigma) a b)
  rw [map_sub,map_smul,← (phasePullback d).intervalIntegral_comp_comm
    ((CenteringFlowLp.continuous_kernelLp (kernelData d) _ _).intervalIntegrable a b)] at hh
  rw [positionLp_eq,positionLp_eq]
  simp_rw [velocityLp_eq]
  rw [intervalIntegral.integral_smul]
  exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)

theorem scoreLp_equation (d : Data ι m) (a b : ℝ) :
    scoreLp d b=scoreLp d a+(d.sigma/2)⁻¹ • ∫t in a..b,centerMeanLp d t-offsetLp d := by
  have hh := congrArg (phasePullback d)
    (CenteringFlowLp.momentumLp_sub (kernelData d) (d.sigma/2) (half_pos d.hsigma) a b)
  rw [map_sub,map_smul,← (phasePullback d).intervalIntegral_comp_comm
    ((CenteringFlowLp.continuous_centeredMeanLp (kernelData d) _ _).intervalIntegrable a b)] at hh
  rw [scoreLp_eq,scoreLp_eq]
  simp_rw [centerMeanLp_eq,add_sub_cancel_right]
  exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)

theorem backwardLp_equation (d : Data ι m) (j : Fin m) (a b : ℝ)
    (ha : a∈Icc 0 (backwardEnd d.G.R)) (hb : b∈Icc 0 (backwardEnd d.G.R)) :
    backwardLp d j b=backwardLp d j a-d.r • ∫t in a..b,backwardMeanLp d j t := by
  simp_rw [backwardMeanLp_eq]
  rw [intervalIntegral.integral_add
    ((TransportFlowLp.continuous_replyLp _ _ _ _ _).intervalIntegrable a b)
    (continuous_const.intervalIntegrable a b),intervalIntegral.integral_const,add_comm]
  exact TransportFlowLp.flowLp_eq_sub_integral _ _ _ _ _ a b ha hb

theorem conditionalLp_equation (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (a b : ℝ)
    (ha : a∈Icc 0 conditionalEnd) (hb : b∈Icc 0 conditionalEnd) :
    conditionalLp d j k b=conditionalLp d j k a-(conditionalData d k).r •
      ∫t in a..b,conditionalMeanLp d j k t := by
  simp_rw [conditionalMeanLp_eq]
  rw [intervalIntegral.integral_add
    ((SamplingCenterLp.continuous_replyLp _ _ _ _ _).intervalIntegrable a b)
    (continuous_const.intervalIntegrable a b),intervalIntegral.integral_const,add_comm]
  exact SamplingCenterLp.pathLp_eq_sub_integral _ _ _ _ _ a b ha hb

theorem forwardLp_equation (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z a b : ℝ)
    (ha : a∈Icc 0 (backwardEnd d.G.R)) (hb : b∈Icc 0 (backwardEnd d.G.R)) :
    forwardLp d j k z b=forwardLp d j k z a-d.r • ∫t in a..b,forwardMeanLp d j k z t := by
  simp_rw [forwardMeanLp_eq]
  rw [intervalIntegral.integral_add
    ((TransportFlowLp.continuous_replyLp _ _ _ _ _).intervalIntegrable a b)
    (continuous_const.intervalIntegrable a b),intervalIntegral.integral_const,add_comm]
  exact TransportFlowLp.flowLp_eq_sub_integral _ _ _ _ _ a b ha hb

theorem actionLp_equation (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z : ℝ) :
    actionLp d j k z = -d.r • ∫t in d.G.rho k..backwardEnd d.G.R,forwardMeanLp d j k z t := by
  rw [actionLp_eq,forwardLp_equation d j k z _ _
    ⟨(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩ ⟨d.G.backwardEnd_pos.le,le_rfl⟩,
    forwardLp_initial,sub_sub_cancel_left,neg_smul]

def integrandLp (d : Data ι m) (j : Fin m) (t : ℝ) :=
  kernelPullback d j (KernelFlowLp.integrandLp (kernelData d) t)
theorem continuous_integrandLp (d : Data ι m) (j : Fin m) : Continuous (integrandLp d j) :=
  (kernelPullback d j).continuous.comp (KernelFlowLp.continuous_integrandLp _)
theorem hasDerivAt_kernelLp (d : Data ι m) (j : Fin m) (t : ℝ) :
    HasDerivAt (kernelLp d j) ((d.r*t) • integrandLp d j t) t := by
  have hh := (kernelPullback d j).hasFDerivAt.comp_hasDerivAt t
    (KernelFlowLp.hasDerivAt_extensionLp (kernelData d) t)
  convert! hh using 1
  · exact funext (fun q => kernelLp_eq d j q)

theorem velocityLp_kernel_integral (d : Data ι m) (j : Fin m) :
    velocityLp d (centerNode j)=-(d.sigma/2)⁻¹ • ∫t in 0..backwardEnd d.G.R,integrandLp d j t := by
  have he : velocityLp d (centerNode j)=-(d.sigma/2)⁻¹ •
      kernelPullback d j (KernelFlowLp.kernelLp (kernelData d)) := by
    exact MemLp.toLp_const_smul (-(d.sigma/2)⁻¹)
      ((KernelFlowLp.kernel_memLp (kernelData d)).comp_measurePreserving
        (kernel_phase_preserving d (centerNode j)))
  rw [he,KernelFlowLp.kernelLp_eq_integral]
  erw [← (kernelPullback d j).intervalIntegral_comp_comm
      ((KernelFlowLp.continuous_integrandLp (kernelData d)).intervalIntegrable 0 (backwardEnd d.G.R))]
  rfl

theorem singular_kernel_ae (d : Data ι m) (j : Fin m) :
    (fun t => t⁻¹ • deriv (kernelLp d j) t) =ᵐ[volume] fun t => d.r • integrandLp d j t := by
  filter_upwards [volume.ae_ne (0:ℝ)] with t ht
  rw [(hasDerivAt_kernelLp d j t).deriv,smul_smul]
  congr 1
  field_simp

theorem velocityLp_singular_equation (d : Data ι m) (j : Fin m) :
    IntervalIntegrable (fun t => t⁻¹ • deriv (kernelLp d j) t) volume 0 (backwardEnd d.G.R) ∧
    velocityLp d (centerNode j)=-(d.r*(d.sigma/2))⁻¹ •
      ∫t in 0..backwardEnd d.G.R,t⁻¹ • deriv (kernelLp d j) t := by
  have hi := ((continuous_integrandLp d j).const_smul d.r).intervalIntegrable (μ := volume) 0 (backwardEnd d.G.R)
  have he := singular_kernel_ae d j
  refine ⟨hi.congr_ae (ae_restrict_of_ae he.symm),?_⟩
  rw [intervalIntegral.integral_congr_ae (he.mono (fun t ht _ => ht)),intervalIntegral.integral_smul,
    smul_smul,velocityLp_kernel_integral]
  congr 1
  field_simp [d.hr.ne',d.hsigma.ne']

/-- The literal midpoint uses the same backward and conditional replies as every row. -/
def midpoint (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (ω : Seed d) : E :=
  let B := backward d j (d.G.rho k) ω
  let H := d.G.rho k • B+(Real.sqrt (d.G.variance k)/conditionalEnd) • conditional d j k conditionalEnd ω
  (d.G.rho k/(1+(d.G.rho k)^2)) • (H+d.G.rho k • B)
theorem midpoint_memLp (d : Data ι m) (j : Fin m) (k : d.G.Kernel) :
    MemLp (midpoint d j k) 2 (seedMeasure d) :=
  ((((backward_memLp d j (d.G.rho k)).const_smul (d.G.rho k)).add
    ((conditional_memLp d j k conditionalEnd).const_smul (Real.sqrt (d.G.variance k)/conditionalEnd))).add
    ((backward_memLp d j (d.G.rho k)).const_smul (d.G.rho k))).const_smul
    (d.G.rho k/(1+(d.G.rho k)^2))

theorem rotation_eq_sourceRotation (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z : ℝ) (ω : Seed d) :
    rotation d j k z ω = AffineFlowIdentities.sourceRotation (backward d j (d.G.rho k) ω)
      (midpoint d j k ω) (score d (centerNode j) ω) (d.G.rotationScale k) z := rfl

theorem hasDerivAt_action (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (ω : Seed d) :
    HasDerivAt (fun z => action d j k z ω) (kernel d j (d.G.rho k) ω) 0 := by
  have hrho : d.G.rho k∈Icc 0 (backwardEnd d.G.R) :=
    ⟨(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩
  have h := AffineFlowIdentities.hasDerivAt_forward_displacement_rotation d.hF d.hell d.hlo d.hup
    d.x d.hr d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one hrho
    (position d (centerNode j) ω) (midpoint d j k ω) (score d (centerNode j) ω)
    (d.G.rotationScale_pos k).ne'
  have hB : backward d j (d.G.rho k) ω =
      Conditional.convexProbabilityFlow d.hF d.hell d.hlo d.hup d.x d.hr d.G.backwardEnd_pos.le
        (by norm_num) d.G.backwardEnd_lt_one ⟨backwardEnd d.G.R,d.G.backwardEnd_pos.le,le_rfl⟩
        (position d (centerNode j) ω) (d.G.rho k) :=
    TransportFlowLp.flow_eq (transportData d) d.x _ hrho _
  have he (z : ℝ) : action d j k z ω =
      Conditional.convexProbabilityFlow d.hF d.hell d.hlo d.hup d.x d.hr d.G.backwardEnd_pos.le
        (by norm_num) d.G.backwardEnd_lt_one ⟨d.G.rho k,hrho⟩
        (AffineFlowIdentities.sourceRotation
          (Conditional.convexProbabilityFlow d.hF d.hell d.hlo d.hup d.x d.hr d.G.backwardEnd_pos.le
            (by norm_num) d.G.backwardEnd_lt_one ⟨backwardEnd d.G.R,d.G.backwardEnd_pos.le,le_rfl⟩
            (position d (centerNode j) ω) (d.G.rho k))
          (midpoint d j k ω) (score d (centerNode j) ω) (d.G.rotationScale k) z)
        (backwardEnd d.G.R) -
        AffineFlowIdentities.sourceRotation
          (Conditional.convexProbabilityFlow d.hF d.hell d.hlo d.hup d.x d.hr d.G.backwardEnd_pos.le
            (by norm_num) d.G.backwardEnd_lt_one ⟨backwardEnd d.G.R,d.G.backwardEnd_pos.le,le_rfl⟩
            (position d (centerNode j) ω) (d.G.rho k))
          (midpoint d j k ω) (score d (centerNode j) ω) (d.G.rotationScale k) z := by
    unfold action forward
    rw [TransportFlowLp.flow_eq _ _ _ ⟨d.G.backwardEnd_pos.le,le_rfl⟩,
      rotation_eq_sourceRotation,hB]
  rw [show (fun z => action d j k z ω)=_ from funext he]
  change HasDerivAt _ (KernelFlowLp.extension (kernelData d) (d.G.rho k) (phase d (centerNode j) ω)) 0
  rw [KernelFlowLp.extension_eq_jacobian (kernelData d) hrho]
  exact h

omit [DecidableEq ι] in
private theorem norm_sourceRotation_sub_zero_le (B mid g : E) {q : ℝ} (hq : 0 < q) (z : ℝ) :
    ‖AffineFlowIdentities.sourceRotation B mid g q z-B‖ ≤
      |z| *(q⁻¹*‖B-mid‖+‖g‖) := by
  have he : AffineFlowIdentities.sourceRotation B mid g q z-B =
      (Real.cos (z/q)-1) • (B-mid)+(q*Real.sin (z/q)) • g := by
    unfold AffineFlowIdentities.sourceRotation
    module
  rw [he]
  have hc : |Real.cos (z/q)-1| ≤ |z| /q := by
    simpa [abs_div,abs_of_pos hq] using Real.abs_cos_sub_cos_le (z/q) 0
  have hs : |Real.sin (z/q)| ≤ |z| /q := by
    simpa [abs_div,abs_of_pos hq] using Real.abs_sin_sub_sin_le (z/q) 0
  calc
    _ ≤ ‖(Real.cos (z/q)-1) • (B-mid)‖+‖(q*Real.sin (z/q)) • g‖ := norm_add_le _ _
    _ = |Real.cos (z/q)-1| *‖B-mid‖+q* |Real.sin (z/q)| *‖g‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_pos hq]
    _ ≤ (|z| /q)*‖B-mid‖+q*(|z| /q)*‖g‖ := by gcongr
    _ = |z| *(q⁻¹*‖B-mid‖+‖g‖) := by field_simp

set_option backward.isDefEq.respectTransparency true
section LpDerivative
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
omit [DecidableEq ι] in
private theorem norm_sq_toLp {g : Ω → E} (hg : MemLp g 2 μ) :
    ‖hg.toLp g‖^2=∫ω,‖g ω‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with ω hω
  rw [hω,real_inner_self_eq_norm_sq]

omit [DecidableEq ι] in
/-- Dominated convergence of actual secants gives the ordinary L² derivative. -/
private theorem hasDerivAt_toLp_of_slope_bound (g : ℝ → Ω → E) (g' : Ω → E)
    (hm : ∀ z,MemLp (g z) 2 μ) (hm' : MemLp g' 2 μ)
    (hd : ∀ ω,HasDerivAt (fun z => g z ω) (g' ω) 0)
    (B : Ω → ℝ) (hB : MemLp B 2 μ)
    (hbound : ∀ z ω,‖slope (fun q => g q ω) 0 z‖≤B ω) :
    HasDerivAt (fun z => (hm z).toLp (g z)) (hm'.toLp g') 0 := by
  let S (z : ℝ) (ω : Ω) := slope (fun q => g q ω) 0 z
  have hS (z : ℝ) : MemLp (S z) 2 μ :=
    ((hm z).sub (hm 0)).const_smul ((z-0)⁻¹)
  have hlim : Filter.Tendsto (fun z => ∫ω,‖S z ω-g' ω‖^2 ∂μ)
      (nhdsWithin 0 {0}ᶜ) (nhds (0:ℝ)) := by
    have hh := tendsto_integral_filter_of_dominated_convergence
      (l := nhdsWithin (0:ℝ) {0}ᶜ) (F := fun z ω => ‖S z ω-g' ω‖^2)
      (f := fun _ => (0:ℝ)) (fun ω => (B ω+‖g' ω‖)^2)
      (Filter.Eventually.of_forall (fun z => ((hS z).aestronglyMeasurable.sub hm'.aestronglyMeasurable).norm.pow 2))
      (Filter.Eventually.of_forall (fun z => Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        have hb : ‖S z ω‖ ≤ B ω := hbound z ω
        have hn : ‖S z ω-g' ω‖ ≤ B ω+‖g' ω‖ := by
          linarith [norm_sub_le (S z ω) (g' ω)]
        exact pow_le_pow_left₀ (norm_nonneg (S z ω-g' ω)) hn 2)))
      ((hB.add hm'.norm).integrable_sq)
      (Filter.Eventually.of_forall (fun ω => by
        simpa [S] using (((hd ω).tendsto_slope.sub (tendsto_const_nhds (x := g' ω))).norm.pow 2)))
    simpa using hh
  have he (z : ℝ) : slope (fun q => (hm q).toLp (g q)) 0 z = (hS z).toLp (S z) := by
    rfl
  have heq (z : ℝ) : dist (slope (fun q => (hm q).toLp (g q)) 0 z) (hm'.toLp g') =
      Real.sqrt (∫ω,‖S z ω-g' ω‖^2 ∂μ) := by
    rw [he,dist_eq_norm,← MemLp.toLp_sub,← norm_sq_toLp]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  rw [hasDerivAt_iff_tendsto_slope,tendsto_iff_dist_tendsto_zero]
  simp_rw [heq]
  simpa [Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hlim
end LpDerivative

/-- A genuine L² secant dominator, derived from actual rotation and transport bounds. -/
def angleEnvelope (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (ω : Seed d) : ℝ :=
  (SamplingCenterLp.amplification (transportData d)+1)*
    ((d.G.rotationScale k)⁻¹*‖backward d j (d.G.rho k) ω-midpoint d j k ω‖+
      ‖score d (centerNode j) ω‖)
theorem angleEnvelope_memLp (d : Data ι m) (j : Fin m) (k : d.G.Kernel) :
    MemLp (angleEnvelope d j k) 2 (seedMeasure d) := by
  have hB := (backward_memLp d j (d.G.rho k)).sub (midpoint_memLp d j k)
  exact ((hB.norm.const_mul (d.G.rotationScale k)⁻¹).add
    (score_memLp d (centerNode j)).norm).const_mul
    (SamplingCenterLp.amplification (transportData d)+1)

theorem norm_action_slope_le (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z : ℝ) (ω : Seed d) :
    ‖slope (fun q => action d j k q ω) 0 z‖≤angleEnvelope d j k ω := by
  have hq := d.G.rotationScale_pos k
  have hrot := norm_sourceRotation_sub_zero_le (backward d j (d.G.rho k) ω)
    (midpoint d j k ω) (score d (centerNode j) ω) hq z
  have hzero : rotation d j k 0 ω=backward d j (d.G.rho k) ω := by
    rw [rotation_eq_sourceRotation,AffineFlowIdentities.sourceRotation_zero]
  have hr : ‖rotation d j k z ω-rotation d j k 0 ω‖ ≤
      |z| *((d.G.rotationScale k)⁻¹*‖backward d j (d.G.rho k) ω-midpoint d j k ω‖+
        ‖score d (centerNode j) ω‖) := by
    rw [hzero,rotation_eq_sourceRotation]
    exact hrot
  have ht := TransportFlowLp.flow_stability (transportData d) d.x
    ⟨d.G.rho k,(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩ (backwardEnd d.G.R)
    (rotation d j k z ω) (rotation d j k 0 ω)
  change ‖forward d j k z (backwardEnd d.G.R) ω-forward d j k 0 (backwardEnd d.G.R) ω‖≤_ at ht
  have he : action d j k z ω-action d j k 0 ω=
      (forward d j k z (backwardEnd d.G.R) ω-forward d j k 0 (backwardEnd d.G.R) ω)-
        (rotation d j k z ω-rotation d j k 0 ω) := by unfold action; abel
  have ha : ‖action d j k z ω-action d j k 0 ω‖≤|z| *angleEnvelope d j k ω := by
    rw [he]
    calc
      _ ≤ ‖forward d j k z (backwardEnd d.G.R) ω-forward d j k 0 (backwardEnd d.G.R) ω‖+
          ‖rotation d j k z ω-rotation d j k 0 ω‖ := norm_sub_le _ _
      _ ≤ (SamplingCenterLp.amplification (transportData d)+1)*
          ‖rotation d j k z ω-rotation d j k 0 ω‖ := by nlinarith
      _ ≤ (SamplingCenterLp.amplification (transportData d)+1)*
          (|z| *((d.G.rotationScale k)⁻¹*‖backward d j (d.G.rho k) ω-midpoint d j k ω‖+
          ‖score d (centerNode j) ω‖)) := mul_le_mul_of_nonneg_left hr (by
            unfold SamplingCenterLp.amplification; positivity)
      _ = |z| *angleEnvelope d j k ω := by unfold angleEnvelope; ring
  rw [slope,sub_zero,norm_smul,Real.norm_eq_abs,abs_inv]
  by_cases hz : z=0
  · subst z
    simp only [abs_zero,inv_zero,zero_mul]
    unfold angleEnvelope SamplingCenterLp.amplification
    positivity
  · exact (mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr (abs_nonneg z))).trans_eq
      (by rw [← mul_assoc,inv_mul_cancel₀ (abs_ne_zero.mpr hz),one_mul])

theorem hasDerivAt_actionLp (d : Data ι m) (j : Fin m) (k : d.G.Kernel) :
    HasDerivAt (actionLp d j k) (kernelLp d j (d.G.rho k)) 0 :=
  hasDerivAt_toLp_of_slope_bound _ _ (action_memLp d j k) (kernel_memLp d j (d.G.rho k))
    (hasDerivAt_action d j k) (angleEnvelope d j k) (angleEnvelope_memLp d j k)
    (norm_action_slope_le d j k)

/-- The common-space assembly constructs its moment inventory and all seven signed source
identities. All parameters are deterministic, and representative agreement is per time. -/
theorem assembly_target (d : Data ι m) : AssemblyTarget d := by
  refine ⟨inventory d,positionLp_initial d,scoreLp_initial d,backwardLp_initial d,
    conditionalLp_initial d,forwardLp_initial d,continuous_positionLp d,continuous_scoreLp d,
    continuous_velocityLp d,continuous_centerMeanLp d,?_,?_,?_,positionLp_equation d,
    scoreLp_equation d,backwardLp_equation d,conditionalLp_equation d,forwardLp_equation d,
    actionLp_equation d,hasDerivAt_actionLp d,velocityLp_singular_equation d⟩
  · intro j
    exact ⟨continuous_backwardLp d j,continuous_backwardMeanLp d j,continuous_kernelLp d j⟩
  · intro j k
    exact ⟨continuous_conditionalLp d j k,continuous_conditionalMeanLp d j k,continuous_rotationLp d j k⟩
  · intro j k z
    exact ⟨continuous_forwardLp d j k z,continuous_forwardMeanLp d j k z⟩

/-- Literal comparison with the earlier pointwise source construction. The source's chosen
smooth kernel and our canonical C¹ integral extension agree on the source slab only. -/
def SourceCorrespondence (d : Data ι m) (ω : Seed d)
    (C : AffineResidual.Mean.Curves d.G E) : Prop :=
  (∀ t,C.position t=position d t ω) ∧ (∀ t,C.score t=score d t ω) ∧
  (∀ t,C.velocity t=velocity d t ω) ∧
  (∀ j t,t∈Icc 0 (backwardEnd d.G.R) → C.backward j t=backward d j t ω) ∧
  (∀ j k t,t∈Icc 0 conditionalEnd → C.conditional j k t=conditional d j k t ω) ∧
  (∀ j k z,C.rotation d.G j k z=rotation d j k z ω) ∧
  (∀ j k z t,t∈Icc (d.G.rho k) (backwardEnd d.G.R) → C.forward j k z t=forward d j k z t ω) ∧
  (∀ j t,t∈Icc 0 (backwardEnd d.G.R) → C.kernel j t=kernel d j t ω)

theorem source_correspondence (d : Data ι m) (ω : Seed d)
    (C : AffineResidual.Mean.Curves d.G E)
    (h : AffineFlowIdentities.SourceMeanAgreement d.hF d.hell d.hlo d.hup d.x d.hr d.hsmall
      d.G d.hsigma ω.1.fst ω.1.snd ω.2 C) : SourceCorrespondence d ω C := by
  have hY (t : ℝ) : C.position t=position d t ω := h.position t
  have hG (t : ℝ) : C.score t=score d t ω := h.score t
  have hV (t : ℝ) : C.velocity t=velocity d t ω := h.velocity t
  have hB (j : Fin m) (t : ℝ) (ht : t∈Icc 0 (backwardEnd d.G.R)) :
      C.backward j t=backward d j t ω := by
    rw [h.backward j t ht,hY]
    exact (TransportFlowLp.flow_eq (transportData d) d.x _ ht _).symm
  have hD (j : Fin m) (k : d.G.Kernel) (t : ℝ) (ht : t∈Icc 0 conditionalEnd) :
      C.conditional j k t=conditional d j k t ω := by
    rw [h.conditional j k t ht,hB j (d.G.rho k) ⟨(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩]
    unfold conditional SamplingCenterLp.path SamplingFlowLp.sourcePath
    erw [SamplingFlowLp.sourceTime_eq conditionalEnd_pos.le ht]
    rfl
  have hW (j : Fin m) (k : d.G.Kernel) (z : ℝ) :
      C.rotation d.G j k z=rotation d j k z ω := by
    unfold AffineResidual.Mean.Curves.rotation rotation
    rw [hB j (d.G.rho k) ⟨(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩,
      hD j k conditionalEnd ⟨conditionalEnd_pos.le,le_rfl⟩,hG]
  refine ⟨hY,hG,hV,hB,hD,hW,?_,?_⟩
  · intro j k z t ht
    rw [h.forward j k z t ht,hW]
    exact (TransportFlowLp.flow_eq (transportData d) d.x _
      ⟨(d.G.rho_mem k).1.trans ht.1,ht.2⟩ _).symm
  · intro j t ht
    rw [h.kernel j t ht,hY,hG]
    exact (KernelFlowLp.extension_eq_jacobian (kernelData d) ht (phase d (centerNode j) ω)).symm

/-- The comparison object exists by the actual source construction; it is not an assembly premise. -/
theorem exists_source_correspondence (d : Data ι m) (ω : Seed d) :
    ∃ C : AffineResidual.Mean.Curves d.G E,
      AffineFlowIdentities.SourceMeanAgreement d.hF d.hell d.hlo d.hup d.x d.hr d.hsmall
        d.G d.hsigma ω.1.fst ω.1.snd ω.2 C ∧
      AffineResidual.Mean.Equations d.G C (Gibbs.primitiveMean d.F) d.r d.sigma d.x
        ω.1.fst ω.1.snd ω.2 ∧ SourceCorrespondence d ω C := by
  obtain ⟨C,hC,hE⟩ := AffineFlowIdentities.exists_sourceMeanCurves_equations d.hF d.hell d.hlo d.hup
    d.x d.hr d.hsmall d.G d.hsigma ω.1.fst ω.1.snd ω.2
  exact ⟨C,hC,hE,source_correspondence d ω C hC⟩

end AcceleratedLogConcave.Numerics.MeanFlowLp
