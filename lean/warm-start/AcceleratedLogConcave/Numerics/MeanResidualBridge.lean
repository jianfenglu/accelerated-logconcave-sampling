import AcceleratedLogConcave.Numerics.MeanFlowLp
import AcceleratedLogConcave.Numerics.AffineResidualRms
/-! Actual positive-radius primitive L² operator and literal mean residual receiver.
Higher-order regularity is required only for a supplied slab-equal kernel replacement. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory AcceleratedLogConcave Conditional
open Numerics Numerics.MeanFlowLp Numerics.AffineGraph Numerics.AffineGraph.MeanGeometry
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι
structure PrimitiveData (ι : Type*) [Fintype ι] where
  F : EuclideanSpace ℝ ι → ℝ
  hF : ContDiff ℝ 2 F
  ell : ℝ
  hell : 0 ≤ ell
  hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a
  hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell*‖a‖^2
  x : EuclideanSpace ℝ ι
variable {Ω : Type*} [MeasurableSpace Ω]
def PrimitiveSpec (p : PrimitiveData ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Lp E 2 μ → ℝ → Lp E 2 μ) : Prop :=
  (∀ q, q ≤ 0 → ∀ Z, U Z q=0) ∧
  AffineResidual.MeanRms.PrimitiveLpCorrespondence (Gibbs.primitiveMean p.F)
    (fun _ : Ω => p.x) U ∧
  (∀ q, 0 < q → LipschitzWith ⟨p.ell,p.hell⟩ (fun Z => U Z q)) ∧
  (∀ q, 0 < q → U 0 q=Lp.const 2 μ (Gibbs.primitiveMean p.F p.x q))
def PrimitiveLiftTarget (p : PrimitiveData ι) (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop :=
  ∃ U, PrimitiveSpec p μ U
def PrimitiveUniqueTarget (p : PrimitiveData ι) (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop :=
  ∀ U V, PrimitiveSpec p μ U → PrimitiveSpec p μ V → U=V

def primitiveData (d : Data ι m) : PrimitiveData ι :=
  ⟨d.F,d.hF,d.ell,d.hell,d.hlo,d.hup,d.x⟩
abbrev H (d : Data ι m) := Lp E 2 (seedMeasure d)
def initialPosition (d : Data ι m) : H d :=
  (seed_position_memLp d).toLp (fun ω : Seed d => ω.1.fst)
def initialScore (d : Data ι m) : H d :=
  (seed_score_memLp d).toLp (fun ω : Seed d => ω.1.snd)
def initialNoise (d : Data ι m) (j : Fin m) (k : d.G.Kernel) : H d :=
  (seed_noise_memLp d j k).toLp (fun ω : Seed d => ω.2 j k)
def curves (d : Data ι m) : AffineResidual.Mean.Curves d.G (H d) :=
  ⟨positionLp d,scoreLp d,velocityLp d,backwardLp d,conditionalLp d,forwardLp d,kernelLp d⟩
def rawCurves (d : Data ι m) (ω : Seed d) : AffineResidual.Mean.Curves d.G E :=
  ⟨fun t=>position d t ω,fun t=>score d t ω,fun t=>velocity d t ω,
    fun j t=>backward d j t ω,fun j k t=>conditional d j k t ω,
    fun j k z t=>MeanFlowLp.forward d j k z t ω,fun j t=>kernel d j t ω⟩
def FieldAgreement (d : Data ι m) (U : H d → ℝ → H d) : Prop :=
  U 0 d.r=offsetLp d ∧
  (∀ t,(curves d).centerMean d.G U 0 d.r t=centerMeanLp d t) ∧
  (∀ j t,t∈Icc 0 (backwardEnd d.G.R) →
    (curves d).backwardMean d.G U 0 d.r j t=backwardMeanLp d j t) ∧
  (∀ j k t,t∈Icc 0 conditionalEnd →
    (curves d).conditionalMean d.G U 0 d.r j k t=conditionalMeanLp d j k t) ∧
  (∀ j k z t,t∈Icc 0 (backwardEnd d.G.R) →
    (curves d).forwardMean d.G U 0 d.r j k z t=forwardMeanLp d j k z t) ∧
  (∀ j k z,(curves d).rotation d.G j k z=rotationLp d j k z) ∧
  (∀ j k z,(curves d).forwardAction d.G U 0 d.r j k z=actionLp d j k z)
def ReceiverTarget (d : Data ι m) : Prop :=
  ∃ U,PrimitiveSpec (primitiveData d) (seedMeasure d) U ∧ FieldAgreement d U ∧
    AffineResidual.Mean.Equations d.G (curves d) U d.r d.sigma 0
      (initialPosition d) (initialScore d) (initialNoise d)
def rawReference (d : Data ι m) (i : d.G.MeanNode) (ω : Seed d) : E :=
  (rawCurves d ω).reference d.G d.x d.r i
def rawResidual (d : Data ι m) (i : d.G.MeanNode) (ω : Seed d) : E :=
  (d.G.graph d.r d.sigma d.x ω.1.fst ω.1.snd ω.2).step (Gibbs.primitiveMean d.F)
    (fun j=>rawReference d j ω) i-rawReference d i ω
def lpResidual (d : Data ι m) (U : H d → ℝ → H d) (i : d.G.MeanNode) : H d :=
  (d.G.graph d.r d.sigma 0 (initialPosition d) (initialScore d) (initialNoise d)).step U
    ((curves d).reference d.G 0 d.r) i-(curves d).reference d.G 0 d.r i
/-- The reference and residual are the literal raw graph with the original shared seed. -/
def RawGraphTarget (d : Data ι m) : Prop :=
  ∀ U,PrimitiveSpec (primitiveData d) (seedMeasure d) U →
    (∀ i,rawReference d i =ᵐ[seedMeasure d]
      AffineResidual.MeanRms.rawReference d.G (fun _ : Seed d=>d.x) d.r (curves d) i) ∧
    (∀ i,rawResidual d i =ᵐ[seedMeasure d]
      AffineResidual.MeanRms.rawResidual d.G (Gibbs.primitiveMean d.F)
        (fun _ : Seed d=>d.x) d.r d.sigma (initialPosition d) (initialScore d)
        (initialNoise d) (curves d) i) ∧
    (∀ i,rawResidual d i =ᵐ[seedMeasure d] (lpResidual d U i : Seed d → E)) ∧
    (∀ i,MemLp (rawReference d i) 2 (seedMeasure d)) ∧
    (∀ i,MemLp (rawResidual d i) 2 (seedMeasure d))
/-- Two actual endpoint facts required by the residual receiver, without higher derivatives. -/
def KernelBoundaryTarget (d : Data ι m) : Prop :=
  (∀ j,deriv ((curves d).kernel j) 0=0) ∧
  (∀ j,(curves d).kernel j (backwardEnd d.G.R)=0)
def curvesWithKernel (d : Data ι m) (K : Fin m → ℝ → H d) : AffineResidual.Mean.Curves d.G (H d) :=
  { curves d with kernel := K }
def KernelAgreement (d : Data ι m) (K : Fin m → ℝ → H d) : Prop :=
  ∀ j t,t∈Icc 0 (backwardEnd d.G.R) → K j t=kernelLp d j t
/-- A slab-equal replacement preserves the equations. No endpoint derivative equality is assumed. -/
def KernelReplacementTarget (d : Data ι m) : Prop :=
  ∀ U,PrimitiveSpec (primitiveData d) (seedMeasure d) U →
  ∀ K,KernelAgreement d K →
    AffineResidual.Mean.Equations d.G (curvesWithKernel d K) U d.r d.sigma 0
      (initialPosition d) (initialScore d) (initialNoise d) ∧
    (curvesWithKernel d K).reference d.G 0 d.r=(curves d).reference d.G 0 d.r
/-- Higher-order regularity applies to a slab-equal replacement, not the clamped C¹ extension. -/
def ConditionalResidualTarget (d : Data ι m) : Prop :=
  ∃ U,PrimitiveSpec (primitiveData d) (seedMeasure d) U ∧
  ∀ (K : Fin m → ℝ → H d),KernelAgreement d K →
  ∀ (h₀ l v : ℝ) (D : AffineResidual.Mean.DerivativeBudget d.G),
    2 ≤ m → 0 ≤ h₀ → l < 0 → backwardEnd d.G.R < v →
    (∀ c,d.G.backward.length c ≤ 2*h₀*(1-(d.G.backward.right c)^2)) →
    AffineResidual.Mean.Regularity d.G (curvesWithKernel d K) U 0 d.r l v D →
    ∃ hres : ∀ i,MemLp (rawResidual d i) 2 (seedMeasure d),
      ∀ i,‖(hres i).toLp (rawResidual d i)‖≤D.rowError d.G d.r d.sigma h₀ i


section Primitive
omit [DecidableEq ι]
variable (p : PrimitiveData ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
def centeredPrimitive (q : ℝ) (z : E) : E :=
  Gibbs.primitiveMean p.F (p.x+z) q-Gibbs.primitiveMean p.F p.x q

theorem centeredPrimitive_zero (q : ℝ) : centeredPrimitive p q 0=0 := by
  simp [centeredPrimitive]

theorem centeredPrimitive_lipschitz {q : ℝ} (hq : 0<q) :
    LipschitzWith ⟨p.ell,p.hell⟩ (centeredPrimitive p q) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have h := (Gibbs.primitive_mean_lipschitz p.hF p.hell p.hlo p.hup hq).dist_le_mul (p.x+a) (p.x+b)
  simpa only [centeredPrimitive,dist_eq_norm,sub_sub_sub_cancel_right,
    add_sub_add_left_eq_sub] using h

def primitiveLp (Z : Lp E 2 μ) (q : ℝ) : Lp E 2 μ :=
  if hq : 0<q then
    (centeredPrimitive_lipschitz p hq).compLp (centeredPrimitive_zero p q) Z+
      Lp.const 2 μ (Gibbs.primitiveMean p.F p.x q)
  else 0

theorem primitiveLp_nonpositive {q : ℝ} (hq : q≤0) (Z : Lp E 2 μ) : primitiveLp p μ Z q=0 := by
  simp only [primitiveLp,dite_eq_right (not_lt.mpr hq)]

theorem primitiveLp_ae {q : ℝ} (hq : 0<q) (Z : Lp E 2 μ) :
    (primitiveLp p μ Z q : Ω → E)=ᵐ[μ] (fun ω=>Gibbs.primitiveMean p.F (p.x+Z ω) q) := by
  rw [primitiveLp,dite_eq_left hq]
  filter_upwards [(centeredPrimitive_lipschitz p hq).coeFn_compLp (centeredPrimitive_zero p q) Z,
    Lp.coeFn_const (μ := μ) (p := 2) (Gibbs.primitiveMean p.F p.x q),
    Lp.coeFn_add ((centeredPrimitive_lipschitz p hq).compLp (centeredPrimitive_zero p q) Z)
      (Lp.const 2 μ (Gibbs.primitiveMean p.F p.x q))] with ω h1 h2 h3
  rw [h3]
  simp only [Pi.add_apply]
  erw [h1,h2]
  simp only [Function.comp_apply,Function.const_apply,centeredPrimitive,sub_add_cancel]

theorem primitiveLp_lipschitz {q : ℝ} (hq : 0<q) :
    LipschitzWith ⟨p.ell,p.hell⟩ (fun Z=>primitiveLp p μ Z q) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [primitiveLp,dite_eq_left hq,dist_add_right]
  exact ((centeredPrimitive_lipschitz p hq).lipschitzWith_compLp
    (μ := μ) (p := 2) (centeredPrimitive_zero p q)).dist_le_mul a b

theorem primitiveLp_zero {q : ℝ} (hq : 0<q) :
    primitiveLp p μ 0 q=Lp.const 2 μ (Gibbs.primitiveMean p.F p.x q) := by
  rw [primitiveLp,dite_eq_left hq]
  erw [LipschitzWith.compLp_zero]
  exact zero_add _

theorem primitiveLp_spec : PrimitiveSpec p μ (primitiveLp p μ) :=
  ⟨fun _ h Z=>primitiveLp_nonpositive p μ h Z,fun Z _ h=>primitiveLp_ae p μ h Z,
    fun _ h=>primitiveLp_lipschitz p μ h,fun _ h=>primitiveLp_zero p μ h⟩

theorem primitiveLift : PrimitiveLiftTarget p μ := ⟨primitiveLp p μ,primitiveLp_spec p μ⟩

theorem primitiveUnique : PrimitiveUniqueTarget p μ := by
  intro U V hu hv
  funext Z q
  by_cases hq : 0<q
  · exact Lp.ext ((hu.2.1 Z q hq).trans (hv.2.1 Z q hq).symm)
  · rw [hu.1 q (le_of_not_gt hq),hv.1 q (le_of_not_gt hq)]
end Primitive


section Receiver
variable (d : Data ι m) (U : H d → ℝ → H d)
  (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)

omit [DecidableEq ι] in
private theorem coe_smul_ae {Z : H d} {f : Seed d → E} (h : (Z : Seed d → E)=ᵐ[seedMeasure d] f)
    (a : ℝ) : (a • Z : H d)=ᵐ[seedMeasure d] (fun ω=>a • f ω) := by
  filter_upwards [Lp.coeFn_smul a Z,h] with ω h1 h2
  simpa only [Pi.smul_apply,h2] using h1

omit [DecidableEq ι] in
private theorem coe_add_ae {Z W : H d} {f g : Seed d → E}
    (hZ : (Z : Seed d → E)=ᵐ[seedMeasure d] f)
    (hW : (W : Seed d → E)=ᵐ[seedMeasure d] g) :
    (Z+W : H d)=ᵐ[seedMeasure d] (fun ω=>f ω+g ω) := by
  filter_upwards [Lp.coeFn_add Z W,hZ,hW] with ω h1 h2 h3
  simpa only [Pi.add_apply,h2,h3] using h1

include hu
omit [DecidableEq ι] in
private theorem primitive_ae_of_ae {Z : H d} {f : Seed d → E}
    (h : (Z : Seed d → E)=ᵐ[seedMeasure d] f) {q : ℝ} (hq : 0<q) :
    (U Z q : Seed d → E)=ᵐ[seedMeasure d] (fun ω=>Gibbs.primitiveMean d.F (d.x+f ω) q) := by
  filter_upwards [hu.2.1 Z q hq,h] with ω h1 h2
  simpa only [primitiveData,h2] using h1

omit hu in
private theorem positive_radius {r b t : ℝ} (hr : 0<r) (hb : b<1)
    (ht : t∈Icc 0 b) : 0<r*Real.sqrt (1-t^2) :=
  mul_pos hr (Real.sqrt_pos.mpr (by nlinarith [ht.1,ht.2]))

omit [DecidableEq ι] in
theorem offset_eq : U 0 d.r=offsetLp d := by
  rw [hu.2.2.2 d.r d.hr]
  rfl

theorem centerMean_eq (t : ℝ) :
    (curves d).centerMean d.G U 0 d.r t=centerMeanLp d t := by
  simp only [AffineResidual.Mean.Curves.centerMean,zero_add,curves]
  exact Lp.ext ((primitive_ae_of_ae d U hu
    (coe_smul_ae d (position_memLp d t).coeFn_toLp (d.r*backwardEnd d.G.R))
    (mul_pos d.hr d.G.R_pos)).trans (centerMean_memLp d t).coeFn_toLp.symm)

theorem backwardMean_eq (j : Fin m) (t : ℝ) (ht : t∈Icc 0 (backwardEnd d.G.R)) :
    (curves d).backwardMean d.G U 0 d.r j t=backwardMeanLp d j t := by
  simp only [AffineResidual.Mean.Curves.backwardMean,zero_add,curves]
  apply Lp.ext
  have h := primitive_ae_of_ae d U hu
    (coe_smul_ae d (backward_memLp d j t).coeFn_toLp (d.r*t))
    (positive_radius d.hr d.G.backwardEnd_lt_one ht)
  filter_upwards [h,(backwardMean_memLp d j t).coeFn_toLp] with ω h1 h2
  erw [h1,h2]
  simp only [backwardMean,SamplingFlowLp.sourceTime_eq d.G.backwardEnd_pos.le ht]

theorem conditionalMean_eq (j : Fin m) (k : d.G.Kernel) (t : ℝ) (ht : t∈Icc 0 conditionalEnd) :
    (curves d).conditionalMean d.G U 0 d.r j k t=conditionalMeanLp d j k t := by
  simp only [AffineResidual.Mean.Curves.conditionalMean,zero_add,curves]
  apply Lp.ext
  have h := primitive_ae_of_ae d U hu
    (coe_add_ae d (coe_smul_ae d (backward_memLp d j (d.G.rho k)).coeFn_toLp (d.r*d.G.rho k))
      (coe_smul_ae d (conditional_memLp d j k t).coeFn_toLp (d.r*Real.sqrt (d.G.variance k)*t)))
    (positive_radius (mul_pos d.hr (Real.sqrt_pos.mpr (d.G.variance_pos k))) conditionalEnd_lt_one ht)
  filter_upwards [h,(conditionalMean_memLp d j k t).coeFn_toLp] with ω h1 h2
  erw [h1,h2]
  simp only [MeanFlowLp.conditionalMean,SamplingFlowLp.sourceTime_eq conditionalEnd_pos.le ht,
    conditionalData,conditionalCenter,add_assoc]

theorem forwardMean_eq (j : Fin m) (k : d.G.Kernel) (z t : ℝ)
    (ht : t∈Icc 0 (backwardEnd d.G.R)) :
    (curves d).forwardMean d.G U 0 d.r j k z t=forwardMeanLp d j k z t := by
  simp only [AffineResidual.Mean.Curves.forwardMean,zero_add,curves]
  apply Lp.ext
  have h := primitive_ae_of_ae d U hu
    (coe_smul_ae d (forward_memLp d j k z t).coeFn_toLp (d.r*t))
    (positive_radius d.hr d.G.backwardEnd_lt_one ht)
  filter_upwards [h,(forwardMean_memLp d j k z t).coeFn_toLp] with ω h1 h2
  erw [h1,h2]
  simp only [forwardMean,SamplingFlowLp.sourceTime_eq d.G.backwardEnd_pos.le ht]

omit hu in
theorem rotation_eq (j : Fin m) (k : d.G.Kernel) (z : ℝ) :
    (curves d).rotation d.G j k z=rotationLp d j k z :=
  (rotationLp_eq d j k z).symm

theorem forwardAction_eq (j : Fin m) (k : d.G.Kernel) (z : ℝ) :
    (curves d).forwardAction d.G U 0 d.r j k z=actionLp d j k z := by
  rw [AffineResidual.Mean.Curves.forwardAction,actionLp_equation]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (d.G.rho_mem k).2.le] at ht
  exact forwardMean_eq d U hu j k z t ⟨(d.G.rho_mem k).1.trans ht.1,ht.2⟩

theorem fieldAgreement : FieldAgreement d U :=
  ⟨offset_eq d U hu,centerMean_eq d U hu,backwardMean_eq d U hu,
    conditionalMean_eq d U hu,forwardMean_eq d U hu,rotation_eq d,forwardAction_eq d U hu⟩

theorem equations : AffineResidual.Mean.Equations d.G (curves d) U d.r d.sigma 0
    (initialPosition d) (initialScore d) (initialNoise d) := by
  constructor
  · intro a _
    exact (positionLp_equation d 0 a).trans (by rw [positionLp_initial]; rfl)
  · intro a _
    have h := scoreLp_equation d 0 a
    rw [scoreLp_initial] at h
    change scoreLp d a=initialScore d+(d.sigma/2)⁻¹ • ∫ t in 0..a,
      (curves d).centerMean d.G U 0 d.r t-U 0 d.r
    simp_rw [centerMean_eq d U hu,offset_eq d U hu]
    exact h
  · intro j a ha
    have h := backwardLp_equation d j (backwardEnd d.G.R) a ⟨d.G.backwardEnd_pos.le,le_rfl⟩ ha
    rw [backwardLp_initial] at h
    change backwardLp d j a=positionLp d (centerNode j)-d.r • _
    rw [h]
    congr 2
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t∈Icc 0 (backwardEnd d.G.R) :=
      ⟨le_trans ha.1 ((uIcc_of_ge ha.2 ▸ ht).1),(uIcc_of_ge ha.2 ▸ ht).2⟩
    exact (backwardMean_eq d U hu j t ht').symm
  · intro j k t ht
    have h := conditionalLp_equation d j k 0 t ⟨le_rfl,conditionalEnd_pos.le⟩ ht
    rw [conditionalLp_initial] at h
    change conditionalLp d j k t=initialNoise d j k-(d.r*Real.sqrt (d.G.variance k)) • _
    rw [h]
    congr 2
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact (conditionalMean_eq d U hu j k s ⟨hs.1,hs.2.trans ht.2⟩).symm
  · intro j k z a _ ha
    have h := forwardLp_equation d j k z (d.G.rho k) a
      ⟨(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩ ⟨(d.G.rho_mem k).1.trans ha.1,ha.2⟩
    rw [forwardLp_initial] at h
    change forwardLp d j k z a=(curves d).rotation d.G j k z-d.r • _
    rw [rotation_eq,h]
    congr 2
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le ha.1] at ht
    exact (forwardMean_eq d U hu j k z t ⟨(d.G.rho_mem k).1.trans ht.1,ht.2.trans ha.2⟩).symm
  · intro j k
    change kernelLp d j (d.G.rho k)=_
    have he : (curves d).forwardAction d.G U 0 d.r j k=actionLp d j k :=
      funext (forwardAction_eq d U hu j k)
    rw [he]
    exact (hasDerivAt_actionLp d j k).deriv.symm
  · intro j
    exact (velocityLp_singular_equation d j).2

omit hu in
theorem receiver : ReceiverTarget d :=
  ⟨primitiveLp (primitiveData d) (seedMeasure d),primitiveLp_spec _ _,
    fieldAgreement d _ (primitiveLp_spec _ _),equations d _ (primitiveLp_spec _ _)⟩
end Receiver


section Raw
variable (d : Data ι m)

theorem rawReference_ae (i : d.G.MeanNode) :
    rawReference d i =ᵐ[seedMeasure d]
      AffineResidual.MeanRms.rawReference d.G (fun _ : Seed d=>d.x) d.r (curves d) i := by
  rcases i with _ | j | ⟨j,k⟩ | ⟨j,⟨k,n⟩⟩ | ⟨j,⟨k,z,n⟩⟩
  · filter_upwards [Lp.coeFn_zero E 2 (seedMeasure d)] with ω h
    simp only [rawReference,AffineResidual.MeanRms.rawReference,
      AffineResidual.Mean.Curves.reference,h,Pi.zero_apply,add_zero]
  · have h := coe_smul_ae d (position_memLp d (centerNode j)).coeFn_toLp (d.r*backwardEnd d.G.R)
    filter_upwards [h] with ω hω
    simpa only [rawReference,rawCurves,AffineResidual.MeanRms.rawReference,
      AffineResidual.Mean.Curves.reference,curves,zero_add,positionLp] using
      (congrArg (fun y=>d.x+y) hω).symm
  · have h := coe_smul_ae d (backward_memLp d j (d.G.backward.location m k)).coeFn_toLp
      (d.r*d.G.backward.location m k)
    filter_upwards [h] with ω hω
    simpa only [rawReference,rawCurves,AffineResidual.MeanRms.rawReference,
      AffineResidual.Mean.Curves.reference,curves,zero_add,backwardLp] using
      (congrArg (fun y=>d.x+y) hω).symm
  · have h := coe_add_ae d
      (coe_smul_ae d (backward_memLp d j (d.G.rho k)).coeFn_toLp (d.r*d.G.rho k))
      (coe_smul_ae d (conditional_memLp d j k ((d.G.conditional k).location m n)).coeFn_toLp
        (d.r*Real.sqrt (d.G.variance k)*(d.G.conditional k).location m n))
    filter_upwards [h] with ω hω
    simpa only [rawReference,rawCurves,AffineResidual.MeanRms.rawReference,
      AffineResidual.Mean.Curves.reference,curves,zero_add,add_assoc,backwardLp,conditionalLp] using
      (congrArg (fun y=>d.x+y) hω).symm
  · have h := coe_smul_ae d
      (forward_memLp d j k (d.G.angleNode z) ((d.G.forward k).location m n)).coeFn_toLp
      (d.r*(d.G.forward k).location m n)
    filter_upwards [h] with ω hω
    simpa only [rawReference,rawCurves,AffineResidual.MeanRms.rawReference,
      AffineResidual.Mean.Curves.reference,curves,zero_add,forwardLp] using
      (congrArg (fun y=>d.x+y) hω).symm

theorem rawResidual_ae_receiver (i : d.G.MeanNode) :
    rawResidual d i =ᵐ[seedMeasure d]
      AffineResidual.MeanRms.rawResidual d.G (Gibbs.primitiveMean d.F)
        (fun _ : Seed d=>d.x) d.r d.sigma (initialPosition d) (initialScore d)
        (initialNoise d) (curves d) i := by
  have hy : (initialPosition d : Seed d → E)=ᵐ[seedMeasure d] (fun ω=>ω.1.fst) :=
    (seed_position_memLp d).coeFn_toLp
  have hg : (initialScore d : Seed d → E)=ᵐ[seedMeasure d] (fun ω=>ω.1.snd) :=
    (seed_score_memLp d).coeFn_toLp
  have hn : ∀ᵐ ω ∂seedMeasure d,∀ j k,initialNoise d j k ω=ω.2 j k :=
    ae_all_iff.mpr fun j=>ae_all_iff.mpr fun k=>(seed_noise_memLp d j k).coeFn_toLp
  have hr := ae_all_iff.mpr (rawReference_ae d)
  filter_upwards [hy,hg,hn,hr] with ω hy hg hn hr
  have hne : (fun j k=>initialNoise d j k ω)=ω.2 := funext fun j=>funext (hn j)
  have hre : (fun j=>rawReference d j ω)=
      (fun j=>AffineResidual.MeanRms.rawReference d.G (fun _ : Seed d=>d.x) d.r (curves d) j ω) :=
    funext hr
  simp only [rawResidual,AffineResidual.MeanRms.rawResidual,hy,hg,hne,hre,hr i]

theorem rawResidual_ae_lp (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U) (i : d.G.MeanNode) :
    rawResidual d i =ᵐ[seedMeasure d] (lpResidual d U i : Seed d → E) :=
  (rawResidual_ae_receiver d i).trans
    (AffineResidual.MeanRms.rawResidual_ae d.G (Gibbs.primitiveMean d.F) (fun _ : Seed d=>d.x)
      d.r d.sigma d.hr U (initialPosition d) (initialScore d) (initialNoise d) (curves d) hu.2.1 i)

theorem rawReference_memLp (i : d.G.MeanNode) : MemLp (rawReference d i) 2 (seedMeasure d) :=
  ((memLp_const d.x).add (Lp.memLp ((curves d).reference d.G 0 d.r i))).ae_eq
    (rawReference_ae d i).symm

theorem rawResidual_memLp (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U) (i : d.G.MeanNode) :
    MemLp (rawResidual d i) 2 (seedMeasure d) :=
  (Lp.memLp (lpResidual d U i)).ae_eq (rawResidual_ae_lp d U hu i).symm

theorem rawGraph : RawGraphTarget d :=
  fun U hu=>⟨rawReference_ae d,rawResidual_ae_receiver d,rawResidual_ae_lp d U hu,
    rawReference_memLp d,rawResidual_memLp d U hu⟩
end Raw

section KernelReplacement
variable (d : Data ι m)

theorem kernelBoundary : KernelBoundaryTarget d := by
  constructor
  · intro j
    change deriv (kernelLp d j) 0=0
    rw [(hasDerivAt_kernelLp d j 0).deriv]
    simp
  · intro j
    apply Lp.ext
    filter_upwards [(kernel_memLp d j (backwardEnd d.G.R)).coeFn_toLp,
      Lp.coeFn_zero E 2 (seedMeasure d)] with ω h1 h2
    erw [h1,h2]
    exact KernelFlowLp.extension_terminal (kernelData d) (phase d (centerNode j) ω)

theorem kernel_deriv_eq_interior (K : Fin m → ℝ → H d) (hK : KernelAgreement d K)
    (j : Fin m) {t : ℝ} (ht : t∈Ioo 0 (backwardEnd d.G.R)) :
    deriv (K j) t=deriv (kernelLp d j) t := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with q hq
  exact hK j q hq

theorem kernelReplacement : KernelReplacementTarget d := by
  intro U hu K hK
  have h := equations d U hu
  refine ⟨?_,rfl⟩
  refine ⟨h.position,h.score,h.backward,h.conditional,h.forward,?_,?_⟩
  · intro j k
    change K j (d.G.rho k)=_
    rw [hK j (d.G.rho k) ⟨(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩]
    exact h.kernel_angle j k
  · intro j
    change velocityLp d (centerNode j)=-(d.r*(d.sigma/2))⁻¹ •
      ∫t in 0..backwardEnd d.G.R,t⁻¹ • deriv (K j) t
    rw [(velocityLp_singular_equation d j).2]
    congr 1
    apply intervalIntegral.integral_congr_Ioo_of_le d.G.backwardEnd_pos.le
    intro t ht
    exact congrArg (fun w=>t⁻¹ • w) (kernel_deriv_eq_interior d K hK j ht).symm

theorem conditionalResidual : ConditionalResidualTarget d := by
  let U := primitiveLp (primitiveData d) (seedMeasure d)
  have hu := primitiveLp_spec (primitiveData d) (seedMeasure d)
  refine ⟨U,hu,?_⟩
  intro K hK h₀ l v D hm hh₀ hl hv hmesh hreg
  have he := (kernelReplacement d U hu K hK).1
  obtain ⟨hres,hbound⟩ := AffineResidual.MeanRms.meanResidual d.G hm d.r d.sigma h₀ l v
    d.hr d.hsigma hh₀ hl hv hmesh (Gibbs.primitiveMean d.F) (fun _ : Seed d=>d.x)
    U (initialPosition d) (initialScore d) (initialNoise d) (curvesWithKernel d K) D hu.2.1 he hreg
  have hr (i : d.G.MeanNode) : rawResidual d i =ᵐ[seedMeasure d]
      AffineResidual.MeanRms.rawResidual d.G (Gibbs.primitiveMean d.F)
        (fun _ : Seed d=>d.x) d.r d.sigma (initialPosition d) (initialScore d)
        (initialNoise d) (curvesWithKernel d K) i := rawResidual_ae_receiver d i
  let hmemb (i : d.G.MeanNode) := (hres i).ae_eq (hr i).symm
  refine ⟨hmemb,?_⟩
  intro i
  have heq : (hmemb i).toLp (rawResidual d i)=(hres i).toLp _ :=
    MemLp.toLp_congr (hmemb i) (hres i) (hr i)
  rw [heq]
  exact hbound i
end KernelReplacement

end AcceleratedLogConcave.Numerics.MeanResidualBridge
