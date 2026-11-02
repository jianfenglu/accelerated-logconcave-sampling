import AcceleratedLogConcave.Numerics.SamplingCenterLp
/-! Actual two-sided arbitrary-start probability flow and its canonical L² lift. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory AcceleratedLogConcave Conditional
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AcceleratedLogConcave.Numerics.TransportFlowLp
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
abbrev Data := SamplingCenterLp.Data

def flow (d : Data ι) (x : E) (s : Icc (0 : ℝ) d.b) (t : ℝ) (p : E) : E :=
  convexProbabilityFlow d.hF d.hell d.hlo d.hup x d.hr d.hb
    (by norm_num) d.hb1 s p (SamplingFlowLp.sourceTime d.hb t)
def reply (d : Data ι) (x : E) (s : Icc (0 : ℝ) d.b) (t : ℝ) (p : E) : E :=
  conditionalMean d.F x d.r (SamplingFlowLp.sourceTime d.hb t)
    (flow d x s t p) - Gibbs.primitiveMean d.F x d.r

theorem flow_eq (d : Data ι) (x : E) (s : Icc (0 : ℝ) d.b)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) (p : E) :
    flow d x s t p = convexProbabilityFlow d.hF d.hell d.hlo d.hup x d.hr d.hb
      (by norm_num) d.hb1 s p t := by
  rw [flow,SamplingFlowLp.sourceTime_eq d.hb ht]

theorem flow_initial (d : Data ι) (x : E) (s : Icc (0 : ℝ) d.b) (p : E) :
    flow d x s s p=p := by
  rw [flow_eq d x s s.property]
  exact convexProbabilityFlow_initial d.hF d.hell d.hlo d.hup x d.hr d.hb
    (by norm_num) d.hb1 s p

theorem flow_cocycle (d : Data ι) (x : E) (s t u : Icc (0 : ℝ) d.b) (p : E) :
    flow d x t u (flow d x s t p)=flow d x s u p := by
  simp only [flow_eq d x t u.property,flow_eq d x s t.property,flow_eq d x s u.property]
  exact convexProbabilityFlow_cocycle d.hF d.hell d.hlo d.hup x d.hr d.hb
    (by norm_num) d.hb1 s t u p

theorem flow_zero_start (d : Data ι) (x : E) (t : ℝ) (p : E) :
    flow d x ⟨0,le_rfl,d.hb⟩ t p=SamplingCenterLp.path d x t p := rfl

theorem flow_eq_path (d : Data ι) (x : E) (s : Icc (0 : ℝ) d.b) (t : ℝ) (p : E) :
    flow d x s t p=SamplingCenterLp.path d x t (flow d x s 0 p) := by
  have h := convexProbabilityFlow_cocycle d.hF d.hell d.hlo d.hup x d.hr d.hb
    (by norm_num) d.hb1 s ⟨0,le_rfl,d.hb⟩ (projIcc 0 d.b d.hb t) p
  rw [flow_eq d x s ⟨le_rfl,d.hb⟩]
  exact h.symm

theorem reply_eq_reply (d : Data ι) (x : E) (s : Icc (0 : ℝ) d.b) (t : ℝ) (p : E) :
    reply d x s t p=SamplingCenterLp.reply d x t (flow d x s 0 p) := by
  rw [SamplingCenterLp.reply,SamplingFlowLp.centeredReply_eq_conditionalMean]
  rw [reply,flow_eq_path]
  rfl

theorem lipschitzWith_flow (d : Data ι) (x : E) (s : Icc (0 : ℝ) d.b) (t : ℝ) :
    LipschitzWith ⟨SamplingCenterLp.amplification d,(Real.exp_pos _).le⟩ (flow d x s t) := by
  have h := OAI.LogConcaveSampling.GlobalODE.flow_lipschitz
    (fun u (_hu : u ∈ Icc 0 d.b) => Conditional.clippedProbabilityVelocity_lipschitz d.hb d.r
      (fun v hv => Conditional.lipschitzWith_conditionalMean d.hF d.hell d.hlo d.hup x d.hr
        (by linarith [hv.1]) (hv.2.trans_lt d.hb1)) u)
    (Conditional.clippedProbabilityVelocity_continuous d.hb d.r
      (Conditional.continuousOn_conditionalMean d.hF d.hlo d.hup x d.r
        (a := 0) (b := d.b) (by norm_num) d.hb1)) s (projIcc 0 d.b d.hb t)
  change LipschitzWith _ (flow d x s t) at h
  apply h.weaken
  change Real.exp ((‖d.r‖*(d.r*d.ell))*|SamplingFlowLp.sourceTime d.hb t-(s:ℝ)|) ≤ _
  rw [Real.norm_eq_abs,abs_of_pos d.hr]
  apply Real.exp_le_exp.mpr
  have hs := s.property
  have ht := SamplingFlowLp.sourceTime_mem d.hb t
  have hab : |SamplingFlowLp.sourceTime d.hb t-(s:ℝ)| ≤ d.b := abs_le.mpr ⟨by linarith [hs.2,ht.1],by linarith [hs.1,ht.2]⟩
  have hle := mul_le_mul_of_nonneg_left hab (mul_nonneg (sq_nonneg d.r) d.hell)
  change _ ≤ d.r^2*d.ell*d.b
  nlinarith

theorem flow_stability (d : Data ι) (x : E) (s : Icc (0 : ℝ) d.b) (t : ℝ) (p q : E) :
    ‖flow d x s t p-flow d x s t q‖ ≤ SamplingCenterLp.amplification d*‖p-q‖ :=
  (lipschitzWith_flow d x s t).norm_sub_le p q

theorem continuous_flow (d : Data ι) (x : E) (s : Icc (0 : ℝ) d.b) :
    Continuous (fun v : ℝ × E => flow d x s v.1 v.2) := by
  have heq : (fun v : ℝ × E => flow d x s v.1 v.2) =
      (fun v : ℝ × E => SamplingCenterLp.path d x v.1 (flow d x s 0 v.2)) :=
    funext (fun v => flow_eq_path d x s v.1 v.2)
  rw [heq]
  exact (SamplingCenterLp.continuous_path d).comp
    (f := fun v : ℝ × E => (v.1,(x,flow d x s 0 v.2)))
    (continuous_fst.prodMk (continuous_const.prodMk
      ((lipschitzWith_flow d x s 0).continuous.comp continuous_snd)))

theorem continuous_reply (d : Data ι) (x : E) (s : Icc (0 : ℝ) d.b) :
    Continuous (fun v : ℝ × E => reply d x s v.1 v.2) := by
  have hc := (Conditional.continuousOn_conditionalMean d.hF d.hlo d.hup x d.r
    (by norm_num : (-1:ℝ)<0) d.hb1).comp_continuous
    (((SamplingFlowLp.continuous_sourceTime d.hb).comp continuous_fst).prodMk
      (continuous_flow d x s))
    (fun v => ⟨SamplingFlowLp.sourceTime_mem d.hb v.1,mem_univ _⟩)
  exact hc.sub continuous_const

theorem reply_stability (d : Data ι) (x : E) (s : Icc (0 : ℝ) d.b)
    (t : ℝ) (p q : E) :
    ‖reply d x s t p-reply d x s t q‖ ≤
      (d.r*d.b*d.ell*SamplingCenterLp.amplification d)*‖p-q‖ := by
  let τ := SamplingFlowLp.sourceTime d.hb t
  have hτ := SamplingFlowLp.sourceTime_mem d.hb t
  have htlo : -1 < τ := by linarith [hτ.1]
  have hthi : τ < 1 := hτ.2.trans_lt d.hb1
  have hrad : 0 < d.r*Real.sqrt (1-τ^2) := mul_pos d.hr (Real.sqrt_pos.mpr (by nlinarith))
  have hu := (Gibbs.primitive_mean_lipschitz d.hF d.hell d.hlo d.hup hrad).norm_sub_le
    (x+(d.r*τ) • flow d x s t p) (x+(d.r*τ) • flow d x s t q)
  have heq : reply d x s t p-reply d x s t q =
      Gibbs.primitiveMean d.F (x+(d.r*τ) • flow d x s t p) (d.r*Real.sqrt (1-τ^2)) -
      Gibbs.primitiveMean d.F (x+(d.r*τ) • flow d x s t q) (d.r*Real.sqrt (1-τ^2)) := by
    simp only [reply,sub_sub_sub_cancel_right]
    rw [AffineFlowIdentities.conditionalMean_eq_primitiveMean d.hF d.hell d.hlo d.hup x d.hr htlo hthi,
      AffineFlowIdentities.conditionalMean_eq_primitiveMean d.hF d.hell d.hlo d.hup x d.hr htlo hthi]
  rw [heq]
  simp only [add_sub_add_left_eq_sub,← smul_sub,norm_smul,Real.norm_eq_abs] at hu
  rw [abs_of_nonneg (show 0 ≤ d.r*τ from mul_nonneg d.hr.le hτ.1)] at hu
  have hcoef := mul_le_mul_of_nonneg_left hτ.2 d.hr.le
  have h1 := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hcoef (norm_nonneg (flow d x s t p-flow d x s t q))) d.hell
  have h2 := mul_le_mul_of_nonneg_left (flow_stability d x s t p q)
    (mul_nonneg (mul_nonneg d.hr.le d.hb) d.hell)
  change _ ≤ d.ell*((d.r*τ)*‖flow d x s t p-flow d x s t q‖) at hu
  nlinarith

theorem uniform_affine_envelopes (d : Data ι) (x : E) (s : Icc (0 : ℝ) d.b) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (t : ℝ) (p : E),
      ‖flow d x s t p‖ ≤ A+SamplingCenterLp.amplification d*‖p‖ ∧
      ‖reply d x s t p‖ ≤ B+
        (d.r*d.b*d.ell*SamplingCenterLp.amplification d)*‖p‖ := by
  obtain ⟨A,B,C,hA,hB,hC,hh⟩ := SamplingCenterLp.uniform_affine_envelopes d
  let D := C*(‖x‖+‖flow d x s 0 0‖)
  have hD : 0 ≤ D := mul_nonneg hC (add_nonneg (norm_nonneg x) (norm_nonneg _))
  refine ⟨A+D,B+D,add_nonneg hA hD,add_nonneg hB hD,?_⟩
  intro t p
  have hY0 : ‖flow d x s t 0‖ ≤ A+D := by
    rw [flow_eq_path];exact (hh x t (flow d x s 0 0)).1
  have hQ0 : ‖reply d x s t 0‖ ≤ B+D := by
    rw [reply_eq_reply];exact (hh x t (flow d x s 0 0)).2
  have hy := flow_stability d x s t p 0
  have hq := reply_stability d x s t p 0
  simp only [sub_zero] at hy hq
  have hy' := norm_add_le (flow d x s t p-flow d x s t 0) (flow d x s t 0)
  have hq' := norm_add_le (reply d x s t p-reply d x s t 0) (reply d x s t 0)
  rw [sub_add_cancel] at hy' hq'
  constructor <;> linarith

theorem flow_eq_sub_integral (d : Data ι) (x : E) (s : Icc (0 : ℝ) d.b)
    (u v : ℝ) (hu : u ∈ Icc 0 d.b) (hv : v ∈ Icc 0 d.b) (p : E) :
    flow d x s v p = flow d x s u p-d.r •
      ((v-u) • Gibbs.primitiveMean d.F x d.r+∫ t in u..v,reply d x s t p) := by
  rw [flow_eq_path d x s v p,flow_eq_path d x s u p]
  simp_rw [reply_eq_reply]
  exact SamplingFlowLp.sourcePath_eq_sub_integral d.hF d.hell d.hlo d.hup x d.hr
    d.hb d.hb1 u v hu hv (flow d x s 0 p)

section RandomInputs
variable (d : Data ι) (x : EuclideanSpace ℝ ι) (s : Icc (0 : ℝ) d.b)
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (P : Ω → EuclideanSpace ℝ ι) (hP : MemLp P 2 μ)
include hP

theorem rewound_memLp : MemLp (fun ω => flow d x s 0 (P ω)) 2 μ := by
  obtain ⟨A,B,hA,hB,hh⟩ := uniform_affine_envelopes d x s
  apply ((memLp_const A).add (hP.norm.const_mul (SamplingCenterLp.amplification d))).mono'
    ((lipschitzWith_flow d x s 0).continuous.comp_aestronglyMeasurable hP.aestronglyMeasurable)
  filter_upwards [] with ω
  exact (hh 0 (P ω)).1

theorem flow_memLp (t : ℝ) : MemLp (fun ω => flow d x s t (P ω)) 2 μ := by
  have h := SamplingCenterLp.path_memLp d (fun _ : Ω => x)
    (fun ω => flow d x s 0 (P ω)) (memLp_const x) (rewound_memLp d x s P hP) t
  have heq : (fun ω => flow d x s t (P ω)) =
      (fun ω => SamplingCenterLp.path d x t (flow d x s 0 (P ω))) :=
    funext (fun ω => flow_eq_path d x s t (P ω))
  rw [heq]
  exact h

theorem reply_memLp (t : ℝ) : MemLp (fun ω => reply d x s t (P ω)) 2 μ := by
  have h := SamplingCenterLp.reply_memLp d (fun _ : Ω => x)
    (fun ω => flow d x s 0 (P ω)) (memLp_const x) (rewound_memLp d x s P hP) t
  have heq : (fun ω => reply d x s t (P ω)) =
      (fun ω => SamplingCenterLp.reply d x t (flow d x s 0 (P ω))) :=
    funext (fun ω => reply_eq_reply d x s t (P ω))
  rw [heq]
  exact h

def flowLp (t : ℝ) : Lp E 2 μ := (flow_memLp d x s P hP t).toLp _
def replyLp (t : ℝ) : Lp E 2 μ := (reply_memLp d x s P hP t).toLp _

omit s P hP in
def initialMeanLp : Lp E 2 μ := (memLp_const (Gibbs.primitiveMean d.F x d.r) :
  MemLp (fun _ : Ω => Gibbs.primitiveMean d.F x d.r) 2 μ).toLp _

theorem flowLp_eq_pathLp (t : ℝ) : flowLp d x s P hP t =
    SamplingCenterLp.pathLp d (fun _ : Ω => x) (fun ω => flow d x s 0 (P ω))
      (memLp_const x) (rewound_memLp d x s P hP) t := by
  unfold flowLp SamplingCenterLp.pathLp
  apply MemLp.toLp_congr
  filter_upwards [] with ω
  exact flow_eq_path d x s t (P ω)

theorem replyLp_eq_replyLp (t : ℝ) : replyLp d x s P hP t =
    SamplingCenterLp.replyLp d (fun _ : Ω => x) (fun ω => flow d x s 0 (P ω))
      (memLp_const x) (rewound_memLp d x s P hP) t := by
  unfold replyLp SamplingCenterLp.replyLp
  apply MemLp.toLp_congr
  filter_upwards [] with ω
  exact reply_eq_reply d x s t (P ω)

theorem continuous_flowLp : Continuous (flowLp d x s P hP) := by
  have heq : flowLp d x s P hP = SamplingCenterLp.pathLp d (fun _ : Ω => x)
      (fun ω => flow d x s 0 (P ω)) (memLp_const x) (rewound_memLp d x s P hP) :=
    funext (flowLp_eq_pathLp d x s P hP)
  rw [heq]
  exact SamplingCenterLp.continuous_pathLp _ _ _ _ _

theorem continuous_replyLp : Continuous (replyLp d x s P hP) := by
  have heq : replyLp d x s P hP = SamplingCenterLp.replyLp d (fun _ : Ω => x)
      (fun ω => flow d x s 0 (P ω)) (memLp_const x) (rewound_memLp d x s P hP) :=
    funext (replyLp_eq_replyLp d x s P hP)
  rw [heq]
  exact SamplingCenterLp.continuous_replyLp _ _ _ _ _

theorem flowLp_initial : flowLp d x s P hP s = hP.toLp P := by
  unfold flowLp
  apply MemLp.toLp_congr
  filter_upwards [] with ω
  exact flow_initial d x s (P ω)

theorem reply_integral_lift (u v : ℝ) :
    ∃ hi : MemLp (fun ω => ∫ t in u..v, reply d x s t (P ω)) 2 μ,
      hi.toLp _ = ∫ t in u..v,replyLp d x s P hP t := by
  simp_rw [reply_eq_reply,replyLp_eq_replyLp]
  exact SamplingCenterLp.reply_integral_lift d (fun _ : Ω => x)
    (fun ω => flow d x s 0 (P ω)) (memLp_const x) (rewound_memLp d x s P hP) u v

theorem flowLp_eq_sub_integral (u v : ℝ) (hu : u ∈ Icc 0 d.b) (hv : v ∈ Icc 0 d.b) :
    flowLp d x s P hP v = flowLp d x s P hP u-d.r •
      ((v-u) • initialMeanLp (μ := μ) d x+∫ t in u..v,replyLp d x s P hP t) := by
  obtain ⟨hi,heq⟩ := reply_integral_lift d x s P hP u v
  rw [← heq]
  unfold flowLp initialMeanLp
  rw [← MemLp.toLp_const_smul,← MemLp.toLp_add,← MemLp.toLp_const_smul,← MemLp.toLp_sub]
  apply MemLp.toLp_congr
  filter_upwards [] with ω
  exact flow_eq_sub_integral d x s u v hu hv (P ω)

end RandomInputs
end AcceleratedLogConcave.Numerics.TransportFlowLp
