import AcceleratedLogConcave.Numerics.SmoothConditional
import AcceleratedLogConcave.Numerics.TransportFlowLp

/-! Joint center dependence of the literal arbitrary-start source flow.
The center is a frozen coordinate of the existing joint Lipschitz field.
The initial probability time is preserved; no initial-law swap is involved. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Numerics.SourceFlowJointCenter
open Conditional ConditionalSmoothing OAI.LogConcaveSampling.GlobalODE
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
variable (d : SamplingCenterLp.Data ι) (s : Icc (0:ℝ) d.b)

def start : Icc (Analysis.PositiveVarianceSlab.left d.b) (Analysis.PositiveVarianceSlab.right d.b) :=
  ⟨s,(fixedData d 0).source_subset_construction s.2⟩

def joint (t : ℝ) (p : E × E) : E × E :=
  OAI.LogConcaveSampling.GlobalODE.flow (fun u _ => lipschitz_velocity d u)
    (continuous_velocity d) (start d s) p
      (time d (SamplingFlowLp.sourceTime d.hb t))

theorem continuous_joint : Continuous (uncurry (joint d s)) :=
  (flow_joint_continuous (fun u _ => lipschitz_velocity d u)
    (continuous_velocity d) (start d s)).comp
      (continuous_snd.prodMk ((continuous_projIcc (h := (fixedData d 0).interval_le)).comp
        ((SamplingFlowLp.continuous_sourceTime d.hb).comp continuous_fst)))

theorem joint_eq_fixed (t : ℝ) (p : E × E) :
    joint d s t p = (p.1,
      OAI.LogConcaveSampling.GlobalODE.flow (fixedData d p.1).lipschitz_clippedVelocity
        (fixedData d p.1).continuous_clippedVelocity (start d s) p.2
          (time d (SamplingFlowLp.sourceTime d.hb t))) := by
  let fd := fixedData d p.1
  let X : ℝ → E × E := fun u => (p.1,
    OAI.LogConcaveSampling.GlobalODE.flow fd.lipschitz_clippedVelocity
      fd.continuous_clippedVelocity (start d s) p.2 u)
  have hX : Continuous X := continuous_const.prodMk (flow_continuous _ _ _ _)
  have hdX (u : ℝ) (hu : u ∈ Icc (Analysis.PositiveVarianceSlab.left d.b)
      (Analysis.PositiveVarianceSlab.right d.b)) :
      HasDerivWithinAt X (velocity d u (X u))
        (Icc (Analysis.PositiveVarianceSlab.left d.b) (Analysis.PositiveVarianceSlab.right d.b)) u := by
    exact (hasDerivWithinAt_const u _ p.1).prodMk
      (flow_deriv fd.lipschitz_clippedVelocity fd.continuous_clippedVelocity (start d s) p.2 u hu)
  have hinit : X (start d s) = p := by simp [X,flow_initial]
  have h := trajectory_dist (fun u _ => lipschitz_velocity d u)
    (flow_continuous (fun u _ => lipschitz_velocity d u) (continuous_velocity d) (start d s) p).continuousOn
    (flow_deriv (fun u _ => lipschitz_velocity d u) (continuous_velocity d) (start d s) p)
    hX.continuousOn hdX (start d s)
      ⟨time d (SamplingFlowLp.sourceTime d.hb t),time_mem d _⟩
  rw [flow_initial,hinit,dist_self,zero_mul,dist_le_zero] at h
  exact h

/-- Exact equality with the existing arbitrary-start source evaluator, at all
real times using its original clamp to the probability interval. -/
theorem joint_snd_eq_source (t : ℝ) (x y : E) :
    (joint d s t (x,y)).2 = TransportFlowLp.flow d x s t y := by
  have ht := SamplingFlowLp.sourceTime_mem d.hb t
  rw [joint_eq_fixed,time_eq d ((fixedData d 0).source_subset_construction ht)]
  exact (fixedData d x).flow_eq_source s ⟨SamplingFlowLp.sourceTime d.hb t,ht⟩ y

theorem continuous_source :
    Continuous (fun p : ℝ × (E × E) => TransportFlowLp.flow d p.2.1 s p.1 p.2.2) := by
  have h : (fun p : ℝ × (E × E) => TransportFlowLp.flow d p.2.1 s p.1 p.2.2) =
      (fun p => (joint d s p.1 p.2).2) := by
    funext p
    exact (joint_snd_eq_source d s p.1 p.2.1 p.2.2).symm
  rw [h]
  exact (continuous_joint d s).snd

end AcceleratedLogConcave.Numerics.SourceFlowJointCenter
