import AcceleratedLogConcave.Numerics.MeanResidualBridge
import AcceleratedLogConcave.Conditional.Flow.ExtendedAgreement
import AcceleratedLogConcave.Conditional.SourcePosteriorParameters
import AcceleratedLogConcave.Conditional.PolynomialMoments
import AcceleratedLogConcave.Analysis.DominatedLp
import AcceleratedLogConcave.Numerics.SmoothConditionalBounds
import AcceleratedLogConcave.Numerics.SmoothConditionalMoments

/-!
# The actual conditional path on an enlarged probability-time slab

The center is a frozen coordinate of a globally Lipschitz ODE. The second
coordinate starts from the original input at time zero. Only the outer
construction endpoints are clamped; zero and conditionalEnd are interior.
No numerical derivative budget or CellRegularity is asserted here.
-/
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped ContDiff Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Numerics.ConditionalSmoothing
open Conditional Analysis.PositiveVarianceSlab Analysis.CoupledVelocityPolynomial
open OAI.LogConcaveSampling.GlobalODE
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
variable (d : SamplingCenterLp.Data ι)

def fixedData (x : E) : PositiveVarianceFlowData E :=
  ⟨d.F, d.hF, d.ell, d.hell, d.hlo, d.hup, x, d.r, d.hr, d.b, d.hb, d.hb1⟩

def start : Icc (left d.b) (right d.b) :=
  ⟨0, (fixedData d 0).source_subset_construction ⟨le_rfl, d.hb⟩⟩

def time (t : ℝ) : ℝ := (fixedData d 0).time t

theorem time_mem (t : ℝ) : time d t ∈ Icc (left d.b) (right d.b) :=
  (fixedData d 0).time_mem t

theorem time_eq {t : ℝ} (ht : t ∈ Icc (left d.b) (right d.b)) : time d t = t :=
  (fixedData d 0).time_eq ht

theorem continuous_time : Continuous (time d) :=
  continuous_subtype_val.comp continuous_projIcc

def openVelocity (p : ℝ × (E × E)) : E × E :=
  (0, (-d.r) • Conditional.conditionalMean d.F p.2.1 d.r p.1 p.2.2)

theorem contDiffOn_coefficient : ContDiffOn ℝ ∞
    (fun p : ℝ × (E × E) => Conditional.conditionalMean d.F p.2.1 d.r p.1 p.2.2)
    (openDomain (E × E)) := by
  have hp : ContDiff ℝ ∞ (fun p : ℝ × (E × E) => (p.2.1, d.r, p.1, p.2.2)) := by
    fun_prop
  have hm := (contDiffOn_conditionalMean_parameters d.hF d.hlo d.hup).comp
    hp.contDiffOn (fun p (hp : p ∈ openDomain (E × E)) => ⟨d.hr, hp⟩)
  exact hm

theorem contDiffOn_openVelocity :
    ContDiffOn ℝ ∞ (openVelocity d) (openDomain (E × E)) :=
  contDiffOn_const.prodMk ((contDiffOn_coefficient d).const_smul (-d.r))

def velocity (t : ℝ) (p : E × E) : E × E := openVelocity d (time d t, p)

theorem continuous_velocity : Continuous (uncurry (velocity d)) :=
  (contDiffOn_openVelocity d).continuousOn.comp_continuous
    ((continuous_time d |>.comp continuous_fst).prodMk continuous_snd)
    (fun p => construction_subset d.hb d.hb1 (time_mem d p.1))

def lipschitzConstant : ℝ≥0 :=
  ⟨d.r * d.ell * (1 + d.r),
    mul_nonneg (mul_nonneg d.hr.le d.hell) (by linarith [d.hr])⟩

theorem lipschitz_velocity (t : ℝ) : LipschitzWith (lipschitzConstant d) (velocity d t) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have ht := construction_subset d.hb d.hb1 (time_mem d t)
  have habs : |time d t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2.le⟩
  have hradius : 0 < d.r * Real.sqrt (1 - (time d t)^2) :=
    mul_pos d.hr (Real.sqrt_pos.mpr (by nlinarith [ht.1, ht.2]))
  have hm := (Gibbs.primitive_mean_lipschitz d.hF d.hell d.hlo d.hup hradius).dist_le_mul
    (p.1 + (d.r * time d t) • p.2) (q.1 + (d.r * time d t) • q.2)
  simp only [dist_eq_norm] at hm
  have hs : |d.r * time d t| ≤ d.r := by
    rw [abs_mul, abs_of_pos d.hr]
    exact mul_le_of_le_one_right d.hr.le habs
  have he : (p.1 + (d.r * time d t) • p.2) -
      (q.1 + (d.r * time d t) • q.2) =
      (p.1-q.1) + (d.r * time d t) • (p.2-q.2) := by module
  have hn : ‖(p.1 + (d.r * time d t) • p.2) -
      (q.1 + (d.r * time d t) • q.2)‖ ≤ (1+d.r) * ‖p-q‖ := by
    rw [he]
    have h := norm_add_le (p.1-q.1) ((d.r * time d t) • (p.2-q.2))
    rw [norm_smul, Real.norm_eq_abs] at h
    have hmul := mul_le_mul hs (norm_snd_le (p-q)) (norm_nonneg _) d.hr.le
    have hfst := norm_fst_le (p-q)
    change |d.r * time d t| * ‖p.2-q.2‖ ≤ d.r * ‖p-q‖ at hmul
    change ‖p.1-q.1‖ ≤ ‖p-q‖ at hfst
    nlinarith
  simp only [dist_eq_norm]
  change ‖((0 : E), (-d.r) • Conditional.conditionalMean d.F p.1 d.r (time d t) p.2) -
      ((0 : E), (-d.r) • Conditional.conditionalMean d.F q.1 d.r (time d t) q.2)‖ ≤
      (d.r*d.ell*(1+d.r)) * ‖p-q‖
  simp only [Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero,
    ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_neg, abs_of_pos d.hr]
  rw [max_eq_right (mul_nonneg d.hr.le (norm_nonneg _))]
  rw [AffineFlowIdentities.conditionalMean_eq_primitiveMean d.hF d.hell d.hlo d.hup
    p.1 d.hr ht.1 ht.2,
    AffineFlowIdentities.conditionalMean_eq_primitiveMean d.hF d.hell d.hlo d.hup
    q.1 d.hr ht.1 ht.2]
  calc
    _ ≤ d.r * (d.ell * ‖(p.1 + (d.r * time d t) • p.2) -
        (q.1 + (d.r * time d t) • q.2)‖) := mul_le_mul_of_nonneg_left hm d.hr.le
    _ ≤ d.r * (d.ell * ((1+d.r)*‖p-q‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn d.hell) d.hr.le
    _ = _ := by simp only [Prod.norm_def]; ring

def jointPath (t : ℝ) (p : E × E) : E × E :=
  OAI.LogConcaveSampling.GlobalODE.flow (fun u _ => lipschitz_velocity d u)
    (continuous_velocity d) (start d) p (time d t)

theorem continuous_jointPath : Continuous (uncurry (jointPath d)) :=
  (flow_joint_continuous (fun u _ => lipschitz_velocity d u)
    (continuous_velocity d) (start d)).comp
      (continuous_snd.prodMk
        ((continuous_projIcc (h := (fixedData d 0).interval_le)).comp continuous_fst))

/-- Freezing the center in the joint ODE gives the literal fixed-center flow,
with the same initial input and reference time zero. -/
theorem jointPath_eq_fixed (t : ℝ) (p : E × E) :
    jointPath d t p = (p.1,
      OAI.LogConcaveSampling.GlobalODE.flow (fixedData d p.1).lipschitz_clippedVelocity
        (fixedData d p.1).continuous_clippedVelocity (start d) p.2 (time d t)) := by
  let fd := fixedData d p.1
  let X : ℝ → E × E := fun u => (p.1,
    OAI.LogConcaveSampling.GlobalODE.flow fd.lipschitz_clippedVelocity
      fd.continuous_clippedVelocity (start d) p.2 u)
  have hX : Continuous X := continuous_const.prodMk (flow_continuous _ _ _ _)
  have hdX (u : ℝ) (hu : u ∈ Icc (left d.b) (right d.b)) :
      HasDerivWithinAt X (velocity d u (X u)) (Icc (left d.b) (right d.b)) u := by
    exact (hasDerivWithinAt_const u (Icc (left d.b) (right d.b)) p.1).prodMk
      (flow_deriv fd.lipschitz_clippedVelocity fd.continuous_clippedVelocity
        (start d) p.2 u hu)
  have hinit : X (start d) = p := by simp [X, flow_initial]
  have h := trajectory_dist (fun u _ => lipschitz_velocity d u)
    (flow_continuous (fun u _ => lipschitz_velocity d u) (continuous_velocity d)
      (start d) p).continuousOn
    (flow_deriv (fun u _ => lipschitz_velocity d u) (continuous_velocity d) (start d) p)
    hX.continuousOn hdX (start d) ⟨time d t, time_mem d t⟩
  rw [flow_initial, hinit, dist_self, zero_mul, dist_le_zero] at h
  exact h

@[simp] theorem jointPath_fst (t : ℝ) (p : E × E) : (jointPath d t p).1 = p.1 := by
  rw [jointPath_eq_fixed]

theorem jointPath_snd_eq_source (x p : E) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    (jointPath d t (x,p)).2 = SamplingCenterLp.path d x t p := by
  rw [jointPath_eq_fixed, time_eq d ((fixedData d x).source_subset_construction ht)]
  have h := (fixedData d x).flow_eq_source ⟨0, le_rfl, d.hb⟩ ⟨t, ht⟩ p
  simpa only [SamplingCenterLp.path, SamplingFlowLp.sourcePath,
    SamplingFlowLp.sourceTime_eq d.hb ht, fixedData, start] using h

theorem exists_jointPath_linear_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t p, ‖jointPath d t p‖ ≤ C * (1 + ‖p‖) := by
  obtain ⟨C,hC,h⟩ := OAI.LogConcaveSampling.GlobalODE.exists_flow_linear_bound
    (continuous_velocity d) (fun u _ => lipschitz_velocity d u) (start d)
  exact ⟨C,hC,fun t p => h (time d t) (time_mem d t) p⟩

theorem hasDerivAt_jointPath {t : ℝ} (ht : t ∈ Ioo (left d.b) (right d.b)) (p : E × E) :
    HasDerivAt (fun u => jointPath d u p) (openVelocity d (t, jointPath d t p)) t := by
  have hh := (flow_deriv (fun u _ => lipschitz_velocity d u) (continuous_velocity d)
    (start d) p t ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have he : (fun u => jointPath d u p) =ᶠ[𝓝 t]
      OAI.LogConcaveSampling.GlobalODE.flow (fun u _ => lipschitz_velocity d u)
        (continuous_velocity d) (start d) p := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    simp only [jointPath, time_eq d ⟨hu.1.le,hu.2.le⟩]
  simpa only [velocity, jointPath, time_eq d ⟨ht.1.le,ht.2.le⟩] using
    hh.congr_of_eventuallyEq he

/-- The universal time-jet recurrence follows the actual frozen-center path. -/
def jet (k : ℕ) (t : ℝ) (p : E × E) : E × E :=
  Analysis.ODEJet.stateJet (openDomain (E × E)) (openVelocity d) k
    (time d t, jointPath d t p)

@[simp] theorem jet_zero (t : ℝ) (p : E × E) : jet d 0 t p = jointPath d t p := rfl

theorem jet_one (t : ℝ) (p : E × E) :
    jet d 1 t p = openVelocity d (time d t, jointPath d t p) := by
  have hp : (time d t, jointPath d t p) ∈ openDomain (E × E) :=
    construction_subset d.hb d.hb1 (time_mem d t)
  change fderivWithin ℝ (ContinuousLinearMap.snd ℝ ℝ (E × E)) (openDomain (E × E))
    (time d t, jointPath d t p) (1, openVelocity d (time d t, jointPath d t p)) = _
  rw [(ContinuousLinearMap.snd ℝ ℝ (E × E)).fderivWithin
    ((isOpen_openDomain (E × E)).uniqueDiffOn _ hp)]
  rfl

theorem continuous_jet (k : ℕ) : Continuous (uncurry (jet d k)) :=
  (Analysis.ODEJet.contDiffOn_stateJet (isOpen_openDomain (E × E)).uniqueDiffOn
    (contDiffOn_openVelocity d) k).continuousOn.comp_continuous
      (((continuous_time d).comp continuous_fst).prodMk (continuous_jointPath d))
      (fun p => construction_subset d.hb d.hb1 (time_mem d p.1))

theorem hasDerivAt_jet (k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) (p : E × E) :
    HasDerivAt (fun u => jet d k u p) (jet d (k+1) t p) t := by
  have hh := Analysis.ODEJet.hasDerivAt_stateJet_along (isOpen_openDomain (E × E))
    (contDiffOn_openVelocity d) (construction_subset d.hb d.hb1 ⟨ht.1.le,ht.2.le⟩)
    (hasDerivAt_jointPath d ht p) k
  have he : (fun u => jet d k u p) =ᶠ[𝓝 t]
      (fun u => Analysis.ODEJet.stateJet (openDomain (E × E)) (openVelocity d) k
        (u, jointPath d u p)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    simp only [jet, time_eq d ⟨hu.1.le,hu.2.le⟩]
  simpa only [jet, time_eq d ⟨ht.1.le,ht.2.le⟩] using hh.congr_of_eventuallyEq he

theorem polynomialJetBound_openVelocity (n : ℕ) :
    PolynomialJetBound (openDomain (E × E)) (closedSlab (E × E) d.b) (openVelocity d) n := by
  have hU : UniqueDiffOn ℝ (openDomain (E × E)) := (isOpen_openDomain (E × E)).uniqueDiffOn
  have hSU := closedSlab_subset_openDomain (E × E) d.hb d.hb1
  exact polynomialJetBound_prod hU hSU contDiffOn_const
    ((contDiffOn_coefficient d).const_smul (-d.r)) n
    (polynomialJetBound_const _ _ (0 : E) n)
    (polynomialJetBound_smul hU hSU contDiffOn_const (contDiffOn_coefficient d) n
      (fun i _ => polynomialJetBound_const _ _ (-d.r) i)
      (fun i _ => polynomialJetBound_conditionalMean d i))

/-- Unlike the fixed-center supplier, this envelope is uniform in both the
unrestricted center and the original initial state. -/
theorem exists_jet_polynomial_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ t p, ‖jet d k t p‖ ≤ C*(1+‖p‖)^N := by
  have hU : UniqueDiffOn ℝ (openDomain (E × E)) := (isOpen_openDomain (E × E)).uniqueDiffOn
  have hSU := closedSlab_subset_openDomain (E × E) d.hb d.hb1
  obtain ⟨C,hC,N,hjet⟩ := Analysis.ODEJet.exists_polynomial_stateJet_bound
    hU hSU (contDiffOn_openVelocity d) k
    (fun q _ => polynomialJetBound_prod hU hSU contDiffOn_const
      (contDiffOn_openVelocity d) q (polynomialJetBound_const _ _ (1 : ℝ) q)
      (polynomialJetBound_openVelocity d q)) k 0 (by omega)
  obtain ⟨D,hD,hstate⟩ := exists_jointPath_linear_bound d
  refine ⟨C*(D+2)^N,mul_nonneg hC (pow_nonneg (by positivity) _),N,?_⟩
  intro t p
  have ht := construction_subset d.hb d.hb1 (time_mem d t)
  have htn : ‖time d t‖ ≤ 1 := by
    rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨ht.1.le,ht.2.le⟩
  have hpair : ‖(time d t,jointPath d t p)‖ ≤ (D+1)*(1+‖p‖) := by
    rw [Prod.norm_def]
    apply max_le
    · nlinarith [norm_nonneg p,mul_nonneg hD (norm_nonneg p)]
    · exact (hstate t p).trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right zero_le_one) (by positivity))
  have hrad : 1+‖(time d t,jointPath d t p)‖ ≤ (D+2)*(1+‖p‖) := by
    nlinarith [norm_nonneg p]
  have hj := hjet (time d t,jointPath d t p) (time_mem d t)
  rw [norm_iteratedFDerivWithin_zero] at hj
  calc
    ‖jet d k t p‖ ≤ C*(1+‖(time d t,jointPath d t p)‖)^N := hj
    _ ≤ C*((D+2)*(1+‖p‖))^N :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hrad N) hC
    _ = _ := by rw [mul_pow,mul_assoc]

end AcceleratedLogConcave.Numerics.ConditionalSmoothing

namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph Analysis.PositiveVarianceSlab
open ConditionalSmoothing
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι
variable (d : MeanFlowLp.Data ι m) (j : Fin m) (ρ : d.G.Kernel)

/-- Time jets evaluated on the original common seed. -/
def conditionalJet (k : ℕ) (t : ℝ) (w : Seed d) : E :=
  (jet (conditionalData d ρ) k t (conditionalInput d j ρ w)).2

theorem continuous_conditionalJet (k : ℕ) : Continuous (uncurry (conditionalJet d j ρ k)) :=
  ((continuous_jet (conditionalData d ρ) k).comp
    (continuous_fst.prodMk ((continuous_conditionalInput d j ρ).comp continuous_snd))).snd

/-- Each finite jet has a genuine common L² envelope on the literal seed law. -/
theorem exists_conditionalJet_envelope (k : ℕ) :
    ∃ B : Seed d → ℝ, MemLp B 2 (seedMeasure d) ∧
      ∀ t w, ‖conditionalJet d j ρ k t w‖ ≤ B w := by
  obtain ⟨C,hC,N,h⟩ := exists_jet_polynomial_bound (conditionalData d ρ) k
  exact ⟨fun w => C*(1+‖conditionalInput d j ρ w‖)^N,
    (conditionalInput_polynomial_memLp d j ρ N).const_mul C,
    fun t w => (norm_snd_le _).trans (h t (conditionalInput d j ρ w))⟩

theorem conditionalJet_memLp (k : ℕ) (t : ℝ) :
    MemLp (conditionalJet d j ρ k t) 2 (seedMeasure d) := by
  obtain ⟨B,hB,h⟩ := exists_conditionalJet_envelope d j ρ k
  exact hB.mono'
    ((continuous_conditionalJet d j ρ k).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall (h t))

theorem hasDerivAt_conditionalJet (k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left conditionalEnd) (right conditionalEnd)) (w : Seed d) :
    HasDerivAt (fun u => conditionalJet d j ρ k u w) (conditionalJet d j ρ (k+1) t w) t :=
  (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_jet (conditionalData d ρ) k ht (conditionalInput d j ρ w))

def conditionalJetLp (k : ℕ) (t : ℝ) : H d :=
  (conditionalJet_memLp d j ρ k t).toLp (conditionalJet d j ρ k t)

theorem contDiffOn_conditionalJetLp (k n : ℕ) :
    ContDiffOn ℝ n (conditionalJetLp d j ρ k)
      (Ioo (left conditionalEnd) (right conditionalEnd)) := by
  choose B hB hb using (fun i : ℕ => exists_conditionalJet_envelope d j ρ i)
  have h := Analysis.DominatedLp.contDiffOn_toLp_of_finite_ladder n
    (fun i => conditionalJet d j ρ (k+i))
    (fun i _ t => conditionalJet_memLp d j ρ (k+i) t)
    (fun i _ => continuous_conditionalJet d j ρ (k+i))
    (fun i => B (k+i)) (fun i _ => hB (k+i)) (fun i _ => hb (k+i))
    (fun i _ t ht w => by
      simpa only [Nat.add_assoc] using hasDerivAt_conditionalJet d j ρ (k+i) ht w)
  change ContDiffOn ℝ n
    (fun t => (conditionalJet_memLp d j ρ k t).toLp (conditionalJet d j ρ k t)) _
  simpa only [Nat.add_zero] using h

/-- Endpoint-safe extension of the actual conditional curve on its common seed. -/
def smoothConditional (t : ℝ) : H d := conditionalJetLp d j ρ 0 t

theorem smoothConditional_eq {t : ℝ} (ht : t ∈ Icc 0 conditionalEnd) :
    smoothConditional d j ρ t = conditionalLp d j ρ t := by
  unfold smoothConditional conditionalJetLp conditionalLp
  apply Lp.ext
  filter_upwards [(conditionalJet_memLp d j ρ 0 t).coeFn_toLp,
    (conditional_memLp d j ρ t).coeFn_toLp] with w h1 h2
  rw [h1,h2]
  exact jointPath_snd_eq_source (conditionalData d ρ) (conditionalCenter d j ρ w) (w.2 j ρ) ht

theorem contDiffOn_smoothConditional (n : ℕ) :
    ContDiffOn ℝ n (smoothConditional d j ρ)
      (Ioo (left conditionalEnd) (right conditionalEnd)) :=
  contDiffOn_conditionalJetLp d j ρ 0 n

/-- Smooth lifted mean, obtained from the first time jet and the fixed positive
local radius. Its equality to the receiver will hold on the open slab. -/
def smoothConditionalMean (t : ℝ) : H d :=
  (-(conditionalData d ρ).r)⁻¹ • conditionalJetLp d j ρ 1 t

theorem contDiffOn_smoothConditionalMean (n : ℕ) :
    ContDiffOn ℝ n (smoothConditionalMean d j ρ)
      (Ioo (left conditionalEnd) (right conditionalEnd)) :=
  (contDiffOn_conditionalJetLp d j ρ 1 n).const_smul _

end AcceleratedLogConcave.Numerics.MeanResidualBridge
