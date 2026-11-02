import AcceleratedLogConcave.Conditional.Flow.ExtendedJets
import AcceleratedLogConcave.Conditional.PolynomialMoments
import AcceleratedLogConcave.Analysis.DominatedLp

/-! Canonical L² lifting on the actual product phase law. Only the finite
material-jet ladder through the requested order is used in each proof. -/
noncomputable section
open Set Function MeasureTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
open Analysis.PositiveVarianceSlab

variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "P" => Kinetic.CoupledPhase E
variable (d : PositiveVarianceFlowData (EuclideanSpace ℝ ι))

def phaseMeasure : Measure P :=
  Kinetic.coupledPhaseMeasure (interpolationLaw d.F d.x d.r d.b)

instance phaseMeasure_probability : IsProbabilityMeasure d.phaseMeasure := by
  let := interpolationLaw_isProbabilityMeasure d.hF d.hlo d.x d.r d.b
  exact Kinetic.coupledPhaseMeasure_probability _

def momentumJet (k : ℕ) (t : ℝ) (z : P) : E := (d.jet k t z.fst).snd z.snd

theorem continuous_momentumJet (k : ℕ) : Continuous (uncurry (d.momentumJet k)) := by
  have hp : Continuous (fun q : ℝ × P => q.2.fst) :=
    (WithLp.prod_continuous_ofLp 2 E E).fst.comp continuous_snd
  have hm : Continuous (fun q : ℝ × P => q.2.snd) :=
    (WithLp.prod_continuous_ofLp 2 E E).snd.comp continuous_snd
  exact ((d.continuous_jet k).comp (continuous_fst.prodMk hp)).snd.clm_apply hm

/-- The envelope uses both position moments and the genuine independent
Gaussian momentum factor, derived from the literal product-phase law. -/
theorem exists_momentumJet_envelope (k : ℕ) :
    ∃ B : P → ℝ, MemLp B 2 d.phaseMeasure ∧ ∀ t z, ‖d.momentumJet k t z‖ ≤ B z := by
  obtain ⟨C, hC, N, hb⟩ := d.exists_jet_polynomial_bound k
  refine ⟨fun z => C * (1 + ‖z.fst‖) ^ N * ‖z.snd‖,
    coupledInterpolation_polynomial_momentum_memLp d.hF d.hlo d.x d.r d.b N C, ?_⟩
  intro t z
  exact ((d.jet k t z.fst).snd.le_opNorm z.snd).trans
    (mul_le_mul_of_nonneg_right ((norm_snd_le (d.jet k t z.fst)).trans (hb t z.fst))
      (norm_nonneg z.snd))

theorem momentumJet_memLp (k : ℕ) (t : ℝ) : MemLp (d.momentumJet k t) 2 d.phaseMeasure := by
  obtain ⟨B, hB, hb⟩ := d.exists_momentumJet_envelope k
  exact hB.mono'
    ((d.continuous_momentumJet k).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall (hb t))

theorem hasDerivAt_momentumJet (k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) (z : P) :
    HasDerivAt (fun u => d.momentumJet k u z) (d.momentumJet (k + 1) t z) t := by
  have hs : HasDerivAt (fun u => (d.jet k u z.fst).snd)
      (d.jet (k + 1) t z.fst).snd t :=
    (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt t
      (d.hasDerivAt_jet k ht z.fst)
  have hh := hs.clm_apply (hasDerivAt_const t z.snd)
  simpa only [momentumJet, map_zero, add_zero] using hh

def momentumJetLp (k : ℕ) (t : ℝ) : Lp E 2 d.phaseMeasure :=
  (d.momentumJet_memLp k t).toLp (d.momentumJet k t)

theorem contDiffOn_momentumJetLp (n : ℕ) :
    ContDiffOn ℝ n (d.momentumJetLp 0) (Ioo (left d.b) (right d.b)) := by
  choose B hB hb using (fun k : Fin (n + 1) => d.exists_momentumJet_envelope k.val)
  let B' : ℕ → P → ℝ := fun k =>
    if hk : k ≤ n then B ⟨k, Nat.lt_succ_of_le hk⟩ else fun _ => 0
  refine Analysis.DominatedLp.contDiffOn_toLp_of_finite_ladder n d.momentumJet
    (fun k _ t => d.momentumJet_memLp k t) (fun k _ => d.continuous_momentumJet k)
    B' ?_ ?_ (fun k _ t ht z => d.hasDerivAt_momentumJet k ht z)
  · intro k hk
    simpa only [B', dite_eq_left hk] using hB ⟨k, Nat.lt_succ_of_le hk⟩
  · intro k hk t z
    simpa only [B', dite_eq_left hk] using hb ⟨k, Nat.lt_succ_of_le hk⟩ t z

/-- Subtract the reference value in the same canonical L² space. Exact
source-kernel agreement is supplied separately by nested-slab uniqueness. -/
def kernelLp (t : ℝ) : Lp E 2 d.phaseMeasure := d.momentumJetLp 0 t - d.momentumJetLp 0 d.b

theorem contDiffOn_kernelLp (n : ℕ) :
    ContDiffOn ℝ n d.kernelLp (Ioo (left d.b) (right d.b)) :=
  (d.contDiffOn_momentumJetLp n).sub contDiffOn_const

@[simp] theorem kernelLp_reference : d.kernelLp d.b = 0 := by simp [kernelLp]

end AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
