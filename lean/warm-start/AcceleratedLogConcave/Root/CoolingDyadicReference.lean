import AcceleratedLogConcave.Channels.CoolingDecoderLaw
import AcceleratedLogConcave.Channels.TerminalHeatBias
import AcceleratedLogConcave.Gibbs.Normalization

/-! Literal dyadic cooling variances, finite exact decoder composition and
terminal heat bias. These are reference suppliers, not an implemented-law
identification or an assumed implementation accuracy statement. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace AcceleratedLogConcave.Root.CoolingDyadicReference

def variance (h : ℝ) (j : ℕ) : ℝ≥0 := ⟨2*h^2/(2:ℝ)^j,by positivity⟩

@[simp] theorem variance_zero (h : ℝ) : (variance h 0:ℝ)=2*h^2 := by change 2*h^2/(2:ℝ)^0=2*h^2; simp

theorem variance_succ (h : ℝ) (j : ℕ) : variance h (j+1)=variance h j/2 := by
  apply NNReal.coe_injective
  change 2*h^2/(2:ℝ)^(j+1)=(2*h^2/(2:ℝ)^j)/2
  rw [pow_succ]
  ring

theorem variance_pos {h : ℝ} (hh : 0<h) (j : ℕ) : 0<variance h j := by
  change 0<2*h^2/(2:ℝ)^j
  positivity

theorem variance_le (h : ℝ) (j : ℕ) : (variance h j:ℝ)≤2*h^2 := by
  exact div_le_self (by positivity) (one_le_pow₀ (by norm_num : (1:ℝ)≤2))

variable {d : ℕ} (V : EuclideanSpace ℝ (Fin d) → ℝ) (hV : Measurable V) (h : ℝ)
/-- Every step is the literal positive-width equal-width posterior decoder. -/
def chain : ℕ → Kernel (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d))
  | 0 => Kernel.id
  | j+1 => Channels.equalWidthBridge V hV (variance h j) ∘ₖ chain j

theorem chain_markov (hI : Integrable (fun x => Real.exp (-V x))) (j : ℕ) :
    IsMarkovKernel (chain V hV h j) := by
  induction j with
  | zero => dsimp [chain]; infer_instance
  | succ j ih =>
    have := Channels.equalWidthBridge_isMarkov hV hI (variance h j)
    dsimp only [chain]
    infer_instance

/-- Finite exact decoder output, proved by the actual posterior bridge law. -/
theorem chain_forward (hI : Integrable (fun x => Real.exp (-V x))) (hh : 0<h) (j : ℕ) :
    chain V hV h j ∘ₘ Channels.forward (volume.tilted (fun x => -V x)) (variance h 0)=
      Channels.forward (volume.tilted (fun x => -V x)) (variance h j) := by
  induction j with
  | zero => simp [chain]
  | succ j ih =>
    rw [chain,← Measure.comp_assoc,ih,Channels.equalWidthBridge_comp_forward hV hI _ (variance_pos hh j),variance_succ]

/-- Original hypotheses supply integrability; no independent normalization
or moment premise is required for the finite decoder endpoint. -/
theorem original_endpoint (hC2 : ContDiff ℝ 2 V) {κ : ℝ} (hκ : 1≤κ)
    (hlo : ∀ x v,κ⁻¹*‖v‖^2≤fderiv ℝ (fderiv ℝ V) x v v)
    (hh : 0<h) (j : ℕ) :
    chain V hV h j ∘ₘ Channels.forward (volume.tilted (fun x => -V x)) (variance h 0)=
      Channels.forward (volume.tilted (fun x => -V x)) (variance h j) :=
  chain_forward V hV h (Gibbs.integrable_exp_neg_of_hessian_lower hC2 (by positivity : 0<κ⁻¹) hlo) hh j

/-- Exact bias after all literal dyadic decoders. -/
theorem terminal_bias (hC2 : ContDiff ℝ 2 V) {κ : ℝ} (hκ : 1≤κ)
    (hlo : ∀ x v,κ⁻¹*‖v‖^2≤fderiv ℝ (fderiv ℝ V) x v v)
    (hup : ∀ x v,fderiv ℝ (fderiv ℝ V) x v v≤‖v‖^2)
    (hh : 0<h) (j : ℕ) :
    let hI := Gibbs.integrable_exp_neg_of_hessian_lower hC2 (by positivity : 0<κ⁻¹) hlo
    let : IsProbabilityMeasure (volume.tilted (fun x => -V x)) := isProbabilityMeasure_tilted hI
    let : IsMarkovKernel (chain V hV h j) := chain_markov V hV h hI j
    let : IsProbabilityMeasure (Channels.forward (volume.tilted (fun x => -V x)) (variance h 0)) := by unfold Channels.forward; infer_instance
    Probability.totalVariationDistance
      (chain V hV h j ∘ₘ Channels.forward (volume.tilted (fun x => -V x)) (variance h 0))
      (volume.tilted (fun x => -V x))≤Real.sqrt ((d:ℝ)*(2*h^2/(2:ℝ)^j))/2 := by
  dsimp only
  have hI := Gibbs.integrable_exp_neg_of_hessian_lower hC2 (by positivity : 0<κ⁻¹) hlo
  let : IsProbabilityMeasure (volume.tilted (fun x => -V x)) := isProbabilityMeasure_tilted hI
  simp only [chain_forward V hV h hI hh j]
  exact Channels.totalVariationDistance_forward_gibbs_le _ V κ hκ hC2 hlo hup rfl (variance h j)
end AcceleratedLogConcave.Root.CoolingDyadicReference
