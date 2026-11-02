import AcceleratedLogConcave.Tensor.PhaseGibbsNetwork
import AcceleratedLogConcave.Kinetic.Reheating.GaussianPoincare
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-! Actual standard Gaussian Gibbs environment for the angle receiver. No
moment or score-integrability hypothesis is delegated to the caller. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.AnglePhase
open Tensor.AdjointReduction Tensor.PolynomialClosure Conditional.Appell
open Tensor.Ordered.Graph Kinetic.Reheating

private theorem partial_linear_cons {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : E →L[ℝ] ℝ) (v : E) (J : List E) :
    ∃ c : ℝ, partialAlong id (v::J) L = fun _ => c := by
  induction J generalizing v with
  | nil => exact ⟨L v, by ext x; simp [partialAlong,dir,L.fderiv]⟩
  | cons w J ih =>
    obtain ⟨c,hc⟩ := ih w
    refine ⟨0,?_⟩
    change dir v (partialAlong id (w::J) L) = fun _ => 0
    rw [hc]
    funext x
    change fderiv ℝ (fun _ : E => c) x v = 0
    simp only [fderiv_const_apply,zero_apply]

theorem polynomialJets_linear {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : E →L[ℝ] ℝ) : HasPolynomialJets L := by
  intro J
  cases J with
  | nil => exact HasGrowth.linear L
  | cons v J =>
    obtain ⟨c,hc⟩ := partial_linear_cons L v J
    rw [hc]
    exact HasGrowth.const c

theorem gaussian_score_polynomial {D : ℕ} (v : EuclideanSpace ℝ (Fin D)) :
    HasPolynomialJets (dir v gaussianPotential) := by
  have he : dir v gaussianPotential = innerSL ℝ v := by
    ext x
    simp [dir,gaussianPotential_fderiv,real_inner_comm]
  rw [he]
  exact polynomialJets_linear _

def gaussianEnvironment (D : ℕ) : SmoothGibbsEnvironment D where
  base := volume
  haar := inferInstance
  potential := gaussianPotential
  smooth := gaussianPotential_smooth
  partition_integrable := gaussianPotential_integrable
  finite := by
    change IsFiniteMeasure (volume.tilted (fun x : EuclideanSpace ℝ (Fin D) => -(‖x‖^2/2)))
    rw [← stdGaussian_eq_quadratic_tilted]
    infer_instance
  moments := by
    intro n
    change Integrable (fun x : EuclideanSpace ℝ (Fin D) => ‖x‖^n)
      (volume.tilted (fun x => -(‖x‖^2/2)))
    rw [← stdGaussian_eq_quadratic_tilted]
    simpa only [id_eq] using
      (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin D))) n (by simp)).integrable_norm_pow'
  score_jets := gaussian_score_polynomial

theorem gaussianEnvironment_law (D : ℕ) :
    (gaussianEnvironment D).law = stdGaussian (EuclideanSpace ℝ (Fin D)) := by
  exact stdGaussian_eq_quadratic_tilted.symm

instance gaussianEnvironment_probability (D : ℕ) :
    IsProbabilityMeasure (gaussianEnvironment D).law := by
  rw [gaussianEnvironment_law]
  infer_instance
end AcceleratedLogConcave.Analysis.AnglePhase
