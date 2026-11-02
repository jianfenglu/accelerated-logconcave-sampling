import AcceleratedLogConcave.Analysis.AnglePhaseCoefficients
import AcceleratedLogConcave.Analysis.GaussianPhaseJets
import AcceleratedLogConcave.Numerics.ConstantSkewBlockSplitNorm

/-! All Gaussian phase primitives other than the displacement gradient have
explicit constant-one or zero derivative tensors. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.AnglePhase
open Tensor Tensor.AdjointReduction Tensor.Ordered.Graph Tensor.PhaseExpression
open Numerics.CenterMeanSecondJetSource
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

private theorem partialAlong_constant_nonempty {V I : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : I → V) (J : List I) (c : ℝ) (hJ : J ≠ []) :
    partialAlong d J (fun _ => c) = fun _ => 0 := by
  induction J with
  | nil => exact False.elim (hJ rfl)
  | cons i J ih =>
    cases J with
    | nil =>
      funext x
      change fderiv ℝ (fun _ : V => c) x (d i) = 0
      simp only [fderiv_const_apply,zero_apply]
    | cons j J =>
      rw [partialAlong,ih (by simp)]
      funext x
      change fderiv ℝ (fun _ : V => (0:ℝ)) x (d i) = 0
      simp only [fderiv_const_apply,zero_apply]

theorem angle_constant_primitive_higher (T : E → E) (M : E) (q a : ℝ)
    (c : Primitive) (hc : c ≠ .observableGradient) (j : ℕ) (hj : 0 < j) (z : EP) :
    phaseCoefficientJet (angleCoefficients T M q a) c j z = 0 := by
  have hJ : List.finRange j ≠ [] := by
    intro h
    have hh : j = 0 := by simpa using congrArg List.length h
    omega
  ext u
  change partialAlong _ (List.finRange j)
    (fun x => angleCoefficients T M q a c x (fun i => u (.inr i))) z = 0
  have hconst : (fun x => angleCoefficients T M q a c x (fun i => u (.inr i))) =
      (fun _ => angleCoefficients T M q a c 0 (fun i => u (.inr i))) := by
    funext x
    cases c <;> simp_all [angleCoefficients,rotationEntry]
  rw [hconst,partialAlong_constant_nonempty _ _ _ hJ]

theorem angle_transport_zero_split (T : E → E) (M : E) (q a : ℝ)
    (z : EP) (S : Finset (Fin 0 ⊕ Fin 2)) (hS : NontrivialSplit S) :
    splitNorm (D+D) S
      (phaseCoefficientJet (angleCoefficients T M q a) .transport 0 z) ≤ 1 := by
  exact negativeIdentity_engine_transport_splitNorm_le (D := D) S hS

theorem angle_identity_zero_split (T : E → E) (M : E) (q a : ℝ)
    (c : Primitive) (hc : c = .scoreHessian ∨ c = .positionProjection)
    (z : EP) (S : Finset (Fin 0 ⊕ Fin 2)) (hS : NontrivialSplit S) :
    splitNorm (D+D) S
      (phaseCoefficientJet (angleCoefficients T M q a) c 0 z) ≤ 1 := by
  have he : phaseCoefficientJet (angleCoefficients T M q a) c 0 z =
      WithLp.toLp 2 (fun u : Fin 0 ⊕ Fin 2 → Fin (D+D) =>
        inner ℝ (coordinateDirection (D+D) (u (.inr 0)))
          (coordinateDirection (D+D) (u (.inr 1)))) := by
    ext u
    rcases hc with rfl | rfl <;>
      simp [phaseCoefficientJet,partialAlong,angleCoefficients,coordinateDirection,
        EuclideanSpace.inner_single_left,PiLp.single_apply] <;> rfl
  rw [he]
  exact ActualCoefficientIntegrability.pairIdentity_splitNorm_le
    (Slot := Fin 0 ⊕ Fin 2) (D := D+D) (by decide)
    (.inr 0) (.inr 1) (by decide) S hS
end AcceleratedLogConcave.Analysis.AnglePhase
