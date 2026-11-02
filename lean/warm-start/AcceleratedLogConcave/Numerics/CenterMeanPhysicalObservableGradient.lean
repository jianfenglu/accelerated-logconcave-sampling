import AcceleratedLogConcave.Numerics.CenterMeanPhysicalPrimitiveBudgets

/-! NEW reconstruction; SOURCE ONLY. The actual normalized mean gradient is
b times normalized J₁, including ell=0. No desired-bound assumption. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor Tensor.AdjointReduction
open Tensor.ActualCoefficientIntegrability Tensor.PhysicalKernelBudget
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

/-- Literal normalized gradient coordinate, output u and input v. -/
def sourceObservableGradientEntry (d : Data (Fin D)) (u v : E) (y : E) : ℝ :=
  (d.r*d.ell)⁻¹ * fderiv ℝ
    (fun z => inner ℝ u (M d z - meanOffset d)) y v

theorem sourceObservableGradientEntry_eq (d : Data (Fin D)) (u v y : E) :
    sourceObservableGradientEntry d u v y =
      d.b * ((d.ell*d.r)⁻¹ * inner ℝ u
        (firstScaledJet d.F d.x d.r d.b y v)) := by
  have hm := ((smooth_M d).differentiable (by simp) y).hasFDerivAt
  have h := (innerSL ℝ u).hasFDerivAt.comp y (hm.sub_const (meanOffset d))
  change HasFDerivAt (fun z => inner ℝ u (M d z - meanOffset d)) _ y at h
  unfold sourceObservableGradientEntry
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  change (d.r*d.ell)⁻¹ * inner ℝ u
    (fderiv ℝ (conditionalMean d.F d.x d.r d.b) y v) = _
  rw [fderiv_conditionalMean_eq_smul_firstScaledJet d.hF d.hlo d.hup
    d.x d.r (by linarith [d.hb]) d.hb1]
  simp only [smul_apply, inner_smul_right]
  rw [mul_comm d.r d.ell]
  ring

/-- n spatial derivatives; terminal output is inr (), terminal input inl(inr 0). -/
def sourceObservableGradientJet (d : Data (Fin D)) (n : ℕ) (y : E) :
    Coeff ((Fin n ⊕ Fin 1) ⊕ Unit) D :=
  WithLp.toLp 2 (fun a => JetCalculus.jet
    (fun i : Fin n => coordinateDirection D (a (.inl (.inl i)))) (List.finRange n)
    (sourceObservableGradientEntry d (coordinateDirection D (a (.inr ())))
      (coordinateDirection D (a (.inl (.inr 0))))) y)

theorem sourceObservableGradientJet_eq (d : Data (Fin D)) (n : ℕ) (y : E) :
    sourceObservableGradientJet d n y = d.b •
      normalizedJetDerivativeCoefficient d.F d.x d.ell d.r d.b 0 n y := by
  ext a
  let b : Fin 2 → Fin D := Fin.cons (a (.inr ())) (fun i => a (.inl (.inr i)))
  have he : sourceObservableGradientEntry d
      (coordinateDirection D (a (.inr ())))
      (coordinateDirection D (a (.inl (.inr 0)))) =
      fun z => d.b * coefficientEnvironment d.F d.x d.ell d.r d.b (.inl 0) z b := by
    funext z
    rw [sourceObservableGradientEntry_eq]
    change _ = d.b * ((d.ell*d.r*((0+1).factorial : ℝ))⁻¹ *
      inner ℝ (coordinateDirection D (b 0))
        (scaledJet 1 d.F d.x d.r d.b z (fun i => coordinateDirection D (b i.succ))))
    rw [ScaledJetPolynomial.scaledJet_one_apply_eq_firstScaledJet
      d.hF d.hlo d.hup d.x d.r (by linarith [d.hb]) d.hb1]
    simp [b]
  have hJ := contDiff_scaledJet_spatial 1 d.hF d.hlo d.hup d.x d.r
    (by linarith [d.hb] : -1 < d.b) d.hb1
  have hc : ContDiff ℝ ∞ (fun z =>
      coefficientEnvironment d.F d.x d.ell d.r d.b (.inl 0) z b) := by
    change ContDiff ℝ ∞ (fun z => (d.ell*d.r*((0+1).factorial : ℝ))⁻¹ *
      inner ℝ (coordinateDirection D (b 0))
        (scaledJet 1 d.F d.x d.r d.b z (fun i => coordinateDirection D (b i.succ))))
    exact contDiff_const.mul (contDiff_const.inner ℝ
      ((ScaledJetPolynomial.tensorEvaluation 1
        (fun i => coordinateDirection D (b i.succ))).contDiff.comp hJ))
  change JetCalculus.jet _ _ _ y = _
  rw [he, JetCalculus.jet_const_mul hc]
  rfl

/-- The retained factor b≤1 gives exactly the c₀=2 primitive allowance;
normalization is r*ell, not ell or an adjusted scale. -/
theorem sourceObservableGradientJet_budget (d : Data (Fin D)) (n : ℕ) (y : E)
    (S : Finset ((Fin n ⊕ Fin 1) ⊕ Unit)) (hS : NontrivialSplit S) :
    splitNorm D S (sourceObservableGradientJet d n y) ≤
      (2:ℝ)^(2+n)*((2+n).factorial : ℝ)*
        ((Real.sqrt (conditionalVariance d.b))^n)⁻¹ := by
  rw [sourceObservableGradientJet_eq, splitNorm_smul, abs_of_nonneg d.hb]
  have h := normalizedJetDerivativeCoefficient_budget (positiveVarianceData d) 0 n
    ⟨by linarith [d.hb], d.hb1⟩ y S hS
  simp only [Nat.zero_add] at h
  apply (mul_le_mul_of_nonneg_left h d.hb).trans
  exact (mul_le_mul_of_nonneg_right d.hb1.le (by positivity)).trans_eq (one_mul _)

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
