import AcceleratedLogConcave.Numerics.MeanInitialError
import AcceleratedLogConcave.Numerics.MeanSmoothCollocationLp
import AcceleratedLogConcave.Numerics.SmoothQuantitativeError

/-!
# Initializer and finite-iteration payment for the smooth mean receiver

The initial state is the actual direct vector of the common-seed graph. Its
one-step defect uses the seed moments and original primitive query bounds from
`MeanInitialError`. The only regularity input below concerns the same smooth
curves used by the quantitative assembly.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory AcceleratedLogConcave
open Numerics Numerics.MeanFlowLp Numerics.MeanResidualBridge Numerics.AffineGraph
open Numerics.AffineGraph.MeanGeometry Numerics.MeanCollocationLp
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace AcceleratedLogConcave.Numerics.SmoothInitialError
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

variable (d : Data ι m) (h₀ : ℝ) (h : MeshConditions d h₀)
  (l v : ℝ) (hl : l < 0) (hv : backwardEnd d.G.R < v)
  (D : AffineResidual.Mean.DerivativeBudget d.G)
  (hreg : AffineResidual.Mean.Regularity d.G (curvesWithSmoothBranches d)
    (operator d) 0 d.r l v D)
include h hl hv hreg

/-- The actual direct-vector defect and smooth-branch residual absorb the
unknown initial distance. There is no bound on the reference vector assumed. -/
theorem initialError_absorption :
    (1 - contraction d h₀) * initialError d ≤
      rowMass d h₀ * (d.ell * directBudget d + meanBudget d) +
        residualBudget d h₀ D := by
  let A := (lpGraph d).direct
  let P := (lpGraph d).step (operator d)
  let R := reference d
  have hC : ‖P A - P R‖ ≤ contraction d h₀ * initialError d := by
    apply (pi_norm_le_iff_of_nonneg
      (mul_nonneg (contraction_nonneg d h₀ h) (norm_nonneg _))).mpr
    exact contraction_target d h₀ h A R
  have hR : ‖P R - R‖ ≤ residualBudget d h₀ D := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    exact MeanSmoothCollocationLp.residual_bound d h₀ h l v hl hv D hreg
  have hA := direct_defect_le d h₀ h
  have h1 : ‖A - R‖ ≤ ‖A - P A‖ + ‖P A - R‖ :=
    norm_sub_le_norm_sub_add_norm_sub A (P A) R
  have h2 : ‖P A - R‖ ≤ ‖P A - P R‖ + ‖P R - R‖ :=
    norm_sub_le_norm_sub_add_norm_sub (P A) (P R) R
  have hsym : ‖A - P A‖ = ‖P A - A‖ := norm_sub_rev _ _
  change ‖P A - A‖ ≤ _ at hA
  change (1 - contraction d h₀) * ‖A - R‖ ≤ _
  change ‖P A - P R‖ ≤ contraction d h₀ * ‖A - R‖ at hC
  nlinarith

/-- A true half-contraction converts the defect into a public-data seed bound. -/
theorem initialError_le_of_half (hq : contraction d h₀ ≤ 1 / 2) :
    initialError d ≤ 2 *
      (rowMass d h₀ * (d.ell * directBudget d + meanBudget d) +
        residualBudget d h₀ D) := by
  have ha := initialError_absorption d h₀ h l v hl hv D hreg
  have hn : 0 ≤ initialError d := norm_nonneg _
  nlinarith

omit [DecidableEq ι] hl hv hreg in
/-- The existing affine resolution theorem pays the contraction at the
one-third power, on the actual graph matrix and the prescribed mesh. -/
theorem contraction_le_resolution {δ b t w S : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ w) (hwt : w ≤ t)
    (ht : t ≤ (1 : ℝ) / 60) (hb : (1 : ℝ) / 2 ≤ b) (hS : 1 ≤ S)
    (hpsi : d.G.psi = δ ^ (4 * t)) (hstep : h₀ = δ ^ w)
    (hsizeR : d.ell * d.r ^ 2 ≤ S * δ ^ b)
    (hsizeS : d.ell * d.r / d.sigma ≤ S * δ ^ b)
    (hres : δ ≤ (520 * (m : ℝ) ^ 5 * S) ^ (-12 : ℝ)) :
    contraction d h₀ ≤ δ ^ ((1 : ℝ) / 3) / 2 := by
  have he := affine_mean_envelope_le_rpow_third h.order hδ hδ1 hw hwt ht hb hS
    d.hsigma hsizeR hsizeS hres
  dsimp [contraction, rowMass]
  rw [hpsi, hstep]
  nlinarith

/-- The finite geometric error has an explicit seed payment and at most twice
the row residual. In particular, no unknown `initialError` remains. -/
theorem finite_payment (N : ℕ) (hq : contraction d h₀ ≤ 1 / 2) :
    ‖iterate d N - reference d‖ ≤
      (contraction d h₀) ^ N *
        (2 * (rowMass d h₀ * (d.ell * directBudget d + meanBudget d) +
          residualBudget d h₀ D)) +
      2 * residualBudget d h₀ D := by
  have hq0 := contraction_nonneg d h₀ h
  have hq1 : contraction d h₀ < 1 := by linarith
  have hinit := initialError_le_of_half d h₀ h l v hl hv D hreg hq
  have hgeom := MeanSmoothCollocationLp.geometric_bound d h₀ h l v hl hv D hreg N hq1
  have hden : 0 < 1 - contraction d h₀ := by linarith
  have hres0 : 0 ≤ residualBudget d h₀ D := norm_nonneg _
  have hres : residualBudget d h₀ D / (1 - contraction d h₀) ≤
      2 * residualBudget d h₀ D := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  exact hgeom.trans (add_le_add
    (mul_le_mul_of_nonneg_left hinit (pow_nonneg hq0 N)) hres)

/-- Under the displayed resolution hypotheses, each prescribed iteration
pays an additional factor at most `δ^(1/3)/2`. -/
theorem finite_payment_of_resolution (N : ℕ) {δ b t w S : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ w) (hwt : w ≤ t)
    (ht : t ≤ (1 : ℝ) / 60) (hb : (1 : ℝ) / 2 ≤ b) (hS : 1 ≤ S)
    (hpsi : d.G.psi = δ ^ (4 * t)) (hstep : h₀ = δ ^ w)
    (hsizeR : d.ell * d.r ^ 2 ≤ S * δ ^ b)
    (hsizeS : d.ell * d.r / d.sigma ≤ S * δ ^ b)
    (hres : δ ≤ (520 * (m : ℝ) ^ 5 * S) ^ (-12 : ℝ)) :
    ‖iterate d N - reference d‖ ≤
      (δ ^ ((1 : ℝ) / 3) / 2) ^ N *
        (2 * (rowMass d h₀ * (d.ell * directBudget d + meanBudget d) +
          residualBudget d h₀ D)) +
      2 * residualBudget d h₀ D := by
  have hq := contraction_le_resolution d h₀ h hδ hδ1 hw hwt ht
    hb hS hpsi hstep hsizeR hsizeS hres
  have hp : δ ^ ((1 : ℝ) / 3) ≤ 1 :=
    Real.rpow_le_one hδ.le hδ1 (by norm_num)
  have hhalf : contraction d h₀ ≤ 1 / 2 := by linarith
  have hseed : 0 ≤ 2 * (rowMass d h₀ * (d.ell * directBudget d + meanBudget d) +
      residualBudget d h₀ D) := by
    have hi := initialError_absorption d h₀ h l v hl hv D hreg
    have hq0 := contraction_nonneg d h₀ h
    have hn : 0 ≤ initialError d := norm_nonneg _
    nlinarith
  exact (finite_payment d h₀ h l v hl hv D hreg N hhalf).trans
    (add_le_add (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (contraction_nonneg d h₀ h) hq N) hseed) le_rfl)

/-- The same finite-iteration payment reaches the original common-seed output,
with the separate center quadrature term retained. -/
theorem final_payment_of_resolution (N : ℕ) {δ b t w S : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ w) (hwt : w ≤ t)
    (ht : t ≤ (1 : ℝ) / 60) (hb : (1 : ℝ) / 2 ≤ b) (hS : 1 ≤ S)
    (hpsi : d.G.psi = δ ^ (4 * t)) (hstep : h₀ = δ ^ w)
    (hsizeR : d.ell * d.r ^ 2 ≤ S * δ ^ b)
    (hsizeS : d.ell * d.r / d.sigma ≤ S * δ ^ b)
    (hres : δ ≤ (520 * (m : ℝ) ^ 5 * S) ^ (-12 : ℝ)) :
    ‖output d N - terminalTarget d‖ ≤
      d.ell * ((δ ^ ((1 : ℝ) / 3) / 2) ^ N *
        (2 * (rowMass d h₀ * (d.ell * directBudget d + meanBudget d) +
          residualBudget d h₀ D)) +
        2 * residualBudget d h₀ D) +
      2 * D.center / (m.factorial : ℝ) := by
  have hq := contraction_le_resolution d h₀ h hδ hδ1 hw hwt ht hb hS hpsi
    hstep hsizeR hsizeS hres
  have hp : δ ^ ((1 : ℝ) / 3) ≤ 1 :=
    Real.rpow_le_one hδ.le hδ1 (by norm_num)
  have hhalf : contraction d h₀ ≤ 1 / 2 := by linarith
  have hq1 : contraction d h₀ < 1 := by linarith
  have hinit := initialError_le_of_half d h₀ h l v hl hv D hreg hhalf
  have hseed : 0 ≤ 2 * (rowMass d h₀ * (d.ell * directBudget d + meanBudget d) +
      residualBudget d h₀ D) := by
    have hi := initialError_absorption d h₀ h l v hl hv D hreg
    have hq0 := contraction_nonneg d h₀ h
    have hn : 0 ≤ initialError d := norm_nonneg _
    nlinarith
  have hpow : contraction d h₀ ^ N ≤ (δ ^ ((1 : ℝ) / 3) / 2) ^ N :=
    pow_le_pow_left₀ (contraction_nonneg d h₀ h) hq N
  have hden : 0 < 1 - contraction d h₀ := by linarith
  have hres0 : 0 ≤ residualBudget d h₀ D := norm_nonneg _
  have hres' : residualBudget d h₀ D / (1 - contraction d h₀) ≤
      2 * residualBudget d h₀ D := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hpayment : contraction d h₀ ^ N * initialError d +
      residualBudget d h₀ D / (1 - contraction d h₀) ≤
      (δ ^ ((1 : ℝ) / 3) / 2) ^ N *
        (2 * (rowMass d h₀ * (d.ell * directBudget d + meanBudget d) +
          residualBudget d h₀ D)) + 2 * residualBudget d h₀ D := by
    apply add_le_add _ hres'
    exact (mul_le_mul_of_nonneg_left hinit
      (pow_nonneg (contraction_nonneg d h₀ h) N)).trans
      (mul_le_mul_of_nonneg_right hpow hseed)
  have hfinal := SmoothQuantitativeError.geometric_final_bound d h₀ h l v hl hv D hreg N hq1
  calc
    ‖output d N - terminalTarget d‖ ≤
        d.ell * (contraction d h₀ ^ N * initialError d +
          residualBudget d h₀ D / (1 - contraction d h₀)) +
          2 * D.center / (m.factorial : ℝ) := by
        convert hfinal using 1; ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hpayment d.hell) le_rfl

end AcceleratedLogConcave.Numerics.SmoothInitialError
