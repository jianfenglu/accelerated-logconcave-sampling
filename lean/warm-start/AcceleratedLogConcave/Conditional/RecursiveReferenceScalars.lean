import AcceleratedLogConcave.Conditional.TerminalChildrenParentFamilyJoint
import AcceleratedLogConcave.Oracle.Termination

/-! Actual active-final parameters and decreasing precision, warm-start.tex
compiler-labels and routine-sizes. No reference kernel or analytic estimate is
assumed here. The child keeps the original potential and changes only its center,
radius and width. -/
noncomputable section
open Set
namespace AcceleratedLogConcave.Conditional.RecursiveReference

 theorem child_small {ell r R : ℝ} (hell : 0 ≤ ell) (_hr : 0 < r)
    (hR : 0 < R) (hRle : R ≤ 1 / 2) (hs : r ^ 2 * ell ≤ 1 / 2) :
    (r * R) ^ 2 * ell ≤ 1 / 2 := by
  have hR1 : R ^ 2 ≤ 1 := by nlinarith
  have hp : 0 ≤ r ^ 2 * ell := mul_nonneg (sq_nonneg _) hell
  calc
    (r * R) ^ 2 * ell = R ^ 2 * (r ^ 2 * ell) := by ring
    _ ≤ 1 * (r ^ 2 * ell) := mul_le_mul_of_nonneg_right hR1 hp
    _ ≤ 1 / 2 := by simpa using hs

 theorem precision_child_lt {q t : ℝ} (ht : 0 < t) (hq : 1 / 2 < q) :
    Oracle.Precision.precisionRank t (q - t) < Oracle.Precision.precisionRank t q := by
  have h := Oracle.Precision.precisionRank_drop ht hq (le_refl (q - t))
  omega

variable {ι : Type*} {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

/-- Literal active-final parameter map, including the physical child width. -/
def childParameters {ell : ℝ} (hell : 0 ≤ ell)
    (G : Numerics.AffineGraph.MeanGeometry m) (theta : SourceParameters E ell)
    (center : E) : SourceParameters E ell :=
  ⟨(center, theta.radius * G.R, G.R * Real.sqrt 3 * theta.width / 4),
    mul_pos theta.radius_pos G.R_pos,
    div_pos (mul_pos (mul_pos G.R_pos (Real.sqrt_pos.mpr (by norm_num))) theta.width_pos)
      (by norm_num),
    child_small hell theta.radius_pos G.R_pos G.R_le_half theta.small⟩

@[simp] theorem childParameters_center {ell : ℝ} (hell : 0 ≤ ell)
    (G : Numerics.AffineGraph.MeanGeometry m) (theta : SourceParameters E ell) (center : E) :
    (childParameters hell G theta center).center = center := rfl

@[simp] theorem childParameters_radius {ell : ℝ} (hell : 0 ≤ ell)
    (G : Numerics.AffineGraph.MeanGeometry m) (theta : SourceParameters E ell) (center : E) :
    (childParameters hell G theta center).radius = theta.radius * G.R := rfl

@[simp] theorem childParameters_width {ell : ℝ} (hell : 0 ≤ ell)
    (G : Numerics.AffineGraph.MeanGeometry m) (theta : SourceParameters E ell) (center : E) :
    (childParameters hell G theta center).width = G.R * Real.sqrt 3 * theta.width / 4 := rfl

 theorem continuous_childParameters {ell : ℝ} (hell : 0 ≤ ell)
    (G : Numerics.AffineGraph.MeanGeometry m) :
    Continuous (fun z : SourceParameters E ell × E => childParameters hell G z.1 z.2) := by
  apply Continuous.subtype_mk
  exact continuous_snd.prodMk
    (((SourceParameters.continuous_radius.comp continuous_fst).mul_const G.R).prodMk
      ((continuous_const.mul (SourceParameters.continuous_width.comp continuous_fst)).div_const 4))

/-- Exact source precision after a chain of active-final edges. -/
theorem precision_after_step (q t : ℝ) (n : ℕ) :
    q - (n + 1 : ℕ) * t = (q - (n : ℝ) * t) - t := by
  push_cast
  ring

end AcceleratedLogConcave.Conditional.RecursiveReference
