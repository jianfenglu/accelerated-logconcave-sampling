import AcceleratedLogConcave.Tensor.PolynomialClosure

/-! Canonical coordinate jets suffice for qualitative polynomial tails of
arbitrary ordered directional jets. No moment or RMS bound is assumed. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Tensor.PolynomialClosure
open AdjointReduction Conditional.Appell
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

def CoordinatePolynomialJets (f : E → ℝ) : Prop :=
  ∀ J : List (Fin D), HasGrowth (partialAlong (coordinateDirection D) J f)

theorem dir_eq_sum_coordinates (v : E) (f : E → ℝ) :
    dir v f = fun x => ∑ i, v i * dir (coordinateDirection D i) f x := by
  have hv : v = ∑ i, v i • coordinateDirection D i := by
    ext j
    simp [coordinateDirection,Pi.single_apply]
  funext x
  change fderiv ℝ f x v = _
  calc
    _ = fderiv ℝ f x (∑ i, v i • coordinateDirection D i) := congrArg _ hv
    _ = _ := by simp [dir]

theorem CoordinatePolynomialJets.direction {f : E → ℝ}
    (hf : CoordinatePolynomialJets f) (hs : ContDiff ℝ ∞ f) (v : E) :
    CoordinatePolynomialJets (dir v f) := by
  intro J
  rw [partialAlong_dir _ J hs,dir_eq_sum_coordinates]
  exact HasGrowth.sum Finset.univ (fun i _ =>
    (HasGrowth.const (v i)).mul (hf (i::J)))

theorem CoordinatePolynomialJets.toPolynomialJets {f : E → ℝ}
    (hf : CoordinatePolynomialJets f) (hs : ContDiff ℝ ∞ f) : HasPolynomialJets f := by
  intro J
  induction J generalizing f with
  | nil => exact hf []
  | cons v J ih =>
    change HasGrowth (dir v (partialAlong id J f))
    rw [← partialAlong_dir id J hs v]
    exact ih (hf.direction hs v) (contDiff_dir hs v)

theorem coordinatePolynomialJets_of_bounded {f : E → ℝ}
    (h : ∀ J : List (Fin D), ∃ C : ℝ, ∀ x,
      ‖partialAlong (coordinateDirection D) J f x‖ ≤ C) : CoordinatePolynomialJets f := by
  intro J
  obtain ⟨C,hC⟩ := h J
  refine ⟨max C 0,le_max_right _ _,0,?_⟩
  intro x
  have hh := hC x
  simp only [pow_zero]
  have hmax := le_max_left C 0
  have hnonneg := le_max_right C 0
  nlinarith
end AcceleratedLogConcave.Tensor.PolynomialClosure
