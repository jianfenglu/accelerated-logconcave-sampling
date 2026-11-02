import AcceleratedLogConcave.Numerics.SourceMeanGeometry

/-!
# Original-data numerical input on the prescribed source meshes

The parameter record contains only the original potential, Hessian bounds,
initial data and scalar domain facts. It does not contain any numerical
accuracy or regularity conclusion. The derived `MeanFlowLp.Data` uses the
literal three source partitions.
-/

noncomputable section
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.SourceNumericalData
open AffineGraph AffineGraph.MeanGeometry SourceMeanGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

structure Inputs (ι : Type*) [Fintype ι] (m : ℕ) where
  F : EuclideanSpace ℝ ι → ℝ
  hF : ContDiff ℝ 2 F
  ell : ℝ
  hell : 0 ≤ ell
  hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a
  hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2
  x : EuclideanSpace ℝ ι
  r : ℝ
  hr : 0 < r
  hsmall : r ^ 2 * ell ≤ 1/2
  sigma : ℝ
  hsigma : 0 < sigma
  δ : ℝ
  t : ℝ
  w : ℝ
  hδ : 0 < δ
  ht : 0 < t
  hw : 0 < w
  hRhalf : δ^t ≤ 1/2

/-- A real common-seed numerical datum built from original analytic facts and
the public source geometry. -/
def data (P : Inputs ι m) : MeanFlowLp.Data ι m where
  F := P.F
  hF := P.hF
  ell := P.ell
  hell := P.hell
  hlo := P.hlo
  hup := P.hup
  x := P.x
  r := P.r
  hr := P.hr
  hsmall := P.hsmall
  G := sourceGeometry m P.δ P.t P.w P.hδ P.ht P.hw P.hRhalf
  sigma := P.sigma
  hsigma := P.hsigma

omit [DecidableEq ι] in
@[simp] theorem data_geometry (P : Inputs ι m) :
    (data P).G = sourceGeometry m P.δ P.t P.w P.hδ P.ht P.hw P.hRhalf := rfl

omit [DecidableEq ι] in
theorem data_backward (P : Inputs ι m) :
    (data P).G.backward =
      actualKernelInterval (P.δ^P.t) (P.δ^P.w)
        (Real.rpow_pos_of_pos P.hδ P.t) P.hRhalf
        (Real.rpow_pos_of_pos P.hδ P.w) :=
  geometry_backward m (P.δ^P.t) (P.δ^(4*P.t)) (P.δ^P.w)
    (Real.rpow_pos_of_pos P.hδ P.t) P.hRhalf
    (Real.rpow_pos_of_pos P.hδ (4*P.t)) (Real.rpow_pos_of_pos P.hδ P.w)

omit [DecidableEq ι] in
theorem data_conditional (P : Inputs ι m) (ρ : (data P).G.Kernel) :
    (data P).G.conditional ρ =
      conditionalGeometricInterval (P.δ^P.w) (Real.rpow_pos_of_pos P.hδ P.w) :=
  geometry_conditional m (P.δ^P.t) (P.δ^(4*P.t)) (P.δ^P.w)
    (Real.rpow_pos_of_pos P.hδ P.t) P.hRhalf
    (Real.rpow_pos_of_pos P.hδ (4*P.t)) (Real.rpow_pos_of_pos P.hδ P.w) ρ

omit [DecidableEq ι] in
theorem data_forward (P : Inputs ι m) (ρ : (data P).G.Kernel) :
    (data P).G.forward ρ =
      forwardGeometricInterval (data P).G ρ (P.δ^P.w)
        (Real.rpow_pos_of_pos P.hδ P.w) :=
  geometry_forward m (P.δ^P.t) (P.δ^(4*P.t)) (P.δ^P.w)
    (Real.rpow_pos_of_pos P.hδ P.t) P.hRhalf
    (Real.rpow_pos_of_pos P.hδ (4*P.t)) (Real.rpow_pos_of_pos P.hδ P.w) ρ

theorem data_meshConditions (P : Inputs ι m) (hm : 2 ≤ m)
    (hδone : P.δ ≤ 1) (hhhalf : P.δ^P.w ≤ 1/2) :
    MeanCollocationLp.MeshConditions (data P) (P.δ^P.w) :=
  sourceGeometry_meshConditions (data P) P.δ P.t P.w P.hδ hδone P.ht P.hw
    P.hRhalf hhhalf hm rfl

end AcceleratedLogConcave.Numerics.SourceNumericalData
