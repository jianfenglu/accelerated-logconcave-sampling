import AcceleratedLogConcave.Numerics.MeanCollocationLp
import AcceleratedLogConcave.Numerics.ConditionalGeometricMesh
import AcceleratedLogConcave.Numerics.ForwardMeshBudget
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Concrete mean geometry for the source schedule

All three partitions are the existing ceiling-balanced geometric meshes. The
source powers are public parameters; the radius half-cap and step half-cap
remain explicit scalar conditions for the schedule theorem.
-/

noncomputable section
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.SourceMeanGeometry
open AffineGraph AffineGraph.MeanGeometry
open ReciprocalQuadrature

private theorem end_pos {R : ℝ} (hR : 0 < R) (hRhalf : R ≤ 1/2) :
    0 < backwardEnd R := by
  unfold backwardEnd
  apply Real.sqrt_pos.2
  nlinarith [sq_nonneg (R - 1/2)]

private theorem end_lt_one {R : ℝ} (hR : 0 < R) (_hRhalf : R ≤ 1/2) :
    backwardEnd R < 1 := by
  unfold backwardEnd
  apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2
  nlinarith [sq_pos_of_pos hR]

/-- The actual backward, conditional and forward partitions, at one common
geometric resolution. -/
def geometry (m : ℕ) (R ψ h₀ : ℝ) (hR : 0 < R) (hRhalf : R ≤ 1/2)
    (hψ : 0 < ψ) (hh₀ : 0 < h₀) : MeanGeometry m := by
  let B := actualKernelInterval R h₀ hR hRhalf hh₀
  let rho : Option (B.Source m) → ℝ := kernelValueLocation m B.point
  have hrho (ρ : Option (B.Source m)) : rho ρ < backwardEnd R := by
    cases ρ with
    | none => exact end_pos hR hRhalf
    | some z => exact (B.location_mem_interval m z).2
  exact actualMeanGeometry m R h₀ ψ hR hRhalf hh₀ hψ
    (fun _ => conditionalGeometricInterval h₀ hh₀)
    (fun ρ => probabilityGeometricInterval (rho ρ) (backwardEnd R) h₀
      (hrho ρ) (end_lt_one hR hRhalf) hh₀)

@[simp] theorem geometry_R (m : ℕ) (R ψ h₀ : ℝ) (hR : 0 < R)
    (hRhalf : R ≤ 1/2) (hψ : 0 < ψ) (hh₀ : 0 < h₀) :
    (geometry m R ψ h₀ hR hRhalf hψ hh₀).R = R := rfl

@[simp] theorem geometry_psi (m : ℕ) (R ψ h₀ : ℝ) (hR : 0 < R)
    (hRhalf : R ≤ 1/2) (hψ : 0 < ψ) (hh₀ : 0 < h₀) :
    (geometry m R ψ h₀ hR hRhalf hψ hh₀).psi = ψ := rfl

theorem geometry_backward (m : ℕ) (R ψ h₀ : ℝ) (hR : 0 < R)
    (hRhalf : R ≤ 1/2) (hψ : 0 < ψ) (hh₀ : 0 < h₀) :
    (geometry m R ψ h₀ hR hRhalf hψ hh₀).backward =
      actualKernelInterval R h₀ hR hRhalf hh₀ := rfl

theorem geometry_conditional (m : ℕ) (R ψ h₀ : ℝ) (hR : 0 < R)
    (hRhalf : R ≤ 1/2) (hψ : 0 < ψ) (hh₀ : 0 < h₀)
    (ρ : (geometry m R ψ h₀ hR hRhalf hψ hh₀).Kernel) :
    (geometry m R ψ h₀ hR hRhalf hψ hh₀).conditional ρ =
      conditionalGeometricInterval h₀ hh₀ := rfl

theorem geometry_forward (m : ℕ) (R ψ h₀ : ℝ) (hR : 0 < R)
    (hRhalf : R ≤ 1/2) (hψ : 0 < ψ) (hh₀ : 0 < h₀)
    (ρ : (geometry m R ψ h₀ hR hRhalf hψ hh₀).Kernel) :
    (geometry m R ψ h₀ hR hRhalf hψ hh₀).forward ρ =
      forwardGeometricInterval (geometry m R ψ h₀ hR hRhalf hψ hh₀) ρ h₀ hh₀ := rfl

theorem meshConditions {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (d : MeanFlowLp.Data ι m) (R ψ h₀ : ℝ) (hR : 0 < R)
    (hRhalf : R ≤ 1/2) (hψ : 0 < ψ) (hh₀ : 0 < h₀)
    (hm : 2 ≤ m) (hψone : ψ ≤ 1) (hhhalf : h₀ ≤ 1/2)
    (hG : d.G = geometry m R ψ h₀ hR hRhalf hψ hh₀) :
    MeanCollocationLp.MeshConditions d h₀ := by
  refine {
    order := hm
    psi_upper := ?_
    step_pos := hh₀
    step_upper := hhhalf
    backward := ?_ }
  · simpa only [hG, geometry_psi] using hψone
  · rw [hG]
    rfl

/-- Source specialization: `R = δ^t`, `ψ = δ^(4t)`, `h₀ = δ^w`.
The remaining half-caps are scalar schedule obligations. -/
def sourceGeometry (m : ℕ) (δ t w : ℝ) (hδ : 0 < δ) (_ht : 0 < t)
    (_hw : 0 < w) (hRhalf : δ^t ≤ 1/2) : MeanGeometry m :=
  geometry m (δ^t) (δ^(4*t)) (δ^w) (Real.rpow_pos_of_pos hδ t)
    hRhalf (Real.rpow_pos_of_pos hδ (4*t)) (Real.rpow_pos_of_pos hδ w)

theorem sourceGeometry_meshConditions {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (d : MeanFlowLp.Data ι m) (δ t w : ℝ) (hδ : 0 < δ)
    (hδone : δ ≤ 1) (ht : 0 < t) (hw : 0 < w)
    (hRhalf : δ^t ≤ 1/2) (hhhalf : δ^w ≤ 1/2)
    (hm : 2 ≤ m)
    (hG : d.G = sourceGeometry m δ t w hδ ht hw hRhalf) :
    MeanCollocationLp.MeshConditions d (δ^w) := by
  apply meshConditions d (δ^t) (δ^(4*t)) (δ^w)
    (Real.rpow_pos_of_pos hδ t) hRhalf
    (Real.rpow_pos_of_pos hδ (4*t)) (Real.rpow_pos_of_pos hδ w)
    hm (Real.rpow_le_one hδ.le hδone (by positivity)) hhhalf hG

end AcceleratedLogConcave.Numerics.SourceMeanGeometry
