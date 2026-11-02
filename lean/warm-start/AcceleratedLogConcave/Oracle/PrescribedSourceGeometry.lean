import AcceleratedLogConcave.Oracle.PrescribedMeshDimensions

/-! Literal prescribed source geometry. All partitions and finite enumerations
are constructed here. Anchors, seeds, analytic certificates, B and resolution
remain separate. Noncomputable equivalences make no bit-runtime claim. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.PrescribedSourceGeometry
open Numerics Numerics.AffineGraph Numerics.GeometricMesh Numerics.ReciprocalQuadrature
open Numerics.PrescribedMeshCardinality

variable (m : ℕ) (R h₀ : ℝ) (hR : 0 < R) (hRh : R ≤ 1/2) (hh : 0 < h₀)

/-- This endpoint fact depends only on the fixed backward kernel. -/
theorem kernel_location_mem (ρ : Option ((actualKernelInterval R h₀ hR hRh hh).Source m)) :
    0 ≤ kernelValueLocation m (actualKernelInterval R h₀ hR hRh hh).point ρ ∧
    kernelValueLocation m (actualKernelInterval R h₀ hR hRh hh).point ρ < backwardEnd R := by
  cases ρ with
  | none => exact ⟨le_rfl, (actualKernelInterval R h₀ hR hRh hh).lo_lt_hi⟩
  | some z => exact ⟨((actualKernelInterval R h₀ hR hRh hh).location_mem_interval m z).1.le,
      ((actualKernelInterval R h₀ hR hRh hh).location_mem_interval m z).2⟩

/-- Constructed before the mean geometry, so there is no recursive mesh choice. -/
def forwardPartition (ρ : Option ((actualKernelInterval R h₀ hR hRh hh).Source m)) :
    IntervalMesh (kernelValueLocation m (actualKernelInterval R h₀ hR hRh hh).point ρ) (backwardEnd R) :=
  probabilityGeometricInterval _ _ h₀ (kernel_location_mem m R h₀ hR hRh hh ρ).2
    (kernel_endpoint_bounds hR hRh).2 hh

/-- The prescribed partitions and the exact angle scale psi=R^4. -/
def meanGeometry : MeanGeometry m :=
  actualMeanGeometry m R h₀ (R^4) hR hRh hh (pow_pos hR 4)
    (fun _ => conditionalGeometricInterval h₀ hh) (forwardPartition m R h₀ hR hRh hh)

@[simp] theorem mean_R : (meanGeometry m R h₀ hR hRh hh).R = R := rfl
@[simp] theorem mean_psi : (meanGeometry m R h₀ hR hRh hh).psi = R^4 := rfl
@[simp] theorem mean_backward : (meanGeometry m R h₀ hR hRh hh).backward =
    actualKernelInterval R h₀ hR hRh hh := rfl
@[simp] theorem mean_conditional (ρ : (meanGeometry m R h₀ hR hRh hh).Kernel) :
    (meanGeometry m R h₀ hR hRh hh).conditional ρ = conditionalGeometricInterval h₀ hh := rfl

/-- The already constructed forward partition is the prescribed one of the assembled geometry. -/
theorem mean_forward (ρ : (meanGeometry m R h₀ hR hRh hh).Kernel) :
    (meanGeometry m R h₀ hR hRh hh).forward ρ =
      forwardGeometricInterval (meanGeometry m R h₀ hR hRh hh) ρ h₀ hh := rfl

/-- Literal private sampling partition, at tau=R/sqrt(1-R^2). -/
def privateMesh : IntervalMesh 0 (samplingEnd (R/backwardEnd R)) :=
  probabilityGeometricInterval 0 _ h₀
    (sampling_endpoint hR (private_tau_mem hR hRh).1 (private_tau_mem hR hRh).2).1
    (sampling_endpoint hR (private_tau_mem hR hRh).1 (private_tau_mem hR hRh).2).2 hh

def samplingGeometry : SamplingGeometry m :=
  RecursiveExecutable.privateGeometry (meanGeometry m R h₀ hR hRh hh) (privateMesh R h₀ hR hRh hh)

@[simp] theorem sampling_R : (samplingGeometry m R h₀ hR hRh hh).R = R := rfl
@[simp] theorem sampling_tau : (samplingGeometry m R h₀ hR hRh hh).τ = R/backwardEnd R := rfl

theorem sampling_mesh : (samplingGeometry m R h₀ hR hRh hh).mesh =
    probabilityGeometricInterval 0 (samplingEnd (samplingGeometry m R h₀ hR hRh hh).τ) h₀
      (samplingGeometry m R h₀ hR hRh hh).samplingEnd_pos
      (samplingGeometry m R h₀ hR hRh hh).samplingEnd_lt_one hh := rfl

/-- Exact dimensions, with no externally supplied enumeration or node count. -/
def meanCount : ℕ := Fintype.card (meanGeometry m R h₀ hR hRh hh).MeanNode
def privateCount : ℕ := Fintype.card ((privateMesh R h₀ hR hRh hh).Source m)

/-- Static source data only; Ds, delta, t, w and layers remain caller parameters. -/
def source (Ds δ t w : ℝ) (layers : ℕ) :
    RecursiveCall.Source m (meanCount m R h₀ hR hRh hh) (privateCount m R h₀ hR hRh hh) where
  M := meanGeometry m R h₀ hR hRh hh
  nodes := (Fintype.equivFin _).symm
  mesh := privateMesh R h₀ hR hRh hh
  snodes := (Fintype.equivFin _).symm
  Ds := Ds
  δ := δ
  t := t
  w := w
  layers := layers

variable (Ds δ t w : ℝ) (layers : ℕ)
@[simp] theorem source_mean : (source m R h₀ hR hRh hh Ds δ t w layers).M =
    meanGeometry m R h₀ hR hRh hh := rfl
@[simp] theorem source_mesh : (source m R h₀ hR hRh hh Ds δ t w layers).mesh =
    privateMesh R h₀ hR hRh hh := rfl
@[simp] theorem source_sampling : (source m R h₀ hR hRh hh Ds δ t w layers).S =
    samplingGeometry m R h₀ hR hRh hh := rfl

theorem source_nodes : (source m R h₀ hR hRh hh Ds δ t w layers).nodes =
    (Fintype.equivFin (meanGeometry m R h₀ hR hRh hh).MeanNode).symm := rfl

theorem source_snodes : (source m R h₀ hR hRh hh Ds δ t w layers).snodes =
    (Fintype.equivFin ((privateMesh R h₀ hR hRh hh).Source m)).symm := rfl

theorem source_parameters :
    let C := source m R h₀ hR hRh hh Ds δ t w layers
    C.Ds = Ds ∧ C.δ = δ ∧ C.t = t ∧ C.w = w ∧ C.layers = layers ∧ C.M.R = R ∧ C.M.psi = R^4 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Count bounds with no mesh-identity premises. -/
theorem counts (hm : 2 ≤ m) (hhalf : h₀ ≤ 1/2) :
    (meanCount m R h₀ hR hRh hh:ℝ) ≤ 1280*(m:ℝ)^4*(meshBudget R h₀)^2 ∧
    (privateCount m R h₀ hR hRh hh:ℝ) ≤ 16*(m:ℝ)*meshBudget R h₀ := by
  constructor
  · exact PrescribedMeshDimensions.mean_card_le _ hm h₀ hh hhalf rfl (fun _ => rfl)
      (mean_forward m R h₀ hR hRh hh)
  · exact PrescribedMeshDimensions.sampling_card_le (samplingGeometry m R h₀ hR hRh hh)
      hm h₀ hh hhalf (sampling_mesh m R h₀ hR hRh hh)

/-- The actual backward constructor is also the prescribed probability mesh. -/
theorem backward_probability : (meanGeometry m R h₀ hR hRh hh).backward =
    probabilityGeometricInterval 0 (backwardEnd R) h₀
      (meanGeometry m R h₀ hR hRh hh).backwardEnd_pos
      (meanGeometry m R h₀ hR hRh hh).backwardEnd_lt_one hh := rfl

theorem backward_step (hhalf : h₀ ≤ 1/2) (c : (meanGeometry m R h₀ hR hRh hh).backward.Cell) :
    (meanGeometry m R h₀ hR hRh hh).backward.length c ≤
      2*h₀*(1-((meanGeometry m R h₀ hR hRh hh).backward.right c)^2) := by
  exact probabilityGeometricInterval_step 0 (backwardEnd R) h₀
    (meanGeometry m R h₀ hR hRh hh).backwardEnd_pos
    (meanGeometry m R h₀ hR hRh hh).backwardEnd_lt_one hh hhalf le_rfl c

theorem backward_firstCell (hhalf : h₀ ≤ 1/2) :
    h₀/4 ≤ (meanGeometry m R h₀ hR hRh hh).backward.length 0 :=
  actualKernelInterval_firstCell_lower hR hRh hh hhalf

theorem conditional_step (hhalf : h₀ ≤ 1/2) (ρ : (meanGeometry m R h₀ hR hRh hh).Kernel)
    (c : ((meanGeometry m R h₀ hR hRh hh).conditional ρ).Cell) :
    ((meanGeometry m R h₀ hR hRh hh).conditional ρ).length c ≤
      2*h₀*(1-(((meanGeometry m R h₀ hR hRh hh).conditional ρ).right c)^2) :=
  conditionalGeometricInterval_step h₀ hh hhalf c

theorem forward_step (hhalf : h₀ ≤ 1/2) (ρ : (meanGeometry m R h₀ hR hRh hh).Kernel)
    (c : ((meanGeometry m R h₀ hR hRh hh).forward ρ).Cell) :
    ((meanGeometry m R h₀ hR hRh hh).forward ρ).length c ≤
      2*h₀*(1-(((meanGeometry m R h₀ hR hRh hh).forward ρ).right c)^2) :=
  forwardGeometricInterval_step (meanGeometry m R h₀ hR hRh hh) ρ h₀ hh hhalf c

theorem private_step (hhalf : h₀ ≤ 1/2) (c : (privateMesh R h₀ hR hRh hh).Cell) :
    (privateMesh R h₀ hR hRh hh).length c ≤ 2*h₀*(1-((privateMesh R h₀ hR hRh hh).right c)^2) :=
  probabilityGeometricInterval_step 0 _ h₀
    (sampling_endpoint hR (private_tau_mem hR hRh).1 (private_tau_mem hR hRh).2).1
    (sampling_endpoint hR (private_tau_mem hR hRh).1 (private_tau_mem hR hRh).2).2 hh hhalf le_rfl c

/-- Exact exponent specialization; no mesh refinement or angle change. -/
theorem rpow_psi (hδ : 0 < δ) (hδt : δ^t ≤ 1/2) :
    (meanGeometry m (δ^t) (δ^w) (Real.rpow_pos_of_pos hδ t) hδt (Real.rpow_pos_of_pos hδ w)).psi =
      δ^(4*t) := by
  rw [mean_psi, mul_comm (4:ℝ) t]
  exact (Real.rpow_mul_natCast hδ.le t 4).symm

set_option backward.isDefEq.respectTransparency false in
/-- Both dimensions of the fully constructed source. B and the half-step cap
are still explicit; there are no supplied mesh identities or count bounds. -/
theorem source_dimensions (Ds : ℝ) (layers : ℕ) (hm : 2 ≤ m) (hδ : 0 < δ) (hδt : δ^t ≤ 1/2) (hδw : δ^w ≤ 1/2)
    (B : ℝ) (hB : Real.sqrt 1280*(m:ℝ)^2*(1+|Real.log (δ^t)|) ≤ B) :
    Real.sqrt (meanCount m (δ^t) (δ^w) (Real.rpow_pos_of_pos hδ t) hδt (Real.rpow_pos_of_pos hδ w)) ≤
      B*δ^(-w) ∧
    Real.sqrt (privateCount m (δ^t) (δ^w) (Real.rpow_pos_of_pos hδ t) hδt (Real.rpow_pos_of_pos hδ w)) ≤
      B*δ^(-w) := by
  let C := source m (δ^t) (δ^w) (Real.rpow_pos_of_pos hδ t) hδt (Real.rpow_pos_of_pos hδ w) Ds δ t w layers
  exact PrescribedMeshDimensions.source_dimension_bounds C hm hδ hδw rfl rfl
    (fun _ => rfl) (fun _ => rfl) rfl B hB
end AcceleratedLogConcave.Oracle.PrescribedSourceGeometry
