import AcceleratedLogConcave.Numerics.AffineQuadrature

/-!
# AffineResidual

Actual sampling and five-family mean graph defects. Physical radii and centers
come from AffineGraph. Exact flow, kernel, and regularity suppliers remain explicit.
-/

noncomputable section AffineResidualResidualDefs
open MeasureTheory Set
open scoped BigOperators ContDiff
open AcceleratedLogConcave.Numerics
open AcceleratedLogConcave.Numerics.AffineGraph
open AcceleratedLogConcave.Numerics.AffineGraph.MeanGeometry
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.AffineResidual
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

namespace Sampling
variable {m : ℕ} (S : SamplingGeometry m)

def meanCurve (u : E → ℝ → E) (x : E) (r : ℝ) (Y : ℝ → E) (a : ℝ) : E :=
  u (x + (r*a) • Y a) (r * Real.sqrt (1-a^2))

def reference (x : E) (r : ℝ) (Y : ℝ → E) (i : S.Node) : E :=
  x + (r * S.mesh.location m i) • Y (S.mesh.location m i)

def FlowEquation (u : E → ℝ → E) (x y0 : E) (r : ℝ) (Y : ℝ → E) : Prop :=
  ∀ a ∈ Icc (0:ℝ) (samplingEnd S.τ),
    Y a = y0 - r • ∫ t in 0..a, meanCurve u x r Y t

def ResidualStatement : Prop :=
  1 ≤ m → ∀ (r : ℝ), 0 < r → ∀ (u : E → ℝ → E) (x y0 : E)
    (Y : ℝ → E) (D : S.mesh.Cell → ℝ),
    FlowEquation S u x y0 r Y → CellRegularity S.mesh m (meanCurve u x r Y) D →
    ∀ i : S.Node,
      ‖(S.graph r x y0).step u (reference S x r Y) i - reference S x r Y i‖ ≤
        r^2 * S.mesh.location m i * cellBudget S.mesh m D

def UniformResidualStatement : Prop :=
  1 ≤ m → ∀ (r : ℝ), 0 < r → ∀ (u : E → ℝ → E) (x y0 : E)
    (Y : ℝ → E) (D : S.mesh.Cell → ℝ),
    FlowEquation S u x y0 r Y → CellRegularity S.mesh m (meanCurve u x r Y) D →
    Collocation.nodeError ((S.graph r x y0).step u (reference S x r Y))
      (reference S x r Y) ≤ r^2 * samplingEnd S.τ * cellBudget S.mesh m D

def FinalResidualStatement : Prop :=
  1 ≤ m → ∀ (r : ℝ), 0 < r → ∀ (u : E → ℝ → E) (x y0 : E)
    (Y : ℝ → E) (D : S.mesh.Cell → ℝ),
    FlowEquation S u x y0 r Y → CellRegularity S.mesh m (meanCurve u x r Y) D →
    ‖S.output r y0 ((S.graph r x y0).collect u (reference S x r Y)) -
      (samplingEnd S.τ)⁻¹ • Y (samplingEnd S.τ)‖ ≤
        (r / samplingEnd S.τ) * cellBudget S.mesh m D
end Sampling

namespace Mean
variable {m : ℕ} (G : MeanGeometry m)

/-- Unconstrained curve data; analytic equations and regularity are below. -/
structure Curves (E : Type*) where
  position : ℝ → E
  score : ℝ → E
  velocity : ℝ → E
  backward : Fin m → ℝ → E
  conditional : Fin m → (ρ : G.Kernel) → ℝ → E
  forward : Fin m → (ρ : G.Kernel) → ℝ → ℝ → E
  kernel : Fin m → ℝ → E

namespace Curves
variable (C : Curves G E)

def centerMean (u : E → ℝ → E) (x : E) (r a : ℝ) : E :=
  u (x + (r * backwardEnd G.R) • C.position a) (r*G.R)

def backwardMean (u : E → ℝ → E) (x : E) (r : ℝ) (b : Fin m) (a : ℝ) : E :=
  u (x + (r*a) • C.backward b a) (r * Real.sqrt (1-a^2))

def conditionalMean (u : E → ℝ → E) (x : E) (r : ℝ) (b : Fin m)
    (ρ : G.Kernel) (η : ℝ) : E :=
  u (x + (r*G.rho ρ) • C.backward b (G.rho ρ) +
    (r * Real.sqrt (G.variance ρ) * η) • C.conditional b ρ η)
    (r * Real.sqrt (G.variance ρ) * Real.sqrt (1-η^2))

def forwardMean (u : E → ℝ → E) (x : E) (r : ℝ) (b : Fin m)
    (ρ : G.Kernel) (z a : ℝ) : E :=
  u (x + (r*a) • C.forward b ρ z a) (r * Real.sqrt (1-a^2))

def rotation (b : Fin m) (ρ : G.Kernel) (z : ℝ) : E :=
  let B := C.backward b (G.rho ρ)
  let H := G.rho ρ • B + (Real.sqrt (G.variance ρ) / conditionalEnd) •
    C.conditional b ρ conditionalEnd
  let mid := (G.rho ρ / (1+(G.rho ρ)^2)) • (H + G.rho ρ • B)
  mid + Real.cos (z / G.rotationScale ρ) • (B-mid) +
    (G.rotationScale ρ * Real.sin (z / G.rotationScale ρ)) • C.score (centerNode b)

def forwardAction (u : E → ℝ → E) (x : E) (r : ℝ) (b : Fin m)
    (ρ : G.Kernel) (z : ℝ) : E :=
  -r • ∫ a in G.rho ρ..backwardEnd G.R, C.forwardMean G u x r b ρ z a

def reference (x : E) (r : ℝ) : G.MeanNode → E
  | .inl _ => x
  | .inr (.inl b) => x + (r * backwardEnd G.R) • C.position (centerNode b)
  | .inr (.inr (.inl (b,j))) =>
      x + (r * G.backward.location m j) • C.backward b (G.backward.location m j)
  | .inr (.inr (.inr (.inl (b,⟨ρ,j⟩)))) =>
      x + (r*G.rho ρ) • C.backward b (G.rho ρ) +
        (r * Real.sqrt (G.variance ρ) * (G.conditional ρ).location m j) •
          C.conditional b ρ ((G.conditional ρ).location m j)
  | .inr (.inr (.inr (.inr (b,⟨ρ,z,j⟩)))) =>
      x + (r * (G.forward ρ).location m j) •
        C.forward b ρ (G.angleNode z) ((G.forward ρ).location m j)
end Curves

/-- Continuous flow equations and the exact kernel/angle representation.
No quadrature errors, graph residuals, coefficient bounds or contraction are fields. -/
structure Equations (C : Curves G E) (u : E → ℝ → E) (r σ : ℝ)
    (x y0 g0 : E) (ζ : Fin m → G.Kernel → E) : Prop where
  position : ∀ a ∈ Icc (0:ℝ) 1,
    C.position a = y0 + ∫ t in 0..a, C.velocity t
  score : ∀ a ∈ Icc (0:ℝ) 1,
    C.score a = g0 + (σ/2)⁻¹ • ∫ t in 0..a, (C.centerMean G u x r t - u x r)
  backward : ∀ b a, a ∈ Icc (0:ℝ) (backwardEnd G.R) →
    C.backward b a = C.position (centerNode b) -
      r • ∫ t in backwardEnd G.R..a, C.backwardMean G u x r b t
  conditional : ∀ b ρ η, η ∈ Icc (0:ℝ) conditionalEnd →
    C.conditional b ρ η = ζ b ρ - (r * Real.sqrt (G.variance ρ)) •
      ∫ t in 0..η, C.conditionalMean G u x r b ρ t
  forward : ∀ b ρ z a, z ∈ Icc (0:ℝ) G.psi →
    a ∈ Icc (G.rho ρ) (backwardEnd G.R) →
    C.forward b ρ z a = C.rotation G b ρ z -
      r • ∫ t in G.rho ρ..a, C.forwardMean G u x r b ρ z t
  kernel_angle : ∀ b ρ,
    C.kernel b (G.rho ρ) = deriv (C.forwardAction G u x r b ρ) 0
  velocity_kernel : ∀ b,
    C.velocity (centerNode b) = -(r*(σ/2))⁻¹ •
      ∫ t in 0..backwardEnd G.R, t⁻¹ • deriv (C.kernel b) t

structure DerivativeBudget where
  velocity : ℝ
  center : ℝ
  backward : Fin m → G.backward.Cell → ℝ
  conditional : Fin m → (ρ : G.Kernel) → (G.conditional ρ).Cell → ℝ
  forward : Fin m → (ρ : G.Kernel) → Fin m → (G.forward ρ).Cell → ℝ
  angle : Fin m → G.Kernel → ℝ
  kernel : Fin m → ℝ

structure Regularity (C : Curves G E) (u : E → ℝ → E) (x : E) (r l v : ℝ)
    (D : DerivativeBudget G) : Prop where
  velocity_nonneg : 0 ≤ D.velocity
  center_nonneg : 0 ≤ D.center
  velocity_smooth : ∀ t ∈ Icc (0:ℝ) 1, ContDiffAt ℝ m C.velocity t
  velocity_bound : ∀ t ∈ Icc (0:ℝ) 1, ‖iteratedDeriv m C.velocity t‖ ≤ D.velocity
  center_smooth : ∀ t ∈ Icc (0:ℝ) 1, ContDiffAt ℝ m (C.centerMean G u x r) t
  center_bound : ∀ t ∈ Icc (0:ℝ) 1,
    ‖iteratedDeriv m (C.centerMean G u x r) t‖ ≤ D.center
  backward : ∀ b, CellRegularity G.backward m (C.backwardMean G u x r b) (D.backward b)
  conditional : ∀ b ρ,
    CellRegularity (G.conditional ρ) m (C.conditionalMean G u x r b ρ) (D.conditional b ρ)
  forward : ∀ b ρ z, CellRegularity (G.forward ρ) m
    (C.forwardMean G u x r b ρ (G.angleNode z)) (D.forward b ρ z)
  angle_nonneg : ∀ b ρ, 0 ≤ D.angle b ρ
  angle_smooth : ∀ b ρ, ∀ z ∈ Icc (0:ℝ) G.psi,
    ContDiffAt ℝ m (C.forwardAction G u x r b ρ) z
  angle_bound : ∀ b ρ, ∀ z ∈ Icc (0:ℝ) G.psi,
    ‖iteratedDeriv m (C.forwardAction G u x r b ρ) z‖ ≤ D.angle b ρ
  kernel_nonneg : ∀ b, 0 ≤ D.kernel b
  kernel_smooth : ∀ b, ContDiffOn ℝ (m+2) (C.kernel b) (Ioo l v)
  kernel_zero_deriv : ∀ b, deriv (C.kernel b) 0 = 0
  kernel_terminal : ∀ b, C.kernel b (backwardEnd G.R) = 0
  kernel_bound : ∀ b, ∀ t ∈ Icc (0:ℝ) (backwardEnd G.R),
    ‖iteratedDeriv (m+2) (C.kernel b) t‖ ≤ D.kernel b / (1-t^2)^(m+2)

namespace DerivativeBudget
variable (D : DerivativeBudget G)

def velocityError (r σ h₀ : ℝ) (b : Fin m) : ℝ :=
  ((16:ℝ)^m * D.kernel b * h₀^m / (m.factorial:ℝ) +
    ∑ ρ, |G.kernelCoeff ρ| *
      ((m:ℝ)^3 * G.psi^(m-1) * D.angle b ρ / (m.factorial:ℝ))) / (r*(σ/2)) +
  (∑ ρ, |G.kernelCoeff ρ| * ∑ z : Fin m,
    |G.angleDerivative z| * cellBudget (G.forward ρ) m (D.forward b ρ z)) / (σ/2)

def positionError (r σ h₀ a : ℝ) : ℝ :=
  2 * D.velocity / (m.factorial:ℝ) +
    ∑ b : Fin m, |centerRow a b| * D.velocityError G r σ h₀ b

def scoreError (σ : ℝ) : ℝ := 2 * D.center / ((σ/2) * (m.factorial:ℝ))

def backwardError (r σ h₀ : ℝ) (b : Fin m) : ℝ :=
  D.positionError G r σ h₀ (centerNode b) + r * cellBudget G.backward m (D.backward b)

def conditionalError (r : ℝ) (b : Fin m) (ρ : G.Kernel) : ℝ :=
  r * Real.sqrt (G.variance ρ) * cellBudget (G.conditional ρ) m (D.conditional b ρ)

def rotationError (r σ h₀ : ℝ) (b : Fin m) (ρ : G.Kernel) (z : ℝ) : ℝ :=
  |1-(G.rotationScale ρ)^2*(1-Real.cos (z/G.rotationScale ρ))| *
    D.backwardError G r σ h₀ b +
  |G.rho ρ * Real.sqrt (G.variance ρ) / (conditionalEnd*(1+(G.rho ρ)^2)) *
      (1-Real.cos (z/G.rotationScale ρ))| * D.conditionalError G r b ρ +
  |G.rotationScale ρ * Real.sin (z/G.rotationScale ρ)| * D.scoreError G σ

def rowError (r σ h₀ : ℝ) : G.MeanNode → ℝ
  | .inl _ => 0
  | .inr (.inl b) => r * backwardEnd G.R * D.positionError G r σ h₀ (centerNode b)
  | .inr (.inr (.inl (b,j))) =>
      r * G.backward.location m j * D.backwardError G r σ h₀ b
  | .inr (.inr (.inr (.inl (b,⟨ρ,j⟩)))) =>
      r * G.rho ρ * D.backwardError G r σ h₀ b +
        r * Real.sqrt (G.variance ρ) * (G.conditional ρ).location m j *
          D.conditionalError G r b ρ
  | .inr (.inr (.inr (.inr (b,⟨ρ,z,j⟩)))) =>
      r * (G.forward ρ).location m j *
        (D.rotationError G r σ h₀ b ρ (G.angleNode z) +
          r * cellBudget (G.forward ρ) m (D.forward b ρ z))
end DerivativeBudget

def ResidualStatement : Prop :=
  2 ≤ m → ∀ (r σ h₀ l v : ℝ), 0 < r → 0 < σ → 0 ≤ h₀ →
    l < 0 → backwardEnd G.R < v →
    (∀ c, G.backward.length c ≤ 2*h₀*(1-(G.backward.right c)^2)) →
  ∀ (u : E → ℝ → E) (x y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (C : Curves G E) (D : DerivativeBudget G),
    Equations G C u r σ x y0 g0 ζ → Regularity G C u x r l v D →
    ∀ i : G.MeanNode,
      ‖(G.graph r σ x y0 g0 ζ).step u (C.reference G x r) i - C.reference G x r i‖ ≤
        D.rowError G r σ h₀ i

def FinalResidualStatement : Prop :=
  2 ≤ m → ∀ (r σ : ℝ), 0 < r → 0 < σ →
  ∀ (u : E → ℝ → E) (x y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (C : Curves G E) (D : ℝ), 0 ≤ D →
    Equations G C u r σ x y0 g0 ζ →
    (∀ t ∈ Icc (0:ℝ) 1, ContDiffAt ℝ m (C.centerMean G u x r) t) →
    (∀ t ∈ Icc (0:ℝ) 1, ‖iteratedDeriv m (C.centerMean G u x r) t‖ ≤ D) →
    ‖G.meanOutput σ g0 ((G.graph r σ x y0 g0 ζ).collect u (C.reference G x r)) -
      (u x r + (σ/2) • C.score 1)‖ ≤ 2 * D / (m.factorial:ℝ)
end Mean
end AcceleratedLogConcave.Numerics.AffineResidual
end AffineResidualResidualDefs

noncomputable section AffineResidualSampling
open MeasureTheory Set
open scoped BigOperators ContDiff
open AcceleratedLogConcave.Numerics
open AcceleratedLogConcave.Numerics.AffineGraph
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.AffineResidual.Sampling
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {m : ℕ} (S : SamplingGeometry m)

/-- The graph collects the actual mean curve at each physical mesh location,
with exactly the radius stored by the sampling graph. -/
theorem collect_reference (u : E → ℝ → E) (x y0 : E) (r : ℝ) (Y : ℝ → E)
    (i : S.Node) :
    (S.graph r x y0).collect u (reference S x r Y) i =
      meanCurve u x r Y (S.mesh.location m i) := rfl

/-- The normalized sampling state error is precisely the signed integral-row defect. -/
theorem state_sub_flow (u : E → ℝ → E) (x y0 : E) (r : ℝ) (Y : ℝ → E)
    (hflow : FlowEquation S u x y0 r Y) (a : ℝ)
    (ha : a ∈ Icc (0:ℝ) (samplingEnd S.τ)) :
    S.state r y0 ((S.graph r x y0).collect u (reference S x r Y)) a - Y a =
      r • ((∫ t in 0..a, meanCurve u x r Y t) -
        ∑ j : S.Node, S.mesh.row m 0 a j • meanCurve u x r Y (S.mesh.location m j)) := by
  rw [hflow a ha]
  simp only [SamplingGeometry.state, collect_reference, SamplingGeometry.row, smul_sub]
  abel

/-- Multiplication by the physical center scale contributes the second radius factor. -/
theorem step_sub_reference (u : E → ℝ → E) (x y0 : E) (r : ℝ) (Y : ℝ → E)
    (hflow : FlowEquation S u x y0 r Y) (i : S.Node) :
    (S.graph r x y0).step u (reference S x r Y) i - reference S x r Y i =
      (r^2 * S.mesh.location m i) •
        ((∫ t in 0..S.mesh.location m i, meanCurve u x r Y t) -
          ∑ j : S.Node, S.mesh.row m 0 (S.mesh.location m i) j •
            meanCurve u x r Y (S.mesh.location m j)) := by
  have hi := S.mesh.location_mem_interval m i
  change (S.graph r x y0).updateFromReplies
    ((S.graph r x y0).collect u (reference S x r Y)) i - _ = _
  rw [S.graph_update_eq_centers]
  simp only [SamplingGeometry.centers, reference, add_sub_add_left_eq_sub, ← smul_sub]
  rw [state_sub_flow S u x y0 r Y hflow _ ⟨hi.1.le, hi.2.le⟩, smul_smul]
  congr 1
  ring

/-- The terminal normalization is retained exactly, including the physical radius. -/
theorem output_sub_terminal (u : E → ℝ → E) (x y0 : E) (r : ℝ) (Y : ℝ → E)
    (hflow : FlowEquation S u x y0 r Y) :
    S.output r y0 ((S.graph r x y0).collect u (reference S x r Y)) -
      (samplingEnd S.τ)⁻¹ • Y (samplingEnd S.τ) =
      (r / samplingEnd S.τ) •
        ((∫ t in 0..samplingEnd S.τ, meanCurve u x r Y t) -
          ∑ j : S.Node, S.mesh.row m 0 (samplingEnd S.τ) j •
            meanCurve u x r Y (S.mesh.location m j)) := by
  rw [S.output_eq_scaled_terminal, ← smul_sub,
    state_sub_flow S u x y0 r Y hflow _ ⟨S.samplingEnd_pos.le, le_rfl⟩, smul_smul]
  congr 1
  ring

/-- Nonnegativity comes from the cellwise derivative majorants, not from a residual estimate. -/
theorem cellBudget_nonneg (f : ℝ → E) (D : S.mesh.Cell → ℝ)
    (hreg : CellRegularity S.mesh m f D) : 0 ≤ cellBudget S.mesh m D := by
  unfold cellBudget
  apply Finset.sum_nonneg
  intro c _
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (pow_nonneg (S.mesh.length_pos c).le _)) (hreg.1 c))
    (Nat.cast_nonneg _)

variable [CompleteSpace E]

/-- The actual row residual is controlled by the proved quadrature adapter. -/
theorem samplingResidual : ResidualStatement (E := E) S := by
  intro hm r hr u x y0 Y D hflow hreg i
  have hi := S.mesh.location_mem_interval m i
  have hquad := intervalRowDefect (E := E) S.mesh m hm 0 (S.mesh.location m i)
    ⟨le_rfl, S.samplingEnd_pos.le⟩ ⟨hi.1.le, hi.2.le⟩
    (meanCurve u x r Y) D hreg
  rw [step_sub_reference S u x y0 r Y hflow i, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg r) hi.1.le)]
  exact mul_le_mul_of_nonneg_left hquad (mul_nonneg (sq_nonneg r) hi.1.le)

/-- The finite-node maximum is taken after the individual deterministic norm estimates. -/
theorem samplingUniformResidual : UniformResidualStatement (E := E) S := by
  intro hm r hr u x y0 Y D hflow hreg
  have hbudget := cellBudget_nonneg S (meanCurve u x r Y) D hreg
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (mul_nonneg (sq_nonneg r) S.samplingEnd_pos.le) hbudget)).2
  intro i
  change ‖(S.graph r x y0).step u (reference S x r Y) i - reference S x r Y i‖ ≤ _
  exact (samplingResidual S hm r hr u x y0 Y D hflow hreg i).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (S.mesh.location_mem_interval m i).2.le
        (sq_nonneg r)) hbudget)

/-- The final sampling output has the exact terminal normalization required by the source. -/
theorem samplingFinalResidual : FinalResidualStatement (E := E) S := by
  intro hm r hr u x y0 Y D hflow hreg
  have hquad := intervalRowDefect (E := E) S.mesh m hm 0 (samplingEnd S.τ)
    ⟨le_rfl, S.samplingEnd_pos.le⟩ ⟨S.samplingEnd_pos.le, le_rfl⟩
    (meanCurve u x r Y) D hreg
  rw [output_sub_terminal S u x y0 r Y hflow, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr.le S.samplingEnd_pos.le)]
  exact mul_le_mul_of_nonneg_left hquad (div_nonneg hr.le S.samplingEnd_pos.le)

end AcceleratedLogConcave.Numerics.AffineResidual.Sampling
end AffineResidualSampling

noncomputable section AffineResidualMeanVelocity
open MeasureTheory Set
open scoped BigOperators ContDiff
open AcceleratedLogConcave.Numerics
open AcceleratedLogConcave.Numerics.AffineGraph
open AcceleratedLogConcave.Numerics.AffineGraph.MeanGeometry
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.AffineResidual.Mean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {m : ℕ} (G : MeanGeometry m) (C : Curves G E)
variable (u : E → ℝ → E) (r σ : ℝ) (x y0 g0 : E) (ζ : Fin m → G.Kernel → E)

@[simp] theorem collect_reference_base :
    (G.graph r σ x y0 g0 ζ).collect u (C.reference G x r) (.base G) = u x r := rfl

@[simp] theorem collect_reference_center (b : Fin m) :
    (G.graph r σ x y0 g0 ζ).collect u (C.reference G x r) (.center G b) =
      C.centerMean G u x r (centerNode b) := rfl

@[simp] theorem collect_reference_backward (b : Fin m) (j : G.backward.Source m) :
    (G.graph r σ x y0 g0 ζ).collect u (C.reference G x r) (.backward G b j) =
      C.backwardMean G u x r b (G.backward.location m j) := rfl

@[simp] theorem collect_reference_conditional (b : Fin m) (ρ : G.Kernel)
    (j : (G.conditional ρ).Source m) :
    (G.graph r σ x y0 g0 ζ).collect u (C.reference G x r) (.conditional G b ρ j) =
      C.conditionalMean G u x r b ρ ((G.conditional ρ).location m j) := rfl

@[simp] theorem collect_reference_forward (b : Fin m) (ρ : G.Kernel)
    (z : Fin m) (j : (G.forward ρ).Source m) :
    (G.graph r σ x y0 g0 ζ).collect u (C.reference G x r) (.forward G b ρ z j) =
      C.forwardMean G u x r b ρ (G.angleNode z) ((G.forward ρ).location m j) := rfl

theorem norm_weighted_sum_le {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (f : ι → E) (B : ι → ℝ) (h : ∀ i, ‖f i‖ ≤ B i) :
    ‖∑ i, a i • f i‖ ≤ ∑ i, |a i| * B i := by
  calc
    _ ≤ ∑ i, ‖a i • f i‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)

variable [CompleteSpace E]

omit [CompleteSpace E] in
theorem velocity_sub_eq (hr : r ≠ 0) (hσ : σ ≠ 0)
    (eqs : Equations G C u r σ x y0 g0 ζ) (b : Fin m) :
    C.velocity (centerNode b) -
      G.velocity σ ((G.graph r σ x y0 g0 ζ).collect u (C.reference G x r)) b =
    -(r*(σ/2))⁻¹ •
      ((∫ t in 0..backwardEnd G.R, t⁻¹ • deriv (C.kernel b) t) -
        ∑ ρ : G.Kernel, G.kernelCoeff ρ • C.kernel b (G.rho ρ)) +
    -(r*(σ/2))⁻¹ • ∑ ρ : G.Kernel, G.kernelCoeff ρ •
      (deriv (C.forwardAction G u x r b ρ) 0 -
        ∑ z : Fin m, G.angleDerivative z • C.forwardAction G u x r b ρ (G.angleNode z)) +
    (σ/2)⁻¹ • ∑ ρ : G.Kernel, G.kernelCoeff ρ • ∑ z : Fin m,
      G.angleDerivative z •
        ((∫ a in G.rho ρ..backwardEnd G.R,
            C.forwardMean G u x r b ρ (G.angleNode z) a) -
          ∑ j : (G.forward ρ).Source m, G.forwRow ρ (backwardEnd G.R) j •
            C.forwardMean G u x r b ρ (G.angleNode z) ((G.forward ρ).location m j)) := by
  let I : G.Kernel → Fin m → E := fun ρ z =>
    ∫ a in G.rho ρ..backwardEnd G.R, C.forwardMean G u x r b ρ (G.angleNode z) a
  have hA : (∑ ρ : G.Kernel, G.kernelCoeff ρ • ∑ z : Fin m,
      G.angleDerivative z • C.forwardAction G u x r b ρ (G.angleNode z)) =
      -r • ∑ ρ : G.Kernel, G.kernelCoeff ρ • ∑ z : Fin m,
        G.angleDerivative z • I ρ z := by
    simp only [Curves.forwardAction, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro ρ _
    apply Finset.sum_congr rfl
    intro z _
    apply congrArg (fun t : ℝ => t • I ρ z)
    ring
  have hs : -(r*(σ/2))⁻¹ * -r = (σ/2)⁻¹ := by
    field_simp [hr, hσ]
  rw [eqs.velocity_kernel]
  simp only [MeanGeometry.velocity, collect_reference_forward, ← eqs.kernel_angle,
    smul_sub, Finset.sum_sub_distrib]
  rw [hA, smul_smul, hs]
  module


theorem center_defect_sub_const (hm : 1 ≤ m) (a : ℝ) (f : ℝ → E) (c : E)
    (hf : IntervalIntegrable f volume 0 a) :
    (∫ t in 0..a, (f t - c)) - ∑ b : Fin m, centerRow a b • (f (centerNode b) - c) =
      (∫ t in 0..a, f t) - ∑ b : Fin m, centerRow a b • f (centerNode b) := by
  rw [intervalIntegral.integral_sub hf intervalIntegrable_const]
  simp only [intervalIntegral.integral_const, sub_zero, smul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_smul, sum_centerRow m hm]
  abel

theorem score_sub_eq (hm : 1 ≤ m) (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1)
    (eqs : Equations G C u r σ x y0 g0 ζ)
    (hi : IntervalIntegrable (C.centerMean G u x r) volume 0 a) :
    C.score a - G.score σ g0
      ((G.graph r σ x y0 g0 ζ).collect u (C.reference G x r)) a =
      (σ/2)⁻¹ • ((∫ t in 0..a, C.centerMean G u x r t) -
        ∑ b : Fin m, centerRow a b • C.centerMean G u x r (centerNode b)) := by
  rw [eqs.score a ha]
  simp only [MeanGeometry.score, collect_reference_center, collect_reference_base]
  rw [show g0 + (σ/2)⁻¹ • (∫ t in 0..a, (C.centerMean G u x r t - u x r)) -
      (g0 + (σ/2)⁻¹ • ∑ b : Fin m, centerRow a b •
        (C.centerMean G u x r (centerNode b) - u x r)) =
      (σ/2)⁻¹ • ((∫ t in 0..a, (C.centerMean G u x r t - u x r)) -
        ∑ b : Fin m, centerRow a b • (C.centerMean G u x r (centerNode b) - u x r)) by module]
  rw [center_defect_sub_const hm a _ _ hi]

omit [CompleteSpace E] in
theorem position_sub_eq (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1)
    (eqs : Equations G C u r σ x y0 g0 ζ) :
    C.position a - G.position σ y0
      ((G.graph r σ x y0 g0 ζ).collect u (C.reference G x r)) a =
      ((∫ t in 0..a, C.velocity t) -
        ∑ b : Fin m, centerRow a b • C.velocity (centerNode b)) +
      ∑ b : Fin m, centerRow a b • (C.velocity (centerNode b) -
        G.velocity σ ((G.graph r σ x y0 g0 ζ).collect u (C.reference G x r)) b) := by
  rw [eqs.position a ha]
  simp only [MeanGeometry.position, smul_sub, Finset.sum_sub_distrib]
  module


theorem norm_score_sub_le (hm : 1 ≤ m) (hσ : 0 < σ)
    (l v : ℝ) (D : DerivativeBudget G)
    (eqs : Equations G C u r σ x y0 g0 ζ) (reg : Regularity G C u x r l v D)
    (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) :
    ‖C.score a - G.score σ g0
      ((G.graph r σ x y0 g0 ζ).collect u (C.reference G x r)) a‖ ≤
      D.scoreError G σ := by
  have hs : 0 < σ/2 := by positivity
  have hc : ContinuousOn (C.centerMean G u x r) (Icc (0:ℝ) 1) :=
    fun t ht => (reg.center_smooth t ht).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable (C.centerMean G u x r) volume 0 a :=
    ContinuousOn.intervalIntegrable (by
      rw [uIcc_of_le ha.1]
      exact hc.mono (Icc_subset_Icc le_rfl ha.2))
  rw [score_sub_eq G C u r σ x y0 g0 ζ hm a ha eqs hi,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
  calc
    _ ≤ (σ/2)⁻¹ * (2*D.center/(m.factorial:ℝ)) :=
      mul_le_mul_of_nonneg_left
        (norm_centerRow_defect_le m hm a ha _ _ reg.center_nonneg
          reg.center_smooth reg.center_bound) (inv_nonneg.mpr hs.le)
    _ = D.scoreError G σ := by
      simp only [DerivativeBudget.scoreError, div_eq_mul_inv, mul_inv_rev]
      ring

theorem norm_position_sub_le_of_velocity (hm : 1 ≤ m)
    (h₀ l v : ℝ) (D : DerivativeBudget G)
    (eqs : Equations G C u r σ x y0 g0 ζ) (reg : Regularity G C u x r l v D)
    (hV : ∀ b, ‖C.velocity (centerNode b) -
      G.velocity σ ((G.graph r σ x y0 g0 ζ).collect u (C.reference G x r)) b‖ ≤
      D.velocityError G r σ h₀ b)
    (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) :
    ‖C.position a - G.position σ y0
      ((G.graph r σ x y0 g0 ζ).collect u (C.reference G x r)) a‖ ≤
      D.positionError G r σ h₀ a := by
  rw [position_sub_eq G C u r σ x y0 g0 ζ a ha eqs]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_centerRow_defect_le m hm a ha _ _ reg.velocity_nonneg
      reg.velocity_smooth reg.velocity_bound)
    (norm_weighted_sum_le (centerRow a) _ _ hV))


theorem norm_velocity_sub_le (hm : 2 ≤ m)
    (h₀ l v : ℝ) (hr : 0 < r) (hσ : 0 < σ) (hh₀ : 0 ≤ h₀)
    (hl : l < 0) (hv : backwardEnd G.R < v)
    (hgeom : ∀ c, G.backward.length c ≤ 2*h₀*(1-(G.backward.right c)^2))
    (D : DerivativeBudget G)
    (eqs : Equations G C u r σ x y0 g0 ζ) (reg : Regularity G C u x r l v D)
    (b : Fin m) :
    ‖C.velocity (centerNode b) -
      G.velocity σ ((G.graph r σ x y0 g0 ζ).collect u (C.reference G x r)) b‖ ≤
      D.velocityError G r σ h₀ b := by
  let κ : E := (∫ t in 0..backwardEnd G.R, t⁻¹ • deriv (C.kernel b) t) -
    ∑ ρ : G.Kernel, G.kernelCoeff ρ • C.kernel b (G.rho ρ)
  let α : G.Kernel → E := fun ρ => deriv (C.forwardAction G u x r b ρ) 0 -
    ∑ z : Fin m, G.angleDerivative z • C.forwardAction G u x r b ρ (G.angleNode z)
  let ε : G.Kernel → Fin m → E := fun ρ z =>
    (∫ a in G.rho ρ..backwardEnd G.R, C.forwardMean G u x r b ρ (G.angleNode z) a) -
      ∑ j : (G.forward ρ).Source m, G.forwRow ρ (backwardEnd G.R) j •
        C.forwardMean G u x r b ρ (G.angleNode z) ((G.forward ρ).location m j)
  let K : ℝ := (16:ℝ)^m * D.kernel b * h₀^m / (m.factorial:ℝ)
  let A : G.Kernel → ℝ := fun ρ =>
    (m:ℝ)^3 * G.psi^(m-1) * D.angle b ρ / (m.factorial:ℝ)
  let F : G.Kernel → Fin m → ℝ := fun ρ z =>
    cellBudget (G.forward ρ) m (D.forward b ρ z)
  have hs : 0 < σ/2 := by positivity
  have hrs : 0 < r*(σ/2) := mul_pos hr hs
  have hk : ‖κ‖ ≤ K := kernelDefect m G (by omega) l v (D.kernel b) h₀ hl hv
    (reg.kernel_nonneg b) hh₀ hgeom (C.kernel b) (reg.kernel_smooth b)
    (reg.kernel_zero_deriv b) (reg.kernel_terminal b) (reg.kernel_bound b)
  have hα (ρ : G.Kernel) : ‖α ρ‖ ≤ A ρ :=
    angleDerivativeDefect m hm G.psi (D.angle b ρ) G.psi_pos
      (reg.angle_nonneg b ρ) _ (reg.angle_smooth b ρ) (reg.angle_bound b ρ)
  have hε (ρ : G.Kernel) (z : Fin m) : ‖ε ρ z‖ ≤ F ρ z :=
    intervalRowDefect (G.forward ρ) m (by omega) (G.rho ρ) (backwardEnd G.R)
      ⟨le_rfl, (G.rho_mem ρ).2.le⟩ ⟨(G.rho_mem ρ).2.le, le_rfl⟩
      _ _ (reg.forward b ρ z)
  have hks : ‖-(r*(σ/2))⁻¹ • κ‖ ≤ (r*(σ/2))⁻¹ * K := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr hrs)]
    exact mul_le_mul_of_nonneg_left hk (inv_nonneg.mpr hrs.le)
  have has : ‖-(r*(σ/2))⁻¹ • ∑ ρ, G.kernelCoeff ρ • α ρ‖ ≤
      (r*(σ/2))⁻¹ * ∑ ρ, |G.kernelCoeff ρ| * A ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr hrs)]
    exact mul_le_mul_of_nonneg_left (norm_weighted_sum_le _ _ _ hα)
      (inv_nonneg.mpr hrs.le)
  have hfs : ‖(σ/2)⁻¹ • ∑ ρ, G.kernelCoeff ρ • ∑ z, G.angleDerivative z • ε ρ z‖ ≤
      (σ/2)⁻¹ * ∑ ρ, |G.kernelCoeff ρ| * ∑ z, |G.angleDerivative z| * F ρ z := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
    exact mul_le_mul_of_nonneg_left (norm_weighted_sum_le _ _ _
      (fun ρ => norm_weighted_sum_le _ _ _ (hε ρ))) (inv_nonneg.mpr hs.le)
  rw [velocity_sub_eq G C u r σ x y0 g0 ζ hr.ne' hσ.ne' eqs b]
  change ‖-(r*(σ/2))⁻¹ • κ + -(r*(σ/2))⁻¹ • ∑ ρ, G.kernelCoeff ρ • α ρ +
    (σ/2)⁻¹ • ∑ ρ, G.kernelCoeff ρ • ∑ z, G.angleDerivative z • ε ρ z‖ ≤ _
  calc
    _ ≤ (‖-(r*(σ/2))⁻¹ • κ‖ +
        ‖-(r*(σ/2))⁻¹ • ∑ ρ, G.kernelCoeff ρ • α ρ‖) +
        ‖(σ/2)⁻¹ • ∑ ρ, G.kernelCoeff ρ • ∑ z, G.angleDerivative z • ε ρ z‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ((r*(σ/2))⁻¹ * K + (r*(σ/2))⁻¹ * ∑ ρ, |G.kernelCoeff ρ| * A ρ) +
        (σ/2)⁻¹ * ∑ ρ, |G.kernelCoeff ρ| * ∑ z, |G.angleDerivative z| * F ρ z :=
      add_le_add (add_le_add hks has) hfs
    _ = D.velocityError G r σ h₀ b := by
      simp only [DerivativeBudget.velocityError, K, A, F, div_eq_mul_inv]
      ring

theorem norm_position_sub_le (hm : 2 ≤ m)
    (h₀ l v : ℝ) (hr : 0 < r) (hσ : 0 < σ) (hh₀ : 0 ≤ h₀)
    (hl : l < 0) (hv : backwardEnd G.R < v)
    (hgeom : ∀ c, G.backward.length c ≤ 2*h₀*(1-(G.backward.right c)^2))
    (D : DerivativeBudget G)
    (eqs : Equations G C u r σ x y0 g0 ζ) (reg : Regularity G C u x r l v D)
    (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) :
    ‖C.position a - G.position σ y0
      ((G.graph r σ x y0 g0 ζ).collect u (C.reference G x r)) a‖ ≤
      D.positionError G r σ h₀ a :=
  norm_position_sub_le_of_velocity G C u r σ x y0 g0 ζ (by omega) h₀ l v D eqs reg
    (norm_velocity_sub_le G C u r σ x y0 g0 ζ hm h₀ l v hr hσ hh₀ hl hv hgeom D eqs reg)
    a ha

end AcceleratedLogConcave.Numerics.AffineResidual.Mean
end AffineResidualMeanVelocity

noncomputable section AffineResidualMeanGraph
open MeasureTheory Set
open scoped BigOperators ContDiff
open AcceleratedLogConcave.Numerics
open AcceleratedLogConcave.Numerics.AffineGraph
open AcceleratedLogConcave.Numerics.AffineGraph.MeanGeometry
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.AffineResidual.Mean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {m : ℕ} (G : MeanGeometry m)

/- The complete shared rotation is collected before taking absolute values. -/
omit [CompleteSpace E] in
theorem rotation_sub_eq (r σ : ℝ) (y0 g0 : E)
    (ζ : Fin m → G.Kernel → E) (Q : G.MeanNode → E)
    (C : Curves G E) (b : Fin m) (ρ : G.Kernel) (z : ℝ) :
    G.rotation r σ y0 g0 ζ Q b ρ z - C.rotation G b ρ z =
      (1-(G.rotationScale ρ)^2*(1-Real.cos (z/G.rotationScale ρ))) •
        (G.backwardState r σ y0 Q b (G.rho ρ) - C.backward b (G.rho ρ)) +
      (G.rho ρ * Real.sqrt (G.variance ρ) / (conditionalEnd*(1+(G.rho ρ)^2)) *
          (1-Real.cos (z/G.rotationScale ρ))) •
        (G.conditionalState r ζ Q b ρ conditionalEnd - C.conditional b ρ conditionalEnd) +
      (G.rotationScale ρ * Real.sin (z/G.rotationScale ρ)) •
        (G.score σ g0 Q (centerNode b) - C.score (centerNode b)) := by
  simp only [MeanGeometry.rotation, MeanGeometry.midpoint, MeanGeometry.observation,
    Curves.rotation]
  rw [G.rotationScale_sq]
  unfold variance
  match_scalars <;> field_simp <;> ring

omit [CompleteSpace E] in
lemma norm_physical_sub_le (x a b : E) (r A : ℝ) (hr : 0 ≤ r)
    (h : ‖a-b‖ ≤ A) : ‖(x+r • a)-(x+r • b)‖ ≤ r*A := by
  have heq : (x+r • a)-(x+r • b) = r • (a-b) := by module
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
  exact mul_le_mul_of_nonneg_left h hr

/- Algebraic rotation propagation; the three premises are previously derived
free-state bounds, with no hypothesis about the graph residual. -/
omit [CompleteSpace E] in
theorem norm_rotation_sub_le (r σ : ℝ) (y0 g0 : E)
    (ζ : Fin m → G.Kernel → E) (Q : G.MeanNode → E)
    (C : Curves G E) (b : Fin m) (ρ : G.Kernel) (z A B P : ℝ)
    (hB : ‖G.backwardState r σ y0 Q b (G.rho ρ)-C.backward b (G.rho ρ)‖ ≤ A)
    (hZ : ‖G.conditionalState r ζ Q b ρ conditionalEnd-C.conditional b ρ conditionalEnd‖ ≤ B)
    (hP : ‖G.score σ g0 Q (centerNode b)-C.score (centerNode b)‖ ≤ P) :
    ‖G.rotation r σ y0 g0 ζ Q b ρ z-C.rotation G b ρ z‖ ≤
      |1-(G.rotationScale ρ)^2*(1-Real.cos (z/G.rotationScale ρ))| *A +
      |G.rho ρ * Real.sqrt (G.variance ρ)/(conditionalEnd*(1+(G.rho ρ)^2))*
        (1-Real.cos (z/G.rotationScale ρ))| *B +
      |G.rotationScale ρ*Real.sin (z/G.rotationScale ρ)| *P := by
  rw [rotation_sub_eq]
  refine (norm_add_le _ _).trans ?_
  refine add_le_add ((norm_add_le _ _).trans ?_) ?_
  · rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact add_le_add (mul_le_mul_of_nonneg_left hB (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hZ (abs_nonneg _))
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hP (abs_nonneg _)

omit [CompleteSpace E] in
theorem backwardState_sub_eq (r σ : ℝ) (u : E → ℝ → E) (x y0 g0 : E)
    (ζ : Fin m → G.Kernel → E) (C : Curves G E)
    (eq : Equations G C u r σ x y0 g0 ζ) (b : Fin m) (a : ℝ)
    (ha : a ∈ Icc (0:ℝ) (backwardEnd G.R)) :
    G.backwardState r σ y0 ((G.graph r σ x y0 g0 ζ).collect u (C.reference G x r)) b a -
        C.backward b a =
      (G.position σ y0 ((G.graph r σ x y0 g0 ζ).collect u (C.reference G x r))
        (centerNode b) - C.position (centerNode b)) +
      r • ((∫ t in backwardEnd G.R..a, C.backwardMean G u x r b t) -
        ∑ j, G.backRow a j • C.backwardMean G u x r b (G.backward.location m j)) := by
  rw [eq.backward b a ha]
  change (_ - r • ∑ j, G.backRow a j • C.backwardMean G u x r b
      (G.backward.location m j)) - _ = _
  module

omit [CompleteSpace E] in
theorem conditionalState_sub_eq (r σ : ℝ) (u : E → ℝ → E) (x y0 g0 : E)
    (ζ : Fin m → G.Kernel → E) (C : Curves G E)
    (eq : Equations G C u r σ x y0 g0 ζ) (b : Fin m) (ρ : G.Kernel) (η : ℝ)
    (hη : η ∈ Icc (0:ℝ) conditionalEnd) :
    G.conditionalState r ζ ((G.graph r σ x y0 g0 ζ).collect u (C.reference G x r)) b ρ η -
        C.conditional b ρ η =
      (r*Real.sqrt (G.variance ρ)) •
        ((∫ t in 0..η, C.conditionalMean G u x r b ρ t) -
        ∑ j, G.condRow ρ η j •
          C.conditionalMean G u x r b ρ ((G.conditional ρ).location m j)) := by
  rw [eq.conditional b ρ η hη]
  change (ζ b ρ - (r*Real.sqrt (G.variance ρ)) • ∑ j, G.condRow ρ η j •
      C.conditionalMean G u x r b ρ ((G.conditional ρ).location m j)) - _ = _
  module

omit [CompleteSpace E] in
theorem forwardState_sub_eq (r σ : ℝ) (u : E → ℝ → E) (x y0 g0 : E)
    (ζ : Fin m → G.Kernel → E) (C : Curves G E)
    (eq : Equations G C u r σ x y0 g0 ζ) (b : Fin m) (ρ : G.Kernel) (z : Fin m) (a : ℝ)
    (ha : a ∈ Icc (G.rho ρ) (backwardEnd G.R)) :
    G.forwardState r σ y0 g0 ζ
        ((G.graph r σ x y0 g0 ζ).collect u (C.reference G x r)) b ρ z a -
        C.forward b ρ (G.angleNode z) a =
      (G.rotation r σ y0 g0 ζ
        ((G.graph r σ x y0 g0 ζ).collect u (C.reference G x r)) b ρ (G.angleNode z) -
        C.rotation G b ρ (G.angleNode z)) +
      r • ((∫ t in G.rho ρ..a, C.forwardMean G u x r b ρ (G.angleNode z) t) -
        ∑ j, G.forwRow ρ a j •
          C.forwardMean G u x r b ρ (G.angleNode z) ((G.forward ρ).location m j)) := by
  rw [eq.forward b ρ (G.angleNode z) a
    ⟨(G.angleNode_mem z).1.le, (G.angleNode_mem z).2.le⟩ ha]
  change (_ - r • ∑ j, G.forwRow ρ a j •
      C.forwardMean G u x r b ρ (G.angleNode z) ((G.forward ρ).location m j)) - _ = _
  module

theorem norm_backwardState_sub_le (hm : 1 ≤ m) (r σ h₀ l v : ℝ) (hr : 0 ≤ r)
    (u : E → ℝ → E) (x y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (C : Curves G E) (D : DerivativeBudget G)
    (eq : Equations G C u r σ x y0 g0 ζ) (reg : Regularity G C u x r l v D)
    (b : Fin m)
    (hpos : ‖G.position σ y0
      ((G.graph r σ x y0 g0 ζ).collect u (C.reference G x r)) (centerNode b) -
      C.position (centerNode b)‖ ≤ D.positionError G r σ h₀ (centerNode b))
    (a : ℝ) (ha : a ∈ Icc (0:ℝ) (backwardEnd G.R)) :
    ‖G.backwardState r σ y0
      ((G.graph r σ x y0 g0 ζ).collect u (C.reference G x r)) b a - C.backward b a‖ ≤
      D.backwardError G r σ h₀ b := by
  have hquad := intervalRowDefect (E := E) G.backward m hm (backwardEnd G.R) a
    ⟨G.backwardEnd_pos.le, le_rfl⟩ ha (C.backwardMean G u x r b) (D.backward b)
    (reg.backward b)
  rw [backwardState_sub_eq G r σ u x y0 g0 ζ C eq b a ha]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
  exact add_le_add hpos (mul_le_mul_of_nonneg_left hquad hr)

theorem norm_conditionalState_sub_le (hm : 1 ≤ m) (r σ l v : ℝ) (hr : 0 ≤ r)
    (u : E → ℝ → E) (x y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (C : Curves G E) (D : DerivativeBudget G)
    (eq : Equations G C u r σ x y0 g0 ζ) (reg : Regularity G C u x r l v D)
    (b : Fin m) (ρ : G.Kernel) (η : ℝ) (hη : η ∈ Icc (0:ℝ) conditionalEnd) :
    ‖G.conditionalState r ζ ((G.graph r σ x y0 g0 ζ).collect u (C.reference G x r))
      b ρ η - C.conditional b ρ η‖ ≤ D.conditionalError G r b ρ := by
  have hquad := intervalRowDefect (E := E) (G.conditional ρ) m hm 0 η
    ⟨le_rfl, conditionalEnd_pos.le⟩ hη (C.conditionalMean G u x r b ρ)
    (D.conditional b ρ) (reg.conditional b ρ)
  rw [conditionalState_sub_eq G r σ u x y0 g0 ζ C eq b ρ η hη, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr (Real.sqrt_nonneg _))]
  exact mul_le_mul_of_nonneg_left hquad (mul_nonneg hr (Real.sqrt_nonneg _))

theorem norm_forwardState_sub_le (hm : 1 ≤ m) (r σ h₀ l v : ℝ) (hr : 0 ≤ r)
    (u : E → ℝ → E) (x y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (C : Curves G E) (D : DerivativeBudget G)
    (eq : Equations G C u r σ x y0 g0 ζ) (reg : Regularity G C u x r l v D)
    (b : Fin m) (ρ : G.Kernel) (z : Fin m)
    (hrot : ‖G.rotation r σ y0 g0 ζ
      ((G.graph r σ x y0 g0 ζ).collect u (C.reference G x r)) b ρ (G.angleNode z) -
      C.rotation G b ρ (G.angleNode z)‖ ≤ D.rotationError G r σ h₀ b ρ (G.angleNode z))
    (a : ℝ) (ha : a ∈ Icc (G.rho ρ) (backwardEnd G.R)) :
    ‖G.forwardState r σ y0 g0 ζ
      ((G.graph r σ x y0 g0 ζ).collect u (C.reference G x r)) b ρ z a -
      C.forward b ρ (G.angleNode z) a‖ ≤
      D.rotationError G r σ h₀ b ρ (G.angleNode z) +
        r * cellBudget (G.forward ρ) m (D.forward b ρ z) := by
  have hquad := intervalRowDefect (E := E) (G.forward ρ) m hm (G.rho ρ) a
    ⟨le_rfl, (G.rho_mem ρ).2.le⟩ ha (C.forwardMean G u x r b ρ (G.angleNode z))
    (D.forward b ρ z) (reg.forward b ρ z)
  rw [forwardState_sub_eq G r σ u x y0 g0 ζ C eq b ρ z a ha]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
  exact add_le_add hrot (mul_le_mul_of_nonneg_left hquad hr)

/- This algebraic assembly consumes proved free-state estimates; it does not
assume any physical graph-row residual. -/
theorem meanResidual_of_position_score (hm : 1 ≤ m) (r σ h₀ l v : ℝ) (hr : 0 ≤ r)
    (u : E → ℝ → E) (x y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (C : Curves G E) (D : DerivativeBudget G)
    (eq : Equations G C u r σ x y0 g0 ζ) (reg : Regularity G C u x r l v D)
    (hpos : ∀ b : Fin m, ‖G.position σ y0
      ((G.graph r σ x y0 g0 ζ).collect u (C.reference G x r)) (centerNode b) -
      C.position (centerNode b)‖ ≤ D.positionError G r σ h₀ (centerNode b))
    (hscore : ∀ b : Fin m, ‖G.score σ g0
      ((G.graph r σ x y0 g0 ζ).collect u (C.reference G x r)) (centerNode b) -
      C.score (centerNode b)‖ ≤ D.scoreError G σ)
    (i : G.MeanNode) :
    ‖(G.graph r σ x y0 g0 ζ).step u (C.reference G x r) i - C.reference G x r i‖ ≤
      D.rowError G r σ h₀ i := by
  let Q := (G.graph r σ x y0 g0 ζ).collect u (C.reference G x r)
  have hB (b : Fin m) (a : ℝ) (ha : a ∈ Icc (0:ℝ) (backwardEnd G.R)) :
      ‖G.backwardState r σ y0 Q b a-C.backward b a‖ ≤ D.backwardError G r σ h₀ b :=
    norm_backwardState_sub_le G hm r σ h₀ l v hr u x y0 g0 ζ C D eq reg b (hpos b) a ha
  have hZ (b : Fin m) (ρ : G.Kernel) (η : ℝ) (hη : η ∈ Icc (0:ℝ) conditionalEnd) :
      ‖G.conditionalState r ζ Q b ρ η-C.conditional b ρ η‖ ≤ D.conditionalError G r b ρ :=
    norm_conditionalState_sub_le G hm r σ l v hr u x y0 g0 ζ C D eq reg b ρ η hη
  have hW (b : Fin m) (ρ : G.Kernel) (z : ℝ) :
      ‖G.rotation r σ y0 g0 ζ Q b ρ z-C.rotation G b ρ z‖ ≤
        D.rotationError G r σ h₀ b ρ z :=
    norm_rotation_sub_le G r σ y0 g0 ζ Q C b ρ z _ _ _
      (hB b (G.rho ρ) ⟨(G.rho_mem ρ).1, (G.rho_mem ρ).2.le⟩)
      (hZ b ρ conditionalEnd ⟨conditionalEnd_pos.le, le_rfl⟩) (hscore b)
  have hF (b : Fin m) (ρ : G.Kernel) (z : Fin m) (a : ℝ)
      (ha : a ∈ Icc (G.rho ρ) (backwardEnd G.R)) :
      ‖G.forwardState r σ y0 g0 ζ Q b ρ z a-C.forward b ρ (G.angleNode z) a‖ ≤
        D.rotationError G r σ h₀ b ρ (G.angleNode z) +
          r*cellBudget (G.forward ρ) m (D.forward b ρ z) :=
    norm_forwardState_sub_le G hm r σ h₀ l v hr u x y0 g0 ζ C D eq reg b ρ z
      (hW b ρ (G.angleNode z)) a ha
  change ‖(G.graph r σ x y0 g0 ζ).updateFromReplies Q i-C.reference G x r i‖ ≤ _
  rw [G.graph_update_eq_centers]
  rcases i with ⟨⟩ | b | ⟨b,j⟩ | ⟨b,ρ,j⟩ | ⟨b,ρ,z,j⟩
  · simp [MeanGeometry.centers, Curves.reference, DerivativeBudget.rowError]
  · exact norm_physical_sub_le x _ _ _ _ (mul_nonneg hr G.backwardEnd_pos.le) (hpos b)
  · have hj := G.backward.location_mem_interval m j
    exact norm_physical_sub_le x _ _ _ _ (mul_nonneg hr hj.1.le)
      (hB b _ ⟨hj.1.le, hj.2.le⟩)
  · have hj := (G.conditional ρ).location_mem_interval m j
    have hρ : 0 ≤ r*G.rho ρ := mul_nonneg hr (G.rho_mem ρ).1
    have hη : 0 ≤ r*Real.sqrt (G.variance ρ)*(G.conditional ρ).location m j :=
      mul_nonneg (mul_nonneg hr (Real.sqrt_nonneg _)) hj.1.le
    change ‖(x+(r*G.rho ρ) • G.backwardState r σ y0 Q b (G.rho ρ) +
        (r*Real.sqrt (G.variance ρ)*(G.conditional ρ).location m j) •
          G.conditionalState r ζ Q b ρ ((G.conditional ρ).location m j)) -
      (x+(r*G.rho ρ) • C.backward b (G.rho ρ) +
        (r*Real.sqrt (G.variance ρ)*(G.conditional ρ).location m j) •
          C.conditional b ρ ((G.conditional ρ).location m j))‖ ≤ _
    have he : (x+(r*G.rho ρ) • G.backwardState r σ y0 Q b (G.rho ρ) +
        (r*Real.sqrt (G.variance ρ)*(G.conditional ρ).location m j) •
          G.conditionalState r ζ Q b ρ ((G.conditional ρ).location m j)) -
      (x+(r*G.rho ρ) • C.backward b (G.rho ρ) +
        (r*Real.sqrt (G.variance ρ)*(G.conditional ρ).location m j) •
          C.conditional b ρ ((G.conditional ρ).location m j)) =
      (r*G.rho ρ) • (G.backwardState r σ y0 Q b (G.rho ρ)-C.backward b (G.rho ρ)) +
      (r*Real.sqrt (G.variance ρ)*(G.conditional ρ).location m j) •
        (G.conditionalState r ζ Q b ρ ((G.conditional ρ).location m j)-
          C.conditional b ρ ((G.conditional ρ).location m j)) := by module
    rw [he]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hρ, abs_of_nonneg hη]
    exact add_le_add (mul_le_mul_of_nonneg_left
      (hB b _ ⟨(G.rho_mem ρ).1, (G.rho_mem ρ).2.le⟩) hρ)
      (mul_le_mul_of_nonneg_left (hZ b ρ _ ⟨hj.1.le, hj.2.le⟩) hη)
  · have hj := (G.forward ρ).location_mem_interval m j
    exact norm_physical_sub_le x _ _ _ _
      (mul_nonneg hr ((G.rho_mem ρ).1.trans hj.1.le))
      (hF b ρ z _ ⟨hj.1.le, hj.2.le⟩)

/-- Residual bound for every row of the actual mean affine graph. All local
quadrature defects are proved from the regularity fields, then propagated through
the literal free states and their physical center scales. -/
theorem meanResidual : ResidualStatement (E := E) G := by
  intro hm r σ h₀ l v hr hσ hh₀ hl hv hgeom u x y0 g0 ζ C D eq reg i
  apply meanResidual_of_position_score G (by omega) r σ h₀ l v hr.le
    u x y0 g0 ζ C D eq reg _ _ i
  · intro b
    rw [norm_sub_rev]
    exact norm_position_sub_le G C u r σ x y0 g0 ζ hm h₀ l v hr hσ hh₀ hl hv hgeom
      D eq reg (centerNode b) ⟨(centerNode_mem b).1.le, (centerNode_mem b).2.le⟩
  · intro b
    rw [norm_sub_rev]
    exact norm_score_sub_le G C u r σ x y0 g0 ζ (by omega) hσ l v D eq reg
      (centerNode b) ⟨(centerNode_mem b).1.le, (centerNode_mem b).2.le⟩

/- The final output has the full unit-interval Gaussian quadrature defect.
The base reply cancels against the exact score's constant integrand. -/
theorem meanFinalResidual : FinalResidualStatement (E := E) G := by
  intro hm r σ hr hσ u x y0 g0 ζ C D hD eq hs hb
  have hσ0 : σ/2 ≠ 0 := ne_of_gt (by linarith)
  have hc : IntervalIntegrable (C.centerMean G u x r) volume (0:ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    exact (hs t (by simpa using ht)).continuousAt.continuousWithinAt
  have he := eq.score 1 (by norm_num)
  rw [intervalIntegral.integral_sub hc intervalIntegrable_const] at he
  simp only [intervalIntegral.integral_const, sub_zero, one_smul] at he
  have hnorm := norm_centerRow_defect_le m (by omega) 1 (by norm_num)
    (C.centerMean G u x r) D hD hs hb
  have hrow (b : Fin m) : centerRow 1 b = GaussLegendre.weight m b := by
    simpa [centerRow, GaussLegendre.cellWeight] using
      GaussLegendre.partialRow_full_one m 0 1 (by norm_num) b
  have hcollect (b : Fin m) :
      (G.graph r σ x y0 g0 ζ).collect u (C.reference G x r) (.center G b) =
        C.centerMean G u x r (centerNode b) := rfl
  simp only [hrow] at hnorm
  have hout : G.meanOutput σ g0
      ((G.graph r σ x y0 g0 ζ).collect u (C.reference G x r)) -
      (u x r + (σ/2) • C.score 1) =
      (∑ b : Fin m, GaussLegendre.weight m b • C.centerMean G u x r (centerNode b)) -
      ∫ t in (0:ℝ)..1, C.centerMean G u x r t := by
    simp only [meanOutput, hcollect, he, smul_add, smul_smul, mul_inv_cancel₀ hσ0,
      one_smul]
    module
  rw [hout, norm_sub_rev]
  exact hnorm

end AcceleratedLogConcave.Numerics.AffineResidual.Mean
end AffineResidualMeanGraph
