import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.ClockHeatFamily
import AcceleratedLogConcave.Kinetic.ReferenceFlow.Divergence

/-! The same variance-indexed heat family constructs the actual reverse-clock
transport family. The drift scale A*rho follows from the chain rule and the
classical continuity equation, not a transported-law assumption. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set InnerProductSpace Function
open scoped Topology
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

private theorem clockVariance_mem {A R ρ : ℝ} (hA : 0 < A) (hR : A < R)
    (hρ : ρ ∈ Icc (0:ℝ) (1/2)) : A*(1-ρ^2) ∈ Icc (3*A/4) R :=
  (VarianceHeatFamily.clock_segment hA hR hρ).1

private theorem clockVariance_mem_interior {A R ρ : ℝ} (hA : 0 < A) (hR : A < R)
    (hρ : ρ ∈ Ioo (0:ℝ) (1/2)) : A*(1-ρ^2) ∈ Ioo (3*A/4) R := by
  have hs : ρ^2 < 1/4 := by nlinarith [hρ.1,hρ.2]
  have hp := mul_lt_mul_of_pos_left hs hA
  have hz := mul_nonneg hA.le (sq_nonneg ρ)
  constructor <;> nlinarith

private theorem clockVariance_hasDerivAt (A ρ : ℝ) :
    HasDerivAt (fun s : ℝ => A*(1-s^2)) (-2*A*ρ) ρ := by
  convert ((hasDerivAt_const ρ (1:ℝ)).sub ((hasDerivAt_id ρ).pow 2)).const_mul A using 1
  · funext s
    simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
  · simp only [id_eq]
    ring

private theorem clock_density_continuity {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ρ : ℝ) (hρ : ρ ∈ Ioo (0:ℝ) (1/2)) (x : E) :
    (-2*A*ρ)*H.source.densityVelocity (A*(1-ρ^2)) x +
      fluxDivergence (fun y => H.source.density (A*(1-ρ^2)) y •
        referenceDrift (fun s => H.source.potential (A*(1-s^2))) (fun s => A*s) ρ y) x = 0 := by
  let v := A*(1-ρ^2)
  let k := -2*A*ρ
  have hv := clockVariance_mem_interior hA hR hρ
  have hJ : DifferentiableAt ℝ (fun y => H.source.density v y •
      referenceDrift H.source.potential H.source.scale v y) x :=
    ((H.source.density_C1 v hv).differentiable (by norm_num) x).smul
      (referenceDrift_hasFDerivAt H.source.potential H.source.scale v x
        (H.source.potential_C2 v (Ioo_subset_Icc_self hv))).differentiableAt
  have hdiv := Kinetic.fluxDivergence_smul (r := fun _ : E => k) (differentiableAt_const k) hJ
  have heq : (fun y => H.source.density v y •
      referenceDrift (fun s => H.source.potential (A*(1-s^2))) (fun s => A*s) ρ y) =
      fun y => k • (H.source.density v y • referenceDrift H.source.potential H.source.scale v y) := by
    funext y
    simp only [referenceDrift, H.scale_eq v (Ioo_subset_Icc_self hv), neg_neg, smul_smul]
    congr 1
    dsimp only [k]
    ring
  change k*H.source.densityVelocity v x + _ = 0
  rw [heq,hdiv,fderiv_const_apply,zero_apply,zero_add,← mul_add,
    H.source.continuity_equation v hv x,mul_zero]

/-- Classical reverse-clock data obtained from the same actual heat family. -/
def clockTransportLocal {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R) :
    LocalReferencePoissonFamily E 0 (1/2) where
  ordered := by norm_num
  potential := fun ρ => H.source.potential (A*(1-ρ^2))
  scale := fun ρ => A*ρ
  potential_C2 := fun ρ hρ => H.source.potential_C2 _ (clockVariance_mem hA hR hρ)
  gradient_continuous := H.source.gradient_continuous.comp
    (show Continuous (fun z : ℝ×E => (A*(1-z.1^2),z.2)) by fun_prop).continuousOn
    (fun z hz => ⟨clockVariance_mem hA hR hz.1,mem_univ _⟩)
  hessian_continuous := H.source.hessian_continuous.comp
    (show Continuous (fun z : ℝ×E => (A*(1-z.1^2),z.2)) by fun_prop).continuousOn
    (fun z hz => ⟨clockVariance_mem hA hR hz.1,mem_univ _⟩)
  scale_continuous := (continuous_const.mul continuous_id).continuousOn
  lower := fun ρ => H.source.lower (A*(1-ρ^2))
  lower_pos := fun ρ hρ => H.source.lower_pos _ (clockVariance_mem hA hR hρ)
  hessian_lower := fun ρ hρ => H.source.hessian_lower _ (clockVariance_mem hA hR hρ)
  hessian_upper := fun ρ hρ => H.source.hessian_upper _ (clockVariance_mem hA hR hρ)
  law := fun ρ => H.source.law (A*(1-ρ^2))
  probability := fun ρ hρ => H.source.probability _ (clockVariance_mem hA hR hρ)
  integrable := fun ρ hρ => H.source.integrable _ (clockVariance_mem hA hR hρ)
  gibbs_law := fun ρ hρ => H.source.gibbs_law _ (clockVariance_mem hA hR hρ)
  density := fun ρ => H.source.density (A*(1-ρ^2))
  densityVelocity := fun ρ x => (-2*A*ρ)*H.source.densityVelocity (A*(1-ρ^2)) x
  density_continuous := H.source.density_continuous.comp
    (show Continuous (fun z : ℝ×E => (A*(1-z.1^2),z.2)) by fun_prop).continuousOn
    (fun z hz => ⟨clockVariance_mem hA hR hz.1,mem_univ _⟩)
  densityVelocity_continuous :=
    (show Continuous (fun z : ℝ×E => -2*A*z.1) by fun_prop).continuousOn.mul
      (H.source.densityVelocity_continuous.comp
        (show Continuous (fun z : ℝ×E => (A*(1-z.1^2),z.2)) by fun_prop).continuousOn
        (fun z hz => ⟨clockVariance_mem_interior hA hR hz.1,mem_univ _⟩))
  density_hasDerivAt := fun ρ hρ x => by
    have hd := (H.source.density_hasDerivAt _ (clockVariance_mem_interior hA hR hρ) x).comp ρ
      (clockVariance_hasDerivAt A ρ)
    simpa only [Function.comp_def,mul_comm] using hd
  density_C1 := fun ρ hρ => H.source.density_C1 _ (clockVariance_mem_interior hA hR hρ)
  continuity_equation := clock_density_continuity H hA hR
  density_law := fun ρ hρ => H.source.density_law _ (clockVariance_mem hA hR hρ)
  density_nonneg := fun ρ hρ => H.source.density_nonneg _ (clockVariance_mem hA hR hρ)

/-- The actual complete transport and Poisson machinery now applies to this
reverse-clock family by the already proved W04 constructor. -/
def clockTransportFamily {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R) :
    ReferencePoissonFamily E 0 (1/2) := (clockTransportLocal H hA hR).toFamily

theorem clockTransportFamily_law {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0:ℝ) (1/2)) :
    (clockTransportFamily H hA hR).law ρ = H.source.law (A*(1-ρ^2)) :=
  (clockTransportLocal H hA hR).toFamily_law ρ hρ

theorem clockTransportFamily_potential {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0:ℝ) (1/2)) :
    (clockTransportFamily H hA hR).potential ρ = H.source.potential (A*(1-ρ^2)) :=
  (clockTransportLocal H hA hR).toFamily_potential ρ hρ

theorem clockTransportFamily_scale {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0:ℝ) (1/2)) :
    (clockTransportFamily H hA hR).scale ρ = A*ρ :=
  (clockTransportLocal H hA hR).toFamily_scale ρ hρ

/-- The reheat input law is exactly the law reached by the reverse-clock flow. -/
theorem clockReheatFamily_initial_eq_transport_law {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0:ℝ) (1/2)) :
    (clockReheatFamily H hA hR ρ hρ).law 0 = (clockTransportFamily H hA hR).law ρ := by
  rw [clockReheatFamily_initial_law,clockTransportFamily_law H hA hR ρ hρ]

theorem clockReheatFamily_final_eq_transport_law {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0:ℝ) (1/2)) :
    (clockReheatFamily H hA hR ρ hρ).law (A*ρ^2) = (clockTransportFamily H hA hR).law 0 := by
  rw [clockReheatFamily_final_law,clockTransportFamily_law H hA hR 0 (by constructor <;> norm_num)]
  simp

theorem clockReheatFamily_initial_eq_transport_potential {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0:ℝ) (1/2)) :
    (clockReheatFamily H hA hR ρ hρ).potential 0 = (clockTransportFamily H hA hR).potential ρ := by
  rw [clockReheatFamily_initial_potential,clockTransportFamily_potential H hA hR ρ hρ]

theorem clockReheatFamily_final_eq_transport_potential {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0:ℝ) (1/2)) :
    (clockReheatFamily H hA hR ρ hρ).potential (A*ρ^2) = (clockTransportFamily H hA hR).potential 0 := by
  rw [clockReheatFamily_final_potential,clockTransportFamily_potential H hA hR 0 (by constructor <;> norm_num)]
  simp

/-- The true heat semigroup returns the reverse-clock marginal to its original law. -/
theorem clockTransportFamily_heat_return {μ : Measure E} [IsProbabilityMeasure μ] {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0:ℝ) (1/2)) :
    heatedLaw ((clockTransportFamily H hA hR).law ρ) (A*ρ^2) =
      (clockTransportFamily H hA hR).law 0 := by
  have he := clockReheatFamily_endpoint hA hR hρ
  have hh := clockReheatFamily_heat H hA hR ρ hρ (A*ρ^2) ⟨he.1,he.2.le⟩
  rw [clockReheatFamily_initial_eq_transport_law,clockReheatFamily_final_eq_transport_law,sub_zero] at hh
  exact hh.symm

/-- The reverse-clock marginal is the prescribed Gaussian smoothing of the base law. -/
theorem clockTransportFamily_heated_law {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0:ℝ) (1/2)) :
    (clockTransportFamily H hA hR).law ρ = heatedLaw μ (A*(1-ρ^2)) := by
  rw [clockTransportFamily_law H hA hR ρ hρ]
  exact H.heat_law _ (clockVariance_mem hA hR hρ)

/-- Both constructions use the same curvature witness at the collision input. -/
theorem clockReheatFamily_initial_eq_transport_lower {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0:ℝ) (1/2)) :
    (clockReheatFamily H hA hR ρ hρ).lower 0 = (clockTransportFamily H hA hR).lower ρ := by
  change H.source.lower (A*(1-ρ^2)+0) = H.source.lower (A*(1-ρ^2))
  rw [add_zero]

theorem clockReheatFamily_final_eq_transport_lower {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0:ℝ) (1/2)) :
    (clockReheatFamily H hA hR ρ hρ).lower (A*ρ^2) = (clockTransportFamily H hA hR).lower 0 := by
  change H.source.lower (A*(1-ρ^2)+A*ρ^2) = H.source.lower (A*(1-(0:ℝ)^2))
  congr 1
  ring

end AcceleratedLogConcave.Kinetic.Reheating
