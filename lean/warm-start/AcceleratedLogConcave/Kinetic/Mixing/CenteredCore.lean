import AcceleratedLogConcave.Kinetic.Reheating.DenseExtension
import AcceleratedLogConcave.Analysis.Poisson.Centered

/-! Compact smooth centered tests are dense in the actual mean-zero L2 space.
Centering uses a compact smooth unit-mass test, preserving compact support. -/
noncomputable section
open Set MeasureTheory
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson

 theorem dense_kernel_core {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (m : H →L[ℝ] ℝ) (S : Submodule ℝ H) (hS : Dense (S : Set H))
    (ρ : H) (hρ : ρ ∈ S) (hmρ : m ρ = 1) :
    Dense {x : m.ker | (x : H) ∈ S} := by
  let P : H → m.ker := fun x => ⟨x-m x • ρ, by simp [map_sub,map_smul,hmρ]⟩
  have hP : Continuous P :=
    (continuous_id.sub (m.continuous.smul continuous_const)).subtype_mk _
  have hsurj : Function.Surjective P := by
    intro x
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change (x : H)-m x • ρ = x
    rw [show m x = 0 from x.property,zero_smul,sub_zero]
  apply (hsurj.denseRange.dense_image hP hS).mono
  rintro x ⟨y,hy,rfl⟩
  exact S.sub_mem hy (S.smul_mem _ hρ)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

def compactSmoothSubmodule : Submodule ℝ (Lp ℝ 2 μ) where
  carrier := {f | ∃ φ : X → ℝ, f =ᵐ[μ] φ ∧ HasCompactSupport φ ∧ ContDiff ℝ 2 φ}
  zero_mem' := ⟨0, Lp.coeFn_zero ℝ 2 μ, HasCompactSupport.zero, contDiff_const⟩
  add_mem' := by
    rintro f g ⟨φ,hf,hc,hφ⟩ ⟨ψ,hg,hd,hψ⟩
    refine ⟨φ+ψ, ?_, hc.add hd,hφ.add hψ⟩
    filter_upwards [Lp.coeFn_add f g,hf,hg] with x hx hfx hgx
    simp only [hx,Pi.add_apply,hfx,hgx]
  smul_mem' := by
    rintro c f ⟨φ,hf,hc,hφ⟩
    refine ⟨c • φ, ?_, hc.smul_left,hφ.const_smul c⟩
    filter_upwards [Lp.coeFn_smul c f,hf] with x hx hfx
    simp only [hx,Pi.smul_apply,hfx]

 theorem centered_compactC2_dense :
    Dense {f : centered μ | ∃ φ : X → ℝ,
      (f : Lp ℝ 2 μ) =ᵐ[μ] φ ∧ HasCompactSupport φ ∧ ContDiff ℝ 2 φ} := by
  let S := compactSmoothSubmodule μ
  have hS : Dense (S : Set (Lp ℝ 2 μ)) := Reheating.compactC2_dense μ
  obtain ⟨g,hg,hmg⟩ := hS.exists_mem_open
    (isOpen_ne_fun (mean μ).continuous (continuous_const (y := (0:ℝ))))
    ⟨oneL2 μ, by change mean μ (oneL2 μ) ≠ 0; rw [mean_oneL2]; norm_num⟩
  change mean μ g ≠ 0 at hmg
  let ρ := (mean μ g)⁻¹ • g
  have hρ : ρ ∈ S := S.smul_mem _ hg
  have hmρ : mean μ ρ = 1 := by simp only [ρ,map_smul,smul_eq_mul,inv_mul_cancel₀ hmg]
  exact dense_kernel_core (mean μ) S hS ρ hρ hmρ

end AcceleratedLogConcave.Kinetic
