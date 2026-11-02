import AcceleratedLogConcave.Tensor.PhaseVectorSource

/-! Joint smoothness in a passive parameter and the active phase coordinates.
No integration or moments are required of the passive parameter. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Tensor.PhaseParametricSmoothness
open AdjointReduction CoordinateReduction PhaseSourceJetInduction
variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem contDiff_parameter_dir {f : P → V → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) (v : V) :
    ContDiff ℝ ∞ (fun p : P × V => dir v (f p.1) p.2) := by
  have h : ContDiff ℝ ∞ (fun p : (P × V) × V => f p.1.1 p.2) :=
    hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact h.fderiv_apply contDiff_snd contDiff_const (by simp)

theorem contDiff_parameter_partialAlong {I : Type*} (d : I → V) (J : List I)
    {f : P → V → ℝ} (hf : ContDiff ℝ ∞ (Function.uncurry f)) :
    ContDiff ℝ ∞ (fun p : P × V => partialAlong d J (f p.1) p.2) := by
  induction J with
  | nil => exact hf
  | cons i J ih => exact contDiff_parameter_dir (f := fun p => partialAlong d J (f p)) ih (d i)

variable {Name : Type*} {σ : CoefficientSignature Name} {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

theorem contDiff_parameter_section (ρ : P → CoefficientEnvironment σ D)
    (H : P → E → ℝ)
    (hρ : ∀ c a, ContDiff ℝ ∞ (fun p : P × E => ρ p.1 c p.2 a))
    (hH : ContDiff ℝ ∞ (Function.uncurry H))
    {r : ℕ} (e : Expr σ r) : ∀ a : Fin r → Fin D,
    ContDiff ℝ ∞ (fun p : P × E => sectionValue (ρ p.1) (H p.1) e a p.2) := by
  induction e with
  | coefficient c => intro a; exact hρ c a
  | permute p e ih => intro a; exact ih _
  | contract e f i j ihe ihf =>
    intro a
    simp_rw [section_contract]
    exact ContDiff.sum (fun k _ => (ihe _).mul (ihf _))
  | derivative e ih =>
    intro a
    simp_rw [section_derivative]
    exact contDiff_parameter_dir
      (f := fun p => sectionValue (ρ p) (H p) e (a ∘ Fin.castSucc)) (ih _) _
  | adjoint i e ih =>
    intro a
    simp_rw [section_adjoint,adjointField]
    apply ContDiff.sum
    intro k _
    exact (contDiff_parameter_dir
      (f := fun p => sectionValue (ρ p) (H p) e (Fin.insertNth i k a)) (ih _) _).neg.add
      ((contDiff_parameter_dir hH _).mul (ih _))

theorem contDiff_parameter_vectorSection
    (ρ : P → CoefficientEnvironment PhaseExpression.signature D)
    (H : P → E → ℝ)
    (hρ : ∀ c a, ContDiff ℝ ∞ (fun p : P × E => ρ p.1 c p.2 a))
    (hH : ContDiff ℝ ∞ (Function.uncurry H)) (e : Expr PhaseExpression.signature 1) :
    ContDiff ℝ ∞ (fun p : P × E => vectorSection (ρ p.1) (H p.1) e p.2) := by
  have hp : ContDiff ℝ ∞ (fun p : P × E => fun i =>
      sectionValue (ρ p.1) (H p.1) e ![i] p.2) :=
    contDiff_pi.mpr (fun i => contDiff_parameter_section ρ H hρ hH e ![i])
  have h := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin D => ℝ)).symm.contDiff.comp hp
  convert h using 1
  funext p
  ext i
  rfl
end AcceleratedLogConcave.Tensor.PhaseParametricSmoothness
