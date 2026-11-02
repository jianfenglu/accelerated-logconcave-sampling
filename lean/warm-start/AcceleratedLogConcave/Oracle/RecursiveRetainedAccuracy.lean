import AcceleratedLogConcave.Oracle.PrescribedRetainedCoupling
import AcceleratedLogConcave.Oracle.PrescribedTerminalAccuracy

/-! Accuracy of the already constructed retained kernels. The error target
is physical: primitiveMean plus the actual width times the normalized
reference. Equality transport preserves the entire source tape. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.RecursiveRetainedAccuracy
open Numerics Numerics.AffineGraph TapeLowering CanonicalTapeMeasurability
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable {d m : ℕ} (M : MeanGeometry m) (hm : 0<m)
  {F : Point d → ℝ} {ell : ℝ} (hF : ContDiff ℝ 2 F) (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (t : ℝ) (ht : 0<t)

/-- Literal execution error on the full original seed and the retained
normalized reference coordinate. -/
def error (E : ExecutableData) (G : Point d → Point d) (base : Point d) (r σ : ℝ) :=
  FreshChildRunShift.lowerError E.program G E.coefficient base
    (Gibbs.primitiveMean F base r) σ

/-- Quantitative accuracy is a property of a specific already selected joint,
not a new existential coupling. -/
def Accurate {r σ q : ℝ} {hr : 0<r} {hσ : 0<σ} {hsmall : r^2*ell≤1/2}
    {E : ExecutableData}
    (J : RecursiveRetainedCoupling.Law M hm hF hell hlo hup t ht r σ q hr hσ hsmall E)
    (G : Point d → Point d) (δ : ℝ) : Prop :=
  ∀ base : Point d,
    MemLp (error (F := F) E G base r σ) 2 (J.joint base) ∧
      (∫ z,‖error (F := F) E G base r σ z‖^2 ∂J.joint base) ≤
        (σ*δ^q*Gibbs.primitiveScale F base)^2

/-- A change of dependent executable presentation changes no quantitative
statement about its actual interpreted error. -/
theorem accurate_castLaw {r σ q : ℝ} {hr : 0<r} {hσ : 0<σ} {hsmall : r^2*ell≤1/2}
    {E E' : ExecutableData} (he : E=E')
    (J : RecursiveRetainedCoupling.Law M hm hF hell hlo hup t ht r σ q hr hσ hsmall E)
    (G : Point d → Point d) (δ : ℝ) :
    Accurate M hm hF hell hlo hup t ht (RecursiveRetainedCoupling.castLaw M hm hF hell hlo hup t ht he J) G δ ↔
      Accurate M hm hF hell hlo hup t ht J G δ := by
  cases he
  rfl

/-- The terminal package uses precisely the existing literal terminal error
and canonical full-seed joint. This theorem supplies no numerical guard. -/
theorem terminal_accurate (scale r σ q δ : ℝ) (hr : 0<r) (hσ : 0<σ)
    (hsmall : r^2*ell≤1/2) (hq : q≤1/2) (G : Point d → Point d)
    (hmem : ∀ base : Point d,
      MemLp (TerminalSourceRetainedCoupling.error RecursiveRetainedCoupling.terminalOrigin
        G scale r σ base (Gibbs.primitiveMean F base r)) 2
        (TerminalSourceRetainedCoupling.joint RecursiveRetainedCoupling.terminalOrigin base))
    (hbound : ∀ base : Point d,
      (∫ z,‖TerminalSourceRetainedCoupling.error RecursiveRetainedCoupling.terminalOrigin
        G scale r σ base (Gibbs.primitiveMean F base r) z‖^2
        ∂TerminalSourceRetainedCoupling.joint RecursiveRetainedCoupling.terminalOrigin base) ≤
          (σ*δ^q*Gibbs.primitiveScale F base)^2) :
    Accurate M hm hF hell hlo hup t ht
      (RecursiveRetainedCoupling.terminalLaw M hm hF hell hlo hup t ht scale r σ q hr hσ hsmall hq) G δ := by
  intro base
  exact ⟨hmem base,hbound base⟩

end AcceleratedLogConcave.Oracle.RecursiveRetainedAccuracy
