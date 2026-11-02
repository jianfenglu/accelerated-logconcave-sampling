import AcceleratedLogConcave.Oracle.RecursiveRetainedAccuracy

/-! The source accuracy constant is explicit and belongs to a property of the
same recursively constructed joint, not to the construction of another joint. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.RecursiveRetainedAccuracy
open Numerics Numerics.AffineGraph TapeLowering CanonicalTapeMeasurability
local instance factorCanonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable {d m : ℕ} (M : MeanGeometry m) (hm : 0<m)
  {F : Point d → ℝ} {ell : ℝ} (hF : ContDiff ℝ 2 F) (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (t : ℝ) (ht : 0<t)

/-- Physical RMS accuracy with an explicit universal constant. The actual
recursive induction uses amplitude four; the terminal base satisfies one. -/
def AccurateWith (amplitude : ℝ) {r σ q : ℝ} {hr : 0<r} {hσ : 0<σ} {hsmall : r^2*ell≤1/2}
    {E : ExecutableData}
    (J : RecursiveRetainedCoupling.Law M hm hF hell hlo hup t ht r σ q hr hσ hsmall E)
    (G : Point d → Point d) (δ : ℝ) : Prop :=
  ∀ base : Point d,
    MemLp (error (F := F) E G base r σ) 2 (J.joint base) ∧
      (∫ z,‖error (F := F) E G base r σ z‖^2 ∂J.joint base) ≤
        (amplitude*(σ*δ^q*Gibbs.primitiveScale F base))^2

/-- A proved unit bound gives any larger nonnegative constant on the same
joint and the same literal full-source error. -/
theorem accurateWith_of_accurate {r σ q : ℝ} {hr : 0<r} {hσ : 0<σ} {hsmall : r^2*ell≤1/2}
    {E : ExecutableData}
    (J : RecursiveRetainedCoupling.Law M hm hF hell hlo hup t ht r σ q hr hσ hsmall E)
    (G : Point d → Point d) (δ amplitude : ℝ) (ha : 1≤amplitude)
    (hJ : Accurate M hm hF hell hlo hup t ht J G δ) :
    AccurateWith M hm hF hell hlo hup t ht amplitude J G δ := by
  intro base
  obtain ⟨hmem,hbound⟩ := hJ base
  refine ⟨hmem,hbound.trans ?_⟩
  have ha2 : 1≤amplitude^2 := by nlinarith
  calc
    (σ*δ^q*Gibbs.primitiveScale F base)^2 ≤ amplitude^2*(σ*δ^q*Gibbs.primitiveScale F base)^2 :=
      le_mul_of_one_le_left (sq_nonneg _) ha2
    _ = (amplitude*(σ*δ^q*Gibbs.primitiveScale F base))^2 := (mul_pow _ _ 2).symm

/-- Full dependent executable casts do not alter accuracy at any constant. -/
theorem accurateWith_castLaw (amplitude : ℝ) {r σ q : ℝ} {hr : 0<r} {hσ : 0<σ}
    {hsmall : r^2*ell≤1/2} {E E' : ExecutableData} (he : E=E')
    (J : RecursiveRetainedCoupling.Law M hm hF hell hlo hup t ht r σ q hr hσ hsmall E)
    (G : Point d → Point d) (δ : ℝ) :
    AccurateWith M hm hF hell hlo hup t ht amplitude
      (RecursiveRetainedCoupling.castLaw M hm hF hell hlo hup t ht he J) G δ ↔
      AccurateWith M hm hF hell hlo hup t ht amplitude J G δ := by
  cases he
  rfl

end AcceleratedLogConcave.Oracle.RecursiveRetainedAccuracy
