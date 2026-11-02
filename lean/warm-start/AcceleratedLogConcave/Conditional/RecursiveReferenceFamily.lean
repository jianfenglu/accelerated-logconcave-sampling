import AcceleratedLogConcave.Conditional.RecursiveReferenceStep

/-! The actual source reference producer, recursively indexed by the real
precision. Recursion stops at q ≤ 1/2. Each active-final child uses q−t,
radius r R and physical width R sqrt(3) sigma/4, with the original potential.
There is no supplied recursive kernel, law, or tree certificate. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff ENNReal
namespace AcceleratedLogConcave.Conditional.RecursiveReference
open Numerics Numerics.MeanFlowLp Numerics.AffineGraph MeanReferenceLayer
open TerminalChildrenParentFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι
variable {F : EuclideanSpace ℝ ι → ℝ} {ell : ℝ} (hF : ContDiff ℝ 2 F) (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
  (G : MeanGeometry m) (hm : 0 < m)

local instance (q : ℝ) : Decidable (Oracle.Precision.terminal q) := Classical.propDecidable _

/-- Literal recursive source reference family on all admissible physical
centers, radii, widths and retained original inputs. -/
def referenceFamily (t : ℝ) (ht : 0 < t) (q : ℝ) : Family ι ell :=
  if _hq : Oracle.Precision.terminal q then terminalFamily
  else parentFamily hF hell hlo hup G hm (referenceFamily t ht (q-t))
termination_by Oracle.Precision.precisionRank t q
decreasing_by exact precision_child_lt ht (lt_of_not_ge _hq)

variable (t : ℝ) (ht : 0 < t)

theorem referenceFamily_terminal (q : ℝ) (hq : Oracle.Precision.terminal q) :
    referenceFamily hF hell hlo hup G hm t ht q = terminalFamily := by
  rw [referenceFamily,dite_eq_left hq]

theorem referenceFamily_nonterminal (q : ℝ) (hq : (1 / 2 : ℝ) < q) :
    referenceFamily hF hell hlo hup G hm t ht q =
      parentFamily hF hell hlo hup G hm
        (referenceFamily hF hell hlo hup G hm t ht (q-t)) := by
  rw [referenceFamily,dite_eq_right (show ¬ Oracle.Precision.terminal q by exact not_le.mpr hq)]

instance referenceFamily_markov (q : ℝ) :
    IsMarkovKernel (referenceFamily hF hell hlo hup G hm t ht q).kernel :=
  (referenceFamily hF hell hlo hup G hm t ht q).markov

theorem referenceFamily_invariant (q : ℝ) (theta : SourceParameters E ell) :
    (referenceFamily hF hell hlo hup G hm t ht q).kernel.comap
      (fun p ↦ (theta,p)) measurable_prodMk_left ∘ₘ stdGaussian E = stdGaussian E :=
  (referenceFamily hF hell hlo hup G hm t ht q).invariant theta

/-- Exact fixed-input source-parent equality at every nonterminal precision. -/
theorem referenceFamily_section (q : ℝ) (hq : (1 / 2 : ℝ) < q)
    (theta : SourceParameters E ell) :
    (referenceFamily hF hell hlo hup G hm t ht q).kernel.comap
      (fun p ↦ (theta,p)) measurable_prodMk_left =
      parentKernel (data hF hell hlo hup G theta)
        (sourceChildren hF hell hlo hup G hm
          (referenceFamily hF hell hlo hup G hm t ht (q-t)) theta) := by
  rw [referenceFamily_nonterminal hF hell hlo hup G hm t ht q hq]
  exact stepKernel_section hF hell hlo hup G hm _ theta


/-- The recursive family is jointly Borel in all actual source parameters and
the retained original input. -/
theorem referenceFamily_measurable (q : ℝ) :
    Measurable (fun z : SourceParameters E ell × E ↦
      (referenceFamily hF hell hlo hup G hm t ht q).kernel z) :=
  (referenceFamily hF hell hlo hup G hm t ht q).kernel.measurable

/-- Every child call is the actual lower precision family, evaluated at the
actual radius and width; the original designated input is retained. -/
theorem referenceFamily_child_apply (q : ℝ) (theta : SourceParameters E ell)
    (i : Fin m) (y p : E) :
    (sourceChildren hF hell hlo hup G hm
      (referenceFamily hF hell hlo hup G hm t ht (q-t)) theta).kernel i (y,p) =
      (referenceFamily hF hell hlo hup G hm t ht (q-t)).kernel
        (childParameters hell G theta y,p) := rfl

/-- The actual conditional finite product at every original host state. -/
theorem referenceFamily_product (q : ℝ) (theta : SourceParameters E ell) (h : Host ι m) :
    let C := sourceChildren hF hell hlo hup G hm
      (referenceFamily hF hell hlo hup G hm t ht (q-t)) theta
    childrenKernel (data hF hell hlo hup G theta) C h =
      Measure.pi (fun i ↦ (referenceFamily hF hell hlo hup G hm t ht (q-t)).kernel
        (childParameters hell G theta
          (childCenter (data hF hell hlo hup G theta) C i h),
          active (data hF hell hlo hup G theta) C h (some i))) := by
  dsimp only
  rw [(product_target _ _).2]
  rfl

/-- The actual child outputs and recovered reserve have the proved joint
Gaussian law after the original input is integrated against its Gaussian law. -/
theorem referenceFamily_childJoint (q : ℝ) (theta : SourceParameters E ell) :
    ChildJointTarget (data hF hell hlo hup G theta)
      (sourceChildren hF hell hlo hup G hm
        (referenceFamily hF hell hlo hup G hm t ht (q-t)) theta) :=
  childJoint_target _ _

/-- Exact retained pair law of the recursively assembled parent. -/
theorem referenceFamily_retained (q : ℝ) (hq : (1 / 2 : ℝ) < q)
    (theta : SourceParameters E ell) :
    let d := data hF hell hlo hup G theta
    let C := sourceChildren hF hell hlo hup G hm
      (referenceFamily hF hell hlo hup G hm t ht (q-t)) theta
    (averagedJoint d C).map (fun z ↦ (z.1.1,recombine d C z.1 z.2)) =
      (stdGaussian E) ⊗ₘ ((referenceFamily hF hell hlo hup G hm t ht q).kernel.comap
        (fun p ↦ (theta,p)) measurable_prodMk_left) := by
  rw [referenceFamily_section hF hell hlo hup G hm t ht q hq]
  exact retained_joint _ _

/-- Recovery of the literal terminal identity reference at every retained input. -/
theorem referenceFamily_terminal_apply (q : ℝ) (hq : Oracle.Precision.terminal q)
    (theta : SourceParameters E ell) (p : E) :
    (referenceFamily hF hell hlo hup G hm t ht q).kernel (theta,p) = Measure.dirac p := by
  rw [referenceFamily_terminal hF hell hlo hup G hm t ht q hq]
  rfl


/-- The source equality boundary is terminal, including its original input. -/
theorem referenceFamily_cutoff (theta : SourceParameters E ell) (p : E) :
    (referenceFamily hF hell hlo hup G hm t ht (1 / 2)).kernel (theta,p) = Measure.dirac p :=
  referenceFamily_terminal_apply hF hell hlo hup G hm t ht _ (by exact le_rfl) theta p

/-- A zero recursive rank unfolds no parent operation. -/
theorem referenceFamily_zero_rank (q : ℝ)
    (hzero : Oracle.Precision.precisionRank t q = 0) :
    referenceFamily hF hell hlo hup G hm t ht q = terminalFamily :=
  referenceFamily_terminal hF hell hlo hup G hm t ht q
    ((Oracle.Precision.precisionRank_zero_iff ht).mp hzero)

omit [DecidableEq ι] in
/-- Terminal children agree with the existing terminal source supplier. -/
theorem sourceChildren_terminal (theta : SourceParameters E ell) :
    sourceChildren hF hell hlo hup G hm terminalFamily theta =
      terminalChildren (data hF hell hlo hup G theta) hm := by
  rfl

/-- The first nonterminal band recovers the previously proved source family,
including equality at each original input and its actual centering increment. -/
theorem referenceFamily_firstBand (q : ℝ) (hq : (1 / 2 : ℝ) < q)
    (hband : q ≤ 1 / 2 + t) (theta : SourceParameters E ell) :
    (referenceFamily hF hell hlo hup G hm t ht q).kernel.comap
      (fun p ↦ (theta,p)) measurable_prodMk_left =
      (familyKernel hF hell hlo hup G).comap
        (fun p ↦ (theta,p)) measurable_prodMk_left := by
  rw [referenceFamily_section hF hell hlo hup G hm t ht q hq,
    referenceFamily_terminal hF hell hlo hup G hm t ht (q-t) (by
      unfold Oracle.Precision.terminal
      linarith),sourceChildren_terminal hF hell hlo hup G hm,
    familyKernel_section hF hell hlo hup G hm theta]


omit [DecidableEq ι] in
/-- The child keeps the literal potential F, with the prescribed physical
center and reduced radius; no replacement potential is supplied. -/
theorem referenceFamily_child_potential (theta : SourceParameters E ell) (y z : E) :
    (data hF hell hlo hup G (childParameters hell G theta y)).F = F ∧
      primitivePotential F (childParameters hell G theta y).center
        (childParameters hell G theta y).radius z = F (y + (theta.radius * G.R) • z) :=
  ⟨rfl,rfl⟩

omit [DecidableEq ι] in
/-- Every actual final slot has the source child precision and actual physical
parameters; no execution is removed by a vanishing coefficient. -/
theorem referenceFamily_final_inventory (q : ℝ) (hq : (1 / 2 : ℝ) < q)
    (theta : SourceParameters E ell) (i : Fin m) (h : Host ι m) :
    Oracle.Precision.CallEdge t .activeFinal (.mean (q-t)) (.mean q) ∧
    (childParameters hell G theta (sourceChildCenter hF hell hlo hup G i (theta,h))).radius =
      theta.radius * G.R ∧
    (childParameters hell G theta (sourceChildCenter hF hell hlo hup G i (theta,h))).width =
      G.R * Real.sqrt 3 * theta.width / 4 :=
  ⟨Oracle.Precision.CallEdge.activeFinal hq,rfl,rfl⟩

end AcceleratedLogConcave.Conditional.RecursiveReference
