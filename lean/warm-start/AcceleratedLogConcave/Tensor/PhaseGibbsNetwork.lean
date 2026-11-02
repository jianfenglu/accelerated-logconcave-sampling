import AcceleratedLogConcave.Tensor.NetworkPrincipalIBP
import AcceleratedLogConcave.Tensor.PolynomialClosure

/-! Generic smooth Gibbs integration by parts for a whole connected network.
The hypotheses concern primitive coordinate jets and the underlying Gibbs law,
not moments of expressions or the desired dimension-sharp conclusion. -/
noncomputable section
open MeasureTheory
open scoped Classical BigOperators ContDiff
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction PolynomialClosure Conditional.Appell
variable {D n : ℕ} {Edge : Type*} [Fintype Edge]

/-- Qualitative analytic environment. Quantitative split budgets are separate.
The moment hypothesis is on powers of the ambient coordinate norm, not on any
expression. It is used only to justify the actual IBP and finite sums. -/
structure SmoothGibbsEnvironment (D : ℕ) where
  base : Measure (EuclideanSpace ℝ (Fin D))
  haar : base.IsAddHaarMeasure
  potential : EuclideanSpace ℝ (Fin D) → ℝ
  smooth : ContDiff ℝ ∞ potential
  partition_integrable : Integrable (fun x => Real.exp (-potential x)) base
  finite : IsFiniteMeasure (base.tilted (fun x => -potential x))
  moments : HasMoments (base.tilted (fun x => -potential x))
  score_jets : ∀ v, HasPolynomialJets (dir v potential)

namespace SmoothGibbsEnvironment
variable (G : SmoothGibbsEnvironment D)
def law := G.base.tilted (fun x => -G.potential x)

/-- A generic principal adjoint is removed by actual Gibbs IBP. All recipients
are different occurrences; no self contraction or expression-moment premise. -/
theorem integral_adjoint_network (g : Graph n Edge) (p : Fin (n+1))
    (T : EuclideanSpace ℝ (Fin D) → g.Tensors D)
    (A : EuclideanSpace ℝ (Fin D) → Fin D → Coeff (g.Slot p) D)
    (hA : ∀ k a, ContDiff ℝ ∞ (fun x => A x k a))
    (hAp : ∀ k a, HasPolynomialJets (fun x => A x k a))
    (hT : ∀ v, v ≠ p → ∀ a, ContDiff ℝ ∞ (fun x => T x v a))
    (hTp : ∀ v, v ≠ p → ∀ a, HasPolynomialJets (fun x => T x v a))
    (hparent : ∀ x, T x p = g.adjointCoordinateTensor p G.potential A x) :
    (∫ x, g.coordinateEval D (T x) ∂G.law) =
      ∑ q : {v : Fin (n+1) // v ≠ p}, ∫ x,
        (g.recipientGraph p q.val (Ne.symm q.property)).coordinateEval D
          (g.principalRecipientFamily p q.val (Ne.symm q.property) T A x) ∂G.law := by
  let :=  G.haar
  let :=  G.finite
  have hts (v : Fin (n+1)) (a : g.Slot v → Fin D) :
      ContDiff ℝ ∞ (fun x => T x v a) := by
    by_cases hv : v = p
    · subst v
      have he : (fun x => T x p a) = (fun x => adjointField
          G.potential (coordinateDirection D) (fun k y => A y k a) x) := by
        funext x
        exact congrArg (fun z : Coeff (g.Slot p) D => z a) (hparent x)
      rw [he]
      unfold adjointField adjointComponent
      apply ContDiff.sum
      intro k _
      exact (contDiff_dir (hA k a) _).neg.add
        ((contDiff_dir G.smooth _).mul (hA k a))
    · exact hT v hv a
  have hi (c : Option Edge → Fin D) (k : Fin D) :=
    productIntegrability_of_polynomialJets G.moments
      (fun _ : Unit => (0 : EuclideanSpace ℝ (Fin D))) [] G.potential
      (fun x => A x k (Sum.elim (fun s : g.InPort p => c s.val)
        (fun s : g.OutPort p => c s.val))) (coordinateDirection D k)
      (fun q : {v : Fin (n+1) // v ≠ p} => fun x => g.wireValue (T x) c q.val)
      G.smooth (hA k _) (fun q => hts q.val _) (G.score_jets _)
      (hAp k _) (fun q => hTp q.val q.property _)
  exact g.integral_adjoint_network p G.potential G.smooth G.partition_integrable
    T A hA (fun v a => (hts v a).differentiable (by simp)) hparent hi

/-- Primitive polynomial coordinate jets suffice for every expression's jets,
including genuine derivative nodes omitted by the material-only receiver. -/
theorem expression_polynomial_jets {Name : Type*} {σ : CoefficientSignature Name}
    (ρ : CoefficientEnvironment σ D)
    (hρs : ∀ c a, ContDiff ℝ ∞ (fun x => ρ c x a))
    (hρ : ∀ c a, HasPolynomialJets (fun x => ρ c x a))
    {r : ℕ} (e : Expr σ r) (a : Fin r → Fin D) :
    HasPolynomialJets (sectionValue ρ G.potential e a) :=
  section_hasPolynomialJets ρ G.potential hρs G.smooth hρ G.score_jets e a
end SmoothGibbsEnvironment
end AcceleratedLogConcave.Tensor.Ordered.Graph
