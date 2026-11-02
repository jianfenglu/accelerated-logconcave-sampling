import AcceleratedLogConcave.Analysis.WeightedGradient.MeasureBridge
import AcceleratedLogConcave.External.Samplinglib.TechnicalLemmas.FunctionalInequalities.WeightedGradientWeak
import AcceleratedLogConcave.External.Samplinglib.TechnicalLemmas.FunctionalInequalities.WeightedC1GradientDomain

/-!
# The actual closed weighted gradient

The initial graph is exactly the graph of gradients of compactly supported smooth
functions in the two weighted L2 spaces. Closability and density are proved from
the C1 Gibbs density. `closedGradient` is its graph closure, not an operator
supplied with a Poincare hypothesis. The law is an explicit argument so that
normalization and posterior modules can use their own measure definitions.
-/

noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace Topology

namespace AcceleratedLogConcave.Analysis.WeightedGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem exists_compactGradient (μ : Measure E) (V : E → ℝ)
    (hV : ContDiff ℝ 1 V) (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x)) :
    ∃ D : Lp ℝ 2 μ →ₗ.[ℝ] Lp E 2 μ,
      Dense (D.domain : Set (Lp ℝ 2 μ)) ∧ D.IsClosable ∧ D.closure.IsClosed ∧
      ∀ (f : Lp ℝ 2 μ) (G : Lp E 2 μ), (f, G) ∈ D.graph ↔
        ∃ φ : E → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
          f =ᵐ[μ] φ ∧ G =ᵐ[μ] gradient φ := by
  subst μ
  exact AutoSamplingTheory.TechnicalLemmas.FunctionalInequalities.WeightedGradient.compact_gradient_closable V hV hI

/-- The densely defined gradient of compactly supported smooth representatives. -/
def compactGradient (μ : Measure E) (V : E → ℝ)
    (hV : ContDiff ℝ 1 V) (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : μ = volume.tilted (fun x => -V x)) : Lp ℝ 2 μ →ₗ.[ℝ] Lp E 2 μ :=
  Classical.choose (exists_compactGradient μ V hV hI hμ)

variable (μ : Measure E) (V : E → ℝ)
  (hV : ContDiff ℝ 1 V) (hI : Integrable (fun x => Real.exp (-V x)))
  (hμ : μ = volume.tilted (fun x => -V x))

theorem compactGradient_dense :
    Dense ((compactGradient μ V hV hI hμ).domain : Set (Lp ℝ 2 μ)) :=
  (Classical.choose_spec (exists_compactGradient μ V hV hI hμ)).1

theorem compactGradient_closable : (compactGradient μ V hV hI hμ).IsClosable :=
  (Classical.choose_spec (exists_compactGradient μ V hV hI hμ)).2.1

theorem mem_compactGradient_graph (f : Lp ℝ 2 μ) (G : Lp E 2 μ) :
    (f, G) ∈ (compactGradient μ V hV hI hμ).graph ↔
      ∃ φ : E → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
        f =ᵐ[μ] φ ∧ G =ᵐ[μ] gradient φ :=
  (Classical.choose_spec (exists_compactGradient μ V hV hI hμ)).2.2.2 f G

/-- The closed weighted gradient, defined as the closure of the actual smooth graph. -/
def closedGradient : Lp ℝ 2 μ →ₗ.[ℝ] Lp E 2 μ :=
  (compactGradient μ V hV hI hμ).closure

/-- Weighted Sobolev functions are elements of the actual closed gradient domain. -/
abbrev Sobolev := (closedGradient μ V hV hI hμ).domain

theorem closedGradient_isClosed : (closedGradient μ V hV hI hμ).IsClosed :=
  (compactGradient_closable μ V hV hI hμ).closure_isClosed

/-- The closed domain is dense in weighted L2. -/
theorem closedGradient_dense :
    Dense ((closedGradient μ V hV hI hμ).domain : Set (Lp ℝ 2 μ)) :=
  (compactGradient_dense μ V hV hI hμ).mono
    (compactGradient μ V hV hI hμ).le_closure.1

theorem closedGradient_graph_eq :
    (closedGradient μ V hV hI hμ).graph =
      (compactGradient μ V hV hI hμ).graph.topologicalClosure :=
  (compactGradient_closable μ V hV hI hμ).graph_closure_eq_closure_graph.symm

/-- C1 functions whose value and genuine gradient are L2 belong to this closure. -/
theorem c1_mem_closedGradient_graph {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hp : MemLp f 2 μ) (hq : MemLp (gradient f) 2 μ) :
    (hp.toLp f, hq.toLp (gradient f)) ∈ (closedGradient μ V hV hI hμ).graph := by
  have : IsProbabilityMeasure μ := hμ ▸ isProbabilityMeasure_tilted hI
  exact AutoSamplingTheory.TechnicalLemmas.FunctionalInequalities.WeightedC1GradientDomain.c1_in_closed_gradient
    μ (compactGradient μ V hV hI hμ) (compactGradient_closable μ V hV hI hμ)
    (mem_compactGradient_graph μ V hV hI hμ) hf hp hq

/-- Constants are genuine domain elements and have zero closed gradient. -/
theorem constants_mem_closedGradient (c : ℝ) :
    ∃ u : Sobolev μ V hV hI hμ,
      (u : Lp ℝ 2 μ) =ᵐ[μ] (fun _ => c) ∧ closedGradient μ V hV hI hμ u = 0 := by
  have : IsProbabilityMeasure μ := hμ ▸ isProbabilityMeasure_tilted hI
  exact AutoSamplingTheory.TechnicalLemmas.FunctionalInequalities.WeightedC1GradientDomain.constants_in_closed_gradient
    μ (compactGradient μ V hV hI hμ) (compactGradient_closable μ V hV hI hμ)
    (mem_compactGradient_graph μ V hV hI hμ) c

/-- Weighted integration by parts for every member of the closed domain.
Both products are integrable; the compact test justifies the boundary term. -/
theorem closedGradient_integrationByParts (u : Sobolev μ V hV hI hμ)
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (v : E) :
    Integrable (fun x => φ x * inner ℝ (closedGradient μ V hV hI hμ u x) v) μ ∧
    Integrable (fun x => (u : Lp ℝ 2 μ) x *
      (fderiv ℝ φ x v - φ x * fderiv ℝ V x v)) μ ∧
    (∫ x, φ x * inner ℝ (closedGradient μ V hV hI hμ u x) v ∂μ) =
      -∫ x, (u : Lp ℝ 2 μ) x * (fderiv ℝ φ x v - φ x * fderiv ℝ V x v) ∂μ := by
  have h := AutoSamplingTheory.TechnicalLemmas.FunctionalInequalities.WeightedGradientWeak.closed_gradient_weighted_ibp (E := E)
  subst μ
  exact h V hV hI (compactGradient _ V hV hI rfl)
    (compactGradient_closable _ V hV hI rfl)
    (mem_compactGradient_graph _ V hV hI rfl) u
    (closedGradient _ V hV hI rfl u) (LinearPMap.mem_graph _ u) φ hφ hc v

end AcceleratedLogConcave.Analysis.WeightedGradient
