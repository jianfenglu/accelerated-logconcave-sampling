import AcceleratedLogConcave.Root.RecursiveInnovation
import DirectW12.ObservableJensen

/-!

-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set MeasureTheory ProbabilityTheory Filter
open scoped ContDiff ENNReal RealInnerProductSpace
namespace AcceleratedLogConcave.Root.RecursiveInnovation
/-- The clock section used by the physical dormant channel. -/
def physicalSourceSection
    {ι : Type*} [fi : Fintype ι] [di : DecidableEq ι] {m : ℕ}
    {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2)
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)
    (G : _root_.AcceleratedLogConcave.Numerics.AffineGraph.MeanGeometry m) (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) (K : ℕ)
    (P : _root_.AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily
      (EuclideanSpace ℝ ι) 0 (1/2))
    (clock : _root_.AcceleratedLogConcave.Root.ClockLaw.Clock) :
    _root_.ProbabilityTheory.Kernel
      (_root_.AcceleratedLogConcave.Kinetic.GaussianPhase (EuclideanSpace ℝ ι))
      (EuclideanSpace ℝ ι) :=
  let D : _root_.AcceleratedLogConcave.Root.ClockBackwardKernel.RadiusChildren ι h K :=
    _root_.AcceleratedLogConcave.Root.RecursiveRadiusFamily.physicalRadiusChildren
      (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
      (V := V) (hV := hV) (hlo := hlo) (hup := hup)
      (G := G) (hm := hm) (t := t) (ht := ht) (K := K)
  let κ : _root_.ProbabilityTheory.Kernel
      (_root_.AcceleratedLogConcave.Root.ClockLaw.Clock ×
        _root_.AcceleratedLogConcave.Kinetic.GaussianPhase (EuclideanSpace ℝ ι))
      (EuclideanSpace ℝ ι) :=
    _root_.AcceleratedLogConcave.Root.ClockBackwardKernel.sourceKernelFromRadiusFamily
      (ι := ι) (F := P) (h := h) (hh := hh) (K := K) (D := D)
  _root_.ProbabilityTheory.Kernel.comap κ
    (fun z : _root_.AcceleratedLogConcave.Kinetic.GaussianPhase (EuclideanSpace ℝ ι) =>
      (clock, z))
    (_root_.measurable_prodMk_left)

open Numerics.AffineGraph Kinetic Kinetic.ConditionalContraction


instance physicalSourceSection_markov
    {ι : Type*} [fi : Fintype ι] [di : DecidableEq ι] {m : ℕ}
    {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2)
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)
    (G : _root_.AcceleratedLogConcave.Numerics.AffineGraph.MeanGeometry m) (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) (K : ℕ)
    (P : _root_.AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily
      (EuclideanSpace ℝ ι) 0 (1/2))
    (clock : _root_.AcceleratedLogConcave.Root.ClockLaw.Clock) :
    _root_.ProbabilityTheory.IsMarkovKernel (_root_.AcceleratedLogConcave.Root.RecursiveInnovation.physicalSourceSection
      (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
      (V := V) (hV := hV) (hlo := hlo) (hup := hup)
      (G := G) (hm := hm) (t := t) (ht := ht) (K := K)
      (P := P) (clock := clock)) := by
  let D : _root_.AcceleratedLogConcave.Root.ClockBackwardKernel.RadiusChildren ι h K :=
    _root_.AcceleratedLogConcave.Root.RecursiveRadiusFamily.physicalRadiusChildren
      (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
      (V := V) (hV := hV) (hlo := hlo) (hup := hup)
      (G := G) (hm := hm) (t := t) (ht := ht) (K := K)
  let κ : _root_.ProbabilityTheory.Kernel
      (_root_.AcceleratedLogConcave.Root.ClockLaw.Clock ×
        _root_.AcceleratedLogConcave.Kinetic.GaussianPhase (EuclideanSpace ℝ ι))
      (EuclideanSpace ℝ ι) :=
    _root_.AcceleratedLogConcave.Root.ClockBackwardKernel.sourceKernelFromRadiusFamily
      (ι := ι) (F := P) (h := h) (hh := hh) (K := K) (D := D)
  have hκ : _root_.ProbabilityTheory.IsMarkovKernel κ :=
    _root_.AcceleratedLogConcave.Root.ClockBackwardKernel.sourceKernelFromRadiusFamily_markov
      (ι := ι) (F := P) (h := h) (hh := hh) (K := K) (D := D)
  change _root_.ProbabilityTheory.IsMarkovKernel
    (_root_.ProbabilityTheory.Kernel.comap κ
      (fun z : _root_.AcceleratedLogConcave.Kinetic.GaussianPhase (EuclideanSpace ℝ ι) => (clock, z))
      (_root_.measurable_prodMk_left))
  exact ⟨fun z => hκ.isProbabilityMeasure (clock, z)⟩


theorem physicalSourceSection_invariant
    {ι : Type*} [fi : Fintype ι] [di : DecidableEq ι] {m : ℕ}
    {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2)
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)
    (G : _root_.AcceleratedLogConcave.Numerics.AffineGraph.MeanGeometry m) (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) (K : ℕ)
    (P : _root_.AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily
      (EuclideanSpace ℝ ι) 0 (1/2))
    (clock : _root_.AcceleratedLogConcave.Root.ClockLaw.Clock) :
    _root_.AcceleratedLogConcave.Kinetic.ConditionalContraction.ConditionallyInvariant
      (stdGaussian (EuclideanSpace ℝ ι))
      (_root_.AcceleratedLogConcave.Root.RecursiveInnovation.physicalSourceSection
      (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
      (V := V) (hV := hV) (hlo := hlo) (hup := hup)
      (G := G) (hm := hm) (t := t) (ht := ht) (K := K)
      (P := P) (clock := clock)) := by
  let D : _root_.AcceleratedLogConcave.Root.ClockBackwardKernel.RadiusChildren ι h K :=
    _root_.AcceleratedLogConcave.Root.RecursiveRadiusFamily.physicalRadiusChildren
      (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
      (V := V) (hV := hV) (hlo := hlo) (hup := hup)
      (G := G) (hm := hm) (t := t) (ht := ht) (K := K)
  let κ : _root_.ProbabilityTheory.Kernel
      (_root_.AcceleratedLogConcave.Root.ClockLaw.Clock ×
        _root_.AcceleratedLogConcave.Kinetic.GaussianPhase (EuclideanSpace ℝ ι))
      (EuclideanSpace ℝ ι) :=
    _root_.AcceleratedLogConcave.Root.ClockBackwardKernel.sourceKernelFromRadiusFamily
      (ι := ι) (F := P) (h := h) (hh := hh) (K := K) (D := D)
  change ∀ (parent : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι)) (s : Set (EuclideanSpace ℝ ι)),
    MeasurableSet s →
      (∫⁻ p, κ (clock, (parent, p)) s ∂stdGaussian (EuclideanSpace ℝ ι)) =
        stdGaussian (EuclideanSpace ℝ ι) s
  exact _root_.AcceleratedLogConcave.Root.ClockBackwardKernel.sourceKernelFromRadiusFamily_conditionallyInvariant
    (ι := ι) (F := P) (h := h) (hh := hh) (K := K) (D := D) (t := clock)

/-- Literal section equality with the normalized root at this parent. -/

theorem physicalSourceSection_parent
    {ι : Type*} [fi : Fintype ι] [di : DecidableEq ι] {m : ℕ}
    {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2)
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)
    (G : _root_.AcceleratedLogConcave.Numerics.AffineGraph.MeanGeometry m) (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) (K : ℕ)
    (P : _root_.AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily
      (EuclideanSpace ℝ ι) 0 (1/2))
    (clock : _root_.AcceleratedLogConcave.Root.ClockLaw.Clock)
    (parent : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι)) :
    _root_.ProbabilityTheory.Kernel.comap
      (_root_.AcceleratedLogConcave.Root.RecursiveInnovation.physicalSourceSection
      (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
      (V := V) (hV := hV) (hlo := hlo) (hup := hup)
      (G := G) (hm := hm) (t := t) (ht := ht) (K := K)
      (P := P) (clock := clock))
      (fun p : EuclideanSpace ℝ ι => (parent, p))
      (_root_.measurable_prodMk_left) =
        _root_.AcceleratedLogConcave.Root.RetainedLaw.rootKernel
          (_root_.AcceleratedLogConcave.Root.RecursiveInnovation.physicalSourceData
      (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
      (V := V) (hV := hV) (hlo := hlo) (hup := hup)
      (G := G) (hm := hm) (t := t) (ht := ht) (K := K)
      (P := P) (clock := clock) (parent := parent)) := by
  let D : _root_.AcceleratedLogConcave.Root.ClockBackwardKernel.RadiusChildren ι h K :=
    _root_.AcceleratedLogConcave.Root.RecursiveRadiusFamily.physicalRadiusChildren
      (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
      (V := V) (hV := hV) (hlo := hlo) (hup := hup)
      (G := G) (hm := hm) (t := t) (ht := ht) (K := K)
  let κ : _root_.ProbabilityTheory.Kernel
      (_root_.AcceleratedLogConcave.Root.ClockLaw.Clock ×
        _root_.AcceleratedLogConcave.Kinetic.GaussianPhase (EuclideanSpace ℝ ι))
      (EuclideanSpace ℝ ι) :=
    _root_.AcceleratedLogConcave.Root.ClockBackwardKernel.sourceKernelFromRadiusFamily
      (ι := ι) (F := P) (h := h) (hh := hh) (K := K) (D := D)
  have hsection :
      _root_.ProbabilityTheory.Kernel.comap κ
        (fun p : EuclideanSpace ℝ ι => (clock, (parent, p)))
        (_root_.measurable_const.prodMk
          (_root_.measurable_prodMk_left)) =
        _root_.AcceleratedLogConcave.Root.RetainedLaw.rootKernel
          (_root_.AcceleratedLogConcave.Root.RecursiveInnovation.physicalSourceData
      (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
      (V := V) (hV := hV) (hlo := hlo) (hup := hup)
      (G := G) (hm := hm) (t := t) (ht := ht) (K := K)
      (P := P) (clock := clock) (parent := parent)) :=
    _root_.AcceleratedLogConcave.Root.RecursiveInnovation.sourceData_kernel_section
      (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf)
      (F := _root_.AcceleratedLogConcave.Root.RecursiveRadiusFamily.physicalPotential V h)
      (hF := _root_.AcceleratedLogConcave.Root.RecursiveRadiusFamily.physicalPotential_C2
        (ι := ι) (V := V) (hV := hV) (h := h))
      (hlo := _root_.AcceleratedLogConcave.Root.RecursiveRadiusFamily.physicalPotential_hessian_nonneg
        (ι := ι) (V := V) (hV := hV) (hlo := hlo) (h := h) (hh := hh.le))
      (hup := _root_.AcceleratedLogConcave.Root.RecursiveRadiusFamily.physicalPotential_hessian_upper
        (ι := ι) (V := V) (hV := hV) (hup := hup) (h := h) (hh := hh.le))
      (G := G) (hm := hm) (t := t) (ht := ht) (K := K)
      (P := P) (clock := clock) (parent := parent)
  ext p : 1
  exact congrArg (fun k : _root_.ProbabilityTheory.Kernel (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι) => k p) hsection



/-- The old-new joint is inherited from execution, not reconstructed from its
marginals. The first output of this map is literally the original input z.1.1. -/
theorem physicalSourceSection_retained_joint
    {ι : Type*} [fi : Fintype ι] [di : DecidableEq ι] {m : ℕ}
    {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2)
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)
    (G : _root_.AcceleratedLogConcave.Numerics.AffineGraph.MeanGeometry m) (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) (K : ℕ)
    (P : _root_.AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily
      (EuclideanSpace ℝ ι) 0 (1/2))
    (clock : ClockLaw.Clock) (parent : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι)) :
    let d := physicalSourceData (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf) (V := V) (hV := hV) (hlo := hlo) (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := clock) (parent := parent)
    (RetainedLaw.averagedJoint d).map (fun z => (z.1.1, RetainedLaw.output d z)) =
      (stdGaussian (EuclideanSpace ℝ ι)) ⊗ₘ
        (physicalSourceSection (ι := ι) (fi := fi) (di := di) (m := m) (h := h) (hh := hh) (hhalf := hhalf) (V := V) (hV := hV) (hlo := hlo) (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := clock)).comap
          (fun p : (EuclideanSpace ℝ ι) => (parent,p)) (_root_.measurable_prodMk_left) := by
  rw [physicalSourceSection_parent (ι := ι) (fi := fi) (di := di) (m := m) (h := h) (hh := hh) (hhalf := hhalf) (V := V) (hV := hV) (hlo := hlo) (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := clock) (parent := parent)]
  exact RetainedLaw.retained_joint _

/-- Test-function law transport for a fixed actual parent. No integrability
hypothesis is required for this nonnegative form. -/
theorem physicalSourceSection_lintegral
    {ι : Type*} [fi : Fintype ι] [di : DecidableEq ι] {m : ℕ}
    {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2)
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)
    (G : _root_.AcceleratedLogConcave.Numerics.AffineGraph.MeanGeometry m) (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) (K : ℕ)
    (P : _root_.AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily
      (EuclideanSpace ℝ ι) 0 (1/2))
    (clock : ClockLaw.Clock) (parent : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι))
    (f : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, ∫⁻ q, f (p,q)
      ∂physicalSourceSection (ι := ι) (fi := fi) (di := di) (m := m) (h := h) (hh := hh) (hhalf := hhalf) (V := V) (hV := hV) (hlo := hlo) (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := clock) (parent,p)
      ∂stdGaussian (EuclideanSpace ℝ ι)) =
      let d := physicalSourceData (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf) (V := V) (hV := hV) (hlo := hlo) (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := clock) (parent := parent)
      ∫⁻ z, f (z.1.1, RetainedLaw.output d z) ∂RetainedLaw.averagedJoint d := by
  let d := physicalSourceData (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf) (V := V) (hV := hV) (hlo := hlo) (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := clock) (parent := parent)
  have hmap : Measurable (fun z : RetainedLaw.Execution (ι := ι)
      (m := ClockSchedule.sourceCells h * ClockSchedule.sourceOrder K) =>
      (z.1.1, RetainedLaw.output d z)) :=
    measurable_fst.fst.prodMk (RetainedLaw.measurable_output d)
  have he := physicalSourceSection_retained_joint (ι := ι) (fi := fi) (di := di) (m := m) (h := h) (hh := hh) (hhalf := hhalf) (V := V) (hV := hV) (hlo := hlo) (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := clock) (parent := parent)
  have hi := congrArg (fun ν => ∫⁻ z, f z ∂ν) he
  rw [lintegral_map hf hmap, Measure.lintegral_compProd hf] at hi
  exact hi.symm

/-- Full dormant law disintegrated over the retained exact parent and the SAME
root execution. This is the global join needed for a parent-dependent vector. -/
theorem physicalSourceSection_dormant_lintegral
    {ι : Type*} [fi : Fintype ι] [di : DecidableEq ι] {m : ℕ}
    {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2)
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)
    (G : _root_.AcceleratedLogConcave.Numerics.AffineGraph.MeanGeometry m) (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) (K : ℕ)
    (P : _root_.AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily
      (EuclideanSpace ℝ ι) 0 (1/2))
    (clock : ClockLaw.Clock)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (f : GaussianPhase (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂dormantJoint (μ.prod (stdGaussian (EuclideanSpace ℝ ι))) (stdGaussian (EuclideanSpace ℝ ι))
      (physicalSourceSection (ι := ι) (fi := fi) (di := di) (m := m) (h := h) (hh := hh) (hhalf := hhalf) (V := V) (hV := hV) (hlo := hlo) (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := clock))) =
      ∫⁻ parent, let d := physicalSourceData (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf) (V := V) (hV := hV) (hlo := hlo) (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := clock) (parent := parent)
        ∫⁻ z, f ((parent,z.1.1),RetainedLaw.output d z) ∂RetainedLaw.averagedJoint d
          ∂μ.prod (stdGaussian (EuclideanSpace ℝ ι)) := by
  rw [dormantJoint, Measure.lintegral_compProd hf]
  rw [lintegral_prod _ hf.lintegral_kernel_prod_right'.aemeasurable]
  apply lintegral_congr
  intro parent
  exact physicalSourceSection_lintegral (ι := ι) (fi := fi) (di := di) (m := m) (h := h) (hh := hh) (hhalf := hhalf) (V := V) (hV := hV) (hlo := hlo) (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := clock) (parent := parent)
    (fun pq => f ((parent,pq.1),pq.2)) (by fun_prop)

/-- Real squared moment transported through the exact pair law. -/
theorem physicalSourceSection_second_moment
    {ι : Type*} [fi : Fintype ι] [di : DecidableEq ι] {m : ℕ}
    {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2)
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)
    (G : _root_.AcceleratedLogConcave.Numerics.AffineGraph.MeanGeometry m) (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) (K : ℕ)
    (P : _root_.AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily
      (EuclideanSpace ℝ ι) 0 (1/2))
    (clock : ClockLaw.Clock) (parent : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι)) (v : (EuclideanSpace ℝ ι)) :
    (∫ pq, inner ℝ v (pq.2-pq.1)^2 ∂(stdGaussian (EuclideanSpace ℝ ι)) ⊗ₘ
      (physicalSourceSection (ι := ι) (fi := fi) (di := di) (m := m) (h := h) (hh := hh) (hhalf := hhalf) (V := V) (hV := hV) (hlo := hlo) (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := clock)).comap
        (fun p : (EuclideanSpace ℝ ι) => (parent,p)) (_root_.measurable_prodMk_left)) =
      let d := physicalSourceData (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf) (V := V) (hV := hV) (hlo := hlo) (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := clock) (parent := parent)
      ∫ z, inner ℝ v (RetainedLaw.output d z-z.1.1)^2 ∂RetainedLaw.averagedJoint d := by
  rw [← physicalSourceSection_retained_joint (ι := ι) (fi := fi) (di := di) (m := m) (h := h) (hh := hh) (hhalf := hhalf) (V := V) (hV := hV) (hlo := hlo) (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := clock) (parent := parent)]
  apply integral_map_of_stronglyMeasurable
  · exact measurable_fst.fst.prodMk (RetainedLaw.measurable_output _)
  · fun_prop

/-- The actual source covariance bound now targets its old/new kernel joint.
There is no generic covariance premise and no newly chosen conditional law. -/
theorem physicalSourceSection_innovation_bound
    {ι : Type*} [fi : Fintype ι] [di : DecidableEq ι] {m : ℕ}
    {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2)
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)
    (G : _root_.AcceleratedLogConcave.Numerics.AffineGraph.MeanGeometry m) (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) (K : ℕ)
    (P : _root_.AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily
      (EuclideanSpace ℝ ι) 0 (1/2))
    (clock : ClockLaw.Clock) (parent : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι)) (v : (EuclideanSpace ℝ ι)) :
    (3/4 : ℝ) * (∫ pq, inner ℝ v (pq.2-pq.1)^2 ∂(stdGaussian (EuclideanSpace ℝ ι)) ⊗ₘ
      (physicalSourceSection (ι := ι) (fi := fi) (di := di) (m := m) (h := h) (hh := hh) (hhalf := hhalf) (V := V) (hV := hV) (hlo := hlo) (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := clock)).comap
        (fun p : (EuclideanSpace ℝ ι) => (parent,p)) (_root_.measurable_prodMk_left)) ≤
      2*h^4 * ∑ i, (ClockSchedule.weight (ClockSchedule.sourceCells h)
        (ClockSchedule.sourceOrder K) clock i)^2 *
        (1-(ClockSchedule.node (ClockSchedule.sourceCells h) (ClockSchedule.sourceOrder K)
          (ClockSchedule.sourceCells_pos hh) clock i : ℝ)^2) *
        fderiv ℝ (fderiv ℝ (Gibbs.heatPotential V
          (2*h^2*(1-(ClockSchedule.node (ClockSchedule.sourceCells h) (ClockSchedule.sourceOrder K)
            (ClockSchedule.sourceCells_pos hh) clock i : ℝ)^2))))
          (physicalCenter (ι := ι) (h := h) (hh := hh) (K := K) (P := P) (clock := clock) (parent := parent) (i := i)) v v := by
  rw [physicalSourceSection_second_moment (ι := ι) (fi := fi) (di := di) (m := m) (h := h) (hh := hh) (hhalf := hhalf) (V := V) (hV := hV) (hlo := hlo) (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := clock) (parent := parent) (v := v)]
  exact physical_source_innovation_bound (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf) (V := V) (hV := hV) (hlo := hlo) (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := clock) (parent := parent) (v := v)

section SourcePhysicalPoissonDefinitions
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι
variable {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2)
  {V : E → ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)
  (G : MeanGeometry m) (hm : 0 < m) (t : ℝ) (ht : 0 < t) (K : ℕ)
  (P : Analysis.Poisson.ReferencePoissonFamily E 0 (1/2))


/-- A source-selected physical corrector: no artificial endpoint inverse. -/
def sourcePhysicalCorrector
    {ι : Type*} [fi : Fintype ι]
    (P : _root_.AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily
      (EuclideanSpace ℝ ι) 0 (1/2))
    (clock : ClockLaw.Clock) :
    Lp ℝ 2 (gaussianPhaseMeasure (P.law clock)) →L[ℝ]
      Lp ℝ 2 (gaussianPhaseMeasure (P.law clock)) :=
  gaussianCorrector (P.law clock) (P.potential clock) (P.potential_C2 clock)
    (P.integrable clock clock.property) (P.gibbs_law clock clock.property)
    (P.lower clock) 1 (P.lower_pos clock clock.property)
    (P.hessian_lower clock clock.property)
    (by simpa only [one_mul] using P.hessian_upper clock clock.property)

def sourcePhysicalCoefficient
    {ι : Type*} [fi : Fintype ι]
    (P : _root_.AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily
      (EuclideanSpace ℝ ι) 0 (1/2))
    (clock : ClockLaw.Clock)
    (f : Lp ℝ 2 (gaussianPhaseMeasure (P.law clock))) :
    Lp (EuclideanSpace ℝ ι) 2 (P.law clock) :=
  Analysis.Poisson.gradientPoissonInverse (P.law clock) (P.potential clock) (P.potential_C2 clock)
    (P.integrable clock clock.property) (P.gibbs_law clock clock.property)
    (P.lower clock) 1 (P.lower_pos clock clock.property)
    (P.hessian_lower clock clock.property)
    (by simpa only [one_mul] using P.hessian_upper clock clock.property)
    (gaussianAverage (P.law clock) f)

end SourcePhysicalPoissonDefinitions

/-- Disintegration specialized to the actual measurable Poisson coefficient.
Tonelli does not presuppose finiteness of the second moment. -/
theorem sourcePhysicalCoefficient_lintegral
    {ι : Type*} [fi : Fintype ι] [di : DecidableEq ι] {m : ℕ}
    {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2)
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)
    (G : _root_.AcceleratedLogConcave.Numerics.AffineGraph.MeanGeometry m) (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) (K : ℕ)
    (P : _root_.AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily
      (EuclideanSpace ℝ ι) 0 (1/2))
    (clock : ClockLaw.Clock)
    (f : Lp ℝ 2 (gaussianPhaseMeasure (P.law clock))) :
    let κ := physicalSourceSection (ι := ι) (fi := fi) (di := di) (m := m) (h := h) (hh := hh) (hhalf := hhalf) (V := V) (hV := hV) (hlo := hlo) (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := clock)
    let v := sourcePhysicalCoefficient P clock f
    (∫⁻ z, ENNReal.ofReal (((Real.sqrt 3/2) * inner ℝ (z.2-z.1.2) (v z.1.1.1))^2)
      ∂dormantJoint ((P.law clock).prod (stdGaussian (EuclideanSpace ℝ ι))) (stdGaussian (EuclideanSpace ℝ ι)) κ) =
      ∫⁻ parent, let d := physicalSourceData (ι := ι) (m := m) (h := h) (hh := hh) (hhalf := hhalf) (V := V) (hV := hV) (hlo := hlo) (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := clock) (parent := parent)
        ∫⁻ z, ENNReal.ofReal (((Real.sqrt 3/2) *
          inner ℝ (RetainedLaw.output d z-z.1.1) (v parent.1))^2)
          ∂RetainedLaw.averagedJoint d ∂(P.law clock).prod (stdGaussian (EuclideanSpace ℝ ι)) := by
  have hv : Measurable (sourcePhysicalCoefficient P clock f) :=
    (Lp.stronglyMeasurable _).measurable
  exact physicalSourceSection_dormant_lintegral (ι := ι) (fi := fi) (di := di) (m := m) (h := h) (hh := hh) (hhalf := hhalf) (V := V) (hV := hV) (hlo := hlo) (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := clock)
    (P.law clock) _ (by fun_prop)


/-- Literal root observable Jensen, including both closed clock endpoints.
This conclusion is not yet the numerical W12 estimate. -/
theorem sourcePhysicalCorrector_jensen
    {ι : Type*} [fi : Fintype ι] [di : DecidableEq ι] {m : ℕ}
    {h : ℝ} (hh : 0 < h) (hhalf : h ≤ 1/2)
    {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)
    (G : _root_.AcceleratedLogConcave.Numerics.AffineGraph.MeanGeometry m) (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) (K : ℕ)
    (P : _root_.AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily
      (EuclideanSpace ℝ ι) 0 (1/2))
    (clock : ClockLaw.Clock)
    (f : Lp ℝ 2 (gaussianPhaseMeasure (P.law clock))) :
    let κ := physicalSourceSection (ι := ι) (fi := fi) (di := di) (m := m) (h := h) (hh := hh) (hhalf := hhalf) (V := V) (hV := hV) (hlo := hlo) (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := clock)
    let hκ := physicalSourceSection_invariant (ι := ι) (fi := fi) (di := di) (m := m) (h := h) (hh := hh) (hhalf := hhalf) (V := V) (hV := hV) (hlo := hlo) (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := clock)
    let A := sourcePhysicalCorrector P clock
    ‖physicalDormantChannel (1/2) (Real.sqrt 3/2) source_split_coefficients
        (P.law clock) κ hκ (A.adjoint f)-A.adjoint f‖^2 ≤
      ∫ z, ((Real.sqrt 3/2) * inner ℝ (z.2-z.1.2)
        (sourcePhysicalCoefficient P clock f z.1.1.1))^2
        ∂dormantJoint ((P.law clock).prod (stdGaussian (EuclideanSpace ℝ ι))) (stdGaussian (EuclideanSpace ℝ ι)) κ := by
  exact Kinetic.DirectW12.physical_corrector_jensen (P.law clock)
    (1/2) (Real.sqrt 3/2) source_split_coefficients
    (physicalSourceSection (ι := ι) (fi := fi) (di := di) (m := m) (h := h) (hh := hh) (hhalf := hhalf) (V := V) (hV := hV) (hlo := hlo) (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := clock))
    (physicalSourceSection_invariant (ι := ι) (fi := fi) (di := di) (m := m) (h := h) (hh := hh) (hhalf := hhalf) (V := V) (hV := hV) (hlo := hlo) (hup := hup) (G := G) (hm := hm) (t := t) (ht := ht) (K := K) (P := P) (clock := clock))
    (P.potential clock) (P.potential_C2 clock)
    (P.integrable clock clock.property) (P.gibbs_law clock clock.property)
    (P.lower clock) 1 (P.lower_pos clock clock.property)
    (P.hessian_lower clock clock.property)
    (by simpa only [one_mul] using P.hessian_upper clock clock.property) f
end AcceleratedLogConcave.Root.RecursiveInnovation
