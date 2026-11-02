import AcceleratedLogConcave.Root.FlowClock
import AcceleratedLogConcave.Root.ClockSchedule

/-! Joint clock-family supplier at the actual inverse-flow GL centers.
The supplied lower-level children are prescribed exact reference kernels on the
same fixed finite inventory. This is not a compiler identification or W12 bound. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open AcceleratedLogConcave.Kinetic AcceleratedLogConcave.Analysis.Poisson
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace AcceleratedLogConcave.Root.ClockBackwardKernel
abbrev Clock := ClockLaw.Clock
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

section ActualCenters
variable (F : AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily (EuclideanSpace ℝ ι) 0 (1/2))
  (ell : ℝ) (J m : ℕ) (hJ : 0 < J)

/-- Exact earlier physical center on the SAME parent trajectory recovered from its terminal pair. -/
def center (i : Fin (J*m)) (z : Clock × (E × E)) : E :=
  BackwardParentLaw.backwardCenter F ell z.1 (ClockSchedule.node J m hJ z.1 i) z.2

/-- Proved from actual joint forward/inverse-flow continuity and actual GL nodes. -/
theorem continuous_center (i : Fin (J*m)) : Continuous (center F ell J m hJ i) :=
  ((FlowClock.referencePair_joint_continuous F ell).comp
    (((ClockSchedule.continuous_node J m hJ i).comp continuous_fst).prodMk
      (FlowClock.referencePair_symm_joint_continuous F ell))).fst

/-- Joint clock/parent measurability is a conclusion, not an arbitrary-center premise. -/
theorem measurable_center (i : Fin (J*m)) : Measurable (center F ell J m hJ i) :=
  (continuous_center F ell J m hJ i).measurable

/-- Literal same-path source identification at every fixed clock. -/
theorem center_forward (i : Fin (J*m)) (t : Clock) (z : E × E) :
    center F ell J m hJ i (t, referenceCoupledPairFlow F ell t z) =
      (referenceCoupledPairFlow F ell (ClockSchedule.node J m hJ t i) z).1 :=
  congrArg Prod.fst (BackwardParentLaw.backwardPair_forward F ell t _ z)
end ActualCenters

/-- Open LOWER-LEVEL supplier: a jointly measurable family of prescribed recursive
exact child kernels on the fixed J*m slots. Each kernel's labels/radius/width/tree
must be the actual source ones. Root invariance and the W12 norm are not fields. -/
structure Children (ι : Type*) [Fintype ι] (J m : ℕ) where
  kernel : Fin (J*m) → Kernel ((Clock × EuclideanSpace ℝ ι) × EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι)
  markov : ∀ i, IsMarkovKernel (kernel i)
  invariant : ∀ i t c,
    (kernel i).comap (fun p => ((t,c),p)) measurable_prodMk_left ∘ₘ stdGaussian (EuclideanSpace ℝ ι) =
      stdGaussian (EuclideanSpace ℝ ι)

section Kernel
variable (F : AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily (EuclideanSpace ℝ ι) 0 (1/2))
  (ell : ℝ) (J m : ℕ) (hJ : 0 < J) (hm : 0 < m) (scale : ℝ) (C : Children ι J m)

/-- Real schedule and exact backward centers form the ClockLaw data. The scaling is
constant, and is instantiated below to 1/sqrt(h), not an arbitrary center function. -/
def data : ClockLaw.Data ι (J*m) where
  weight z := ClockSchedule.weight J m z.1
  measurable_weight := (ClockSchedule.measurable_weight J m).comp measurable_fst
  admissible z := ClockSchedule.admissible J m hJ hm z.1
  child i := (C.kernel i).comap
    (fun z => ((z.1.1, scale • center F ell J m hJ i z.1), z.2))
    ((measurable_fst.fst.prodMk ((measurable_center F ell J m hJ i).comp measurable_fst |>.const_smul scale)).prodMk measurable_snd)
  markov i := by let := C.markov i; infer_instance
  invariant i z := by
    have hi := C.invariant i z.1 (scale • center F ell J m hJ i z)
    exact hi

/-- Concrete all-clock kernel with the exact downstream clock/phase domain. -/
def kernel : Kernel (Clock × GaussianPhase E) E :=
  ClockLaw.kernel (data F ell J m hJ hm scale C)
instance kernel_markov : IsMarkovKernel (kernel F ell J m hJ hm scale C) := by
  unfold kernel
  infer_instance

/-- Every clock section has the required conditional invariance, derived from child invariance. -/
theorem section_conditionallyInvariant (t : Clock) :
    ∀ x s, MeasurableSet s →
      (∫⁻ h, (kernel F ell J m hJ hm scale C) (t,(x,h)) s ∂stdGaussian E) = stdGaussian E s :=
  ClockLaw.section_conditionallyInvariant (data F ell J m hJ hm scale C) t

/-- Fixed-clock child written in the physical-center convention of BackwardParentLaw. -/
def physicalChild (t : Clock) (i : Fin (J*m)) : Kernel (E × E) E :=
  (C.kernel i).comap (fun z => ((t, scale • z.1), z.2))
    ((measurable_const.prodMk (measurable_fst.const_smul scale)).prodMk measurable_snd)
instance physicalChild_markov (t : Clock) (i : Fin (J*m)) :
    IsMarkovKernel (physicalChild J m scale C t i) := by
  let := C.markov i
  unfold physicalChild
  infer_instance
lemma physicalChild_invariant (t : Clock) (i : Fin (J*m)) (c : E) :
    (physicalChild J m scale C t i).comap (fun p => (c,p)) measurable_prodMk_left ∘ₘ
      stdGaussian E = stdGaussian E := C.invariant i t (scale • c)

/-- Freeze the actual node schedule without changing any child index or precision tree. -/
def fixedData (t : Clock) : ConditionalLaw.Data (E × E) ι (J*m) :=
  BackwardParentLaw.backwardData F ell t (ClockSchedule.node J m hJ t)
    (ClockSchedule.weight J m t) (ClockSchedule.admissible J m hJ hm t)
    (physicalChild J m scale C t) (fun _ => inferInstance) (physicalChild_invariant J m scale C t)

/-- The all-clock family has EXACTLY the previously proved fixed-clock retained construction. -/
theorem atParent_eq (t : Clock) (b : E × E) :
    ConditionalLaw.atParent (data F ell J m hJ hm scale C) (t,b) =
      ConditionalLaw.atParent (fixedData F ell J m hJ hm scale C t) b := rfl

/-- Kernel equality, not just equality of output marginals. -/
theorem kernel_section_apply (t : Clock) (b : E × E) (h : E) :
    kernel F ell J m hJ hm scale C (t,(b,h)) =
      ConditionalLaw.rootKernel (fixedData F ell J m hJ hm scale C t) (b,h) := by
  have hl := congrArg (fun k : Kernel E E => k h)
    (ConditionalLaw.rootKernel_section (data F ell J m hJ hm scale C) (t,b))
  have hr := congrArg (fun k : Kernel E E => k h)
    (ConditionalLaw.rootKernel_section (fixedData F ell J m hJ hm scale C t) b)
  rw [atParent_eq] at hl
  exact hl.trans hr.symm
end Kernel

section Source
variable (F : AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily (EuclideanSpace ℝ ι) 0 (1/2))

def sourceRadius (h : ℝ) (hh : 0 < h) (K : ℕ) (i : Fin (ClockSchedule.sourceCells h * ClockSchedule.sourceOrder K))
    (t : Clock) : ℝ :=
  Real.sqrt (2*h) * Real.sqrt (1 - (ClockSchedule.node (ClockSchedule.sourceCells h)
    (ClockSchedule.sourceOrder K) (ClockSchedule.sourceCells_pos hh) t i : ℝ)^2)

/-- Exact compact range of the source mean-child radii; no unrequested all-radius extension. -/
abbrev RadiusBand (h : ℝ) := Icc (Real.sqrt 3 / 2 * Real.sqrt (2*h)) (Real.sqrt (2*h))

lemma continuous_sourceRadius (h : ℝ) (hh : 0 < h) (K : ℕ)
    (i : Fin (ClockSchedule.sourceCells h * ClockSchedule.sourceOrder K)) :
    Continuous (sourceRadius h hh K i) := by
  have hu := (ClockSchedule.continuous_node (ClockSchedule.sourceCells h)
    (ClockSchedule.sourceOrder K) (ClockSchedule.sourceCells_pos hh) i).subtype_val
  unfold sourceRadius
  exact continuous_const.mul ((continuous_const.sub (hu.pow 2)).sqrt)

lemma sourceRadius_mem (h : ℝ) (hh : 0 < h) (K : ℕ)
    (i : Fin (ClockSchedule.sourceCells h * ClockSchedule.sourceOrder K)) (t : Clock) :
    sourceRadius h hh K i t ∈ RadiusBand h := by
  let u := ClockSchedule.node (ClockSchedule.sourceCells h) (ClockSchedule.sourceOrder K)
    (ClockSchedule.sourceCells_pos hh) t i
  have hu0 : (0 : ℝ) ≤ u := u.2.1
  have hu1 : (u : ℝ) ≤ 1/2 := u.2.2
  have hv : 0 ≤ 1-(u : ℝ)^2 := by nlinarith
  have hs := Real.sq_sqrt hv
  have hs0 := Real.sqrt_nonneg (1-(u : ℝ)^2)
  have ht := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have ht0 := Real.sqrt_nonneg 3
  have hlo : Real.sqrt 3 / 2 ≤ Real.sqrt (1-(u : ℝ)^2) := by nlinarith
  have hup : Real.sqrt (1-(u : ℝ)^2) ≤ 1 := by nlinarith [sq_nonneg (u : ℝ)]
  have hr := Real.sqrt_nonneg (2*h)
  constructor
  · change Real.sqrt 3 / 2 * Real.sqrt (2*h) ≤ Real.sqrt (2*h) * Real.sqrt (1-(u : ℝ)^2)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hlo hr
  · change Real.sqrt (2*h) * Real.sqrt (1-(u : ℝ)^2) ≤ Real.sqrt (2*h)
    exact mul_le_of_le_one_right hr hup

def radiusParameter (h : ℝ) (hh : 0 < h) (K : ℕ)
    (i : Fin (ClockSchedule.sourceCells h * ClockSchedule.sourceOrder K)) (t : Clock) : RadiusBand h :=
  ⟨sourceRadius h hh K i t, sourceRadius_mem h hh K i t⟩

lemma continuous_radiusParameter (h : ℝ) (hh : 0 < h) (K : ℕ)
    (i : Fin (ClockSchedule.sourceCells h * ClockSchedule.sourceOrder K)) :
    Continuous (radiusParameter h hh K i) :=
  (continuous_sourceRadius h hh K i).subtype_mk _

def sourceWidth (h : ℝ) : ℝ := (Real.sqrt 3/2) / ((1/2)*Real.sqrt (2*h))

/-- The literal manuscript cell/order counts, physical scale sqrt(2h²), and mean-center
rescaling 1/sqrt(h), all fixed before the stopping endpoint. The recursive children
must still be supplied at sourceRadius/sourceWidth and their unchanged precision-K trees. -/
def sourceKernel (h : ℝ) (hh : 0 < h) (K : ℕ)
    (C : Children ι (ClockSchedule.sourceCells h) (ClockSchedule.sourceOrder K)) :
    Kernel (Clock × GaussianPhase E) E :=
  kernel F (Real.sqrt (2*h^2)) _ _ (ClockSchedule.sourceCells_pos hh)
    (ClockSchedule.sourceOrder_pos K) (Real.sqrt h)⁻¹ C

instance sourceKernel_markov (h : ℝ) (hh : 0 < h) (K : ℕ)
    (C : Children ι (ClockSchedule.sourceCells h) (ClockSchedule.sourceOrder K)) :
    IsMarkovKernel (sourceKernel F h hh K C) := by unfold sourceKernel; infer_instance
/-- Precise remaining kernel producer: the prescribed finite-tree child at fixed
source width/precision, jointly measurable in its radius on the TRUE compact band
and in its mean-coordinate center. Tree/slot labels are retained separately for each i.
This record is an OPEN lower-level interface, not a constructed recursive sampler. -/
structure RadiusChildren (ι : Type*) [Fintype ι] (h : ℝ) (K : ℕ) where
  kernel : Fin (ClockSchedule.sourceCells h * ClockSchedule.sourceOrder K) →
    Kernel ((RadiusBand h × EuclideanSpace ℝ ι) × EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι)
  markov : ∀ i, IsMarkovKernel (kernel i)
  invariant : ∀ i r c,
    (kernel i).comap (fun p => ((r,c),p)) measurable_prodMk_left ∘ₘ stdGaussian (EuclideanSpace ℝ ι) =
      stdGaussian (EuclideanSpace ℝ ι)

/-- No arbitrary clock measurability is assumed: it is pulled back along the proved
source radius schedule. Every original finite child slot is preserved. -/
def sourceClockChildren (h : ℝ) (hh : 0 < h) (K : ℕ) (D : RadiusChildren ι h K) :
    Children ι (ClockSchedule.sourceCells h) (ClockSchedule.sourceOrder K) where
  kernel i := (D.kernel i).comap
    (fun z => ((radiusParameter h hh K i z.1.1,z.1.2),z.2))
    ((((continuous_radiusParameter h hh K i).measurable.comp measurable_fst.fst).prodMk
      measurable_fst.snd).prodMk measurable_snd)
  markov i := by let := D.markov i; infer_instance
  invariant i t c := D.invariant i (radiusParameter h hh K i t) c

/-- Source-specialized all-clock kernel, conditional only on the explicit unresolved
radius/center measurable recursive child family. -/
def sourceKernelFromRadiusFamily (h : ℝ) (hh : 0 < h) (K : ℕ) (D : RadiusChildren ι h K) :
    Kernel (Clock × GaussianPhase E) E := sourceKernel F h hh K (sourceClockChildren h hh K D)

instance sourceKernelFromRadiusFamily_markov (h : ℝ) (hh : 0 < h) (K : ℕ)
    (D : RadiusChildren ι h K) : IsMarkovKernel (sourceKernelFromRadiusFamily F h hh K D) := by
  unfold sourceKernelFromRadiusFamily
  infer_instance

theorem sourceKernelFromRadiusFamily_conditionallyInvariant (h : ℝ) (hh : 0 < h) (K : ℕ)
    (D : RadiusChildren ι h K) (t : Clock) :
    ∀ x s, MeasurableSet s →
      (∫⁻ q, sourceKernelFromRadiusFamily F h hh K D (t,(x,q)) s ∂stdGaussian E) = stdGaussian E s :=
  section_conditionallyInvariant F _ _ _ _ _ _ _ t
end Source
end AcceleratedLogConcave.Root.ClockBackwardKernel
