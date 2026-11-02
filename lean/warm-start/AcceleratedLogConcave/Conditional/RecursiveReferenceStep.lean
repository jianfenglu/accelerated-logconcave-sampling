import AcceleratedLogConcave.Conditional.TerminalChildrenParentFamilyJoint
import AcceleratedLogConcave.Conditional.RecursiveReferenceScalars

/-! The actual recursive parent operation on jointly measurable reference
families. The child family is evaluated at the source final centers, radius
`r R`, and width `R sqrt(3) sigma / 4`. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff ENNReal
namespace AcceleratedLogConcave.Conditional.RecursiveReference
open Numerics Numerics.MeanFlowLp Numerics.AffineGraph MeanReferenceLayer
open TerminalChildrenParentFamily
/-- A jointly measurable family with the section law needed by the source
parent operation. Instances below are constructed from the terminal kernel by
well-founded recursion. -/
structure Family (ι : Type*) [Fintype ι] (ell : ℝ) where
  kernel : Kernel (SourceParameters (EuclideanSpace ℝ ι) ell × EuclideanSpace ℝ ι)
    (EuclideanSpace ℝ ι)
  markov : IsMarkovKernel kernel
  invariant : ∀ theta, kernel.comap (fun p ↦ (theta,p)) measurable_prodMk_left ∘ₘ
    stdGaussian (EuclideanSpace ℝ ι) = stdGaussian (EuclideanSpace ℝ ι)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι
variable {F : EuclideanSpace ℝ ι → ℝ} {ell : ℝ} (hF : ContDiff ℝ 2 F) (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
  (G : MeanGeometry m) (hm : 0 < m)

abbrev Parameters := SourceParameters E ell
abbrev State := Parameters (ι := ι) (ell := ell) × Host ι m

/-- Literal terminal reference, retaining the designated original input. -/
def terminalFamily : Family ι ell where
  kernel := Kernel.deterministic Prod.snd measurable_snd
  markov := inferInstance
  invariant theta := by
    have he : (Kernel.deterministic Prod.snd measurable_snd :
        Kernel (Parameters (ι := ι) (ell := ell) × E) E).comap
        (fun p ↦ (theta,p)) measurable_prodMk_left = Kernel.id := by
      ext p : 1
      rfl
    rw [he]
    exact Measure.id_comp

/-- Actual common coefficients; no child or original input is resampled. -/
def sourceActive (z : State (ι := ι) (ell := ell) (m := m))
    (i : Option (Fin m)) : E :=
  GaussianAssembly.active (normalizedCoefficients G) z.2.1 z.2.2.2 i

/-- Full source centering path with the actual half parent width. -/
def sourcePhase (u : ℝ) (z : State (ι := ι) (ell := ell) (m := m)) : Centering.Phase E := by
  exact Centering.sourceCenteringFlow hF hell hlo hup z.1.center z.1.radius_pos
    G.backwardEnd_pos.le G.backwardEnd_lt_one z.1.small (half_pos z.1.width_pos)
    (WithLp.toLp 2 (z.2.2.1,sourceActive G z none)) u

omit [DecidableEq ι] in
theorem continuous_sourceActive (i : Option (Fin m)) :
    Continuous (fun z : State (ι := ι) (ell := ell) (m := m) ↦ sourceActive G z i) := by
  unfold sourceActive GaussianAssembly.active GaussianAssembly.noiseSum
  fun_prop

omit [DecidableEq ι] in
theorem continuous_sourcePhase (u : ℝ) :
    Continuous (fun z : State (ι := ι) (ell := ell) (m := m) ↦ sourcePhase hF hell hlo hup G u z) := by
  have hp : Continuous (fun z : State (ι := ι) (ell := ell) (m := m) ↦
      halfParameters z.1) := continuous_halfParameters.comp continuous_fst
  have hz : Continuous (fun z : State (ι := ι) (ell := ell) (m := m) ↦
      WithLp.toLp 2 (z.2.2.1,sourceActive G z none)) :=
    (WithLp.prod_continuous_toLp 2 E E).comp
      (continuous_snd.snd.fst.prodMk (continuous_sourceActive G none))
  have hc := (Centering.continuous_sourceCenteringFlow_parameters hF hell hlo hup
    G.backwardEnd_pos.le G.backwardEnd_lt_one).comp
      (hp.prodMk ((continuous_const : Continuous (fun _ : State (ι := ι) (ell := ell) (m := m) ↦ u)).prodMk hz))
  simpa only [Function.comp_def, sourcePhase, halfParameters, SourceParameters.center,
    SourceParameters.radius, SourceParameters.width] using hc

/-- Literal final query center of the actual parent path. -/
def sourceChildCenter (i : Fin m) (z : State (ι := ι) (ell := ell) (m := m)) : E :=
  z.1.center + (z.1.radius * backwardEnd G.R) •
    (sourcePhase hF hell hlo hup G (GaussLegendre.node m i) z).fst

omit [DecidableEq ι] in
theorem continuous_sourceChildCenter (i : Fin m) :
    Continuous (sourceChildCenter hF hell hlo hup G i) := by
  unfold sourceChildCenter
  exact (SourceParameters.continuous_center.comp continuous_fst).add
    (((SourceParameters.continuous_radius.comp continuous_fst).mul continuous_const).smul
      ((WithLp.prod_continuous_ofLp 2 E E).fst.comp
        (continuous_sourcePhase hF hell hlo hup G _)))

/-- Actual child references, at their original designated inputs. -/
def sourceRecombine (z : State (ι := ι) (ell := ell) (m := m)) (p' : Fin m → E) : E :=
  z.2.1 + (1 / 2 : ℝ) • ((sourcePhase hF hell hlo hup G 1 z).snd-sourceActive G z none) +
    ∑ i, normalizedCoefficients G (some i) • (p' i-sourceActive G z (some i))

omit [DecidableEq ι] in
theorem continuous_sourceRecombine :
    Continuous (fun z : State (ι := ι) (ell := ell) (m := m) × (Fin m → E) ↦
      sourceRecombine hF hell hlo hup G z.1 z.2) := by
  unfold sourceRecombine
  exact ((continuous_fst.snd.fst.add
    ((((WithLp.prod_continuous_ofLp 2 E E).snd.comp
      ((continuous_sourcePhase hF hell hlo hup G 1).comp continuous_fst)).sub
        ((continuous_sourceActive G none).comp continuous_fst)).const_smul (1 / 2 : ℝ))).add
    (continuous_finsetSum _ fun i _ ↦
      (((continuous_apply i).comp continuous_snd).sub
        ((continuous_sourceActive G (some i)).comp continuous_fst)).const_smul
          (normalizedCoefficients G (some i))))


/-- Actual source parent children obtained from a lower precision family. -/
def sourceChildren (C : Family ι ell) (theta : Parameters (ι := ι) (ell := ell)) :
    Children (data hF hell hlo hup G theta) where
  scale _ := childScale (data hF hell hlo hup G theta)
  scale_pos _ := childScale_pos _
  beta := beta (data hF hell hlo hup G theta)
  beta_pos := beta_pos _ hm
  budget := source_budget _ hm
  kernel _ := C.kernel.comap (fun z : E × E ↦ (childParameters hell G theta z.1,z.2))
    (((continuous_childParameters hell G).comp (continuous_const.prodMk continuous_fst)).prodMk
      continuous_snd).measurable
  markov _ := by let := C.markov; infer_instance
  invariant _ y := C.invariant (childParameters hell G theta y)

omit [DecidableEq ι] in
theorem coefficients_sourceChildren (C : Family ι ell)
    (theta : Parameters (ι := ι) (ell := ell)) :
    coefficients (data hF hell hlo hup G theta)
      (sourceChildren hF hell hlo hup G hm C theta) = normalizedCoefficients G :=
  coefficients_eq_normalized _ hm

/-- Jointly measurable finite independent child product. -/
def stepChild (C : Family ι ell) (i : Fin m) :
    Kernel (State (ι := ι) (ell := ell) (m := m)) E :=
  C.kernel.comap
    (fun z ↦ (childParameters hell G z.1 (sourceChildCenter hF hell hlo hup G i z),
      sourceActive G z (some i)))
    ((((continuous_childParameters hell G).comp
      (continuous_fst.prodMk (continuous_sourceChildCenter hF hell hlo hup G i))).prodMk
      (continuous_sourceActive G (some i))).measurable)

instance stepChild_markov (C : Family ι ell) (i : Fin m) :
    IsMarkovKernel (stepChild hF hell hlo hup G C i) := by
  let := C.markov
  unfold stepChild
  infer_instance

def stepChildren (C : Family ι ell) :
    Kernel (State (ι := ι) (ell := ell) (m := m)) (Fin m → E) :=
  finiteProduct m (stepChild hF hell hlo hup G C)

instance stepChildren_markov (C : Family ι ell) :
    IsMarkovKernel (stepChildren hF hell hlo hup G C) :=
  finiteProduct_markov m _ (fun _ ↦ inferInstance)

/-- Draw the actual source position and independent auxiliary Gaussian array,
while storing both the source parameters and the original parent input. -/
def stepHost : Kernel (Parameters (ι := ι) (ell := ell) × E)
    (State (ι := ι) (ell := ell) (m := m)) :=
  ((Kernel.id : Kernel (Parameters (ι := ι) (ell := ell) × E)
    (Parameters (ι := ι) (ell := ell) × E)) ×ₖ familyFreshKernel hF hlo G).map
      (fun z ↦ (z.1.1,(z.1.2,z.2)))

instance stepHost_markov : IsMarkovKernel (stepHost (ell := ell) hF hlo G) :=
  Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- Parent update after drawing each child independently at the actual source
center and the designated retained input. -/
def stepUpdate (C : Family ι ell) : Kernel (State (ι := ι) (ell := ell) (m := m)) E :=
  ((Kernel.id : Kernel (State (ι := ι) (ell := ell) (m := m))
      (State (ι := ι) (ell := ell) (m := m))) ×ₖ stepChildren hF hell hlo hup G C).map
    (fun z ↦ sourceRecombine hF hell hlo hup G z.1 z.2)

instance stepUpdate_markov (C : Family ι ell) :
    IsMarkovKernel (stepUpdate hF hell hlo hup G C) :=
  Kernel.IsMarkovKernel.map _ (continuous_sourceRecombine hF hell hlo hup G).measurable

def stepKernel (C : Family ι ell) : Kernel (Parameters (ι := ι) (ell := ell) × E) E :=
  stepUpdate hF hell hlo hup G C ∘ₖ stepHost hF hlo G

instance stepKernel_markov (C : Family ι ell) :
    IsMarkovKernel (stepKernel hF hell hlo hup G C) := by
  unfold stepKernel
  infer_instance


/-- The joint source path is the very same path used by the fixed parent. -/
theorem sourcePhase_eq (C : Family ι ell)
    (theta : Parameters (ι := ι) (ell := ell)) (u : ℝ) (h : Host ι m) :
    sourcePhase hF hell hlo hup G u (theta,h) =
      phase (data hF hell hlo hup G theta) (sourceChildren hF hell hlo hup G hm C theta) u h := by
  unfold MeanReferenceLayer.phase active
  rw [coefficients_sourceChildren]
  rfl

theorem sourceChildCenter_eq (C : Family ι ell)
    (theta : Parameters (ι := ι) (ell := ell)) (i : Fin m) (h : Host ι m) :
    sourceChildCenter hF hell hlo hup G i (theta,h) =
      childCenter (data hF hell hlo hup G theta) (sourceChildren hF hell hlo hup G hm C theta) i h := by
  unfold sourceChildCenter childCenter
  rw [sourcePhase_eq hF hell hlo hup G hm C]
  rfl

omit [DecidableEq ι] in
theorem sourceActive_eq (C : Family ι ell)
    (theta : Parameters (ι := ι) (ell := ell)) (i : Option (Fin m)) (h : Host ι m) :
    sourceActive G (theta,h) i =
      active (data hF hell hlo hup G theta) (sourceChildren hF hell hlo hup G hm C theta) h i := by
  unfold active
  rw [coefficients_sourceChildren]
  rfl

/-- The retained source formula equals the literal normalized parent assembly
at every original input, before taking any law. -/
theorem sourceRecombine_eq (C : Family ι ell)
    (theta : Parameters (ι := ι) (ell := ell)) (h : Host ι m) (p' : Fin m → E) :
    sourceRecombine hF hell hlo hup G (theta,h) p' =
      recombine (data hF hell hlo hup G theta)
        (sourceChildren hF hell hlo hup G hm C theta) h p' := by
  let d := data hF hell hlo hup G theta
  let c := sourceChildren hF hell hlo hup G hm C theta
  have hd := displacement_target d c h p'
  apply (smul_right_injective E theta.width_pos.ne')
  dsimp only
  rw [sourceRecombine]
  rw [smul_add,smul_add,smul_smul]
  have hp := sourcePhase_eq hF hell hlo hup G hm C theta 1 h
  have ha := sourceActive_eq hF hell hlo hup G hm C theta none h
  simp only [hp,ha]
  simp only [d,c] at hd
  have hs : theta.width * (1 / 2 : ℝ) = theta.width / 2 := by ring
  rw [hs]
  rw [Finset.smul_sum]
  simp_rw [smul_smul]
  have hc (i : Fin m) : theta.width * normalizedCoefficients G (some i) =
      GaussLegendre.weight m i * childScale d := by
    dsimp [normalizedCoefficients, childScale, d, data]
    ring
  simp_rw [hc, sourceActive_eq hF hell hlo hup G hm C theta]
  rw [smul_sub] at hd
  have hh := eq_add_of_sub_eq hd
  dsimp only [d,data,sourceChildren] at hh ⊢
  rw [hh]
  abel


theorem stepChildren_at (C : Family ι ell)
    (theta : Parameters (ι := ι) (ell := ell)) (h : Host ι m) :
    stepChildren hF hell hlo hup G C (theta,h) =
      childrenKernel (data hF hell hlo hup G theta)
        (sourceChildren hF hell hlo hup G hm C theta) h := by
  rw [stepChildren,finiteProduct_apply m _ (fun _ ↦ inferInstance),
    childrenKernel,finiteProduct_apply m _ (fun _ ↦ inferInstance)]
  congr 1
  funext i
  rw [stepChild,childKernel,Kernel.comap_apply,Kernel.comap_apply]
  change C.kernel _ = C.kernel _
  rw [sourceChildCenter_eq hF hell hlo hup G hm C,
    sourceActive_eq hF hell hlo hup G hm C]

theorem stepUpdate_at (C : Family ι ell)
    (theta : Parameters (ι := ι) (ell := ell)) (h : Host ι m) :
    stepUpdate hF hell hlo hup G C (theta,h) =
      (((Kernel.id : Kernel (Host ι m) (Host ι m)) ×ₖ
        childrenKernel (data hF hell hlo hup G theta)
          (sourceChildren hF hell hlo hup G hm C theta)).map
        (fun z ↦ recombine (data hF hell hlo hup G theta)
          (sourceChildren hF hell hlo hup G hm C theta) z.1 z.2)) h := by
  rw [stepUpdate,Kernel.map_apply _ (continuous_sourceRecombine hF hell hlo hup G).measurable,
    Kernel.prod_apply,Kernel.id_apply,stepChildren_at hF hell hlo hup G hm C,
    Kernel.map_apply _ (continuous_recombine _ _).measurable,
    Kernel.prod_apply,Kernel.id_apply,Measure.dirac_prod,Measure.dirac_prod,
    Measure.map_map (continuous_sourceRecombine hF hell hlo hup G).measurable measurable_prodMk_left,
    Measure.map_map (continuous_recombine _ _).measurable measurable_prodMk_left]
  congr 1
  funext p'
  exact sourceRecombine_eq hF hell hlo hup G hm C theta h p'

omit [DecidableEq ι] in
theorem stepHost_apply (theta : Parameters (ι := ι) (ell := ell)) (p : E) :
    stepHost hF hlo G (theta,p) =
      (freshKernel (data hF hell hlo hup G theta) p).map (fun h ↦ (theta,h)) := by
  rw [stepHost, Kernel.map_apply _ (by fun_prop),Kernel.prod_apply,Kernel.id_apply,
    familyFreshKernel_apply hF hell hlo hup G,Measure.dirac_prod,
    Measure.map_map (by fun_prop) measurable_prodMk_left,
    freshKernel,Kernel.prod_apply,Kernel.id_apply,Kernel.const_apply,Measure.dirac_prod,
    Measure.map_map measurable_prodMk_left measurable_prodMk_left]
  rfl

/-- Every fixed-parameter section equals the literal source parent assembled
from the actual lower precision references. This is equality at every retained
input, not merely equality after Gaussian averaging. -/
theorem stepKernel_section (C : Family ι ell)
    (theta : Parameters (ι := ι) (ell := ell)) :
    (stepKernel hF hell hlo hup G C).comap (fun p ↦ (theta,p)) measurable_prodMk_left =
      parentKernel (data hF hell hlo hup G theta)
        (sourceChildren hF hell hlo hup G hm C theta) := by
  rw [parentKernel,jointKernel,Kernel.map_comp]
  ext p s hs
  rw [Kernel.comap_apply,stepKernel,Kernel.comp_apply' _ _ _ hs,
    Kernel.comp_apply' _ _ _ hs,stepHost_apply hF hell hlo hup G,
    MeasureTheory.lintegral_map
      ((stepUpdate hF hell hlo hup G C).measurable_coe hs) measurable_prodMk_left]
  apply lintegral_congr
  intro h
  exact congrArg (fun μ : Measure E ↦ μ s) (stepUpdate_at hF hell hlo hup G hm C theta h)

include hm in
/-- Source Gaussian stationarity follows from the actual fixed-parent theorem. -/
theorem stepKernel_invariant (C : Family ι ell)
    (theta : Parameters (ι := ι) (ell := ell)) :
    (stepKernel hF hell hlo hup G C).comap (fun p ↦ (theta,p)) measurable_prodMk_left ∘ₘ
      stdGaussian E = stdGaussian E := by
  rw [stepKernel_section hF hell hlo hup G hm C theta]
  exact parentKernel_invariant _ _

/-- One actual recursive source-parent operation. -/
def parentFamily (C : Family ι ell) : Family ι ell where
  kernel := stepKernel hF hell hlo hup G C
  markov := inferInstance
  invariant := stepKernel_invariant hF hell hlo hup G hm C

end AcceleratedLogConcave.Conditional.RecursiveReference
