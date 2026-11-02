import AcceleratedLogConcave.Oracle.MeanIncomingPrivateCoupling
import AcceleratedLogConcave.Oracle.MeanCompletedAugmentedLaws
import AcceleratedLogConcave.Oracle.MeanPrivateReferenceBridge
import Mathlib.Probability.ProductMeasure

/-! Joint deterministic Gaussian assembly and actual scaled private anchor.
The original P is used in the assembly; the reserve is retained for its exact
reconstruction. The full conditional-flow seed inventory is retained. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.MeanIncomingAssemblyLaw
open Numerics Numerics.AffineGraph SourceMeanExecutable
open Conditional.GaussianAssembly
open AcceleratedLogConcave.Probability.MixedResidualAbsorption

private theorem swapMiddle {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μa : Measure A) (μb : Measure B) (μc : Measure C) [SFinite μa] [SFinite μb] [SFinite μc] :
    MeasurePreserving (fun z : A × (B × C) => (z.2.1,(z.1,z.2.2)))
      (μa.prod (μb.prod μc)) (μb.prod (μa.prod μc)) :=
  (measurePreserving_prodAssoc μb μa μc).comp
    (((Measure.measurePreserving_swap (μ := μa) (ν := μb)).prod (MeasurePreserving.id μc)).comp
      (measurePreserving_prodAssoc μa μb μc).symm)

private theorem cross {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μa : Measure A) (μb : Measure B) (μc : Measure C) (μd : Measure D)
    [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (fun z : (A × B) × (C × D) => ((z.1.1,z.2.1),(z.1.2,z.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μb.prod μd)) :=
  (measurePreserving_prodAssoc μa μc (μb.prod μd)).symm.comp
    (((MeasurePreserving.id μa).prod (swapMiddle μb μc μd)).comp
      (measurePreserving_prodAssoc μa μb (μc.prod μd)))

private theorem regroup {A B C D E : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace E]
    (μa : Measure A) (μb : Measure B) (μc : Measure C) (μd : Measure D) (μe : Measure E)
    [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] [SFinite μe] :
    MeasurePreserving (fun z : (A × (B × C)) × (D × E) =>
      ((z.1.1,((z.2.1,z.1.2.1),z.2.2)),z.1.2.2))
      ((μa.prod (μb.prod μc)).prod (μd.prod μe))
      ((μa.prod ((μd.prod μb).prod μe)).prod μc) := by
  have h0 := (measurePreserving_prodAssoc μa (μb.prod μc) (μd.prod μe))
  have h1 := ((MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μb μc (μd.prod μe))).comp h0
  have h2 := ((MeasurePreserving.id μa).prod
    ((MeasurePreserving.id μb).prod (swapMiddle μc μd μe))).comp h1
  have h3 := ((MeasurePreserving.id μa).prod (swapMiddle μb μd (μc.prod μe))).comp h2
  have h4 := ((MeasurePreserving.id μa).prod ((MeasurePreserving.id μd).prod
    ((MeasurePreserving.id μb).prod (Measure.measurePreserving_swap (μ := μc) (ν := μe))))).comp h3
  have h5 := ((MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μd μb (μe.prod μc)).symm).comp h4
  have h6 := ((MeasurePreserving.id μa).prod (measurePreserving_prodAssoc (μd.prod μb) μe μc).symm).comp h5
  exact (measurePreserving_prodAssoc μa ((μd.prod μb).prod μe) μc).symm.comp h6

variable {m h d : ℕ} (M : MeanGeometry m) (seeds : Fin h ≃ Fin m × M.Kernel)
local notation "γ" => stdGaussian (Point d)

/-- The same literal Gaussian assembly, with reserve and every active input. -/
theorem assembly_preserving : MeasurePreserving
    (fun z : Point d × (Fin (m+1) → Point d) =>
      (residual (assembly M) z.1 z.2,
        (active (assembly M) z.1 z.2 0,fun i : Fin m => active (assembly M) z.1 z.2 i.succ)))
    ((γ).prod (Measure.pi fun _ : Fin (m+1) => γ))
    ((γ).prod ((γ).prod (Measure.pi fun _ : Fin m => γ))) := by
  let e := MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin (m+1)) => Point d)
  have he : MeasurePreserving e
      (Measure.pi fun _ : Option (Fin (m+1)) => γ)
      ((Measure.pi fun _ : Fin (m+1) => γ).prod γ) :=
    (show MeasurePreserving e.symm _ _ from ⟨e.symm.measurable,Measure.pi_map_piOptionEquivProd _⟩).symm
  have ha : MeasurePreserving (assemble (assembly M) : (Option (Fin (m+1)) → Point d) → _)
      (Measure.pi fun _ : Option (Fin (m+1)) => γ) (Measure.pi fun _ : Option (Fin (m+1)) => γ) :=
    ⟨measurable_assemble _,assemble_map_pi (MeanAssemblyJointLaw.assembly_mass M)⟩
  have hp := (Measure.measurePreserving_swap (μ := Measure.pi fun _ : Fin (m+1) => γ) (ν := γ)).comp
    (he.comp (ha.comp comparisonPack_preserving))
  have hs := (MeasurePreserving.id γ).prod (measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => γ) 0)
  convert hs.comp hp using 1
  funext z
  simp only [e,MeasurableEquiv.piOptionEquivProd,MeasurableEquiv.piFinSuccAbove,
    Fin.succAbove_zero]
  rfl

/-- Literal enumeration of all flow seeds, with its full nested product law. -/
theorem flow_preserving : MeasurePreserving
    (fun z : Fin h → Point d => fun j k => z (seeds.symm (j,k)))
    (Measure.pi fun _ : Fin h => γ)
    (Measure.pi fun _ : Fin m => Measure.pi fun _ : M.Kernel => γ) := by
  have hr := measurePreserving_piCongrLeft (fun _ : Fin m × M.Kernel => γ) seeds
  have hc : MeasurePreserving (MeasurableEquiv.curry (Fin m) M.Kernel (Point d))
      (Measure.pi fun _ : Fin m × M.Kernel => γ)
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : M.Kernel => γ) := by
    refine ⟨MeasurableEquiv.measurable _,?_⟩
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_curry (fun _ : Fin m => fun _ : M.Kernel => γ))
  convert hc.comp hr using 1
  funext z j k
  simp only [Function.comp_apply,MeasurableEquiv.curry_apply,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
  apply eq_of_heq
  symm
  exact eqRec_heq_iff.mpr HEq.rfl

variable {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (r σ : ℝ) (hr : 0<r) (hσ : 0<σ) (hsmall : r^2*ell≤1/2) (base : Point d)

/-- Exact reserved assembly coordinate, physical phase seed and active Pi
inventory, all computed from the same P/private-reference/raw/flow sample. -/
def assembledInventory (z : (Point d × Point d) × ((Fin (m+1) → Point d) × (Fin h → Point d))) :
    (Point d × MeanFlowLp.Seed (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)) ×
      (Fin m → Point d) :=
  ((residual (assembly M) z.1.1 z.2.1,
    ((WithLp.toLp 2 (backwardEnd M.R • z.1.2,active (assembly M) z.1.1 z.2.1 0)),
      fun j k => z.2.2 (seeds.symm (j,k)))),
    fun i => active (assembly M) z.1.1 z.2.1 i.succ)

/-- Actual private forward-reference law plus original independent Gaussian
inventories gives the full incoming GE/phase/Pi law required by chronology.
The position scaling is the literal backwardEnd R prefix multiplication. -/
theorem assembledInventory_preserving : MeasurePreserving
    (assembledInventory M seeds hF hell hlo hup r σ hr hσ hsmall base)
    (((γ).prod (Channels.forward (Conditional.baseLaw F base r)
      ⟨(M.R/backwardEnd M.R)^2,by positivity⟩)).prod
      ((Measure.pi fun _ : Fin (m+1) => γ).prod (Measure.pi fun _ : Fin h => γ)))
    (((γ).prod (MeanFlowLp.seedMeasure (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base))).prod
      (Measure.pi fun _ : Fin m => γ)) := by
  let ν := Channels.forward (Conditional.baseLaw F base r)
    ⟨(M.R/backwardEnd M.R)^2,by positivity⟩
  let μ := Conditional.interpolationLaw F base r (backwardEnd M.R)
  let : IsProbabilityMeasure (Conditional.baseLaw F base r) :=
    Conditional.baseLaw_isProbabilityMeasure hF hlo base r
  let : IsProbabilityMeasure ν := by dsimp [ν,Channels.forward]; infer_instance
  let : IsProbabilityMeasure μ := Conditional.interpolationLaw_isProbabilityMeasure hF hlo base r _
  let rawLaw := Measure.pi fun _ : Fin (m+1) => γ
  let piLaw := Measure.pi fun _ : Fin m => γ
  let flatLaw := Measure.pi fun _ : Fin h => γ
  let flowLaw := Measure.pi fun _ : Fin m => Measure.pi fun _ : M.Kernel => γ
  have hscale : MeasurePreserving (fun y : Point d => backwardEnd M.R • y) ν μ :=
    ⟨by fun_prop,MeanPrivateReferenceBridge.scaled_forward M hF hlo base r⟩
  have hp := ((assembly_preserving (d := d) M).prod (hscale.prod (flow_preserving (d := d) M seeds))).comp
    (cross γ ν rawLaw flatLaw)
  have hreg := (regroup γ γ piLaw μ flowLaw).comp hp
  have hphase : MeasurePreserving (WithLp.toLp 2 : Point d × Point d → _)
      (μ.prod γ) (Kinetic.coupledPhaseMeasure μ) :=
    ⟨(WithLp.prod_continuous_toLp 2 (Point d) (Point d)).measurable,rfl⟩
  have hf := (((MeasurePreserving.id γ).prod (hphase.prod (MeasurePreserving.id flowLaw))).prod
    (MeasurePreserving.id piLaw)).comp hreg
  exact hf

end AcceleratedLogConcave.Oracle.MeanIncomingAssemblyLaw
