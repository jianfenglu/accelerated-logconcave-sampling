import AcceleratedLogConcave.Oracle.FreshChildBatchCoupling
import AcceleratedLogConcave.Oracle.FreshChildRunShift
import AcceleratedLogConcave.Oracle.CausalTailHistory
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Child error transport through the concrete finite batch of actual
completed-seed conditionals. Disintegration identities are used as measure
equalities, never as pointwise conditional-law premises. The original full
sample remains the first coordinate of every extension. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.FreshChildBatchErrorTransfer
open TapeLowering NoisyLayer CanonicalTapeLaw CanonicalTapeMeasurability AffineLowering
open FreshChildBatchCoupling FreshChildAbsorbedLaw
open AcceleratedLogConcave.Conditional.MeanReferenceLayer
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

local instance canonicalTapeSpace (d : ℕ) (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p

private theorem map_pair_compProd {X X' Y Y' : Type*}
    [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y] [MeasurableSpace Y']
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure X')
    (f : X → X') (hf : MeasurePreserving f μ ν) (g : Y → Y') (hg : Measurable g)
    (κ : Kernel X Y) [IsMarkovKernel κ] (η : Kernel X' Y') [IsMarkovKernel η]
    (hk : κ.map g = η.comap f hf.measurable) :
    (μ ⊗ₘ κ).map (Prod.map f g) = ν ⊗ₘ η := by
  have hm : Measurable (Prod.map id g : X × Y → X × Y') := measurable_id.prodMap hg
  have hm' : Measurable (Prod.map f id : X × Y' → X' × Y') :=
    hf.measurable.prodMap measurable_id
  have he : Prod.map f g = (Prod.map f id) ∘ (Prod.map id g) := rfl
  rw [he, ← Measure.map_map hm' hm, ← Measure.compProd_map hg, hk]
  change (μ ⊗ₘ η.comap f hf.measurable).map (fun z => (f z.1,z.2)) = _
  rw [compProd_comap_push μ η f hf.measurable, hf.map_eq]

variable {d N C : ℕ} {Γ : Ctx}
    (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
    (B : Data N C Γ) (J : Lower L B)
    {H : Type*} [MeasurableSpace H]
    (center : Fin N → H → Point d) (hcenter : ∀ i, Measurable (center i))

theorem referenceBatch_coordinate (i : Fin N) :
    (referenceBatch L hL B J center hcenter).map (fun v => v i) =
      (childConditional L hL B J i).comap
        (fun z : H × (∀ j, Raw d B j) => (center i z.1,z.2 i))
        (((hcenter i).comp measurable_fst).prodMk
          ((measurable_pi_apply i).comp measurable_snd)) := by
  ext z s hs
  rw [Kernel.map_apply _ (measurable_pi_apply i), referenceBatch,
    finiteProduct_apply N _ (fun _ => inferInstance)]
  exact congrArg (fun μ => μ s)
    (measurePreserving_eval (fun j => childConditional L hL B J j (center j z.1,z.2 j)) i).map_eq

def occurrenceConditional (i : Fin N) : Kernel (H × Raw d B i) (Point d) :=
  (childConditional L hL B J i).comap
    (fun z => (center i z.1,z.2)) (((hcenter i).comp measurable_fst).prodMk measurable_snd)

instance occurrenceConditional_markov (i : Fin N) :
    IsMarkovKernel (occurrenceConditional L hL B J center hcenter i) := by
  unfold occurrenceConditional
  infer_instance

def occurrenceKernel (i : Fin N) : Kernel H (Raw d B i × Point d) :=
  Kernel.const H (rawLaw L B i) ⊗ₖ occurrenceConditional L hL B J center hcenter i

instance occurrenceKernel_markov (i : Fin N) :
    IsMarkovKernel (occurrenceKernel L hL B J center hcenter i) := by
  unfold occurrenceKernel
  infer_instance

theorem occurrenceKernel_apply (i : Fin N) (h : H) :
    occurrenceKernel L hL B J center hcenter i h =
      FreshChildRetainedCoupling.occurrenceLaw L hL (B.child i).program (B.child i).enumeration
        (B.slot i) (B.old i) (B.designated i) (B.auxiliary i)
        (B.rho i) (B.radius i) B.Ds (B.child i).shiftVector
        (B.rho_nonneg i) (B.radius_pos i) B.Ds_pos (B.shift_budget i) (B.small i)
        (J.joint i) (center i h) := by
  let := FreshChildRetainedCoupling.originalLaw_probability L
    (B.child i).program (B.child i).enumeration (B.slot i)
    (B.old i) (B.designated i) (B.auxiliary i)
  ext s hs
  unfold FreshChildRetainedCoupling.occurrenceLaw
  rw [occurrenceKernel, Kernel.compProd_apply hs, Measure.compProd_apply hs]
  rfl

def completedMap (i : Fin N) : Raw d B i × Point d →
    (Point d × Tape d (B.child i).program) × Point d :=
  Prod.map (completedSource (B.child i).program (B.child i).enumeration
    (B.slot i) (B.old i) (B.designated i) (B.auxiliary i)
    (B.rho i) (B.radius i) (B.child i).shiftVector) id

include L hL in
theorem completedMap_measurable (i : Fin N) : Measurable (completedMap (d := d) B i) :=
  (completedSource_preserving L hL (B.child i).program (B.child i).enumeration
    (B.slot i) (B.old i) (B.designated i) (B.auxiliary i)
    (B.rho i) (B.radius i) B.Ds (B.child i).shiftVector
    (B.rho_nonneg i) (B.radius_pos i) B.Ds_pos (B.shift_budget i) (B.small i)).measurable.prodMap
      measurable_id

/-- The parameterized completed-seed joint law is the actual LOWER coupling.
No pointwise equality of conditional distributions is required. -/
theorem occurrenceKernel_completed (i : Fin N) :
    (occurrenceKernel L hL B J center hcenter i).map (completedMap B i) =
      (J.joint i).comap (center i) (hcenter i) := by
  ext h s hs
  rw [Kernel.map_apply _ (completedMap_measurable L hL B i), occurrenceKernel_apply]
  exact congrArg (fun μ => μ s)
    (FreshChildRetainedCoupling.projected_joint L hL (B.child i).program (B.child i).enumeration
      (B.slot i) (B.old i) (B.designated i) (B.auxiliary i)
      (B.rho i) (B.radius i) B.Ds (B.child i).shiftVector
      (B.rho_nonneg i) (B.radius_pos i) B.Ds_pos (B.shift_budget i) (B.small i)
      (J.joint i) (J.source i) (center i h))

/-- Exact child occurrence marginal of the entire augmented batch. The
remaining child seeds stay in the surrounding source sample. -/
theorem batch_child_preserving (ν : Measure H) [IsProbabilityMeasure ν] (i : Fin N) :
    MeasurePreserving
      (fun z : (H × (∀ j, Raw d B j)) × (Fin N → Point d) => (z.1.1,(z.1.2 i,z.2 i)))
      ((ν.prod (Measure.pi (rawLaw L B))) ⊗ₘ referenceBatch L hL B J center hcenter)
      (ν ⊗ₘ occurrenceKernel L hL B J center hcenter i) := by
  let f : H × (∀ j, Raw d B j) → H × Raw d B i := fun z => (z.1,z.2 i)
  have hf : MeasurePreserving f (ν.prod (Measure.pi (rawLaw L B))) (ν.prod (rawLaw L B i)) :=
    (MeasurePreserving.id ν).prod (measurePreserving_eval (rawLaw L B) i)
  have hk : (referenceBatch L hL B J center hcenter).map (fun v => v i) =
      (occurrenceConditional L hL B J center hcenter i).comap f hf.measurable := by
    rw [referenceBatch_coordinate]
    rfl
  have hp := map_pair_compProd (ν.prod (Measure.pi (rawLaw L B))) (ν.prod (rawLaw L B i))
    f hf (fun v => v i) (measurable_pi_apply i)
    (referenceBatch L hL B J center hcenter)
    (occurrenceConditional L hL B J center hcenter i) hk
  have h := congrArg (fun ρ : Measure ((H × Raw d B i) × Point d) =>
    ρ.map MeasurableEquiv.prodAssoc) hp
  have ha : Measurable (MeasurableEquiv.prodAssoc : ((H × Raw d B i) × Point d) →
      H × (Raw d B i × Point d)) := MeasurableEquiv.prodAssoc.measurable
  have hmap : Measurable (Prod.map f (fun v : Fin N → Point d => v i)) :=
    hf.measurable.prodMap (measurable_pi_apply i)
  have ht : ((ν.prod (rawLaw L B i)) ⊗ₘ occurrenceConditional L hL B J center hcenter i).map
      MeasurableEquiv.prodAssoc = ν ⊗ₘ occurrenceKernel L hL B J center hcenter i := by
    rw [← Measure.compProd_const]
    exact Measure.compProd_assoc'
  rw [Measure.map_map ha hmap, ht] at h
  exact ⟨measurable_fst.fst.prodMk
    (((measurable_pi_apply i).comp measurable_fst.snd).prodMk
      ((measurable_pi_apply i).comp measurable_snd)),h⟩

/-- Each completed full seed/reference pair has exactly its lower joint law,
integrated against the retained coarse center. This is the finite-batch
disintegration adapter used before paying child errors. -/
theorem batch_completed_preserving (ν : Measure H) [IsProbabilityMeasure ν] (i : Fin N) :
    MeasurePreserving
      (fun z : (H × (∀ j, Raw d B j)) × (Fin N → Point d) =>
        (z.1.1,completedMap B i (z.1.2 i,z.2 i)))
      ((ν.prod (Measure.pi (rawLaw L B))) ⊗ₘ referenceBatch L hL B J center hcenter)
      (ν ⊗ₘ (J.joint i).comap (center i) (hcenter i)) := by
  have hp : MeasurePreserving (Prod.map id (completedMap (d := d) B i))
      (ν ⊗ₘ occurrenceKernel L hL B J center hcenter i)
      (ν ⊗ₘ (J.joint i).comap (center i) (hcenter i)) := by
    refine ⟨measurable_id.prodMap (completedMap_measurable L hL B i), ?_⟩
    rw [← Measure.compProd_map (completedMap_measurable L hL B i), occurrenceKernel_completed]
  exact hp.comp (batch_child_preserving L hL B J center hcenter ν i)

/-- Integrate lower-depth error moments over the actual coarse centers.
Fibrewise L2 membership alone is insufficient: the scalar error payment must
also be integrable over those centers. -/
theorem averaged_error_memLp (ν : Measure H) [IsProbabilityMeasure ν] (i : Fin N)
    (err : H × ((Point d × Tape d (B.child i).program) × Point d) → Point d)
    (hmeas : StronglyMeasurable err)
    (hfiber : ∀ᵐ h ∂ν, MemLp (fun z => err (h,z)) 2 (J.joint i (center i h)))
    (hcost : Integrable (fun h => ∫ z, ‖err (h,z)‖^2 ∂J.joint i (center i h)) ν) :
    MemLp err 2 (ν ⊗ₘ (J.joint i).comap (center i) (hcenter i)) := by
  apply (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).2
  apply (Measure.integrable_compProd_iff (hmeas.norm.pow 2).aestronglyMeasurable).2
  constructor
  · filter_upwards [hfiber] with h hh
    exact (memLp_two_iff_integrable_sq_norm hh.aestronglyMeasurable).mp hh
  · change Integrable (fun h => ∫ z, ‖‖err (h,z)‖^2‖ ∂J.joint i (center i h)) ν
    simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using hcost

/-- An integrable lower-child scalar payment closes the averaged L2 moment.
The scalar payment may vary with the actual coarse center. -/
theorem averaged_error_memLp_of_bound (ν : Measure H) [IsProbabilityMeasure ν] (i : Fin N)
    (err : H × ((Point d × Tape d (B.child i).program) × Point d) → Point d)
    (hmeas : StronglyMeasurable err)
    (hfiber : ∀ᵐ h ∂ν, MemLp (fun z => err (h,z)) 2 (J.joint i (center i h)))
    (ε : H → ℝ) (hε : Integrable (fun h => ε h ^ 2) ν)
    (hbound : ∀ᵐ h ∂ν, (∫ z, ‖err (h,z)‖^2 ∂J.joint i (center i h)) ≤ ε h ^ 2) :
    MemLp err 2 (ν ⊗ₘ (J.joint i).comap (center i) (hcenter i)) ∧
      (∫ z, ‖err z‖^2 ∂ν ⊗ₘ (J.joint i).comap (center i) (hcenter i)) ≤
        ∫ h, ε h ^ 2 ∂ν := by
  have hm : StronglyMeasurable (fun h => ∫ z, ‖err (h,z)‖^2 ∂J.joint i (center i h)) :=
    (hmeas.norm.pow 2).integral_kernel_prod_right' (κ := (J.joint i).comap (center i) (hcenter i))
  have hi : Integrable (fun h => ∫ z, ‖err (h,z)‖^2 ∂J.joint i (center i h)) ν := by
    apply hε.mono' hm.aestronglyMeasurable
    filter_upwards [hbound] with h hh
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
    exact hh
  have herr := averaged_error_memLp L B J center hcenter ν i err hmeas hfiber hi
  refine ⟨herr,?_⟩
  rw [Measure.integral_compProd ((memLp_two_iff_integrable_sq_norm
    herr.aestronglyMeasurable).mp herr)]
  exact integral_mono_ae hi hε hbound

/-- Convert the transported squared-error payment to the genuine L2 norm
used by the synchronous numerical recurrence. -/
theorem norm_toLp_sq_eq {W : Type*} [MeasurableSpace W] (μ : Measure W)
    (f : W → Point d) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖^2 = ∫ z, ‖f z‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with z hz
  rw [hz, real_inner_self_eq_norm_sq]

theorem norm_toLp_le_of_square_integral {W : Type*} [MeasurableSpace W] (μ : Measure W)
    (f : W → Point d) (hf : MemLp f 2 μ) (ε : ℝ) (hε : 0 ≤ ε)
    (hbound : (∫ z, ‖f z‖^2 ∂μ) ≤ ε^2) : ‖hf.toLp f‖ ≤ ε := by
  have hn := norm_toLp_sq_eq μ f hf
  nlinarith [norm_nonneg (hf.toLp f)]

section Observed
variable {W : Type*} [MeasurableSpace W]
    (μ : Measure W) [IsProbabilityMeasure μ] (ν : Measure H) [IsProbabilityMeasure ν]
    (observe : W → H × (∀ j, Raw d B j)) (hobs : Measurable observe)
    (hprojection : μ.map observe = ν.prod (Measure.pi (rawLaw L B)))

/-- Original full sample/reference-vector extension at its actual observation. -/
def observedLaw := μ ⊗ₘ (referenceBatch L hL B J center hcenter).comap observe hobs

instance observedLaw_probability :
    IsProbabilityMeasure (observedLaw L hL B J center hcenter μ observe hobs) := by
  unfold observedLaw
  infer_instance

theorem observedLaw_original :
    (observedLaw L hL B J center hcenter μ observe hobs).map Prod.fst = μ :=
  Measure.fst_compProd _ _

def lowerProjection (i : Fin N) (z : W × (Fin N → Point d)) :
    H × ((Point d × Tape d (B.child i).program) × Point d) :=
  ((observe z.1).1,completedMap B i ((observe z.1).2 i,z.2 i))

include hprojection in
/-- AE disintegration is consumed only through the proved measure identity.
The old sample may contain history correlated with the comparison vector;
only its stated coarse/raw projection is used. -/
theorem observed_completed_preserving (i : Fin N) :
    MeasurePreserving (lowerProjection B observe i)
      (observedLaw L hL B J center hcenter μ observe hobs)
      (ν ⊗ₘ (J.joint i).comap (center i) (hcenter i)) := by
  have hp : MeasurePreserving (fun z : W × (Fin N → Point d) => (observe z.1,z.2))
      (observedLaw L hL B J center hcenter μ observe hobs)
      ((ν.prod (Measure.pi (rawLaw L B))) ⊗ₘ referenceBatch L hL B J center hcenter) := by
    refine ⟨(hobs.comp measurable_fst).prodMk measurable_snd, ?_⟩
    rw [observedLaw, compProd_comap_push, hprojection]
  exact (batch_completed_preserving L hL B J center hcenter ν i).comp hp

include hprojection in
theorem observed_error_memLp (i : Fin N)
    (err : H × ((Point d × Tape d (B.child i).program) × Point d) → Point d)
    (herr : MemLp err 2 (ν ⊗ₘ (J.joint i).comap (center i) (hcenter i))) :
    MemLp (fun z => err (lowerProjection B observe i z)) 2
      (observedLaw L hL B J center hcenter μ observe hobs) :=
  herr.comp_measurePreserving
    (observed_completed_preserving L hL B J center hcenter μ ν observe hobs hprojection i)

include hprojection in
theorem observed_error_square_integral (i : Fin N)
    (err : H × ((Point d × Tape d (B.child i).program) × Point d) → Point d)
    (herr : MemLp err 2 (ν ⊗ₘ (J.joint i).comap (center i) (hcenter i))) :
    (∫ z, ‖err (lowerProjection B observe i z)‖^2
      ∂observedLaw L hL B J center hcenter μ observe hobs) =
      ∫ h, ∫ z, ‖err (h,z)‖^2 ∂J.joint i (center i h) ∂ν := by
  have hp := observed_completed_preserving L hL B J center hcenter μ ν observe hobs hprojection i
  have hg : AEStronglyMeasurable (fun z => ‖err z‖^2)
      (ν ⊗ₘ (J.joint i).comap (center i) (hcenter i)) :=
    herr.aestronglyMeasurable.norm.pow 2
  have hi := integral_map hp.aemeasurable (hp.map_eq.symm ▸ hg)
  rw [hp.map_eq] at hi
  rw [← hi]
  exact Measure.integral_compProd ((memLp_two_iff_integrable_sq_norm
    herr.aestronglyMeasurable).mp herr)

def benchmarkError (i : Fin N) (G : Point d → Point d)
    (input : W → Inputs d C) (env : W → Env d Γ) (u : H → Point d) (σ : ℝ)
    (z : W × (Fin N → Point d)) : Point d :=
  (show Point d from (run (program B i) G (input z.1) (env z.1) ((observe z.1).2 i).2).value) -
    (u (observe z.1).1 + σ • z.2 i)

def lowerError (i : Fin N) (G : Point d → Point d) (u : H → Point d) (σ : ℝ)
    (z : H × ((Point d × Tape d (B.child i).program) × Point d)) : Point d :=
  FreshChildRunShift.lowerError (B.child i).program G (B.child i).coefficient
    (center i z.1) (u z.1) σ z.2

include hcenter in
/-- Actual lower error measurability follows from finite executable syntax and
the measurable original oracle; it is not a child regularity certificate. -/
theorem lowerError_stronglyMeasurable (i : Fin N) (G : Point d → Point d) (hG : Measurable G)
    (u : H → Point d) (hu : Measurable u) (σ : ℝ) :
    StronglyMeasurable (lowerError (d := d) B center i G u σ) := by
  apply Measurable.stronglyMeasurable
  have hr := CanonicalTapeMeasurability.program_point_of_measurable
    (B.child i).program G hG (fun _ => (B.child i).coefficient)
    (fun z : H × ((Point d × Tape d (B.child i).program) × Point d) => center i z.1)
    (fun z => z.2.1.1) (fun z => z.2.1.2)
    measurable_const ((hcenter i).comp measurable_fst) measurable_snd.fst.fst measurable_snd.fst.snd
  have hs : Measurable (fun z : H × ((Point d × Tape d (B.child i).program) × Point d) =>
      σ • z.2.2) :=
    (measurable_const : Measurable (fun _ : H × ((Point d × Tape d (B.child i).program) × Point d) =>
      σ)).smul measurable_snd.snd
  exact hr.sub ((hu.comp measurable_fst).add hs)

/-- Deterministic absorption may hold only almost everywhere in the old
retained history. It still identifies the actual benchmark child error on the
augmented batch with the lower error at the SAME completed source seed. -/
theorem benchmarkError_eq_ae (i : Fin N) (G : Point d → Point d)
    (input : W → Inputs d C) (env : W → Env d Γ) (u : H → Point d) (σ : ℝ)
    (hshift : ChildAbsorption.QueryShift (B.child i).program (B.child i).enumeration
      (B.child i).coefficient (B.radius i) (B.child i).shiftVector)
    (htable : ∀ᵐ w ∂μ, (input w).coefficient ∘ B.slot i =
      matrixTable (CovarianceSetup.childRoot (B.rho i) (B.radius i)
        (B.child i).shiftVector) (B.child i).coefficient)
    (hstored : ∀ᵐ w ∂μ, storedPoint (env w) (B.old i) =
      center i (observe w).1 + B.rho i • ((observe w).2 i).1) :
    benchmarkError B observe i G input env u σ =ᵐ[observedLaw L hL B J center hcenter μ observe hobs]
      (fun z => lowerError B center i G u σ (lowerProjection B observe i z)) := by
  have hp : MeasurePreserving Prod.fst
      (observedLaw L hL B J center hcenter μ observe hobs) μ :=
    ⟨measurable_fst, observedLaw_original L hL B J center hcenter μ observe hobs⟩
  filter_upwards [hp.quasiMeasurePreserving.ae htable, hp.quasiMeasurePreserving.ae hstored]
    with z ht hs
  exact FreshChildRunShift.freshChild_error_eq (B.child i).program (B.child i).enumeration
    (B.slot i) (B.old i) (B.designated i) (B.auxiliary i)
    (B.rho i) (B.radius i) B.Ds (B.child i).shiftVector (B.child i).coefficient
    (B.rho_nonneg i) (B.radius_pos i) B.Ds_pos (B.shift_budget i) (B.small i)
    hshift G (input z.1) (env z.1) (center i (observe z.1).1) ht ((observe z.1).2 i)
    hs (u (observe z.1).1) (z.2 i) σ

include hprojection in
theorem benchmark_error_memLp (i : Fin N) (G : Point d → Point d)
    (input : W → Inputs d C) (env : W → Env d Γ) (u : H → Point d) (σ : ℝ)
    (hshift : ChildAbsorption.QueryShift (B.child i).program (B.child i).enumeration
      (B.child i).coefficient (B.radius i) (B.child i).shiftVector)
    (htable : ∀ᵐ w ∂μ, (input w).coefficient ∘ B.slot i =
      matrixTable (CovarianceSetup.childRoot (B.rho i) (B.radius i)
        (B.child i).shiftVector) (B.child i).coefficient)
    (hstored : ∀ᵐ w ∂μ, storedPoint (env w) (B.old i) =
      center i (observe w).1 + B.rho i • ((observe w).2 i).1)
    (herr : MemLp (lowerError B center i G u σ) 2
      (ν ⊗ₘ (J.joint i).comap (center i) (hcenter i))) :
    MemLp (benchmarkError B observe i G input env u σ) 2
      (observedLaw L hL B J center hcenter μ observe hobs) := by
  exact MemLp.ae_eq
    (benchmarkError_eq_ae L hL B J center hcenter μ observe hobs
      i G input env u σ hshift htable hstored).symm
    (observed_error_memLp L hL B J center hcenter μ ν observe hobs hprojection
      i (lowerError B center i G u σ) herr)

include hprojection in
theorem benchmark_error_square_integral (i : Fin N) (G : Point d → Point d)
    (input : W → Inputs d C) (env : W → Env d Γ) (u : H → Point d) (σ : ℝ)
    (hshift : ChildAbsorption.QueryShift (B.child i).program (B.child i).enumeration
      (B.child i).coefficient (B.radius i) (B.child i).shiftVector)
    (htable : ∀ᵐ w ∂μ, (input w).coefficient ∘ B.slot i =
      matrixTable (CovarianceSetup.childRoot (B.rho i) (B.radius i)
        (B.child i).shiftVector) (B.child i).coefficient)
    (hstored : ∀ᵐ w ∂μ, storedPoint (env w) (B.old i) =
      center i (observe w).1 + B.rho i • ((observe w).2 i).1)
    (herr : MemLp (lowerError B center i G u σ) 2
      (ν ⊗ₘ (J.joint i).comap (center i) (hcenter i))) :
    (∫ z, ‖benchmarkError B observe i G input env u σ z‖^2
      ∂observedLaw L hL B J center hcenter μ observe hobs) =
      ∫ h, ∫ z, ‖FreshChildRunShift.lowerError (B.child i).program G (B.child i).coefficient
        (center i h) (u h) σ z‖^2 ∂J.joint i (center i h) ∂ν := by
  have he := benchmarkError_eq_ae L hL B J center hcenter μ observe hobs
    i G input env u σ hshift htable hstored
  calc
    _ = ∫ z, ‖lowerError B center i G u σ (lowerProjection B observe i z)‖^2
        ∂observedLaw L hL B J center hcenter μ observe hobs := by
      apply integral_congr_ae
      filter_upwards [he] with z hz
      rw [hz]
    _ = _ := observed_error_square_integral L hL B J center hcenter μ ν observe hobs hprojection
      i (lowerError B center i G u σ) herr

end Observed

section FullTape
open TailOccurrenceCut TailCut
variable {d₀ c₀ : ℕ} {Γ₀ Δ₀ : Ctx} {τ₀ υ₀ : Ty}
    {host : Prog c₀ Γ₀ τ₀} {tail : Prog c₀ Δ₀ υ₀}
    {A₀ R₀ : Type*} [MeasurableSpace A₀] [MeasurableSpace R₀]
    (L₀ : PrimitiveLaws d₀) (cut : TailCut tail host)
local instance : MeasurableSpace (Prefix d₀ cut) := prefixSpace d₀ cut
local instance : IsProbabilityMeasure (tapeLaw L₀ tail) := tapeLaw_probability L₀ _

/-- Return from the consumed-prefix presentation to the actual retained full
tape/reference sample. The complete unread tail is only forgotten by this
projection, and remains present in the original coupling law rho. -/
theorem full_sample_projection_preserving
    (ρ : Measure ((A₀ × Tape d₀ host) × R₀))
    (σ : Measure ((A₀ × Prefix d₀ cut) × R₀)) [SFinite σ]
    (hcut : ρ.map (CausalTailHistory.unpackExtended cut) = σ.prod (tapeLaw L₀ tail)) :
    MeasurePreserving
      (fun z : (A₀ × Tape d₀ host) × R₀ => ((z.1.1,(split cut z.1.2).1),z.2)) ρ σ :=
  (measurePreserving_fst (μ := σ) (ν := tapeLaw L₀ tail)).comp
    ⟨CausalTailHistory.measurable_unpackExtended L₀ cut,hcut⟩

theorem full_sample_error_memLp
    (ρ : Measure ((A₀ × Tape d₀ host) × R₀))
    (σ : Measure ((A₀ × Prefix d₀ cut) × R₀)) [SFinite σ]
    (hcut : ρ.map (CausalTailHistory.unpackExtended cut) = σ.prod (tapeLaw L₀ tail))
    (err : ((A₀ × Prefix d₀ cut) × R₀) → Point d₀) (herr : MemLp err 2 σ) :
    MemLp (fun z : (A₀ × Tape d₀ host) × R₀ =>
      err ((z.1.1,(split cut z.1.2).1),z.2)) 2 ρ :=
  herr.comp_measurePreserving (full_sample_projection_preserving L₀ cut ρ σ hcut)

theorem full_sample_error_square_integral
    (ρ : Measure ((A₀ × Tape d₀ host) × R₀))
    (σ : Measure ((A₀ × Prefix d₀ cut) × R₀)) [SFinite σ]
    (hcut : ρ.map (CausalTailHistory.unpackExtended cut) = σ.prod (tapeLaw L₀ tail))
    (err : ((A₀ × Prefix d₀ cut) × R₀) → Point d₀) (herr : MemLp err 2 σ) :
    (∫ z : (A₀ × Tape d₀ host) × R₀,
      ‖err ((z.1.1,(split cut z.1.2).1),z.2)‖^2 ∂ρ) = ∫ z, ‖err z‖^2 ∂σ := by
  have hp := full_sample_projection_preserving L₀ cut ρ σ hcut
  have hg : AEStronglyMeasurable (fun z => ‖err z‖^2) σ :=
    herr.aestronglyMeasurable.norm.pow 2
  have hi := integral_map hp.aemeasurable (hp.map_eq.symm ▸ hg)
  rw [hp.map_eq] at hi
  exact hi.symm

end FullTape

end AcceleratedLogConcave.Oracle.FreshChildBatchErrorTransfer
