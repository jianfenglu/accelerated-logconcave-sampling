import AcceleratedLogConcave.Oracle.FreshChildRetainedCoupling
import AcceleratedLogConcave.Oracle.ExecutableData
import AcceleratedLogConcave.Conditional.MeanReferenceLayer
import AcceleratedLogConcave.Conditional.RecursiveReferenceFamily

/-! A finite batch of the actual fresh-child disintegrations. Each conditional
reads the same completed source seed of its literal child occurrence. The
original comparison draws, designated draws and complete child tapes are kept.
Only lower-depth source and reference marginals are inputs; no parent accuracy
or parent Gaussian invariant is a premise. Empty batches are included. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open MeasureTheory.Measure
open scoped ENNReal
namespace AcceleratedLogConcave.Oracle.FreshChildBatchCoupling
open TapeLowering NoisyLayer CanonicalTapeLaw CanonicalTapeMeasurability
open AcceleratedLogConcave.Conditional.MeanReferenceLayer

local instance canonicalTapeSpace (d : ℕ) (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p

/-- Literal child programs, their actual slot embeddings and covariance domain.
The Gaussian enumeration and shift vector are computed from ExecutableData.
No accuracy or law certificate is stored here. -/
structure Data (N C : ℕ) (Γ : Ctx) where
  child : Fin N → ExecutableData
  slot : ∀ i, Fin ((tapeShape (child i).program).gaussianBlocks * (tapeShape (child i).program).gaussianBlocks + (child i).size) → Fin C
  old : Fin N → Ref Γ .point
  designated : Fin N → Origin
  auxiliary : ∀ i, Fin (tapeShape (child i).program).gaussianBlocks → Origin
  rho : Fin N → ℝ
  radius : Fin N → ℝ
  Ds : ℝ
  rho_nonneg : ∀ i, 0 ≤ rho i
  radius_pos : ∀ i, 0 < radius i
  Ds_pos : 0 < Ds
  shift_budget : ∀ i, CovarianceSetup.shiftSq (child i).shiftVector ≤ Ds ^ 2
  small : ∀ i, rho i ≤ radius i / (2 * Ds)

variable {d N C : ℕ} {Γ : Ctx}

def program (B : Data N C Γ) (i : Fin N) : Prog C Γ .point :=
  freshChild (B.child i).program (B.child i).enumeration
    (B.slot i) (B.old i) (B.designated i) (B.auxiliary i)

abbrev Raw (d : ℕ) (B : Data N C Γ) (i : Fin N) := Point d × Tape d (program B i)

def rawLaw (L : PrimitiveLaws d) (B : Data N C Γ) (i : Fin N) : Measure (Raw d B i) :=
  (stdGaussian (Point d)).prod (tapeLaw L (program B i))

instance rawLaw_probability (L : PrimitiveLaws d) (B : Data N C Γ) (i : Fin N) :
    IsProbabilityMeasure (rawLaw L B i) := by
  exact FreshChildRetainedCoupling.originalLaw_probability L
    (B.child i).program (B.child i).enumeration (B.slot i)
    (B.old i) (B.designated i) (B.auxiliary i)

/-- Separate the comparison vector from the entire literal tape array. This
is only a reordering of a full original sample. -/
def rawSplit (d : ℕ) (B : Data N C Γ) :
    (∀ i, Raw d B i) ≃ᵐ ((Fin N → Point d) × (∀ i, Tape d (program B i))) where
  toFun w := (fun i => (w i).1,fun i => (w i).2)
  invFun z i := (z.1 i,z.2 i)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := (measurable_pi_iff.mpr fun i =>
    measurable_fst.comp (measurable_pi_apply i)).prodMk
      (measurable_pi_iff.mpr fun i => measurable_snd.comp (measurable_pi_apply i))
  measurable_invFun := measurable_pi_iff.mpr fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)

theorem rawSplit_preserving (L : PrimitiveLaws d) (B : Data N C Γ) :
    MeasurePreserving (rawSplit d B) (Measure.pi (rawLaw L B))
      ((Measure.pi (fun _ : Fin N => stdGaussian (Point d))).prod
        (Measure.pi (fun i => tapeLaw L (program B i)))) := by
  let : ∀ i, IsProbabilityMeasure (tapeLaw L (program B i)) := fun i => tapeLaw_probability L _
  refine ⟨(rawSplit d B).measurable, ?_⟩
  refine (FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
    ((FiniteSpanningSetsIn.pi fun _ : Fin N =>
      (stdGaussian (Point d)).toFiniteSpanningSetsIn).prod
      (FiniteSpanningSetsIn.pi fun i => (tapeLaw L (program B i)).toFiniteSpanningSetsIn))
    ?_).symm
  · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
    · exact (FiniteSpanningSetsIn.pi fun _ : Fin N =>
        (stdGaussian (Point d)).toFiniteSpanningSetsIn).isCountablySpanning
    · exact (FiniteSpanningSetsIn.pi fun i =>
        (tapeLaw L (program B i)).toFiniteSpanningSetsIn).isCountablySpanning
  · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
    rw [MeasurableEquiv.map_apply]
    have he : (rawSplit d B) ⁻¹' (univ.pi s ×ˢ univ.pi t) =
        univ.pi (fun i => s i ×ˢ t i) := by
      ext w
      simp [rawSplit, Set.mem_pi, forall_and]
    rw [he]
    simp_rw [Measure.prod_prod, Measure.pi_pi, rawLaw,
      Measure.prod_prod, Finset.prod_mul_distrib]

/-- The supplied coupling is for each LOWER child, with its entire standalone
source seed as first marginal and its exact reference invariant as second.
The batch conclusion itself is not an input. -/
structure Lower (L : PrimitiveLaws d) (B : Data N C Γ) where
  joint : ∀ i, Kernel (Point d) ((Point d × Tape d (B.child i).program) × Point d)
  markov : ∀ i, IsMarkovKernel (joint i)
  source : ∀ i, (joint i).fst = Kernel.const (Point d)
    (FreshChildRetainedCoupling.sourceLaw L (B.child i).program)
  reference : ∀ i x, (joint i x).snd = stdGaussian (Point d)

instance lower_markov (L : PrimitiveLaws d) (B : Data N C Γ) (J : Lower L B) (i : Fin N) :
    IsMarkovKernel (J.joint i) := J.markov i

/-- A lower retained designated/reference identity and the reference kernel's
proved invariant imply the needed reference marginal. -/
theorem reference_marginal_of_retained {c : ℕ} (p : Program c .point)
    (μ : Measure ((Point d × Tape d p) × Point d))
    (k : Kernel (Point d) (Point d)) [IsMarkovKernel k]
    (hretained : μ.map (fun z => (z.1.1,z.2)) = stdGaussian (Point d) ⊗ₘ k)
    (hinvariant : k ∘ₘ stdGaussian (Point d) = stdGaussian (Point d)) :
    μ.snd = stdGaussian (Point d) := by
  have h := congrArg (fun ρ : Measure (Point d × Point d) => ρ.map Prod.snd) hretained
  rw [Measure.map_map measurable_snd (by fun_prop)] at h
  change μ.snd = (stdGaussian (Point d) ⊗ₘ k).snd at h
  rwa [Measure.snd_compProd, hinvariant] at h

/-- The actual recursive reference family supplies the invariant in the
previous lemma at the prescribed lower precision and physical parameters.
The potential remains the original F. -/
theorem recursive_reference_marginal {c m : ℕ} {F : Point d → ℝ} {ell : ℝ}
    (hF : ContDiff ℝ 2 F) (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (G : Numerics.AffineGraph.MeanGeometry m) (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) (q : ℝ)
    (theta : Conditional.SourceParameters (Point d) ell) (p : Program c .point)
    (μ : Measure ((Point d × Tape d p) × Point d))
    (hretained : μ.map (fun z => (z.1.1,z.2)) = stdGaussian (Point d) ⊗ₘ
      (Conditional.RecursiveReference.referenceFamily hF hell hlo hup G hm t ht q).kernel.comap
        (fun v => (theta,v)) measurable_prodMk_left) :
    μ.snd = stdGaussian (Point d) := by
  exact reference_marginal_of_retained p μ _ hretained
    (Conditional.RecursiveReference.referenceFamily_invariant hF hell hlo hup G hm t ht q theta)

/-- Build the batch's lower inputs directly from the actual lower retained
reference identity. Its Gaussian marginal field is a theorem of the recursive
reference family and is not an additional induction hypothesis. -/
def Lower.ofRecursiveReference (L : PrimitiveLaws d) (B : Data N C Γ)
    {m : ℕ} {F : Point d → ℝ} {ell : ℝ}
    (hF : ContDiff ℝ 2 F) (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (G : Numerics.AffineGraph.MeanGeometry m) (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) (q : Fin N → ℝ)
    (theta : Fin N → Point d → Conditional.SourceParameters (Point d) ell)
    (joint : ∀ i, Kernel (Point d) ((Point d × Tape d (B.child i).program) × Point d))
    (hmarkov : ∀ i, IsMarkovKernel (joint i))
    (hsource : ∀ i, (joint i).fst = Kernel.const (Point d)
      (FreshChildRetainedCoupling.sourceLaw L (B.child i).program))
    (hretained : ∀ i x, (joint i x).map (fun z => (z.1.1,z.2)) =
      stdGaussian (Point d) ⊗ₘ
        (Conditional.RecursiveReference.referenceFamily hF hell hlo hup G hm t ht (q i)).kernel.comap
          (fun v => (theta i x,v)) measurable_prodMk_left) : Lower L B where
  joint := joint
  markov := hmarkov
  source := hsource
  reference i x := recursive_reference_marginal hF hell hlo hup G hm t ht (q i)
    (theta i x) (B.child i).program (joint i x) (hretained i x)

variable (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
    (B : Data N C Γ) (J : Lower L B)

/-- Source-specific conditional at the SAME completed seed, using all actual
program/table/enumeration data of child i. -/
def childConditional (i : Fin N) : Kernel (Point d × Raw d B i) (Point d) :=
  FreshChildRetainedCoupling.conditional L hL (B.child i).program (B.child i).enumeration
    (B.slot i) (B.old i) (B.designated i) (B.auxiliary i)
    (B.rho i) (B.radius i) B.Ds (B.child i).shiftVector
    (B.rho_nonneg i) (B.radius_pos i) B.Ds_pos (B.shift_budget i) (B.small i) (J.joint i)

instance childConditional_markov (i : Fin N) :
    IsMarkovKernel (childConditional L hL B J i) := by
  exact FreshChildRetainedCoupling.conditional_markov L hL
    (B.child i).program (B.child i).enumeration (B.slot i)
    (B.old i) (B.designated i) (B.auxiliary i)
    (B.rho i) (B.radius i) B.Ds (B.child i).shiftVector
    (B.rho_nonneg i) (B.radius_pos i) B.Ds_pos (B.shift_budget i) (B.small i) (J.joint i)

theorem childConditional_invariant (i : Fin N) (x : Point d) :
    (childConditional L hL B J i).comap (fun w => (x,w)) measurable_prodMk_left ∘ₘ
      rawLaw L B i = stdGaussian (Point d) := by
  have hp := FreshChildRetainedCoupling.projected_joint L hL
    (B.child i).program (B.child i).enumeration
    (B.slot i) (B.old i) (B.designated i) (B.auxiliary i)
    (B.rho i) (B.radius i) B.Ds (B.child i).shiftVector
    (B.rho_nonneg i) (B.radius_pos i) B.Ds_pos (B.shift_budget i) (B.small i)
    (J.joint i) (J.source i) x
  have h := congrArg (fun μ => Measure.map Prod.snd μ) hp
  rw [Measure.map_map measurable_snd (by
    exact (FreshChildAbsorbedLaw.completedSource_preserving L hL
      (B.child i).program (B.child i).enumeration
      (B.slot i) (B.old i) (B.designated i) (B.auxiliary i)
      (B.rho i) (B.radius i) B.Ds (B.child i).shiftVector
      (B.rho_nonneg i) (B.radius_pos i) B.Ds_pos (B.shift_budget i)
      (B.small i)).measurable.prodMap measurable_id)] at h
  change (rawLaw L B i ⊗ₘ
    (childConditional L hL B J i).comap (fun w => (x,w)) measurable_prodMk_left).snd =
      (J.joint i x).snd at h
  rw [Measure.snd_compProd, J.reference i x] at h
  exact h

/-- Existing finiteProduct, applied to the literal child occurrence
conditionals; centers can depend on arbitrary measurable coarse data. -/
def referenceBatch {H : Type*} [MeasurableSpace H]
    (center : Fin N → H → Point d) (hcenter : ∀ i, Measurable (center i)) :
    Kernel (H × (∀ i, Raw d B i)) (Fin N → Point d) :=
  finiteProduct N (fun i => (childConditional L hL B J i).comap
    (fun z => (center i z.1,z.2 i))
    ((hcenter i).comp measurable_fst |>.prodMk
      ((measurable_pi_apply i).comp measurable_snd)))

instance referenceBatch_markov {H : Type*} [MeasurableSpace H]
    (center : Fin N → H → Point d) (hcenter : ∀ i, Measurable (center i)) :
    IsMarkovKernel (referenceBatch L hL B J center hcenter) := by
  apply finiteProduct_markov
  intro i
  infer_instance

theorem referenceBatch_measurable {H : Type*} [MeasurableSpace H]
    (center : Fin N → H → Point d) (hcenter : ∀ i, Measurable (center i)) :
    Measurable (referenceBatch L hL B J center hcenter) := Kernel.measurable _

/-- The full vector of adjoined references is an independent Gaussian vector.
This is derived by averaging the actual completed-seed conditionals against
the full original occurrence laws, rather than assumed as a batch certificate. -/
theorem referenceBatch_invariant {H : Type*} [MeasurableSpace H]
    (center : Fin N → H → Point d) (hcenter : ∀ i, Measurable (center i)) (h : H) :
    (referenceBatch L hL B J center hcenter).comap
      (fun w => (h,w)) measurable_prodMk_left ∘ₘ Measure.pi (rawLaw L B) =
      Measure.pi (fun _ : Fin N => stdGaussian (Point d)) := by
  let k := (referenceBatch L hL B J center hcenter).comap
    (fun w => (h,w)) measurable_prodMk_left
  apply (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.bind_apply (MeasurableSet.univ_pi hs) k.aemeasurable]
  have he : ∀ w, k w (Set.univ.pi s) =
      ∏ i, childConditional L hL B J i (center i h,w i) (s i) := by
    intro w
    rw [Kernel.comap_apply, referenceBatch, finiteProduct_apply N _ (fun _ => inferInstance),
      Measure.pi_pi]
    rfl
  simp_rw [he]
  have hf : ∀ i, Measurable (fun w : Raw d B i =>
      childConditional L hL B J i (center i h,w) (s i)) := fun i =>
    ((childConditional L hL B J i).measurable_coe (hs i)).comp measurable_prodMk_left
  have hi := iIndepFun_pi (μ := rawLaw L B) (fun i => (hf i).aemeasurable)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hi
    (fun i => (hf i).comp (measurable_pi_apply i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [(measurePreserving_eval (rawLaw L B) i).lintegral_comp (hf i)]
  change (∫⁻ w, ((childConditional L hL B J i).comap
    (fun w => (center i h,w)) measurable_prodMk_left) w (s i) ∂rawLaw L B i) = _
  rw [← Measure.bind_apply (hs i) (Kernel.aemeasurable _),
    childConditional_invariant L hL B J i (center i h)]

/-- The same invariant with the comparison vector and actual whole child tape
array separated, as needed when only a projection of the past has this law. -/
theorem referenceBatch_separated_invariant {H : Type*} [MeasurableSpace H]
    (center : Fin N → H → Point d) (hcenter : ∀ i, Measurable (center i)) (h : H) :
    (referenceBatch L hL B J center hcenter).comap
      (fun z => (h,(rawSplit d B).symm z))
      (measurable_const.prodMk (rawSplit d B).symm.measurable) ∘ₘ
      ((Measure.pi (fun _ : Fin N => stdGaussian (Point d))).prod
        (Measure.pi (fun i => tapeLaw L (program B i)))) =
      Measure.pi (fun _ : Fin N => stdGaussian (Point d)) := by
  rw [← (rawSplit_preserving L B).map_eq,
    bind_map_input _ _ _ (rawSplit d B).measurable]
  have hk : ((referenceBatch L hL B J center hcenter).comap
      (fun z => (h,(rawSplit d B).symm z))
      (measurable_const.prodMk (rawSplit d B).symm.measurable)).comap
        (rawSplit d B) (rawSplit d B).measurable =
      (referenceBatch L hL B J center hcenter).comap
        (fun w => (h,w)) measurable_prodMk_left := by
    ext w s hs
    simp only [Kernel.comap_apply, MeasurableEquiv.symm_apply_apply]
  rw [hk]
  exact referenceBatch_invariant L hL B J center hcenter h

/-- The entire coarse datum and raw occurrence sample are retained in the
kernel output; the new reference is the only appended coordinate. -/
def retainedBatch {H : Type*} [MeasurableSpace H]
    (center : Fin N → H → Point d) (hcenter : ∀ i, Measurable (center i)) :=
  (Kernel.id : Kernel (H × (∀ i, Raw d B i)) _) ×ₖ
    referenceBatch L hL B J center hcenter

instance retainedBatch_markov {H : Type*} [MeasurableSpace H]
    (center : Fin N → H → Point d) (hcenter : ∀ i, Measurable (center i)) :
    IsMarkovKernel (retainedBatch L hL B J center hcenter) := by
  unfold retainedBatch
  infer_instance

theorem retainedBatch_original {H : Type*} [MeasurableSpace H]
    (center : Fin N → H → Point d) (hcenter : ∀ i, Measurable (center i)) :
    (retainedBatch L hL B J center hcenter).fst = Kernel.id := by
  unfold retainedBatch
  exact Kernel.fst_prod _ _

/-- Reference vector and coarse data have their exact product law. The raw
sample remains present and may correlate with the references. -/
theorem coarse_reference_law {H : Type*} [MeasurableSpace H]
    (center : Fin N → H → Point d) (hcenter : ∀ i, Measurable (center i))
    (μ : Measure H) [IsProbabilityMeasure μ] :
    ((retainedBatch L hL B J center hcenter) ∘ₘ
      μ.prod (Measure.pi (rawLaw L B))).map (fun z => (z.1.1,z.2)) =
      μ.prod (Measure.pi (fun _ : Fin N => stdGaussian (Point d))) := by
  rw [Measure.map_comp _ _ (by fun_prop)]
  have hk : (retainedBatch L hL B J center hcenter).map (fun z => (z.1.1,z.2)) =
      (Kernel.deterministic Prod.fst measurable_fst) ×ₖ
        referenceBatch L hL B J center hcenter := by
    ext z s hs
    rw [Kernel.map_apply _ (by fun_prop), retainedBatch, Kernel.prod_apply, Kernel.prod_apply,
      Kernel.id_apply, Kernel.deterministic_apply]
    change ((Measure.dirac z).prod ((referenceBatch L hL B J center hcenter) z)).map
      (Prod.map Prod.fst id) s = _
    rw [← Measure.map_prod_map _ _ measurable_fst measurable_id]
    rw [Measure.map_dirac' measurable_fst, Measure.map_id]
  rw [hk]
  exact retained_update μ (Measure.pi (rawLaw L B))
    (Measure.pi (fun _ : Fin N => stdGaussian (Point d))) _
    (referenceBatch_invariant L hL B J center hcenter)

/-- Pull back the concrete occurrence conditional through an arbitrary old
history. Only its projected coarse/raw law must factor; the whole history
can be correlated with the comparison draws. All of that history is retained
in the compProd, and its first projection is exactly the original law. -/
theorem projected_coarse_reference_law {A H : Type*}
    [MeasurableSpace A] [MeasurableSpace H]
    (center : Fin N → H → Point d) (hcenter : ∀ i, Measurable (center i))
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure H) [IsProbabilityMeasure ν]
    (project : A → H × (∀ i, Raw d B i)) (hp : Measurable project)
    (hprojection : μ.map project = ν.prod (Measure.pi (rawLaw L B))) :
    (μ ⊗ₘ (referenceBatch L hL B J center hcenter).comap project hp).map
      (fun z => ((project z.1).1,z.2)) =
      ν.prod (Measure.pi (fun _ : Fin N => stdGaussian (Point d))) := by
  have h := compProd_comap_push μ (referenceBatch L hL B J center hcenter) project hp
  have h' := congrArg (fun ρ : Measure ((H × (∀ i, Raw d B i)) × (Fin N → Point d)) =>
    ρ.map (fun z => (z.1.1,z.2))) h
  have hpair : Measurable (fun z : A × (Fin N → Point d) => (project z.1,z.2)) :=
    (hp.comp measurable_fst).prodMk measurable_snd
  rw [Measure.map_map (by fun_prop) hpair,
    hprojection] at h'
  have hc := coarse_reference_law L hL B J center hcenter ν
  rw [retainedBatch, ← Measure.compProd_eq_comp_prod] at hc
  exact h'.trans hc

/-- Parallel identity keeps the complete residual/unread suffix. -/
def fullBatch {H R : Type*} [MeasurableSpace H] [MeasurableSpace R]
    (center : Fin N → H → Point d) (hcenter : ∀ i, Measurable (center i)) :=
  retainedBatch L hL B J center hcenter ∥ₖ (Kernel.id : Kernel R R)

instance fullBatch_markov {H R : Type*} [MeasurableSpace H] [MeasurableSpace R]
    (center : Fin N → H → Point d) (hcenter : ∀ i, Measurable (center i)) :
    IsMarkovKernel (fullBatch (R := R) L hL B J center hcenter) := by
  unfold fullBatch
  infer_instance

/-- The WHOLE suffix remains independent of the old complete sample and all
newly adjoined references. No statement conditions on the original momentum. -/
theorem whole_suffix_fresh {H R : Type*} [MeasurableSpace H] [MeasurableSpace R]
    (center : Fin N → H → Point d) (hcenter : ∀ i, Measurable (center i))
    (μ : Measure (H × (∀ i, Raw d B i))) [SFinite μ]
    (ν : Measure R) [SFinite ν] :
    fullBatch L hL B J center hcenter ∘ₘ (μ.prod ν) =
      ((retainedBatch L hL B J center hcenter) ∘ₘ μ).prod ν :=
  (Measure.prod_comp_left).symm

theorem original_sample_preserved {H R : Type*} [MeasurableSpace H] [MeasurableSpace R]
    (center : Fin N → H → Point d) (hcenter : ∀ i, Measurable (center i))
    (μ : Measure (H × (∀ i, Raw d B i))) [SFinite μ]
    (ν : Measure R) [SFinite ν] :
    (fullBatch L hL B J center hcenter ∘ₘ (μ.prod ν)).map
      (Prod.map Prod.fst id) = μ.prod ν := by
  rw [whole_suffix_fresh, ← Measure.map_prod_map _ _ measurable_fst measurable_id,
    Measure.map_id, Measure.map_comp _ _ measurable_fst]
  rw [← Kernel.fst_eq, retainedBatch_original]
  rw [Measure.id_comp]

end AcceleratedLogConcave.Oracle.FreshChildBatchCoupling
