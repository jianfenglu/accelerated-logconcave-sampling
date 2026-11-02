import AcceleratedLogConcave.Oracle.MeanIncomingPrivateReferenceLaw
import AcceleratedLogConcave.Oracle.PrivateRetainedAccuracy
import AcceleratedLogConcave.Oracle.SourceMeanBuildRms

/-! Actual embedded private error on the full incoming mean coupling. The
same restored private seed is used by the lower coupling and the executable
prefix; the stored-anchor multiplication is the literal backwardEnd R. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.MeanIncomingPrivateError
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open MeanIncomingPrivateCoupling
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (path : TailCut q p) :
    MeasurableSpace (Prefix d path) := prefixSpace d path
variable {m n a h d : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData) (N : ℕ)
local notation "host" => SourceMeanExecutable.program M nodes anchors seeds main final sampling N
local notation "cut" => MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N
local notation "Sample" => MeanIncomingCompletedLaw.History d × Tape d host
local notation "PrivateSeed" => (Point d × Tape d sampling.program) × Point d
variable (L : PrimitiveLaws d)
  (J : Kernel (Point d) ((Point d × Tape d sampling.program) × Point d)) [IsMarkovKernel J]

/-- Literal designated input, entire restored private tape, and actual
reference on the incoming prefix. -/
def prefixSource (z : MeanIncomingCompletedLaw.History d × Prefix d cut) : PrivateSeed :=
  ((z.1.1.2,consumed M nodes anchors seeds main final sampling N z.2),z.1.2)

theorem prefixSource_measurable : Measurable (prefixSource (d := d) M nodes anchors seeds main final sampling N) :=
  (measurable_fst.fst.snd.prodMk ((consumed_measurable M nodes anchors seeds main final sampling N).comp
    measurable_snd)).prodMk measurable_fst.snd

private theorem dirac_compProd_map {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] (κ : Kernel A B) [IsSFiniteKernel κ] (a : A) :
    (Measure.dirac a) ⊗ₘ κ = (κ a).map (Prod.mk a) := by
  ext s hs
  rw [Measure.dirac_compProd_apply hs,Measure.map_apply measurable_prodMk_left hs]

/-- Exact lower full-source/reference joint marginal at the actual body cut. -/
theorem prefixSource_law
    (hsource : J.fst=Kernel.const (Point d) (FreshChildRetainedCoupling.sourceLaw L sampling.program))
    (base : Point d) :
    (MeanIncomingCompletedLaw.bodyPrefixLaw M nodes anchors seeds main final sampling N L J base).map
      (prefixSource M nodes anchors seeds main final sampling N) = J base := by
  let drop : (Point d × (Point d × Tape d sampling.program)) × Point d → PrivateSeed :=
    fun z => (z.1.2,z.2)
  have hd : Measurable drop := measurable_fst.snd.prodMk measurable_snd
  have hc := consumed_measurable (d := d) M nodes anchors seeds main final sampling N
  have hm : Measurable (fun z : (((Point d × Point d) × Prefix d cut) × Point d) =>
      ((z.1.1.1,(z.1.1.2,consumed M nodes anchors seeds main final sampling N z.1.2)),z.2)) :=
    (measurable_fst.fst.fst.prodMk (measurable_fst.fst.snd.prodMk
      (hc.comp measurable_fst.snd))).prodMk measurable_snd
  have hp := congrArg (fun μ => μ.map drop)
    (consumed_joint_law M nodes anchors seeds main final sampling N L J hsource base)
  rw [Measure.map_map hd hm,Measure.map_map hd MeasurableEquiv.prodAssoc.symm.measurable,
    dirac_compProd_map,Measure.map_map (hd.comp MeasurableEquiv.prodAssoc.symm.measurable)
      measurable_prodMk_left] at hp
  change _ = (J base).map id at hp
  rw [Measure.map_id] at hp
  rw [MeanIncomingCompletedLaw.bodyPrefixLaw,Measure.map_map
    (prefixSource_measurable M nodes anchors seeds main final sampling N)
    (PrivateCausalAdvance.regroupPrefix_measurable cut)]
  exact hp

/-- The full original mean tape remains present; only its actual consumed
private slice is observed here. -/
def source (z : Sample) : PrivateSeed :=
  prefixSource M nodes anchors seeds main final sampling N
    (z.1,(split cut z.2).1)

include L in
theorem source_measurable : Measurable (source (d := d) M nodes anchors seeds main final sampling N) :=
  (prefixSource_measurable M nodes anchors seeds main final sampling N).comp
    (CausalTailHistory.measurable_unpack L cut).fst

/-- Actual incoming private occurrence has the exact complete lower joint;
this does not replace the full original sample by a new independent seed. -/
theorem source_law
    (hsource : J.fst=Kernel.const (Point d) (FreshChildRetainedCoupling.sourceLaw L sampling.program))
    (base : Point d) :
    (MeanIncomingCompletedLaw.kernel M nodes anchors seeds main final sampling N L J base).map
      (source M nodes anchors seeds main final sampling N) = J base := by
  let : IsProbabilityMeasure (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N)) :=
    tapeLaw_probability L _
  have hp : MeasurePreserving (CausalTailHistory.unpack cut)
      (MeanIncomingCompletedLaw.kernel M nodes anchors seeds main final sampling N L J base)
      ((MeanIncomingCompletedLaw.bodyPrefixLaw M nodes anchors seeds main final sampling N L J base).prod
        (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N))) :=
    ⟨CausalTailHistory.measurable_unpack L cut,
      MeanIncomingCompletedLaw.kernel_body_split M nodes anchors seeds main final sampling N L J base⟩
  have hs : MeasurePreserving (prefixSource M nodes anchors seeds main final sampling N)
      (MeanIncomingCompletedLaw.bodyPrefixLaw M nodes anchors seeds main final sampling N L J base) (J base) :=
    ⟨prefixSource_measurable M nodes anchors seeds main final sampling N,
      prefixSource_law M nodes anchors seeds main final sampling N L J hsource base⟩
  exact ((hs.comp measurePreserving_fst).comp hp).map_eq

variable (r σ Ds δ t w : ℝ) (privateShift : GaussianSlot sampling.program → ℝ)
  (G : Point d → Point d)

/-- Exact public private coefficients, with no table-match hypothesis. -/
theorem private_table : table M nodes anchors r σ Ds δ t w main final sampling ∘
    (prefixSlot (a := a) main final sampling ∘ PrefixPublicTable.privateSlot) = sampling.coefficient := by
  funext i
  simp only [Function.comp_apply,table_prefix,PrefixPublicTable.table_private]

/-- Full embedded Result, including its paid trace, equals the standalone
private execution on the same restored complete seed. -/
theorem private_run (x P : Point d) (ω : Tape d host) :
    run (sampling.program.embed (prefixSlot (a := a) main final sampling ∘ PrefixPublicTable.privateSlot)
      (.there .here) .here) G
      ⟨table M nodes anchors r σ Ds δ t w main final sampling,x,P⟩
      (SourceMeanShift.inputEnv x P) (ω.2.2.1 0) =
    run sampling.program G ⟨sampling.coefficient,x,P⟩ Env.empty
      (consumed M nodes anchors seeds main final sampling N (split cut ω).1) := by
  rw [run_embed_every_tape]
  rw [private_table]
  rfl

/-- The private result used by the literal full source build is the same
lower program at the exact source seed read by the retained conditional. -/
theorem privateResult_eq (x P : Point d) (ω : Tape d host) :
    SourceMeanBuildRms.privateResult M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift
      G x P ω =
    (run sampling.program G ⟨sampling.coefficient,x,P⟩ Env.empty
      (consumed M nodes anchors seeds main final sampling N (split cut ω).1)).value := by
  exact congrArg Result.value (private_run M nodes anchors seeds main final sampling N r σ Ds δ t w G x P ω)

/-- Actual standalone lower private error, with the full designated seed. -/
def lowerError (base : Point d) (z : PrivateSeed) : Point d :=
  (show Point d from (run sampling.program G ⟨sampling.coefficient,base,z.1.1⟩ Env.empty z.1.2).value)-z.2

/-- Actual embedded private error under the retained full incoming sample. -/
def error (base : Point d) (z : Sample) : Point d :=
  SourceMeanBuildRms.privateResult M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift
    G base z.1.1.2 z.2-z.1.2

/-- Actual difference of the two stored position anchors. Both are multiplied
by the same literal public backwardEnd R coefficient. -/
def anchorError (base : Point d) (z : Sample) : Point d :=
  backwardEnd M.R • (SourceMeanBuildRms.privateResult M nodes anchors seeds r σ Ds δ t w
    main final sampling N privateShift G base z.1.1.2 z.2) - backwardEnd M.R • z.1.2

theorem error_eq (base : Point d) :
    error M nodes anchors seeds main final sampling N r σ Ds δ t w privateShift G base =
      lowerError sampling G base ∘ source M nodes anchors seeds main final sampling N := by
  funext z
  exact congrArg (fun v : Point d => v-z.1.2)
    (privateResult_eq M nodes anchors seeds main final sampling N r σ Ds δ t w privateShift G base z.1.1.2 z.2)

theorem anchorError_eq (base : Point d) :
    anchorError M nodes anchors seeds main final sampling N r σ Ds δ t w privateShift G base =
      fun z => backwardEnd M.R • error M nodes anchors seeds main final sampling N r σ Ds δ t w privateShift G base z := by
  funext z
  exact (smul_sub _ _ _).symm

variable (hG : Measurable G)

include hG in
theorem lowerError_measurable (base : Point d) : Measurable (lowerError (d := d) sampling G base) := by
  have hp := CanonicalTapeMeasurability.program_point_of_measurable sampling.program G hG
    (fun _ : PrivateSeed => sampling.coefficient) (fun _ => base) (fun z => z.1.1) (fun z => z.1.2)
    measurable_const measurable_const measurable_fst.fst measurable_fst.snd
  exact hp.sub measurable_snd

include L hG in
theorem error_measurable (base : Point d) :
    Measurable (error M nodes anchors seeds main final sampling N r σ Ds δ t w privateShift G base) := by
  rw [error_eq]
  exact (lowerError_measurable sampling G hG base).comp
    (source_measurable M nodes anchors seeds main final sampling N L)

include hG in
/-- Equality of actual embedded and standalone lower error laws. The
conditional was evaluated at this very seed, not a replacement source. -/
theorem error_law
    (hsource : J.fst=Kernel.const (Point d) (FreshChildRetainedCoupling.sourceLaw L sampling.program))
    (base : Point d) :
    (MeanIncomingCompletedLaw.kernel M nodes anchors seeds main final sampling N L J base).map
      (error M nodes anchors seeds main final sampling N r σ Ds δ t w privateShift G base) =
        (J base).map (lowerError sampling G base) := by
  rw [error_eq,← Measure.map_map (lowerError_measurable sampling G hG base)
    (source_measurable M nodes anchors seeds main final sampling N L),
    source_law M nodes anchors seeds main final sampling N L J hsource base]

include hG in
/-- Exact L2 and squared-error transport from the actual LOWER private
retained coupling to the embedded private occurrence in the original mean tape. -/
theorem error_memLp_integral
    (hsource : J.fst=Kernel.const (Point d) (FreshChildRetainedCoupling.sourceLaw L sampling.program))
    (base : Point d) (hmem : MemLp (lowerError sampling G base) 2 (J base)) :
    ∃ _hi : MemLp (error M nodes anchors seeds main final sampling N r σ Ds δ t w privateShift G base) 2
      (MeanIncomingCompletedLaw.kernel M nodes anchors seeds main final sampling N L J base),
      (∫ z,‖error M nodes anchors seeds main final sampling N r σ Ds δ t w privateShift G base z‖^2
        ∂MeanIncomingCompletedLaw.kernel M nodes anchors seeds main final sampling N L J base) =
          ∫ z,‖lowerError sampling G base z‖^2 ∂J base := by
  exact PrivateCompletedRms.memLp_integral_of_law _ _ _ _
    (error_measurable M nodes anchors seeds main final sampling N L r σ Ds δ t w privateShift G hG base)
    (lowerError_measurable sampling G hG base)
    (error_law M nodes anchors seeds main final sampling N L J r σ Ds δ t w privateShift G hG hsource base) hmem

include hG in
/-- Literal stored-anchor scaling gives its exact squared payment. No
parent mean accuracy premise is used. -/
theorem anchorError_memLp_integral
    (hsource : J.fst=Kernel.const (Point d) (FreshChildRetainedCoupling.sourceLaw L sampling.program))
    (base : Point d) (hmem : MemLp (lowerError sampling G base) 2 (J base)) :
    ∃ _hi : MemLp (anchorError M nodes anchors seeds main final sampling N r σ Ds δ t w privateShift G base) 2
      (MeanIncomingCompletedLaw.kernel M nodes anchors seeds main final sampling N L J base),
      (∫ z,‖anchorError M nodes anchors seeds main final sampling N r σ Ds δ t w privateShift G base z‖^2
        ∂MeanIncomingCompletedLaw.kernel M nodes anchors seeds main final sampling N L J base) =
          (backwardEnd M.R)^2*(∫ z,‖lowerError sampling G base z‖^2 ∂J base) := by
  obtain ⟨he,hi⟩ := error_memLp_integral M nodes anchors seeds main final sampling N L J
    r σ Ds δ t w privateShift G hG hsource base hmem
  rw [anchorError_eq]
  have haes := ((error_measurable M nodes anchors seeds main final sampling N L r σ Ds δ t w
    privateShift G hG base).const_smul (backwardEnd M.R)).aestronglyMeasurable
      (μ := MeanIncomingCompletedLaw.kernel M nodes anchors seeds main final sampling N L J base)
  have hsq := (memLp_two_iff_integrable_sq_norm he.aestronglyMeasurable).1 he
  refine ⟨(memLp_two_iff_integrable_sq_norm haes).2 ?_,?_⟩
  · simpa only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] using hsq.const_mul ((backwardEnd M.R)^2)
  simp_rw [norm_smul,Real.norm_eq_abs,mul_pow, sq_abs]
  rw [integral_const_mul,hi]

include hG in
/-- A lower private squared payment transfers to the literal stored anchor. -/
theorem anchorError_square_bound
    (hsource : J.fst=Kernel.const (Point d) (FreshChildRetainedCoupling.sourceLaw L sampling.program))
    (base : Point d) (B : ℝ) (hmem : MemLp (lowerError sampling G base) 2 (J base))
    (hbound : (∫ z,‖lowerError sampling G base z‖^2 ∂J base)≤B^2) :
    ∃ _hi : MemLp (anchorError M nodes anchors seeds main final sampling N r σ Ds δ t w privateShift G base) 2
      (MeanIncomingCompletedLaw.kernel M nodes anchors seeds main final sampling N L J base),
      (∫ z,‖anchorError M nodes anchors seeds main final sampling N r σ Ds δ t w privateShift G base z‖^2
        ∂MeanIncomingCompletedLaw.kernel M nodes anchors seeds main final sampling N L J base) ≤
          (backwardEnd M.R*B)^2 := by
  obtain ⟨hm,he⟩ := anchorError_memLp_integral M nodes anchors seeds main final sampling N L J
    r σ Ds δ t w privateShift G hG hsource base hmem
  refine ⟨hm,?_⟩
  rw [he,mul_pow]
  exact mul_le_mul_of_nonneg_left hbound (sq_nonneg _)

end AcceleratedLogConcave.Oracle.MeanIncomingPrivateError
