import AcceleratedLogConcave.Oracle.PrivateCausalLayer
import AcceleratedLogConcave.Oracle.ResidualGaussianRecombination

/-! Consume the original current residual and deterministic row batches.
The next focus follows the same finite program and retains every source slot.
Comparison noise below uses adjoined child references, never designated draws. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Oracle.PrivateCausalAdvance
open AffineLowering TapeLowering NoisyLayer SourceMeanLayer RecursiveMeanProgram
open RecursiveMeanContinuation TailOccurrenceCut TailCut GeneralMainFocus PrivateCausalLayer
open CanonicalTapeLaw CanonicalTapeMeasurability

section Focus
variable {n C d : ℕ} {Ξ Γ Δ : Ctx} {τ : Ty}
  (c : Fin n → ℕ) (p : ∀ i, Program (c i) .point)
  (slots : Fin (publicSize c p) → Fin C)
  (en : ∀ i, GaussianSlot (p i) ≃ Fin (tapeShape (p i)).gaussianBlocks)
  (outer : ℕ → Origin) (designated residual : ℕ → Fin n → Origin)
  (auxiliary : ℕ → ∀ i, Fin (tapeShape (p i)).gaussianBlocks → Origin)
  (finish : ∀ {Δ : Ctx}, (Fin n → Ref Δ .point) →
    (Fin n → Ref Δ .point) → RefMap Ξ Δ → Prog C Δ τ)
  {host : Prog C Γ τ} (remaining : ℕ) (old direct : Fin n → Ref Δ .point)
  (saved : RefMap Ξ Δ)
  (cut : TailCut (iterateThen c p slots en outer designated residual auxiliary finish
    (remaining+1) old direct saved) host)

/-- The exact next suffix after all three current batches, including the
deterministic row tapes. At remaining=0 this is the original paid finish. -/
def afterLayer : TailCut
    (iterateThen c p slots en outer designated residual auxiliary finish remaining
      batchRef (fun j => preserveDirect (direct j)) (fun q => preserveDirect (saved q))) host :=
  afterBatch (afterBatch (afterBatch cut))

/-- Literal interpreter continuation at the exact consumed-layer cut. -/
theorem run_afterLayer (G : Point d → Point d) (input : Inputs d C)
    (env : Env d Γ) (ω : Tape d host) :
    (run host G input env ω).value =
      (run (iterateThen c p slots en outer designated residual auxiliary finish remaining
        batchRef (fun j => preserveDirect (direct j)) (fun q => preserveDirect (saved q)))
        G input (envAt G input (afterLayer c p slots en outer designated residual auxiliary
          finish remaining old direct saved cut) env
          (split (afterLayer c p slots en outer designated residual auxiliary finish
            remaining old direct saved cut) ω).1)
        (split (afterLayer c p slots en outer designated residual auxiliary finish
          remaining old direct saved cut) ω).2).value :=
  run_split_value G input _ env ω

/-- Build the next actual main-child focus without assuming an equality with
a separately generated cursor. Positive remaining is precisely the horizon guard. -/
def nextFocus (f : Focus c p slots en outer designated residual auxiliary finish host)
    (hf : 0 < f.remainingAfter) : Focus c p slots en outer designated residual auxiliary finish host where
  remainingAfter := f.remainingAfter-1
  ctx := nextCtx n f.ctx
  old := batchRef
  direct j := preserveDirect (f.direct j)
  saved q := preserveDirect (f.saved q)
  cut := by
    rw [Nat.sub_add_cancel hf]
    exact afterLayer c p slots en outer designated residual auxiliary finish
      f.remainingAfter f.old f.direct f.saved f.cut

theorem nextFocus_remaining (f : Focus c p slots en outer designated residual auxiliary finish host)
    (hf : 0 < f.remainingAfter) :
    (nextFocus c p slots en outer designated residual auxiliary finish f hf).remainingAfter =
      f.remainingAfter-1 := rfl

/-- Read the actual current residual instructions after consuming the rows.
The child reference vector is not read from this source prefix. -/
def currentResidual (h : Prefix d
    (afterLayer c p slots en outer designated residual auxiliary finish remaining old direct saved cut)) :
    Fin n → Point d :=
  let rows := batchParts (afterBatch (afterBatch cut)) h
  let noise := batchParts (afterBatch cut) rows.1
  fun i => (noise.2 i).1

theorem currentResidual_on_original (ω : Tape d host) (i : Fin n) :
    currentResidual c p slots en outer designated residual auxiliary finish remaining old direct saved cut
      (split (afterLayer c p slots en outer designated residual auxiliary finish remaining old direct saved cut) ω).1 i =
        ((split (afterBatch cut) ω).2.1 i).1 := by
  simp only [currentResidual,afterLayer,split_afterBatch,batchParts_append]

theorem currentResidual_measurable :
    let : MeasurableSpace (Prefix d
      (afterLayer c p slots en outer designated residual auxiliary finish remaining old direct saved cut)) :=
        prefixSpace d _
    Measurable (currentResidual (d := d) c p slots en outer designated residual auxiliary finish remaining old direct saved cut) := by
  let : MeasurableSpace (Prefix d
    (afterLayer c p slots en outer designated residual auxiliary finish remaining old direct saved cut)) := prefixSpace d _
  let : MeasurableSpace (Prefix d (afterBatch cut)) := prefixSpace d _
  let : MeasurableSpace (Prefix d (afterBatch (afterBatch cut))) := prefixSpace d _
  let : MeasurableSpace (Prefix d (afterBatch (afterBatch (afterBatch cut)))) := prefixSpace d _
  have hr := measurable_batchParts (d := d) (afterBatch (afterBatch cut))
  have hn := (measurable_batchParts (d := d) (afterBatch cut)).comp hr.fst
  exact Measurable.of_eval fun i => ((measurable_pi_apply i).comp hn.snd).fst

end Focus

section History
variable {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty} {p : Prog c Γ τ} {q : Prog c Δ σ}
  {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  (L : PrimitiveLaws d) (cut : TailCut q p)
local instance : MeasurableSpace (Tape d p) := tapeSpace d p
local instance : MeasurableSpace (Tape d q) := tapeSpace d q
local instance : MeasurableSpace (Prefix d cut) := prefixSpace d cut

/-- Reassociate the newly adjoined references into augmented history while
keeping the original source tape verbatim. -/
def regroupOriginal (z : (A × Tape d p) × B) : (A × B) × Tape d p :=
  ((z.1.1,z.2),z.1.2)

def regroupPrefix (z : (A × Prefix d cut) × B) : (A × B) × Prefix d cut :=
  ((z.1.1,z.2),z.1.2)

theorem regroupOriginal_measurable : Measurable (regroupOriginal (d := d) (p := p) (A := A) (B := B)) :=
  (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd

theorem regroupPrefix_measurable : Measurable (regroupPrefix (d := d) (A := A) (B := B) cut) :=
  (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd

/-- The exact cut law survives this reassociation. No independence between
old history and new references is asserted or required. -/
theorem regroup_cut_law (ρ : Measure ((A × Tape d p) × B))
    (ν : Measure ((A × Prefix d cut) × B)) [SFinite ν]
    (hcut : ρ.map (CausalTailHistory.unpackExtended cut) = ν.prod (tapeLaw L q)) :
    (ρ.map regroupOriginal).map (CausalTailHistory.unpack cut) =
      (ν.map (regroupPrefix cut)).prod (tapeLaw L q) := by
  let : IsProbabilityMeasure (tapeLaw L q) := tapeLaw_probability L _
  have hm := (regroupPrefix_measurable (d := d) (A := A) (B := B) cut).prodMap
    (measurable_id : Measurable (id : Tape d q → Tape d q))
  have h := congrArg (fun μ => μ.map (Prod.map (regroupPrefix cut) id)) hcut
  rw [Measure.map_map hm (CausalTailHistory.measurable_unpackExtended L cut),
    ← Measure.map_prod_map _ _ (regroupPrefix_measurable (d := d) cut) measurable_id,
    Measure.map_id] at h
  rw [Measure.map_map (CausalTailHistory.measurable_unpack L cut) regroupOriginal_measurable]
  exact h

end History

section Rows
variable {d c n₁ n₂ : ℕ} {Γ Δ : Ctx} {τ σ : Ty} {p : Prog c Γ τ}
  {o₁ o₂ : Origin} {first : Fin n₁ → Prog c Δ .point}
  {second : Fin n₂ → Prog c (replyCtx n₁ Δ) .point}
  {next : Prog c (replyCtx n₂ (replyCtx n₁ Δ)) σ}
  (L : PrimitiveLaws d) (cut : TailCut (.batch o₁ first (.batch o₂ second next)) p)
  {A : Type*} [MeasurableSpace A]
local instance tapeSpace' {c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance : MeasurableSpace (Prefix d cut) := prefixSpace d _
local instance : MeasurableSpace (Prefix d (afterBatch cut)) := prefixSpace d _
local instance : MeasurableSpace (Prefix d (afterBatch (afterBatch cut))) := prefixSpace d _

/-- Consume both actual batches, including every unit in the deterministic
row tape. This is the residual/row advance used after reference augmentation. -/
theorem consume_two_batches (oldLaw : Measure (A × Tape d p))
    (μ : Measure (A × Prefix d cut)) [SFinite μ]
    (hsplit : oldLaw.map (CausalTailHistory.unpack cut) =
      μ.prod (tapeLaw L (.batch o₁ first (.batch o₂ second next)))) :
    oldLaw.map (CausalTailHistory.unpack (afterBatch (afterBatch cut))) =
      (advancedLaw L (afterBatch cut) (advancedLaw L cut μ)).prod (tapeLaw L next) := by
  exact advanced_split_of_split L (afterBatch cut) oldLaw (advancedLaw L cut μ)
    (advanced_split_of_split L cut oldLaw μ hsplit)

end Rows

section ResidualLaw
variable {d c n : ℕ} {Γ : Ctx} (L : PrimitiveLaws d) (origins : Fin n → Origin)
local instance : IsProbabilityMeasure L.pointDraw := L.point_probability
local instance drawTapeSpace (i : Fin n) : MeasurableSpace
    (Tape d (residualDraw (c := c) (Γ := Γ) (origins i))) := tapeSpace d _
local instance drawTapeProbability (i : Fin n) : IsProbabilityMeasure
    (tapeLaw L (residualDraw (c := c) (Γ := Γ) (origins i))) := tapeLaw_probability L _

/-- Current residuals are the first coordinates of their literal Gaussian
instructions; all unit coordinates are still present in the source law. -/
theorem residualBatch_preserving :
    MeasurePreserving
      (fun t : (∀ i, Tape d (residualDraw (c := c) (Γ := Γ) (origins i))) =>
        fun i => (show Point d from (t i).1))
      (Measure.pi fun i => tapeLaw L (residualDraw (c := c) (Γ := Γ) (origins i)))
      (Measure.pi fun _ : Fin n => L.pointDraw) := by
  apply measurePreserving_pi
    (fun i => tapeLaw L (residualDraw (c := c) (Γ := Γ) (origins i)))
    (fun _ : Fin n => L.pointDraw)
    (f := fun i t => (show Point d from t.1))
  intro i
  change MeasurePreserving (Prod.fst : Point d × PUnit → Point d)
    (L.pointDraw.prod (Measure.dirac PUnit.unit)) L.pointDraw
  exact measurePreserving_fst

end ResidualLaw

section ActualResidual
variable {d c n : ℕ} {Γ Δ : Ctx} {τ σ : Ty} {host : Prog c Γ τ} {o : Origin}
  (origins : Fin n → Origin) (next : Prog c (replyCtx n Δ) σ)
  (cut : TailCut (.batch o (fun i => residualDraw (origins i)) next) host)
  {A H : Type*} [MeasurableSpace A] [MeasurableSpace H]
  (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
local instance tapeSpace'' {c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance : MeasurableSpace (Prefix d cut) := prefixSpace d _
local instance : IsProbabilityMeasure (tapeLaw L next) := tapeLaw_probability L _
local instance : ∀ i, IsProbabilityMeasure
    (tapeLaw L (residualDraw (c := c) (Γ := Δ) (origins i))) := fun _ => tapeLaw_probability L _
include hL

/-- The actual unread residual block remains independent of the already
adjoined reference vector jointly with its coarse datum. All old correlations
remain in rho and nu; only their stated projections are used. -/
theorem actual_residual_joint
    (ρ : Measure ((A × Tape d host) × (Fin n → Point d)))
    (ν : Measure ((A × Prefix d cut) × (Fin n → Point d))) [SFinite ν]
    (ζ : Measure H) [SFinite ζ]
    (coarse : A × Prefix d cut → H) (hc : Measurable coarse)
    (hcut : ρ.map (CausalTailHistory.unpackExtended cut) =
      ν.prod (tapeLaw L (.batch o (fun i => residualDraw (origins i)) next)))
    (href : ν.map (fun z => (coarse z.1,z.2)) =
      ζ.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d))) :
    MeasurePreserving
      (fun z : (A × Tape d host) × (Fin n → Point d) =>
        ((coarse (z.1.1,(split cut z.1.2).1),z.2),
          fun i => (show Point d from ((split cut z.1.2).2.1 i).1))) ρ
      ((ζ.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d))).prod
        (Measure.pi fun _ : Fin n => stdGaussian (Point d))) := by
  have hp : MeasurePreserving (fun z : (A × Prefix d cut) × (Fin n → Point d) =>
      (coarse z.1,z.2)) ν
      (ζ.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d))) :=
    ⟨(hc.comp measurable_fst).prodMk measurable_snd,href⟩
  have hz := (residualBatch_preserving (c := c) (Γ := Δ) L origins).comp
    (measurePreserving_fst (μ := Measure.pi fun i =>
      tapeLaw L (residualDraw (c := c) (Γ := Δ) (origins i))) (ν := tapeLaw L next))
  rw [hL] at hz
  have hs : MeasurePreserving (CausalTailHistory.unpackExtended cut) ρ
      (ν.prod (tapeLaw L (.batch o (fun i => residualDraw (origins i)) next))) :=
    ⟨CausalTailHistory.measurable_unpackExtended L cut,hcut⟩
  exact (hp.prod hz).comp hs

/-- The next Gaussian comparison is a theorem of the retained child-reference
law, the actual fresh residual instructions, and the prescribed covariance.
Neither the old full history nor the original momentum is conditioned away. -/
theorem actual_recombine_law
    (ρ : Measure ((A × Tape d host) × (Fin n → Point d)))
    (ν : Measure ((A × Prefix d cut) × (Fin n → Point d))) [SFinite ν]
    (ζ : Measure H) [SFinite ζ]
    (coarse : A × Prefix d cut → H) (hc : Measurable coarse)
    (hcut : ρ.map (CausalTailHistory.unpackExtended cut) =
      ν.prod (tapeLaw L (.batch o (fun i => residualDraw (origins i)) next)))
    (href : ν.map (fun z => (coarse z.1,z.2)) =
      ζ.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)))
    (M : CovarianceSetup.Mat n) {rho a : ℝ} (hrho : 0 < rho) (ha : 0 < a)
    (hM : ∀ i, ∑ j, |M i j| ≤ a) :
    ρ.map (fun z => (coarse (z.1.1,(split cut z.1.2).1),
      ResidualGaussianRecombination.recombine M rho a
        (z.2,fun i => (show Point d from ((split cut z.1.2).2.1 i).1)))) =
      ζ.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) := by
  exact ((ResidualGaussianRecombination.recombine_coarse_assoc_preserving ζ M hrho ha hM).comp
    (actual_residual_joint origins next cut L hL ρ ν ζ coarse hc hcut href)).map_eq

end ActualResidual

section Comparison
open Numerics.AffineGraph CovarianceSetup SourceExecutableTables
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node) (r Ds : ℝ)
local instance comparisonTapeSpace {c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p

/-- The reference vector of the completed child batch and the actual current
residual vector generate the next comparison. These are distinct inputs. -/
def nextComparison (Gref Zres : Fin n → Point d) (i : Fin n) : Point d :=
  (samplingNoise S r Ds)⁻¹ •
    ((∑ j, samplingMatrix S e r i j •
      (RecursiveMeanPublicTable.mainWidth n r S.R Ds (r^2) • Gref j)) +
      ∑ j, residualRoot (samplingMatrix S e r) (samplingNoise S r Ds) (r^2) i j • Zres j)

theorem nextComparison_measurable :
    Measurable (fun z : (Fin n → Point d) × (Fin n → Point d) => nextComparison (d := d) S e r Ds z.1 z.2) := by
  unfold nextComparison
  fun_prop

/-- Exact comparison state reconstruction; division is only by the proved
positive public noise scale, never by a source reference coordinate. -/
theorem noise_mul_nextComparison (hr : 0 < r) (hDs : 0 < Ds)
    (Gref Zres : Fin n → Point d) (i : Fin n) :
    samplingNoise S r Ds • nextComparison S e r Ds Gref Zres i =
      (∑ j, samplingMatrix S e r i j •
        (RecursiveMeanPublicTable.mainWidth n r S.R Ds (r^2) • Gref j)) +
        ∑ j, residualRoot (samplingMatrix S e r) (samplingNoise S r Ds) (r^2) i j • Zres j := by
  rw [nextComparison,smul_smul,mul_inv_cancel₀
    (ne_of_gt (RecursiveExecutableDomain.sampling_noise_pos S r Ds hr hDs)),one_smul]

theorem nextComparison_preserving (hm : 0 < m) (hr : 0 < r) (hDs : 0 < Ds) :
    MeasurePreserving
      (fun z : (Fin n → Point d) × (Fin n → Point d) => nextComparison S e r Ds z.1 z.2)
      ((Measure.pi fun _ : Fin n => stdGaussian (Point d)).prod
        (Measure.pi fun _ : Fin n => stdGaussian (Point d)))
      (Measure.pi fun _ : Fin n => stdGaussian (Point d)) :=
  ResidualGaussianRecombination.sampling_recombine_preserving S e r Ds hm hr hDs

/-- Actual-source specialization of the chronological comparison update.
All covariance and row-mass guards are discharged for the source sampling
matrix; only the already proved entering cut/reference laws are used. -/
theorem actual_sampling_nextComparison_law
    {c : ℕ} {Γ Δ : Ctx} {τ υ : Ty} {host : Prog c Γ τ} {o : Origin}
    (origins : Fin n → Origin) (next : Prog c (replyCtx n Δ) υ)
    (cut : TailCut (.batch o (fun i => residualDraw (origins i)) next) host)
    {A H : Type*} [MeasurableSpace A] [MeasurableSpace H]
    (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
    (hm : 0 < m) (hr : 0 < r) (hDs : 0 < Ds) :
    let : MeasurableSpace (Tape d host) := tapeSpace d host
    let : MeasurableSpace (Prefix d cut) := prefixSpace d cut
    ∀ (ρ : Measure ((A × Tape d host) × (Fin n → Point d)))
      (ν : Measure ((A × Prefix d cut) × (Fin n → Point d))) [SFinite ν]
      (ζ : Measure H) [SFinite ζ]
      (coarse : A × Prefix d cut → H) (_hc : Measurable coarse)
      (_hcut : ρ.map (CausalTailHistory.unpackExtended cut) =
        ν.prod (tapeLaw L (.batch o (fun i => residualDraw (origins i)) next)))
      (_href : ν.map (fun z => (coarse z.1,z.2)) =
        ζ.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d))),
    ρ.map (fun z => (coarse (z.1.1,(split cut z.1.2).1),
      nextComparison S e r Ds z.2
        (fun i => (show Point d from ((split cut z.1.2).2.1 i).1)))) =
      ζ.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) := by
  let : MeasurableSpace (Tape d host) := tapeSpace d host
  let : MeasurableSpace (Prefix d cut) := prefixSpace d cut
  dsimp only
  intro ρ ν _ ζ _ coarse hc hcut href
  exact actual_recombine_law origins next cut L hL ρ ν ζ coarse hc hcut href
    (samplingMatrix S e r) (RecursiveExecutableDomain.sampling_noise_pos S r Ds hr hDs)
    (sq_pos_of_pos hr) (FixedTapeSampling.sampling_matrix_mass_le S e r hm hr.le)

end Comparison
end AcceleratedLogConcave.Oracle.PrivateCausalAdvance
