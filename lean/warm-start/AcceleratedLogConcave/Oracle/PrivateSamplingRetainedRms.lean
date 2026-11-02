import AcceleratedLogConcave.Oracle.PrivateConditionalFlowConsumer
import AcceleratedLogConcave.Oracle.SourceMeanRetainedRms
import AcceleratedLogConcave.Oracle.MeanPaidFinalRms

/-! RMS propagation for the literal private sampling loop on an augmented
sample space. Phi/u use the actual setup position occurrence. Returned child
reference outputs may live on the augmentation; designated input draws are not
substituted for them. Lower-child bounds and quantitative residual bounds remain
explicit. No reference law or whole-parent accuracy is assumed or constructed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
namespace AcceleratedLogConcave.Oracle.PrivateSamplingRetainedRms
open MeasureTheory Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open SourceExecutableTables CovarianceSetup FixedTapeStability
open PrivateSamplingExecutionSchedule
open scoped BigOperators NNReal

variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
variable {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)
  (x : Point d) (hr : 0 < r)

def reference (i : Fin n) (ω : FullTape (d := d) S e r Ds main final N) : Point d :=
  PrivateConditionalFlowConsumer.nodePhi S e hF hell hlo hup x hr i ω.2.1

def reply (i : Fin n) (ω : FullTape (d := d) S e r Ds main final N) : Point d :=
  PrivateConditionalFlowConsumer.nodeReply S e hF hell hlo hup x hr i ω.2.1

/-- Literal initialization residual from the same complete tape. -/
def initialNoise (i : Fin n) (ω : FullTape (d := d) S e r Ds main final N) : Point d :=
  samplingNoise S r Ds • (show Point d from ((bodyTape S e r Ds main final N ω).1 i).1)

private theorem iterate_pullback {Ω Ξ : Type*}
    (b : Fin n → Ξ → Point d) (A C : Fin n → Fin n → ℝ)
    (eval : ℕ → Fin n → Ξ → Point d → Point d) (Z : ℕ → Fin n → Ξ → Point d)
    (init : Fin n → Ξ → Point d) (tape : Ω → Ξ) (k : ℕ) :
    SharedLayerRms.iterate (fun i ω => b i (tape ω)) A C
      (fun k i ω => eval k i (tape ω)) (fun k i ω => Z k i (tape ω))
      (fun i ω => init i (tape ω)) k =
      (fun i ω => SharedLayerRms.iterate b A C eval Z init k i (tape ω)) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [SharedLayerRms.iterate, ih]

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (G : Point d → Point d) (P : Point d)
  (tape : Ω → FullTape (d := d) S e r Ds main final N)
  (Gref : ℕ → Fin n → Ω → Point d)
local notation "A" => samplingMatrix S e r
local notation "rho" => samplingNoise S r Ds
local notation "Cmat" => residualRoot A rho (r^2)
local notation "σ" => RecursiveMeanPublicTable.mainWidth n r S.R Ds (r^2)
local notation "U0" => reply S e r Ds main final N hF hell hlo hup x hr
local notation "xStar" => (fun i ω => reference S e r Ds main final N hF hell hlo hup x hr i (tape ω))
local notation "U" => (fun i ω => U0 i (tape ω))
local notation "b0" => (fun i (ω : FullTape (d := d) S e r Ds main final N) => x+(r*S.mesh.location m (e i)) • (show Point d from ω.2.1))
local notation "b" => (fun i ω => b0 i (tape ω))
local notation "init0" => initial S e r Ds main final N x
local notation "init" => (fun i ω => init0 (tape ω) i)
local notation "nu0" => (fun i ω => initialNoise S e r Ds main final N i (tape ω))
local notation "eval0" => evaluator S e r Ds main final N G U0
local notation "eval" => (fun k i ω => eval0 k i (tape ω))
local notation "Z0" => residualNoise (d := d) S e r Ds main final N
local notation "Z" => (fun k i ω => Z0 k i (tape ω))
local notation "Pmain" => SourceMeanRetainedRms.finiteReference N Gref
local notation "X" => SharedLayerRms.iterate b A Cmat eval Z init
local notation "Y" => SharedLayerRms.benchmark xStar A Cmat σ Pmain Z nu0
local notation "H" => SharedLayerRms.childError eval Y U σ Pmain
local notation "res" => SharedLayerRms.residual b A U xStar
local notation "actual" => (fun i ω =>
  let st := PrivateSamplingTapeProjections.state (samplingConfig main final N) G
    (inp S e r Ds main final x P) (tape ω)
  storedPoint st.env (st.old i) - Y N i ω)

/-- The augmented space carries the unchanged full execution tape. All
reference fields use its actual setup seed. Only k<N child estimates are inputs;
there is no Gaussian, independence, marginal-law or absolute-state moment premise. -/
theorem retained_main_error_bound (κ : ℝ≥0) (aRow Rres : ℝ)
    (ha : 0 ≤ aRow) (hR : 0 ≤ Rres) (ε : ℕ → Fin n → ℝ)
    (hrow : ∀ i, ∑ j, |A i j| ≤ aRow)
    (hstable : ∀ i, ChildStable (main i).program (main i).coefficient G κ)
    (hmeas : ∀ k, k<N → ∀ i, AEStronglyMeasurable
      (fun ω => eval k i ω (X k i ω) - eval k i ω (Y k i ω)) μ)
    (hinit : ∀ i, MemLp (fun ω => init i ω - (xStar i ω + nu0 i ω)) 2 μ)
    (hres : ∀ i, MemLp (res i) 2 μ)
    (hresBound : ∀ i, ‖(hres i).toLp (res i)‖ ≤ Rres)
    (hchild : ∀ k, k<N → ∀ i, MemLp (H k i) 2 μ)
    (hchildBound : ∀ k (hk : k<N) i, ‖(hchild k hk i).toLp (H k i)‖ ≤ ε k i) :
    ∃ hactual : ∀ i, MemLp (actual i) 2 μ,
      Collocation.rawNodeErrorNorm μ actual hactual ≤
        ((κ : ℝ)*aRow)^N * Collocation.rawNodeErrorNorm μ
          (fun i ω => init i ω - (xStar i ω + nu0 i ω)) hinit +
        Collocation.forcingSum ((κ : ℝ)*aRow)
          (fun k => Rres + SharedLayerRms.childRowBudget A (SourceMeanExecutionRms.finiteBudget N ε) k) N := by
  have hn (k : ℕ) (hk : ¬k<N) (ω : Ω) :
      MeanExecutionSchedule.inputAt (fun i => (main i).size) (fun i => (main i).program)
        (finisher main final N) N (raw S e r Ds main final N (tape ω)) k = none :=
    MeanExecutionSchedule.inputAt_none _ _ _ N _ k (Nat.le_of_not_gt hk)
  have hm : ∀ k i, AEStronglyMeasurable
      (fun ω => eval k i ω (X k i ω) - eval k i ω (Y k i ω)) μ := by
    intro k i
    by_cases hk : k<N
    · exact hmeas k hk i
    · simpa only [evaluator,MeanExecutionSchedule.evaluator,hn k hk,sub_self] using
        (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : Ω => (0 : Point d)) μ)
  have hzero (k : ℕ) (hk : ¬k<N) (i : Fin n) : H k i = (fun _ => 0) := by
    funext ω
    simp only [SharedLayerRms.childError,evaluator,MeanExecutionSchedule.evaluator,
      hn k hk,SourceMeanRetainedRms.finiteReference,ite_eq_right hk,sub_self,smul_zero]
  have hc : ∀ k i, MemLp (H k i) 2 μ := by
    intro k i
    by_cases hk : k<N
    · exact hchild k hk i
    · rw [hzero k hk i]; exact MemLp.zero
  have hcb : ∀ k i, ‖(hc k i).toLp (H k i)‖ ≤ SourceMeanExecutionRms.finiteBudget N ε k i := by
    intro k i
    by_cases hk : k<N
    · simpa [SourceMeanExecutionRms.finiteBudget,hk] using hchildBound k hk i
    · simp [SourceMeanExecutionRms.finiteBudget,hk,hzero k hk i]
  obtain ⟨herr,hbound⟩ := SharedLayerRms.iterate_error_bound b xStar U init nu0 A Cmat eval
    Pmain Z σ μ κ aRow Rres ha hR (SourceMeanExecutionRms.finiteBudget N ε) hrow
    (fun k i ω => MeanExecutionSchedule.evaluator_lipschitz _ _ _ _ _ _ _ N
      (raw S e r Ds main final N) U0 κ hstable k i (tape ω)) hm hinit hres hresBound hc hcb
  have hs := state_old_eq_iterate S e r Ds main final N G x P U0
  have hi := iterate_pullback b0 A Cmat eval0 Z0 (fun i ω => init0 ω i) tape N
  have he : actual = (fun i ω => X N i ω - Y N i ω) := by
    funext i ω
    exact congrArg (fun z => z - Y N i ω)
      ((congrFun (congrFun hs i) (tape ω)).trans (congrFun (congrFun hi i) ω).symm)
  have hactual : ∀ i, MemLp (actual i) 2 μ := by rw [he]; exact herr N
  have heLp : (fun i => (hactual i).toLp (actual i)) =
      (fun i => (herr N i).toLp (fun ω => X N i ω - Y N i ω)) := by
    funext i
    apply Lp.ext
    filter_upwards [(hactual i).coeFn_toLp,(herr N i).coeFn_toLp] with ω ha hb
    rw [ha,hb]
    exact congrFun (congrFun he i) ω
  refine ⟨hactual,?_⟩
  change ‖fun i => (hactual i).toLp (actual i)‖ ≤ _
  rw [heLp]
  exact hbound N

/-- The fresh final child's exact transformed source tape, kept fixed when
its entering center is changed to the benchmark. -/
def finalSourceTape (ω : FullTape (d := d) S e r Ds main final N) (i : Fin n) :
    Tape d (final i).program :=
  let data := PrivateSamplingTapeProjections.finalData (samplingConfig main final N) G
    (inp S e r Ds main final x P) ω i
  transformedSourceTape (final i).program (final i).enumeration
    (childRoot rho (S.radius r (e i)) (final i).shiftVector) data.2.1 data.2.2

def finalEvaluator (ω : FullTape (d := d) S e r Ds main final N) (i : Fin n)
    (z : Point d) : Point d :=
  let data := PrivateSamplingTapeProjections.finalData (samplingConfig main final N) G
    (inp S e r Ds main final x P) ω i
  (run (final i).program G ⟨(final i).coefficient,z,data.1⟩ Env.empty
    (finalSourceTape S e r Ds main final N x G P ω i)).value

theorem finalValue_eq (ω : FullTape (d := d) S e r Ds main final N) (i : Fin n) :
    PrivateSamplingTapeProjections.finalValue (samplingConfig main final N) G
      (inp S e r Ds main final x P) ω i =
    let st := PrivateSamplingTapeProjections.state (samplingConfig main final N) G
      (inp S e r Ds main final x P) ω
    finalEvaluator S e r Ds main final N x G P ω i (storedPoint st.env (st.old i)) := by
  let cfg := samplingConfig main final N
  let input := inp S e r Ds main final x P
  let st := PrivateSamplingTapeProjections.state cfg G input ω
  have ht : input.coefficient ∘ cfg.finalSlots i =
      matrixTable (childRoot rho (S.radius r (e i)) (final i).shiftVector)
        (final i).coefficient := funext fun j => samplingTable_final S e r Ds main final i j
  have hv := congrArg (fun z : Result d .point => z.value) (run_freshChild (final i).program (final i).enumeration
    (cfg.finalSlots i) (st.old i) (cfg.finalDesignated i) (cfg.finalAuxiliary i)
    (childRoot rho (S.radius r (e i)) (final i).shiftVector) (final i).coefficient
    G input st.env ht (st.tape.1 i))
  exact hv

/-- The literal affine output: initial, residual and reserve coordinates are
the unchanged occurrences in the input tape. -/
theorem output_eq (ω : FullTape (d := d) S e r Ds main final N) :
    (run (SamplingExecutable.build S e r Ds main final N).program G
      (inp S e r Ds main final x P) Env.empty ω).value =
    let cfg := samplingConfig main final N
    let st := PrivateSamplingTapeProjections.state cfg G (inp S e r Ds main final x P) ω
    let z := PrivateSamplingTapeProjections.coordinates cfg ω
    (samplingEnd S.τ)⁻¹ • z (.inl ()) +
      (∑ i, samplingFinalWeight S e r i •
        finalEvaluator S e r Ds main final N x G P ω i (storedPoint st.env (st.old i))) +
      (samplingBeta S e r • z (.inr (.inr (.inl ()))) +
        (S.τ/2) • z (.inr (.inr (.inr ())))) := by
  let cfg := samplingConfig main final N
  let input := inp S e r Ds main final x P
  have hinv : input.coefficient cfg.invEnd = (samplingEnd S.τ)⁻¹ := by
    change samplingTable S e r Ds main final
      (scalarSlot main final (Fin.natAdd _ (Fin.natAdd _ (1 : Fin 4)))) = _
    simp [samplingTable_scalar,samplingScalarTable]
  have hw (i : Fin n) : input.coefficient (cfg.rowWeight i) = samplingFinalWeight S e r i := by
    change samplingTable S e r Ds main final
      (scalarSlot main final (Fin.natAdd _ (Fin.castAdd _ i))) = _
    simp [samplingTable_scalar,samplingScalarTable]
  have hbeta : input.coefficient cfg.beta = samplingBeta S e r := by
    change samplingTable S e r Ds main final
      (scalarSlot main final (Fin.natAdd _ (Fin.natAdd _ (2 : Fin 4)))) = _
    simp [samplingTable_scalar,samplingScalarTable]
  have hreserve : input.coefficient cfg.reserve = S.τ/2 := by
    change samplingTable S e r Ds main final
      (scalarSlot main final (Fin.natAdd _ (Fin.natAdd _ (3 : Fin 4)))) = _
    simp [samplingTable_scalar,samplingScalarTable]
  have he := PrivateSamplingTapeProjections.run_code_value cfg G input ω
  dsimp only [cfg,input] at he hinv hw hbeta hreserve
  simpa only [SamplingExecutable.build,hinv,hw,hbeta,hreserve,
    finalValue_eq S e r Ds main final N x G P ω] using he

local notation "XE" => (fun i ω =>
  let st := PrivateSamplingTapeProjections.state (samplingConfig main final N) G
    (inp S e r Ds main final x P) (tape ω)
  storedPoint st.env (st.old i))
local notation "FE" => (fun i ω => finalEvaluator S e r Ds main final N x G P (tape ω) i)
local notation "wf" => samplingFinalWeight S e r
local notation "width" => samplingFinalWidth S r
local notation "out" => (fun ω => (show Point d from
  (run (SamplingExecutable.build S e r Ds main final N).program
    G (inp S e r Ds main final x P) Env.empty (tape ω)).value))
local notation "background" => (fun ω =>
  let z := PrivateSamplingTapeProjections.coordinates (samplingConfig main final N) (tape ω)
  (samplingEnd S.τ)⁻¹ • z (.inl ()) +
    (samplingBeta S e r • z (.inr (.inr (.inl ()))) +
      (S.τ/2) • z (.inr (.inr (.inr ())))))

/-- Full literal private output propagation. The target keeps the actual
initial/residual/reserve blocks and the returned final child references at the
exact source finalWidth. Their Gaussian reference-law identification is separate. -/
theorem retained_output_error_bound (κ κf : ℝ≥0) (aRow Rres : ℝ)
    (ha : 0 ≤ aRow) (hR : 0 ≤ Rres) (ε : ℕ → Fin n → ℝ)
    (hrow : ∀ i, ∑ j, |A i j| ≤ aRow)
    (hstable : ∀ i, ChildStable (main i).program (main i).coefficient G κ)
    (hmeas : ∀ k, k<N → ∀ i, AEStronglyMeasurable
      (fun ω => eval k i ω (X k i ω) - eval k i ω (Y k i ω)) μ)
    (hinit : ∀ i, MemLp (fun ω => init i ω - (xStar i ω + nu0 i ω)) 2 μ)
    (hres : ∀ i, MemLp (res i) 2 μ)
    (hresBound : ∀ i, ‖(hres i).toLp (res i)‖ ≤ Rres)
    (hchild : ∀ k, k<N → ∀ i, MemLp (H k i) 2 μ)
    (hchildBound : ∀ k (hk : k<N) i, ‖(hchild k hk i).toLp (H k i)‖ ≤ ε k i)
    (Pref : Fin n → Ω → Point d) (εf : Fin n → ℝ)
    (hfinalStable : ∀ i, ChildStable (final i).program (final i).coefficient G κf)
    (hfinalMeas : ∀ i, AEStronglyMeasurable
      (fun ω => FE i ω (XE i ω) - FE i ω (Y N i ω)) μ)
    (hfinalChild : ∀ i, MemLp
      (fun ω => FE i ω (Y N i ω) - width • Pref i ω - U i ω) 2 μ)
    (hfinalBound : ∀ i, ‖(hfinalChild i).toLp
      (fun ω => FE i ω (Y N i ω) - width • Pref i ω - U i ω)‖ ≤ εf i) :
    let D := ((κ : ℝ)*aRow)^N * Collocation.rawNodeErrorNorm μ
      (fun i ω => init i ω - (xStar i ω + nu0 i ω)) hinit +
      Collocation.forcingSum ((κ : ℝ)*aRow)
        (fun k => Rres + SharedLayerRms.childRowBudget A (SourceMeanExecutionRms.finiteBudget N ε) k) N
    let outputError := fun ω => out ω -
      (background ω + ∑ i, wf i • (U i ω + width • Pref i ω))
    ∃ hout : MemLp outputError 2 μ,
      ‖hout.toLp outputError‖ ≤ (∑ i, |wf i|) * ((κf : ℝ)*D) + ∑ i, |wf i| * εf i := by
  dsimp only
  let D := ((κ : ℝ)*aRow)^N * Collocation.rawNodeErrorNorm μ
    (fun i ω => init i ω - (xStar i ω + nu0 i ω)) hinit +
    Collocation.forcingSum ((κ : ℝ)*aRow)
      (fun k => Rres + SharedLayerRms.childRowBudget A (SourceMeanExecutionRms.finiteBudget N ε) k) N
  obtain ⟨herr,hB⟩ := retained_main_error_bound S e r Ds main final N hF hell hlo hup x hr
    μ G P tape Gref κ aRow Rres ha hR ε hrow hstable hmeas hinit hres hresBound hchild hchildBound
  have hD (i : Fin n) : ‖(herr i).toLp (fun ω => XE i ω - Y N i ω)‖ ≤ D :=
    (norm_le_pi_norm (fun j => (herr j).toLp (fun ω => XE j ω - Y N j ω)) i).trans hB
  have hf (i : Fin n) (ω : Ω) : LipschitzWith κf (FE i ω) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simp only [dist_eq_norm]
    exact childStable_tape (final i).program (final i).coefficient G κf (hfinalStable i)
      (PrivateSamplingTapeProjections.finalData (samplingConfig main final N) G
        (inp S e r Ds main final x P) (tape ω) i).1 u v
      (finalSourceTape S e r Ds main final N x G P (tape ω) i)
  let target := fun i ω => U i ω + width • Pref i ω
  have hechild (i : Fin n) :
      (fun ω => FE i ω (Y N i ω) - (0 : ℝ) • (0 : Point d) - target i ω) =
      (fun ω => FE i ω (Y N i ω) - width • Pref i ω - U i ω) := by
    funext ω
    dsimp only [target]
    simp only [zero_smul,sub_zero]
    abel
  have hc (i : Fin n) : MemLp
      (fun ω => FE i ω (Y N i ω) - (0 : ℝ) • (0 : Point d) - target i ω) 2 μ := by
    rw [hechild]; exact hfinalChild i
  have hcb (i : Fin n) : ‖(hc i).toLp _‖ ≤ εf i := by
    simpa only [hechild] using hfinalBound i
  obtain ⟨hp,hpB⟩ := MeanPaidFinalRms.paid_error_bound μ 0 wf (fun _ => 0)
    (fun _ => (0 : Point d)) (fun _ _ => 0) target XE (Y N) id FE κf D εf
    hf herr hD hfinalMeas hc hcb
  have he : (fun ω => out ω - (background ω + ∑ i, wf i • (U i ω + width • Pref i ω))) =
      (fun ω => ((0 : ℝ) • (0 : Point d) + ∑ i, wf i • (FE i ω (XE i ω) - (0 : ℝ) • (0 : Point d))) -
        ((0 : ℝ) • (0 : Point d) + ∑ i, wf i • target i ω)) := by
    funext ω
    dsimp only
    rw [output_eq S e r Ds main final N x G P (tape ω)]
    dsimp only [target]
    simp only [zero_smul,sub_zero,zero_add]
    abel
  rw [he]
  exact ⟨hp,hpB⟩

theorem reference_eq (i : Fin n) (ω : FullTape (d := d) S e r Ds main final N) :
    reference S e r Ds main final N hF hell hlo hup x hr i ω =
      PrivateSamplingFlowResidual.reference S e r Ds main final N hF hell hlo hup x hr i ω :=
  PrivateConditionalFlowConsumer.nodePhi_eq_reference S e hF hell hlo hup x hr Ds main final N i ω

theorem reply_eq (i : Fin n) (ω : FullTape (d := d) S e r Ds main final N) :
    reply S e r Ds main final N hF hell hlo hup x hr i ω =
      PrivateSamplingFlowResidual.reply S e r Ds main final N hF hell hlo hup x hr i ω :=
  PrivateConditionalFlowConsumer.nodeReply_eq_reply S e hF hell hlo hup x hr Ds main final N i ω

/-- An augmented actual-tape projection supplies initial difference membership
from original flow analysis; no moment of the absolute entering state is needed. -/
theorem initial_error_memLp_of_projection (L : CanonicalTapeLaw.PrimitiveLaws d)
    (hL : L.pointDraw = ProbabilityTheory.stdGaussian (Point d)) (i : Fin n) :
    let : MeasurableSpace (FullTape (d := d) S e r Ds main final N) :=
      CanonicalTapeMeasurability.tapeSpace d _
    ∀ (_htape : MeasurePreserving tape μ
      (CanonicalTapeLaw.tapeLaw L (SamplingExecutable.build S e r Ds main final N).program)),
      MemLp (fun ω => init i ω - (xStar i ω + nu0 i ω)) 2 μ := by
  let : MeasurableSpace (FullTape (d := d) S e r Ds main final N) :=
    CanonicalTapeMeasurability.tapeSpace d _
  dsimp only
  intro htape
  have hm := PrivateSamplingFlowResidual.initial_error_memLp S e r Ds main final N
    hF hell hlo hup x hr L hL i
  have hc := hm.comp_measurePreserving htape
  apply hc.ae_eq
  filter_upwards with ω
  simp only [Function.comp_apply,initialNoise,reference_eq]

/-- The same augmented full-tape projection supplies the actual quadrature
residual's L2 membership. Its small quantitative budget is a separate obligation. -/
theorem residual_memLp_of_projection (L : CanonicalTapeLaw.PrimitiveLaws d)
    (hL : L.pointDraw = ProbabilityTheory.stdGaussian (Point d)) (i : Fin n) :
    let : MeasurableSpace (FullTape (d := d) S e r Ds main final N) :=
      CanonicalTapeMeasurability.tapeSpace d _
    ∀ (_htape : MeasurePreserving tape μ
      (CanonicalTapeLaw.tapeLaw L (SamplingExecutable.build S e r Ds main final N).program)),
      MemLp (res i) 2 μ := by
  let : MeasurableSpace (FullTape (d := d) S e r Ds main final N) :=
    CanonicalTapeMeasurability.tapeSpace d _
  dsimp only
  intro htape
  have hm := PrivateSamplingFlowResidual.residual_memLp S e r Ds main final N
    hF hell hlo hup x hr L hL i
  have hc := hm.comp_measurePreserving htape
  apply hc.ae_eq
  filter_upwards with ω
  simp only [Function.comp_apply,SharedLayerRms.residual,reference_eq,reply_eq]

end AcceleratedLogConcave.Oracle.PrivateSamplingRetainedRms
