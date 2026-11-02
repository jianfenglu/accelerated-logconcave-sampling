import AcceleratedLogConcave.Root.CoolingExecutable
import AcceleratedLogConcave.Oracle.TailCutExecution
import AcceleratedLogConcave.Probability.CanonicalNativeTapeLaw
import AcceleratedLogConcave.Channels.CoolingLocalKL

/-! Exact factorization of the literal final reserve from the entire actual
pre-reserve output. The syntax cut consumes all original layers, final children
and the final residual. The resulting decoder law uses the unchanged full
source tape and proves no approximation or reference-coupling bound. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.CoolingReserveLaw
open Oracle Oracle.TapeLowering Oracle.TailOccurrenceCut Oracle.TailOccurrenceCut.TailCut
open Oracle.CanonicalTapeLaw Oracle.CanonicalTapeMeasurability
variable {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty} {p : Prog c Γ τ} {q : Prog c Δ σ}

def liftSlot : {Γ : Ctx} → {τ : Ty} → {p : Prog c Γ τ} →
    TailCut q p → GaussianSlot q → GaussianSlot p
  | _, _, _, .here, j => j
  | _, _, _, .step _ _ _ t, j => .inr (liftSlot t j)
  | _, _, _, .batch _ _ _ t, j => .inr (liftSlot t j)

theorem split_liftSlot (cut : TailCut q p) (j : GaussianSlot q) (ω : Tape d p) :
    (splitTape p ω).1 (liftSlot cut j) = (splitTape q (split cut ω).2).1 j := by
  induction cut with
  | here => rfl
  | step o a next cut ih => exact ih ω.2
  | batch o children next cut ih => exact ih ω.2

/-- The whole unread suffix factors before its Gaussian first coordinate is selected. -/
theorem prefix_gaussian_joint (L : PrimitiveLaws d) {o : Origin}
    {next : Prog c (.point :: Δ) σ}
    (cut : TailCut (.step o .gaussian next) p)
    (f : Prefix d cut → Point d)
    (hf : @Measurable _ _ (prefixSpace d cut) _ f) :
    let : MeasurableSpace (Tape d p) := tapeSpace d p
    let : MeasurableSpace (Prefix d cut) := prefixSpace d cut
    (tapeLaw L p).map (fun ω => (f (split cut ω).1,(show Point d from (split cut ω).2.1))) =
      ((prefixLaw L cut).map f).prod L.pointDraw := by
  let : MeasurableSpace (Tape d p) := tapeSpace d p
  let : MeasurableSpace (Prefix d cut) := prefixSpace d cut
  let : MeasurableSpace (Tape d next) := tapeSpace d next
  let : MeasurableSpace (Tape d (.step o .gaussian next)) := tapeSpace d _
  let : IsProbabilityMeasure (prefixLaw L cut) := prefixLaw_probability L cut
  let : IsProbabilityMeasure L.pointDraw := L.point_probability
  let : IsProbabilityMeasure (tapeLaw L next) := tapeLaw_probability L next
  have hs := measurePreserving_split L cut
  have hfst : Measurable (fun ω : Tape d (.step o .gaussian next) => (show Point d from ω.1)) := by
    change Measurable (Prod.fst : Point d × Tape d next → Point d)
    exact measurable_fst
  have hm : Measurable (fun z : Prefix d cut × Tape d (.step o .gaussian next) =>
      (f z.1,(show Point d from z.2.1))) := hf.prodMap hfst
  change (tapeLaw L p).map ((fun z : Prefix d cut × Tape d (.step o .gaussian next) =>
      (f z.1,(show Point d from z.2.1))) ∘ split cut) = _
  rw [← Measure.map_map hm hs.measurable, hs.map_eq]
  change ((prefixLaw L cut).prod (L.pointDraw.prod (tapeLaw L next))).map
    (Prod.map f Prod.fst) = _
  rw [← Measure.map_prod_map _ _ hf measurable_fst]
  congr 1
  change ((L.pointDraw.prod (tapeLaw L next)).fst) = L.pointDraw
  exact Measure.fst_prod



open Oracle.AffineLowering Oracle.NoisyLayer Oracle.SourceMeanLayer
open Oracle.RecursiveMeanProgram Oracle.RecursiveMeanContinuation Oracle.PrivateSamplingProgram
open Oracle.SourceExecutableTables
open scoped BigOperators NNReal

variable {n C : ℕ} {cm cf : Fin n → ℕ} {pm : ∀ i, Program (cm i) .point}
  {pf : ∀ i, Program (cf i) .point} (cfg : Config n C cm cf pm pf)

def reserveCode {Ξ : Ctx} (out : Ref Ξ .point) : Prog C (.point :: replyCtx n Ξ) .point :=
  .step cfg.finalReserve .gaussian
    (affineRow [] (.there (.there (RefMap.shiftMany n out)))
      ((List.ofFn fun i => (cfg.rowWeight i,.there (.there (batchRef i)))) ++
        [(cfg.beta,.there .here),(cfg.reserve,.here)]))

structure ReserveFocus {Γ : Ctx} (host : Prog C Γ .point) where
  ctx : Ctx
  out : Ref ctx .point
  cut : TailCut (reserveCode cfg out) host

def finishReserveCut {Ξ : Ctx} (old : Fin n → Ref Ξ .point) (out : Ref Ξ .point) :
    TailCut (reserveCode cfg out) (finish cfg old out) :=
  .batch _ _ _ (.step _ _ _ .here)

def loopReserveFocus {Ξ : Ctx} (out : Ref Ξ .point) (N : ℕ) {Γ : Ctx}
    (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ) :
    ReserveFocus cfg (iterateThen cm pm cfg.mainSlots cfg.mainEquiv cfg.layerOrigin
      cfg.mainDesignated cfg.mainResidual cfg.mainAuxiliary
      (fun old _ saved => finish cfg old (saved out)) N old direct saved) :=
  let f := atFinish cm pm cfg.mainSlots cfg.mainEquiv cfg.layerOrigin
    cfg.mainDesignated cfg.mainResidual cfg.mainAuxiliary
    (fun old _ saved => finish cfg old (saved out)) N old direct saved
  ⟨f.ctx,f.saved out,(finishReserveCut cfg f.old (f.saved out)).trans f.cut⟩

def privateReserveFocus : ReserveFocus cfg (code cfg) := by
  let f := loopReserveFocus cfg (RefMap.shiftMany n (.here : Ref [.point,.scalar,.point,.point] .point))
    cfg.layers batchRef
    (fun i => RefMap.shiftMany n (RefMap.shiftMany n (batchRef i)))
    (fun q => RefMap.shiftMany n (RefMap.shiftMany n q))
  refine ⟨f.ctx,f.out,?_⟩
  unfold code body initializeCenters
  exact .step _ _ _ (.step _ _ _ (.step _ _ _ (.step _ _ _
    (.batch _ _ _ (.batch _ _ _ (.batch _ _ _ f.cut))))))

private theorem liftSlot_trans {c : ℕ} {Γ Δ Ξ : Ctx} {τ σ υ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} {r : Prog c Ξ υ}
    (inner : TailCut r q) (outer : TailCut q p) (j : GaussianSlot r) :
    liftSlot (inner.trans outer) j = liftSlot outer (liftSlot inner j) := by
  induction outer with
  | here => rfl
  | step o a next cut ih => exact congrArg Sum.inr ih
  | batch o children next cut ih => exact congrArg Sum.inr ih

private theorem atFinish_slot {Ξ : Ctx} (out : Ref Ξ .point) (N : ℕ) {Γ : Ctx}
    (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ)
    (j : Oracle.PrivateSamplingTapeProjections.FinalIndex n) :
    let f := atFinish cm pm cfg.mainSlots cfg.mainEquiv cfg.layerOrigin
      cfg.mainDesignated cfg.mainResidual cfg.mainAuxiliary
      (fun old _ saved => finish cfg old (saved out)) N old direct saved
    liftSlot f.cut (Oracle.PrivateSamplingTapeProjections.finishSlot cfg f.old (f.saved out) j) =
      Oracle.PrivateSamplingTapeProjections.loopSlot cfg out N old direct saved j := by
  induction N generalizing Γ with
  | zero => rfl
  | succ N ih =>
      exact congrArg Sum.inr (congrArg Sum.inr (congrArg Sum.inr
        (ih batchRef (fun i => preserveDirect (direct i)) (fun q => preserveDirect (saved q)))))

private theorem loopReserveFocus_slot {Ξ : Ctx} (out : Ref Ξ .point) (N : ℕ) {Γ : Ctx}
    (old direct : Fin n → Ref Γ .point) (saved : RefMap Ξ Γ) :
    liftSlot (loopReserveFocus cfg out N old direct saved).cut (.inl PUnit.unit) =
      Oracle.PrivateSamplingTapeProjections.loopSlot cfg out N old direct saved (.inr (.inr ())) := by
  dsimp only [loopReserveFocus]
  rw [liftSlot_trans]
  exact atFinish_slot cfg out N old direct saved (.inr (.inr ()))

theorem privateReserveFocus_slot :
    liftSlot (privateReserveFocus cfg).cut (.inl PUnit.unit) =
      Oracle.PrivateSamplingTapeProjections.slot cfg (.inr (.inr (.inr ()))) := by
  exact congrArg Sum.inr (congrArg Sum.inr (congrArg Sum.inr (congrArg Sum.inr
    (congrArg Sum.inr (congrArg Sum.inr (congrArg Sum.inr
      (loopReserveFocus_slot cfg _ cfg.layers batchRef _ _)))))))



def reserveRead {Ξ : Ctx} (input : Inputs d C) (out : Ref Ξ .point)
    (env : Env d (.point :: replyCtx n Ξ)) : Point d :=
  storedPoint env (.there (RefMap.shiftMany n out)) +
    (∑ i, input.coefficient (cfg.rowWeight i) • storedPoint env (.there (batchRef i))) +
      input.coefficient cfg.beta • storedPoint env .here

theorem run_reserveCode {Ξ : Ctx} (G : Point d → Point d) (input : Inputs d C)
    (out : Ref Ξ .point) (env : Env d (.point :: replyCtx n Ξ))
    (ω : Tape d (reserveCode cfg out)) :
    (run (reserveCode cfg out) G input env ω).value =
      reserveRead cfg input out env + input.coefficient cfg.reserve • (show Point d from ω.1) := by
  simp only [reserveCode, run, evalInstr, run_affineRow, pointResult]
  simp only [List.map_append, List.sum_append, List.map_ofFn, Function.comp_def,
    Fin.sum_ofFn, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  simp only [storedPoint, Env.cons_here, Env.cons_there, reserveRead]
  abel

def prefixPre {Γ : Ctx} {host : Prog C Γ .point} (f : ReserveFocus cfg host)
    (G : Point d → Point d) (input : Inputs d C) (env : Env d Γ)
    (h : Prefix d f.cut) : Point d :=
  reserveRead cfg input f.out (envAt G input f.cut env h)

theorem prefixPre_measurable {Γ : Ctx} {host : Prog C Γ .point} (f : ReserveFocus cfg host)
    (G : Point d → Point d) (hG : Measurable G) (input : Inputs d C) (env : Env d Γ) :
    @Measurable _ _ (prefixSpace d f.cut) _ (prefixPre cfg f G input env) := by
  let : MeasurableSpace (Prefix d f.cut) := prefixSpace d f.cut
  exact ((prefixReadout_measurable G hG f.cut input env _).add
    (Finset.measurable_sum _ (fun i _ =>
      (prefixReadout_measurable G hG f.cut input env (.there (batchRef i))).const_smul
        (input.coefficient (cfg.rowWeight i))))).add
          ((prefixReadout_measurable G hG f.cut input env .here).const_smul
            (input.coefficient cfg.beta))

theorem privateReserve_coordinate (ω : Tape d (code cfg)) :
    Oracle.PrivateSamplingTapeProjections.coordinates cfg ω (.inr (.inr (.inr ()))) =
      (show Point d from (split (privateReserveFocus cfg).cut ω).2.1) := by
  have hs := split_liftSlot (privateReserveFocus cfg).cut (.inl PUnit.unit) ω
  rw [privateReserveFocus_slot] at hs
  exact hs

open CoolingExecutable
variable {m nm na nh ns nc : ℕ} (P : Setup m nm na nh ns nc)

theorem prefixPre_eq_actual (h : ℝ) (v : ℝ≥0) (K : ℕ)
    (G : Point d → Point d) (x : Point d) (ω : FullTape P d h v K) :
    prefixPre (config P h v K) (privateReserveFocus (config P h v K)) G (input P h v K x)
      Env.empty (split (privateReserveFocus (config P h v K)).cut ω).1 =
        preReserve P h v K G x ω := by
  let f := privateReserveFocus (config P h v K)
  have hs := run_split_value G (input P h v K x) f.cut Env.empty ω
  rw [run_reserveCode] at hs
  have hc := privateReserve_coordinate (config P h v K) ω
  rw [← hc, reserve_coefficient P h v K x] at hs
  have he := execute_value_eq_preReserve_add_reserve P h v K G x ω
  exact add_right_cancel (hs.symm.trans he)



theorem preKernel_apply (h : ℝ) (v : ℝ≥0) (K : ℕ)
    {G : Point d → Point d} (hG : Measurable G) (x : Point d) :
    preKernel P h v K G x =
      (Probability.MixedResidualTape.tapeLaw d (data P h v K).program).map
        (preReserve P h v K G x) := by
  have hm := preReserve_measurable P h v K hG
  rw [preKernel, Kernel.map_apply _ hm, Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map hm measurable_prodMk_left]
  rfl

/-- Exact independence of the actual final reserve from the entire actual
pre-reserve output, with every original source tape coordinate retained. -/
theorem preReserve_reserve_joint (h : ℝ) (v : ℝ≥0) (K : ℕ)
    {G : Point d → Point d} (hG : Measurable G) (x : Point d) :
    (Probability.MixedResidualTape.tapeLaw d (data P h v K).program).map
      (fun ω => (preReserve P h v K G x ω,reserve P h v K ω)) =
      (preKernel P h v K G x).prod (stdGaussian (Point d)) := by
  let L := Probability.CanonicalNativeTapeLaw.primitiveLaws d
  let f := privateReserveFocus (config P h v K)
  let pre := prefixPre (config P h v K) f G (input P h v K x) Env.empty
  let : MeasurableSpace (Prefix d f.cut) := prefixSpace d f.cut
  let : IsProbabilityMeasure (prefixLaw L f.cut) := prefixLaw_probability L f.cut
  have hpre : Measurable pre := prefixPre_measurable (config P h v K) f G hG
    (input P h v K x) Env.empty
  have hp := prefix_gaussian_joint L f.cut pre hpre
  dsimp only at hp
  have he (ω : FullTape P d h v K) :
      (preReserve P h v K G x ω,reserve P h v K ω) =
        (pre (split f.cut ω).1,(show Point d from (split f.cut ω).2.1)) := by
    change _ = (prefixPre (config P h v K) (privateReserveFocus (config P h v K)) G
      (input P h v K x) Env.empty (split (privateReserveFocus (config P h v K)).cut ω).1,_)
    rw [prefixPre_eq_actual, ← privateReserve_coordinate]
    rfl
  have hj : (Probability.MixedResidualTape.tapeLaw d (data P h v K).program).map
      (fun ω => (preReserve P h v K G x ω,reserve P h v K ω)) =
      ((prefixLaw L f.cut).map pre).prod (stdGaussian (Point d)) := by
    rw [Probability.CanonicalNativeTapeLaw.map_native_eq]
    rw [show (fun ω : FullTape P d h v K => (preReserve P h v K G x ω,reserve P h v K ω)) =
      (fun ω => (pre (split f.cut ω).1,(show Point d from (split f.cut ω).2.1))) from funext he]
    exact hp
  have hm : Measurable (fun ω : FullTape P d h v K =>
      (preReserve P h v K G x ω,reserve P h v K ω)) :=
    ((preReserve_measurable P h v K hG).comp (measurable_const.prodMk measurable_id)).prodMk
      (reserve_measurable P h v K)
  have hfirst := congrArg (fun μ : Measure (Point d × Point d) => μ.map Prod.fst) hj
  rw [Measure.map_map measurable_fst hm] at hfirst
  change (Probability.MixedResidualTape.tapeLaw d (data P h v K).program).map
    (preReserve P h v K G x) = (((prefixLaw L f.cut).map pre).prod
      (stdGaussian (Point d))).fst at hfirst
  rw [Measure.fst_prod] at hfirst
  rw [preKernel_apply P h v K hG, hfirst]
  exact hj



/-- The literal executable cooling kernel is the reserved decoder of its own
actual pre-reserve kernel. This uses the actual final reserve occurrence. -/
theorem kernel_eq_reservedDecoder (h : ℝ) (v : ℝ≥0) (K : ℕ)
    {G : Point d → Point d} (hG : Measurable G) :
    kernel P h v K G = Channels.reservedDecoder (preKernel P h v K G) v := by
  let : IsMarkovKernel (preKernel P h v K G) := preKernel_markov P h v K hG
  have hn : Channels.noise (1/4 : ℝ≥0) =
      (stdGaussian (Point d)).map (fun z => (1/2 : ℝ) • z) := by
    rw [Channels.noise_eq_scaled_stdGaussian]
    norm_num
  ext x : 1
  let decode : Point d × Point d → Point d := fun z =>
    x+(Real.sqrt (v : ℝ)/2) • (z.1+(1/2 : ℝ) • z.2)
  have hd : Measurable decode := by fun_prop
  have hm : Measurable (fun ω : FullTape P d h v K =>
      (preReserve P h v K G x ω,reserve P h v K ω)) :=
    ((preReserve_measurable P h v K hG).comp (measurable_const.prodMk measurable_id)).prodMk
      (reserve_measurable P h v K)
  have hp : (preKernel P h v K G x).prod (Channels.noise (1/4 : ℝ≥0)) =
      ((preKernel P h v K G x).prod (stdGaussian (Point d))).map
        (fun z => (z.1,(1/2 : ℝ) • z.2)) := by
    rw [hn]
    have hscale : Measurable (fun z : Point d => (1/2 : ℝ) • z) :=
      measurable_id.const_smul (1/2 : ℝ)
    convert (Measure.map_prod_map (preKernel P h v K G x) (stdGaussian (Point d))
      measurable_id hscale) using 1 <;> simp only [Measure.map_id]
    rfl
  calc
    kernel P h v K G x =
        (Probability.MixedResidualTape.tapeLaw d (data P h v K).program).map
          (decode ∘ (fun ω => (preReserve P h v K G x ω,reserve P h v K ω))) := by
      rw [kernel_apply P h v K hG]
      congr 1
      funext ω
      exact output_eq_decode_actual_reserve P h v K G x ω
    _ = ((Probability.MixedResidualTape.tapeLaw d (data P h v K).program).map
        (fun ω => (preReserve P h v K G x ω,reserve P h v K ω))).map decode :=
      (Measure.map_map hd hm).symm
    _ = ((preKernel P h v K G x).prod (stdGaussian (Point d))).map decode := by
      rw [preReserve_reserve_joint P h v K hG]
    _ = Channels.reservedDecoder (preKernel P h v K G) v x := by
      rw [Channels.reservedDecoder_apply, hp, Measure.map_map (by fun_prop) (by fun_prop)]
      rfl

end AcceleratedLogConcave.Root.CoolingReserveLaw
