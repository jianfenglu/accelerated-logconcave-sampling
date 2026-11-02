import AcceleratedLogConcave.Oracle.MeanChronologicalHost

/-! Finite chronological augmentation of the literal original mean-main loop.
The static incoming history and entire original tape are retained. Main-child
references are sampled from the concrete lower retained couplings. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace AcceleratedLogConcave.Oracle.MeanChronologicalCoupling
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RecursiveMeanProgram RecursiveMeanContinuation SourceMeanLayer SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateCausalLayer PrivateCausalAdvance
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p

variable {m n a h d : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData) (N : ℕ)

abbrev Host := SourceMeanExecutable.program M nodes anchors seeds main final sampling N
abbrev History (A : Type*) := MeanInitialComparison.History (d := d) M nodes anchors seeds main final sampling N A
abbrev Coarse (A : Type*) := MeanInitialComparison.Coarse (d := d) M nodes anchors seeds main final sampling N A

abbrev Loop {Γ : Ctx} (remaining : ℕ) (old direct : Fin n → Ref Γ .point)
    (saved : RefMap (SourceMeanExecutionRms.Ready n m h) Γ) :
    Prog (SourceMeanExecutable.size (a := a) main final sampling) Γ .point :=
  iterateThen (fun i => (main i).size) (fun i => (main i).program)
    (mainSlot (a := a) main final sampling) (fun i => (main i).enumeration)
    layerOrigin mainDesignated residualOrigin (mainAuxiliary main)
    (SourceMeanExecutionRms.finish (a := a) (h := h) M nodes main final sampling)
    remaining old direct saved

structure Cursor where
  remaining : ℕ
  ctx : Ctx
  old : Fin n → Ref ctx .point
  direct : Fin n → Ref ctx .point
  saved : RefMap (SourceMeanExecutionRms.Ready n m h) ctx
  cut : TailCut (Loop M nodes main final sampling remaining old direct saved)
    (Host M nodes anchors seeds main final sampling N)

def entry : Cursor M nodes anchors seeds main final sampling N where
  remaining := N
  ctx := replyCtx n (replyCtx n (SourceMeanExecutionRms.Ready n m h))
  old := batchRef
  direct i := RefMap.shiftMany n (RefMap.shiftMany n (MeanExecutablePrefix.direct i))
  saved q := RefMap.shiftMany n (RefMap.shiftMany n q)
  cut := MeanInitialComparison.entryCut M nodes anchors seeds main final sampling N

def focus (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining) :
    GeneralMainFocus.Focus (fun i => (main i).size) (fun i => (main i).program)
      (mainSlot (a := a) main final sampling) (fun i => (main i).enumeration)
      layerOrigin mainDesignated residualOrigin (mainAuxiliary main)
      (SourceMeanExecutionRms.finish (a := a) (h := h) M nodes main final sampling)
      (Host M nodes anchors seeds main final sampling N) where
  remainingAfter := s.remaining-1
  ctx := s.ctx
  old := s.old
  direct := s.direct
  saved := s.saved
  cut := by rw [Nat.sub_add_cancel hs]; exact s.cut

def advance (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining) :
    Cursor M nodes anchors seeds main final sampling N where
  remaining := s.remaining-1
  ctx := nextCtx n s.ctx
  old := batchRef
  direct i := preserveDirect (s.direct i)
  saved q := preserveDirect (s.saved q)
  cut := afterLayer (fun i => (main i).size) (fun i => (main i).program)
    (mainSlot (a := a) main final sampling) (fun i => (main i).enumeration)
    layerOrigin mainDesignated residualOrigin (mainAuxiliary main)
    (SourceMeanExecutionRms.finish (a := a) (h := h) M nodes main final sampling)
    (s.remaining-1) s.old s.direct s.saved
    (focus M nodes anchors seeds main final sampling N s hs).cut

def stage : (k : ℕ) → (hk : k≤N) →
    {s : Cursor M nodes anchors seeds main final sampling N // s.remaining=N-k}
  | 0,_ => ⟨entry M nodes anchors seeds main final sampling N,by simp [entry]⟩
  | k+1,hk =>
    let s := stage k (by omega)
    ⟨advance M nodes anchors seeds main final sampling N s.1 (by rw [s.2]; omega),by
      change s.1.remaining-1=N-(k+1)
      rw [s.2]; omega⟩

theorem stage_remaining (k : ℕ) (hk : k≤N) :
    (stage M nodes anchors seeds main final sampling N k hk).1.remaining=N-k :=
  (stage M nodes anchors seeds main final sampling N k hk).2

def terminalCursor : Cursor M nodes anchors seeds main final sampling N :=
  (stage M nodes anchors seeds main final sampling N N le_rfl).1
@[simp] theorem terminal_remaining :
    (terminalCursor M nodes anchors seeds main final sampling N).remaining=0 :=
  (stage_remaining M nodes anchors seeds main final sampling N N le_rfl).trans (Nat.sub_self N)

def terminalCut : TailCut
    (SourceMeanExecutionRms.finish (a := a) (h := h) M nodes main final sampling
      (terminalCursor M nodes anchors seeds main final sampling N).old
      (terminalCursor M nodes anchors seeds main final sampling N).direct
      (terminalCursor M nodes anchors seeds main final sampling N).saved)
    (Host M nodes anchors seeds main final sampling N) := by
  have h := (terminalCursor M nodes anchors seeds main final sampling N).cut
  rw [terminal_remaining] at h
  exact h



variable (r Ds : ℝ) (hr : 0<r) (hDs : 0<Ds)
  (hmass : ∀ i,CovarianceSetup.shiftSq (main i).shiftVector≤Ds^2)

def data (s : Cursor M nodes anchors seeds main final sampling N) (_hs : 0<s.remaining) :
    FreshChildBatchCoupling.Data n (SourceMeanExecutable.size (a := a) main final sampling) s.ctx where
  child := main
  slot i := mainSlot (a := a) main final sampling ∘
    childSlot (fun i => (main i).size) (fun i => (main i).program) i
  old := s.old
  designated := mainDesignated (s.remaining-1)
  auxiliary := mainAuxiliary main (s.remaining-1)
  rho _ := RecursiveMeanPublicTable.centerNoise r M.R Ds
  radius i := M.radius r (nodes i)
  Ds := Ds
  rho_nonneg _ := (RecursiveExecutableDomain.center_noise_pos M r Ds hr hDs).le
  radius_pos i := M.radius_pos r hr (nodes i)
  Ds_pos := hDs
  shift_budget := hmass
  small i := RecursiveExecutableDomain.mean_noise_separation M r Ds hr hDs (nodes i)

def next (s : Cursor M nodes anchors seeds main final sampling N) :
    Prog (SourceMeanExecutable.size (a := a) main final sampling) (replyCtx n s.ctx) .point :=
  .batch [] (fun j => residualDraw (residualOrigin (s.remaining-1) j))
    (.batch [] (noisyRow
      (fun j l => mainSlot (a := a) main final sampling
        (aSlot (fun i => (main i).size) (fun i => (main i).program) j l))
      (fun j l => mainSlot (a := a) main final sampling
        (residualSlot (fun i => (main i).size) (fun i => (main i).program) j l)) s.direct)
      (Loop M nodes main final sampling (s.remaining-1) batchRef
        (fun j => preserveDirect (s.direct j)) (fun q => preserveDirect (s.saved q))))

def batchCut (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining) :
    TailCut (.batch (layerOrigin (s.remaining-1))
      (FreshChildBatchCoupling.program (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))
      (next M nodes anchors seeds main final sampling N s)) (Host M nodes anchors seeds main final sampling N) := (focus M nodes anchors seeds main final sampling N s hs).cut

local instance bodyPrefixSpace : MeasurableSpace
    (Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N)) := prefixSpace d _

variable {A : Type*} [MeasurableSpace A]
local instance cursorPrefixSpace (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining) :
    MeasurableSpace (Prefix d (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))) := prefixSpace d _

def observation (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining)
    (z : History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))) :
    Coarse (d := d) M nodes anchors seeds main final sampling N A × (∀ i,FreshChildBatchCoupling.Raw d (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs) i) :=
  (z.1.1,fun i => (z.1.2.2 i,
    (batchParts (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs) z.2).2 i))

theorem observation_measurable (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining) :
    Measurable (observation (d := d) (A := A) M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs) := by
  have hb := (measurable_batchParts (d := d) (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)).comp
    (measurable_snd : Measurable (Prod.snd : History (d := d) M nodes anchors seeds main final sampling N A × _ → _))
  exact measurable_fst.fst.prodMk (Measurable.of_eval fun i =>
    ((measurable_pi_apply i).comp measurable_fst.snd.snd).prodMk
      ((measurable_pi_apply i).comp hb.snd))

variable (L : PrimitiveLaws d) (hL : L.pointDraw=stdGaussian (Point d))
  (x P referencePosition : A → Point d) (hx : Measurable x) (hP : Measurable P)
  (hreference : Measurable referencePosition)
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (σ : ℝ) (hσ : 0<σ) (hsmall : r^2*ell≤1/2)

def conditional (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining)
    (J : FreshChildBatchCoupling.Lower L (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) :
    Kernel (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)))
      (Fin n → Point d) :=
  (FreshChildBatchCoupling.referenceBatch L hL (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs) J
    (MeanChronologicalHost.center M nodes anchors seeds main final sampling N x P referencePosition hF hell hlo hup r σ hr hσ hsmall)
    (MeanChronologicalHost.center_measurable M nodes anchors seeds main final sampling N x P referencePosition hx hP hreference
      hF hell hlo hup r σ hr hσ hsmall)).comap
        (observation M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)
        (observation_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)

instance conditional_markov (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining)
    (J : FreshChildBatchCoupling.Lower L (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) :
    IsMarkovKernel (conditional M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference
      hF hell hlo hup σ hσ hsmall s hs J) := by unfold conditional; infer_instance

def adjoin (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining)
    (J : FreshChildBatchCoupling.Lower L (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) :
    Kernel (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N))
      ((History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)) × (Fin n → Point d)) :=
  CausalTailHistory.onTape L (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))
    (conditional M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference
      hF hell hlo hup σ hσ hsmall s hs J)

instance adjoin_markov (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining)
    (J : FreshChildBatchCoupling.Lower L (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) :
    IsMarkovKernel (adjoin M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference
      hF hell hlo hup σ hσ hsmall s hs J) := by unfold adjoin; infer_instance

theorem adjoin_original (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining)
    (J : FreshChildBatchCoupling.Lower L (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) :
    (adjoin M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference
      hF hell hlo hup σ hσ hsmall s hs J).fst=Kernel.id :=
  CausalTailHistory.onTape_original L _ _



variable (δ t w : ℝ)

def comparisonUpdate (gz : (Fin n → Point d) × (Fin n → Point d)) : Fin n → Point d :=
  ResidualGaussianRecombination.recombine (fun i j => M.matrix r σ (nodes i) (nodes j))
    (RecursiveMeanPublicTable.centerNoise r M.R Ds) (rowBound (m := m) r σ δ t w) gz

theorem comparisonUpdate_measurable : Measurable (comparisonUpdate (d := d) M nodes r Ds σ δ t w) :=
  ResidualGaussianRecombination.recombine_measurable _ _ _

def record (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining) (k : Fin N)
    (z : (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)) × (Fin n → Point d)) :
    History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N) :=
  ((z.1.1.1,(Function.update z.1.1.2.1 k z.2,
    comparisonUpdate M nodes r Ds σ δ t w (z.2,fun i =>
      ((split (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) z.1.2).2.1 i).1))),z.1.2)

include L in
theorem record_measurable (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining) (k : Fin N) :
    Measurable (record (d := d) (A := A) M nodes anchors seeds main final sampling N r Ds hr hDs hmass σ δ t w s hs k) := by
  have hsplit := (measurePreserving_split L
    (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))).measurable.comp
      (measurable_fst.snd : Measurable
        (fun z : (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)) ×
          (Fin n → Point d) => z.1.2))
  have hres : Measurable (fun z : (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)) ×
      (Fin n → Point d) => fun i : Fin n =>
        ((split (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) z.1.2).2.1 i).1) :=
    Measurable.of_eval fun i => ((measurable_pi_apply i).comp hsplit.snd.fst).fst
  have hu : Measurable (fun z : (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)) ×
      (Fin n → Point d) => Function.update z.1.1.2.1 k z.2) := by
    apply Measurable.of_eval
    intro i
    by_cases hi : i=k
    · subst i; simpa only [Function.update_self] using measurable_snd
    · have hm : Measurable (fun z : (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)) ×
          (Fin n → Point d) => z.1.1.2.1 i) := by fun_prop
      simpa only [Function.update_of_ne hi] using hm
  exact (measurable_fst.fst.fst.prodMk (hu.prodMk
    ((comparisonUpdate_measurable M nodes r Ds σ δ t w).comp (measurable_snd.prodMk hres)))).prodMk
      measurable_fst.snd

def step (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining) (k : Fin N)
    (J : FreshChildBatchCoupling.Lower L (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) :
    Kernel (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)) (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)) :=
  (adjoin M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs J).map (record M nodes anchors seeds main final sampling N r Ds hr hDs hmass σ δ t w s hs k)

instance step_markov (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining) (k : Fin N)
    (J : FreshChildBatchCoupling.Lower L (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) :
    IsMarkovKernel (step M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w s hs k J) := by
  unfold step
  exact Kernel.IsMarkovKernel.map _ (record_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass L σ δ t w s hs k)

def original (z : History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)) : A × Tape d (Host M nodes anchors seeds main final sampling N) :=
  (z.1.1.1,z.2)

theorem original_measurable : Measurable (original (d := d) (A := A) M nodes anchors seeds main final sampling N) :=
  measurable_fst.fst.fst.prodMk measurable_snd

theorem step_original (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining) (k : Fin N)
    (J : FreshChildBatchCoupling.Lower L (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) :
    (step M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w s hs k J).map (original M nodes anchors seeds main final sampling N) =
      Kernel.deterministic (original M nodes anchors seeds main final sampling N) (original_measurable M nodes anchors seeds main final sampling N) := by
  rw [step,← Kernel.map_comp_right _
    (record_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass L σ δ t w s hs k) (original_measurable M nodes anchors seeds main final sampling N)]
  change (adjoin M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs J).map ((original M nodes anchors seeds main final sampling N) ∘ Prod.fst) = _
  rw [Kernel.map_comp_right _ measurable_fst (original_measurable M nodes anchors seeds main final sampling N),
    ← Kernel.fst_eq,adjoin_original,Kernel.id_map]

theorem stage_positive (k : ℕ) (hk : k<N) :
    0<(stage M nodes anchors seeds main final sampling N k hk.le).1.remaining := by rw [stage_remaining]; omega

variable
  (J : ∀ (k : ℕ) (hk : k<N),FreshChildBatchCoupling.Lower L
    (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass (stage M nodes anchors seeds main final sampling N k hk.le).1 (stage_positive M nodes anchors seeds main final sampling N k hk)))

def iteration : (k : ℕ) → (hk : k≤N) →
    Kernel (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)) (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N))
  | 0,_ => Kernel.id
  | k+1,hk =>
    (step M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w (stage M nodes anchors seeds main final sampling N k (by omega)).1
      (stage_positive M nodes anchors seeds main final sampling N k (by omega)) ⟨k,by omega⟩ (J k (by omega))) ∘ₖ iteration k (by omega)

instance iteration_markov (k : ℕ) (hk : k≤N) :
    IsMarkovKernel (iteration M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J k hk) := by
  induction k with
  | zero => change IsMarkovKernel Kernel.id; infer_instance
  | succ k ih =>
    have := ih (by omega)
    dsimp only [iteration]
    infer_instance

theorem iteration_original (k : ℕ) (hk : k≤N) :
    (iteration M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J k hk).map (original M nodes anchors seeds main final sampling N) =
      Kernel.deterministic (original M nodes anchors seeds main final sampling N) (original_measurable M nodes anchors seeds main final sampling N) := by
  induction k with
  | zero => exact Kernel.id_map (original_measurable M nodes anchors seeds main final sampling N)
  | succ k ih =>
    rw [iteration,Kernel.map_comp,step_original,Kernel.deterministic_comp_eq_map]
    exact ih (by omega)

def kernel : Kernel (A × Tape d (Host M nodes anchors seeds main final sampling N)) (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)) :=
  iteration M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J N le_rfl ∘ₖ
    Kernel.deterministic (MeanInitialComparison.prepare M nodes anchors seeds main final sampling N) (MeanInitialComparison.prepare_measurable M nodes anchors seeds main final sampling N L)

instance kernel_markov : IsMarkovKernel (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J) := by unfold kernel; infer_instance

theorem kernel_original : (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J).map (original M nodes anchors seeds main final sampling N)=Kernel.id := by
  rw [kernel,Kernel.map_comp,iteration_original,Kernel.deterministic_comp_eq_map,
    Kernel.deterministic_map (MeanInitialComparison.prepare_measurable M nodes anchors seeds main final sampling N L) (original_measurable M nodes anchors seeds main final sampling N)]
  change Kernel.deterministic id _=Kernel.id
  rfl

end AcceleratedLogConcave.Oracle.MeanChronologicalCoupling
