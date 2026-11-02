import AcceleratedLogConcave.Root.ClockRetainedShape
import AcceleratedLogConcave.Root.ClockRetainedPublicTablesMeasurability
import AcceleratedLogConcave.Root.ClockRetainedTapeTransport

/-! Measurability of the literal retained root table after transporting its
fixed program shape to clock zero. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace AcceleratedLogConcave.Root.ClockRetainedTableMeasurability
open Oracle Oracle.RecursiveExecutableParameterShape
  Oracle.RecursiveExecutableParameterMeasurability
open ClockRetainedShape ClockCoefficientMeasurability

variable (P : SourceSchedule) (hR : P.R ≤ 1/2) (hc : 0 < P.csch)
  (hsmall : P.csch < 1/160)

def anchor : ClockLaw.Clock := ⟨0, by constructor <;> norm_num⟩

theorem mainData_parameter_identity (i : ClockNoisyLayer.Index P)
    (clock : ClockLaw.Clock) :
    ClockNoisyLayer.child P hR hc hsmall clock i =
      Oracle.CubicExecutableWorkShift.data P hR hc hsmall (Real.sqrt P.delta)
        (ClockNoisyLayer.radius P clock i)
        (1/(2*P.Ds*Real.sqrt (ClockNoisyLayer.N P:ℝ)*Real.sqrt (2*P.delta)))
        (P.K:ℝ) := by
  rfl

theorem finalData_parameter_identity (i : ClockNoisyLayer.Index P)
    (clock : ClockLaw.Clock) :
    FinalMeanScheduledData.finalData P hR hc hsmall i clock =
      Oracle.CubicExecutableWorkShift.data P hR hc hsmall (Real.sqrt P.delta)
        (FinalMeanScheduledData.state P i clock).radius
        (ClockRetainedFinalSplice.width P clock i) (P.K:ℝ) := by
  rfl

theorem data_shape (q scale r σ scale₀ r₀ σ₀ : ℝ) :
    shape (Oracle.CubicExecutableWorkShift.data P hR hc hsmall scale r σ q) =
      shape (Oracle.CubicExecutableWorkShift.data P hR hc hsmall scale₀ r₀ σ₀ q) := by
  unfold Oracle.CubicExecutableWorkShift.data Oracle.RecursiveExecutable.mean
  apply meanCore_shape

theorem measurable_data_payload {X : Type*} [MeasurableSpace X]
    (q scale₀ r₀ σ₀ : ℝ) (scale r σ : X → ℝ)
    (hscale : Measurable scale) (hr : Measurable r) (hσ : Measurable σ) :
    Measurable (fun x => alignedPayload
      (Oracle.CubicExecutableWorkShift.data P hR hc hsmall
        (scale x) (r x) (σ x) q)
      (shape (Oracle.CubicExecutableWorkShift.data P hR hc hsmall
        scale₀ r₀ σ₀ q))
      (data_shape P hR hc hsmall q (scale x) (r x) (σ x) scale₀ r₀ σ₀)) := by
  unfold Oracle.CubicExecutableWorkShift.data Oracle.RecursiveExecutable.mean
  apply meanCore_alignedPayload_measurable
  · exact hscale
  · exact hr
  · exact hσ

private theorem measurable_alignedPayload_change_shape
    {X : Type*} [MeasurableSpace X]
    {s t : Shape} (h : s = t) (E : X → Oracle.ExecutableData)
    (hs : ∀ x, shape (E x) = s)
    (hm : Measurable (fun x => alignedPayload (E x) s (hs x))) :
    Measurable (fun x => alignedPayload (E x) t ((hs x).trans h)) := by
  cases h
  simpa using hm

def mainShape (i : ClockNoisyLayer.Index P) : Shape :=
  shape (ClockNoisyLayer.child P hR hc hsmall anchor i)

def canonicalShape : Shape :=
  shape (Oracle.CubicExecutableWorkShift.data P hR hc hsmall 0 0 0 (P.K:ℝ))

theorem canonicalShape_eq_mainShape (i : ClockNoisyLayer.Index P) :
    canonicalShape P hR hc hsmall = mainShape P hR hc hsmall i := by
  unfold canonicalShape mainShape
  rw [mainData_parameter_identity P hR hc hsmall i anchor]
  unfold Oracle.CubicExecutableWorkShift.data
  apply mean_shape

theorem mainShape_eq_canonical (i : ClockNoisyLayer.Index P)
    (clock : ClockLaw.Clock) :
    shape (ClockNoisyLayer.child P hR hc hsmall clock i) =
      canonicalShape P hR hc hsmall :=
  (main_child_shape_clock P hR hc hsmall i clock anchor).trans
    (canonicalShape_eq_mainShape P hR hc hsmall i).symm

def mainPayload (i : ClockNoisyLayer.Index P) (clock : ClockLaw.Clock) :
    Payload (mainShape P hR hc hsmall i) :=
  alignedPayload (ClockNoisyLayer.child P hR hc hsmall clock i)
    (mainShape P hR hc hsmall i)
    (main_child_shape_clock P hR hc hsmall i clock anchor)

theorem reconstruct_mainPayload (i : ClockNoisyLayer.Index P)
    (clock : ClockLaw.Clock) :
    reconstruct (mainShape P hR hc hsmall i) (mainPayload P hR hc hsmall i clock) =
      ClockNoisyLayer.child P hR hc hsmall clock i :=
  reconstruct_alignedPayload _ _ _

def finalShape (i : ClockNoisyLayer.Index P) : Shape :=
  shape (FinalMeanScheduledData.finalData P hR hc hsmall i anchor)

theorem canonicalShape_eq_finalShape (i : ClockNoisyLayer.Index P) :
    canonicalShape P hR hc hsmall = finalShape P hR hc hsmall i := by
  unfold canonicalShape finalShape
  rw [finalData_parameter_identity P hR hc hsmall i anchor]
  unfold Oracle.CubicExecutableWorkShift.data
  apply mean_shape

theorem finalShape_eq_canonical (i : ClockNoisyLayer.Index P)
    (clock : ClockLaw.Clock) :
    shape (FinalMeanScheduledData.finalData P hR hc hsmall i clock) =
      canonicalShape P hR hc hsmall :=
  (final_child_shape_clock P hR hc hsmall i clock anchor).trans
    (canonicalShape_eq_finalShape P hR hc hsmall i).symm

theorem measurable_mainPayload_of_canonical (i : ClockNoisyLayer.Index P)
    (hm : Measurable (fun clock : ClockLaw.Clock =>
      alignedPayload (ClockNoisyLayer.child P hR hc hsmall clock i)
        (canonicalShape P hR hc hsmall)
        (mainShape_eq_canonical P hR hc hsmall i clock))) :
    Measurable (mainPayload P hR hc hsmall i) := by
  have h := measurable_alignedPayload_change_shape
    (canonicalShape_eq_mainShape P hR hc hsmall i)
    (fun clock : ClockLaw.Clock => ClockNoisyLayer.child P hR hc hsmall clock i)
    (mainShape_eq_canonical P hR hc hsmall i) hm
  convert h using 1
  funext clock
  rfl

def finalPayload (i : ClockNoisyLayer.Index P) (clock : ClockLaw.Clock) :
    Payload (finalShape P hR hc hsmall i) :=
  alignedPayload (FinalMeanScheduledData.finalData P hR hc hsmall i clock)
    (finalShape P hR hc hsmall i)
    (final_child_shape_clock P hR hc hsmall i clock anchor)

theorem reconstruct_finalPayload (i : ClockNoisyLayer.Index P)
    (clock : ClockLaw.Clock) :
    reconstruct (finalShape P hR hc hsmall i) (finalPayload P hR hc hsmall i clock) =
      FinalMeanScheduledData.finalData P hR hc hsmall i clock :=
  reconstruct_alignedPayload _ _ _

theorem measurable_finalPayload_of_canonical (i : ClockNoisyLayer.Index P)
    (hf : Measurable (fun clock : ClockLaw.Clock =>
      alignedPayload (FinalMeanScheduledData.finalData P hR hc hsmall i clock)
        (canonicalShape P hR hc hsmall)
        (finalShape_eq_canonical P hR hc hsmall i clock))) :
    Measurable (finalPayload P hR hc hsmall i) := by
  have h := measurable_alignedPayload_change_shape
    (canonicalShape_eq_finalShape P hR hc hsmall i)
    (fun clock : ClockLaw.Clock => FinalMeanScheduledData.finalData P hR hc hsmall i clock)
    (finalShape_eq_canonical P hR hc hsmall i) hf
  convert h using 1
  funext clock
  rfl

def fixedMainT (clock : ClockLaw.Clock) :
    ∀ i : ClockNoisyLayer.Index P,
      Oracle.CovarianceSetup.Mat
        (Oracle.tapeShape (mainShape P hR hc hsmall i).2).gaussianBlocks :=
  fun i => Oracle.CovarianceSetup.childRoot (ClockNoisyLayer.rhoC P)
    (ClockNoisyLayer.radius P clock i)
    (reconstruct (mainShape P hR hc hsmall i)
      (mainPayload P hR hc hsmall i clock)).shiftVector

def fixedMainCoeff (clock : ClockLaw.Clock) :
    ∀ i : ClockNoisyLayer.Index P, Fin (mainShape P hR hc hsmall i).1 → ℝ :=
  fun i => (reconstruct (mainShape P hR hc hsmall i)
    (mainPayload P hR hc hsmall i clock)).coefficient

def fixedMainTable (clock : ClockLaw.Clock) :=
  Oracle.NoisyLayer.layerTable
    (fun i : ClockNoisyLayer.Index P => (mainShape P hR hc hsmall i).1)
    (fun i : ClockNoisyLayer.Index P => (mainShape P hR hc hsmall i).2)
    (ClockNoisyLayer.A P clock) (ClockNoisyLayer.C P clock)
    (fixedMainT P hR hc hsmall clock) (fixedMainCoeff P hR hc hsmall clock)

theorem measurable_fixedMainTable
    (hm : ∀ i : ClockNoisyLayer.Index P,
      Measurable (mainPayload P hR hc hsmall i)) :
    Measurable (fixedMainTable P hR hc hsmall) := by
  unfold fixedMainTable
  have hT : Measurable (fixedMainT P hR hc hsmall) := by
    apply measurable_pi_iff.mpr
    intro i
    exact Oracle.CovarianceSetup.measurable_childRoot
      (fun _ : ClockLaw.Clock => ClockNoisyLayer.rhoC P)
      (fun clock => ClockNoisyLayer.radius P clock i)
      (fun clock => (show Fin (Oracle.tapeShape
        (mainShape P hR hc hsmall i).2).gaussianBlocks → ℝ from
        (reconstruct (mainShape P hR hc hsmall i)
          (mainPayload P hR hc hsmall i clock)).shiftVector))
      measurable_const (measurable_radius P i)
      (measurable_reconstruct_shiftVector
        (mainShape P hR hc hsmall i) (mainPayload P hR hc hsmall i) (hm i))
  have hcoeff : Measurable (fixedMainCoeff P hR hc hsmall) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_reconstruct_coefficient
      (mainShape P hR hc hsmall i) (mainPayload P hR hc hsmall i) (hm i)
  exact measurable_layerTable _ _ _ _ _ _
    (measurable_A P) (measurable_C P) hT hcoeff

def fixedFinalT (clock : ClockLaw.Clock) :
    ∀ i : ClockNoisyLayer.Index P,
      Oracle.CovarianceSetup.Mat
        (Oracle.tapeShape (finalShape P hR hc hsmall i).2).gaussianBlocks :=
  fun i => Oracle.CovarianceSetup.childRoot (ClockNoisyLayer.rhoC P)
    (FinalMeanScheduledData.state P i clock).radius
    (reconstruct (finalShape P hR hc hsmall i)
      (finalPayload P hR hc hsmall i clock)).shiftVector

def fixedFinalCoeff (clock : ClockLaw.Clock) :
    ∀ i : ClockNoisyLayer.Index P, Fin (finalShape P hR hc hsmall i).1 → ℝ :=
  fun i => (reconstruct (finalShape P hR hc hsmall i)
    (finalPayload P hR hc hsmall i clock)).coefficient

def fixedFinalTable (clock : ClockLaw.Clock) :=
  Oracle.RecursiveMeanPublicTable.finalTable
    (fun i : ClockNoisyLayer.Index P => (finalShape P hR hc hsmall i).1)
    (fun i : ClockNoisyLayer.Index P => (finalShape P hR hc hsmall i).2)
    (fixedFinalT P hR hc hsmall clock) (fixedFinalCoeff P hR hc hsmall clock)

theorem measurable_fixedFinalTable
    (hf : ∀ i : ClockNoisyLayer.Index P,
      Measurable (finalPayload P hR hc hsmall i)) :
    Measurable (fixedFinalTable P hR hc hsmall) := by
  unfold fixedFinalTable
  have hT : Measurable (fixedFinalT P hR hc hsmall) := by
    apply measurable_pi_iff.mpr
    intro i
    exact Oracle.CovarianceSetup.measurable_childRoot
      (fun _ : ClockLaw.Clock => ClockNoisyLayer.rhoC P)
      (fun clock => (FinalMeanScheduledData.state P i clock).radius)
      (fun clock => (show Fin (Oracle.tapeShape
        (finalShape P hR hc hsmall i).2).gaussianBlocks → ℝ from
        (reconstruct (finalShape P hR hc hsmall i)
          (finalPayload P hR hc hsmall i clock)).shiftVector))
      measurable_const (measurable_final_radius P i)
      (measurable_reconstruct_shiftVector
        (finalShape P hR hc hsmall i) (finalPayload P hR hc hsmall i) (hf i))
  have hcoeff : Measurable (fixedFinalCoeff P hR hc hsmall) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_reconstruct_coefficient
      (finalShape P hR hc hsmall i) (finalPayload P hR hc hsmall i) (hf i)
  exact measurable_finalTable _ _ _ _ hT hcoeff

private def mainTablePack (clock : ClockLaw.Clock)
    (family : ClockNoisyLayer.Index P → Oracle.ExecutableData) :
    Σ n : ℕ, Fin n → ℝ :=
  ⟨Oracle.NoisyLayer.publicSize (fun i => (family i).size)
      (fun i => (family i).program),
    Oracle.NoisyLayer.layerTable (fun i => (family i).size)
      (fun i => (family i).program)
      (ClockNoisyLayer.A P clock) (ClockNoisyLayer.C P clock)
      (fun i => Oracle.CovarianceSetup.childRoot (ClockNoisyLayer.rhoC P)
        (ClockNoisyLayer.radius P clock i) (family i).shiftVector)
      (fun i => (family i).coefficient)⟩

theorem fixedMainTable_heq (clock : ClockLaw.Clock) :
    fixedMainTable P hR hc hsmall clock ≍
      ClockNoisyLayer.table P hR hc hsmall clock := by
  let reconstructed : ClockNoisyLayer.Index P → Oracle.ExecutableData :=
    fun i => reconstruct (mainShape P hR hc hsmall i)
      (mainPayload P hR hc hsmall i clock)
  have hfamily : reconstructed = ClockNoisyLayer.child P hR hc hsmall clock := by
    funext i
    exact reconstruct_mainPayload P hR hc hsmall i clock
  change (mainTablePack P clock reconstructed).2 ≍
    (mainTablePack P clock (ClockNoisyLayer.child P hR hc hsmall clock)).2
  exact (Sigma.mk.inj_iff.mp (congrArg (mainTablePack P clock) hfamily)).2

private def finalTablePack (clock : ClockLaw.Clock)
    (family : ClockNoisyLayer.Index P → Oracle.ExecutableData) :
    Σ n : ℕ, Fin n → ℝ :=
  ⟨Oracle.RecursiveMeanPublicTable.finalSize (fun i => (family i).size)
      (fun i => (family i).program),
    Oracle.RecursiveMeanPublicTable.finalTable (fun i => (family i).size)
      (fun i => (family i).program)
      (fun i => Oracle.CovarianceSetup.childRoot (ClockNoisyLayer.rhoC P)
        (FinalMeanScheduledData.state P i clock).radius (family i).shiftVector)
      (fun i => (family i).coefficient)⟩

theorem fixedFinalTable_heq (clock : ClockLaw.Clock) :
    fixedFinalTable P hR hc hsmall clock ≍
      (fun k : Fin (ClockRetainedFinalSplice.finalSize P hR hc hsmall clock) =>
        let q := finSigmaFinEquiv.symm k
        Oracle.AffineLowering.matrixTable
          (ClockRetainedFinalSplice.finalRoot P hR hc hsmall clock q.1)
          (ClockRetainedFinalSplice.final P hR hc hsmall clock q.1).coefficient q.2) := by
  let reconstructed : ClockNoisyLayer.Index P → Oracle.ExecutableData :=
    fun i => reconstruct (finalShape P hR hc hsmall i)
      (finalPayload P hR hc hsmall i clock)
  have hfamily : reconstructed = ClockRetainedFinalSplice.final P hR hc hsmall clock := by
    funext i
    exact reconstruct_finalPayload P hR hc hsmall i clock
  change (finalTablePack P clock reconstructed).2 ≍
    (finalTablePack P clock (ClockRetainedFinalSplice.final P hR hc hsmall clock)).2
  exact (Sigma.mk.inj_iff.mp (congrArg (finalTablePack P clock) hfamily)).2

def fixedOldTable (clock : ClockLaw.Clock) :=
  Fin.append
    (Fin.append (fixedMainTable P hR hc hsmall clock)
      (fun _ : Fin 1 => ClockNoisyLayer.rhoC P))
    (Fin.append (ClockPublicSetup.slopes P clock)
      ![ClockPublicSetup.s, ClockPublicSetup.noise, -ClockPublicSetup.s])

theorem measurable_fixedOldTable
    (hm : ∀ i : ClockNoisyLayer.Index P,
      Measurable (mainPayload P hR hc hsmall i)) :
    Measurable (fixedOldTable P hR hc hsmall) := by
  unfold fixedOldTable
  apply measurable_fin_append
  · apply measurable_fin_append
    · exact measurable_fixedMainTable P hR hc hsmall hm
    · exact measurable_const
  · apply measurable_fin_append
    · exact measurable_public_slopes P
    · exact measurable_const

abbrev fixedMainSize : ℕ :=
  Oracle.NoisyLayer.publicSize
    (fun i : ClockNoisyLayer.Index P => (mainShape P hR hc hsmall i).1)
    (fun i : ClockNoisyLayer.Index P => (mainShape P hR hc hsmall i).2)

abbrev fixedFinalSize : ℕ :=
  Oracle.RecursiveMeanPublicTable.finalSize
    (fun i : ClockNoisyLayer.Index P => (finalShape P hR hc hsmall i).1)
    (fun i : ClockNoisyLayer.Index P => (finalShape P hR hc hsmall i).2)

abbrev fixedRootSize : ℕ :=
  ((fixedMainSize P hR hc hsmall + 1) + (ClockNoisyLayer.N P + 3)) +
    (ClockRetainedFinalSplice.assemblySize P +
      (fixedFinalSize P hR hc hsmall + ClockRetainedFinalSplice.correctionSize P))

theorem fixedMainSize_eq_clock (clock : ClockLaw.Clock) :
    fixedMainSize P hR hc hsmall =
      ClockNoisyLayer.tableSize P hR hc hsmall clock := by
  let reconstructed : ClockNoisyLayer.Index P → Oracle.ExecutableData :=
    fun i => reconstruct (mainShape P hR hc hsmall i)
      (mainPayload P hR hc hsmall i clock)
  have hfamily : reconstructed = ClockNoisyLayer.child P hR hc hsmall clock := by
    funext i
    exact reconstruct_mainPayload P hR hc hsmall i clock
  change (mainTablePack P clock reconstructed).1 =
    (mainTablePack P clock (ClockNoisyLayer.child P hR hc hsmall clock)).1
  exact congrArg Sigma.fst (congrArg (mainTablePack P clock) hfamily)

theorem fixedFinalSize_eq_clock (clock : ClockLaw.Clock) :
    fixedFinalSize P hR hc hsmall =
      ClockRetainedFinalSplice.finalSize P hR hc hsmall clock := by
  let reconstructed : ClockNoisyLayer.Index P → Oracle.ExecutableData :=
    fun i => reconstruct (finalShape P hR hc hsmall i)
      (finalPayload P hR hc hsmall i clock)
  have hfamily : reconstructed = ClockRetainedFinalSplice.final P hR hc hsmall clock := by
    funext i
    exact reconstruct_finalPayload P hR hc hsmall i clock
  change (finalTablePack P clock reconstructed).1 =
    (finalTablePack P clock (ClockRetainedFinalSplice.final P hR hc hsmall clock)).1
  exact congrArg Sigma.fst (congrArg (finalTablePack P clock) hfamily)

theorem fixedRootSize_eq_clock (clock : ClockLaw.Clock) :
    fixedRootSize P hR hc hsmall =
      ClockRetainedFinalSplice.size P hR hc hsmall clock := by
  unfold fixedRootSize ClockRetainedFinalSplice.size
    ClockRetainedFinalSplice.oldSize ClockPublicSetup.size
    ClockInitialLayer.extendedSize
  rw [fixedMainSize_eq_clock P hR hc hsmall clock,
    fixedFinalSize_eq_clock P hR hc hsmall clock]

def fixedRootTable (clock : ClockLaw.Clock) :
    Fin (fixedRootSize P hR hc hsmall) → ℝ :=
  Fin.append (fixedOldTable P hR hc hsmall clock)
    (Fin.append (Oracle.MeanGaussianSetup.table
        (ClockRetainedFinalSplice.coefficient P clock))
      (Fin.append (fixedFinalTable P hR hc hsmall clock)
        (Oracle.RetainedMeanCorrection.table 1
          (ClockRetainedFinalSplice.correctionWeight P clock)
          (ClockRetainedFinalSplice.width P clock))))

theorem measurable_fixedRootTable
    (hm : ∀ i : ClockNoisyLayer.Index P,
      Measurable (mainPayload P hR hc hsmall i))
    (hf : ∀ i : ClockNoisyLayer.Index P,
      Measurable (finalPayload P hR hc hsmall i)) :
    Measurable (fixedRootTable P hR hc hsmall) := by
  unfold fixedRootTable
  apply measurable_fin_append
  · exact measurable_fixedOldTable P hR hc hsmall hm
  · apply measurable_fin_append
    · exact ClockRetainedPublicTablesMeasurability.measurable_assembly_table P
    · apply measurable_fin_append
      · exact measurable_fixedFinalTable P hR hc hsmall hf
      · exact ClockRetainedPublicTablesMeasurability.measurable_correction_table P

private def rootTablePack (clock : ClockLaw.Clock)
    (mainFamily finalFamily : ClockNoisyLayer.Index P → Oracle.ExecutableData) :
    Σ n : ℕ, Fin n → ℝ :=
  let main := mainTablePack P clock mainFamily
  let final := finalTablePack P clock finalFamily
  ⟨_, Fin.append
    (Fin.append (Fin.append main.2 (fun _ : Fin 1 => ClockNoisyLayer.rhoC P))
      (Fin.append (ClockPublicSetup.slopes P clock)
        ![ClockPublicSetup.s, ClockPublicSetup.noise, -ClockPublicSetup.s]))
    (Fin.append (Oracle.MeanGaussianSetup.table
        (ClockRetainedFinalSplice.coefficient P clock))
      (Fin.append final.2
        (Oracle.RetainedMeanCorrection.table 1
          (ClockRetainedFinalSplice.correctionWeight P clock)
          (ClockRetainedFinalSplice.width P clock))))⟩

/-- The measurable fixed-anchor table is exactly the actual retained-root
coefficient table, with all main and final child table entries transported. -/
theorem fixedRootTable_heq (clock : ClockLaw.Clock) :
    fixedRootTable P hR hc hsmall clock ≍
      ClockRetainedFinalSplice.table P hR hc hsmall clock := by
  let mainReconstructed : ClockNoisyLayer.Index P → Oracle.ExecutableData :=
    fun i => reconstruct (mainShape P hR hc hsmall i)
      (mainPayload P hR hc hsmall i clock)
  let finalReconstructed : ClockNoisyLayer.Index P → Oracle.ExecutableData :=
    fun i => reconstruct (finalShape P hR hc hsmall i)
      (finalPayload P hR hc hsmall i clock)
  have hm : mainReconstructed = ClockNoisyLayer.child P hR hc hsmall clock := by
    funext i
    exact reconstruct_mainPayload P hR hc hsmall i clock
  have hf : finalReconstructed = ClockRetainedFinalSplice.final P hR hc hsmall clock := by
    funext i
    exact reconstruct_finalPayload P hR hc hsmall i clock
  change (rootTablePack P clock mainReconstructed finalReconstructed).2 ≍
    (rootTablePack P clock
      (ClockNoisyLayer.child P hR hc hsmall clock)
      (ClockRetainedFinalSplice.final P hR hc hsmall clock)).2
  have hpack : rootTablePack P clock mainReconstructed finalReconstructed =
      rootTablePack P clock (ClockNoisyLayer.child P hR hc hsmall clock)
        (ClockRetainedFinalSplice.final P hR hc hsmall clock) := by
    rw [hm, hf]
  exact (Sigma.mk.inj_iff.mp hpack).2

private theorem eval_heq_cast {a b : ℕ} (h : a = b)
    (f : Fin a → ℝ) (g : Fin b → ℝ) (hfg : f ≍ g) (k : Fin a) :
    f k = g (Fin.cast h k) := by
  cases h
  exact congrFun (eq_of_heq hfg) k

theorem fixedRootTable_eq_actual_cast (clock : ClockLaw.Clock)
    (k : Fin (fixedRootSize P hR hc hsmall)) :
    fixedRootTable P hR hc hsmall clock k =
      ClockRetainedFinalSplice.table P hR hc hsmall clock
        (Fin.cast (fixedRootSize_eq_clock P hR hc hsmall clock) k) :=
  eval_heq_cast (fixedRootSize_eq_clock P hR hc hsmall clock)
    (fixedRootTable P hR hc hsmall clock)
    (ClockRetainedFinalSplice.table P hR hc hsmall clock)
    (fixedRootTable_heq P hR hc hsmall clock) k

/-- The literal coefficient array transported to clock zero's register carrier. -/
def anchoredTable (clock : ClockLaw.Clock) :
    Fin (ClockRetainedFinalSplice.size P hR hc hsmall anchor) → ℝ :=
  fun k => ClockRetainedFinalSplice.table P hR hc hsmall clock
    (Fin.cast (whole_size_clock P hR hc hsmall anchor clock) k)

theorem anchoredTable_eq_fixedRootTable (clock : ClockLaw.Clock)
    (k : Fin (ClockRetainedFinalSplice.size P hR hc hsmall anchor)) :
    anchoredTable P hR hc hsmall clock k =
      fixedRootTable P hR hc hsmall clock
        (Fin.cast (fixedRootSize_eq_clock P hR hc hsmall anchor).symm k) := by
  unfold anchoredTable
  rw [fixedRootTable_eq_actual_cast P hR hc hsmall clock]
  congr 1

theorem measurable_anchoredTable
    (hm : ∀ i : ClockNoisyLayer.Index P,
      Measurable (mainPayload P hR hc hsmall i))
    (hf : ∀ i : ClockNoisyLayer.Index P,
      Measurable (finalPayload P hR hc hsmall i)) :
    Measurable (anchoredTable P hR hc hsmall) := by
  apply measurable_pi_iff.mpr
  intro k
  have hfixed := (measurable_pi_apply
    (Fin.cast (fixedRootSize_eq_clock P hR hc hsmall anchor).symm k)).comp
      (measurable_fixedRootTable P hR hc hsmall hm hf)
  convert hfixed using 1
  funext clock
  exact anchoredTable_eq_fixedRootTable P hR hc hsmall clock k

private def localCoeffCast {s t : Σ c : ℕ, Oracle.Program c .point}
    (h : s = t) (coeff : Fin s.1 → ℝ) : Fin t.1 → ℝ := by
  cases h
  exact coeff

private theorem localCoeffCast_apply {s t : Σ c : ℕ, Oracle.Program c .point}
    (h : s = t) (coeff : Fin s.1 → ℝ) (k : Fin t.1) :
    localCoeffCast h coeff k = coeff (Fin.cast (congrArg Sigma.fst h).symm k) := by
  cases h
  rfl

theorem transport_anchorTable_eq_anchoredTable (clock : ClockLaw.Clock) (ell : ℕ) :
    ClockRetainedTapeTransport.anchorTable P hR hc hsmall clock ell =
      anchoredTable P hR hc hsmall clock := by
  change localCoeffCast
    (ClockRetainedTapeTransport.codeShape_clock P hR hc hsmall clock ell)
    (ClockRetainedFinalSplice.table P hR hc hsmall clock) =
      anchoredTable P hR hc hsmall clock
  funext k
  have h := localCoeffCast_apply
    (ClockRetainedTapeTransport.codeShape_clock P hR hc hsmall clock ell)
    (ClockRetainedFinalSplice.table P hR hc hsmall clock) k
  unfold anchoredTable
  convert h using 1
  congr 1

theorem measurable_anchorTable_of_payload (ell : ℕ)
    (hm : ∀ i : ClockNoisyLayer.Index P,
      Measurable (mainPayload P hR hc hsmall i))
    (hf : ∀ i : ClockNoisyLayer.Index P,
      Measurable (finalPayload P hR hc hsmall i)) :
    Measurable (fun clock : ClockLaw.Clock =>
      ClockRetainedTapeTransport.anchorTable P hR hc hsmall clock ell) := by
  have hfun : (fun clock : ClockLaw.Clock =>
      ClockRetainedTapeTransport.anchorTable P hR hc hsmall clock ell) =
      anchoredTable P hR hc hsmall := by
    funext clock
    exact transport_anchorTable_eq_anchoredTable P hR hc hsmall clock ell
  rw [hfun]
  exact measurable_anchoredTable P hR hc hsmall hm hf

theorem measurable_mainPayload (i : ClockNoisyLayer.Index P) :
    Measurable (mainPayload P hR hc hsmall i) := by
  apply measurable_mainPayload_of_canonical
  have h := measurable_data_payload P hR hc hsmall (P.K : ℝ) 0 0 0
    (fun _ : ClockLaw.Clock => Real.sqrt P.delta)
    (fun clock => ClockNoisyLayer.radius P clock i)
    (fun _ => 1/(2*P.Ds*Real.sqrt (ClockNoisyLayer.N P:ℝ)*Real.sqrt (2*P.delta)))
    measurable_const (measurable_radius P i) measurable_const
  change Measurable (fun clock : ClockLaw.Clock => alignedPayload
    (Oracle.CubicExecutableWorkShift.data P hR hc hsmall (Real.sqrt P.delta)
      (ClockNoisyLayer.radius P clock i)
      (1/(2*P.Ds*Real.sqrt (ClockNoisyLayer.N P:ℝ)*Real.sqrt (2*P.delta)))
      (P.K:ℝ))
    (shape (Oracle.CubicExecutableWorkShift.data P hR hc hsmall 0 0 0 (P.K:ℝ)))
    (mainShape_eq_canonical P hR hc hsmall i clock))
  exact h

theorem measurable_finalPayload (i : ClockNoisyLayer.Index P) :
    Measurable (finalPayload P hR hc hsmall i) := by
  apply measurable_finalPayload_of_canonical
  have h := measurable_data_payload P hR hc hsmall (P.K : ℝ) 0 0 0
    (fun _ : ClockLaw.Clock => Real.sqrt P.delta)
    (fun clock => (FinalMeanScheduledData.state P i clock).radius)
    (fun clock => ClockRetainedFinalSplice.width P clock i)
    measurable_const (measurable_final_radius P i) (measurable_width P i)
  change Measurable (fun clock : ClockLaw.Clock => alignedPayload
    (Oracle.CubicExecutableWorkShift.data P hR hc hsmall (Real.sqrt P.delta)
      (FinalMeanScheduledData.state P i clock).radius
      (ClockRetainedFinalSplice.width P clock i) (P.K:ℝ))
    (shape (Oracle.CubicExecutableWorkShift.data P hR hc hsmall 0 0 0 (P.K:ℝ)))
    (finalShape_eq_canonical P hR hc hsmall i clock))
  exact h

theorem measurable_anchorTable (ell : ℕ) :
    Measurable (fun clock : ClockLaw.Clock =>
      ClockRetainedTapeTransport.anchorTable P hR hc hsmall clock ell) :=
  measurable_anchorTable_of_payload P hR hc hsmall ell
    (measurable_mainPayload P hR hc hsmall)
    (measurable_finalPayload P hR hc hsmall)

end AcceleratedLogConcave.Root.ClockRetainedTableMeasurability
