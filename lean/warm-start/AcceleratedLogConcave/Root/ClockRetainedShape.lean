import AcceleratedLogConcave.Root.ClockRetainedFinalSplice
import AcceleratedLogConcave.Oracle.RecursiveExecutableParameterShape

/-! The literal retained root program has one fixed register count and syntax
for every source clock, including clock zero. This is the structural gate for
transporting a single canonical tape space across the clock mixture. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace AcceleratedLogConcave.Root.ClockRetainedShape
open Oracle Oracle.RecursiveExecutableParameterShape
open ClockNoisyLayer ClockRetainedFinalSplice

variable (P : SourceSchedule) (hR : P.R ≤ 1/2) (hc : 0 < P.csch)
  (hsmall : P.csch < 1/160)

/-- The actual main child has identical register count and syntax at every
fixed clock, although its coefficient array varies. -/
theorem main_child_shape_clock (i : Index P) (clock clock' : ClockLaw.Clock) :
    shape (ClockNoisyLayer.child P hR hc hsmall clock i) =
      shape (ClockNoisyLayer.child P hR hc hsmall clock' i) := by
  unfold ClockNoisyLayer.child OuterMainStability.mainData
    Oracle.CubicExecutableWorkShift.data
  apply mean_shape

theorem main_child_program_heq (i : Index P) (clock clock' : ClockLaw.Clock) :
    ClockNoisyLayer.p P hR hc hsmall clock i ≍
      ClockNoisyLayer.p P hR hc hsmall clock' i :=
  (Sigma.mk.inj_iff.mp (main_child_shape_clock P hR hc hsmall i clock clock')).2

/-- The fresh final child likewise has fixed syntax across source clocks. -/
theorem final_child_shape_clock (i : Index P) (clock clock' : ClockLaw.Clock) :
    shape (FinalMeanScheduledData.finalData P hR hc hsmall i clock) =
      shape (FinalMeanScheduledData.finalData P hR hc hsmall i clock') := by
  unfold FinalMeanScheduledData.finalData Oracle.CubicExecutableWorkShift.data
  apply mean_shape

theorem final_child_program_heq (i : Index P) (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.pf P hR hc hsmall clock i ≍
      ClockRetainedFinalSplice.pf P hR hc hsmall clock' i :=
  (Sigma.mk.inj_iff.mp (final_child_shape_clock P hR hc hsmall i clock clock')).2

theorem main_sizes_clock (clock clock' : ClockLaw.Clock) :
    ClockNoisyLayer.c P hR hc hsmall clock =
      ClockNoisyLayer.c P hR hc hsmall clock' := by
  funext i
  exact (Sigma.mk.inj_iff.mp (main_child_shape_clock P hR hc hsmall i clock clock')).1

theorem final_sizes_clock (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.cf P hR hc hsmall clock =
      ClockRetainedFinalSplice.cf P hR hc hsmall clock' := by
  funext i
  exact (Sigma.mk.inj_iff.mp (final_child_shape_clock P hR hc hsmall i clock clock')).1

theorem main_programs_heq (clock clock' : ClockLaw.Clock) :
    ClockNoisyLayer.p P hR hc hsmall clock ≍
      ClockNoisyLayer.p P hR hc hsmall clock' := by
  apply Function.hfunext rfl
  intro i j hij
  have h : i = j := eq_of_heq hij
  subst j
  exact main_child_program_heq P hR hc hsmall i clock clock'

theorem final_programs_heq (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.pf P hR hc hsmall clock ≍
      ClockRetainedFinalSplice.pf P hR hc hsmall clock' := by
  apply Function.hfunext rfl
  intro i j hij
  have h : i = j := eq_of_heq hij
  subst j
  exact final_child_program_heq P hR hc hsmall i clock clock'

private theorem shape_enum_heq {s t : Σ c : ℕ, Oracle.Program c .point} (h : s = t) :
    Oracle.TapeLowering.gaussianSlotEquiv s.2 ≍
      Oracle.TapeLowering.gaussianSlotEquiv t.2 := by
  cases h
  rfl

theorem main_e_heq (i : Index P) (clock clock' : ClockLaw.Clock) :
    ClockNoisyLayer.e P hR hc hsmall clock i ≍
      ClockNoisyLayer.e P hR hc hsmall clock' i := by
  change Oracle.TapeLowering.gaussianSlotEquiv
      (shape (ClockNoisyLayer.child P hR hc hsmall clock i)).2 ≍
    Oracle.TapeLowering.gaussianSlotEquiv
      (shape (ClockNoisyLayer.child P hR hc hsmall clock' i)).2
  exact shape_enum_heq (main_child_shape_clock P hR hc hsmall i clock clock')

theorem final_ef_heq (i : Index P) (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.ef P hR hc hsmall clock i ≍
      ClockRetainedFinalSplice.ef P hR hc hsmall clock' i := by
  change Oracle.TapeLowering.gaussianSlotEquiv
      (shape (FinalMeanScheduledData.finalData P hR hc hsmall i clock)).2 ≍
    Oracle.TapeLowering.gaussianSlotEquiv
      (shape (FinalMeanScheduledData.finalData P hR hc hsmall i clock')).2
  exact shape_enum_heq (final_child_shape_clock P hR hc hsmall i clock clock')

theorem main_e_family_heq (clock clock' : ClockLaw.Clock) :
    ClockNoisyLayer.e P hR hc hsmall clock ≍
      ClockNoisyLayer.e P hR hc hsmall clock' := by
  apply Function.hfunext rfl
  intro i j hij
  have h : i = j := eq_of_heq hij
  subst j
  exact main_e_heq P hR hc hsmall i clock clock'

theorem final_ef_family_heq (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.ef P hR hc hsmall clock ≍
      ClockRetainedFinalSplice.ef P hR hc hsmall clock' := by
  apply Function.hfunext rfl
  intro i j hij
  have h : i = j := eq_of_heq hij
  subst j
  exact final_ef_heq P hR hc hsmall i clock clock'

theorem main_g_clock (i : Index P) (clock clock' : ClockLaw.Clock) :
    ClockNoisyLayer.g P hR hc hsmall clock i =
      ClockNoisyLayer.g P hR hc hsmall clock' i := by
  exact congrArg (fun s : Σ c : ℕ, Oracle.Program c .point =>
    (Oracle.tapeShape s.2).gaussianBlocks)
    (main_child_shape_clock P hR hc hsmall i clock clock')

theorem final_g_clock (i : Index P) (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.gf P hR hc hsmall clock i =
      ClockRetainedFinalSplice.gf P hR hc hsmall clock' i := by
  exact congrArg (fun s : Σ c : ℕ, Oracle.Program c .point =>
    (Oracle.tapeShape s.2).gaussianBlocks)
    (final_child_shape_clock P hR hc hsmall i clock clock')

theorem main_auxiliary_heq (D remaining : ℕ) (clock clock' : ClockLaw.Clock) :
    ClockRepeatedLayers.auxiliary P hR hc hsmall clock D remaining ≍
      ClockRepeatedLayers.auxiliary P hR hc hsmall clock' D remaining := by
  apply Function.hfunext rfl
  intro i j hij
  have h : i = j := eq_of_heq hij
  subst j
  apply Function.hfunext (congrArg Fin (main_g_clock P hR hc hsmall i clock clock'))
  intro k l hkl
  have hv : k.val = l.val := Fin.val_eq_val_of_heq hkl
  simp only [ClockRepeatedLayers.auxiliary, hv]
  rfl

theorem main_auxiliary_partial_heq (D : ℕ) (clock clock' : ClockLaw.Clock) :
    (ClockRepeatedLayers.auxiliary P hR hc hsmall clock D :
      (remaining : ℕ) → (i : Index P) →
        Fin (ClockNoisyLayer.g P hR hc hsmall clock i) → Oracle.Origin) ≍
      (ClockRepeatedLayers.auxiliary P hR hc hsmall clock' D :
        (remaining : ℕ) → (i : Index P) →
          Fin (ClockNoisyLayer.g P hR hc hsmall clock' i) → Oracle.Origin) := by
  apply Function.hfunext rfl
  intro r s hrs
  have h : r = s := eq_of_heq hrs
  subst s
  exact main_auxiliary_heq P hR hc hsmall D r clock clock'

theorem final_auxiliary_heq (ell : ℕ) (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.finalAuxiliary P hR hc hsmall clock ell ≍
      ClockRetainedFinalSplice.finalAuxiliary P hR hc hsmall clock' ell := by
  apply Function.hfunext rfl
  intro i j hij
  have h : i = j := eq_of_heq hij
  subst j
  apply Function.hfunext (congrArg Fin (final_g_clock P hR hc hsmall i clock clock'))
  intro k l hkl
  have hv : k.val = l.val := Fin.val_eq_val_of_heq hkl
  simp only [ClockRetainedFinalSplice.finalAuxiliary, hv]
  rfl

private def childTableSize (s : Σ c : ℕ, Oracle.Program c .point) : ℕ :=
  Oracle.NoisyLayer.childSize s.2

theorem main_child_table_size_clock (i : Index P) (clock clock' : ClockLaw.Clock) :
    Oracle.NoisyLayer.childSize (ClockNoisyLayer.p P hR hc hsmall clock i) =
      Oracle.NoisyLayer.childSize (ClockNoisyLayer.p P hR hc hsmall clock' i) := by
  exact congrArg childTableSize (main_child_shape_clock P hR hc hsmall i clock clock')

theorem final_child_table_size_clock (i : Index P) (clock clock' : ClockLaw.Clock) :
    Oracle.NoisyLayer.childSize (ClockRetainedFinalSplice.pf P hR hc hsmall clock i) =
      Oracle.NoisyLayer.childSize (ClockRetainedFinalSplice.pf P hR hc hsmall clock' i) := by
  exact congrArg childTableSize (final_child_shape_clock P hR hc hsmall i clock clock')

theorem main_table_size_clock (clock clock' : ClockLaw.Clock) :
    ClockNoisyLayer.tableSize P hR hc hsmall clock =
      ClockNoisyLayer.tableSize P hR hc hsmall clock' := by
  unfold ClockNoisyLayer.tableSize Oracle.NoisyLayer.publicSize
  have hsum : (∑ i, Oracle.NoisyLayer.childSize
      (ClockNoisyLayer.p P hR hc hsmall clock i)) =
      ∑ i, Oracle.NoisyLayer.childSize
        (ClockNoisyLayer.p P hR hc hsmall clock' i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact main_child_table_size_clock P hR hc hsmall i clock clock'
  rw [hsum]

theorem old_size_clock (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.oldSize P hR hc hsmall clock =
      ClockRetainedFinalSplice.oldSize P hR hc hsmall clock' := by
  unfold ClockRetainedFinalSplice.oldSize ClockPublicSetup.size
    ClockInitialLayer.extendedSize ClockNoisyLayer.tableSize
    Oracle.NoisyLayer.publicSize
  have hsum : (∑ i, Oracle.NoisyLayer.childSize
      (ClockNoisyLayer.p P hR hc hsmall clock i)) =
      ∑ i, Oracle.NoisyLayer.childSize
        (ClockNoisyLayer.p P hR hc hsmall clock' i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact main_child_table_size_clock P hR hc hsmall i clock clock'
  rw [hsum]

theorem final_size_clock (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.finalSize P hR hc hsmall clock =
      ClockRetainedFinalSplice.finalSize P hR hc hsmall clock' := by
  unfold ClockRetainedFinalSplice.finalSize
  apply Finset.sum_congr rfl
  intro i _
  exact final_child_table_size_clock P hR hc hsmall i clock clock'

/-- All public table registers, including the fresh final child tables, have
one fixed size independent of the source clock. -/
theorem whole_size_clock (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.size P hR hc hsmall clock =
      ClockRetainedFinalSplice.size P hR hc hsmall clock' := by
  unfold ClockRetainedFinalSplice.size
  rw [old_size_clock P hR hc hsmall clock clock',
    final_size_clock P hR hc hsmall clock clock']

theorem oldSlot_heq (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.oldSlot P hR hc hsmall clock ≍
      ClockRetainedFinalSplice.oldSlot P hR hc hsmall clock' := by
  apply Function.hfunext (congrArg Fin (old_size_clock P hR hc hsmall clock clock'))
  intro i j hij
  apply (Fin.heq_ext_iff (whole_size_clock P hR hc hsmall clock clock')).2
  simpa only [ClockRetainedFinalSplice.oldSlot,Fin.val_castAdd] using Fin.val_eq_val_of_heq hij

theorem assemblySlot_heq (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.assemblySlot P hR hc hsmall clock ≍
      ClockRetainedFinalSplice.assemblySlot P hR hc hsmall clock' := by
  apply Function.hfunext rfl
  intro i j hij
  apply (Fin.heq_ext_iff (whole_size_clock P hR hc hsmall clock clock')).2
  have hij' : i.val = j.val := Fin.val_eq_val_of_heq hij
  simp only [ClockRetainedFinalSplice.assemblySlot,Fin.val_natAdd,Fin.val_castAdd]
  rw [old_size_clock P hR hc hsmall clock clock',hij']

theorem correctionSlot_heq (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.correctionSlot P hR hc hsmall clock ≍
      ClockRetainedFinalSplice.correctionSlot P hR hc hsmall clock' := by
  apply Function.hfunext rfl
  intro i j hij
  apply (Fin.heq_ext_iff (whole_size_clock P hR hc hsmall clock clock')).2
  have hij' : i.val = j.val := Fin.val_eq_val_of_heq hij
  simp only [ClockRetainedFinalSplice.correctionSlot,Fin.val_natAdd]
  rw [old_size_clock P hR hc hsmall clock clock',
    final_size_clock P hR hc hsmall clock clock',hij']

theorem finalSlot_heq (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.finalSlot P hR hc hsmall clock ≍
      ClockRetainedFinalSplice.finalSlot P hR hc hsmall clock' := by
  have hfamily : (fun i : Index P => Oracle.NoisyLayer.childSize
      (ClockRetainedFinalSplice.pf P hR hc hsmall clock i)) =
      (fun i : Index P => Oracle.NoisyLayer.childSize
        (ClockRetainedFinalSplice.pf P hR hc hsmall clock' i)) := by
    funext i
    exact final_child_table_size_clock P hR hc hsmall i clock clock'
  apply Function.hfunext rfl
  intro i j hij
  have hij' : i = j := eq_of_heq hij
  subst j
  apply Function.hfunext
    (congrArg Fin (final_child_table_size_clock P hR hc hsmall i clock clock'))
  intro k l hkl
  apply (Fin.heq_ext_iff (whole_size_clock P hR hc hsmall clock clock')).2
  have hval : k.val = l.val := Fin.val_eq_val_of_heq hkl
  have hsum : (∑ x : Fin i, Oracle.NoisyLayer.childSize
      (ClockRetainedFinalSplice.pf P hR hc hsmall clock
        (Fin.castLE i.isLt.le x))) =
      ∑ x : Fin i, Oracle.NoisyLayer.childSize
        (ClockRetainedFinalSplice.pf P hR hc hsmall clock'
          (Fin.castLE i.isLt.le x)) := by
    apply Finset.sum_congr rfl
    intro x _
    exact congrFun hfamily _
  simp only [ClockRetainedFinalSplice.finalSlot,Fin.val_natAdd,Fin.val_castAdd,
    finSigmaFinEquiv_apply]
  rw [old_size_clock P hR hc hsmall clock clock', hsum, hval]

theorem mainSlots_heq (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.mainSlots P hR hc hsmall clock ≍
      ClockRetainedFinalSplice.mainSlots P hR hc hsmall clock' := by
  apply Function.hfunext (congrArg Fin
    (main_table_size_clock P hR hc hsmall clock clock'))
  intro i j hij
  apply (Fin.heq_ext_iff (whole_size_clock P hR hc hsmall clock clock')).2
  have hval : i.val = j.val := Fin.val_eq_val_of_heq hij
  simpa only [ClockRetainedFinalSplice.mainSlots, Function.comp_apply,
    ClockRetainedFinalSplice.oldSlot, ClockRepeatedLayers.slots,
    ClockPublicSetup.oldSlot, ClockInitialLayer.oldSlot,Fin.val_castAdd]
    using hval

theorem extended_size_clock (clock clock' : ClockLaw.Clock) :
    ClockInitialLayer.extendedSize P hR hc hsmall clock =
      ClockInitialLayer.extendedSize P hR hc hsmall clock' := by
  unfold ClockInitialLayer.extendedSize
  rw [main_table_size_clock P hR hc hsmall clock clock']

theorem public_sharedSlot_heq (clock clock' : ClockLaw.Clock) :
    ClockPublicSetup.sharedSlot P hR hc hsmall clock ≍
      ClockPublicSetup.sharedSlot P hR hc hsmall clock' := by
  apply Function.hfunext rfl
  intro i j hij
  apply (Fin.heq_ext_iff (old_size_clock P hR hc hsmall clock clock')).2
  have hval : i.val = j.val := Fin.val_eq_val_of_heq hij
  simp only [ClockPublicSetup.sharedSlot,Fin.val_natAdd]
  rw [extended_size_clock P hR hc hsmall clock clock',hval]

theorem public_slopeSlot_heq (clock clock' : ClockLaw.Clock) :
    ClockPublicSetup.slopeSlot P hR hc hsmall clock ≍
      ClockPublicSetup.slopeSlot P hR hc hsmall clock' := by
  apply Function.hfunext rfl
  intro i j hij
  apply (Fin.heq_ext_iff (old_size_clock P hR hc hsmall clock clock')).2
  have hval : i.val = j.val := Fin.val_eq_val_of_heq hij
  simp only [ClockPublicSetup.slopeSlot,Fin.val_natAdd,Fin.val_castAdd]
  rw [extended_size_clock P hR hc hsmall clock clock',hval]

theorem public_splitSlots_heq (s : Fin 2) (clock clock' : ClockLaw.Clock) :
    ClockPublicSetup.splitSlots P hR hc hsmall clock s ≍
      ClockPublicSetup.splitSlots P hR hc hsmall clock' s := by
  apply Function.hfunext rfl
  intro i j hij
  have hij' : i = j := eq_of_heq hij
  subst j
  apply (Fin.heq_ext_iff (old_size_clock P hR hc hsmall clock clock')).2
  fin_cases s <;> fin_cases i <;>
    simp [ClockPublicSetup.splitSlots,ClockPublicSetup.sharedSlot,
      extended_size_clock P hR hc hsmall clock clock']

theorem public_splitRow_heq (s : Fin 2) (clock clock' : ClockLaw.Clock) :
    ClockPublicSetup.splitRow P hR hc hsmall clock s ≍
      ClockPublicSetup.splitRow P hR hc hsmall clock' s := by
  unfold ClockPublicSetup.splitRow
  congr! 1
  · exact old_size_clock P hR hc hsmall clock clock'
  · exact public_splitSlots_heq P hR hc hsmall s clock clock'

theorem public_directRow_heq (i : Index P) (clock clock' : ClockLaw.Clock) :
    ClockPublicSetup.directRow P hR hc hsmall clock i ≍
      ClockPublicSetup.directRow P hR hc hsmall clock' i := by
  unfold ClockPublicSetup.directRow
  congr! 1
  · exact old_size_clock P hR hc hsmall clock clock'
  · congr! 1
    · exact congrArg (fun n => Fin n × Ref ClockPublicSetup.splitCtx Ty.point)
        (old_size_clock P hR hc hsmall clock clock')
    · congr! 1
      · exact congrArg Fin (old_size_clock P hR hc hsmall clock clock')
      · apply (Fin.heq_ext_iff (old_size_clock P hR hc hsmall clock clock')).2
        simp only [ClockPublicSetup.slopeSlot, Fin.val_natAdd, Fin.val_castAdd]
        exact congrArg (· + i.val)
          (extended_size_clock P hR hc hsmall clock clock')
    · congr! 1

theorem splitRow_heq (j : Fin 2) (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.splitRow P hR hc hsmall clock j ≍
      ClockRetainedFinalSplice.splitRow P hR hc hsmall clock' j := by
  unfold ClockRetainedFinalSplice.splitRow
  congr! 1
  · exact old_size_clock P hR hc hsmall clock clock'
  · exact whole_size_clock P hR hc hsmall clock clock'
  · exact oldSlot_heq P hR hc hsmall clock clock'
  · exact public_splitRow_heq P hR hc hsmall j clock clock'

theorem publicDirectRow_heq (i : Index P) (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.publicDirectRow P hR hc hsmall clock i ≍
      ClockRetainedFinalSplice.publicDirectRow P hR hc hsmall clock' i := by
  unfold ClockRetainedFinalSplice.publicDirectRow
  congr! 1
  · exact old_size_clock P hR hc hsmall clock clock'
  · exact whole_size_clock P hR hc hsmall clock clock'
  · exact oldSlot_heq P hR hc hsmall clock clock'
  · exact public_directRow_heq P hR hc hsmall i clock clock'

theorem splitRows_heq (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.splitRow P hR hc hsmall clock ≍
      ClockRetainedFinalSplice.splitRow P hR hc hsmall clock' := by
  apply Function.hfunext rfl
  intro i j hij
  have h : i = j := eq_of_heq hij
  subst j
  exact splitRow_heq P hR hc hsmall i clock clock'

theorem publicDirectRows_heq (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.publicDirectRow P hR hc hsmall clock ≍
      ClockRetainedFinalSplice.publicDirectRow P hR hc hsmall clock' := by
  apply Function.hfunext rfl
  intro i j hij
  have h : i = j := eq_of_heq hij
  subst j
  exact publicDirectRow_heq P hR hc hsmall i clock clock'

theorem finish_heq (ell : ℕ) (clock clock' : ClockLaw.Clock) :
    (ClockRetainedFinalSplice.finish P hR hc hsmall clock ell :
      ClockRetainedFinalSplice.Finish P hR hc hsmall clock) ≍
      (ClockRetainedFinalSplice.finish P hR hc hsmall clock' ell :
        ClockRetainedFinalSplice.Finish P hR hc hsmall clock') := by
  unfold ClockRetainedFinalSplice.finish
  congr! 5 <;> (try subst_vars; try simp_all only)
  all_goals first
    | exact whole_size_clock P hR hc hsmall clock clock'
    | exact final_sizes_clock P hR hc hsmall clock clock'
    | exact final_programs_heq P hR hc hsmall clock clock'
    | exact final_ef_family_heq P hR hc hsmall clock clock'
    | exact finalSlot_heq P hR hc hsmall clock clock'
    | exact correctionSlot_heq P hR hc hsmall clock clock'
    | exact final_auxiliary_heq P hR hc hsmall ell clock clock'
    | rfl

theorem loop_heq (ell : ℕ) (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.loop P hR hc hsmall clock ell ≍
      ClockRetainedFinalSplice.loop P hR hc hsmall clock' ell := by
  unfold ClockRetainedFinalSplice.loop
  congr! 1
  all_goals first
    | exact whole_size_clock P hR hc hsmall clock clock'
    | exact main_sizes_clock P hR hc hsmall clock clock'
    | exact main_programs_heq P hR hc hsmall clock clock'
    | exact mainSlots_heq P hR hc hsmall clock clock'
    | exact main_e_family_heq P hR hc hsmall clock clock'
    | exact main_auxiliary_partial_heq P hR hc hsmall (P.K+4) clock clock'
    | exact finish_heq P hR hc hsmall ell clock clock'

theorem rhoSlot_heq (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.oldSlot P hR hc hsmall clock
        (ClockRepeatedLayers.rhoSlot P hR hc hsmall clock) ≍
      ClockRetainedFinalSplice.oldSlot P hR hc hsmall clock'
        (ClockRepeatedLayers.rhoSlot P hR hc hsmall clock') := by
  apply (Fin.heq_ext_iff (whole_size_clock P hR hc hsmall clock clock')).2
  simp only [ClockRetainedFinalSplice.oldSlot,ClockRepeatedLayers.rhoSlot,
    ClockPublicSetup.oldSlot,ClockInitialLayer.rhoSlot,Fin.val_castAdd,Fin.val_natAdd]
  rw [main_table_size_clock P hR hc hsmall clock clock']

theorem initialized_heq (ell : ℕ) (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.initialized P hR hc hsmall clock ell ≍
      ClockRetainedFinalSplice.initialized P hR hc hsmall clock' ell := by
  unfold ClockRetainedFinalSplice.initialized
  congr! 1
  all_goals first
    | exact whole_size_clock P hR hc hsmall clock clock'
    | exact rhoSlot_heq P hR hc hsmall clock clock'
    | exact loop_heq P hR hc hsmall ell clock clock'

theorem assembled_heq (ell : ℕ) (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.assembled P hR hc hsmall clock ell ≍
      ClockRetainedFinalSplice.assembled P hR hc hsmall clock' ell := by
  unfold ClockRetainedFinalSplice.assembled
  congr! 1
  all_goals first
    | exact whole_size_clock P hR hc hsmall clock clock'
    | exact assemblySlot_heq P hR hc hsmall clock clock'
    | exact initialized_heq P hR hc hsmall ell clock clock'

theorem code_heq (ell : ℕ) (clock clock' : ClockLaw.Clock) :
    ClockRetainedFinalSplice.code P hR hc hsmall clock ell ≍
      ClockRetainedFinalSplice.code P hR hc hsmall clock' ell := by
  unfold ClockRetainedFinalSplice.code
  congr! 1
  · exact whole_size_clock P hR hc hsmall clock clock'
  · congr! 1
  · congr! 1
    · congr! 1
    · congr! 1
      all_goals first
        | exact splitRows_heq P hR hc hsmall clock clock'
        | exact publicDirectRows_heq P hR hc hsmall clock clock'
        | exact assembled_heq P hR hc hsmall ell clock clock'
        | congr! 1
      all_goals first
        | exact splitRows_heq P hR hc hsmall clock clock'
        | exact publicDirectRows_heq P hR hc hsmall clock clock'
        | exact assembled_heq P hR hc hsmall ell clock clock'
        | congr! 1
      all_goals first
        | exact splitRows_heq P hR hc hsmall clock clock'
        | exact publicDirectRows_heq P hR hc hsmall clock clock'
        | exact assembled_heq P hR hc hsmall ell clock clock'

/-- The literal retained root executable has one register count and one
program syntax for every value of the source clock. -/
theorem whole_code_shape_clock (ell : ℕ) (clock clock' : ClockLaw.Clock) :
    (⟨ClockRetainedFinalSplice.size P hR hc hsmall clock,
        ClockRetainedFinalSplice.code P hR hc hsmall clock ell⟩ :
      Σ c : ℕ, Oracle.Program c .point) =
    ⟨ClockRetainedFinalSplice.size P hR hc hsmall clock',
      ClockRetainedFinalSplice.code P hR hc hsmall clock' ell⟩ := by
  apply Sigma.ext (whole_size_clock P hR hc hsmall clock clock')
  exact code_heq P hR hc hsmall ell clock clock'

end AcceleratedLogConcave.Root.ClockRetainedShape
