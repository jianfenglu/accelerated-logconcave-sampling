/- NEW source-only reconstruction: surviving body with minimal reconstructed imports. -/
import AcceleratedLogConcave.Numerics.CenterMeanPhasePrimitiveSupport
import AcceleratedLogConcave.Tensor.PhasePolynomialPullback
import AcceleratedLogConcave.Tensor.PhasePrimitiveBudgets

/-! Exact physical K spatial tensors and their two mixed-block phase embeddings.
No quantitative estimate is asserted in this file. The lower block keeps the
minus sign and transposes only the two matrix slots, never derivative slots. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor Tensor.AdjointReduction Tensor.CoordinateReduction
open Tensor.Ordered.Graph
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))
local notation "e" => EuclideanSpace.basisFun (Fin D) ℝ

/-- Literal matrix coordinate of the original transported Stein kernel transpose. -/
def physicalTransportEntry (d : Data (Fin D)) (i k : Fin D) (y : E) : ℝ :=
  inner ℝ (e i) (K d y (e k))

theorem smooth_physicalTransportEntry (d : Data (Fin D)) (i k : Fin D) :
    ContDiff ℝ ∞ (physicalTransportEntry d i k) := by
  exact contDiff_const.inner ℝ
    ((Transport.contDiff_infty_transportedSteinKernelTranspose d.hF d.hell d.hlo d.hup
      d.x d.hr d.hb d.hb1 d.hsmall).clm_apply contDiff_const)

/-- Derivative slots are `inl`; matrix row and column are `inr 0`, `inr 1`. -/
def physicalTransportJet (d : Data (Fin D)) (j : ℕ) (y : E) :
    Coeff (Fin j ⊕ Fin 2) D :=
  WithLp.toLp 2 (fun v => partialAlong
    (fun u : Fin j => coordinateDirection D (v (.inl u))) (List.finRange j)
    (physicalTransportEntry d (v (.inr 0)) (v (.inr 1))) y)

/-- The upper-right block: spatial and row slots are position; column is momentum. -/
def transportUpperEmbedding (j : ℕ) : (Fin j ⊕ Fin 2) → (Fin D ↪ Fin (D+D))
  | .inl _ => Fin.castAddEmb D
  | .inr k => if k = 0 then Fin.castAddEmb D else Fin.natAddEmb D

/-- The lower-left block: spatial and column slots are position; row is momentum. -/
def transportLowerEmbedding (j : ℕ) : (Fin j ⊕ Fin 2) → (Fin D ↪ Fin (D+D))
  | .inl _ => Fin.castAddEmb D
  | .inr k => if k = 0 then Fin.natAddEmb D else Fin.castAddEmb D

/-- Only the terminal matrix slots are exchanged. -/
def physicalTransportTransposeJet (d : Data (Fin D)) (j : ℕ) (y : E) :
    Coeff (Fin j ⊕ Fin 2) D :=
  WithLp.toLp 2 (fun v => physicalTransportJet d j y (v ∘ centerGradientSlotSwap j))

private theorem partialAlong_position {I : Type*} (v : I → EP) (J : List I)
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (z : EP) :
    partialAlong v J (fun x => f (phasePosition x)) z =
      partialAlong (fun i => phasePosition (v i)) J f (phasePosition z) := by
  change partialAlong v J (f ∘ phasePositionCLM) z = _
  rw [PolynomialClosure.partialAlong_map_id,
    PolynomialClosure.partialAlong_comp_linear hf]
  conv_rhs => rw [PolynomialClosure.partialAlong_map_id]
  simp only [List.map_map, Function.comp_def]
  rfl

private theorem partialAlong_zero {I V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (v : I → V) (J : List I) :
    partialAlong v J (fun _ => (0 : ℝ)) = fun _ => 0 := by
  induction J with
  | nil => rfl
  | cons i J ih => rw [partialAlong, ih]; funext x; simp [dir]

private theorem castAdd_ne_natAdd (i k : Fin D) :
    Fin.castAdd D i ≠ Fin.natAdd D k := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

/-- A single incompatible coordinate proves an entire padded entry vanishes. -/
private theorem pad_zero_at_slot {j : ℕ}
    (emb : (Fin j ⊕ Fin 2) → (Fin D ↪ Fin (D+D)))
    (T : Coeff (Fin j ⊕ Fin 2) D) (b : Fin j ⊕ Fin 2 → Fin (D+D))
    (s : Fin j ⊕ Fin 2) (h : ∀ i : Fin D, emb s i ≠ b s) :
    coordinatePadCoeff emb T b = 0 := by
  apply coordinatePadCoeff_off_image
  rintro ⟨v, hv⟩
  exact h (v s) (congrFun hv s)

private theorem transportJet_position_directions (d : Data (Fin D)) (L a : ℝ)
    (j : ℕ) (z : EP) (b : Fin j ⊕ Fin 2 → Fin (D+D))
    (w : Fin j → Fin D) (hw : ∀ i, b (.inl i) = Fin.castAdd D (w i)) :
    phaseCoefficientJet (phaseCoefficients d L a) .transport j z b =
      L⁻¹ * partialAlong (fun i => coordinateDirection D (w i)) (List.finRange j)
        (fun y => skewBlockEntry (K d y)
          (finSumFinEquiv.symm (b (.inr 0)))
          (finSumFinEquiv.symm (b (.inr 1)))) (phasePosition z) := by
  let f : E → ℝ := fun y => skewBlockEntry (K d y)
    (finSumFinEquiv.symm (b (.inr 0))) (finSumFinEquiv.symm (b (.inr 1)))
  have hf : ContDiff ℝ ∞ f := by
    dsimp [f]
    cases finSumFinEquiv.symm (b (.inr 0)) <;>
      cases finSumFinEquiv.symm (b (.inr 1))
    · exact contDiff_const
    · exact smooth_physicalTransportEntry d _ _
    · exact (smooth_physicalTransportEntry d _ _).neg
    · exact contDiff_const
  change partialAlong (fun u : Fin j => coordinateDirection (D+D) (b (.inl u)))
    (List.finRange j) (fun x => L⁻¹ * f (phasePosition x)) z = _
  have hfc : ContDiff ℝ ∞ (fun x : EP => f (phasePosition x)) :=
    hf.comp smooth_phasePosition
  rw [partialAlong_const_mul _ _ _ hfc]
  dsimp only
  rw [partialAlong_position _ _ f hf]
  congr 1
  have hv : (fun i : Fin j => phasePosition (coordinateDirection (D+D) (b (.inl i)))) =
      fun i => coordinateDirection D (w i) := by
    funext i
    rw [hw i, phasePosition_coordinate_castAdd]
  rw [hv]

/-- A momentum derivative annihilates the actual phase transport coefficient. -/
theorem phaseTransportJet_momentum_derivative (d : Data (Fin D)) (L a : ℝ)
    (j : ℕ) (z : EP) (b : Fin j ⊕ Fin 2 → Fin (D+D))
    (i : Fin j) (k : Fin D) (hk : b (.inl i) = Fin.natAdd D k) :
    phaseCoefficientJet (phaseCoefficients d L a) .transport j z b = 0 := by
  let f : E → ℝ := fun y => L⁻¹ * skewBlockEntry (K d y)
    (finSumFinEquiv.symm (b (.inr 0))) (finSumFinEquiv.symm (b (.inr 1)))
  have hf : ContDiff ℝ ∞ f := by
    dsimp [f]
    cases finSumFinEquiv.symm (b (.inr 0)) <;>
      cases finSumFinEquiv.symm (b (.inr 1))
    · simpa only [skewBlockEntry, mul_zero] using
        (contDiff_const : ContDiff ℝ ∞ (fun _ : E => (0 : ℝ)))
    · exact (contDiff_const : ContDiff ℝ ∞ (fun _ : E => L⁻¹)).mul
        (smooth_physicalTransportEntry d _ _)
    · exact (contDiff_const : ContDiff ℝ ∞ (fun _ : E => L⁻¹)).mul
        (smooth_physicalTransportEntry d _ _).neg
    · simpa only [skewBlockEntry, mul_zero] using
        (contDiff_const : ContDiff ℝ ∞ (fun _ : E => (0 : ℝ)))
  change partialAlong (fun u : Fin j => coordinateDirection (D+D) (b (.inl u)))
    (List.finRange j) (fun x => f (phasePosition x)) z = 0
  rw [partialAlong_position _ _ f hf, partialAlong_zero_direction _ _ _
    ⟨i, by simp, by rw [hk, phasePosition_coordinate_natAdd]⟩]

/-- Exact all-order tensor equality to two zero embeddings. Neither L nor D
needs to be positive. The lower block is minus the terminal-slot transpose. -/
theorem phaseTransportJet_eq_two_pads (d : Data (Fin D)) (L a : ℝ)
    (j : ℕ) (z : EP) :
    phaseCoefficientJet (phaseCoefficients d L a) .transport j z =
      L⁻¹ • (coordinatePadCoeff (transportUpperEmbedding j)
        (physicalTransportJet d j (phasePosition z)) +
        coordinatePadCoeff (transportLowerEmbedding j)
          ((-1 : ℝ) • physicalTransportTransposeJet d j (phasePosition z))) := by
  classical
  apply (WithLp.equiv 2 _).injective
  funext b
  change Fin j ⊕ Fin 2 → Fin (D+D) at b
  change phaseCoefficientJet (phaseCoefficients d L a) .transport j z b =
    L⁻¹ * (coordinatePadCoeff _ _ b + coordinatePadCoeff _ _ b)
  by_cases hd : ∀ i : Fin j, ∃ k : Fin D, b (.inl i) = Fin.castAdd D k
  · choose w hw using hd
    rw [transportJet_position_directions d L a j z b w hw]
    cases ho : finSumFinEquiv.symm (b (.inr 0)) with
    | inl o =>
      have h0 : b (.inr 0) = Fin.castAdd D o := by simpa using congrArg finSumFinEquiv ho
      have hl : coordinatePadCoeff (transportLowerEmbedding j)
          ((-1 : ℝ) • physicalTransportTransposeJet d j (phasePosition z)) b = 0 := by
        apply pad_zero_at_slot _ _ b (.inr 0)
        intro k
        simpa [transportLowerEmbedding, h0]
          using (castAdd_ne_natAdd o k).symm
      rw [hl, add_zero]
      cases hi : finSumFinEquiv.symm (b (.inr 1)) with
      | inl i =>
        have h1 : b (.inr 1) = Fin.castAdd D i := by simpa using congrArg finSumFinEquiv hi
        have hu : coordinatePadCoeff (transportUpperEmbedding j)
            (physicalTransportJet d j (phasePosition z)) b = 0 := by
          apply pad_zero_at_slot _ _ b (.inr 1)
          intro k
          simpa [transportUpperEmbedding, h1] using (castAdd_ne_natAdd i k).symm
        rw [hu]
        simp only [skewBlockEntry, partialAlong_zero, mul_zero]
      | inr i =>
        have h1 : b (.inr 1) = Fin.natAdd D i := by simpa using congrArg finSumFinEquiv hi
        let v : Fin j ⊕ Fin 2 → Fin D := Sum.elim w ![o,i]
        have hb : b = fun s => transportUpperEmbedding j s (v s) := by
          funext s
          cases s with
          | inl u => exact hw u
          | inr u => fin_cases u <;> simp [transportUpperEmbedding, v, h0, h1]
        rw [hb, coordinatePadCoeff_at_image]
        rfl
    | inr o =>
      have h0 : b (.inr 0) = Fin.natAdd D o := by simpa using congrArg finSumFinEquiv ho
      have hu : coordinatePadCoeff (transportUpperEmbedding j)
          (physicalTransportJet d j (phasePosition z)) b = 0 := by
        apply pad_zero_at_slot _ _ b (.inr 0)
        intro k
        simpa [transportUpperEmbedding, h0] using castAdd_ne_natAdd k o
      rw [hu, zero_add]
      cases hi : finSumFinEquiv.symm (b (.inr 1)) with
      | inl i =>
        have h1 : b (.inr 1) = Fin.castAdd D i := by simpa using congrArg finSumFinEquiv hi
        let v : Fin j ⊕ Fin 2 → Fin D := Sum.elim w ![o,i]
        have hb : b = fun s => transportLowerEmbedding j s (v s) := by
          funext s
          cases s with
          | inl u => exact hw u
          | inr u => fin_cases u <;> simp [transportLowerEmbedding, v, h0, h1]
        rw [hb, coordinatePadCoeff_at_image]
        simp only [skewBlockEntry, partialAlong_neg]
        change L⁻¹ * (-partialAlong (fun u => coordinateDirection D (w u))
          (List.finRange j) (physicalTransportEntry d i o) (phasePosition z)) =
          L⁻¹ * ((-1 : ℝ) * physicalTransportJet d j (phasePosition z)
            (v ∘ centerGradientSlotSwap j))
        simp only [physicalTransportJet, centerGradientSlotSwap, Function.comp_def,
          Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.refl_apply, v,
          Sum.elim_inl, Sum.elim_inr, Equiv.swap_apply_left, Equiv.swap_apply_right,
          Matrix.cons_val_zero, Matrix.cons_val_one, neg_mul, one_mul]
      | inr i =>
        have h1 : b (.inr 1) = Fin.natAdd D i := by simpa using congrArg finSumFinEquiv hi
        have hl : coordinatePadCoeff (transportLowerEmbedding j)
            ((-1 : ℝ) • physicalTransportTransposeJet d j (phasePosition z)) b = 0 := by
          apply pad_zero_at_slot _ _ b (.inr 1)
          intro k
          simpa [transportLowerEmbedding, h1] using castAdd_ne_natAdd k i
        rw [hl]
        simp only [skewBlockEntry, partialAlong_zero, mul_zero]
  · push Not at hd
    obtain ⟨i, hi⟩ := hd
    have hk : ∃ k : Fin D, b (.inl i) = Fin.natAdd D k := by
      cases he : finSumFinEquiv.symm (b (.inl i)) with
      | inl k => exact False.elim (hi k (by simpa using congrArg finSumFinEquiv he))
      | inr k => exact ⟨k, by simpa using congrArg finSumFinEquiv he⟩
    obtain ⟨k, hk⟩ := hk
    rw [phaseTransportJet_momentum_derivative d L a j z b i k hk]
    have hu : coordinatePadCoeff (transportUpperEmbedding j)
        (physicalTransportJet d j (phasePosition z)) b = 0 := by
      apply pad_zero_at_slot _ _ b (.inl i)
      intro u
      simpa [transportUpperEmbedding, hk] using castAdd_ne_natAdd u k
    have hl : coordinatePadCoeff (transportLowerEmbedding j)
        ((-1 : ℝ) • physicalTransportTransposeJet d j (phasePosition z)) b = 0 := by
      apply pad_zero_at_slot _ _ b (.inl i)
      intro u
      simpa [transportLowerEmbedding, hk] using castAdd_ne_natAdd u k
    rw [hu, hl, add_zero, mul_zero]

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
