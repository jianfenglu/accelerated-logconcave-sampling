import AcceleratedLogConcave.Analysis.AnglePhaseCoefficients
import AcceleratedLogConcave.Analysis.AngleDisplacementPullback
import AcceleratedLogConcave.Tensor.CoordinateEmbeddingConsumers
import AcceleratedLogConcave.Tensor.PhasePrimitiveBudgets

/-! Literal phase-gradient jets are zero-padded physical displacement jets.
This module supplies no physical jet bound and assumes no positive dimension. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.AnglePhase
open Tensor Tensor.AdjointReduction Tensor.CoordinateReduction Tensor.PhaseExpression
open Tensor.PhaseGeneratorIdentification Tensor.Ordered.Graph
open Numerics.CenterMeanSecondJetSource
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

private theorem partialAlong_map_index {I J V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : J → V) (g : I → J) (L : List I) (f : V → ℝ) :
    partialAlong d (L.map g) f = partialAlong (fun i => d (g i)) L f := by
  induction L with
  | nil => rfl
  | cons i L ih => simp only [List.map_cons, partialAlong, ih]

@[simp] theorem phasePosition_coordinate_castAdd (i : Fin D) :
    phasePosition (coordinateDirection (D+D) (Fin.castAdd D i)) = coordinateDirection D i := by
  ext k
  simp [phasePosition_apply, coordinateDirection, finSumFinEquiv_apply_left]

@[simp] theorem phasePosition_coordinate_natAdd (i : Fin D) :
    phasePosition (coordinateDirection (D+D) (Fin.natAdd D i)) = 0 := by
  ext k
  have hne : Fin.castAdd D k ≠ Fin.natAdd D i := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  change (Pi.single (Fin.natAdd D i) 1 : Fin (D+D) → ℝ) (Fin.castAdd D k) = 0
  exact Pi.single_eq_of_ne (M := fun _ : Fin (D+D) => ℝ) hne 1

private theorem basis_eq_coordinate (i : Fin D) :
    EuclideanSpace.basisFun (Fin D) ℝ i = coordinateDirection D i := by
  simp [EuclideanSpace.basisFun_apply, coordinateDirection, EuclideanSpace.single]

/-- The output slot is `inr 0`; the first derivative is `inr 1`. -/
def physicalDisplacementJet (T : E → E) (j : ℕ) (y : E) : Coeff (Fin j ⊕ Fin 2) D :=
  WithLp.toLp 2 (fun v => partialAlong (coordinateDirection D)
    (v (.inr 1) :: (List.finRange j).map (fun i => v (.inl i)))
    (fun x => inner ℝ (coordinateDirection D (v (.inr 0))) (T x - x)) y)

private theorem gradient_entry_pullback (T : E → E) (hT : ContDiff ℝ ∞ T)
    (M : E) (q a : ℝ) (j : ℕ) (z : EP) (b : Fin j ⊕ Fin 2 → Fin (D+D))
    (i : Fin D) (hi : b (.inr 0) = Fin.castAdd D i) :
    phaseCoefficientJet (angleCoefficients T M q a) .observableGradient j z b =
      (a⁻¹ * q^(j+1)) * partialAlong
        (fun k => phasePosition (coordinateDirection (D+D) k))
        (b (.inr 1) :: (List.finRange j).map (fun k => b (.inl k)))
        (fun x => inner ℝ (coordinateDirection D i) (T x-x))
        (M+q • phasePosition z) := by
  let f : E → ℝ := fun x => inner ℝ (coordinateDirection D i) (T x-x)
  have hf : ContDiff ℝ ∞ f := contDiff_const.inner ℝ (hT.sub contDiff_id)
  have hd : displacementCoordinate T M q a (b (.inr 0)) =
      fun x => a⁻¹ * f (M+q • phasePosition x) := by
    rw [hi]
    funext x
    simp only [displacementCoordinate, finSumFinEquiv_symm_apply_castAdd, basis_eq_coordinate]
    rfl
  change partialAlong (fun k : Fin j => coordinateDirection (D+D) (b (.inl k)))
    (List.finRange j) (dir (coordinateDirection (D+D) (b (.inr 1)))
      (displacementCoordinate T M q a (b (.inr 0)))) z = _
  rw [hd, PolynomialClosure.partialAlong_map_id, ordered_gradient_affine_pullback f hf]
  simp only [List.length_map, List.length_finRange]
  have hL : coordinateDirection (D+D) (b (.inr 1)) ::
      (List.finRange j).map (fun k => coordinateDirection (D+D) (b (.inl k))) =
      (b (.inr 1) :: (List.finRange j).map (fun k => b (.inl k))).map
        (coordinateDirection (D+D)) := by simp only [List.map_cons, List.map_map, Function.comp_def]
  rw [hL, partialAlong_map_index]

/-- Every entry with all slots in the physical block is the expected ordered jet. -/
theorem angleGradientJet_at_image (T : E → E) (hT : ContDiff ℝ ∞ T)
    (M : E) (q a : ℝ) (j : ℕ) (z : EP) (v : Fin j ⊕ Fin 2 → Fin D) :
    phaseCoefficientJet (angleCoefficients T M q a) .observableGradient j z
      (fun s => Fin.castAdd D (v s)) =
      (a⁻¹ * q^(j+1)) * physicalDisplacementJet T j (M+q • phasePosition z) v := by
  erw [gradient_entry_pullback T hT M q a j z (fun s => Fin.castAdd D (v s)) (v (.inr 0)) rfl]
  change _ = _ * partialAlong _ _ _ _
  have hL : Fin.castAdd D (v (.inr 1)) ::
      (List.finRange j).map (fun k => Fin.castAdd D (v (.inl k))) =
      (v (.inr 1) :: (List.finRange j).map (fun k => v (.inl k))).map
        (Fin.castAdd D) := by simp only [List.map_cons, List.map_map, Function.comp_def]
  rw [hL, partialAlong_map_index]
  simp only [phasePosition_coordinate_castAdd]

private theorem partialAlong_zero_function {I V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (d : I → V) (L : List I) :
    partialAlong d L (fun _ => (0 : ℝ)) = fun _ => 0 := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    rw [partialAlong, ih]
    funext x
    simp [dir]

/-- A momentum-block slot, including the output slot, forces the literal entry to zero. -/
theorem angleGradientJet_momentum_entry (T : E → E) (hT : ContDiff ℝ ∞ T)
    (M : E) (q a : ℝ) (j : ℕ) (z : EP) (b : Fin j ⊕ Fin 2 → Fin (D+D))
    (s : Fin j ⊕ Fin 2) (k : Fin D) (hk : b s = Fin.natAdd D k) :
    phaseCoefficientJet (angleCoefficients T M q a) .observableGradient j z b = 0 := by
  cases ho : finSumFinEquiv.symm (b (.inr 0)) with
  | inl i =>
    have hi : b (.inr 0) = Fin.castAdd D i := by
      have hh := congrArg finSumFinEquiv ho
      simpa using hh
    rw [gradient_entry_pullback T hT M q a j z b i hi]
    have hz : ∃ r ∈ b (.inr 1) :: (List.finRange j).map (fun u => b (.inl u)),
        phasePosition (coordinateDirection (D+D) r) = 0 := by
      cases s with
      | inl u =>
          refine ⟨b (.inl u), List.mem_cons_of_mem _ (List.mem_map.mpr ⟨u, by simp, rfl⟩), ?_⟩
          rw [hk, phasePosition_coordinate_natAdd]
      | inr u =>
          fin_cases u
          · change b (.inr 0) = Fin.natAdd D k at hk
            have hh := hi.symm.trans hk
            have hv := congrArg Fin.val hh
            simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
            omega
          · change b (.inr 1) = Fin.natAdd D k at hk
            exact ⟨b (.inr 1), by simp, by rw [hk, phasePosition_coordinate_natAdd]⟩
    rw [partialAlong_zero_direction _ _ _ hz]
    simp
  | inr i =>
    have hi : b (.inr 0) = Fin.natAdd D i := by
      have hh := congrArg finSumFinEquiv ho
      simpa using hh
    have hd : displacementCoordinate T M q a (b (.inr 0)) = fun _ => 0 := by
      rw [hi]
      funext x
      simp only [displacementCoordinate, finSumFinEquiv_symm_apply_natAdd]
    change partialAlong _ _ (dir _ (displacementCoordinate T M q a (b (.inr 0)))) z = 0
    rw [hd]
    have hd0 (w : EP) : dir w (fun _ : EP => (0 : ℝ)) = fun _ => 0 := by
      funext x
      simp [dir]
    rw [hd0, partialAlong_zero_function]

/-- Exact tensor identity. Neither q nor a needs to be nonzero. -/
theorem angleGradientJet_coordinatePad (T : E → E) (hT : ContDiff ℝ ∞ T)
    (M : E) (q a : ℝ) (j : ℕ) (z : EP) :
    phaseCoefficientJet (angleCoefficients T M q a) .observableGradient j z =
      (a⁻¹ * q^(j+1)) • coordinatePadCoeff (fun _ => Fin.castAddEmb D)
        (physicalDisplacementJet T j (M+q • phasePosition z)) := by
  classical
  apply (WithLp.equiv 2 _).injective
  funext b
  by_cases hb : b ∈ Set.range (assignmentEmbedding (fun _ : Fin j ⊕ Fin 2 => Fin.castAddEmb D))
  · obtain ⟨v, rfl⟩ := hb
    change _ = (a⁻¹ * q^(j+1)) * coordinatePadCoeff _ _ (fun s => Fin.castAdd D (v s))
    erw [coordinatePadCoeff_at_image]
    exact angleGradientJet_at_image T hT M q a j z v
  · have hs : ∃ s k, b s = Fin.natAdd D k := by
      by_contra hn
      push Not at hn
      have he (s : Fin j ⊕ Fin 2) : ∃ i : Fin D, b s = Fin.castAdd D i := by
        cases hi : finSumFinEquiv.symm (b s) with
        | inl i => exact ⟨i, by simpa using congrArg finSumFinEquiv hi⟩
        | inr i => exact False.elim (hn s i (by simpa using congrArg finSumFinEquiv hi))
      choose v hv using he
      apply hb
      exact ⟨v, funext (fun s => (hv s).symm)⟩
    obtain ⟨s,k,hk⟩ := hs
    change _ = (a⁻¹ * q^(j+1)) * coordinatePadCoeff _ _ b
    rw [coordinatePadCoeff_off_image _ _ b hb, mul_zero]
    exact angleGradientJet_momentum_entry T hT M q a j z b s k hk

/-- Constant-one embedding loss for every rectangular split, including empty splits. -/
theorem splitNorm_angleGradientJet_le (T : E → E) (hT : ContDiff ℝ ∞ T)
    (M : E) (q a : ℝ) (j : ℕ) (z : EP) (S : Finset (Fin j ⊕ Fin 2)) :
    splitNorm (D+D) S (phaseCoefficientJet (angleCoefficients T M q a) .observableGradient j z) ≤
      |a⁻¹ * q^(j+1)| * splitNorm D S (physicalDisplacementJet T j (M+q • phasePosition z)) := by
  rw [angleGradientJet_coordinatePad T hT, splitNorm_smul]
  exact mul_le_mul_of_nonneg_left (splitNorm_coordinatePadCoeff_le _ _ _) (abs_nonneg _)

end AcceleratedLogConcave.Analysis.AnglePhase
