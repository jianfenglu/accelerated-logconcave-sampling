import AcceleratedLogConcave.Numerics.CenterMeanPhasePrimitiveSupport
import AcceleratedLogConcave.Numerics.CenterMeanPhysicalPrimitiveBudgets
import AcceleratedLogConcave.Analysis.GaussianPhaseJets
import AcceleratedLogConcave.Tensor.PhasePolynomialPullback

/-! NEW reconstruction; SOURCE ONLY. Exact score-jet zero-padding for coordinate
projections. No bound is hypothesized. Includes zero derivative order and D=0;
the quantitative score application below will use only positive orders. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor Tensor.AdjointReduction Tensor.CoordinateReduction
open Tensor.Ordered.Graph Tensor.ActualCoefficientIntegrability
variable {D N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EN" => EuclideanSpace ℝ (Fin N)

private theorem partialAlong_projection {I : Type*} (v : I → EN) (J : List I)
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (L : EN →L[ℝ] E) (z : EN) :
    partialAlong v J (f ∘ L) z =
      partialAlong (fun i => L (v i)) J f (L z) := by
  rw [PolynomialClosure.partialAlong_map_id,
    PolynomialClosure.partialAlong_comp_linear hf]
  conv_rhs => rw [PolynomialClosure.partialAlong_map_id]
  simp only [List.map_map, Function.comp_def]

private theorem partialAlong_zero_function {I V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (v : I → V) (J : List I) :
    partialAlong v J (fun _ => (0 : ℝ)) = fun _ => 0 := by
  induction J with
  | nil => rfl
  | cons i J ih => rw [partialAlong, ih]; funext x; simp [dir]

/-- A coordinate projection sends selected coordinates to the matching physical
basis and all other coordinates to zero. This yields literal zero padding in
EVERY derivative and terminal score slot, not just an operator norm estimate. -/
theorem phaseScoreJet_projection_eq_pad
    (H : E → ℝ) (hH : ContDiff ℝ ∞ H) (L : EN →L[ℝ] E)
    (e : Fin D ↪ Fin N)
    (he : ∀ k, L (coordinateDirection N (e k)) = coordinateDirection D k)
    (hz : ∀ k, k ∉ Set.range e → L (coordinateDirection N k) = 0)
    (j : ℕ) (z : EN) :
    phaseScoreJet (H ∘ L) j z =
      coordinatePadCoeff (fun _ : Fin j ⊕ Unit => e) (phaseScoreJet H j (L z)) := by
  classical
  ext a
  have hv : phaseScoreJet (H ∘ L) j z a =
      partialAlong (fun i : Fin j => L (coordinateDirection N (a (.inl i))))
        (List.finRange j) (dir (L (coordinateDirection N (a (.inr ())))) H) (L z) := by
    change partialAlong _ _ (dir _ (H ∘ L)) z = _
    rw [PolynomialClosure.dir_comp_linear hH]
    exact partialAlong_projection _ _ _
      (contDiff_dir hH _) L z
  rw [hv]
  by_cases ha : ∀ s : Fin j ⊕ Unit, ∃ k : Fin D, a s = e k
  · choose b hb using ha
    have hab : a = fun s => e (b s) := funext hb
    rw [hab, coordinatePadCoeff_at_image]
    simp only [he]
    rfl
  · push Not at ha
    obtain ⟨s, hs⟩ := ha
    have hsrange : a s ∉ Set.range e := by
      rintro ⟨k, hk⟩
      exact hs k hk.symm
    have hpad : coordinatePadCoeff (fun _ : Fin j ⊕ Unit => e)
        (phaseScoreJet H j (L z)) a = 0 := by
      apply coordinatePadCoeff_off_image
      rintro ⟨b, hb⟩
      exact hs (b s) (congrFun hb s).symm
    rw [hpad]
    cases s with
    | inl i =>
      rw [partialAlong_zero_direction _ _ _
        ⟨i, by simp, hz _ hsrange⟩]
    | inr u =>
      cases u
      rw [hz _ hsrange]
      have hzero : dir (0 : E) H = fun _ => 0 := by
        funext y
        simp [dir]
      rw [hzero, partialAlong_zero_function]

private theorem coordinate_not_castAdd (k : Fin (D+D))
    (hk : k ∉ Set.range (Fin.castAddEmb D : Fin D ↪ Fin (D+D))) :
    ∃ i : Fin D, k = Fin.natAdd D i := by
  cases h : finSumFinEquiv.symm k with
  | inl i =>
    exact False.elim (hk ⟨i, by simpa using (congrArg finSumFinEquiv h).symm⟩)
  | inr i => exact ⟨i, by simpa using congrArg finSumFinEquiv h⟩

/-- Literal spatial projection of any smooth physical potential. -/
theorem phaseScoreJet_position_eq_pad (H : E → ℝ) (hH : ContDiff ℝ ∞ H)
    (j : ℕ) (z : EuclideanSpace ℝ (Fin (D+D))) :
    phaseScoreJet (H ∘ phasePositionCLM) j z =
      coordinatePadCoeff (fun _ : Fin j ⊕ Unit => Fin.castAddEmb D)
        (phaseScoreJet H j (phasePosition z)) := by
  apply phaseScoreJet_projection_eq_pad H hH phasePositionCLM (Fin.castAddEmb D)
    phasePosition_coordinate_castAdd
  intro k hk
  obtain ⟨i, rfl⟩ := coordinate_not_castAdd k hk
  exact phasePosition_coordinate_natAdd i

theorem phaseMomentum_coordinate_castAdd (i : Fin D) :
    phaseMomentum (coordinateDirection (D+D) (Fin.castAdd D i)) = 0 := by
  have hb (N : ℕ) (k : Fin N) : coordinateDirection N k =
      EuclideanSpace.basisFun (Fin N) ℝ k := by
    simp [EuclideanSpace.basisFun_apply, coordinateDirection, EuclideanSpace.single]
  simp only [hb]
  exact phaseMomentum_position_basis i

theorem phaseMomentum_coordinate_natAdd (i : Fin D) :
    phaseMomentum (coordinateDirection (D+D) (Fin.natAdd D i)) =
      coordinateDirection D i := by
  have hb (N : ℕ) (k : Fin N) : coordinateDirection N k =
      EuclideanSpace.basisFun (Fin N) ℝ k := by
    simp [EuclideanSpace.basisFun_apply, coordinateDirection, EuclideanSpace.single]
  simp only [hb]
  exact phaseMomentum_momentum_basis i

/-- Literal momentum projection; every slot is in the momentum block. -/
theorem phaseScoreJet_momentum_eq_pad (H : E → ℝ) (hH : ContDiff ℝ ∞ H)
    (j : ℕ) (z : EuclideanSpace ℝ (Fin (D+D))) :
    phaseScoreJet (H ∘ phaseMomentumCLM) j z =
      coordinatePadCoeff (fun _ : Fin j ⊕ Unit => Fin.natAddEmb D)
        (phaseScoreJet H j (phaseMomentum z)) := by
  apply phaseScoreJet_projection_eq_pad H hH phaseMomentumCLM (Fin.natAddEmb D)
    phaseMomentum_coordinate_natAdd
  intro k hk
  cases h : finSumFinEquiv.symm k with
  | inl i =>
    have he : k = Fin.castAdd D i := by simpa using congrArg finSumFinEquiv h
    rw [he]
    exact phaseMomentum_coordinate_castAdd i
  | inr i =>
    exact False.elim (hk ⟨i, by simpa using (congrArg finSumFinEquiv h).symm⟩)

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
