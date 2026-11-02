import AcceleratedLogConcave.Numerics.CenterMeanPhaseScorePadding
import AcceleratedLogConcave.Numerics.CenterMeanPhysicalObservableGradient

/-! NEW reconstruction; SOURCE ONLY. Exact all-slot position padding of actual
vector gradients. Hypotheses below are coordinate identities, not bounds. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor Tensor.AdjointReduction Tensor.CoordinateReduction
open Tensor.Ordered.Graph Tensor.ActualCoefficientIntegrability
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

/-- Canonical row/output 0, input 1, with n untouched derivative slots. -/
def physicalVectorGradientJet (f : Fin D → E → ℝ) (n : ℕ) (y : E) :
    Coeff (Fin n ⊕ Fin 2) D := WithLp.toLp 2 (fun a =>
  partialAlong (fun i : Fin n => coordinateDirection D (a (.inl i))) (List.finRange n)
    (dir (coordinateDirection D (a (.inr 1))) (f (a (.inr 0)))) y)

def vectorGradientJet (V : EP → EP) (n : ℕ) (z : EP) :
    Coeff (Fin n ⊕ Fin 2) (D+D) := WithLp.toLp 2 (fun a =>
  partialAlong (fun i : Fin n => coordinateDirection (D+D) (a (.inl i))) (List.finRange n)
    (dir (coordinateDirection (D+D) (a (.inr 1))) (fun w => V w (a (.inr 0)))) z)

private theorem partialAlong_position_map {I : Type*} (v : I → EP) (J : List I)
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (z : EP) :
    partialAlong v J (f ∘ phasePositionCLM) z =
      partialAlong (fun i => phasePosition (v i)) J f (phasePosition z) := by
  rw [PolynomialClosure.partialAlong_map_id,
    PolynomialClosure.partialAlong_comp_linear hf]
  conv_rhs => rw [PolynomialClosure.partialAlong_map_id]
  simp only [List.map_map, Function.comp_def]
  rfl

private theorem partialAlong_zero' {I V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (v : I → V) (J : List I) :
    partialAlong v J (fun _ => (0 : ℝ)) = fun _ => 0 := by
  induction J with
  | nil => rfl
  | cons i J ih => rw [partialAlong, ih]; funext x; simp [dir]

private theorem dir_zero' (f : E → ℝ) : dir (0 : E) f = fun _ => 0 := by
  funext y
  simp [dir]

private theorem castAdd_ne_natAdd' (i k : Fin D) :
    Fin.castAdd D i ≠ Fin.natAdd D k := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

/-- A general padded vector field: all n derivative slots and both terminal
slots must be physical position coordinates. Empty dimensions need no case. -/
theorem vectorGradientJet_eq_pad (V : EP → EP) (f : Fin D → E → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hpos : ∀ i, (fun z => V z (Fin.castAdd D i)) = f i ∘ phasePositionCLM)
    (hmom : ∀ i, (fun z => V z (Fin.natAdd D i)) = fun _ => 0)
    (n : ℕ) (z : EP) :
    vectorGradientJet V n z =
      coordinatePadCoeff (fun _ : Fin n ⊕ Fin 2 => Fin.castAddEmb D)
        (physicalVectorGradientJet f n (phasePosition z)) := by
  classical
  ext a
  have pad_zero (s : Fin n ⊕ Fin 2) (k : Fin D)
      (hs : a s = Fin.natAdd D k) :
      coordinatePadCoeff (fun _ : Fin n ⊕ Fin 2 => Fin.castAddEmb D)
        (physicalVectorGradientJet f n (phasePosition z)) a = 0 := by
    apply coordinatePadCoeff_off_image
    rintro ⟨b, hb⟩
    exact castAdd_ne_natAdd' (b s) k ((congrFun hb s).trans hs)
  cases ho : finSumFinEquiv.symm (a (.inr 0)) with
  | inr o =>
    have ho' : a (.inr 0) = Fin.natAdd D o := by simpa using congrArg finSumFinEquiv ho
    rw [pad_zero _ _ ho']
    change partialAlong _ _ (dir _ (fun w => V w (a (.inr 0)))) z = 0
    rw [ho', hmom]
    have hc : dir (coordinateDirection (D+D) (a (.inr 1))) (fun _ : EP => (0:ℝ)) =
        fun _ => 0 := by funext w; simp [dir]
    rw [hc, partialAlong_zero']
  | inl o =>
    have ho' : a (.inr 0) = Fin.castAdd D o := by simpa using congrArg finSumFinEquiv ho
    have hv : vectorGradientJet V n z a =
        partialAlong (fun i : Fin n => phasePosition (coordinateDirection (D+D) (a (.inl i))))
          (List.finRange n)
          (dir (phasePosition (coordinateDirection (D+D) (a (.inr 1)))) (f o))
          (phasePosition z) := by
      change partialAlong _ _ (dir _ (fun w => V w (a (.inr 0)))) z = _
      rw [ho', hpos, PolynomialClosure.dir_comp_linear (hf o)]
      exact partialAlong_position_map _ _ _ (contDiff_dir (hf o) _) z
    rw [hv]
    by_cases ha : ∀ s : Fin n ⊕ Fin 2, ∃ k : Fin D, a s = Fin.castAdd D k
    · choose b hb using ha
      have hab : a = fun s => Fin.castAdd D (b s) := funext hb
      have hob : b (.inr 0) = o := (Fin.castAdd_injective D D)
        ((hb (.inr 0)).symm.trans ho')
      rw [hab]
      have hp := coordinatePadCoeff_at_image
        (fun _ : Fin n ⊕ Fin 2 => (Fin.castAddEmb D : Fin D ↪ Fin (D+D)))
        (physicalVectorGradientJet f n (phasePosition z)) b
      change coordinatePadCoeff _ _ (fun s => Fin.castAdd D (b s)) = _ at hp
      rw [hp]
      simp only [phasePosition_coordinate_castAdd]
      simp only [physicalVectorGradientJet, hob]
    · push Not at ha
      obtain ⟨s, hs⟩ := ha
      have hm : ∃ k : Fin D, a s = Fin.natAdd D k := by
        cases he : finSumFinEquiv.symm (a s) with
        | inl k => exact False.elim (hs k (by simpa using congrArg finSumFinEquiv he))
        | inr k => exact ⟨k, by simpa using congrArg finSumFinEquiv he⟩
      obtain ⟨k, hk⟩ := hm
      rw [pad_zero _ _ hk]
      cases s with
      | inl i =>
        rw [partialAlong_zero_direction _ _ _
          ⟨i, by simp, by rw [hk, phasePosition_coordinate_natAdd]⟩]
      | inr i =>
        fin_cases i
        · exact False.elim (hs o ho')
        · change a (.inr 1) = Fin.natAdd D k at hk
          rw [hk, phasePosition_coordinate_natAdd, dir_zero', partialAlong_zero']

theorem phaseEmbedPosition_coordinate_castAdd (y : E) (i : Fin D) :
    phaseEmbedPosition y (Fin.castAdd D i) = y i := by
  have h := congrArg (fun w : WithLp 2 (E × E) => w.ofLp.1 i)
    (phaseCoordinateEquiv.apply_symm_apply (WithLp.toLp 2 (y, (0:E))))
  exact h

theorem phaseEmbedPosition_coordinate_natAdd (y : E) (i : Fin D) :
    phaseEmbedPosition y (Fin.natAdd D i) = 0 := by
  have h := congrArg (fun w : WithLp 2 (E × E) => w.ofLp.2 i)
    (phaseCoordinateEquiv.apply_symm_apply (WithLp.toLp 2 (y, (0:E))))
  exact h

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
