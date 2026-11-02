/- NEW source-only reconstruction: retains tensor transfer only, NOT the conditional receiver. -/
import AcceleratedLogConcave.Numerics.CenterMeanPhysicalTransportJet

/-! Dimension-free physical-K-to-phase transfer. The factor two is explicit;
no physical K analytic estimate is proved or hidden in a structure field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor Tensor.Ordered.Graph
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

/-- Pure tensor algebra, independent of the physical Data and K definitions. -/
theorem transportTwoPad_split_bound (j : ℕ) (S : Finset (Fin j ⊕ Fin 2))
    (T : Coeff (Fin j ⊕ Fin 2) D) :
    splitNorm (D+D) S
      (coordinatePadCoeff (transportUpperEmbedding j) T +
        coordinatePadCoeff (transportLowerEmbedding j)
          ((-1 : ℝ) • WithLp.toLp 2 (fun v => T (v ∘ centerGradientSlotSwap j)))) ≤
      splitNorm D S T + splitNorm D (S.map (centerGradientSlotSwap j).symm.toEmbedding) T := by
  have htrans := splitNorm_slotEquiv_le D (centerGradientSlotSwap j).symm S T
  simp only [Equiv.symm_symm] at htrans
  have hpad := splitNorm_coordinatePadCoeff_add_le
    (transportUpperEmbedding (D := D) j) (transportLowerEmbedding (D := D) j) S T
    ((-1 : ℝ) • WithLp.toLp 2 (fun v => T (v ∘ centerGradientSlotSwap j)))
  rw [splitNorm_smul] at hpad
  norm_num only [abs_neg, abs_one, one_mul] at hpad
  linarith only [hpad, htrans]

/-- Every rectangular split transfers, with only the terminal-slot transpose
changing its physical split. This also applies to empty/full splits and D=0. -/
theorem phaseTransportJet_split_bound (d : Data (Fin D)) (L a : ℝ)
    (j : ℕ) (z : EP) (S : Finset (Fin j ⊕ Fin 2)) :
    splitNorm (D+D) S (phaseCoefficientJet (phaseCoefficients d L a) .transport j z) ≤
      |L⁻¹| * (splitNorm D S (physicalTransportJet d j (phasePosition z)) +
        splitNorm D (S.map (centerGradientSlotSwap j).symm.toEmbedding)
          (physicalTransportJet d j (phasePosition z))) := by
  rw [phaseTransportJet_eq_two_pads d L a j z, splitNorm_smul]
  exact mul_le_mul_of_nonneg_left
    (transportTwoPad_split_bound j S (physicalTransportJet d j (phasePosition z)))
    (abs_nonneg (L⁻¹))

/-- Two mixed blocks cost at most two, with no coordinate sum or dimension loss. -/
theorem phaseTransportJet_split_two (d : Data (Fin D)) (L a B : ℝ)
    (j : ℕ) (z : EP) (S : Finset (Fin j ⊕ Fin 2)) (hS : NontrivialSplit S)
    (hK : ∀ T : Finset (Fin j ⊕ Fin 2), NontrivialSplit T →
      |L⁻¹| * splitNorm D T (physicalTransportJet d j (phasePosition z)) ≤ B) :
    splitNorm (D+D) S (phaseCoefficientJet (phaseCoefficients d L a) .transport j z) ≤
      2 * B := by
  apply (phaseTransportJet_split_bound d L a j z S).trans
  calc
    _ = |L⁻¹| * splitNorm D S (physicalTransportJet d j (phasePosition z)) +
        |L⁻¹| * splitNorm D (S.map (centerGradientSlotSwap j).symm.toEmbedding)
          (physicalTransportJet d j (phasePosition z)) := by ring
    _ ≤ B + B := add_le_add (hK S hS)
      (hK _ (nontrivialSplit_map_equiv _ hS))
    _ = 2 * B := by ring

/-- The exact target phase budget follows from a physical tensor budget with
half the target allowance. The hypothesis is on literal K derivatives in D,
not on the phase coefficient, its skew block, or a finished source expression. -/
theorem phaseTransportJet_budget_of_physical (d : Data (Fin D)) (L a c R : ℝ)
    (hL : 0 < L)
    (hK : ∀ j (y : E) (S : Finset (Fin j ⊕ Fin 2)), NontrivialSplit S →
      splitNorm D S (physicalTransportJet d j y) ≤
        L * (c^(2+j) * ((2+j).factorial : ℝ) * R^(-(j:ℝ))) / 2)
    (j : ℕ) (z : EP) (S : Finset (Fin j ⊕ Fin 2)) (hS : NontrivialSplit S) :
    splitNorm (D+D) S (phaseCoefficientJet (phaseCoefficients d L a) .transport j z) ≤
      c^(2+j) * ((2+j).factorial : ℝ) * R^(-(j:ℝ)) := by
  have hnorm (T : Finset (Fin j ⊕ Fin 2)) (hT : NontrivialSplit T) :
      |L⁻¹| * splitNorm D T (physicalTransportJet d j (phasePosition z)) ≤
        (c^(2+j) * ((2+j).factorial : ℝ) * R^(-(j:ℝ))) / 2 := by
    calc
      _ ≤ |L⁻¹| * (L * (c^(2+j) * ((2+j).factorial : ℝ) * R^(-(j:ℝ))) / 2) :=
        mul_le_mul_of_nonneg_left (hK j (phasePosition z) T hT) (abs_nonneg _)
      _ = _ := by rw [abs_of_pos (inv_pos.mpr hL)]; field_simp [ne_of_gt hL]
  have h := phaseTransportJet_split_two d L a
    ((c^(2+j) * ((2+j).factorial : ℝ) * R^(-(j:ℝ))) / 2) j z S hS hnorm
  convert h using 1; ring

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
