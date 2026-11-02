import AcceleratedLogConcave.Conditional.Flow.ActualJacobianWords

/-! The manuscript's exact C-jet formula, with actual material derivatives
of the division-free first scaled jet. Source warm-start.tex 1987--1993.
No higher derivatives of the original potential are assumed. -/
noncomputable section
open Set
open scoped ContDiff Topology
set_option autoImplicit false
namespace AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
open Analysis.PositiveVarianceSlab Analysis.CoupledVelocityPolynomial Analysis.ODEJet
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (d : PositiveVarianceFlowData E)

def firstJetField (p : CoupledSpaceTime E) : E →L[ℝ] E :=
  firstScaledJet d.F d.x d.r p.1 p.2.1

def materialFirstJet (k : ℕ) (t : ℝ) (y : E) : E →L[ℝ] E :=
  observableJet (openDomain (CoupledState E))
    (conditionalCoupledVelocity d.F d.x d.r) d.firstJetField k (t, d.state t y)

theorem materialFirstJet_zero (t : ℝ) (y : E) :
    d.materialFirstJet 0 t y = firstScaledJet d.F d.x d.r t (d.state t y).fst := rfl

theorem contDiffOn_firstJetField :
    ContDiffOn ℝ ∞ d.firstJetField (openDomain (CoupledState E)) :=
  (contDiffOn_firstScaledJet_natural d.hF d.hlo d.hhi d.x d.r).comp_continuousLinearMap
    (timeSpaceProjection E)

theorem hasDerivAt_materialFirstJet (k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) (y : E) :
    HasDerivAt (fun u => d.materialFirstJet k u y) (d.materialFirstJet (k+1) t y) t :=
  hasDerivAt_observableJet_along (isOpen_openDomain (CoupledState E))
    (contDiffOn_conditionalCoupledVelocity d.hF d.hlo d.hhi d.x d.r)
    d.contDiffOn_firstJetField (construction_subset d.hb0 d.hb1 ⟨ht.1.le, ht.2.le⟩)
    (d.hasDerivAt_state ht y) k

/-- The coefficient k vanishes at k=0, so no negative jet order is used. -/
def coefficientMaterialJet (k : ℕ) (t : ℝ) (y : E) : E →L[ℝ] E :=
  d.r • (t • d.materialFirstJet k t y + (k : ℝ) • d.materialFirstJet (k-1) t y)

theorem coefficientMaterialJet_zero (t : ℝ) (y : E) :
    d.coefficientMaterialJet 0 t y = d.jacobianCoefficientJet 0 t y := by
  simp only [coefficientMaterialJet, Nat.cast_zero, zero_smul, add_zero,
    materialFirstJet_zero, smul_smul, jacobianCoefficientJet_zero]

theorem hasDerivAt_coefficientMaterialJet (k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) (y : E) :
    HasDerivAt (fun u => d.coefficientMaterialJet k u y)
      (d.coefficientMaterialJet (k+1) t y) t := by
  cases k with
  | zero =>
    have hh := (((hasDerivAt_id t).smul (d.hasDerivAt_materialFirstJet 0 ht y)).const_smul d.r)
    convert hh using 1
    · funext u
      simp only [coefficientMaterialJet, Nat.cast_zero, zero_smul, add_zero]
      rfl
    · simp [coefficientMaterialJet]
  | succ k =>
    have hh := (((hasDerivAt_id t).smul (d.hasDerivAt_materialFirstJet (k+1) ht y)).add
      ((d.hasDerivAt_materialFirstJet k ht y).const_smul (k+1 : ℝ))).const_smul d.r
    convert hh using 1
    · funext u
      simp only [coefficientMaterialJet, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
        Pi.add_apply, Pi.smul_apply]
      rfl
    · simp only [coefficientMaterialJet, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, id_eq,
        one_smul, add_smul]
      congr 1
      abel

/-- Exact source formula C^(k)=r[t D^k U1 + k D^(k-1) U1], with y fixed. -/
theorem jacobianCoefficientJet_eq_material (k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) (y : E) :
    d.jacobianCoefficientJet k t y =
      d.r • (t • d.materialFirstJet k t y + (k : ℝ) • d.materialFirstJet (k-1) t y) := by
  have hh := Analysis.iteratedDeriv_eq_of_finite_ladder k
    (fun q u => d.coefficientMaterialJet q u y) isOpen_Ioo
    (fun q _ _u hu => d.hasDerivAt_coefficientMaterialJet q hu y) ht
  have he : (fun u => d.coefficientMaterialJet 0 u y) =
      (fun u => d.jacobianCoefficientJet 0 u y) := funext (fun u => d.coefficientMaterialJet_zero u y)
  rw [he, d.iteratedDeriv_jacobianCoefficient k ht y] at hh
  exact hh

end AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
