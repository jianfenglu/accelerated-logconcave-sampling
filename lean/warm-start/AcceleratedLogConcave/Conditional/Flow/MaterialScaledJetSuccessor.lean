import AcceleratedLogConcave.Tensor.ActualCoefficientSplitBounds
import AcceleratedLogConcave.Conditional.Flow.MaterialCommutator

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
open Analysis Analysis.CoupledVelocityPolynomial Analysis.PositiveVarianceSlab
variable {D : ℕ} (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))

def scaledJetCoordinate (q : ℕ) (w : EuclideanSpace ℝ (Fin D))
    (a : Fin q → EuclideanSpace ℝ (Fin D))
    (p : ℝ × EuclideanSpace ℝ (Fin D)) : ℝ :=
  inner ℝ w (scaledJet q d.F d.x d.r p.1 p.2 a)

theorem contDiffOn_scaledJetCoordinate (q : ℕ) (w : EuclideanSpace ℝ (Fin D))
    (a : Fin q → EuclideanSpace ℝ (Fin D)) :
    ContDiffOn ℝ ∞ (d.scaledJetCoordinate q w a) (openDomain (EuclideanSpace ℝ (Fin D))) :=
  (innerSL ℝ w).contDiff.comp_contDiffOn
    ((ScaledJetPolynomial.tensorEvaluation q a).contDiff.comp_contDiffOn
      (contDiffOn_scaledJet q d.hF d.hlo d.hhi d.x d.r))

/-- Actual scalar spatial transition in space-time form; it does not divide by rho. -/
theorem directional_scaledJetCoordinate (q : ℕ) (w v : EuclideanSpace ℝ (Fin D))
    (a : Fin q → EuclideanSpace ℝ (Fin D)) {t : ℝ}
    (ht : -1 < t ∧ t < 1) (y : EuclideanSpace ℝ (Fin D)) :
    directionalDerivative (0,v) (d.scaledJetCoordinate q w a) (t,y) =
      t * d.scaledJetCoordinate (q+1) w (Fin.cons v a) (t,y) := by
  have hf := ((d.contDiffOn_scaledJetCoordinate q w a).contDiffAt
    ((isOpen_openDomain _).mem_nhds (show (t,y) ∈ openDomain _ from ht))).differentiableAt (by simp)
  have hh := hf.hasFDerivAt.comp y ((hasFDerivAt_const t y).prodMk (hasFDerivAt_id y))
  have he := congrArg (fun L : EuclideanSpace ℝ (Fin D) →L[ℝ] ℝ => L v) hh.fderiv
  change fderiv ℝ (fun z => inner ℝ w (scaledJet q d.F d.x d.r t z a)) y v =
    directionalDerivative (0,v) (d.scaledJetCoordinate q w a) (t,y) at he
  rw [←he,fderiv_scaledJet_coordinate q d.hF d.hlo d.hhi d.x d.r ht.1 ht.2]
  rfl

/-- Nonsingular all-q material/spatial successor identity. This is the
cancellation step needed by the full material leaf induction, not a
replacement for that induction. It is valid at rho=0 as stated. -/
theorem material_scaledJet_successor (q : ℕ) (w v : EuclideanSpace ℝ (Fin D))
    (a : Fin q → EuclideanSpace ℝ (Fin D)) {t : ℝ}
    (ht : -1 < t ∧ t < 1) (y : EuclideanSpace ℝ (Fin D)) :
    t * materialDerivative d.materialVelocity
        (d.scaledJetCoordinate (q+1) w (Fin.cons v a)) (t,y) =
      directionalDerivative (0,v)
        (materialDerivative d.materialVelocity (d.scaledJetCoordinate q w a)) (t,y) -
      d.scaledJetCoordinate (q+1) w (Fin.cons v a) (t,y) +
      (d.r*t^2) * d.scaledJetCoordinate (q+1) w
        (Fin.cons (firstScaledJet d.F d.x d.r t y v) a) (t,y) := by
  let G := d.scaledJetCoordinate (q+1) w (Fin.cons v a)
  have hp : (t,y) ∈ openDomain (EuclideanSpace ℝ (Fin D)) := ht
  have hg := ((d.contDiffOn_scaledJetCoordinate (q+1) w (Fin.cons v a)).contDiffAt
    ((isOpen_openDomain _).mem_nhds hp)).differentiableAt (by simp)
  have he : directionalDerivative (0,v) (d.scaledJetCoordinate q w a) =ᶠ[nhds (t,y)]
      (fun p => p.1 * G p) := by
    filter_upwards [(isOpen_openDomain _).mem_nhds hp] with p hp'
    exact d.directional_scaledJetCoordinate q w v a hp' p.2
  have hprod := ((hasFDerivAt_fst (𝕜 := ℝ) (p := (t,y))).mul hg.hasFDerivAt).fderiv
  change fderiv ℝ (fun p => p.1 * G p) (t,y) = _ at hprod
  have hleft : materialDerivative d.materialVelocity
      (directionalDerivative (0,v) (d.scaledJetCoordinate q w a)) (t,y) =
      G (t,y) + t * materialDerivative d.materialVelocity G (t,y) := by
    unfold materialDerivative
    rw [he.fderiv_eq]
    rw [hprod]
    simp [materialVelocity,G,add_comm]
  have hh := d.material_spatial_commutator (d.contDiffOn_scaledJetCoordinate q w a) ht y v
  rw [hleft,d.directional_scaledJetCoordinate q w
    (firstScaledJet d.F d.x d.r t y v) a ht y] at hh
  simp only [smul_eq_mul] at hh
  dsimp only [G] at hh
  nlinarith

end AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
