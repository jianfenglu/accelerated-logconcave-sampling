import AcceleratedLogConcave.Conditional.Flow.MaterialScore
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! Exact product rule for the positive weighted adjoint, then its actual
U1 specialization. These identities precede any integration or norm bound. -/
noncomputable section
open scoped RealInnerProductSpace ContDiff
set_option autoImplicit false
namespace AcceleratedLogConcave.Conditional
open Analysis.Poisson Kinetic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem weightedAdjoint_add {score V W : E → E} {y : E}
    (hV : DifferentiableAt ℝ V y) (hW : DifferentiableAt ℝ W y) :
    weightedAdjoint score (fun z => V z + W z) y =
      weightedAdjoint score V y + weightedAdjoint score W y := by
  unfold weightedAdjoint
  rw [fluxDivergence_add hV hW, inner_add_right]
  ring

theorem weightedAdjoint_smul {score V : E → E} {c : E → ℝ} {y : E}
    (hc : DifferentiableAt ℝ c y) (hV : DifferentiableAt ℝ V y) :
    weightedAdjoint score (fun z => c z • V z) y =
      c y * weightedAdjoint score V y - fderiv ℝ c y (V y) := by
  unfold weightedAdjoint
  rw [fluxDivergence_smul hc hV, inner_smul_right]
  ring

theorem weightedAdjoint_finsetSum {I : Type*} (s : Finset I) (score : E → E)
    (V : I → E → E) {y : E} (hV : ∀ i ∈ s, DifferentiableAt ℝ (V i) y) :
    weightedAdjoint score (fun z => ∑ i ∈ s, V i z) y =
      ∑ i ∈ s, weightedAdjoint score (V i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [weightedAdjoint, fluxDivergence]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [weightedAdjoint_add (hV i (by simp))
      (DifferentiableAt.fun_sum (fun j hj => hV j (by simp [hj]))),
      ih (fun j hj => hV j (by simp [hj]))]

end AcceleratedLogConcave.Conditional

namespace AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
open Analysis.Poisson Kinetic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The actual U1-adjoint product is a single expression; this does not
apply Holder or estimate its factors separately. -/
theorem weightedAdjoint_firstJet_apply (d : PositiveVarianceFlowData E)
    {t : ℝ} (ht : -1 < t ∧ t < 1) {V : E → E}
    (hV : Differentiable ℝ V) (y : E) :
    weightedAdjoint (fun z => z + (d.r*t) • conditionalMean d.F d.x d.r t z)
      (fun z => firstScaledJet d.F d.x d.r t z (V z)) y =
      inner ℝ (V y) (conditionalMaterialMean d.F d.x d.r t y) -
      ∑ i : Fin (Module.finrank ℝ E), inner ℝ ((stdOrthonormalBasis ℝ E) i)
        (fderiv ℝ V y (firstScaledJet d.F d.x d.r t y ((stdOrthonormalBasis ℝ E) i))) := by
  let b := stdOrthonormalBasis ℝ E
  let row (i : Fin (Module.finrank ℝ E)) := firstScaledJetRow d.F d.x (b i) d.r t
  let c (i : Fin (Module.finrank ℝ E)) (z : E) := inner ℝ (b i) (V z)
  have hr (i : Fin (Module.finrank ℝ E)) (z : E) :
      row i z = firstScaledJet d.F d.x d.r t z (b i) := by
    change (firstScaledJet d.F d.x d.r t z).adjoint (b i) = _
    rw [
      (firstScaledJet_symmetric d.hF d.hlo d.hhi d.x d.hr.ne' ht.1 ht.2 z).clm_adjoint_eq]
  have he : (fun z => firstScaledJet d.F d.x d.r t z (V z)) =
      (fun z => ∑ i, c i z • row i z) := by
    funext z
    rw [← b.sum_repr' (V z)]
    simp only [map_sum, map_smul, c, hr]
  rw [he, weightedAdjoint_finsetSum Finset.univ _ (fun i z => c i z • row i z)]
  · have hh (i : Fin (Module.finrank ℝ E)) :
        weightedAdjoint (fun z => z + (d.r*t) • conditionalMean d.F d.x d.r t z)
          (fun z => c i z • row i z) y =
        c i y * inner ℝ (b i) (conditionalMaterialMean d.F d.x d.r t y) -
          inner ℝ (b i) (fderiv ℝ V y (firstScaledJet d.F d.x d.r t y (b i))) := by
      have hc := (innerSL ℝ (b i)).hasFDerivAt.comp y (hV y).hasFDerivAt
      have hrow := (contDiff_firstScaledJetRow d.hF d.hlo d.hhi d.x (b i) d.hr.ne' ht.1 ht.2).differentiable_one y
      change HasFDerivAt (c i) _ y at hc
      change DifferentiableAt ℝ (row i) y at hrow
      rw [weightedAdjoint_smul hc.differentiableAt hrow,
        ← conditionalMaterialMean_eq_weightedAdjoint d.hF d.hlo d.hhi d.x (b i) d.hr.ne' ht.1 ht.2 y]
      rw [hc.fderiv, hr]
      rfl
    simp_rw [hh]
    rw [Finset.sum_sub_distrib]
    congr 1
    simpa only [c, real_inner_comm (b _) (V y)] using
      b.sum_inner_mul_inner (V y) (conditionalMaterialMean d.F d.x d.r t y)
  · intro i _
    exact ((innerSL ℝ (b i)).differentiable.comp (hV)).differentiableAt.smul
      ((contDiff_firstScaledJetRow d.hF d.hlo d.hhi d.x (b i) d.hr.ne' ht.1 ht.2).differentiable_one y)

end AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
