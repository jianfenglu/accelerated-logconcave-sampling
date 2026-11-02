import AcceleratedLogConcave.Root.OuterRootLiteralScore
import AcceleratedLogConcave.Root.OuterRootMainQuadrature
import AcceleratedLogConcave.Root.OuterRootSeedDefectLp

/-! Actual main-row residual on the original common seed, with a proved L2
payment from original curvature and the prescribed partial quadrature row. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Root.OuterRootMainResidual
open OuterRootFlowIdentification OuterRootStrongJetLp
variable {ι : Type*} [Fintype ι]
  {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
  {m h : ℝ} (hm : 0<m) (hh : 0<h)
  (hlo : ∀ z v,m*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (K : ℕ) (clock : ClockLaw.Clock) (i : ClockCollocation.MainIndex h K)
local notation "F" => family hV hm hh hlo hup
local notation "data" => OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup
local notation "c" => (Real.sqrt h)⁻¹
local notation "u" => ClockCollocation.u h K clock i
local notation "a" => ClockCollocation.rF h*u
local notation "W" => ClockCollocation.W h hh K clock (ClockCollocation.v h K i)
local notation "E" => EuclideanSpace ℝ ι

/-- The common-seed main-center defect, using the prescribed source labels. -/
def residual (p : E × E) : E :=
  a • (seedJet data c 0 0 p +
    ∑ j : ClockCollocation.MainIndex h K,W j • seedJet data c 1 (ClockCollocation.u h K clock j) p -
    seedJet data c 0 u p)

theorem residual_memLp : MemLp (residual hV hm hh hlo hup K clock i) 2 (seedMeasure F) := by
  have hs := memLp_finsetSum' Finset.univ (fun j : ClockCollocation.MainIndex h K => fun _ =>
    (seedJet_memLp F data c 1 (ClockCollocation.u h K clock j)).const_smul (W j))
  convert (((seedJet_memLp F data c 0 0).add hs).sub (seedJet_memLp F data c 0 u)).const_smul a using 1
  funext p
  simp only [residual,Pi.smul_apply,Pi.add_apply,Pi.sub_apply,Finset.sum_apply]

private theorem finite_toLp {Ω X I : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup X] [Fintype I] (μ : Measure Ω)
    (f : I → Ω → X) (hf : ∀ i,MemLp (f i) 2 μ) :
    (memLp_finsetSum' Finset.univ (fun i _ => hf i)).toLp (∑ i,f i)=∑ i,(hf i).toLp (f i) := by
  classical
  have H (s : Finset I) : (memLp_finsetSum' s (fun i _ => hf i)).toLp (∑ i∈s,f i)=∑ i∈s,(hf i).toLp (f i) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact MemLp.toLp_zero _
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      change ((hf i).add (memLp_finsetSum' s (fun j _ => hf j))).toLp (f i+∑ j∈s,f j)=_
      rw [MemLp.toLp_add (hf i) (memLp_finsetSum' s (fun j _ => hf j)),ih]
  exact H Finset.univ

theorem residual_toLp :
    (residual_memLp hV hm hh hlo hup K clock i).toLp (residual hV hm hh hlo hup K clock i)=
      -a • ((jetLp F data c 0 u-jetLp F data c 0 0)-
        ∑ j : ClockCollocation.MainIndex h K,W j • jetLp F data c 1 (ClockCollocation.u h K clock j)) := by
  have hrow (j : ClockCollocation.MainIndex h K) :=
    (seedJet_memLp F data c 1 (ClockCollocation.u h K clock j)).const_smul (W j)
  have hsum := memLp_finsetSum' Finset.univ (fun j _ => hrow j)
  have hfun : residual hV hm hh hlo hup K clock i =
      a • (seedJet data c 0 0 + ∑ j : ClockCollocation.MainIndex h K,
        W j • seedJet data c 1 (ClockCollocation.u h K clock j) - seedJet data c 0 u) := by
    funext p; simp only [residual,Pi.smul_apply,Pi.add_apply,Pi.sub_apply,Finset.sum_apply]
  simp only [hfun]
  rw [MemLp.toLp_const_smul a (((seedJet_memLp F data c 0 0).add hsum).sub (seedJet_memLp F data c 0 u)),
    MemLp.toLp_sub ((seedJet_memLp F data c 0 0).add hsum) (seedJet_memLp F data c 0 u),
    MemLp.toLp_add (seedJet_memLp F data c 0 0) hsum,finite_toLp _ _ hrow]
  change a • (jetLp F data c 0 0+∑ j,W j • jetLp F data c 1 (ClockCollocation.u h K clock j)-jetLp F data c 0 u)=_
  simp only [smul_sub,neg_smul,smul_add]
  abel

/-- Literal zero-order jet equals the original Gaussian-start path. -/
theorem seedJet_zero_eq_rawY (p : E × E) {t : ℝ} (ht : t∈Set.Icc (0:ℝ) (1/2)) :
    seedJet data c 0 t p = OuterRootPhysicalPath.rawY hV hh (lower_nonneg hm hlo) hup (c • p.1) p.2 t := by
  change (Numerics.ConditionalSmoothing.jet data 0 t (c • p.1,p.2)).2=_
  rw [Numerics.ConditionalSmoothing.jet_zero,
    Numerics.ConditionalSmoothing.jointPath_snd_eq_source _ _ _ ht]
  exact OuterRootLiteralScore.path_eq_rawY hV hh (lower_nonneg hm hlo) hup _ _ ht

/-- The defect is exactly b+A times the prescribed primitive means minus the
actual conditional-flow centers, on the same source seed. -/
theorem residual_eq_graph (p : E × E) :
    residual hV hm hh hlo hup K clock i p =
      (ClockCollocation.graph h hh K clock (c • p.1) p.2).updateFromReplies
        (fun j => OuterRootLiteralScore.score hV hh (lower_nonneg hm hlo) hup (c • p.1) p.2
          (ClockCollocation.u h K clock j)) i -
      ((c • p.1)+a • OuterRootPhysicalPath.rawY hV hh (lower_nonneg hm hlo) hup
        (c • p.1) p.2 u) := by
  have hu : u∈Set.Icc (0:ℝ) (1/2) :=
    ⟨(ClockCollocation.u_mem hh K clock i).1,(ClockCollocation.u_mem hh K clock i).2.trans clock.2.2⟩
  have hj (j : ClockCollocation.MainIndex h K) :
      seedJet data c 1 (ClockCollocation.u h K clock j) p =
        (-ClockCollocation.rF h) • OuterRootLiteralScore.score hV hh (lower_nonneg hm hlo) hup
          (c • p.1) p.2 (ClockCollocation.u h K clock j) := by
    exact OuterRootLiteralScore.jet_one_eq_score hV hh (lower_nonneg hm hlo) hup _ _
      ⟨(ClockCollocation.u_mem hh K clock j).1,(ClockCollocation.u_mem hh K clock j).2.trans clock.2.2⟩
  have hzero : OuterRootPhysicalPath.rawY hV hh (lower_nonneg hm hlo) hup (c • p.1) p.2 0=p.2 := by
    unfold OuterRootPhysicalPath.rawY
    exact Conditional.convexProbabilityFlow_initial _ _ _ _ _ _ _ _ _ _ _
  rw [residual,seedJet_zero_eq_rawY hV hm hh hlo hup p (by norm_num),
    seedJet_zero_eq_rawY hV hm hh hlo hup p hu,hzero,ClockCollocation.updateFromReplies_eq]
  simp_rw [hj,smul_smul]
  have hrow : (∑ j : ClockCollocation.MainIndex h K,
      (W j*(-ClockCollocation.rF h)) • OuterRootLiteralScore.score hV hh (lower_nonneg hm hlo) hup
        (c • p.1) p.2 (ClockCollocation.u h K clock j)) =
      -(ClockCollocation.rF h) • ∑ j : ClockCollocation.MainIndex h K,
        W j • OuterRootLiteralScore.score hV hh (lower_nonneg hm hlo) hup
          (c • p.1) p.2 (ClockCollocation.u h K clock j) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul,mul_comm]
  rw [hrow,neg_smul]
  module

/-- Every partial main-center residual is square-integrable with its explicit
order, dimension and precision bound. -/
theorem residual_energy (hsmall : h≤1/2) :
    Integrable (fun p => ‖residual hV hm hh hlo hup K clock i p‖^2) (seedMeasure F) ∧
    (∫ p,‖residual hV hm hh hlo hup K clock i p‖^2 ∂seedMeasure F)≤
      ((ClockCollocation.rF h/2)*ClockQuadraturePower.orderConstant K*
        Real.sqrt (Fintype.card ι:ℝ)*h^(K+6))^2 := by
  refine ⟨(residual_memLp hV hm hh hlo hup K clock i).norm.integrable_sq,?_⟩
  rw [← Analysis.DominatedLp.norm_sq_toLp (residual_memLp hV hm hh hlo hup K clock i),residual_toLp]
  rw [neg_smul,norm_neg]
  have H := OuterRootMainQuadrature.source_main_center_defect hV hm hh hlo hup hsmall K clock i
  exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans H)).mpr H

end AcceleratedLogConcave.Root.OuterRootMainResidual
