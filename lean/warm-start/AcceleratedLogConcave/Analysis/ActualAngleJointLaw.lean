import AcceleratedLogConcave.Analysis.ActualAngleJointCoordinates

/-! New exact joint pushforward for the actual same-seed angle coordinates. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option maxHeartbeats 1000000
namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open Conditional Analysis.AnglePhase CenterMeanSecondJetSource AffineGraph
variable {D m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

def angleMidpointLaw (d : Data (Fin D) m) (k : d.G.Kernel) : Measure E :=
  ((baseLaw d.F d.x d.r).prod (stdGaussian E)).map (angleIndependentMidpoint d k)

theorem continuous_angleIndependentMidpoint (d : Data (Fin D) m) (k : d.G.Kernel) :
    Continuous (angleIndependentMidpoint d k) := by unfold angleIndependentMidpoint; fun_prop

instance angleMidpointLaw_probability (d : Data (Fin D) m) (k : d.G.Kernel) :
    IsProbabilityMeasure (angleMidpointLaw d k) := by
  have := baseLaw_isProbabilityMeasure d.hF d.hlo d.x d.r
  unfold angleMidpointLaw
  infer_instance

theorem lintegral_angleSeedCoordinates (d : Data (Fin D) m) (j : Fin m) (k : d.G.Kernel)
    (f : E × EP → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ w, f (angleSeedCoordinates d j k w) ∂seedMeasure d) =
      ∫⁻ p, f p ∂(angleMidpointLaw d k).prod (stdGaussian EP) := by
  have := baseLaw_isProbabilityMeasure d.hF d.hlo d.x d.r
  have h := lintegral_actual_observation_independent d j k
    (f ∘ angleObservationCoordinates d k)
    (hf.comp (continuous_angleObservationCoordinates d k).measurable)
  change (∫⁻ w, f (angleSeedCoordinates d j k w) ∂seedMeasure d) = _ at h
  simp only [Function.comp_def,angleObservationCoordinates_independent] at h
  rw [h]
  let H : E → E → E → E → ℝ≥0∞ := fun u c a s =>
    f (angleIndependentMidpoint d k (u,c),phaseMeasurableEquiv.symm (a,s))
  have hH : Measurable (fun p : ((E × E) × E) × E => H p.1.1.1 p.1.1.2 p.1.2 p.2) := by
    dsimp [H]
    exact hf.comp (((continuous_angleIndependentMidpoint d k).measurable.comp
      (measurable_fst.fst.fst.prodMk measurable_fst.fst.snd)).prodMk
      (phaseMeasurableEquiv.symm.measurable.comp (measurable_fst.snd.prodMk measurable_snd)))
  have hs : (∫⁻ s, ∫⁻ u, ∫⁻ a, ∫⁻ c, H u c a s
      ∂stdGaussian E ∂stdGaussian E ∂baseLaw d.F d.x d.r ∂stdGaussian E) =
      ∫⁻ u, ∫⁻ c, ∫⁻ a, ∫⁻ s, H u c a s
      ∂stdGaussian E ∂stdGaussian E ∂stdGaussian E ∂baseLaw d.F d.x d.r := by
    rw [lintegral_lintegral_swap (show AEMeasurable
      (fun p : E × E => ∫⁻ a, ∫⁻ c, H p.2 c a p.1 ∂stdGaussian E ∂stdGaussian E) _ from by
        apply Measurable.aemeasurable
        have h0 : Measurable (fun p : ((E × E) × E) × E => H p.1.1.2 p.2 p.1.2 p.1.1.1) :=
          hH.comp (show Measurable (fun p : ((E × E) × E) × E =>
            (((p.1.1.2,p.2),p.1.2),p.1.1.1)) by fun_prop)
        have h1 : Measurable (fun p : (E × E) × E => ∫⁻ c, H p.1.2 c p.2 p.1.1 ∂stdGaussian E) :=
          Measurable.lintegral_prod_right (f := fun (p : (E × E) × E) c => H p.1.2 c p.2 p.1.1) h0
        exact Measurable.lintegral_prod_right (f := fun (p : E × E) a => ∫⁻ c, H p.2 c a p.1 ∂stdGaussian E) h1)]
    apply lintegral_congr
    intro u
    have hac (s : E) : (∫⁻ a, ∫⁻ c, H u c a s ∂stdGaussian E ∂stdGaussian E) =
        ∫⁻ c, ∫⁻ a, H u c a s ∂stdGaussian E ∂stdGaussian E :=
      lintegral_lintegral_swap (hH.comp (show Measurable (fun p : E × E =>
        (((u,p.2),p.1),s)) by fun_prop)).aemeasurable
    simp_rw [hac]
    rw [lintegral_lintegral_swap (show AEMeasurable
      (fun p : E × E => ∫⁻ a, H u p.2 a p.1 ∂stdGaussian E) _ from by
        have h0 : Measurable (fun p : (E × E) × E => H u p.1.2 p.2 p.1.1) :=
          hH.comp (show Measurable (fun p : (E × E) × E => (((u,p.1.2),p.2),p.1.1)) by fun_prop)
        exact (Measurable.lintegral_prod_right (f := fun (p : E × E) a => H u p.2 a p.1) h0).aemeasurable)]
    apply lintegral_congr
    intro c
    exact lintegral_lintegral_swap (hH.comp (show Measurable (fun p : E × E =>
      (((u,c),p.2),p.1)) by fun_prop)).aemeasurable
  change (∫⁻ s, ∫⁻ u, ∫⁻ a, ∫⁻ c, H u c a s
    ∂stdGaussian E ∂stdGaussian E ∂baseLaw d.F d.x d.r ∂stdGaussian E) = _
  rw [hs,lintegral_prod _ hf.aemeasurable]
  have hfm : Measurable (fun x : E => ∫⁻ y : EP, f (x,y) ∂stdGaussian EP) :=
    Measurable.lintegral_prod_right (f := fun x y => f (x,y)) hf
  rw [angleMidpointLaw,lintegral_map hfm
    (continuous_angleIndependentMidpoint d k).measurable]
  rw [lintegral_prod (fun p : E × E => ∫⁻ y : EP, f (angleIndependentMidpoint d k p,y) ∂stdGaussian EP)
    (hfm.comp (continuous_angleIndependentMidpoint d k).measurable).aemeasurable]
  apply lintegral_congr
  intro u
  apply lintegral_congr
  intro c
  have hm : Measurable (fun z : EP => f (angleIndependentMidpoint d k (u,c),z)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  have he := ((phaseMeasurableEquiv_preserving (D := D)).symm phaseMeasurableEquiv).lintegral_comp hm
  rw [lintegral_prod (fun p : E × E => f (angleIndependentMidpoint d k (u,c),phaseMeasurableEquiv.symm p))
    (hm.comp phaseMeasurableEquiv.symm.measurable).aemeasurable] at he
  exact he

theorem angleSeedCoordinates_preserving (d : Data (Fin D) m) (j : Fin m) (k : d.G.Kernel) :
    MeasurePreserving (angleSeedCoordinates d j k) (seedMeasure d)
      ((angleMidpointLaw d k).prod (stdGaussian EP)) := by
  refine ⟨measurable_angleSeedCoordinates d j k, ?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_angleSeedCoordinates d j k)]
  exact lintegral_angleSeedCoordinates d j k f hf
end AcceleratedLogConcave.Numerics.MeanFlowLp
