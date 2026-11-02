import AcceleratedLogConcave.Conditional.MaterialJetRoutes
import AcceleratedLogConcave.Tensor.MaterialMeanExpression

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff RealInnerProductSpace Topology BigOperators
namespace AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
open Analysis Analysis.CoupledVelocityPolynomial Tensor Tensor.AdjointReduction Kinetic

private theorem cancel_time_at_zero {f g : ℝ → ℝ}
    (hf : ContinuousAt f 0) (hg : ContinuousAt g 0)
    (he : ∀ t ∈ Ioo (-1:ℝ) 1, t*f t=t*g t) : f 0=g 0 := by
  have : NeBot (𝓝[Ioi (0:ℝ)] 0) := nhdsWithin_Ioi_neBot (le_refl 0)
  apply tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[Ioi (0:ℝ)] 0)
    (hf.mono_left nhdsWithin_le_nhds) (hg.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds] with t ht ht1
  change 0 < t at ht
  exact mul_left_cancel₀ (ne_of_gt ht) (he t ⟨by linarith,ht1⟩)

private theorem weightedAdjoint_coordinate_sum {D : ℕ}
    (score V : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D))
    (y : EuclideanSpace ℝ (Fin D)) (hV : DifferentiableAt ℝ V y) :
    weightedAdjoint score V y = ∑ k : Fin D,
      (- fderiv ℝ (fun z => inner ℝ (coordinateDirection D k) (V z)) y
          (coordinateDirection D k) +
        inner ℝ (score y) (coordinateDirection D k) *
          inner ℝ (coordinateDirection D k) (V y)) := by
  let b := EuclideanSpace.basisFun (Fin D) ℝ
  have hb (k : Fin D) : b k = coordinateDirection D k := by
    simp [b,EuclideanSpace.basisFun_apply,coordinateDirection,EuclideanSpace.single]
  have hd (k : Fin D) : fderiv ℝ (fun z => inner ℝ (coordinateDirection D k) (V z)) y =
      (innerSL ℝ (coordinateDirection D k)).comp (fderiv ℝ V y) :=
    ((innerSL ℝ (coordinateDirection D k)).hasFDerivAt.comp y hV.hasFDerivAt).fderiv
  unfold weightedAdjoint
  rw [fluxDivergence_eq_sum_basis b hV,←b.sum_inner_mul_inner (score y) (V y)]
  simp only [hb,hd,ContinuousLinearMap.comp_apply,innerSL_apply_apply,
    Finset.sum_add_distrib,Finset.sum_neg_distrib]

variable {D : ℕ} (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))

private theorem differentiableAt_material_coordinate (q : ℕ) (w : EuclideanSpace ℝ (Fin D))
    (a : Fin q → EuclideanSpace ℝ (Fin D)) {t : ℝ}
    (ht : -1<t ∧ t<1) (y : EuclideanSpace ℝ (Fin D)) :
    DifferentiableAt ℝ
      (materialDerivative d.materialVelocity (d.scaledJetCoordinate q w a)) (t,y) := by
  have hf := (d.contDiffOn_scaledJetCoordinate q w a).contDiffAt
    ((isOpen_openDomain _).mem_nhds (show (t,y) ∈ openDomain _ from ht))
  have hv := d.contDiffOn_materialVelocity.contDiffAt
    ((isOpen_openDomain _).mem_nhds (show (t,y) ∈ openDomain _ from ht))
  exact ((hf.fderiv_right (m:=1) (by simp)).differentiableAt_one).clm_apply
    (hv.differentiableAt (by simp))

private theorem directional_material_coordinate (q : ℕ) (w v : EuclideanSpace ℝ (Fin D))
    (a : Fin q → EuclideanSpace ℝ (Fin D)) {t : ℝ}
    (ht : -1<t ∧ t<1) (y : EuclideanSpace ℝ (Fin D)) :
    directionalDerivative (0,v)
      (materialDerivative d.materialVelocity (d.scaledJetCoordinate q w a)) (t,y) =
    dir v (fun z => materialDerivative d.materialVelocity (d.scaledJetCoordinate q w a) (t,z)) y := by
  have hh := (differentiableAt_material_coordinate d q w a ht y).hasFDerivAt.comp y
    ((hasFDerivAt_const t y).prodMk (hasFDerivAt_id y))
  exact (congrArg (fun L : EuclideanSpace ℝ (Fin D) →L[ℝ] ℝ => L v) hh.fderiv).symm

private theorem material_scaledJet_nil (w : EuclideanSpace ℝ (Fin D))
    {t : ℝ} (ht : -1<t ∧ t<1) (y : EuclideanSpace ℝ (Fin D)) :
    materialDerivative d.materialVelocity (d.scaledJetList w []) (t,y) =
      d.scaledJetAdjoint 0 w (fun i => Fin.elim0 i) t y := by
  have he : d.scaledJetList w [] =
      fun p => inner ℝ w (conditionalMean d.F d.x d.r p.1 p.2) := by
    funext p
    simp [scaledJetList,scaledJetCoordinate,scaledJet,conditionalMean,conditionalLaw]
  have hM := ((contDiffOn_conditionalMean d.hF d.hlo d.hhi d.x d.r).contDiffAt
    ((isOpen_openDomain _).mem_nhds (show (t,y) ∈ openDomain _ from ht))).differentiableAt (by simp)
  rw [he]
  unfold materialDerivative
  have hf := ((innerSL ℝ w).hasFDerivAt.comp (t,y) hM.hasFDerivAt).fderiv
  change fderiv ℝ (fun p => inner ℝ w (conditionalMean d.F d.x d.r p.1 p.2)) (t,y) = _ at hf
  rw [hf]
  change inner ℝ w (conditionalMaterialMean d.F d.x d.r t y) = _
  rw [conditionalMaterialMean_eq_weightedAdjoint d.hF d.hlo d.hhi d.x w d.hr.ne' ht.1 ht.2 y,
    weightedAdjoint_coordinate_sum _ _ y
      ((contDiff_firstScaledJetRow d.hF d.hlo d.hhi d.x w d.hr.ne' ht.1 ht.2).differentiable_one y)]
  have hrow (k : Fin D) : (fun z => inner ℝ (coordinateDirection D k)
      (firstScaledJetRow d.F d.x w d.r t z)) =
      fun z => d.scaledJetCoordinate 1 w (Fin.cons (coordinateDirection D k) Fin.elim0) (t,z) := by
    funext z
    unfold firstScaledJetRow scaledJetCoordinate
    rw [real_inner_comm,ContinuousLinearMap.adjoint_inner_left,
      ScaledJetPolynomial.scaledJet_one_apply_eq_firstScaledJet d.hF d.hlo d.hhi d.x d.r ht.1 ht.2]
    rfl
  unfold scaledJetAdjoint adjointField adjointComponent dir
  apply Finset.sum_congr rfl
  intro k _
  rw [hrow,congrFun (hrow k) y]
  have hscore : fderiv ℝ (interpolationPotential d.F d.x d.r t) y (coordinateDirection D k) =
      inner ℝ (y+(d.r*t) • conditionalMean d.F d.x d.r t y) (coordinateDirection D k) := by
    rw [←inner_gradient_left,gradient_interpolationPotential d.hF d.hlo d.hhi d.x d.r ht.1 ht.2]
  rw [hscore]

/-- Away from zero only for this intermediate induction. The final theorem
extends the exact actual identity to zero by proved smoothness. -/
private theorem material_scaledJet_list_nonzero (w : EuclideanSpace ℝ (Fin D))
    (l : List (EuclideanSpace ℝ (Fin D))) {t : ℝ} (ht : -1<t ∧ t<1)
    (ht0 : t ≠ 0) (y : EuclideanSpace ℝ (Fin D)) :
    materialDerivative d.materialVelocity (d.scaledJetList w l) (t,y) =
      d.scaledJetAdjoint l.length w (fun i => l.get i) t y +
        (2*d.r*t) * d.materialRouteSum w l t y := by
  induction l generalizing y with
  | nil =>
    have he : (fun i : Fin 0 => ([] : List (EuclideanSpace ℝ (Fin D))).get i) = Fin.elim0 := by funext i; exact Fin.elim0 i
    simp only [List.length_nil,materialRouteSum,scoreRoutes,List.map_nil,List.sum_nil,mul_zero,add_zero]
    rw [he]
    exact material_scaledJet_nil d w ht y
  | cons v l ih =>
    have hs := d.material_scaledJet_successor l.length w v (fun i => l.get i) ht y
    rw [directional_material_coordinate d _ w v _ ht y] at hs
    have hi : (fun z => materialDerivative d.materialVelocity (d.scaledJetList w l) (t,z)) =
        fun z => d.scaledJetAdjoint l.length w (fun i => l.get i) t z +
          (2*d.r*t) * d.materialRouteSum w l t z := funext ih
    change t * materialDerivative d.materialVelocity
      (d.scaledJetCoordinate (l.length+1) w (Fin.cons v (fun i => l.get i))) (t,y) =
      dir v (fun z => materialDerivative d.materialVelocity (d.scaledJetList w l) (t,z)) y -
      d.scaledJetList w (v::l) (t,y) +
      (d.r*t^2) * d.scaledJetList w (firstScaledJet d.F d.x d.r t y v :: l) (t,y) at hs
    rw [hi] at hs
    have hA : ContDiff ℝ ∞ (d.scaledJetAdjoint l.length w (fun i => l.get i) t) := by
      have hrow (k : Fin D) : ContDiff ℝ ∞ (fun z =>
          d.scaledJetCoordinate (l.length+1) w (Fin.cons (coordinateDirection D k) (fun i => l.get i)) (t,z)) :=
        by simpa only [scaledJetList_cons] using
          d.contDiff_scaledJetList w (coordinateDirection D k :: l) ht
      unfold scaledJetAdjoint adjointField adjointComponent
      exact ContDiff.sum (fun k _ => (contDiff_dir (hrow k) (coordinateDirection D k)).neg.add
        ((contDiff_dir (contDiff_interpolationPotential d.hF d.hlo d.hhi d.x d.r ht.1 ht.2)
          (coordinateDirection D k)).mul (hrow k)))
    have hR : ContDiff ℝ ∞ (d.materialRouteSum w l t) :=
      contDiff_list_sum (scoreRoutes l) _ (fun p _ => d.contDiff_materialRouteTerm w p.1 p.2 ht)
    rw [dir_add v (hA.differentiable (by simp))
      ((contDiff_const.mul hR).differentiable (by simp))] at hs
    have hm : dir v (fun z => (2*d.r*t)*d.materialRouteSum w l t z) y =
        (2*d.r*t)*dir v (d.materialRouteSum w l t) y := by
      unfold dir
      rw [fderiv_const_mul (hR.differentiable (by simp) y)]
      simp
    dsimp only at hs
    rw [hm,d.spatial_scaledJetAdjoint _ w v _ ht y,
      d.spatial_materialRouteSum w v l ht y,d.materialRouteTerm_singleton w v l ht y] at hs
    have hc : d.scaledJetList w (v::l) =
        d.scaledJetCoordinate (l.length+1) w (Fin.cons v (fun i => l.get i)) :=
      funext (fun p => d.scaledJetList_cons w v l p)
    rw [hc]
    apply mul_left_cancel₀ ht0
    rw [hs]
    have ha : (fun i : Fin (v::l).length => (v::l).get i) =
        Fin.cons v (fun i => l.get i) := by
      funext i; refine Fin.cases ?_ (fun k => ?_) i <;> rfl
    simp only [List.length_cons,ha]
    rw [←d.scaledJetList_cons w v l (t,y),
      ←d.scaledJetList_cons w (firstScaledJet d.F d.x d.r t y v) l (t,y)]
    ring

private theorem continuousAt_list_sum {I : Type*} (l : List I) (F : I → ℝ → ℝ)
    (hF : ∀ a ∈ l, ContinuousAt (F a) 0) :
    ContinuousAt (fun t => (l.map (fun a => F a t)).sum) 0 := by
  induction l with
  | nil => simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => (0:ℝ)) 0)
  | cons a l ih =>
    exact (hF a (by simp)).add (ih (fun b hb => hF b (by simp [hb])))

/-- The actual nonsingular all-order material leaf identity. Every
nonempty positional subset is retained by canonical scoreRoutes, with
the source coefficient exactly 2*r*rho. No inverse time appears. -/
theorem material_scaledJet_list (w : EuclideanSpace ℝ (Fin D))
    (l : List (EuclideanSpace ℝ (Fin D))) {t : ℝ} (ht : -1<t ∧ t<1)
    (y : EuclideanSpace ℝ (Fin D)) :
    materialDerivative d.materialVelocity (d.scaledJetList w l) (t,y) =
      d.scaledJetAdjoint l.length w (fun i => l.get i) t y +
        (2*d.r*t) * d.materialRouteSum w l t y := by
  by_cases ht0 : t = 0
  · subst t
    have h0 : (-1:ℝ)<0 ∧ (0:ℝ)<1 := by constructor <;> norm_num
    have hj (q : ℕ) (w : EuclideanSpace ℝ (Fin D)) (a : Fin q → EuclideanSpace ℝ (Fin D)) :
        ContinuousAt (fun t : ℝ => d.scaledJetCoordinate q w a (t,y)) 0 :=
      ((d.contDiffOn_scaledJetCoordinate q w a).contDiffAt
        ((isOpen_openDomain _).mem_nhds (show (0,y) ∈ openDomain _ from h0))).continuousAt.comp (f := fun t : ℝ => (t,y))
          (continuous_id.prodMk continuous_const).continuousAt
    have hscore : ContinuousAt (fun t : ℝ =>
        y+(d.r*t) • conditionalMean d.F d.x d.r t y) 0 :=
      ((d.contDiffOn_scoreField).contDiffAt
        ((isOpen_openDomain _).mem_nhds (show (0,y) ∈ openDomain _ from h0))).continuousAt.comp (f := fun t : ℝ => (t,y))
          (continuous_id.prodMk continuous_const).continuousAt
    have hA : ContinuousAt (fun t : ℝ => d.scaledJetAdjoint l.length w (fun i => l.get i) t y) 0 := by
      have he : ContinuousAt (fun t : ℝ => ∑ k : Fin D,
          (-t * d.scaledJetCoordinate (l.length+2) w
            (Fin.cons (coordinateDirection D k) (Fin.cons (coordinateDirection D k) (fun i => l.get i))) (t,y) +
          inner ℝ (y+(d.r*t) • conditionalMean d.F d.x d.r t y) (coordinateDirection D k) *
            d.scaledJetCoordinate (l.length+1) w (Fin.cons (coordinateDirection D k) (fun i => l.get i)) (t,y))) 0 := by
        fun_prop
      apply he.congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds h0.1 h0.2] with t ht
      exact d.scaledJetAdjoint_eq_explicit l.length w (fun i => l.get i) ht y
    have hR : ContinuousAt (fun t : ℝ => d.materialRouteSum w l t y) 0 := by
      apply continuousAt_list_sum
      intro p _
      unfold materialRouteTerm scaledJetList
      fun_prop
    have hleft : ContinuousAt (fun t : ℝ =>
        materialDerivative d.materialVelocity (d.scaledJetList w l) (t,y)) 0 :=
      (differentiableAt_material_coordinate d l.length w (fun i => l.get i) h0 y).continuousAt.comp (f := fun t : ℝ => (t,y))
        (continuous_id.prodMk continuous_const).continuousAt
    apply cancel_time_at_zero hleft (hA.add ((continuousAt_const.mul continuousAt_id).mul hR))
    intro t ht
    by_cases ht0 : t = 0
    · simp [ht0]
    · rw [material_scaledJet_list_nonzero d w l ht ht0 y]
      rfl
  · exact material_scaledJet_list_nonzero d w l ht ht0 y

end AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
