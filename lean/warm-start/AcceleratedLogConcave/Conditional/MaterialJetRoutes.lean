import AcceleratedLogConcave.Conditional.ScaledJetAdjointSuccessor

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff RealInnerProductSpace BigOperators
namespace AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
open Tensor Tensor.AdjointReduction
variable {D : ℕ} (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))

/-- List labels are actual directions; repeated directions retain multiplicity. -/
def scaledJetList (w : EuclideanSpace ℝ (Fin D)) (l : List (EuclideanSpace ℝ (Fin D)))
    (p : ℝ × EuclideanSpace ℝ (Fin D)) : ℝ :=
  d.scaledJetCoordinate l.length w (fun i => l.get i) p

theorem scaledJetList_cons (w v : EuclideanSpace ℝ (Fin D))
    (l : List (EuclideanSpace ℝ (Fin D))) (p : ℝ × EuclideanSpace ℝ (Fin D)) :
    d.scaledJetList w (v::l) p =
      d.scaledJetCoordinate (l.length+1) w (Fin.cons v (fun i => l.get i)) p := by
  unfold scaledJetList
  congr 1
  funext i
  refine Fin.cases ?_ (fun k => ?_) i <;> rfl

theorem contDiff_scaledJetList (w : EuclideanSpace ℝ (Fin D))
    (l : List (EuclideanSpace ℝ (Fin D))) {t : ℝ} (ht : -1 < t ∧ t < 1) :
    ContDiff ℝ ∞ (fun z => d.scaledJetList w l (t,z)) :=
  (innerSL ℝ w).contDiff.comp
    ((ScaledJetPolynomial.tensorEvaluation l.length (fun i => l.get i)).contDiff.comp
      (contDiff_scaledJet_spatial l.length d.hF d.hlo d.hhi d.x d.r ht.1 ht.2))

theorem spatial_scaledJetList (w v : EuclideanSpace ℝ (Fin D))
    (l : List (EuclideanSpace ℝ (Fin D))) {t : ℝ} (ht : -1 < t ∧ t < 1)
    (y : EuclideanSpace ℝ (Fin D)) :
    dir v (fun z => d.scaledJetList w l (t,z)) y = t*d.scaledJetList w (v::l) (t,y) := by
  change fderiv ℝ (fun z => inner ℝ w (scaledJet l.length d.F d.x d.r t z (fun i => l.get i))) y v = _
  rw [fderiv_scaledJet_coordinate l.length d.hF d.hlo d.hhi d.x d.r ht.1 ht.2,d.scaledJetList_cons]
  rfl

theorem scaledJetList_swap (w u v : EuclideanSpace ℝ (Fin D))
    (l : List (EuclideanSpace ℝ (Fin D))) {t : ℝ} (ht : -1 < t ∧ t < 1)
    (y : EuclideanSpace ℝ (Fin D)) :
    d.scaledJetList w (u::v::l) (t,y) = d.scaledJetList w (v::u::l) (t,y) := by
  have he : (fun i : Fin (l.length+1) => (v::l).get i) = Fin.cons v (fun i => l.get i) := by
    funext i; refine Fin.cases ?_ (fun k => ?_) i <;> rfl
  have hf : (fun i : Fin (l.length+1) => (u::l).get i) = Fin.cons u (fun i => l.get i) := by
    funext i; refine Fin.cases ?_ (fun k => ?_) i <;> rfl
  rw [d.scaledJetList_cons,d.scaledJetList_cons]
  change d.scaledJetCoordinate (l.length+2) w (Fin.cons u (fun i : Fin (l.length+1) => (v::l).get i)) (t,y) =
    d.scaledJetCoordinate (l.length+2) w (Fin.cons v (fun i : Fin (l.length+1) => (u::l).get i)) (t,y)
  rw [he,hf]
  exact d.scaledJetCoordinate_swap_heads l.length w u v (fun i => l.get i) ht y

def materialRouteTerm (w : EuclideanSpace ℝ (Fin D))
    (A B : List (EuclideanSpace ℝ (Fin D))) (t : ℝ) (y : EuclideanSpace ℝ (Fin D)) : ℝ :=
  ∑ k : Fin D, d.scaledJetList (coordinateDirection D k) A (t,y) *
    d.scaledJetList w (coordinateDirection D k :: B) (t,y)

def materialRouteSum (w : EuclideanSpace ℝ (Fin D))
    (l : List (EuclideanSpace ℝ (Fin D))) (t : ℝ) (y : EuclideanSpace ℝ (Fin D)) : ℝ :=
  ((scoreRoutes l).map (fun p => d.materialRouteTerm w p.1 p.2 t y)).sum

theorem contDiff_materialRouteTerm (w : EuclideanSpace ℝ (Fin D))
    (A B : List (EuclideanSpace ℝ (Fin D))) {t : ℝ} (ht : -1 < t ∧ t < 1) :
    ContDiff ℝ ∞ (d.materialRouteTerm w A B t) := by
  exact ContDiff.sum (fun k _ => (d.contDiff_scaledJetList _ A ht).mul (d.contDiff_scaledJetList w _ ht))

theorem spatial_materialRouteTerm (w v : EuclideanSpace ℝ (Fin D))
    (A B : List (EuclideanSpace ℝ (Fin D))) {t : ℝ} (ht : -1 < t ∧ t < 1)
    (y : EuclideanSpace ℝ (Fin D)) :
    dir v (d.materialRouteTerm w A B t) y =
      t * (d.materialRouteTerm w (v::A) B t y + d.materialRouteTerm w A (v::B) t y) := by
  unfold materialRouteTerm
  rw [dir_sum Finset.univ v _ (fun k _ =>
    ((d.contDiff_scaledJetList _ A ht).mul (d.contDiff_scaledJetList w _ ht)).differentiable (by simp))]
  simp_rw [dir_mul v ((d.contDiff_scaledJetList _ A ht).differentiable (by simp))
    ((d.contDiff_scaledJetList w _ ht).differentiable (by simp))]
  simp_rw [d.spatial_scaledJetList _ v _ ht y,d.scaledJetList_swap w v _ B ht y]
  rw [←Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Actual labeled subset routing under one spatial derivative. Existing
scoreRoutes supplies the combinatorics; no terms or multiplicities are discarded. -/
theorem spatial_materialRouteSum (w v : EuclideanSpace ℝ (Fin D))
    (l : List (EuclideanSpace ℝ (Fin D))) {t : ℝ} (ht : -1 < t ∧ t < 1)
    (y : EuclideanSpace ℝ (Fin D)) :
    dir v (d.materialRouteSum w l t) y =
      t * (d.materialRouteSum w (v::l) t y - d.materialRouteTerm w [v] l t y) := by
  unfold materialRouteSum
  rw [dir_list_sum v (scoreRoutes l) _ (fun p _ => d.contDiff_materialRouteTerm w p.1 p.2 ht)]
  simp_rw [d.spatial_materialRouteTerm w v _ _ ht y]
  simp only [scoreRoutes,List.map_append,List.sum_append,List.map_map,Function.comp_def]
  rw [routes_eq]
  simp only [List.map_cons,List.sum_cons]
  simp only [List.sum_map_mul_left,List.sum_map_add]
  ring

/-- The singleton nonlinear route is the literal U1 insertion, not an
independent contraction hypothesis. -/
theorem materialRouteTerm_singleton (w v : EuclideanSpace ℝ (Fin D))
    (l : List (EuclideanSpace ℝ (Fin D))) {t : ℝ} (ht : -1 < t ∧ t < 1)
    (y : EuclideanSpace ℝ (Fin D)) :
    d.materialRouteTerm w [v] l t y =
      d.scaledJetList w (firstScaledJet d.F d.x d.r t y v :: l) (t,y) := by
  unfold materialRouteTerm
  have hfirst (k : Fin D) : d.scaledJetList (coordinateDirection D k) [v] (t,y) =
      inner ℝ (coordinateDirection D k) (firstScaledJet d.F d.x d.r t y v) := by
    change inner ℝ (coordinateDirection D k)
      (scaledJet 1 d.F d.x d.r t y (fun i => [v].get i)) = _
    rw [ScaledJetPolynomial.scaledJet_one_apply_eq_firstScaledJet d.hF d.hlo d.hhi d.x d.r ht.1 ht.2]
    rfl
  simp_rw [hfirst]
  simp only [scaledJetList_cons]
  let b := EuclideanSpace.basisFun (Fin D) ℝ
  let L : EuclideanSpace ℝ (Fin D) →L[ℝ] ℝ := (innerSL ℝ w).comp
    ((ScaledJetPolynomial.tensorEvaluation l.length (fun i => l.get i)).comp
      (scaledJet (l.length+1) d.F d.x d.r t y).curryLeft)
  have hh := congrArg L (b.sum_repr' (firstScaledJet d.F d.x d.r t y v))
  simpa [b,EuclideanSpace.basisFun_apply,EuclideanSpace.single,coordinateDirection,L,
    scaledJetCoordinate,ScaledJetPolynomial.tensorEvaluation,map_sum,map_smul,smul_eq_mul] using hh

end AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
