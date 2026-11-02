import AcceleratedLogConcave.Conditional.LiftedLaplaceCoordinates
import AcceleratedLogConcave.Tensor.SplitNormRestriction

noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace Topology
namespace AcceleratedLogConcave.Conditional

/-- Canonical Euclidean basis of the two-block lift, with a single Fin index. -/
def liftedCoordinateBasis (D : ℕ) :
    OrthonormalBasis (Fin (D+D)) ℝ (EuclideanSpace ℝ (Fin D ⊕ Fin D)) :=
  (EuclideanSpace.basisFun (Fin D ⊕ Fin D) ℝ).reindex finSumFinEquiv

theorem liftedCoordinateBasis_inl {D : ℕ} (i : Fin D) :
    liftedCoordinateBasis D (finSumFinEquiv (Sum.inl i)) =
      positionLiftCLM (EuclideanSpace.basisFun (Fin D) ℝ i) := by
  unfold liftedCoordinateBasis
  rw [OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply]
  ext j
  cases j <;> simp [EuclideanSpace.basisFun_apply]

theorem liftedCoordinateBasis_inr {D : ℕ} (i : Fin D) :
    liftedCoordinateBasis D (finSumFinEquiv (Sum.inr i)) =
      observableLiftCLM (EuclideanSpace.basisFun (Fin D) ℝ i) := by
  unfold liftedCoordinateBasis
  rw [OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply]
  ext j
  cases j <;> simp [EuclideanSpace.basisFun_apply]

theorem logJet_eq_cumulantTensor {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] (hμ : HasLocalMGF μ)
    {Slot : Type} [Fintype Slot] [DecidableEq Slot] {N : ℕ}
    (b : OrthonormalBasis (Fin N) ℝ E) (a : Slot → Fin N)
    (l : List Slot) (hl : l.Nodup) (hall : l.toFinset = Finset.univ) :
    JetCalculus.jet (fun i => b (a i)) l
      (fun θ => Real.log (Appell.laplace μ (fun _ => (1 : ℝ)) θ)) 0 =
      cumulantTensor μ b a := by
  obtain ⟨M,he⟩ := hμ.exists_momentModel
  have hlog := he.mono fun θ hθ => congrArg Real.log hθ
  have hp : l.Perm (Finset.univ.toList : List Slot) :=
    List.perm_of_nodup_nodup_toFinset_eq hl (Finset.nodup_toList _) (by simpa using hall)
  change _ = JetCalculus.jet (fun i => b (a i)) (Finset.univ.toList : List Slot) _ 0
  rw [(JetCalculus.jet_eventuallyEq _ l hlog).eq_of_nhds,
    (JetCalculus.jet_eventuallyEq _ (Finset.univ.toList : List Slot) hlog).eq_of_nhds,
    JetCalculus.jet_perm (M.smooth.log (fun θ => (M.positive θ).ne')) _ hp]

/-- Embedding of the q position slots and one output slot in the lifted law. -/
def jetSlotEmbedding {q D : ℕ} : (Fin q ⊕ Unit) → Fin D → Fin (D+D) :=
  Sum.elim (fun _ i => finSumFinEquiv (Sum.inl i))
    (fun _ i => finSumFinEquiv (Sum.inr i))

theorem jetSlotEmbedding_injective {q D : ℕ} (s : Fin q ⊕ Unit) :
    Function.Injective (jetSlotEmbedding (D := D) s) := by
  cases s
  · exact finSumFinEquiv.injective.comp Sum.inl_injective
  · exact finSumFinEquiv.injective.comp Sum.inr_injective

/-- Actual all-slots Hilbert coefficient tensor of Uq, including its output. -/
def scaledJetCoefficient {D : ℕ} (q : ℕ) (F : EuclideanSpace ℝ (Fin D) → ℝ)
    (x : EuclideanSpace ℝ (Fin D)) (r t : ℝ) (y : EuclideanSpace ℝ (Fin D)) :
    Tensor.Coeff (Fin q ⊕ Unit) D :=
  WithLp.toLp 2 (fun a => inner ℝ (EuclideanSpace.basisFun (Fin D) ℝ (a (Sum.inr ())))
    (scaledJet q F x r t y (fun i => EuclideanSpace.basisFun (Fin D) ℝ (a (Sum.inl i)))))

namespace PositiveVarianceFlowData
variable {D : ℕ} (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))

theorem scaledJetCoefficient_eq_restricted_cumulant (hell : 0 < d.ell)
    (q : ℕ) {t : ℝ} (ht : -1 < t ∧ t < 1) (y : EuclideanSpace ℝ (Fin D)) :
    scaledJetCoefficient q d.F d.x d.r t y =
      ((conditionalVariance t ^ q)⁻¹ * (d.r*d.ell)) •
      WithLp.toLp 2 (fun a => cumulantTensor (d.liftedConditionalLaw t y)
        (liftedCoordinateBasis D) (fun s => jetSlotEmbedding s (a s))) := by
  let : IsProbabilityMeasure (d.liftedConditionalLaw t y) :=
    conditionalLift_isProbabilityMeasure d.hF d.hlo d.x y d.r d.ell ht.1 ht.2
  have hμ : HasLocalMGF (d.liftedConditionalLaw t y) :=
    conditionalLift_hasLocalMGF d.hF hell d.hr d.hlo d.hhi d.x y ht.1 ht.2
  ext a
  have hh := d.scaledJet_coordinate_eq_lifted_logJet hell ht y
    (EuclideanSpace.basisFun (Fin D) ℝ (a (Sum.inr ())))
    (fun i : Fin q => EuclideanSpace.basisFun (Fin D) ℝ (a (Sum.inl i)))
    (List.finRange q)
  have hl : ((List.finRange q).map (Sum.inl : Fin q → Fin q ⊕ Unit) ++ [Sum.inr ()]).Nodup := by
    rw [List.nodup_append]
    refine ⟨(List.nodup_finRange q).map Sum.inl_injective, by simp, ?_⟩
    simp
  have hall : ((List.finRange q).map (Sum.inl : Fin q → Fin q ⊕ Unit) ++ [Sum.inr ()]).toFinset = Finset.univ := by
    ext s
    cases s <;> simp
  have hc := logJet_eq_cumulantTensor hμ (liftedCoordinateBasis D)
    (fun s => jetSlotEmbedding s (a s)) _ hl hall
  have hv : (fun s => liftedCoordinateBasis D (jetSlotEmbedding s (a s))) =
      Sum.elim (fun i : Fin q => positionLiftCLM (EuclideanSpace.basisFun (Fin D) ℝ (a (Sum.inl i))))
        (fun _ : Unit => observableLiftCLM (EuclideanSpace.basisFun (Fin D) ℝ (a (Sum.inr ())))) := by
    funext s
    cases s with
    | inl i => exact liftedCoordinateBasis_inl _
    | inr u => cases u; exact liftedCoordinateBasis_inr _
  rw [hv] at hc
  rw [hc] at hh
  convert! hh using 1 <;> simp [scaledJetCoefficient]
  congr 1
  have cast_eval (n m : ℕ) (h : n = m) (v : Fin m → EuclideanSpace ℝ (Fin D)) :
      scaledJet n d.F d.x d.r t y (fun i => v (Fin.cast h i)) =
        scaledJet m d.F d.x d.r t y v := by subst m; rfl
  exact (cast_eval _ _ (List.length_finRange (n := q)) _).symm

/-- Original-data dimension-free all-split bound on the actual Uq tensor.
The exact square-root constant is retained, stronger than the manuscript's
coarser power-of-two bound; probability time zero is included. -/
theorem scaledJetCoefficient_splitNorm_le_of_pos (hell : 0 < d.ell)
    (q : ℕ) {t : ℝ} (ht : -1 < t ∧ t < 1) (y : EuclideanSpace ℝ (Fin D))
    (S : Finset (Fin q ⊕ Unit)) (hS : Tensor.NontrivialSplit S) :
    Tensor.splitNorm D S (scaledJetCoefficient q d.F d.x d.r t y) ≤
      ((conditionalVariance t ^ q)⁻¹ * (d.r*d.ell)) *
        ((q.factorial : ℝ) * (Real.sqrt (2*conditionalVariance t))^(q+1)) := by
  rw [d.scaledJetCoefficient_eq_restricted_cumulant hell q ht y, Tensor.splitNorm_smul]
  have hp : 0 ≤ (conditionalVariance t ^ q)⁻¹ * (d.r*d.ell) :=
    mul_nonneg (inv_nonneg.mpr (pow_nonneg (conditionalVariance_pos ht.1 ht.2).le q))
      (mul_pos d.hr hell).le
  rw [abs_of_nonneg hp]
  apply mul_le_mul_of_nonneg_left _ hp
  apply (Tensor.splitNorm_coordinateRestriction_le jetSlotEmbedding
    jetSlotEmbedding_injective S _).trans
  simpa only [liftedConditionalLaw, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit, Nat.add_sub_cancel] using
    conditionalLift_cumulantTensor_splitNorm_le d.hF hell d.hr d.hlo d.hhi d.x y
      ht.1 ht.2 (liftedCoordinateBasis D) S hS

/-- The sharp actual split bound with only the original nonnegative curvature
assumption. Inflating the Hessian upper bound and taking an elementary order
limit includes ell=0 without dividing by it. -/
theorem scaledJetCoefficient_splitNorm_le
    (q : ℕ) {t : ℝ} (ht : -1 < t ∧ t < 1) (y : EuclideanSpace ℝ (Fin D))
    (S : Finset (Fin q ⊕ Unit)) (hS : Tensor.NontrivialSplit S) :
    Tensor.splitNorm D S (scaledJetCoefficient q d.F d.x d.r t y) ≤
      ((conditionalVariance t ^ q)⁻¹ * (d.r*d.ell)) *
        ((q.factorial : ℝ) * (Real.sqrt (2*conditionalVariance t))^(q+1)) := by
  let K := (conditionalVariance t ^ q)⁻¹ * d.r *
    ((q.factorial : ℝ) * (Real.sqrt (2*conditionalVariance t))^(q+1))
  have hv : 0 < conditionalVariance t := conditionalVariance_pos ht.1 ht.2
  have hr := d.hr
  have hf : 0 < (q.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos q)
  have hs : 0 < Real.sqrt (2*conditionalVariance t) := Real.sqrt_pos.mpr (mul_pos (by norm_num) hv)
  have hK : 0 < K := by dsimp [K]; positivity
  apply le_of_forall_pos_le_add
  intro ε hε
  let d' : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)) :=
    { d with ell := d.ell + ε/K
             hell := add_nonneg d.hell (div_pos hε hK).le
             hhi := fun z w => (d.hhi z w).trans
               (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (div_pos hε hK).le) (sq_nonneg _)) }
  have hp : 0 < d'.ell := add_pos_of_nonneg_of_pos d.hell (div_pos hε hK)
  have hh := d'.scaledJetCoefficient_splitNorm_le_of_pos hp q ht y S hS
  change Tensor.splitNorm D S (scaledJetCoefficient q d.F d.x d.r t y) ≤
    ((conditionalVariance t ^ q)⁻¹ * (d.r*(d.ell+ε/K))) *
      ((q.factorial : ℝ) * (Real.sqrt (2*conditionalVariance t))^(q+1)) at hh
  have hc : ε/K*K = ε := div_mul_cancel₀ ε hK.ne'
  dsimp [K] at hc
  nlinarith [hh]

end PositiveVarianceFlowData
end AcceleratedLogConcave.Conditional
