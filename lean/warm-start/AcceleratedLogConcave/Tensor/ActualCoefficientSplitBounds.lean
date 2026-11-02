import AcceleratedLogConcave.Conditional.ScaledJetSplitNorm
import AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
import AcceleratedLogConcave.Conditional.ScaledJetSpatialTransition

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
variable {D : ℕ} (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))

/-- All ordered spatial derivatives of an actual scaled-jet coordinate,
without dividing by probability time. This is the derivative supplier for the
literal normalized coefficient environment, not an assumed coefficient bound. -/
theorem spatialJet_scaledJet_coordinate {I : Type*} {t : ℝ}
    (ht : -1 < t ∧ t < 1) (v : I → EuclideanSpace ℝ (Fin D))
    (l k : List I) (w y : EuclideanSpace ℝ (Fin D)) :
    JetCalculus.jet v l (fun z => inner ℝ w
      (scaledJet k.length d.F d.x d.r t z (fun i => v (k.get i)))) y =
    t^l.length * inner ℝ w (scaledJet (l++k).length d.F d.x d.r t y
      (fun i => v ((l++k).get i))) := by
  let N := fun c : EuclideanSpace ℝ (Fin D) => ∫ z, primitiveObservable d.F d.x d.r z
    ∂Gibbs.heatPosterior (primitivePotential d.F d.x d.r) (conditionalVariance t) c
  have hN : ContDiff ℝ ∞ N :=
    Tilt.contDiff_integral_heatPosterior (contDiff_primitivePotential d.hF d.x d.r)
      (le_refl 0) (conditionalVariance_pos ht.1 ht.2)
      (by simpa using primitivePotential_hessian_nonneg d.hF d.hlo d.x d.r)
      (continuous_primitiveObservable d.hF d.x d.r)
      (‖gradient d.F 0‖ + |d.ell| * ‖d.x‖) (|d.ell| * |d.r|) 1
      (by simpa only [pow_one] using norm_primitiveObservable_le_affine d.hF d.hlo d.hhi d.x d.r)
  let f := fun c => inner ℝ w (N c)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_const.inner ℝ hN
  have he (a : List I) (z : EuclideanSpace ℝ (Fin D)) :
      inner ℝ w (scaledJet a.length d.F d.x d.r t z (fun i => v (a.get i))) =
        JetCalculus.jet v a f (t • z) := by
    rw [JetCalculus.jet_eq_iteratedFDeriv hf]
    have hh := (innerSL ℝ w).iteratedFDeriv_comp_left (x := t • z) hN.contDiffAt
      (show (a.length : ℕ∞ω) ≤ (⊤ : ℕ∞) by simp)
    change iteratedFDeriv ℝ a.length f (t • z) = _ at hh
    rw [hh]
    rfl
  have hek : (fun z => inner ℝ w (scaledJet k.length d.F d.x d.r t z
      (fun i => v (k.get i)))) = fun z => JetCalculus.jet v k f (t • z) := funext (he k)
  rw [hek, he (l++k) y]
  have hsk := JetCalculus.smooth_jet hf v k
  have hc := JetCalculus.jet_comp_affine hsk (t • ContinuousLinearMap.id ℝ _) 0 v l
  have hce : (fun z => JetCalculus.jet v k f ((t • ContinuousLinearMap.id ℝ _) z + 0)) =
      fun z => JetCalculus.jet v k f (t • z) := by simp
  rw [hce] at hc
  rw [hc]
  simp only [smul_apply, ContinuousLinearMap.id_apply, add_zero,
    JetCalculus.jet_smul hsk, JetCalculus.jet_append]

/-- Same supplier with the literal Jq normalization. Totalized inverse keeps
this identity valid also when ell=0. -/
theorem spatialJet_normalized_scaledJet_coordinate {I : Type*} {t : ℝ}
    (ht : -1 < t ∧ t < 1) (v : I → EuclideanSpace ℝ (Fin D))
    (l k : List I) (w y : EuclideanSpace ℝ (Fin D)) :
    JetCalculus.jet v l (fun z => (d.ell*d.r*(k.length.factorial : ℝ))⁻¹ *
      inner ℝ w (scaledJet k.length d.F d.x d.r t z (fun i => v (k.get i)))) y =
    (d.ell*d.r*(k.length.factorial : ℝ))⁻¹ * t^l.length *
      inner ℝ w (scaledJet (l++k).length d.F d.x d.r t y
        (fun i => v ((l++k).get i))) := by
  have hJ := contDiff_scaledJet_spatial k.length d.hF d.hlo d.hhi d.x d.r ht.1 ht.2
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun z => inner ℝ w
      (scaledJet k.length d.F d.x d.r t z (fun i => v (k.get i)))) :=
    contDiff_const.inner ℝ ((ScaledJetPolynomial.tensorEvaluation k.length (fun i => v (k.get i))).contDiff.comp hJ)
  rw [JetCalculus.jet_const_mul hs]
  dsimp only
  rw [d.spatialJet_scaledJet_coordinate ht v l k w y]
  ring

end AcceleratedLogConcave.Conditional.PositiveVarianceFlowData

namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional

/-- Literal jth spatial derivative of the actual J_(n+1) coefficient.
Its slot order is j derivative slots, n+1 input slots, then output. -/
def normalizedJetDerivativeCoefficient {D : ℕ} (F : EuclideanSpace ℝ (Fin D) → ℝ)
    (x : EuclideanSpace ℝ (Fin D)) (ell r t : ℝ) (n j : ℕ)
    (y : EuclideanSpace ℝ (Fin D)) : Coeff ((Fin j ⊕ Fin (n+1)) ⊕ Unit) D :=
  WithLp.toLp 2 (fun a => JetCalculus.jet
    (fun i : Fin j => coordinateDirection D (a (Sum.inl (Sum.inl i))))
    (List.finRange j)
    (fun z => coefficientEnvironment F x ell r t (Sum.inl n) z
      (Fin.cons (a (Sum.inr ())) (fun i => a (Sum.inl (Sum.inr i))))) y)

variable {D : ℕ} (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))

theorem normalizedJetDerivativeCoefficient_eq_restricted_cumulant
    (hell : 0 < d.ell) (n j : ℕ) {t : ℝ} (ht : -1 < t ∧ t < 1)
    (y : EuclideanSpace ℝ (Fin D)) :
    normalizedJetDerivativeCoefficient d.F d.x d.ell d.r t n j y =
      ((d.ell*d.r*((n+1).factorial : ℝ))⁻¹ * t^j *
        (conditionalVariance t ^ (j+(n+1)))⁻¹ * (d.r*d.ell)) •
      WithLp.toLp 2 (fun a => cumulantTensor (d.liftedConditionalLaw t y)
        (liftedCoordinateBasis D)
        (fun s : (Fin j ⊕ Fin (n+1)) ⊕ Unit =>
          Sum.elim (fun _ => finSumFinEquiv (Sum.inl (a s)))
            (fun _ => finSumFinEquiv (Sum.inr (a s))) s)) := by
  let : IsProbabilityMeasure (d.liftedConditionalLaw t y) :=
    conditionalLift_isProbabilityMeasure d.hF d.hlo d.x y d.r d.ell ht.1 ht.2
  have hμ : HasLocalMGF (d.liftedConditionalLaw t y) :=
    conditionalLift_hasLocalMGF d.hF hell d.hr d.hlo d.hhi d.x y ht.1 ht.2
  ext a
  let v : Fin j ⊕ Fin (n+1) → EuclideanSpace ℝ (Fin D) :=
    fun i => coordinateDirection D (a (Sum.inl i))
  let l : List (Fin j ⊕ Fin (n+1)) := (List.finRange j).map Sum.inl
  let k : List (Fin j ⊕ Fin (n+1)) := (List.finRange (n+1)).map Sum.inr
  let w := coordinateDirection D (a (Sum.inr ()))
  have hk : k.length = n+1 := by simp [k]
  have hl : l.length = j := by simp [l]
  have hefun : (fun z => coefficientEnvironment d.F d.x d.ell d.r t (Sum.inl n) z
        (Fin.cons (a (Sum.inr ())) (fun i => a (Sum.inl (Sum.inr i))))) =
      (fun z => (d.ell*d.r*(k.length.factorial : ℝ))⁻¹ *
        inner ℝ w (scaledJet k.length d.F d.x d.r t z (fun i => v (k.get i)))) := by
    funext z
    change (d.ell*d.r*((n+1).factorial : ℝ))⁻¹ * inner ℝ w
      (scaledJet (n+1) d.F d.x d.r t z (fun i => coordinateDirection D (a (Sum.inl (Sum.inr i))))) = _
    have hea : (fun i => v (k.get i)) = fun i => coordinateDirection D (a (Sum.inl (Sum.inr (Fin.cast hk i)))) := by
      funext i
      simp [k,v,Fin.cast]
    rw [hea]
    have cast_eval (b c : ℕ) (h : b = c) (u : Fin c → EuclideanSpace ℝ (Fin D)) :
        scaledJet b d.F d.x d.r t z (fun i => u (Fin.cast h i)) =
          scaledJet c d.F d.x d.r t z u := by subst c; rfl
    rw [cast_eval _ _ hk (fun i => coordinateDirection D (a (Sum.inl (Sum.inr i)))), hk]
  have hh := d.spatialJet_normalized_scaledJet_coordinate ht v l k w y
  rw [d.scaledJet_coordinate_eq_lifted_logJet hell ht y w v (l++k)] at hh
  have hnod : ((l++k).map (Sum.inl : (Fin j ⊕ Fin (n+1)) → _ ) ++ [Sum.inr ()]).Nodup := by
    have hnk : (l++k).Nodup := by
      rw [List.nodup_append]
      refine ⟨(List.nodup_finRange j).map Sum.inl_injective,
        (List.nodup_finRange (n+1)).map Sum.inr_injective, ?_⟩
      simp [l,k]
    rw [List.nodup_append]
    refine ⟨hnk.map Sum.inl_injective, by simp, ?_⟩
    simp
  have hall : ((l++k).map (Sum.inl : (Fin j ⊕ Fin (n+1)) → _) ++ [Sum.inr ()]).toFinset = Finset.univ := by
    ext s
    cases s with
    | inl i => cases i <;> simp [l,k]
    | inr u => cases u; simp [l,k]
  let e : ((Fin j ⊕ Fin (n+1)) ⊕ Unit) → Fin D → Fin (D+D) :=
    Sum.elim (fun _ b => finSumFinEquiv (Sum.inl b)) (fun _ b => finSumFinEquiv (Sum.inr b))
  have hc := logJet_eq_cumulantTensor hμ (liftedCoordinateBasis D)
    (fun s => e s (a s)) _ hnod hall
  have hb (i : Fin D) : EuclideanSpace.basisFun (Fin D) ℝ i = coordinateDirection D i := by
    ext z
    simp [coordinateDirection, EuclideanSpace.basisFun_apply, PiLp.single_apply]
  have hdirs : (fun s => liftedCoordinateBasis D (e s (a s))) =
      Sum.elim (fun i => positionLiftCLM (v i)) (fun _ : Unit => observableLiftCLM w) := by
    funext s
    cases s with
    | inl i =>
      change liftedCoordinateBasis D (finSumFinEquiv (Sum.inl (a (Sum.inl i)))) = _
      rw [liftedCoordinateBasis_inl, hb]
      rfl
    | inr u =>
      cases u
      change liftedCoordinateBasis D (finSumFinEquiv (Sum.inr (a (Sum.inr ())))) = _
      rw [liftedCoordinateBasis_inr, hb]
      rfl
  rw [hdirs] at hc
  rw [hc] at hh
  change JetCalculus.jet _ _ _ y = _
  rw [hefun]
  have hmap : JetCalculus.jet (fun i : Fin j => coordinateDirection D (a (Sum.inl (Sum.inl i))))
      (List.finRange j) = JetCalculus.jet v l := by
    funext f
    exact (JetCalculus.jet_map v Sum.inl (List.finRange j) f).symm
  rw [hmap,hh]
  change _ = ((d.ell*d.r*((n+1).factorial : ℝ))⁻¹ * t^j *
    (conditionalVariance t ^ (j+(n+1)))⁻¹ * (d.r*d.ell)) *
    cumulantTensor (d.liftedConditionalLaw t y) (liftedCoordinateBasis D)
      (fun s => Sum.elim (fun _ => finSumFinEquiv (Sum.inl (a s)))
        (fun _ => finSumFinEquiv (Sum.inr (a s))) s)
  have hee : (fun s => Sum.elim (fun _ => finSumFinEquiv (Sum.inl (a s)))
      (fun _ => finSumFinEquiv (Sum.inr (a s))) s) = fun s => e s (a s) := by
    funext s; cases s <;> rfl
  rw [hee]
  simp only [List.length_append,hl,hk]
  ring

/-- Every spatial derivative of the literal normalized J coefficient has an
actual dimension-free split bound. The source factorial and variance powers
are retained exactly; ell=0 is included by the literal zero normalization. -/
theorem normalizedJetDerivativeCoefficient_splitNorm_le
    (n j : ℕ) {t : ℝ} (ht : -1 < t ∧ t < 1) (y : EuclideanSpace ℝ (Fin D))
    (S : Finset ((Fin j ⊕ Fin (n+1)) ⊕ Unit)) (hS : NontrivialSplit S) :
    splitNorm D S (normalizedJetDerivativeCoefficient d.F d.x d.ell d.r t n j y) ≤
      (|t|^j * ((n+1).factorial : ℝ)⁻¹ * (conditionalVariance t ^ (j+(n+1)))⁻¹) *
        (((j+(n+1)).factorial : ℝ) * (Real.sqrt (2*conditionalVariance t))^(j+(n+1)+1)) := by
  have hv := conditionalVariance_pos ht.1 ht.2
  rcases lt_or_eq_of_le d.hell with hell | hflat
  · rw [normalizedJetDerivativeCoefficient_eq_restricted_cumulant d hell n j ht y, splitNorm_smul]
    let e : ((Fin j ⊕ Fin (n+1)) ⊕ Unit) → Fin D → Fin (D+D) :=
      Sum.elim (fun _ b => finSumFinEquiv (Sum.inl b)) (fun _ b => finSumFinEquiv (Sum.inr b))
    have he : ∀ s, Function.Injective (e s) := by
      intro s; cases s
      · exact finSumFinEquiv.injective.comp Sum.inl_injective
      · exact finSumFinEquiv.injective.comp Sum.inr_injective
    have hre : (WithLp.toLp 2 (fun a : ((Fin j ⊕ Fin (n+1)) ⊕ Unit) → Fin D => cumulantTensor (d.liftedConditionalLaw t y)
        (liftedCoordinateBasis D) (fun s => Sum.elim
          (fun _ => finSumFinEquiv (Sum.inl (a s)))
          (fun _ => finSumFinEquiv (Sum.inr (a s))) s))) =
        (WithLp.toLp 2 (fun a : ((Fin j ⊕ Fin (n+1)) ⊕ Unit) → Fin D => cumulantTensor (d.liftedConditionalLaw t y)
          (liftedCoordinateBasis D) (fun s => e s (a s)))) := by
      congr 1
      funext a
      apply congrArg (fun a => cumulantTensor (d.liftedConditionalLaw t y) (liftedCoordinateBasis D) a)
      funext s; cases s <;> rfl
    rw [hre]
    have hbound := (splitNorm_coordinateRestriction_le e he S
      (cumulantTensor (d.liftedConditionalLaw t y) (liftedCoordinateBasis D))).trans
      (conditionalLift_cumulantTensor_splitNorm_le d.hF hell d.hr d.hlo d.hhi d.x y ht.1 ht.2
        (liftedCoordinateBasis D) S hS)
    have hc : |(d.ell*d.r*((n+1).factorial : ℝ))⁻¹ * t^j *
        (conditionalVariance t ^ (j+(n+1)))⁻¹ * (d.r*d.ell)| =
        |t|^j * ((n+1).factorial : ℝ)⁻¹ * (conditionalVariance t ^ (j+(n+1)))⁻¹ := by
      rw [abs_mul, abs_mul, abs_mul, abs_inv, abs_pow,
        abs_of_pos (mul_pos (mul_pos hell d.hr) (Nat.cast_pos.mpr (Nat.factorial_pos _))),
        abs_of_pos (inv_pos.mpr (pow_pos hv _)), abs_of_pos (mul_pos d.hr hell)]
      field_simp [hell.ne', d.hr.ne']
    rw [hc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [Fintype.card_sum,Fintype.card_fin,Fintype.card_unit,Nat.add_sub_cancel,
      PositiveVarianceFlowData.liftedConditionalLaw] using hbound
  · have hz : normalizedJetDerivativeCoefficient d.F d.x d.ell d.r t n j y = 0 := by
      ext a
      simp [normalizedJetDerivativeCoefficient, coefficientEnvironment, ← hflat, JetCalculus.jet_const]
    rw [hz, splitNorm_zero]
    positivity

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability

