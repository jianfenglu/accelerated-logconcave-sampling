import AcceleratedLogConcave.Conditional.PolynomialJets
import AcceleratedLogConcave.Conditional.JetBasics
import AcceleratedLogConcave.Tensor.PolynomialClosure
import AcceleratedLogConcave.Analysis.PolynomialComposition

/-! Fixed-time polynomial tails of the actual full scaled-jet family.
The zero-time branch is retained explicitly. Constants are not uniform in time. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function MeasureTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Conditional.ScaledJetPolynomial
open Appell Tensor.PolynomialClosure Tensor.AdjointReduction
section General
variable {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [NormedSpace ℝ E] [NormedSpace ℝ G] in
lemma growth_of_bound {f : E → G} {g : E → ℝ} (hg : HasGrowth g)
    (hb : ∀ x, ‖f x‖ ≤ g x) : HasGrowth f := by
  obtain ⟨C,hC,n,hn⟩ := hg
  exact ⟨C,hC,n,fun x => (hb x).trans ((le_abs_self _).trans (hn x))⟩

omit [NormedSpace ℝ G] in
lemma growth_of_envelope {f : E → G} {C : ℝ} (N : ℕ)
    (hb : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖)^N) : HasGrowth f := by
  have hid : HasGrowth (fun x : E => x) := HasGrowth.linear (ContinuousLinearMap.id ℝ E)
  exact growth_of_bound ((HasGrowth.const C).mul
    (((HasGrowth.const (1:ℝ)).add hid.norm).pow N)) hb

/-- A finite-dimensional tensor-valued field with polynomial norm jets. -/
def NormJets (f : E → G) : Prop := ∀ n : ℕ, HasGrowth (iteratedFDeriv ℝ n f)

lemma NormJets.derivative {f : E → G} (hf : NormJets f) : NormJets (fderiv ℝ f) := by
  intro n
  obtain ⟨C,hC,k,hk⟩ := hf (n+1)
  exact ⟨C,hC,k,fun x => by rw [norm_iteratedFDeriv_fderiv]; exact hk x⟩

lemma NormJets.linear {f : E → G} (hf : NormJets f) (hs : ContDiff ℝ ∞ f)
    (L : G →L[ℝ] H) : NormJets (L ∘ f) := by
  intro n
  exact growth_of_bound ((HasGrowth.const ‖L‖).mul (hf n).norm)
    (fun x => L.norm_iteratedFDeriv_comp_left hs.contDiffAt (by simp))

lemma NormJets.add {f g : E → G} (hf : NormJets f) (hg : NormJets g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g) : NormJets (fun x => f x+g x) := by
  intro n
  change HasGrowth (iteratedFDeriv ℝ n (f+g))
  rw [iteratedFDeriv_add (hfs.of_le (by simp)) (hgs.of_le (by simp))]
  exact (hf n).add (hg n)

lemma NormJets.clm (L : E →L[ℝ] G) : NormJets L := by
  intro n
  cases n with
  | zero =>
    obtain ⟨C,hC,k,hk⟩ := HasGrowth.linear L
    exact ⟨C,hC,k,fun x => by rw [norm_iteratedFDeriv_zero]; exact hk x⟩
  | succ n =>
    have he : fderiv ℝ L = fun _ => L := funext fun x => L.fderiv
    apply growth_of_bound (HasGrowth.const ‖L‖)
    intro x
    rw [← norm_iteratedFDeriv_fderiv, he]
    cases n with
    | zero => rw [norm_iteratedFDeriv_zero]
    | succ n => rw [iteratedFDeriv_succ_const]; simp

lemma NormJets.iterated {f : E → G} (hf : NormJets f) (hs : ContDiff ℝ ∞ f)
    (q : ℕ) : NormJets (iteratedFDeriv ℝ q f) := by
  induction q with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact hf.linear hs (continuousMultilinearCurryFin0 ℝ E G).symm.toContinuousLinearEquiv.toContinuousLinearMap
  | succ q ih =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    have hq : ContDiff ℝ ∞ (iteratedFDeriv ℝ q f) := hs.iteratedFDeriv_right (by simp)
    exact ih.derivative.linear (hq.fderiv_right (by simp))
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (q+1) => E) G).symm.toContinuousLinearEquiv.toContinuousLinearMap

lemma NormJets.direction {f : E → ℝ} (hf : NormJets f) (hs : ContDiff ℝ ∞ f)
    (v : E) : NormJets (dir v f) := by
  exact hf.derivative.linear (hs.fderiv_right (by simp)) (ContinuousLinearMap.apply ℝ ℝ v)

lemma NormJets.polynomialJets {f : E → ℝ} (hf : NormJets f) (hs : ContDiff ℝ ∞ f) :
    HasPolynomialJets f := by
  have h (J : List E) : NormJets (partialAlong id J f) := by
    induction J with
    | nil => exact hf
    | cons v J ih => exact ih.direction (contDiff_partialAlong id J hs) v
  intro J
  obtain ⟨C,hC,n,hn⟩ := h J 0
  exact ⟨C,hC,n,fun x => by simpa only [norm_iteratedFDeriv_zero] using hn x⟩

lemma NormJets.const (c : G) : NormJets (fun _ : E => c) := by
  intro n
  cases n with
  | zero =>
    exact growth_of_bound (HasGrowth.const ‖c‖) (fun x => by rw [norm_iteratedFDeriv_zero])
  | succ n =>
    rw [iteratedFDeriv_succ_const]
    exact HasGrowth.const (E := E) (0 : E [×(n+1)]→L[ℝ] G)

open Analysis.PositiveVarianceSlab Tilt.NaturalParameterJets

omit [NormedSpace ℝ E] in
lemma norm_slice_le (t : ℝ) (x : E) :
    1 + ‖(t,x)‖ ≤ (1+|t|)*(1+‖x‖) := by
  rw [Prod.norm_def, Real.norm_eq_abs]
  have hh : max |t| ‖x‖ ≤ |t|+‖x‖ := max_le
    (le_add_of_nonneg_right (norm_nonneg x)) (le_add_of_nonneg_left (abs_nonneg t))
  nlinarith [mul_nonneg (abs_nonneg t) (norm_nonneg x)]

lemma slice_normJets {f : ℝ × E → G} {t : ℝ}
    (ht : -1 < t ∧ t < 1) (hs : ContDiffOn ℝ ∞ f domain)
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x : E,
      ‖iteratedFDerivWithin ℝ n f domain (t,x)‖ ≤ C*(1+‖(t,x)‖)^N) :
    NormJets (fun x : E => f (t,x)) := by
  let a : E → ℝ × E := fun x => (t,x)
  have ha : ContDiff ℝ ∞ a := by dsimp [a]; fun_prop
  have had : fderiv ℝ a = fun _ => ContinuousLinearMap.inr ℝ ℝ E := by
    funext x
    change fderiv ℝ (fun x : E => (t,x)) x = _
    have he : (0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E) =
        ContinuousLinearMap.inr ℝ ℝ E := by ext y <;> rfl
    simpa only [he, id_eq] using ((hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id x)).fderiv
  intro n
  obtain ⟨C,hC,N,hN⟩ := Analysis.PolynomialEnvelope.exists_polynomial_comp_jet_bound
    (U := Set.univ) (S := Set.univ) uniqueDiffOn_univ isOpen_domain.uniqueDiffOn
    (Set.Subset.refl _) ha.contDiffOn hs (fun x _ => ht)
    (R := fun x : E => 1+‖x‖) (fun x _ => le_add_of_nonneg_right (norm_nonneg x)) n
    (fun i _ => by
      obtain ⟨C,hC,N,hN⟩ := hb i
      refine ⟨C*(1+|t|)^N, by positivity, N, ?_⟩
      intro x _
      exact (hN x).trans ((mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (norm_slice_le t x) N) hC).trans_eq
          (by rw [mul_pow, mul_assoc])))
    (fun i _ => by
      refine ⟨1+|t|, by positivity, 1, ?_⟩
      intro x _
      rw [iteratedFDerivWithin_univ]
      cases i with
      | zero =>
        rw [norm_iteratedFDeriv_zero, pow_one]
        exact (le_add_of_nonneg_left zero_le_one).trans (norm_slice_le t x)
      | succ i =>
        rw [← norm_iteratedFDeriv_fderiv, had]
        cases i with
        | zero =>
          rw [norm_iteratedFDeriv_zero, pow_one]
          exact (ContinuousLinearMap.norm_inr_le_one ℝ ℝ E).trans (by nlinarith [abs_nonneg t, norm_nonneg x, mul_nonneg (abs_nonneg t) (norm_nonneg x)])
        | succ i => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]; positivity)
  apply growth_of_envelope N
  intro x
  simpa only [iteratedFDerivWithin_univ, Function.comp_def, a] using hN x (Set.mem_univ x)

end General

section Actual
open Analysis.PositiveVarianceSlab Tilt.NaturalParameterJets
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem scaledJet_one_apply_eq_firstScaledJet {F : E → ℝ} (hF : ContDiff ℝ 2 F) {L : ℝ}
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L*‖w‖^2)
    (x : E) (r : ℝ) {t : ℝ} (htlo : -1 < t) (hthi : t < 1)
    (y : E) (v : Fin 1 → E) :
    scaledJet 1 F x r t y v = firstScaledJet F x r t y (v 0) := by
  unfold scaledJet
  rw [iteratedFDeriv_one_apply, fderiv_centerMean_eq_firstScaledJet hF hlo hhi x r htlo hthi]

theorem conditionalMean_normJets {F : E → ℝ} (hF : ContDiff ℝ 2 F) {L b : ℝ}
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L*‖w‖^2)
    (hb0 : 0 ≤ b) (hb1 : b < 1) (x : E) (r : ℝ) {t : ℝ}
    (ht : t ∈ Icc (left b) (right b)) : NormJets (conditionalMean F x r t) := by
  apply slice_normJets (construction_subset hb0 hb1 ht)
    (contDiffOn_conditionalMean hF hlo hhi x r)
  intro n
  obtain ⟨C,hC,N,hN⟩ := exists_polynomial_conditionalMean_jet_bound hF hlo hhi hb0 hb1 x r n
  exact ⟨C,hC,N,fun y => hN (t,y) ht⟩

theorem scaledJet_normJets (q : ℕ) {F : E → ℝ} (hF : ContDiff ℝ 2 F) {L b : ℝ}
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L*‖w‖^2)
    (hb0 : 0 ≤ b) (hb1 : b < 1) (x : E) (r : ℝ) {t : ℝ}
    (ht : t ∈ Icc (left b) (right b)) : NormJets (scaledJet q F x r t) := by
  by_cases ht0 : t = 0
  · subst t
    change NormJets (fun y : E => scaledJet q F x r 0 y)
    simp only [scaledJet, zero_smul]
    exact NormJets.const
      (E := E) (iteratedFDeriv ℝ q
        (fun c : E => ∫ z, primitiveObservable F x r z ∂
          Gibbs.heatPosterior (primitivePotential F x r) (conditionalVariance 0) c) 0)
  · have ht' := construction_subset hb0 hb1 ht
    have hm : ContDiff ℝ ∞ (conditionalMean F x r t) := by
      have hc : ContDiff ℝ ∞ (fun y : E => (t,y)) := contDiff_const.prodMk contDiff_id
      have hh := (contDiffOn_conditionalMean hF hlo hhi x r).comp
        hc.contDiffOn (s := Set.univ) (fun _ _ => ht')
      exact contDiffOn_univ.mp hh
    have he : scaledJet q F x r t = fun y => (t^q)⁻¹ •
        iteratedFDeriv ℝ q (conditionalMean F x r t) y :=
      funext (scaledJet_eq_inv_smul_iteratedFDeriv q hF hlo hhi x r ht'.1 ht'.2 ht0)
    rw [he]
    have hj := (conditionalMean_normJets hF hlo hhi hb0 hb1 x r ht).iterated hm q
    have hjs : ContDiff ℝ ∞ (iteratedFDeriv ℝ q (conditionalMean F x r t)) :=
      hm.iteratedFDeriv_right (by simp)
    have hh := hj.linear hjs ((t^q)⁻¹ • ContinuousLinearMap.id ℝ (E [×q]→L[ℝ] E))
    exact hh

/-- Every fixed linear coordinate of the full normalized family has all
polynomial spatial derivatives. Division is Lean's total scalar division;
no nonzero-time premise is added, and time zero is proved separately. -/
theorem scaledJet_coordinate_polynomialJets (q : ℕ) {F : E → ℝ}
    (hF : ContDiff ℝ 2 F) {L b : ℝ}
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L*‖w‖^2)
    (hb0 : 0 ≤ b) (hb1 : b < 1) (x : E) (r : ℝ) {t : ℝ}
    (ht : t ∈ Icc (left b) (right b)) (c : ℝ)
    (A : (E [×q]→L[ℝ] E) →L[ℝ] ℝ) :
    HasPolynomialJets (fun y => c * A (scaledJet q F x r t y)) := by
  have hs : ContDiff ℝ ∞ (scaledJet q F x r t) := by
    have hc : ContDiff ℝ ∞ (fun y : E => (t,y)) := contDiff_const.prodMk contDiff_id
    have hh := (contDiffOn_scaledJet q hF hlo hhi x r).comp
      hc.contDiffOn (s := Set.univ) (fun _ _ => construction_subset hb0 hb1 ht)
    exact contDiffOn_univ.mp hh
  have hh := (scaledJet_normJets q hF hlo hhi hb0 hb1 x r ht).linear hs (c • A)
  exact hh.polynomialJets ((c • A).contDiff.comp hs)

theorem score_normJets {F : E → ℝ} (hF : ContDiff ℝ 2 F) {L b : ℝ}
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L*‖w‖^2)
    (hb0 : 0 ≤ b) (hb1 : b < 1) (x : E) (r : ℝ) {t : ℝ}
    (ht : t ∈ Icc (left b) (right b)) :
    NormJets (gradient (interpolationPotential F x r t)) := by
  have ht' := construction_subset hb0 hb1 ht
  have hm : ContDiff ℝ ∞ (conditionalMean F x r t) := by
    have hc : ContDiff ℝ ∞ (fun y : E => (t,y)) := contDiff_const.prodMk contDiff_id
    have hh := (contDiffOn_conditionalMean hF hlo hhi x r).comp
      hc.contDiffOn (s := Set.univ) (fun _ _ => ht')
    exact contDiffOn_univ.mp hh
  rw [show gradient (interpolationPotential F x r t) =
      fun y => y + (r*t) • conditionalMean F x r t y from
    funext (gradient_interpolationPotential hF hlo hhi x r ht'.1 ht'.2)]
  exact (NormJets.clm (ContinuousLinearMap.id ℝ E)).add
    ((conditionalMean_normJets hF hlo hhi hb0 hb1 x r ht).linear hm
      ((r*t) • ContinuousLinearMap.id ℝ E)) contDiff_id (contDiff_const.smul hm)

theorem score_direction_polynomialJets {F : E → ℝ} (hF : ContDiff ℝ 2 F) {L b : ℝ}
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L*‖w‖^2)
    (hb0 : 0 ≤ b) (hb1 : b < 1) (x : E) (r : ℝ) {t : ℝ}
    (ht : t ∈ Icc (left b) (right b)) (v : E) :
    HasPolynomialJets (dir v (interpolationPotential F x r t)) := by
  have ht' := construction_subset hb0 hb1 ht
  have hm : ContDiff ℝ ∞ (conditionalMean F x r t) := by
    have hc : ContDiff ℝ ∞ (fun y : E => (t,y)) := contDiff_const.prodMk contDiff_id
    have hh := (contDiffOn_conditionalMean hF hlo hhi x r).comp
      hc.contDiffOn (s := Set.univ) (fun _ _ => ht')
    exact contDiffOn_univ.mp hh
  have hs : ContDiff ℝ ∞ (gradient (interpolationPotential F x r t)) := by
    rw [show gradient (interpolationPotential F x r t) =
        fun y => y + (r*t) • conditionalMean F x r t y from
      funext (gradient_interpolationPotential hF hlo hhi x r ht'.1 ht'.2)]
    exact contDiff_id.add (contDiff_const.smul hm)
  have he : dir v (interpolationPotential F x r t) =
      (innerSL ℝ v) ∘ gradient (interpolationPotential F x r t) := by
    funext y
    simp [dir]
  rw [he]
  exact ((score_normJets hF hlo hhi hb0 hb1 x r ht).linear hs
    (innerSL ℝ v)).polynomialJets ((innerSL ℝ v).contDiff.comp hs)

/-- Hessian coefficients S=∇²H inherit all polynomial spatial jets. -/
theorem hessian_coordinate_polynomialJets {F : E → ℝ} (hF : ContDiff ℝ 2 F) {L b : ℝ}
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L*‖w‖^2)
    (hb0 : 0 ≤ b) (hb1 : b < 1) (x : E) (r : ℝ) {t : ℝ}
    (ht : t ∈ Icc (left b) (right b)) (u v : E) :
    HasPolynomialJets (dir u (dir v (interpolationPotential F x r t))) :=
  (score_direction_polynomialJets hF hlo hhi hb0 hb1 x r ht v).direction u

/-- Evaluation on a fixed ordered list of slots is a genuine continuous linear
map on the tensor space, including repeated physical coordinate directions. -/
def tensorEvaluation (q : ℕ) (v : Fin q → E) : (E [×q]→L[ℝ] E) →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun A => A v
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    (∏ i, ‖v i‖) (fun A => by change ‖A v‖ ≤ (∏ i, ‖v i‖) * ‖A‖; simpa only [mul_comm] using A.le_opNorm v)

theorem normalized_scaledJet_coordinate_polynomialJets (q : ℕ) {F : E → ℝ}
    (hF : ContDiff ℝ 2 F) {L b : ℝ}
    (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
    (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ L*‖w‖^2)
    (hb0 : 0 ≤ b) (hb1 : b < 1) (x : E) (r : ℝ) {t : ℝ}
    (ht : t ∈ Icc (left b) (right b)) (v : Fin q → E) (w : E) :
    HasPolynomialJets (fun y => (L*r*(q.factorial:ℝ))⁻¹ *
      inner ℝ w (scaledJet q F x r t y v)) := by
  exact scaledJet_coordinate_polynomialJets q hF hlo hhi hb0 hb1 x r ht
    (L*r*(q.factorial:ℝ))⁻¹ ((innerSL ℝ w).comp (tensorEvaluation q v))

end Actual
end AcceleratedLogConcave.Conditional.ScaledJetPolynomial
