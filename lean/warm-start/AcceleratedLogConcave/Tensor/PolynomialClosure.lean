import AcceleratedLogConcave.Tensor.CoordinateReduction
import AcceleratedLogConcave.Conditional.Cumulants
import AcceleratedLogConcave.Conditional.PolynomialMoments
import AcceleratedLogConcave.Conditional.InterpolationTilted

/-! Polynomial tails are preserved by the actual restricted expression
semantics, including arbitrary repeated directional derivatives and weighted
adjoints. This closes qualitative integrability under an actual moment law;
it does not establish the sharp order/dimension estimate. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Tensor.PolynomialClosure
open AdjointReduction CoordinateReduction Conditional.Appell
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Polynomial growth of every literal ordered directional derivative.
Lists retain repeated direction values and their positions. -/
def HasPolynomialJets (f : E → ℝ) : Prop :=
  ∀ J : List E, HasGrowth (partialAlong id J f)

omit [NormedSpace ℝ E] in
lemma growth_list_sum {I : Type*} (l : List I) (f : I → E → ℝ)
    (hf : ∀ i ∈ l, HasGrowth (f i)) : HasGrowth (fun x => (l.map (fun i => f i x)).sum) := by
  induction l with
  | nil => simpa using (HasGrowth.const (E := E) (0 : ℝ))
  | cons i l ih =>
    simpa using (hf i (by simp)).add (ih (fun j hj => hf j (by simp [hj])))

lemma HasPolynomialJets.neg {f : E → ℝ} (hf : HasPolynomialJets f) :
    HasPolynomialJets (fun x => -f x) := by
  intro J
  rw [partialAlong_neg]
  obtain ⟨C, hC, n, hb⟩ := hf J
  exact ⟨C, hC, n, fun x => by simpa using hb x⟩

lemma HasPolynomialJets.add {f g : E → ℝ} (hf : HasPolynomialJets f)
    (hg : HasPolynomialJets g) (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g) :
    HasPolynomialJets (fun x => f x + g x) := by
  intro J
  rw [partialAlong_add id J hfs hgs]
  exact (hf J).add (hg J)

lemma HasPolynomialJets.mul {f g : E → ℝ} (hf : HasPolynomialJets f)
    (hg : HasPolynomialJets g) (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g) :
    HasPolynomialJets (fun x => f x * g x) := by
  intro J
  rw [partialAlong_mul id J hfs hgs]
  exact growth_list_sum (routes J) _ (fun p _ => (hf p.1).mul (hg p.2))

lemma HasPolynomialJets.direction {f : E → ℝ} (hf : HasPolynomialJets f) (v : E) :
    HasPolynomialJets (dir v f) := by
  intro J
  have he : partialAlong id J (dir v f) = partialAlong id (J ++ [v]) f := by
    rw [partialAlong_append]
    rfl
  rw [he]
  exact hf _

lemma HasPolynomialJets.sum {I : Type*} (s : Finset I) (f : I → E → ℝ)
    (hf : ∀ i ∈ s, HasPolynomialJets (f i)) (hs : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) :
    HasPolynomialJets (fun x => ∑ i ∈ s, f i x) := by
  intro J
  rw [partialAlong_sum id J s f hs]
  exact HasGrowth.sum s (fun i hi => hf i hi J)

/-- All decorated expression coordinates inherit polynomial tails from the
coefficient jets and score jets. No integrability, IBP, or terminal estimate
is assumed in this structural closure theorem. -/
theorem section_hasPolynomialJets {Name : Type*} {σ : CoefficientSignature Name} {D : ℕ}
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (hρs : ∀ c a, ContDiff ℝ ∞ (fun x => ρ c x a)) (hHs : ContDiff ℝ ∞ H)
    (hρ : ∀ c a, HasPolynomialJets (fun x => ρ c x a))
    (hH : ∀ v, HasPolynomialJets (dir v H))
    {r : ℕ} (e : Expr σ r) : ∀ a, HasPolynomialJets (sectionValue ρ H e a) := by
  induction e with
  | coefficient c => intro a; exact hρ c a
  | permute p e ih => intro a; rw [section_permute]; exact ih _
  | contract e f i j ihe ihf =>
    intro a
    rw [section_contract]
    apply HasPolynomialJets.sum
    · intro k _
      exact (ihe _).mul (ihf _) (contDiff_section ρ H hρs hHs e _)
        (contDiff_section ρ H hρs hHs f _)
    · intro k _
      exact (contDiff_section ρ H hρs hHs e _).mul (contDiff_section ρ H hρs hHs f _)
  | derivative e ih => intro a; rw [section_derivative]; exact (ih _).direction _
  | adjoint i e ih =>
    intro a
    rw [section_adjoint]
    unfold adjointField adjointComponent
    apply HasPolynomialJets.sum
    · intro k _
      exact ((ih _).direction _).neg.add
        ((hH _).mul (ih _) (contDiff_dir hHs _) (contDiff_section ρ H hρs hHs e _))
        (contDiff_dir (contDiff_section ρ H hρs hHs e _) _).neg
        ((contDiff_dir hHs _).mul (contDiff_section ρ H hρs hHs e _))
    · intro k _
      exact (contDiff_dir (contDiff_section ρ H hρs hHs e _) _).neg.add
        ((contDiff_dir hHs _).mul (contDiff_section ρ H hρs hHs e _))

/-- Direction labels can repeat and are mapped position by position. -/
lemma partialAlong_map_id {L : Type*} (d : L → E) (J : List L) (f : E → ℝ) :
    partialAlong d J f = partialAlong id (J.map d) f := by
  induction J with
  | nil => rfl
  | cons i J ih => simp only [partialAlong, List.map_cons, id_eq, ih]

lemma HasPolynomialJets.growth_partialAlong {f : E → ℝ} (hf : HasPolynomialJets f)
    {L : Type*} (d : L → E) (J : List L) : HasGrowth (partialAlong d J f) := by
  rw [partialAlong_map_id]
  exact hf _

/-- Discharge every analytic product obligation of the existing complete
coordinate reduction, from actual derivative growth and a genuine moment law.
No integration identity is a premise. -/
theorem productIntegrability_of_polynomialJets [MeasurableSpace E]
    {ν : Measure E} [IsFiniteMeasure ν] (hν : HasMoments ν)
    {L K : Type*} [Fintype K] [DecidableEq K] (d : L → E) (J : List L)
    (H f : E → ℝ) (v : E) (g : K → E → ℝ)
    (hHs : ContDiff ℝ ∞ H) (hfs : ContDiff ℝ ∞ f) (hgs : ∀ k, ContDiff ℝ ∞ (g k))
    (hH : HasPolynomialJets (dir v H)) (hf : HasPolynomialJets f)
    (hg : ∀ k, HasPolynomialJets (g k)) [BorelSpace E] :
    ProductIntegrability ν d J H f v g := by
  have hprod : HasGrowth (fun x => ∏ k, g k x) :=
    HasGrowth.prod Finset.univ (fun k _ => hg k [])
  have hcprod : Continuous (fun x => ∏ k, g k x) :=
    continuous_finsetProd _ (fun k _ => (hgs k).continuous)
  have hj := hf.growth_partialAlong d J
  have hcj := (contDiff_partialAlong d J hfs).continuous
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (hj.mul hprod).integrable (hcj.mul hcprod).aestronglyMeasurable hν
  · exact (((hH []).mul hj).mul hprod).integrable
      (((contDiff_dir hHs v).continuous.mul hcj).mul hcprod).aestronglyMeasurable hν
  · have hd : HasGrowth (dir v (partialAlong d J f)) := by
      rw [partialAlong_map_id]
      exact hf (v :: J.map d)
    exact (hd.mul hprod).integrable
      ((contDiff_dir (contDiff_partialAlong d J hfs) v).continuous.mul hcprod).aestronglyMeasurable hν
  · intro k
    exact ((hj.mul ((hg k).direction v [])).mul
      (HasGrowth.prod (Finset.univ.erase k) (fun j _ => hg j []))).integrable
      ((hcj.mul (contDiff_dir (hgs k) v).continuous).mul
        (continuous_finsetProd _ (fun j _ => (hgs j).continuous))).aestronglyMeasurable hν
  · intro p _
    exact (((hH.growth_partialAlong d p.1).mul (hf.growth_partialAlong d p.2)).mul hprod).integrable
      (((contDiff_partialAlong d p.1 (contDiff_dir hHs v)).continuous.mul
        (contDiff_partialAlong d p.2 hfs).continuous).mul hcprod).aestronglyMeasurable hν

/-- Every power of every decorated expression coordinate is integrable under
the actual interpolation law. Polynomial tails are proved by grammar induction,
not passed as an integrability certificate for the finished expression. -/
theorem interpolation_integrable_section_pow {Name : Type*} {σ : CoefficientSignature Name} {D : ℕ}
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (hρs : ∀ c a, ContDiff ℝ ∞ (fun x => ρ c x a)) (hHs : ContDiff ℝ ∞ H)
    (hρ : ∀ c a, HasPolynomialJets (fun x => ρ c x a))
    (hH : ∀ v, HasPolynomialJets (dir v H))
    {F : EuclideanSpace ℝ (Fin D) → ℝ} (hF : ContDiff ℝ 2 F)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (x : EuclideanSpace ℝ (Fin D)) (r t : ℝ)
    {s : ℕ} (e : Expr σ s) (a : Fin s → Fin D)
    (J : List (EuclideanSpace ℝ (Fin D))) (q : ℕ) :
    Integrable (fun y => (partialAlong id J (sectionValue ρ H e a) y) ^ q)
      (Conditional.interpolationLaw F x r t) := by
  let := Conditional.interpolationLaw_isProbabilityMeasure hF hlo x r t
  exact ((section_hasPolynomialJets ρ H hρs hHs hρ hH e a J).pow q).integrable
    ((contDiff_partialAlong id J (contDiff_section ρ H hρs hHs e a)).continuous.pow q).aestronglyMeasurable
    (Conditional.interpolationLaw_integrable_norm_pow hF hlo x r t)

/-- The complete decorated-adjoint reduction on the ACTUAL interpolation law.
Normalizability, law identification and potential smoothness are discharged
from the original data. Only constituent polynomial jet growth remains as
an explicit coefficient-level analytic premise. -/
theorem interpolation_integral_decorated_adjoint
    {D : ℕ} {L K : Type*} [Fintype K] [DecidableEq K]
    {F : EuclideanSpace ℝ (Fin D) → ℝ} (hF : ContDiff ℝ 2 F) {ell t : ℝ}
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : EuclideanSpace ℝ (Fin D)) (r : ℝ) (htlo : -1 < t) (hthi : t < 1)
    (d : L → EuclideanSpace ℝ (Fin D)) (J : List L)
    (f : EuclideanSpace ℝ (Fin D) → ℝ) (v : EuclideanSpace ℝ (Fin D))
    (g : K → EuclideanSpace ℝ (Fin D) → ℝ)
    (hfs : ContDiff ℝ ∞ f) (hgs : ∀ k, ContDiff ℝ ∞ (g k))
    (hscore : HasPolynomialJets (dir v (Conditional.interpolationPotential F x r t)))
    (hf : HasPolynomialJets f) (hg : ∀ k, HasPolynomialJets (g k)) :
    (∫ y, partialAlong d J (adjointComponent (Conditional.interpolationPotential F x r t) v f) y *
      ∏ k, g k y ∂Conditional.interpolationLaw F x r t) =
      (∑ k, ∫ y, partialAlong d J f y * dir v (g k) y *
        ∏ s ∈ Finset.univ.erase k, g s y ∂Conditional.interpolationLaw F x r t) +
      ((scoreRoutes J).map (fun p => ∫ y,
        partialAlong d p.1 (dir v (Conditional.interpolationPotential F x r t)) y *
        partialAlong d p.2 f y * ∏ k, g k y ∂Conditional.interpolationLaw F x r t)).sum := by
  let := Conditional.interpolationLaw_isProbabilityMeasure hF hlo x r t
  have hHs := Conditional.contDiff_interpolationPotential hF hlo hup x r htlo hthi
  have hi := productIntegrability_of_polynomialJets
    (Conditional.interpolationLaw_integrable_norm_pow hF hlo x r t) d J
    (Conditional.interpolationPotential F x r t) f v g hHs hfs hgs hscore hf hg
  rw [Conditional.interpolationLaw_eq_tilted hF hlo x r htlo hthi] at hi ⊢
  exact integral_decorated_adjoint_mul_prod d J hHs hfs v g
    (fun k => (hgs k).differentiable (by simp))
    (Conditional.integrable_exp_neg_interpolationPotential hF hlo x r htlo hthi) hi

end AcceleratedLogConcave.Tensor.PolynomialClosure
