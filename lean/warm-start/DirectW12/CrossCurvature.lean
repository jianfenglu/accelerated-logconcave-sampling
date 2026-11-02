import DirectW12.VectorIncrement
import AcceleratedLogConcave.Root.BackwardParentLaw

/-!

-/
noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory InnerProductSpace Set Function Filter
open scoped Topology NNReal RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.DirectW12
open Analysis.Poisson Analysis.WeightedGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {a b : ℝ}
section Field
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
variable (μ : Measure X) (A : X → E →L[ℝ] E) (hA : Continuous A)
  (M : ℝ) (hM : ∀ x, ‖A x‖ ≤ M)
include hA hM

omit [MeasurableSpace E] [BorelSpace E] in
private theorem phaseField_memLp (G : Lp E 2 μ) : MemLp (fun x => A x (G x)) 2 μ := by
  apply (Lp.memLp G).of_le_mul
    ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hA.aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable G)))
  exact Eventually.of_forall fun x => ((A x).le_opNorm (G x)).trans
    (mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))

private def phaseFieldAction (G : Lp E 2 μ) : Lp E 2 μ := (phaseField_memLp μ A hA M hM G).toLp _
omit [MeasurableSpace E] [BorelSpace E] in
private theorem phaseFieldAction_coe (G : Lp E 2 μ) :
    phaseFieldAction μ A hA M hM G =ᵐ[μ] fun x => A x (G x) :=
  (phaseField_memLp μ A hA M hM G).coeFn_toLp

/-- Multiplication by a continuous uniformly bounded spatial matrix field. -/
def phaseFieldMultiplier : Lp E 2 μ →L[ℝ] Lp E 2 μ := LinearMap.mkContinuous
  { toFun := phaseFieldAction μ A hA M hM
    map_add' := by
      intro G F
      apply Lp.ext
      filter_upwards [phaseFieldAction_coe μ A hA M hM (G + F), phaseFieldAction_coe μ A hA M hM G,
        phaseFieldAction_coe μ A hA M hM F, Lp.coeFn_add G F,
        Lp.coeFn_add (phaseFieldAction μ A hA M hM G) (phaseFieldAction μ A hA M hM F)] with x h1 h2 h3 h4 h5
      simp only [h1, h4, h5, Pi.add_apply, h2, h3, map_add]
    map_smul' := by
      intro c G
      apply Lp.ext
      filter_upwards [phaseFieldAction_coe μ A hA M hM (c • G), phaseFieldAction_coe μ A hA M hM G,
        Lp.coeFn_smul c G, Lp.coeFn_smul c (phaseFieldAction μ A hA M hM G)] with x h1 h2 h3 h4
      simp only [RingHom.id_apply, h1, h3, h4, Pi.smul_apply, h2, map_smul] }
  M (fun G => Lp.norm_le_mul_norm_of_ae_le_mul (by
    filter_upwards [phaseFieldAction_coe μ A hA M hM G] with x hx
    change ‖(phaseFieldAction μ A hA M hM G) x‖ ≤ M * ‖G x‖
    rw [hx]
    exact ((A x).le_opNorm (G x)).trans
      (mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))))

omit [MeasurableSpace E] [BorelSpace E] in
theorem phaseFieldMultiplier_coe (G : Lp E 2 μ) :
    phaseFieldMultiplier μ A hA M hM G =ᵐ[μ] fun x => A x (G x) := phaseFieldAction_coe μ A hA M hM G
end Field

/-- The genuine physical inverse, with final-law input; no auxiliary endpoint. -/
def physicalGradientInverse (P : ReferencePoissonFamily E a b) (t : Icc a b) :=
  gradientPoissonInverse (P.law t) (P.potential t) (P.potential_C2 t)
    (P.integrable t t.property) (P.gibbs_law t t.property)
    (P.lower t) 1 (P.lower_pos t t.property) (P.hessian_lower t t.property)
    (by simpa only [one_mul] using P.hessian_upper t t.property)

def actualHessian (P : ReferencePoissonFamily E a b) (t : Icc a b) :=
  hessianMultiplier (P.law t) (P.potential t) (P.potential_C2 t)
    (P.lower t) 1 (P.hessian_lower t t.property)
    (by simpa only [one_mul] using P.hessian_upper t t.property)

/-- Same-time energy is proved from the actual weak Bochner equality. -/
theorem actualHessianBochner (P : ReferencePoissonFamily E a b) (t : Icc a b)
    (f : Lp ℝ 2 (P.law t)) :
    inner ℝ (actualHessian P t (physicalGradientInverse P t f))
      (physicalGradientInverse P t f) ≤ ‖f‖^2 := by
  let hu := poissonSolution_spec (μ := P.law t) (V := P.potential t)
    (hV := P.potential_C2 t) (hI := P.integrable t t.property)
    (hμ := P.gibbs_law t t.property) (m := P.lower t) (L := 1)
    (hm := P.lower_pos t t.property) (hlower := P.hessian_lower t t.property)
    (hupper := by simpa only [one_mul] using P.hessian_upper t t.property) f
  obtain ⟨rows, _, hb⟩ := weak_poisson_bochner (P.law t) (P.potential t)
    (P.potential_C2 t) (P.integrable t t.property) (P.gibbs_law t t.property)
    (P.lower t) 1 (P.lower_pos t t.property) (P.hessian_lower t t.property)
    (by simpa only [one_mul] using P.hessian_upper t t.property) _ _ hu.2
  have hs : 0 ≤ ∑ i, ‖rows i‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc := norm_centerForcing_le (P.law t) f
  change ‖centerForcing (P.law t) f‖^2 = (∑ i, ‖rows i‖^2) +
    inner ℝ (actualHessian P t (physicalGradientInverse P t f))
      (physicalGradientInverse P t f) at hb
  nlinarith [norm_nonneg (centerForcing (P.law t) f), norm_nonneg f]

theorem actualHessian_gradient_norm_le (P : ReferencePoissonFamily E a b)
    (t : Icc a b) (f : Lp ℝ 2 (P.law t)) :
    ‖actualHessian P t (physicalGradientInverse P t f)‖ ≤ ‖f‖ := by
  have h := hessianMultiplier_comp_gradientPoissonInverse_norm_le
    (P.law t) (P.potential t) (P.potential_C2 t)
    (P.integrable t t.property) (P.gibbs_law t t.property)
    (P.lower t) (P.lower_pos t t.property) (P.hessian_lower t t.property)
    (by simpa only [one_mul] using P.hessian_upper t t.property)
  change ‖(actualHessian P t).comp (physicalGradientInverse P t)‖ ≤ 1 at h
  exact ((actualHessian P t).comp (physicalGradientInverse P t)).le_opNorm f |>.trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right h (norm_nonneg f))

/-- Hessian at the earlier point of the SAME actual forward trajectory. -/
def pathHessianField (P : ReferencePoissonFamily E a b) (ell : ℝ) (u : Icc a b)
    (z : E × E) : E →L[ℝ] E :=
  hessianOperator (P.potential u) (referenceCoupledPairFlow P ell u z).1

theorem pathHessianField_continuous (P : ReferencePoissonFamily E a b)
    (ell : ℝ) (u : Icc a b) : Continuous (pathHessianField P ell u) :=
  (continuous_hessianOperator (P.potential_C2 u)).comp
    (referenceCoupledPairFlow P ell u).continuous.fst

theorem pathHessianField_norm_le (P : ReferencePoissonFamily E a b)
    (ell : ℝ) (u : Icc a b) (z : E × E) : ‖pathHessianField P ell u z‖ ≤ 1 := by
  simpa only [pathHessianField, abs_zero, abs_one, max_eq_right zero_le_one] using
    hessianOperator_norm_le (P.potential_C2 u)
      (m := 0) (L := 1)
      (by simpa only [zero_mul] using P.hessian_nonneg u u.property)
      (by simpa only [one_mul] using P.hessian_upper u u.property)
      (referenceCoupledPairFlow P ell u z).1

def pathHessian (P : ReferencePoissonFamily E a b) (ell : ℝ) (u : Icc a b) :=
  phaseFieldMultiplier ((P.law a).prod (stdGaussian E))
    (pathHessianField P ell u) (pathHessianField_continuous P ell u) 1
    (pathHessianField_norm_le P ell u)

theorem pathHessian_coe (P : ReferencePoissonFamily E a b) (ell : ℝ) (u : Icc a b)
    (v : Lp E 2 ((P.law a).prod (stdGaussian E))) :
    (pathHessian P ell u v : E × E → E) =ᵐ[(P.law a).prod (stdGaussian E)]
      fun z => pathHessianField P ell u z (v z) :=
  phaseFieldMultiplier_coe _ _ _ _ _ v

theorem pathHessian_norm_le (P : ReferencePoissonFamily E a b) (ell : ℝ) (u : Icc a b)
    (v : Lp E 2 ((P.law a).prod (stdGaussian E))) : ‖pathHessian P ell u v‖ ≤ ‖v‖ := by
  have hb : ‖pathHessian P ell u v‖ ≤ 1 * ‖v‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [pathHessian_coe P ell u v] with z hz
    rw [hz]
    exact ((pathHessianField P ell u z).le_opNorm (v z)).trans
      (mul_le_mul_of_nonneg_right (pathHessianField_norm_le P ell u z) (norm_nonneg _))
  simpa only [one_mul] using hb
theorem pathHessian_symmetric (P : ReferencePoissonFamily E a b) (ell : ℝ)
    (u : Icc a b) : (pathHessian P ell u).IsSymmetric := by
  intro v w
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [pathHessian_coe P ell u v, pathHessian_coe P ell u w] with z hv hw
  change inner ℝ (pathHessian P ell u v z) (w z) =
    inner ℝ (v z) (pathHessian P ell u w z)
  rw [hv, hw]
  exact hessianOperator_symmetric (P.potential_C2 u) _ _ _

/-- Actual intertwining, with both composition null sets pulled back legally. -/
theorem pathHessian_coupledVector (P : ReferencePoissonFamily E a b) (ell : ℝ)
    (u : Icc a b) (g : Lp ℝ 2 (P.law a)) :
    pathHessian P ell u (physicalCoupledVector P ell g u) =
      coupledPullback P ell u
        (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst
          (actualHessian P u (physicalGradient P g u))) := by
  apply Lp.ext
  let mp := referenceCoupledPairFlow_measurePreserving P ell u
  filter_upwards [pathHessian_coe P ell u (physicalCoupledVector P ell g u),
    physicalCoupledVector_coe P ell g u,
    Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst
        (actualHessian P u (physicalGradient P g u))) mp,
    mp.quasiMeasurePreserving.ae
      (Lp.coeFn_compMeasurePreserving (actualHessian P u (physicalGradient P g u))
        measurePreserving_fst),
    (measurePreserving_fst.comp mp).quasiMeasurePreserving.ae
      (hessianMultiplier_coe (P.law u) (P.potential u) (P.potential_C2 u)
        (P.lower u) 1 (P.hessian_lower u u.property)
        (by simpa only [one_mul] using P.hessian_upper u u.property)
        (physicalGradient P g u))] with z h1 h2 h3 h4 h5
  change (coupledPullback P ell u
      (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst
        (actualHessian P u (physicalGradient P g u)))) z =
    (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst
      (actualHessian P u (physicalGradient P g u)))
        (referenceCoupledPairFlow P ell u z) at h3
  change (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst
      (actualHessian P u (physicalGradient P g u)))
        (referenceCoupledPairFlow P ell u z) =
    actualHessian P u (physicalGradient P g u)
      (referenceCoupledPairFlow P ell u z).1 at h4
  change actualHessian P u (physicalGradient P g u)
      (referenceCoupledPairFlow P ell u z).1 =
    pathHessianField P ell u z
      (physicalGradient P g u (referenceCoupledPairFlow P ell u z).1) at h5
  rw [h1, h2]
  exact (h3.trans (h4.trans h5)).symm

/-- Same-time curvature energy and Hessian-action bounds on the actual path. -/
theorem pathHessian_same_time (P : ReferencePoissonFamily E a b) (ell : ℝ)
    (u : Icc a b) (g : Lp ℝ 2 (P.law a)) :
    inner ℝ (pathHessian P ell u (physicalCoupledVector P ell g u))
      (physicalCoupledVector P ell g u) ≤ ‖g‖^2 ∧
    ‖pathHessian P ell u (physicalCoupledVector P ell g u)‖ ≤ ‖g‖ := by
  simp only [pathHessian_coupledVector]
  constructor
  · unfold physicalCoupledVector
    rw [LinearIsometry.inner_map_map, LinearIsometry.inner_map_map]
    simpa only [physicalGradient, physicalGradientInverse, LinearIsometryEquiv.norm_map] using
      actualHessianBochner P u ((P.unitary u).symm g)
  · simp only [LinearIsometry.norm_map]
    simpa only [physicalGradient, physicalGradientInverse, LinearIsometryEquiv.norm_map] using
      actualHessian_gradient_norm_le P u ((P.unitary u).symm g)

/-- Pure Hilbert algebra used below, proved here rather than assumed as a field. -/
theorem symmetric_contraction_increment {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (T : H →L[ℝ] H) (hs : T.IsSymmetric)
    (hn : ∀ v, ‖T v‖ ≤ ‖v‖) (v w : H) {G D : ℝ}
    (hG : 0 ≤ G) (hD : 0 ≤ D) (hw : inner ℝ (T w) w ≤ G^2)
    (hTw : ‖T w‖ ≤ G) (hdelta : ‖v-w‖ ≤ D) :
    inner ℝ (T v) v ≤ (G+D)^2 := by
  let d := v-w
  have hv : v = w+d := by dsimp [d]; abel
  have hmix : inner ℝ (T w) d ≤ G*D :=
    (real_inner_le_norm _ _).trans (mul_le_mul hTw hdelta (norm_nonneg _) hG)
  have hdd : inner ℝ (T d) d ≤ D^2 := by
    calc
      _ ≤ ‖T d‖ * ‖d‖ := real_inner_le_norm _ _
      _ ≤ D * D := mul_le_mul ((hn d).trans hdelta) hdelta (norm_nonneg _) hD
      _ = _ := by ring
  rw [hv, map_add, inner_add_left, inner_add_right, inner_add_right]
  have hsym : inner ℝ (T d) w = inner ℝ (T w) d :=
    (hs d w).trans (real_inner_comm _ _)
  rw [hsym]
  nlinarith

/-- Exact closed-clock same-path cross-curvature in the initial phase law. -/
theorem physical_poisson_cross_curvature_path (P : ReferencePoissonFamily E a b)
    {ell A u R : ℝ} (hell : 0 ≤ ell) (hA : 0 ≤ A) (hu : 0 ≤ u)
    (huR : u ≤ R) (huI : u ∈ Icc a b) (hRI : R ∈ Icc a b)
    (hscale : ∀ r ∈ Ioo u R, P.scale r = A*r)
    (g : Lp ℝ 2 (P.law a)) :
    inner ℝ (pathHessian P ell ⟨u,huI⟩ (physicalCoupledVector P ell g ⟨R,hRI⟩))
      (physicalCoupledVector P ell g ⟨R,hRI⟩) ≤
      (1 + ell*(R-u) + A*(R^2-u^2)/2)^2 * ‖g‖^2 := by
  let c := ell*(R-u) + A*(R^2-u^2)/2
  have hc : 0 ≤ c := by
    dsimp [c]
    apply add_nonneg (mul_nonneg hell (sub_nonneg.mpr huR))
    apply div_nonneg (mul_nonneg hA _) (by norm_num)
    nlinarith [mul_nonneg (sub_nonneg.mpr huR) (add_nonneg (hu.trans huR) hu)]
  obtain ⟨henergy, haction⟩ := pathHessian_same_time P ell ⟨u,huI⟩ g
  have hb := symmetric_contraction_increment (pathHessian P ell ⟨u,huI⟩)
    (pathHessian_symmetric P ell ⟨u,huI⟩) (pathHessian_norm_le P ell ⟨u,huI⟩)
    (physicalCoupledVector P ell g ⟨R,hRI⟩) (physicalCoupledVector P ell g ⟨u,huI⟩)
    (norm_nonneg g) (mul_nonneg hc (norm_nonneg g)) henergy haction
    (physicalCoupledVector_increment_le P hell hA hu huR huI hRI hscale g)
  convert hb using 1
  dsimp [c]
  ring

section Terminal
variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ ι

/-- The exact production backward center recovers the same earlier path point. -/
theorem actualBackwardCenter_forward (P : ReferencePoissonFamily V a b)
    (ell : ℝ) (R u : Icc a b) (z : V × V) :
    Root.BackwardParentLaw.backwardCenter P ell R u
      (referenceCoupledPairFlow P ell R z) = (referenceCoupledPairFlow P ell u z).1 := by
  exact congrArg Prod.fst (Root.BackwardParentLaw.backwardPair_forward P ell R u z)

/-- Exact equality of the terminal-parent integral with the path quadratic form.
The terminal Hessian is evaluated at the actual backwardCenter, never at a fresh draw. -/
theorem terminal_curvature_eq_path (P : ReferencePoissonFamily V a b)
    (ell : ℝ) (R u : Icc a b) (gR : Lp ℝ 2 (P.law R)) :
    (∫ z, fderiv ℝ (fderiv ℝ (P.potential u))
      (Root.BackwardParentLaw.backwardCenter P ell R u z)
      (physicalGradientInverse P R gR z.1) (physicalGradientInverse P R gR z.1)
      ∂(P.law R).prod (stdGaussian V)) =
    inner ℝ (pathHessian P ell u (physicalCoupledVector P ell (P.unitary R gR) R))
      (physicalCoupledVector P ell (P.unitary R gR) R) := by
  rw [← (referenceCoupledPairFlow_measurePreserving P ell R).integral_comp
    (referenceCoupledPairFlow P ell R).toMeasurableEquiv.measurableEmbedding]
  rw [L2.inner_def]
  have hv : physicalGradient P (P.unitary R gR) R = physicalGradientInverse P R gR := by
    unfold physicalGradient physicalGradientInverse
    rw [LinearIsometryEquiv.symm_apply_apply]
  apply integral_congr_ae
  filter_upwards [pathHessian_coe P ell u (physicalCoupledVector P ell (P.unitary R gR) R),
    physicalCoupledVector_coe P ell (P.unitary R gR) R] with z hH hW
  rw [hH, hW, hv, actualBackwardCenter_forward]
  exact (inner_hessianOperator (P.potential u) _ _ _).symm

/-- The terminal curvature integral is genuinely integrable, independently of
Lean's convention for the integral of a nonintegrable function. -/
theorem terminal_curvature_integrable (P : ReferencePoissonFamily V a b)
    (ell : ℝ) (R u : Icc a b) (gR : Lp ℝ 2 (P.law R)) :
    Integrable (fun z => fderiv ℝ (fderiv ℝ (P.potential u))
      (Root.BackwardParentLaw.backwardCenter P ell R u z)
      (physicalGradientInverse P R gR z.1) (physicalGradientInverse P R gR z.1))
      ((P.law R).prod (stdGaussian V)) := by
  apply ((referenceCoupledPairFlow_measurePreserving P ell R).integrable_comp_emb
    (referenceCoupledPairFlow P ell R).toMeasurableEquiv.measurableEmbedding).mp
  let W := physicalCoupledVector P ell (P.unitary R gR) R
  apply (L2.integrable_inner (pathHessian P ell u W) W).congr
  have hv : physicalGradient P (P.unitary R gR) R = physicalGradientInverse P R gR := by
    unfold physicalGradient physicalGradientInverse
    rw [LinearIsometryEquiv.symm_apply_apply]
  filter_upwards [pathHessian_coe P ell u W,
    physicalCoupledVector_coe P ell (P.unitary R gR) R] with z hH hW
  dsimp only [Function.comp_def]
  change inner ℝ (pathHessian P ell u W z) (W z) = _
  rw [hH, hW, hv, actualBackwardCenter_forward]
  exact inner_hessianOperator (P.potential u) _ _ _

/-- Source-facing terminal-parent cross-curvature with the exact affine factor.
All closed endpoints, R=u, and dimension zero are included. -/
theorem physical_poisson_cross_curvature (P : ReferencePoissonFamily V a b)
    {ell A u R : ℝ} (hell : 0 ≤ ell) (hA : 0 ≤ A) (hu : 0 ≤ u)
    (huR : u ≤ R) (huI : u ∈ Icc a b) (hRI : R ∈ Icc a b)
    (hscale : ∀ r ∈ Ioo u R, P.scale r = A*r)
    (gR : Lp ℝ 2 (P.law R)) :
    (∫ z, fderiv ℝ (fderiv ℝ (P.potential u))
      (Root.BackwardParentLaw.backwardCenter P ell ⟨R,hRI⟩ ⟨u,huI⟩ z)
      (physicalGradientInverse P ⟨R,hRI⟩ gR z.1)
      (physicalGradientInverse P ⟨R,hRI⟩ gR z.1)
      ∂(P.law R).prod (stdGaussian V)) ≤
      (1 + ell*(R-u) + A*(R^2-u^2)/2)^2 * ‖gR‖^2 := by
  rw [terminal_curvature_eq_path P ell ⟨R, hRI⟩ ⟨u, huI⟩ gR]
  simpa only [LinearIsometryEquiv.norm_map] using
    physical_poisson_cross_curvature_path P hell hA hu huR huI hRI hscale
      (P.unitary ⟨R,hRI⟩ gR)

end Terminal
end AcceleratedLogConcave.Kinetic.DirectW12
