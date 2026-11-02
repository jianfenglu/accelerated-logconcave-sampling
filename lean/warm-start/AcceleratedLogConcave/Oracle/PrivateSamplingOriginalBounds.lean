import AcceleratedLogConcave.Oracle.PrivateSamplingRetainedRms
import AcceleratedLogConcave.Numerics.SamplingGaussianJetLp
import AcceleratedLogConcave.Conditional.RecursiveReferenceCovariance

/-! Original-data quantitative bounds for the literal private initializer and
sampling-row residual. Actual Gaussian-start fields and full-tape projections
are retained; no derivative regularity or desired error budget is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff Topology BigOperators
namespace AcceleratedLogConcave.Oracle.PrivateSamplingOriginalBounds
open Numerics Numerics.AffineGraph SamplingGaussianJetLp ConditionalSmoothing
open Analysis.PositiveVarianceSlab
variable {D : ℕ} (d : SamplingCenterLp.Data (Fin D)) (x : EuclideanSpace ℝ (Fin D))
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "γ" => stdGaussian E
local notation "centered" => SamplingFlowLp.centeredReply d.hF d.hell d.hlo d.hup x d.hr d.hb d.hb1
local notation "centeredLp" => SamplingFlowLp.replyLp d.hF d.hell d.hlo d.hup x d.hr d.hb d.hb1

/-- The actual transported conditional covariance, on its original Gaussian seed. -/
theorem centeredReply_norm (hsmall : d.r^2*d.ell ≤ 1/2) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    ‖centeredLp t‖ ≤ (Real.exp 1*(d.r*d.ell))*Real.sqrt (Module.finrank ℝ E) := by
  let ν := Conditional.interpolationLaw d.F x d.r t
  let : IsProbabilityMeasure ν := Conditional.interpolationLaw_isProbabilityMeasure d.hF d.hlo x d.r t
  let g : E → E := fun y => Conditional.conditionalMean d.F x d.r t y-Gibbs.primitiveMean d.F x d.r
  have hg : MemLp g 2 ν :=
    (Conditional.RecursiveReferenceCovariance.conditionalMean_memLp
      d.hF d.hell d.hlo d.hup x d.hr ht.1 (ht.2.trans_lt d.hb1)).sub (memLp_const _)
  have hp := ConditionalSmoothing.path_measurePreserving d x ht
  have hgm : AEStronglyMeasurable (fun y => ‖g y‖^2) ((stdGaussian E).map (SamplingCenterLp.path d x t)) := by
    rw [hp.map_eq]
    exact hg.aestronglyMeasurable.norm.pow 2
  have hmap := integral_map hp.measurable.aemeasurable hgm
  rw [hp.map_eq] at hmap
  have hfunc (z : E) : centered t z = g (SamplingCenterLp.path d x t z) := by
    rw [SamplingFlowLp.centeredReply_eq_conditionalMean,SamplingFlowLp.sourceTime_eq d.hb ht]
    rfl
  have hs := Analysis.DominatedLp.norm_sq_toLp
    (SamplingFlowLp.samplingCenteredReply_memLp_two d.hF d.hell d.hlo d.hup x d.hr d.hb d.hb1 t)
  have hb := Conditional.integral_conditionalMean_centered_norm_sq_le
    d.hF d.hell d.hlo d.hup x d.hr ht.1 (ht.2.trans_lt d.hb1) hsmall
  have hi : (∫ z, ‖centered t z‖^2 ∂γ) = ∫ y, ‖g y‖^2 ∂ν := by
    simp_rw [hfunc]
    exact hmap.symm
  change ‖centeredLp t‖^2 = _ at hs
  rw [hi] at hs
  change (∫ y, ‖g y‖^2 ∂ν) ≤ _ at hb
  have hdim := Real.sq_sqrt (Nat.cast_nonneg (Module.finrank ℝ E))
  have hnon : 0 ≤ (Real.exp 1*(d.r*d.ell))*Real.sqrt (Module.finrank ℝ E) := by positivity [d.hr.le,d.hell]
  nlinarith [norm_nonneg (centeredLp t)]

/-- Only the original center gradient and public scalar data enter this budget. -/
def replyBudget : ℝ :=
  ‖gradient d.F x‖ + (d.ell*d.r)*(Real.sqrt (Module.finrank ℝ E)+d.r*‖gradient d.F x‖) +
    (Real.exp 1*(d.r*d.ell))*Real.sqrt (Module.finrank ℝ E)

theorem replyBudget_nonneg : 0 ≤ replyBudget d x := by
  unfold replyBudget
  positivity [d.hr.le,d.hell]

theorem primitiveMean_norm_le : ‖Gibbs.primitiveMean d.F x d.r‖ ≤
    ‖gradient d.F x‖ + (d.ell*d.r)*(Real.sqrt (Module.finrank ℝ E)+d.r*‖gradient d.F x‖) := by
  have hb := (Gibbs.norm_primitiveMean_sub_gradient_le_rms d.hF d.hell d.hlo d.hup d.hr.le x).trans
    (mul_le_mul_of_nonneg_left (Gibbs.primitive_second_moment_le d.hF d.hell d.hlo d.hup d.hr x)
      (mul_nonneg d.hell d.hr.le))
  have ht := norm_add_le (Gibbs.primitiveMean d.F x d.r-gradient d.F x) (gradient d.F x)
  rw [sub_add_cancel] at ht
  linarith

theorem meanLp_norm_le (hsmall : d.r^2*d.ell ≤ 1/2) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    ‖meanLp d x t‖ ≤ replyBudget d x := by
  have he : meanLp d x t = centeredLp t +
      (memLp_const (μ := γ) (p := 2) (Gibbs.primitiveMean d.F x d.r)).toLp
        (fun _ => Gibbs.primitiveMean d.F x d.r) := by
    rw [meanLp_eq_toLp d x ht]
    exact MemLp.toLp_add _ _
  have hc : ‖(memLp_const (μ := γ) (p := 2) (Gibbs.primitiveMean d.F x d.r)).toLp
      (fun _ => Gibbs.primitiveMean d.F x d.r)‖ = ‖Gibbs.primitiveMean d.F x d.r‖ := by
    simp [MemLp.toLp_const,Lp.norm_const]
  rw [he]
  have hh := norm_add_le (centeredLp t)
    ((memLp_const (μ := γ) (p := 2) (Gibbs.primitiveMean d.F x d.r)).toLp (fun _ => Gibbs.primitiveMean d.F x d.r))
  rw [hc] at hh
  exact hh.trans (by have h1 := centeredReply_norm d x hsmall ht; have h2 := primitiveMean_norm_le d x; unfold replyBudget; linarith)

theorem meanLp_row_defect (hsmall : d.r^2*d.ell ≤ 1/2)
    (M : IntervalMesh 0 d.b) (m : ℕ) (hm : 1 ≤ m) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    ‖(∫ s in 0..t, meanLp d x s) -
      ∑ j : M.Source m, M.row m 0 t j • meanLp d x (M.location m j)‖ ≤
      AffineResidual.cellBudget M m (fun _ => derivativeBudget d m) :=
  AffineResidual.intervalRowDefect M m hm 0 t ⟨le_rfl,d.hb⟩ ht
    (meanLp d x) (fun _ => derivativeBudget d m) (meanLp_cellRegularity d x hsmall M m hm)

def initialErrorLp (t : ℝ) : Lp E 2 γ :=
  (d.r*t) • (jetLp d x 0 0-jetLp d x 0 t)

/-- Signed strong FTC for the actual Gaussian-start path, with no endpoint
derivative premise: the source endpoints lie in the open construction slab. -/
theorem initialErrorLp_integral {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    initialErrorLp d x t = (d.r^2*t) • (∫ s in 0..t, meanLp d x s) := by
  have hint : IntervalIntegrable (jetLp d x 1) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1
      ((jetLp_contDiffOn d x 1 0).continuousOn.mono (fun u hu =>
        source_subset d.hb d.hb1 ⟨hu.1,hu.2.trans ht.2⟩))
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => jetLp_deriv d x 0 (source_subset d.hb d.hb1 (by
      rw [uIcc_of_le ht.1] at hu
      exact ⟨hu.1,hu.2.trans ht.2⟩))) hint
  have hjet (s : ℝ) : jetLp d x 1 s = (-d.r) • meanLp d x s := by
    simp only [meanLp,smul_smul,mul_inv_cancel₀ (neg_ne_zero.mpr d.hr.ne'),one_smul]
  simp_rw [hjet,intervalIntegral.integral_smul] at H
  unfold initialErrorLp
  calc
    _ = (d.r*t) • (-((-d.r) • (∫ s in 0..t, meanLp d x s))) := by rw [H]; module
    _ = _ := by module

theorem initialErrorLp_norm_le (hsmall : d.r^2*d.ell ≤ 1/2) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    ‖initialErrorLp d x t‖ ≤ d.r^2*t^2*replyBudget d x := by
  have hi : ‖∫ s in 0..t, meanLp d x s‖ ≤ t*replyBudget d x := by
    have H := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := t) (f := meanLp d x) (fun s hs =>
      meanLp_norm_le d x hsmall (by
        rw [uIoc_of_le ht.1] at hs
        exact ⟨hs.1.le,hs.2.trans ht.2⟩))
    simpa only [sub_zero,abs_of_nonneg ht.1,mul_comm] using H
  rw [initialErrorLp_integral d x ht,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (sq_nonneg _) ht.1)]
  calc
    _ ≤ (d.r^2*t)*(t*replyBudget d x) := mul_le_mul_of_nonneg_left hi (by positivity [ht.1])
    _ = _ := by ring

def rowResidualLp (M : IntervalMesh 0 d.b) (m : ℕ) (t : ℝ) : Lp E 2 γ :=
  initialErrorLp d x t - (d.r^2*t) •
    (∑ j : M.Source m, M.row m 0 t j • meanLp d x (M.location m j))

theorem rowResidualLp_norm_le (hsmall : d.r^2*d.ell ≤ 1/2)
    (M : IntervalMesh 0 d.b) (m : ℕ) (hm : 1 ≤ m) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    ‖rowResidualLp d x M m t‖ ≤
      d.r^2*t * AffineResidual.cellBudget M m (fun _ => derivativeBudget d m) := by
  unfold rowResidualLp
  rw [initialErrorLp_integral d x ht,← smul_sub,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (sq_nonneg _) ht.1)]
  exact mul_le_mul_of_nonneg_left (meanLp_row_defect d x hsmall M m hm ht)
    (mul_nonneg (sq_nonneg _) ht.1)

theorem seedJet_zero_source {t : ℝ} (ht : t ∈ Icc 0 d.b) (z : E) :
    seedJet d x 0 t z = SamplingFlowLp.sourcePath d.hF d.hell d.hlo d.hup x d.hr d.hb d.hb1 t z := by
  rw [seedJet,jet_zero,jointPath_snd_eq_source d x z ht]
  rfl

theorem seedJet_zero_initial (z : E) : seedJet d x 0 0 z = z := by
  rw [seedJet_zero_source d x ⟨le_rfl,d.hb⟩]
  simp only [SamplingFlowLp.sourcePath,SamplingFlowLp.sourceTime_eq d.hb ⟨le_rfl,d.hb⟩]
  exact Conditional.convexProbabilityFlow_initial d.hF d.hell d.hlo d.hup x d.hr d.hb (by norm_num) d.hb1 _ z

theorem initialErrorLp_ae {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    (initialErrorLp d x t : E → E) =ᵐ[γ]
      (fun z => (d.r*t) • (z-SamplingFlowLp.sourcePath d.hF d.hell d.hlo d.hup x d.hr d.hb d.hb1 t z)) := by
  filter_upwards [Lp.coeFn_smul (d.r*t) (jetLp d x 0 0-jetLp d x 0 t),
    Lp.coeFn_sub (jetLp d x 0 0) (jetLp d x 0 t),
    (seedJet_memLp d x 0 0).coeFn_toLp,(seedJet_memLp d x 0 t).coeFn_toLp]
      with z hs hsub hzero htime
  simp only [initialErrorLp,jetLp] at *
  rw [hs,Pi.smul_apply,hsub,Pi.sub_apply,hzero,htime,
    seedJet_zero_initial d x z,seedJet_zero_source d x ht z]

theorem rowResidualLp_ae (M : IntervalMesh 0 d.b) (m : ℕ) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    (rowResidualLp d x M m t : E → E) =ᵐ[γ]
      (fun z => (d.r*t) • (z-SamplingFlowLp.sourcePath d.hF d.hell d.hlo d.hup x d.hr d.hb d.hb1 t z) -
        (d.r^2*t) • ∑ j : M.Source m, M.row m 0 t j • sourceReply d x (M.location m j) z) := by
  have hm (j : M.Source m) : (meanLp d x (M.location m j) : E → E) =ᵐ[γ]
      sourceReply d x (M.location m j) := by
    have htj := M.location_mem_interval m j
    rw [meanLp_eq_toLp d x ⟨htj.1.le,htj.2.le⟩]
    exact (sourceReply_memLp d x _).coeFn_toLp
  filter_upwards [Lp.coeFn_sub (initialErrorLp d x t)
      ((d.r^2*t) • ∑ j : M.Source m, M.row m 0 t j • meanLp d x (M.location m j)),
    Lp.coeFn_smul (d.r^2*t) (∑ j : M.Source m, M.row m 0 t j • meanLp d x (M.location m j)),
    AffineResidual.coeFn_weighted_sum (M.row m 0 t) (fun j => meanLp d x (M.location m j)),
    initialErrorLp_ae d x ht,ae_all_iff.2 hm] with z hsub hs hsum hi hmz
  dsimp only [rowResidualLp]
  rw [hsub,Pi.sub_apply,hi,hs,Pi.smul_apply,hsum]
  simp_rw [hmz]

private theorem norm_of_projection {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (seed : Ω → E) (hp : MeasurePreserving seed ν γ) (v : Lp E 2 γ)
    (f : Ω → E) (he : f =ᵐ[ν] (fun sample => v (seed sample))) :
    ∃ hf : MemLp f 2 ν, ‖hf.toLp f‖ = ‖v‖ := by
  let w := Lp.compMeasurePreserving seed hp v
  have hew : f =ᵐ[ν] (w : Ω → E) := he.trans (Lp.coeFn_compMeasurePreserving v hp).symm
  have hf : MemLp f 2 ν := (Lp.memLp w).ae_eq hew.symm
  refine ⟨hf,?_⟩
  rw [AffineResidual.toLp_eq_of_ae hf hew]
  exact Lp.norm_compMeasurePreserving v hp

def finalErrorLp (M : IntervalMesh 0 d.b) (m : ℕ) : Lp E 2 γ :=
  (d.r*d.b^2)⁻¹ • rowResidualLp d x M m d.b

theorem finalErrorLp_norm_le (hsmall : d.r^2*d.ell ≤ 1/2) (hb : 0 < d.b)
    (M : IntervalMesh 0 d.b) (m : ℕ) (hm : 1 ≤ m) :
    ‖finalErrorLp d x M m‖ ≤
      (d.r/d.b) * AffineResidual.cellBudget M m (fun _ => derivativeBudget d m) := by
  unfold finalErrorLp
  rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (mul_pos d.hr (sq_pos_of_pos hb))]
  have H := mul_le_mul_of_nonneg_left (rowResidualLp_norm_le d x hsmall M m hm ⟨d.hb,le_rfl⟩)
    (inv_nonneg.mpr (mul_nonneg d.hr.le (sq_nonneg d.b)))
  refine H.trans_eq ?_
  field_simp [d.hr.ne',hb.ne']

theorem finalErrorLp_ae (M : IntervalMesh 0 d.b) (m : ℕ) :
    (finalErrorLp d x M m : E → E) =ᵐ[γ]
      (fun z => (d.r*d.b^2)⁻¹ •
        ((d.r*d.b) • (z-SamplingFlowLp.sourcePath d.hF d.hell d.hlo d.hup x d.hr d.hb d.hb1 d.b z) -
          (d.r^2*d.b) • ∑ j : M.Source m, M.row m 0 d.b j • sourceReply d x (M.location m j) z)) := by
  filter_upwards [Lp.coeFn_smul (d.r*d.b^2)⁻¹ (rowResidualLp d x M m d.b),
    rowResidualLp_ae d x M m ⟨d.hb,le_rfl⟩] with z hs hr
  dsimp only [finalErrorLp]
  rw [hs,Pi.smul_apply,hr]

theorem meanLp_row_defect_local (hsmall : d.r^2*d.ell ≤ 1/2)
    (M : IntervalMesh 0 d.b) (m : ℕ) (hm : 1 ≤ m) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    ‖(∫ s in 0..t, meanLp d x s) -
      ∑ j : M.Source m, M.row m 0 t j • meanLp d x (M.location m j)‖ ≤
      AffineResidual.cellBudget M m (cellDerivativeBudget d M m) :=
  AffineResidual.intervalRowDefect M m hm 0 t ⟨le_rfl,d.hb⟩ ht
    (meanLp d x) (cellDerivativeBudget d M m) (meanLp_cellRegularity_local d x hsmall M m hm)

theorem rowResidualLp_norm_local (hsmall : d.r^2*d.ell ≤ 1/2)
    (M : IntervalMesh 0 d.b) (m : ℕ) (hm : 1 ≤ m) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    ‖rowResidualLp d x M m t‖ ≤
      d.r^2*t * AffineResidual.cellBudget M m (cellDerivativeBudget d M m) := by
  unfold rowResidualLp
  rw [initialErrorLp_integral d x ht,← smul_sub,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (sq_nonneg _) ht.1)]
  exact mul_le_mul_of_nonneg_left (meanLp_row_defect_local d x hsmall M m hm ht)
    (mul_nonneg (sq_nonneg _) ht.1)

theorem finalErrorLp_norm_local (hsmall : d.r^2*d.ell ≤ 1/2) (hb : 0 < d.b)
    (M : IntervalMesh 0 d.b) (m : ℕ) (hm : 1 ≤ m) :
    ‖finalErrorLp d x M m‖ ≤
      (d.r/d.b) * AffineResidual.cellBudget M m (cellDerivativeBudget d M m) := by
  unfold finalErrorLp
  rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (mul_pos d.hr (sq_pos_of_pos hb))]
  have H := mul_le_mul_of_nonneg_left (rowResidualLp_norm_local d x hsmall M m hm ⟨d.hb,le_rfl⟩)
    (inv_nonneg.mpr (mul_nonneg d.hr.le (sq_nonneg d.b)))
  refine H.trans_eq ?_
  field_simp [d.hr.ne',hb.ne']

section Actual
open PrivateSamplingExecutionSchedule SourceExecutableTables TapeLowering
variable {dimension m n : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
  {F : (Point dimension) → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)
  (hr : 0 < r) (center : Point dimension)

def data (S : SamplingGeometry m) (r : ℝ) {F : (Point dimension) → ℝ} (hF : ContDiff ℝ 2 F)
    {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2) (hr : 0 < r) :
    SamplingCenterLp.Data (Fin dimension) :=
  ⟨F,hF,ell,hell,hlo,hup,r,hr,samplingEnd S.τ,S.samplingEnd_pos.le,S.samplingEnd_lt_one⟩

local notation "δ" => data S r hF hell hlo hup hr
variable {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
  (tape : Ω → FullTape (d := dimension) S e r Ds main final N)
local notation "seed" => (fun sample => (show (Point dimension) from (tape sample).2.1))
local notation "ref" => PrivateSamplingRetainedRms.reference S e r Ds main final N hF hell hlo hup center hr
local notation "rep" => PrivateSamplingRetainedRms.reply S e r Ds main final N hF hell hlo hup center hr
local notation "initErr" => (fun i sample => initial S e r Ds main final N center (tape sample) i -
  (ref i (tape sample) + PrivateSamplingRetainedRms.initialNoise S e r Ds main final N i (tape sample)))

/-- Original C2 convex data, the small physical radius, and the unchanged full
tape law supply a uniform initializer bound on any augmented execution space. -/
theorem initial_norm_bound (hsmall : r^2*ell ≤ 1/2)
    (L : CanonicalTapeLaw.PrimitiveLaws dimension) (hL : L.pointDraw = stdGaussian (Point dimension)) :
    let : MeasurableSpace (FullTape (d := dimension) S e r Ds main final N) :=
      CanonicalTapeMeasurability.tapeSpace dimension _
    ∀ (_htape : MeasurePreserving tape ν
      (CanonicalTapeLaw.tapeLaw L (SamplingExecutable.build S e r Ds main final N).program)) (i : Fin n),
      ∃ hi : MemLp (initErr i : Ω → (Point dimension)) 2 ν,
        ‖hi.toLp (initErr i)‖ ≤ r^2*(samplingEnd S.τ)^2*replyBudget δ center := by
  let : MeasurableSpace (FullTape (d := dimension) S e r Ds main final N) :=
    CanonicalTapeMeasurability.tapeSpace dimension _
  dsimp only
  intro htape i
  have hp : MeasurePreserving seed ν (stdGaussian (Point dimension)) :=
    (PrivateSamplingFlowResidual.position_preserving S e r Ds main final N L hL).comp htape
  let t := S.mesh.location m (e i)
  have ht : t ∈ Icc 0 (δ).b :=
    ⟨(S.mesh.location_mem_interval m (e i)).1.le,(S.mesh.location_mem_interval m (e i)).2.le⟩
  have ha := hp.quasiMeasurePreserving.ae (initialErrorLp_ae δ center ht)
  have he : initErr i =ᵐ[ν] (fun sample => initialErrorLp δ center t (seed sample)) := by
    filter_upwards [ha] with sample hs
    rw [hs]
    simp only [PrivateSamplingExecutionSchedule.initial,PrivateSamplingRetainedRms.initialNoise,
      PrivateSamplingRetainedRms.reference,PrivateConditionalFlowConsumer.nodePhi,
      ConditionalSamplingFlowFields.Phi,data]
    dsimp only [t]
    module
  obtain ⟨hi,hn⟩ := norm_of_projection seed hp (initialErrorLp δ center t) (initErr i) he
  refine ⟨hi,hn.le.trans ((initialErrorLp_norm_le δ center hsmall ht).trans ?_)⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1 ht.2 2) (sq_nonneg r))
    (replyBudget_nonneg δ center)

local notation "resErr" => SharedLayerRms.residual
  (fun j sample => center+(r*S.mesh.location m (e j)) • seed sample)
  (samplingMatrix S e r) (fun j sample => rep j (tape sample)) (fun j sample => ref j (tape sample))

/-- The complete original tape, including all unused future coordinates,
projects the literal sampling row residual to its proved Gaussian L2 class. -/
theorem residual_norm_bound (hsmall : r^2*ell ≤ 1/2) (hm : 1 ≤ m)
    (L : CanonicalTapeLaw.PrimitiveLaws dimension) (hL : L.pointDraw = stdGaussian (Point dimension)) :
    let : MeasurableSpace (FullTape (d := dimension) S e r Ds main final N) :=
      CanonicalTapeMeasurability.tapeSpace dimension _
    ∀ (_htape : MeasurePreserving tape ν
      (CanonicalTapeLaw.tapeLaw L (SamplingExecutable.build S e r Ds main final N).program)) (i : Fin n),
      ∃ hi : MemLp (resErr i : Ω → (Point dimension)) 2 ν,
        ‖hi.toLp (resErr i)‖ ≤ r^2*(samplingEnd S.τ) *
          AffineResidual.cellBudget S.mesh m (cellDerivativeBudget δ S.mesh m) := by
  let : MeasurableSpace (FullTape (d := dimension) S e r Ds main final N) :=
    CanonicalTapeMeasurability.tapeSpace dimension _
  dsimp only
  intro htape i
  have hp : MeasurePreserving seed ν (stdGaussian (Point dimension)) :=
    (PrivateSamplingFlowResidual.position_preserving S e r Ds main final N L hL).comp htape
  let t := S.mesh.location m (e i)
  have ht : t ∈ Icc 0 (δ).b :=
    ⟨(S.mesh.location_mem_interval m (e i)).1.le,(S.mesh.location_mem_interval m (e i)).2.le⟩
  have ha := hp.quasiMeasurePreserving.ae (rowResidualLp_ae δ center S.mesh m ht)
  have he : resErr i =ᵐ[ν] (fun sample => rowResidualLp δ center S.mesh m t (seed sample)) := by
    filter_upwards [ha] with sample hs
    rw [hs]
    have hmatrix : (∑ j, samplingMatrix S e r i j • rep j (tape sample)) =
        (-(r*t)*r) • (∑ j, S.row t (e j) • rep j (tape sample)) := by
      simp only [samplingMatrix,t,Finset.smul_sum,smul_smul]
    have hsum : (∑ j, S.row t (e j) • rep j (tape sample)) =
        ∑ j : S.mesh.Source m, S.mesh.row m 0 t j • sourceReply δ center (S.mesh.location m j) (seed sample) := by
      simpa only [SamplingGeometry.row,sourceReply,data,PrivateSamplingRetainedRms.reply,
        PrivateConditionalFlowConsumer.nodeReply,ConditionalSamplingFlowFields.reply] using
        e.sum_comp (fun j => S.mesh.row m 0 t j • sourceReply δ center (S.mesh.location m j) (seed sample))
    dsimp only [SharedLayerRms.residual]
    rw [hmatrix,hsum]
    simp only [PrivateSamplingRetainedRms.reference,PrivateConditionalFlowConsumer.nodePhi,
      ConditionalSamplingFlowFields.Phi,data]
    dsimp only [t]
    module
  obtain ⟨hi,hn⟩ := norm_of_projection seed hp (rowResidualLp δ center S.mesh m t) (resErr i) he
  refine ⟨hi,hn.le.trans ((rowResidualLp_norm_local δ center hsmall S.mesh m hm ht).trans ?_)⟩
  have hB : 0 ≤ AffineResidual.cellBudget S.mesh m (cellDerivativeBudget δ S.mesh m) := by
    unfold AffineResidual.cellBudget
    exact Finset.sum_nonneg (fun j _ => div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (S.mesh.length_pos j).le _))
        (cellDerivativeBudget_nonneg δ S.mesh m j)) (Nat.cast_nonneg _))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht.2 (sq_nonneg r)) hB

local notation "endpoint" => (fun sample => SamplingFlowLp.sourcePath hF hell hlo hup center hr
  S.samplingEnd_pos.le S.samplingEnd_lt_one (samplingEnd S.τ) (seed sample))
local notation "finalErr" => (fun sample => (samplingEnd S.τ)⁻¹ • seed sample +
  (∑ j, samplingFinalWeight S e r j • rep j (tape sample)) - (samplingEnd S.τ)⁻¹ • endpoint sample)

omit [MeasurableSpace Ω] in
/-- The exact final affine reference part joins the endpoint readout with
the physical output factor r/rhoEnd and the proved source final-row budget. -/
theorem final_defect_eq (sample : Ω) :
    finalErr sample = (r/samplingEnd S.τ) •
      ((∫ s in 0..samplingEnd S.τ, PrivateSamplingFlowResidual.curve S e r Ds main final N
          hF hell hlo hup center hr (tape sample) s) -
        ∑ j, S.row (samplingEnd S.τ) (e j) • rep j (tape sample)) := by
  have hy := AffineFlowIdentities.sampling_source_flowEquation hF hell hlo hup center hr S
    (seed sample) (samplingEnd S.τ) ⟨S.samplingEnd_pos.le,le_rfl⟩
  change PrivateSamplingFlowResidual.path S e r Ds main final N hF hell hlo hup center hr
      (tape sample) (samplingEnd S.τ) = seed sample - r •
      (∫ s in 0..samplingEnd S.τ, PrivateSamplingFlowResidual.curve S e r Ds main final N
        hF hell hlo hup center hr (tape sample) s) at hy
  have hpath : endpoint sample = PrivateSamplingFlowResidual.path S e r Ds main final N
      hF hell hlo hup center hr (tape sample) (samplingEnd S.τ) := by
    simp only [SamplingFlowLp.sourcePath,
      SamplingFlowLp.sourceTime_eq S.samplingEnd_pos.le ⟨S.samplingEnd_pos.le,le_rfl⟩,
      PrivateSamplingFlowResidual.path]
  have hw : (∑ j, samplingFinalWeight S e r j • rep j (tape sample)) =
      (-(r/samplingEnd S.τ)) • ∑ j, S.row (samplingEnd S.τ) (e j) • rep j (tape sample) := by
    simp only [samplingFinalWeight,Finset.smul_sum,smul_smul]
  dsimp only at hpath hy hw ⊢
  rw [hpath,hy,hw]
  simp only [div_eq_mul_inv,smul_sub,smul_smul]
  module

theorem final_norm_bound (hsmall : r^2*ell ≤ 1/2) (hm : 1 ≤ m)
    (L : CanonicalTapeLaw.PrimitiveLaws dimension) (hL : L.pointDraw = stdGaussian (Point dimension)) :
    let : MeasurableSpace (FullTape (d := dimension) S e r Ds main final N) :=
      CanonicalTapeMeasurability.tapeSpace dimension _
    ∀ (_htape : MeasurePreserving tape ν
      (CanonicalTapeLaw.tapeLaw L (SamplingExecutable.build S e r Ds main final N).program)),
      ∃ hi : MemLp (finalErr : Ω → Point dimension) 2 ν,
        ‖hi.toLp finalErr‖ ≤ (r/samplingEnd S.τ) *
          AffineResidual.cellBudget S.mesh m (cellDerivativeBudget δ S.mesh m) := by
  let : MeasurableSpace (FullTape (d := dimension) S e r Ds main final N) :=
    CanonicalTapeMeasurability.tapeSpace dimension _
  dsimp only
  intro htape
  have hp : MeasurePreserving seed ν (stdGaussian (Point dimension)) :=
    (PrivateSamplingFlowResidual.position_preserving S e r Ds main final N L hL).comp htape
  have ha := hp.quasiMeasurePreserving.ae (finalErrorLp_ae δ center S.mesh m)
  have he : finalErr =ᵐ[ν] (fun sample => finalErrorLp δ center S.mesh m (seed sample)) := by
    filter_upwards [ha] with sample hs
    rw [hs]
    have hsum : (∑ j, S.row (samplingEnd S.τ) (e j) • rep j (tape sample)) =
        ∑ j : S.mesh.Source m, S.mesh.row m 0 (samplingEnd S.τ) j •
          sourceReply δ center (S.mesh.location m j) (seed sample) := by
      simpa only [SamplingGeometry.row,sourceReply,data,PrivateSamplingRetainedRms.reply,
        PrivateConditionalFlowConsumer.nodeReply,ConditionalSamplingFlowFields.reply] using
        e.sum_comp (fun j => S.mesh.row m 0 (samplingEnd S.τ) j • sourceReply δ center (S.mesh.location m j) (seed sample))
    have hw : (∑ j, samplingFinalWeight S e r j • rep j (tape sample)) =
        (-(r/samplingEnd S.τ)) • ∑ j : S.mesh.Source m, S.mesh.row m 0 (samplingEnd S.τ) j •
          sourceReply δ center (S.mesh.location m j) (seed sample) := by
      rw [← hsum]
      simp only [samplingFinalWeight,Finset.smul_sum,smul_smul]
    have h1 : (r*(samplingEnd S.τ)^2)⁻¹*(r*samplingEnd S.τ) = (samplingEnd S.τ)⁻¹ := by
      field_simp [hr.ne',S.samplingEnd_pos.ne']
    have h2 : (r*(samplingEnd S.τ)^2)⁻¹*(r^2*samplingEnd S.τ) = r/samplingEnd S.τ := by
      field_simp [hr.ne',S.samplingEnd_pos.ne']
    rw [hw]
    simp only [data,smul_sub,smul_smul,h1,h2]
    module
  obtain ⟨hi,hn⟩ := norm_of_projection seed hp (finalErrorLp δ center S.mesh m) finalErr he
  exact ⟨hi,hn.le.trans (finalErrorLp_norm_local δ center hsmall S.samplingEnd_pos S.mesh m hm)⟩

theorem initial_node_norm_bound (hsmall : r^2*ell ≤ 1/2)
    (L : CanonicalTapeLaw.PrimitiveLaws dimension) (hL : L.pointDraw = stdGaussian (Point dimension)) :
    let : MeasurableSpace (FullTape (d := dimension) S e r Ds main final N) :=
      CanonicalTapeMeasurability.tapeSpace dimension _
    ∀ (_htape : MeasurePreserving tape ν
      (CanonicalTapeLaw.tapeLaw L (SamplingExecutable.build S e r Ds main final N).program)),
      ∃ hi : ∀ i, MemLp (initErr i : Ω → Point dimension) 2 ν,
        Collocation.rawNodeErrorNorm ν initErr hi ≤
          r^2*(samplingEnd S.τ)^2*replyBudget δ center := by
  let : MeasurableSpace (FullTape (d := dimension) S e r Ds main final N) :=
    CanonicalTapeMeasurability.tapeSpace dimension _
  dsimp only
  intro htape
  choose hi hB using initial_norm_bound (S := S) (e := e) (r := r) (Ds := Ds)
    (main := main) (final := final) (N := N) (hF := hF) (hell := hell) (hlo := hlo) (hup := hup)
    (hr := hr) (center := center) (ν := ν) (tape := tape) hsmall L hL htape
  refine ⟨hi,?_⟩
  change ‖fun i => (hi i).toLp (initErr i)‖ ≤ _
  exact (pi_norm_le_iff_of_nonneg
    (mul_nonneg (mul_nonneg (sq_nonneg r) (sq_nonneg _)) (replyBudget_nonneg δ center))).2 hB

theorem residual_bounds (hsmall : r^2*ell ≤ 1/2) (hm : 1 ≤ m)
    (L : CanonicalTapeLaw.PrimitiveLaws dimension) (hL : L.pointDraw = stdGaussian (Point dimension)) :
    let : MeasurableSpace (FullTape (d := dimension) S e r Ds main final N) :=
      CanonicalTapeMeasurability.tapeSpace dimension _
    ∀ (_htape : MeasurePreserving tape ν
      (CanonicalTapeLaw.tapeLaw L (SamplingExecutable.build S e r Ds main final N).program)),
      ∃ hi : ∀ i, MemLp (resErr i : Ω → Point dimension) 2 ν,
        ∀ i, ‖(hi i).toLp (resErr i)‖ ≤ r^2*(samplingEnd S.τ) *
          AffineResidual.cellBudget S.mesh m (cellDerivativeBudget δ S.mesh m) := by
  let : MeasurableSpace (FullTape (d := dimension) S e r Ds main final N) :=
    CanonicalTapeMeasurability.tapeSpace dimension _
  dsimp only
  intro htape
  choose hi hB using residual_norm_bound (S := S) (e := e) (r := r) (Ds := Ds)
    (main := main) (final := final) (N := N) (hF := hF) (hell := hell) (hlo := hlo) (hup := hup)
    (hr := hr) (center := center) (ν := ν) (tape := tape) hsmall hm L hL htape
  exact ⟨hi,hB⟩

end Actual
end AcceleratedLogConcave.Oracle.PrivateSamplingOriginalBounds
