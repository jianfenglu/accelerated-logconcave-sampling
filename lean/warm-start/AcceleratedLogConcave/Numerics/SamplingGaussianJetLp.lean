import AcceleratedLogConcave.Numerics.SmoothConditionalCell
import AcceleratedLogConcave.Numerics.AffineQuadrature

/-! Strong L2 jets of the actual fixed-center Gaussian-start sampling flow.
All moments, derivative ladders and material budgets come from original C2
convex/Hessian data. The Gaussian input is kept at probability time zero. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff Topology
namespace AcceleratedLogConcave.Numerics.SamplingGaussianJetLp
open ConditionalSmoothing Analysis.PositiveVarianceSlab
variable {D : ℕ} (d : SamplingCenterLp.Data (Fin D)) (x : EuclideanSpace ℝ (Fin D))
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "μ" => stdGaussian E

theorem input_polynomial_memLp (N : ℕ) :
    MemLp (fun z : E => (1+‖(x,z)‖)^N) 2 μ := by
  have hm := Analysis.PolynomialLp.memLp_two_one_add_norm_pow N
    (show Integrable (fun z : E => ‖z‖^(2*N)) μ from
      (IsGaussian.memLp_id μ ((2*N : ℕ) : ENNReal) (by finiteness)).integrable_norm_pow')
  apply (hm.const_mul ((1+‖x‖)^N)).mono' (by fun_prop)
  filter_upwards with z
  simp only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (by positivity : 0 ≤ 1+‖(x,z)‖) N)]
  calc
    _ ≤ ((1+‖x‖)*(1+‖z‖))^N := by
      apply pow_le_pow_left₀ (by positivity)
      have hh : ‖(x,z)‖ ≤ ‖x‖+‖z‖ := by
        rw [Prod.norm_def]
        exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
      nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg z)]
    _ = _ := mul_pow _ _ _

def seedJet (k : ℕ) (t : ℝ) (z : E) : E := (jet d k t (x,z)).2

theorem continuous_seedJet (k : ℕ) : Continuous (Function.uncurry (seedJet d x k)) :=
  ((continuous_jet d k).comp (continuous_fst.prodMk
    (continuous_const.prodMk continuous_snd))).snd

theorem seedJet_envelope (k : ℕ) :
    ∃ B : E → ℝ, MemLp B 2 μ ∧ ∀ t z, ‖seedJet d x k t z‖ ≤ B z := by
  obtain ⟨C,_hC,N,h⟩ := exists_jet_polynomial_bound d k
  exact ⟨fun z => C*(1+‖(x,z)‖)^N,(input_polynomial_memLp x N).const_mul C,
    fun t z => (norm_snd_le _).trans (h t (x,z))⟩

theorem seedJet_memLp (k : ℕ) (t : ℝ) : MemLp (seedJet d x k t) 2 μ := by
  obtain ⟨B,hB,h⟩ := seedJet_envelope d x k
  exact hB.mono' ((continuous_seedJet d x k).comp
    (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall (h t))

def jetLp (k : ℕ) (t : ℝ) : Lp E 2 μ := (seedJet_memLp d x k t).toLp (seedJet d x k t)

theorem seedJet_deriv (k : ℕ) {t : ℝ} (ht : t ∈ Ioo (left d.b) (right d.b)) (z : E) :
    HasDerivAt (fun u => seedJet d x k u z) (seedJet d x (k+1) t z) t :=
  (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_jet d k ht (x,z))

theorem jetLp_deriv (k : ℕ) {t : ℝ} (ht : t ∈ Ioo (left d.b) (right d.b)) :
    HasDerivAt (jetLp d x k) (jetLp d x (k+1) t) t := by
  obtain ⟨B,hB,hbound⟩ := seedJet_envelope d x (k+1)
  exact Analysis.DominatedLp.hasDerivAt_toLp_of_dominated
    (seedJet d x k) (seedJet d x (k+1)) (continuous_seedJet d x (k+1)) B hB hbound
    (seedJet_memLp d x k) (seedJet_memLp d x (k+1)) (fun _ ht' z => seedJet_deriv d x k ht' z) ht

theorem jetLp_contDiffOn (k n : ℕ) :
    ContDiffOn ℝ n (jetLp d x k) (Ioo (left d.b) (right d.b)) := by
  choose B hB hb using (fun i : ℕ => seedJet_envelope d x i)
  have H := Analysis.DominatedLp.contDiffOn_toLp_of_finite_ladder n
    (fun i => seedJet d x (k+i)) (fun i _ t => seedJet_memLp d x (k+i) t)
    (fun i _ => continuous_seedJet d x (k+i)) (fun i => B (k+i))
    (fun i _ => hB (k+i)) (fun i _ => hb (k+i))
    (fun i _ t ht z => by simpa only [Nat.add_assoc] using seedJet_deriv d x (k+i) ht z)
  unfold jetLp
  simpa only [Nat.add_zero] using H

theorem jetLp_iteratedDeriv (k n : ℕ) {t : ℝ} (ht : t ∈ Ioo (left d.b) (right d.b)) :
    iteratedDeriv n (jetLp d x k) t = jetLp d x (k+n) t := by
  simpa only [Nat.add_zero,Nat.add_assoc] using
    Analysis.iteratedDeriv_eq_of_finite_ladder n (fun i => jetLp d x (k+i)) isOpen_Ioo
      (fun i _ _ ht' => by simpa only [Nat.add_assoc] using jetLp_deriv d x (k+i) ht') ht

theorem jetLp_material_norm (hsmall : d.r^2*d.ell ≤ 1/2) (k : ℕ)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    ‖jetLp d x (k+2) t‖ ≤ (d.ell*d.r^2)*materialOrderFactor D k/(1-t^2)^(k+1) := by
  have hs : ‖jetLp d x (k+2) t‖^2 ≤
      ((d.ell*d.r^2)*materialOrderFactor D k/(1-t^2)^(k+1))^2 := by
    rw [jetLp,Analysis.DominatedLp.norm_sq_toLp]
    exact integral_gaussian_jet_sq_le_material d hsmall k x ht
  have hv : 0 < 1-t^2 := by nlinarith [ht.1,ht.2.trans_lt d.hb1]
  have hnon : 0 ≤ (d.ell*d.r^2)*materialOrderFactor D k/(1-t^2)^(k+1) :=
    div_nonneg (mul_nonneg (mul_nonneg d.hell (sq_nonneg _)) (materialOrderFactor_nonneg _ _))
      (pow_nonneg hv.le _)
  nlinarith [norm_nonneg (jetLp d x (k+2) t)]

theorem jetLp_gauss_cell (hsmall : d.r^2*d.ell ≤ 1/2) (n : ℕ)
    (a delta u v : ℝ) (hdelta : 0 < delta) (hu : u ∈ Icc (0:ℝ) 1) (hv : v ∈ Icc (0:ℝ) 1)
    (hcell : Icc a (a+delta) ⊆ Icc 0 d.b) :
    ‖(∫ t in (a+delta*u)..(a+delta*v), jetLp d x 1 t) -
      ∑ i : Fin (n+1), GaussLegendre.partialRow (n+1) a delta u v (fun _ => 1) i •
        jetLp d x 1 (GaussLegendre.cellNode (n+1) a delta i)‖ ≤
      2*delta^(n+2)*((d.ell*d.r^2)*materialOrderFactor D n/(1-d.b^2)^(n+1))/((n+1).factorial:ℝ) := by
  have hb : 0 < 1-d.b^2 := by nlinarith [d.hb,d.hb1]
  let B := (d.ell*d.r^2)*materialOrderFactor D n/(1-d.b^2)^(n+1)
  have hB0 : 0 ≤ B := div_nonneg
    (mul_nonneg (mul_nonneg d.hell (sq_nonneg _)) (materialOrderFactor_nonneg _ _)) (pow_nonneg hb.le _)
  have hf (t : ℝ) (ht : t ∈ Icc a (a+delta)) : ContDiffAt ℝ (n+1) (jetLp d x 1) t :=
    (jetLp_contDiffOn d x 1 (n+1) t (source_subset d.hb d.hb1 (hcell ht))).contDiffAt
      (isOpen_Ioo.mem_nhds (source_subset d.hb d.hb1 (hcell ht)))
  have hB (t : ℝ) (ht : t ∈ Icc a (a+delta)) : ‖iteratedDeriv (n+1) (jetLp d x 1) t‖ ≤ B := by
    rw [jetLp_iteratedDeriv d x 1 (n+1) (source_subset d.hb d.hb1 (hcell ht))]
    have hi : 1+(n+1)=n+2 := by omega
    rw [hi]
    refine (jetLp_material_norm d x hsmall n (hcell ht)).trans ?_
    have hden : (1-d.b^2)^(n+1) ≤ (1-t^2)^(n+1) := pow_le_pow_left₀ hb.le (by nlinarith [(hcell ht).1,(hcell ht).2]) _
    exact div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg d.hell (sq_nonneg _)) (materialOrderFactor_nonneg _ _)) (pow_pos hb _) hden
  have H := AffineResidual.norm_partialRow_defect_le (n+1) (by omega) a delta u v hdelta hu hv
    (fun _ => 1) intervalIntegrable_const (fun _ _ => by norm_num) (jetLp d x 1) B hB0 hf hB
  simpa only [one_smul,Nat.add_assoc] using H

def sourceReply (t : ℝ) (z : E) : E :=
  SamplingFlowLp.centeredReply d.hF d.hell d.hlo d.hup x d.hr d.hb d.hb1 t z +
    Gibbs.primitiveMean d.F x d.r

theorem sourceReply_memLp (t : ℝ) : MemLp (sourceReply d x t) 2 μ :=
  (SamplingFlowLp.samplingCenteredReply_memLp_two d.hF d.hell d.hlo d.hup x d.hr d.hb d.hb1 t).add
    (memLp_const _)

theorem seedJet_one_source {t : ℝ} (ht : t ∈ Icc 0 d.b) (z : E) :
    seedJet d x 1 t z = (-d.r) • sourceReply d x t z := by
  simp only [seedJet,jet_one,openVelocity,time_eq d ((fixedData d x).source_subset_construction ht)]
  rw [jointPath_fst]
  change (-d.r) • Conditional.conditionalMean d.F x d.r t (jointPath d t (x,z)).2 = _
  rw [jointPath_snd_eq_source d x z ht]
  simp only [sourceReply,SamplingFlowLp.centeredReply_eq_conditionalMean,
    SamplingFlowLp.sourceTime_eq d.hb ht,sub_add_cancel,SamplingCenterLp.path]

def meanLp (t : ℝ) : Lp E 2 μ := (-d.r)⁻¹ • jetLp d x 1 t

theorem meanLp_eq_toLp {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    meanLp d x t = (sourceReply_memLp d x t).toLp (sourceReply d x t) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (-d.r)⁻¹ (jetLp d x 1 t),
    (seedJet_memLp d x 1 t).coeFn_toLp,(sourceReply_memLp d x t).coeFn_toLp]
      with z hs hj hr
  simp only [meanLp,jetLp] at *
  rw [hs,Pi.smul_apply,hj,hr,seedJet_one_source d x ht z,smul_smul]
  simp only [inv_mul_cancel₀ (neg_ne_zero.mpr d.hr.ne'),one_smul]

theorem meanLp_contDiffOn (n : ℕ) :
    ContDiffOn ℝ n (meanLp d x) (Ioo (left d.b) (right d.b)) :=
  (jetLp_contDiffOn d x 1 n).const_smul _

theorem meanLp_iteratedDeriv (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (left d.b) (right d.b)) :
    iteratedDeriv n (meanLp d x) t = (-d.r)⁻¹ • jetLp d x (n+1) t := by
  have H := Analysis.iteratedDeriv_eq_of_finite_ladder n
    (fun i t => (-d.r)⁻¹ • jetLp d x (i+1) t) isOpen_Ioo
    (fun i _ t ht => by
      have hd := (jetLp_deriv d x (i+1) ht).const_smul (-d.r)⁻¹
      have he : ((-d.r)⁻¹ • jetLp d x (i+1) : ℝ → Lp E 2 μ) =
          (fun u => (-d.r)⁻¹ • jetLp d x (i+1) u) := rfl
      rw [he] at hd
      exact hd) ht
  exact H

/-- Literal positive-order derivative budget of the uncentered primitive reply.
Only ell*r remains after conversion from the state jet. -/
def derivativeBudget (m : ℕ) : ℝ :=
  (d.ell*d.r)*materialOrderFactor D (m-1)/(1-d.b^2)^m

theorem derivativeBudget_nonneg (m : ℕ) : 0 ≤ derivativeBudget d m := by
  unfold derivativeBudget
  have hb : 0 < 1-d.b^2 := by nlinarith [d.hb,d.hb1]
  exact div_nonneg (mul_nonneg (mul_nonneg d.hell d.hr.le) (materialOrderFactor_nonneg _ _)) (pow_nonneg hb.le _)

theorem meanLp_derivative_le (hsmall : d.r^2*d.ell ≤ 1/2) (m : ℕ) (hm : 1 ≤ m)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    ‖iteratedDeriv m (meanLp d x) t‖ ≤ derivativeBudget d m := by
  rw [meanLp_iteratedDeriv d x m (source_subset d.hb d.hb1 ht),
    norm_smul,Real.norm_eq_abs,abs_inv,abs_neg,abs_of_pos d.hr]
  have hj := jetLp_material_norm d x hsmall (m-1) ht
  have hi : m-1+2=m+1 := by omega
  rw [hi,Nat.sub_add_cancel hm] at hj
  have H := mul_le_mul_of_nonneg_left hj (inv_nonneg.mpr d.hr.le)
  have he : d.r⁻¹*((d.ell*d.r^2)*materialOrderFactor D (m-1)/(1-t^2)^m) =
      (d.ell*d.r)*materialOrderFactor D (m-1)/(1-t^2)^m := by field_simp [d.hr.ne']
  rw [he] at H
  refine H.trans ?_
  have hb : 0 < 1-d.b^2 := by nlinarith [d.hb,d.hb1]
  exact div_le_div_of_nonneg_left
    (mul_nonneg (mul_nonneg d.hell d.hr.le) (materialOrderFactor_nonneg _ _))
    (pow_pos hb _) (pow_le_pow_left₀ hb.le (by nlinarith [ht.1,ht.2]) _)

theorem meanLp_cellRegularity (hsmall : d.r^2*d.ell ≤ 1/2)
    (M : AffineGraph.IntervalMesh 0 d.b) (m : ℕ) (hm : 1 ≤ m) :
    AffineResidual.CellRegularity M m (meanLp d x) (fun _ => derivativeBudget d m) := by
  refine ⟨fun _ => derivativeBudget_nonneg d m,?_,?_⟩
  · intro c t ht
    have hs : t ∈ Icc 0 d.b := ⟨(M.lo_le_left c).trans ht.1,ht.2.trans (M.right_le_hi c)⟩
    exact (meanLp_contDiffOn d x m t (source_subset d.hb d.hb1 hs)).contDiffAt
      (isOpen_Ioo.mem_nhds (source_subset d.hb d.hb1 hs))
  · intro c t ht
    exact meanLp_derivative_le d x hsmall m hm
      ⟨(M.lo_le_left c).trans ht.1,ht.2.trans (M.right_le_hi c)⟩

theorem meanLp_derivative_le_at (hsmall : d.r^2*d.ell ≤ 1/2) (m : ℕ) (hm : 1 ≤ m)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    ‖iteratedDeriv m (meanLp d x) t‖ ≤
      (d.ell*d.r)*materialOrderFactor D (m-1)/(1-t^2)^m := by
  rw [meanLp_iteratedDeriv d x m (source_subset d.hb d.hb1 ht),
    norm_smul,Real.norm_eq_abs,abs_inv,abs_neg,abs_of_pos d.hr]
  have hj := jetLp_material_norm d x hsmall (m-1) ht
  have hi : m-1+2=m+1 := by omega
  rw [hi,Nat.sub_add_cancel hm] at hj
  have H := mul_le_mul_of_nonneg_left hj (inv_nonneg.mpr d.hr.le)
  convert H using 1
  field_simp [d.hr.ne']

/-- Cell-local variance denominator: prescribed adaptive cell lengths retain
their cancellation against this actual derivative budget. -/
def cellDerivativeBudget (M : AffineGraph.IntervalMesh 0 d.b) (m : ℕ) (c : M.Cell) : ℝ :=
  (d.ell*d.r)*materialOrderFactor D (m-1)/(1-(M.right c)^2)^m

theorem cell_right_variance_pos (M : AffineGraph.IntervalMesh 0 d.b) (c : M.Cell) :
    0 < 1-(M.right c)^2 := by
  have h0 := M.lo_le_left c
  have hl := M.length_pos c
  have hb := M.right_le_hi c
  dsimp only [AffineGraph.IntervalMesh.length] at hl
  nlinarith [d.hb1]

theorem cellDerivativeBudget_nonneg (M : AffineGraph.IntervalMesh 0 d.b) (m : ℕ) (c : M.Cell) :
    0 ≤ cellDerivativeBudget d M m c :=
  div_nonneg (mul_nonneg (mul_nonneg d.hell d.hr.le) (materialOrderFactor_nonneg _ _))
    (pow_nonneg (cell_right_variance_pos d M c).le _)

theorem meanLp_cellRegularity_local (hsmall : d.r^2*d.ell ≤ 1/2)
    (M : AffineGraph.IntervalMesh 0 d.b) (m : ℕ) (hm : 1 ≤ m) :
    AffineResidual.CellRegularity M m (meanLp d x) (cellDerivativeBudget d M m) := by
  refine ⟨cellDerivativeBudget_nonneg d M m,?_,?_⟩
  · intro c t ht
    have hs : t ∈ Icc 0 d.b := ⟨(M.lo_le_left c).trans ht.1,ht.2.trans (M.right_le_hi c)⟩
    exact (meanLp_contDiffOn d x m t (source_subset d.hb d.hb1 hs)).contDiffAt
      (isOpen_Ioo.mem_nhds (source_subset d.hb d.hb1 hs))
  · intro c t ht
    have hs : t ∈ Icc 0 d.b := ⟨(M.lo_le_left c).trans ht.1,ht.2.trans (M.right_le_hi c)⟩
    refine (meanLp_derivative_le_at d x hsmall m hm hs).trans ?_
    exact div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg d.hell d.hr.le) (materialOrderFactor_nonneg _ _))
      (pow_pos (cell_right_variance_pos d M c) _)
      (pow_le_pow_left₀ (cell_right_variance_pos d M c).le (by nlinarith [hs.1,ht.2]) _)

end AcceleratedLogConcave.Numerics.SamplingGaussianJetLp
