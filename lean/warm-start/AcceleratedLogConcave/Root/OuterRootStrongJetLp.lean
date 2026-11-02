import AcceleratedLogConcave.Root.OriginalRootStationaryMoments
import AcceleratedLogConcave.Numerics.SmoothConditional
import AcceleratedLogConcave.Root.OuterRootMaterialProduct
import AcceleratedLogConcave.Analysis.PolynomialLp
import AcceleratedLogConcave.Numerics.AffineQuadrature
import AcceleratedLogConcave.Analysis.FiniteDerivativeLadder

/-! Common-seed L2 lift. Polynomial moments are derived from the
positive-curvature reference law; no numerical jet budget is an input. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory ProbabilityTheory Function
open scoped ContDiff Topology
namespace AcceleratedLogConcave.Root.OuterRootStrongJetLp
open Analysis.Poisson Analysis.PositiveVarianceSlab Numerics Numerics.ConditionalSmoothing
variable {ι : Type*} [Fintype ι]
variable {a b : ℝ} (F : ReferencePoissonFamily (EuclideanSpace ℝ ι) a b)

def seedMeasure : Measure ((EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι)) := (F.law a).prod (stdGaussian (EuclideanSpace ℝ ι))
instance : IsProbabilityMeasure (seedMeasure F) := by
  unfold seedMeasure
  infer_instance

/-- c is the literal inverse sqrt(h) coordinate conversion in the root caller. -/
def input (c : ℝ) (p : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι)) : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι) := (c • p.1,p.2)

theorem input_moment (c : ℝ) (n : ℕ) :
    Integrable (fun p => ‖input c p‖^n) (seedMeasure F) := by
  have hx := OriginalRootStationaryMoments.family_position_moment F
    (show a ∈ Icc a b from ⟨le_rfl,F.ordered⟩) n
  have hz : Integrable (fun z : (EuclideanSpace ℝ ι) => ‖z‖^n) (stdGaussian (EuclideanSpace ℝ ι)) := by
    simpa only [id_eq] using
      (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ ι)) n (by simp)).integrable_norm_pow'
  apply ((((hx.comp_fst (stdGaussian (EuclideanSpace ℝ ι))).const_mul (|c|^n)).add
    (hz.comp_snd (F.law a))).const_mul (2^(n-1))).mono' (by unfold input; fun_prop)
  filter_upwards [] with p
  simp only [Pi.add_apply,Real.norm_eq_abs]
  rw [abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  have hn : ‖input c p‖ ≤ |c| *‖p.1‖+‖p.2‖ := by
    simp only [input,Prod.norm_def,norm_smul,Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _))
      (le_add_of_nonneg_left (mul_nonneg (abs_nonneg _) (norm_nonneg _)))
  calc
    _ ≤ (|c| *‖p.1‖+‖p.2‖)^n := pow_le_pow_left₀ (norm_nonneg _) hn n
    _ ≤ 2^(n-1)*((|c| *‖p.1‖)^n+‖p.2‖^n) :=
      add_pow_le (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (norm_nonneg _) n
    _ = _ := by simp only [mul_pow]

theorem input_polynomial_memLp (c : ℝ) (N : ℕ) :
    MemLp (fun p => (1+‖input c p‖)^N) 2 (seedMeasure F) := by
  have hc : Continuous (input (ι := ι) c) := by unfold input; fun_prop
  have hm : Integrable (fun p : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι) => ‖p‖^(2*N))
      ((seedMeasure F).map (input c)) :=
    (integrable_map_measure (by fun_prop) hc.aemeasurable).mpr (input_moment F c (2*N))
  exact (memLp_map_measure_iff (by fun_prop) hc.aemeasurable).mp
    (Analysis.PolynomialLp.memLp_two_one_add_norm_pow N hm)

variable (d : SamplingCenterLp.Data ι) (c : ℝ)
def seedJet (k : ℕ) (t : ℝ) (p : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι)) : (EuclideanSpace ℝ ι) := (jet d k t (input c p)).2

theorem continuous_seedJet (k : ℕ) : Continuous (uncurry (seedJet d c k)) := by
  have hi : Continuous (input (ι := ι) c) := by unfold input; fun_prop
  exact ((continuous_jet d k).comp
    (continuous_fst.prodMk (hi.comp continuous_snd))).snd

theorem seedJet_envelope (k : ℕ) :
    ∃ B : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι) → ℝ, MemLp B 2 (seedMeasure F) ∧
      ∀ t p, ‖seedJet d c k t p‖ ≤ B p := by
  obtain ⟨C,_hC,N,h⟩ := exists_jet_polynomial_bound d k
  exact ⟨fun p => C*(1+‖input c p‖)^N,
    (input_polynomial_memLp F c N).const_mul C,
    fun t p => (norm_snd_le _).trans (h t (input c p))⟩

theorem seedJet_memLp (k : ℕ) (t : ℝ) :
    MemLp (seedJet d c k t) 2 (seedMeasure F) := by
  obtain ⟨B,hB,h⟩ := seedJet_envelope F d c k
  exact hB.mono' ((continuous_seedJet d c k).comp
    (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall (h t))

def jetLp (k : ℕ) (t : ℝ) : Lp (EuclideanSpace ℝ ι) 2 (seedMeasure F) :=
  (seedJet_memLp F d c k t).toLp (seedJet d c k t)

theorem seedJet_deriv (k : ℕ) {t : ℝ} (ht : t ∈ Ioo (left d.b) (right d.b))
    (p : (EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι)) : HasDerivAt (fun u => seedJet d c k u p)
      (seedJet d c (k+1) t p) t :=
  (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_jet d k ht (input c p))

theorem jetLp_deriv (k : ℕ) {t : ℝ} (ht : t ∈ Ioo (left d.b) (right d.b)) :
    HasDerivAt (jetLp F d c k) (jetLp F d c (k+1) t) t := by
  obtain ⟨B,hB,hbound⟩ := seedJet_envelope F d c (k+1)
  exact Analysis.DominatedLp.hasDerivAt_toLp_of_dominated
    (seedJet d c k) (seedJet d c (k+1)) (continuous_seedJet d c (k+1))
    B hB hbound (seedJet_memLp F d c k) (seedJet_memLp F d c (k+1))
    (fun _ ht' p => seedJet_deriv d c k ht' p) ht

theorem jetLp_contDiffOn (k n : ℕ) :
    ContDiffOn ℝ n (jetLp F d c k) (Ioo (left d.b) (right d.b)) := by
  choose B hB hb using (fun i : ℕ => seedJet_envelope F d c i)
  have H := Analysis.DominatedLp.contDiffOn_toLp_of_finite_ladder n
    (fun i => seedJet d c (k+i)) (fun i _ t => seedJet_memLp F d c (k+i) t)
    (fun i _ => continuous_seedJet d c (k+i)) (fun i => B (k+i))
    (fun i _ => hB (k+i)) (fun i _ => hb (k+i))
    (fun i _ t ht p => by simpa only [Nat.add_assoc] using seedJet_deriv d c (k+i) ht p)
  unfold jetLp
  simpa only [Nat.add_zero] using H

theorem jetLp_iteratedDeriv (k n : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) :
    iteratedDeriv n (jetLp F d c k) t = jetLp F d c (k+n) t := by
  simpa only [Nat.add_zero,Nat.add_assoc] using
    Analysis.iteratedDeriv_eq_of_finite_ladder n (fun i => jetLp F d c (k+i))
      isOpen_Ioo (fun i _ _ ht' => by
        simpa only [Nat.add_assoc] using jetLp_deriv F d c (k+i) ht') ht

/-- Exact scaling of the initial center preserves the product structure; this
is a pushforward identity, not an assumption of independence after transport. -/
theorem input_preserving : MeasurePreserving (input c) (seedMeasure F)
    (((F.law a).map (fun x : (EuclideanSpace ℝ ι) => c • x)).prod (stdGaussian (EuclideanSpace ℝ ι))) := by
  refine ⟨by unfold input; fun_prop, ?_⟩
  symm
  change _ = Measure.map (Prod.map (fun x : EuclideanSpace ℝ ι => c • x) id) ((F.law a).prod (stdGaussian (EuclideanSpace ℝ ι)))
  simpa only [Measure.map_id] using
    Measure.map_prod_map (F.law a) (stdGaussian (EuclideanSpace ℝ ι))
      (show Measurable (fun x : (EuclideanSpace ℝ ι) => c • x) by fun_prop) measurable_id

/-- Actual material L2 norm, with its local radius, curvature and time factors.
The budget is proved from the conditional Gaussian jet theorem. -/
theorem jetLp_material_norm (hsmall : d.r^2*d.ell ≤ 1/2) (k : ℕ)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    ‖jetLp F d c (k+2) t‖ ≤
      (d.ell*d.r^2)*materialOrderFactor (Fintype.card ι) k/(1-t^2)^(k+1) := by
  let mu := (F.law a).map (fun x : (EuclideanSpace ℝ ι) => c • x)
  have : IsProbabilityMeasure mu := by dsimp [mu]; infer_instance
  have hb := OuterRootMaterialProduct.jet_product_integral_sq_le d hsmall mu k ht
  have he : (∫ p, ‖(jet d (k+2) t (input c p)).2‖^2 ∂seedMeasure F) =
      ∫ p, ‖(jet d (k+2) t p).2‖^2 ∂mu.prod (stdGaussian (EuclideanSpace ℝ ι)) := by
    rw [← (input_preserving F c).map_eq]
    symm
    exact integral_map (input_preserving F c).measurable.aemeasurable
      ((((continuous_jet d (k+2)).comp
        (continuous_const.prodMk continuous_id)).snd.norm.pow 2).aestronglyMeasurable)
  have hs : ‖jetLp F d c (k+2) t‖^2 ≤
      ((d.ell*d.r^2)*materialOrderFactor (Fintype.card ι) k/(1-t^2)^(k+1))^2 := by
    rw [jetLp, Analysis.DominatedLp.norm_sq_toLp]
    change (∫ p, ‖(jet d (k+2) t (input c p)).2‖^2 ∂seedMeasure F) ≤ _
    rw [he]
    exact hb
  have ht1 : t < 1 := ht.2.trans_lt d.hb1
  have hv : 0 < 1-t^2 := by nlinarith [ht.1]
  have hnon : 0 ≤ (d.ell*d.r^2)*materialOrderFactor (Fintype.card ι) k /
      (1-t^2)^(k+1) := div_nonneg
    (mul_nonneg (mul_nonneg d.hell (sq_nonneg _)) (materialOrderFactor_nonneg _ _))
    (pow_nonneg hv.le _)
  nlinarith [norm_nonneg (jetLp F d c (k+2) t)]

/-- A literal Gauss-Legendre partial row applied to the actual first state jet.
The derivative budget is discharged, not assumed. Caller still must identify
this cell row with ClockSchedule and convert Jet1=-rF*g into output units. -/
theorem jetLp_gauss_cell (hsmall : d.r^2*d.ell ≤ 1/2) (n : ℕ)
    (x delta u v : ℝ) (hdelta : 0 < delta)
    (hu : u ∈ Icc (0:ℝ) 1) (hv : v ∈ Icc (0:ℝ) 1)
    (hcell : Icc x (x+delta) ⊆ Icc 0 d.b) :
    ‖(∫ t in (x+delta*u)..(x+delta*v), jetLp F d c 1 t) -
      ∑ i : Fin (n+1), GaussLegendre.partialRow (n+1) x delta u v (fun _ => 1) i •
        jetLp F d c 1 (GaussLegendre.cellNode (n+1) x delta i)‖ ≤
      2*delta^(n+2)*((d.ell*d.r^2)*materialOrderFactor (Fintype.card ι) n /
        (1-d.b^2)^(n+1))/((n+1).factorial:ℝ) := by
  have hb : 0 < 1-d.b^2 := by nlinarith [d.hb,d.hb1]
  let D := (d.ell*d.r^2)*materialOrderFactor (Fintype.card ι) n /(1-d.b^2)^(n+1)
  have hD0 : 0 ≤ D := div_nonneg
    (mul_nonneg (mul_nonneg d.hell (sq_nonneg _)) (materialOrderFactor_nonneg _ _))
    (pow_nonneg hb.le _)
  have hf (t : ℝ) (ht : t ∈ Icc x (x+delta)) :
      ContDiffAt ℝ (n+1) (jetLp F d c 1) t :=
    (jetLp_contDiffOn F d c 1 (n+1) t
      (source_subset d.hb d.hb1 (hcell ht))).contDiffAt
      (isOpen_Ioo.mem_nhds (source_subset d.hb d.hb1 (hcell ht)))
  have hD (t : ℝ) (ht : t ∈ Icc x (x+delta)) :
      ‖iteratedDeriv (n+1) (jetLp F d c 1) t‖ ≤ D := by
    rw [jetLp_iteratedDeriv F d c 1 (n+1) (source_subset d.hb d.hb1 (hcell ht))]
    have hindex : 1+(n+1)=n+2 := by omega
    rw [hindex]
    refine (jetLp_material_norm F d c hsmall n (hcell ht)).trans ?_
    have ht0 := (hcell ht).1
    have htb := (hcell ht).2
    have hden : (1-d.b^2)^(n+1) ≤ (1-t^2)^(n+1) :=
      pow_le_pow_left₀ hb.le (by nlinarith) _
    exact div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg d.hell (sq_nonneg _)) (materialOrderFactor_nonneg _ _))
      (pow_pos hb _) hden
  have H := AffineResidual.norm_partialRow_defect_le (n+1) (by omega) x delta u v hdelta hu hv
    (fun _ => 1) (intervalIntegrable_const) (fun _ _ => by norm_num)
    (jetLp F d c 1) D hD0 hf hD
  simpa only [one_smul, Nat.add_assoc] using H

end AcceleratedLogConcave.Root.OuterRootStrongJetLp
