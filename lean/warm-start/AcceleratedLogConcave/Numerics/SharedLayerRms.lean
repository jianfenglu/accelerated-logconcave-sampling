import AcceleratedLogConcave.Numerics.AffineResidualRms

/-! Difference-only RMS propagation for literal shared noisy affine layers.
The evaluator may depend on the entire sample. Fixed-tape Lipschitz stability
and measurability of its difference are explicit premises. Child errors are
evaluated at the benchmark, never at the actual center. No Gaussian law,
independence, absolute-state moment or executable stability is asserted. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.SharedLayerRms
variable {ι Ω E : Type*} [Fintype ι] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The literal numerical row of NoisyLayer.noisyValues_layerTable. -/
def layer (b : ι → E) (A C : ι → ι → ℝ) (Q Z : ι → E) (i : ι) : E :=
  b i + ∑ j, A i j • Q j + ∑ j, C i j • Z j

/-- The next comparison state is X* plus the shared reference noise. -/
def benchmarkLayer (xStar : ι → E) (A C : ι → ι → ℝ) (σ : ℝ)
    (G Z : ι → E) (i : ι) : E :=
  xStar i + ∑ j, A i j • (σ • G j) + ∑ j, C i j • Z j

/-- Cancellation is pathwise for arbitrary C, Z and sigma, without moment premises. -/
theorem layer_sub_benchmark (b xStar : ι → E) (A C : ι → ι → ℝ)
    (Q Qbenchmark U G Z : ι → E) (σ : ℝ) (i : ι) :
    layer b A C Q Z i - benchmarkLayer xStar A C σ G Z i =
      (b i + ∑ j, A i j • U j - xStar i) +
        (∑ j, A i j • (Q j - Qbenchmark j)) +
        ∑ j, A i j • (Qbenchmark j - U j - σ • G j) := by
  simp only [layer,benchmarkLayer,smul_sub,Finset.sum_sub_distrib]
  abel

def iterate (b : ι → Ω → E) (A C : ι → ι → ℝ)
    (M : ℕ → ι → Ω → E → E) (Z : ℕ → ι → Ω → E) (initial : ι → Ω → E) :
    ℕ → ι → Ω → E
  | 0 => initial
  | k+1 => fun i ω => layer (fun j => b j ω) A C
      (fun j => M k j ω (iterate b A C M Z initial k j ω)) (fun j => Z k j ω) i

def benchmark (xStar : ι → Ω → E) (A C : ι → ι → ℝ) (σ : ℝ)
    (G Z : ℕ → ι → Ω → E) (nu0 : ι → Ω → E) : ℕ → ι → Ω → E
  | 0 => fun i ω => xStar i ω + nu0 i ω
  | k+1 => fun i ω => benchmarkLayer (fun j => xStar j ω) A C σ
      (fun j => G k j ω) (fun j => Z k j ω) i

def residual (b : ι → Ω → E) (A : ι → ι → ℝ) (U xStar : ι → Ω → E)
    (i : ι) (ω : Ω) : E := b i ω + ∑ j, A i j • U j ω - xStar i ω

def childError (M : ℕ → ι → Ω → E → E) (Y : ℕ → ι → Ω → E)
    (U : ι → Ω → E) (σ : ℝ) (G : ℕ → ι → Ω → E) (k : ℕ) (j : ι) (ω : Ω) : E :=
  M k j ω (Y k j ω) - U j ω - σ • G k j ω

/-- Maximum of deterministic row sums of the individual child RMS budgets. -/
def childRowBudget (A : ι → ι → ℝ) (ε : ℕ → ι → ℝ) (k : ℕ) : ℝ :=
  ‖fun i => ∑ j, |A i j| * ε k j‖

omit [NormedSpace ℝ E] in
theorem memLp_fixedTape_sub {μ : Measure Ω} (M : Ω → E → E) (X Y : Ω → E)
    (κ : ℝ≥0) (hM : ∀ ω, LipschitzWith κ (M ω))
    (hmeas : AEStronglyMeasurable (fun ω => M ω (X ω) - M ω (Y ω)) μ)
    (hD : MemLp (fun ω => X ω - Y ω) 2 μ) :
    MemLp (fun ω => M ω (X ω) - M ω (Y ω)) 2 μ :=
  hD.of_le_mul hmeas (Filter.Eventually.of_forall fun ω => (hM ω).norm_sub_le _ _)

omit [NormedSpace ℝ E] in
theorem norm_toLp_fixedTape_sub_le {μ : Measure Ω} (M : Ω → E → E) (X Y : Ω → E)
    (κ : ℝ≥0) (hM : ∀ ω, LipschitzWith κ (M ω))
    (hD : MemLp (fun ω => X ω - Y ω) 2 μ)
    (hH : MemLp (fun ω => M ω (X ω) - M ω (Y ω)) 2 μ) :
    ‖hH.toLp (fun ω => M ω (X ω) - M ω (Y ω))‖ ≤
      (κ : ℝ) * ‖hD.toLp (fun ω => X ω - Y ω)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hH.coeFn_toLp,hD.coeFn_toLp] with ω hHω hDω
  simpa only [hHω,hDω] using (hM ω).norm_sub_le (X ω) (Y ω)

private theorem weighted_toLp_ae {μ : Measure Ω} (w : ι → ℝ) (f : ι → Ω → E)
    (hf : ∀ j, MemLp (f j) 2 μ) :
    (∑ j, w j • (hf j).toLp (f j) : Lp E 2 μ) =ᵐ[μ]
      (fun ω => ∑ j, w j • f j ω) := by
  apply (AffineResidual.coeFn_weighted_sum w (fun j => (hf j).toLp (f j))).trans
  filter_upwards [ae_all_iff.2 (fun j => (hf j).coeFn_toLp)] with ω hω
  simp only [hω]

variable (b xStar U initial nu0 : ι → Ω → E) (A C : ι → ι → ℝ)
  (M : ℕ → ι → Ω → E → E) (G Z : ℕ → ι → Ω → E) (σ : ℝ)
local notation "X" => iterate b A C M Z initial
local notation "Y" => benchmark xStar A C σ G Z nu0
local notation "err" => (fun k i ω => X k i ω - Y k i ω)

omit [MeasurableSpace Ω] in
/-- The actual and benchmark iterates contain literally the same C Z term. -/
theorem iterate_difference (k : ℕ) (i : ι) (ω : Ω) :
    err (k+1) i ω = residual b A U xStar i ω +
      (∑ j, A i j • (M k j ω (X k j ω) - M k j ω (Y k j ω))) +
      ∑ j, A i j • childError M Y U σ G k j ω :=
  layer_sub_benchmark (fun j => b j ω) (fun j => xStar j ω) A C
    (fun j => M k j ω (X k j ω)) (fun j => M k j ω (Y k j ω))
    (fun j => U j ω) (fun j => G k j ω) (fun j => Z k j ω) σ i

/-- Only differences and the explicit residual/benchmark child errors require L2.
The finite node norm is the maximum of individual L2 norms, not L2 of a maximum.
No independence or absolute-state measurability/moment premise is used. -/
theorem iterate_error_bound (μ : Measure Ω) (κ : ℝ≥0) (a R : ℝ)
    (ha : 0 ≤ a) (hR : 0 ≤ R) (ε : ℕ → ι → ℝ)
    (hrow : ∀ i, ∑ j, |A i j| ≤ a)
    (hM : ∀ k j ω, LipschitzWith κ (M k j ω))
    (hmeas : ∀ k j, AEStronglyMeasurable
      (fun ω => M k j ω (X k j ω) - M k j ω (Y k j ω)) μ)
    (hinit : ∀ i, MemLp (fun ω => initial i ω - (xStar i ω + nu0 i ω)) 2 μ)
    (hres : ∀ i, MemLp (residual b A U xStar i) 2 μ)
    (hresBound : ∀ i, ‖(hres i).toLp (residual b A U xStar i)‖ ≤ R)
    (hchild : ∀ k j, MemLp (childError M Y U σ G k j) 2 μ)
    (hchildBound : ∀ k j, ‖(hchild k j).toLp (childError M Y U σ G k j)‖ ≤ ε k j) :
    ∃ herr : ∀ k i, MemLp (err k i) 2 μ,
      ∀ N, Collocation.rawNodeErrorNorm μ (err N) (herr N) ≤
        ((κ : ℝ)*a)^N * Collocation.rawNodeErrorNorm μ (err 0) (herr 0) +
          Collocation.forcingSum ((κ : ℝ)*a) (fun k => R + childRowBudget A ε k) N := by
  classical
  have hdiff (k : ℕ) (hk : ∀ i, MemLp (err k i) 2 μ) (j : ι) :
      MemLp (fun ω => M k j ω (X k j ω) - M k j ω (Y k j ω)) 2 μ :=
    memLp_fixedTape_sub (M k j) (X k j) (Y k j) κ (hM k j) (hmeas k j) (hk j)
  have herr : ∀ k i, MemLp (err k i) 2 μ := by
    intro k
    induction k with
    | zero => exact hinit
    | succ k ih =>
      intro i
      have hd := memLp_finsetSum Finset.univ (fun j _ => (hdiff k ih j).const_smul (A i j))
      have hc := memLp_finsetSum Finset.univ (fun j _ => (hchild k j).const_smul (A i j))
      apply (((hres i).add hd).add hc).ae_eq
      filter_upwards with ω
      simp only [Pi.add_apply,Pi.smul_apply]
      exact (iterate_difference b xStar U initial nu0 A C M G Z σ k i ω).symm
  refine ⟨herr, fun N => ?_⟩
  apply Collocation.nodeL2Norm_error_le μ (fun k i => (herr k i).toLp (err k i))
    ((κ : ℝ)*a) (fun k => R + childRowBudget A ε k) N (mul_nonneg κ.coe_nonneg ha)
    (fun _ _ => add_nonneg hR (norm_nonneg _))
  intro k _ i
  let Δ (j : ι) : Lp E 2 μ := (hdiff k (herr k) j).toLp
    (fun ω => M k j ω (X k j ω) - M k j ω (Y k j ω))
  let H (j : ι) : Lp E 2 μ := (hchild k j).toLp (childError M Y U σ G k j)
  let V : Lp E 2 μ := (hres i).toLp (residual b A U xStar i)
  have hΔ : ‖∑ j, A i j • Δ j‖ ≤
      (κ : ℝ)*a*Collocation.nodeL2Norm μ (fun j => (herr k j).toLp (err k j)) := by
    have hnorm (j : ι) : ‖Δ j‖ ≤
        (κ : ℝ)*‖fun j => (herr k j).toLp (err k j)‖ :=
      (norm_toLp_fixedTape_sub_le (M k j) (X k j) (Y k j) κ (hM k j)
        (herr k j) (hdiff k (herr k) j)).trans
        (mul_le_mul_of_nonneg_left
          (norm_le_pi_norm (fun j => (herr k j).toLp (err k j)) j) κ.coe_nonneg)
    simpa only [Collocation.nodeL2Norm,mul_left_comm a (κ : ℝ),mul_assoc] using
      AffineGraph.norm_sum_smul_le_of_norm_le (A i) Δ (hrow i)
        (mul_nonneg κ.coe_nonneg (norm_nonneg _)) hnorm
  have hH : ‖∑ j, A i j • H j‖ ≤ childRowBudget A ε k := by
    calc
      _ ≤ ∑ j, ‖A i j • H j‖ := norm_sum_le _ _
      _ = ∑ j, |A i j| * ‖H j‖ := by simp only [norm_smul,Real.norm_eq_abs]
      _ ≤ ∑ j, |A i j| * ε k j := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hchildBound k j) (abs_nonneg _)
      _ ≤ ‖fun i => ∑ j, |A i j| * ε k j‖ := (le_abs_self _).trans (by
        simpa only [Real.norm_eq_abs] using
          norm_le_pi_norm (fun i => ∑ j, |A i j| * ε k j) i)
  have hid : (herr (k+1) i).toLp (err (k+1) i) =
      V + (∑ j, A i j • Δ j) + ∑ j, A i j • H j := by
    apply Lp.ext
    have hd := weighted_toLp_ae (A i)
      (fun j ω => M k j ω (X k j ω) - M k j ω (Y k j ω)) (hdiff k (herr k))
    have hc := weighted_toLp_ae (A i) (childError M Y U σ G k) (hchild k)
    filter_upwards [(herr (k+1) i).coeFn_toLp,(hres i).coeFn_toLp,hd,hc,
      Lp.coeFn_add V (∑ j, A i j • Δ j),
      Lp.coeFn_add (V + ∑ j, A i j • Δ j) (∑ j, A i j • H j)] with ω he hv hdω hcω ha hb
    rw [he,hb]
    simp only [Pi.add_apply]
    rw [ha]
    change err (k+1) i ω = V ω + (∑ j, A i j • Δ j) ω + (∑ j, A i j • H j) ω
    rw [show V ω = residual b A U xStar i ω from hv,hdω,hcω]
    exact iterate_difference b xStar U initial nu0 A C M G Z σ k i ω
  rw [hid]
  calc
    _ ≤ ‖V‖ + ‖∑ j, A i j • Δ j‖ + ‖∑ j, A i j • H j‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ R + ((κ : ℝ)*a*Collocation.nodeL2Norm μ (fun j => (herr k j).toLp (err k j))) +
        childRowBudget A ε k := add_le_add (add_le_add (hresBound i) hΔ) hH
    _ = _ := by ring

end AcceleratedLogConcave.Numerics.SharedLayerRms
