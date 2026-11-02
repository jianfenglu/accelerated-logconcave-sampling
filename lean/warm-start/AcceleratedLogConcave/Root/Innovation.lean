import AcceleratedLogConcave.Root.ConditionalLaw

/-!
# Exact innovation second moment of the retained reference root

The off-diagonal terms are derived from the actual split/independent-child
execution, not postulated. The only remaining variance input in the final bound
is a directional second-moment bound for each exact child. No W12 norm is assumed.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open AcceleratedLogConcave.Conditional
open scoped ENNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AcceleratedLogConcave.Root.RetainedLaw
variable {ι : Type*} [Fintype ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

def childIncrement (d : Data ι m) (i : Fin m) (z : Execution (ι := ι) (m := m)) : E :=
  z.2 i - active d z.1 i

theorem host_preserving (d : Data ι m) :
    MeasurePreserving Prod.fst (averagedJoint d)
      ((stdGaussian E).prod (noiseLaw (ι := ι) (m := m))) := by
  refine ⟨measurable_fst, ?_⟩
  rw [averagedJoint_eq]
  exact Measure.fst_compProd _ _

theorem activeCoordinates_preserving (d : Data ι m) :
    MeasurePreserving (fun z : Execution (ι := ι) (m := m) => active d z.1)
      (averagedJoint d) (noiseLaw (ι := ι) (m := m)) :=
  measurePreserving_snd.comp ((split_preserving d).comp (host_preserving d))

theorem returnedCoordinates_preserving (d : Data ι m) :
    MeasurePreserving (fun z : Execution (ι := ι) (m := m) => z.2)
      (averagedJoint d) (noiseLaw (ι := ι) (m := m)) := by
  have hs : MeasurePreserving (fun z : Execution (ι := ι) (m := m) => (reserve d z.1,z.2))
      (averagedJoint d) ((stdGaussian E).prod (noiseLaw (ι := ι) (m := m))) :=
    ⟨((measurable_reserve d).comp measurable_fst).prodMk measurable_snd, updated_split_law d⟩
  simpa only [Function.comp_def] using
    (measurePreserving_snd (μ := stdGaussian E) (ν := noiseLaw (ι := ι) (m := m))).comp hs

theorem active_memLp (d : Data ι m) (i : Fin m) :
    MemLp (fun z : Execution (ι := ι) (m := m) => active d z.1 i) 2 (averagedJoint d) :=
  IsGaussian.memLp_two_id.comp_measurePreserving
    ((measurePreserving_eval (fun _ : Fin m => stdGaussian E) i).comp (activeCoordinates_preserving d))
theorem returned_memLp (d : Data ι m) (i : Fin m) :
    MemLp (fun z : Execution (ι := ι) (m := m) => z.2 i) 2 (averagedJoint d) :=
  IsGaussian.memLp_two_id.comp_measurePreserving
    ((measurePreserving_eval (fun _ : Fin m => stdGaussian E) i).comp (returnedCoordinates_preserving d))
theorem increment_memLp (d : Data ι m) (i : Fin m) :
    MemLp (childIncrement d i) 2 (averagedJoint d) :=
  (returned_memLp d i).sub (active_memLp d i)

theorem stateChildren_apply (d : Data ι m) (z : E × (Fin m → E)) :
    stateChildren d z = Measure.pi (fun i => d.child i (z.2 i)) := by
  let : ∀ i, IsMarkovKernel (d.child i) := d.markov
  exact MeanReferenceLayer.finiteProduct_apply m _ (fun _ => inferInstance) z

theorem splitExecution_preserving (d : Data ι m) :
    MeasurePreserving (fun z : Execution (ι := ι) (m := m) => (split d z.1,z.2))
      (averagedJoint d)
      (((stdGaussian E).prod (noiseLaw (ι := ι) (m := m))) ⊗ₘ stateChildren d) := by
  refine ⟨((measurable_split d).comp measurable_fst).prodMk measurable_snd, ?_⟩
  have hp := MeanReferenceLayer.compProd_comap_push
    ((stdGaussian E).prod (noiseLaw (ι := ι) (m := m))) (stateChildren d)
    (split d) (measurable_split d)
  change (_ ⊗ₘ childrenKernel d).map _ = _ at hp
  rwa [← averagedJoint_eq, (split_preserving d).map_eq] at hp

private theorem gaussian_coordinate_mean (v : E) (i : Fin m) :
    (∫ p : Fin m → E, ⟪v,p i⟫ ∂Measure.pi (fun _ : Fin m => stdGaussian E)) = 0 := by
  have h := measurePreserving_eval (fun _ : Fin m => stdGaussian E) i
  rw [← integral_map_of_stronglyMeasurable h.measurable (by fun_prop), h.map_eq]
  exact integral_strongDual_stdGaussian (innerSL ℝ v)

/-- Different child tapes have zero mixed old/new moment under the actual execution. -/
theorem returned_active_cross (d : Data ι m) (v : E) (i j : Fin m) (hij : i ≠ j) :
    (∫ z : Execution (ι := ι) (m := m),
      ⟪v,z.2 i⟫ * ⟪v,active d z.1 j⟫ ∂averagedJoint d) = 0 := by
  let π := noiseLaw (ι := ι) (m := m)
  let ν := (stdGaussian E).prod π
  let f : (E × (Fin m → E)) × (Fin m → E) → ℝ := fun z => ⟪v,z.2 i⟫ * ⟪v,z.1.2 j⟫
  have hf : StronglyMeasurable f := by dsimp [f]; fun_prop
  have hp := splitExecution_preserving d
  have hint : Integrable f (ν ⊗ₘ stateChildren d) := by
    apply (hp.integrable_comp hf.aestronglyMeasurable).mp
    exact ((returned_memLp d i).const_inner (𝕜 := ℝ) v).integrable_mul
      ((active_memLp d j).const_inner (𝕜 := ℝ) v)
  have hinter : Integrable
      (fun z : E × (Fin m → E) => ∫ q, f (z,q) ∂stateChildren d z) ν := by
    have h := hint.integral_compProd
    simpa only [Kernel.const_apply,Kernel.prodMkLeft_apply] using h
  change (∫ z, f (split d z.1,z.2) ∂averagedJoint d) = 0
  rw [← integral_map_of_stronglyMeasurable hp.measurable hf,hp.map_eq]
  rw [Measure.integral_compProd hint,integral_prod _ hinter]
  apply integral_eq_zero_of_ae
  filter_upwards with g
  have he : ∀ p : Fin m → E,
      (∫ q, f ((g,p),q) ∂stateChildren d (g,p)) =
      (∫ x, ⟪v,x⟫ ∂d.child i (p i)) * ⟪v,p j⟫ := by
    intro p
    dsimp [f]
    rw [integral_mul_const,stateChildren_apply]
    let : ∀ k, IsProbabilityMeasure (d.child k (p k)) :=
      fun k => by let := d.markov k; infer_instance
    have hh := measurePreserving_eval (fun k => d.child k (p k)) i
    congr 1
    rw [← integral_map_of_stronglyMeasurable hh.measurable (by fun_prop),hh.map_eq]
  simp_rw [he]
  let a : E → ℝ := fun p => ∫ x,⟪v,x⟫ ∂d.child i p
  have ha : StronglyMeasurable a :=
    (show StronglyMeasurable (fun x : E => ⟪v,x⟫) by fun_prop).integral_kernel
  have hind := (iIndepFun_pi (μ := fun _ : Fin m => stdGaussian E)
    (X := fun _ (p : E) => p) (fun _ => measurable_id.aemeasurable)).indepFun hij
  have hscalar := hind.comp ha.measurable (by fun_prop : Measurable (fun p : E => ⟪v,p⟫))
  have hfactor := hscalar.integral_fun_mul_eq_mul_integral
    (ha.comp_measurable (measurable_pi_apply i)).aestronglyMeasurable
    (by fun_prop : StronglyMeasurable (fun p : Fin m → E => ⟪v,p j⟫)).aestronglyMeasurable
  simpa [Function.comp_def, gaussian_coordinate_mean, mul_zero, a, π, noiseLaw] using hfactor

private theorem gaussian_pair_cross_comp {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    {μ : Measure Ω} {g : Ω → J → E}
    (hg : MeasurePreserving g μ (Measure.pi (fun _ : J => stdGaussian E)))
    (v : E) (i j : J) (hij : i ≠ j) :
    (∫ z, ⟪v,g z i⟫ * ⟪v,g z j⟫ ∂μ) = 0 := by
  have hm : StronglyMeasurable (fun p : J → E => ⟪v,p i⟫ * ⟪v,p j⟫) := by fun_prop
  rw [← integral_map_of_stronglyMeasurable hg.measurable hm,hg.map_eq]
  have hi := iIndepFun_pi (μ := fun _ : J => stdGaussian E)
    (X := fun _ (p : E) => ⟪v,p⟫) (fun _ => by fun_prop)
  rw [(hi.indepFun hij).integral_fun_mul_eq_mul_integral
    (by fun_prop : StronglyMeasurable (fun p : J → E => ⟪v,p i⟫)).aestronglyMeasurable
    (by fun_prop : StronglyMeasurable (fun p : J → E => ⟪v,p j⟫)).aestronglyMeasurable]
  have h := measurePreserving_eval (fun _ : J => stdGaussian E) j
  have hz : (∫ p : J → E, ⟪v,p j⟫ ∂Measure.pi (fun _ : J => stdGaussian E)) = 0 := by
    rw [← integral_map_of_stronglyMeasurable h.measurable (by fun_prop),h.map_eq]
    exact integral_strongDual_stdGaussian (innerSL ℝ v)
  rw [hz,mul_zero]

/-- No off-diagonal covariance assumption is used. -/
theorem child_child_cross (d : Data ι m) (v : E) (i j : Fin m) (hij : i ≠ j) :
    (∫ z, ⟪v,childIncrement d i z⟫ * ⟪v,childIncrement d j z⟫ ∂averagedJoint d) = 0 := by
  have hqq := gaussian_pair_cross_comp (returnedCoordinates_preserving d) v i j hij
  have hpp := gaussian_pair_cross_comp (activeCoordinates_preserving d) v i j hij
  have hqp := returned_active_cross d v i j hij
  have hpq : (∫ z : Execution (ι := ι) (m := m),
      ⟪v,active d z.1 i⟫ * ⟪v,z.2 j⟫ ∂averagedJoint d) = 0 := by
    simpa only [mul_comm] using returned_active_cross d v j i hij.symm
  have hqi := (returned_memLp d i).const_inner (𝕜 := ℝ) v
  have hqj := (returned_memLp d j).const_inner (𝕜 := ℝ) v
  have hpi := (active_memLp d i).const_inner (𝕜 := ℝ) v
  have hpj := (active_memLp d j).const_inner (𝕜 := ℝ) v
  simp only [childIncrement,inner_sub_right,sub_mul,mul_sub]
  have h1 := integral_sub ((hqi.integrable_mul hqj).sub (hpi.integrable_mul hqj))
    ((hqi.integrable_mul hpj).sub (hpi.integrable_mul hpj))
  have h2 := integral_sub (hqi.integrable_mul hqj) (hpi.integrable_mul hqj)
  have h3 := integral_sub (hqi.integrable_mul hpj) (hpi.integrable_mul hpj)
  simp only [Pi.sub_apply,Pi.mul_apply] at h1 h2 h3
  rw [h1,h2,h3,hqq,hpp,hqp,hpq]
  norm_num

private lemma integral_sq_sum_orthogonal {A J : Type*} [MeasurableSpace A] [Fintype J]
    (μ : Measure A) (X : J → A → ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    (horth : ∀ i j, i ≠ j → (∫ a, X i a * X j a ∂μ) = 0) :
    (∫ a, (∑ i, X i a)^2 ∂μ) = ∑ i, ∫ a, (X i a)^2 ∂μ := by
  classical
  simp_rw [pow_two, Finset.sum_mul_sum]
  have hi (i : J) : Integrable (fun a => ∑ j, X i a * X j a) μ :=
    integrable_finsetSum Finset.univ (fun j _ => (hX i).integrable_mul (hX j))
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  have hij (j : J) : Integrable (fun a => X i a * X j a) μ := (hX i).integrable_mul (hX j)
  rw [integral_finsetSum Finset.univ (fun j _ => hij j)]
  exact Finset.sum_eq_single i (fun j _ hji => horth i j hji.symm) (by simp)

/-- Exact conditional-parent directional covariance sum for the constructed root. -/
theorem innovation_second_moment (d : Data ι m) (v : E) :
    (∫ z, ⟪v, output d z - z.1.1⟫^2 ∂averagedJoint d) =
      ∑ i, (d.weight i)^2 * (∫ z, ⟪v, childIncrement d i z⟫^2 ∂averagedJoint d) := by
  let X : Fin m → Execution (ι := ι) (m := m) → ℝ :=
    fun i z => (-d.weight i) * ⟪v,childIncrement d i z⟫
  have hX : ∀ i, MemLp (X i) 2 (averagedJoint d) :=
    fun i => ((increment_memLp d i).const_inner (𝕜 := ℝ) v).const_mul _
  have ho : ∀ i j, i ≠ j → (∫ z, X i z * X j z ∂averagedJoint d) = 0 := by
    intro i j hij
    simp only [X, mul_mul_mul_comm]
    rw [integral_const_mul, child_child_cross d v i j hij, mul_zero]
  have he := integral_sq_sum_orthogonal (averagedJoint d) X hX ho
  have hs : ∀ z, ⟪v, output d z - z.1.1⟫ = ∑ i, X i z := by
    intro z
    rw [innovation]
    simp only [inner_sum,inner_smul_right,X,childIncrement]
  simp_rw [hs]
  rw [he]
  simp only [X, mul_pow, neg_sq, integral_const_mul]

/-- A child directional variance estimate transfers with squared quadrature weights.
This is not a W12 conclusion; the child bound and later Poisson estimate remain explicit. -/
theorem innovation_second_moment_le (d : Data ι m) (v : E) (b : Fin m → ℝ)
    (hb : ∀ i, (∫ z, ⟪v,childIncrement d i z⟫^2 ∂averagedJoint d) ≤ b i) :
    (∫ z, ⟪v,output d z-z.1.1⟫^2 ∂averagedJoint d) ≤ ∑ i, (d.weight i)^2 * b i := by
  rw [innovation_second_moment]
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hb i) (sq_nonneg _))

end AcceleratedLogConcave.Root.RetainedLaw
