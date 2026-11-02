import AcceleratedLogConcave.Numerics.MeanBenchmarkCoupling
import AcceleratedLogConcave.Conditional.GaussianAssembly
import Mathlib.Probability.Independence.Integration
noncomputable section
open Set MeasureTheory ProbabilityTheory AcceleratedLogConcave
open Numerics Numerics.MeanFlowLp Conditional
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AcceleratedLogConcave.Conditional.MeanReferenceLayer
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

/-- An actual finite independent product, constructed recursively, not supplied as a law premise. -/
def finiteProduct {Ω : Type*} [MeasurableSpace Ω] :
    (n : ℕ) → (Fin n → Kernel Ω E) → Kernel Ω (Fin n → E)
  | 0,_ => Kernel.deterministic (fun _=>Fin.elim0) measurable_const
  | n+1,k => ((k 0) ×ₖ finiteProduct n (fun j=>k j.succ)).map
      (fun z j=>Fin.cases z.1 z.2 j)

structure Children (d : Data ι m) where
  scale : Fin m → ℝ
  scale_pos : ∀ i,0<scale i
  beta : ℝ
  beta_pos : 0<beta
  budget : (d.sigma/2)^2+(∑ i,(GaussLegendre.weight m i*scale i)^2)+beta^2=d.sigma^2
  kernel : Fin m → Kernel (E × E) E
  markov : ∀ i,IsMarkovKernel (kernel i)
  invariant : ∀ i y,(kernel i).comap (fun p=>(y,p)) measurable_prodMk_left ∘ₘ (stdGaussian E)=stdGaussian E

def coefficients (d : Data ι m) (c : Children d) (i : Option (Fin m)) : ℝ :=
  GaussianAssembly.inventoryCoefficients (d.sigma/2) (GaussLegendre.weight m) c.scale i / d.sigma
abbrev Fresh (ι : Type*) (m : ℕ) := EuclideanSpace ℝ ι × (Option (Fin m) → EuclideanSpace ℝ ι)
abbrev Host (ι : Type*) (m : ℕ) := EuclideanSpace ℝ ι × Fresh ι m

def active (d : Data ι m) (c : Children d) (h : Host ι m) : Option (Fin m) → E :=
  GaussianAssembly.active (coefficients d c) h.1 h.2.2
def reserve (d : Data ι m) (c : Children d) (h : Host ι m) : E :=
  GaussianAssembly.residual (coefficients d c) h.1 h.2.2
/-- The actual centering path depends on the independent position and active G0 only. -/
def phase (d : Data ι m) (c : Children d) (t : ℝ) (h : Host ι m) : Centering.Phase E :=
  CenteringFlowLp.phase (kernelData d) (d.sigma/2) (half_pos d.hsigma) t
    (WithLp.toLp 2 (h.2.1,active d c h none))
def childCenter (d : Data ι m) (c : Children d) (i : Fin m) (h : Host ι m) : E :=
  d.x+(d.r*AffineGraph.backwardEnd d.G.R) • (phase d c (GaussLegendre.node m i) h).fst

def freshLaw (d : Data ι m) : Measure (Fresh ι m) :=
  (MeanBenchmarkCoupling.positionLaw d).prod (Measure.pi (fun _ : Option (Fin m)=>stdGaussian E))
def freshKernel (d : Data ι m) : Kernel E (Host ι m) :=
  (Kernel.id : Kernel E E) ×ₖ Kernel.const E (freshLaw d)

def childKernel (d : Data ι m) (c : Children d) (i : Fin m) : Kernel (Host ι m) E :=
  (c.kernel i).comap (fun h=>(childCenter d c i h,active d c h (some i))) (by
    unfold childCenter phase active GaussianAssembly.active GaussianAssembly.noiseSum
    have hc := CenteringFlowLp.continuous_phase (kernelData d) (d.sigma/2) (half_pos d.hsigma)
    exact ((continuous_const.add (by fun_prop)).prodMk (by fun_prop)).measurable)
def childrenKernel (d : Data ι m) (c : Children d) : Kernel (Host ι m) (Fin m → E) :=
  finiteProduct m (childKernel d c)
def jointKernel (d : Data ι m) (c : Children d) : Kernel E (Host ι m × (Fin m → E)) :=
  ((Kernel.id : Kernel (Host ι m) (Host ι m)) ×ₖ childrenKernel d c) ∘ₖ freshKernel d

def recombine (d : Data ι m) (c : Children d) (h : Host ι m) (p' : Fin m → E) : E :=
  d.sigma⁻¹ • ((d.sigma/2) • (phase d c 1 h).snd+
    (∑ i,(GaussLegendre.weight m i*c.scale i) • p' i)+c.beta • reserve d c h)
def parentKernel (d : Data ι m) (c : Children d) : Kernel E E :=
  (jointKernel d c).map (fun z=>recombine d c z.1 z.2)
def averagedJoint (d : Data ι m) (c : Children d) : Measure (Host ι m × (Fin m → E)) :=
  jointKernel d c ∘ₘ (stdGaussian E)

/-- Actual section is precisely the independent child-product law. -/
def ProductTarget (d : Data ι m) (c : Children d) : Prop :=
  IsMarkovKernel (childrenKernel d c) ∧
  ∀ h,childrenKernel d c h=Measure.pi (fun i=>c.kernel i (childCenter d c i h,active d c h (some i)))

/-- Complete input split, including the independently drawn position and recovered reserve. -/
def SplitTarget (d : Data ι m) (c : Children d) : Prop :=
  ((stdGaussian E).prod (freshLaw d)).map
    (fun h=>(h.2.1,fun i : Option (Option (Fin m))=>i.elim (reserve d c h) (active d c h)))=
    (MeanBenchmarkCoupling.positionLaw d).prod
      (Measure.pi (fun _ : Option (Option (Fin m))=>stdGaussian E))

/-- Given the actual initial path data, all returned child momenta and the reserve are
independent Gaussians. This is a joint-law conclusion, not an assumed conditional law. -/
def ChildJointTarget (d : Data ι m) (c : Children d) : Prop :=
  (averagedJoint d c).map
    (fun z=>((z.1.2.1,active d c z.1 none),
      fun j : Option (Fin m)=>j.elim (reserve d c z.1) z.2))=
    ((MeanBenchmarkCoupling.positionLaw d).prod (stdGaussian E)).prod
      (Measure.pi (fun _ : Option (Fin m)=>stdGaussian E))

/-- Recombine actual endpoint G1, returned child momenta and the same recovered reserve. -/
def OutputJointTarget (d : Data ι m) (c : Children d) : Prop :=
  (averagedJoint d c).map
    (fun z=>(fun j : Option (Option (Fin m))=>j.elim (reserve d c z.1)
      (fun i=>i.elim ((phase d c 1 z.1).snd) z.2)))=
    Measure.pi (fun _ : Option (Option (Fin m))=>stdGaussian E)

def KernelTarget (d : Data ι m) (c : Children d) : Prop :=
  IsMarkovKernel (parentKernel d c) ∧ parentKernel d c ∘ₘ (stdGaussian E)=stdGaussian E ∧
  (averagedJoint d c).map (fun z=>(z.1.1,recombine d c z.1 z.2))=
    (stdGaussian E) ⊗ₘ parentKernel d c

/-- Exact source displacement uses the very same original input, before taking any expectations. -/
def DisplacementTarget (d : Data ι m) (c : Children d) : Prop :=
  ∀ h p',d.sigma • (recombine d c h p'-h.1)=
    (d.sigma/2) • ((phase d c 1 h).snd-active d c h none)+
    ∑ i,(GaussLegendre.weight m i*c.scale i) • (p' i-active d c h (some i))


omit [DecidableEq ι] [Fintype ι] in
theorem measurable_cons (n : ℕ) :
    Measurable (fun z : E × (Fin n → E) => fun j : Fin (n+1)=>(Fin.cases z.1 z.2 j : E)) := by
  apply Measurable.of_eval
  intro j
  refine Fin.cases ?_ (fun i=>?_) j
  · exact measurable_fst
  · exact (measurable_pi_apply i).comp measurable_snd

omit [DecidableEq ι] [Fintype ι] in
theorem finiteProduct_markov {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (k : Fin n → Kernel Ω E) (hk : ∀ i,IsMarkovKernel (k i)) : IsMarkovKernel (finiteProduct n k) := by
  induction n with
  | zero => unfold finiteProduct;infer_instance
  | succ n ih =>
    let : IsMarkovKernel (k 0) := hk 0
    let : IsMarkovKernel (finiteProduct n (fun j=>k j.succ)) := ih _ (fun j=>hk j.succ)
    exact Kernel.IsMarkovKernel.map _ (measurable_cons n)

omit [DecidableEq ι] in
theorem finiteProduct_apply {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (k : Fin n → Kernel Ω E) (hk : ∀ i,IsMarkovKernel (k i)) (x : Ω) :
    finiteProduct n k x=Measure.pi (fun i=>k i x) := by
  induction n with
  | zero =>
    rw [finiteProduct,Kernel.deterministic_apply,Measure.pi_of_empty _ Fin.elim0]
  | succ n ih =>
    let : ∀ i,IsMarkovKernel (k i) := hk
    let := finiteProduct_markov n (fun j=>k j.succ) (fun j=>hk j.succ)
    rw [finiteProduct,Kernel.map_apply _ (measurable_cons n),Kernel.prod_apply,ih _ (fun j=>hk j.succ)]
    apply (Measure.pi_eq fun s hs=>?_).symm
    rw [Measure.map_apply (measurable_cons n) (MeasurableSet.univ_pi hs)]
    have he : (fun z : E × (Fin n → E)=>fun j=>Fin.cases z.1 z.2 j) ⁻¹' Set.univ.pi s =
        s 0 ×ˢ Set.univ.pi (fun j=>s j.succ) := by
      ext z
      simp [Set.mem_pi,Fin.forall_fin_succ]
    rw [he,Measure.prod_prod,Measure.pi_pi]
    exact (Fin.prod_univ_succ fun i=>k i x (s i)).symm

instance childKernel_markov (d : Data ι m) (c : Children d) (i : Fin m) :
    IsMarkovKernel (childKernel d c i) := by
  let := c.markov i
  unfold childKernel
  infer_instance
instance childrenKernel_markov (d : Data ι m) (c : Children d) :
    IsMarkovKernel (childrenKernel d c) := finiteProduct_markov m _ (fun _=>inferInstance)

theorem product_target (d : Data ι m) (c : Children d) : ProductTarget d c := by
  refine ⟨inferInstance,fun h=>?_⟩
  exact finiteProduct_apply m _ (fun _=>inferInstance) h

instance freshLaw_probability (d : Data ι m) : IsProbabilityMeasure (freshLaw d) := by
  unfold freshLaw
  infer_instance
instance freshKernel_markov (d : Data ι m) : IsMarkovKernel (freshKernel d) := by
  unfold freshKernel
  infer_instance
instance jointKernel_markov (d : Data ι m) (c : Children d) :
    IsMarkovKernel (jointKernel d c) := by
  unfold jointKernel
  infer_instance

omit [DecidableEq ι] in
theorem budget_admissible (d : Data ι m) (c : Children d) :
    GaussianAssembly.mass (coefficients d c)<1 :=
  GaussianAssembly.inventory_budget_admissible d.hsigma c.beta_pos c.budget

omit [DecidableEq ι] in
theorem reconstruction (d : Data ι m) (c : Children d) (h : Host ι m) :
    d.sigma • h.1=(d.sigma/2) • active d c h none+
      (∑ i,(GaussLegendre.weight m i*c.scale i) • active d c h (some i))+c.beta • reserve d c h :=
  GaussianAssembly.inventory_reconstruction d.hsigma c.beta_pos c.budget h.1 h.2.2

theorem displacement_target (d : Data ι m) (c : Children d) : DisplacementTarget d c := by
  intro h p'
  rw [smul_sub,recombine,smul_smul,mul_inv_cancel₀ d.hsigma.ne',one_smul,reconstruction]
  simp_rw [smul_sub,Finset.sum_sub_distrib]
  abel


omit [DecidableEq ι] in
theorem continuous_active (d : Data ι m) (c : Children d) (i : Option (Fin m)) :
    Continuous (fun h : Host ι m=>active d c h i) := by
  unfold active GaussianAssembly.active GaussianAssembly.noiseSum
  fun_prop
omit [DecidableEq ι] in
theorem continuous_reserve (d : Data ι m) (c : Children d) : Continuous (reserve d c) := by
  unfold reserve GaussianAssembly.residual GaussianAssembly.noiseSum
  fun_prop

theorem continuous_phase (d : Data ι m) (c : Children d) (t : ℝ) : Continuous (phase d c t) := by
  unfold phase
  exact (CenteringFlowLp.continuous_phase (kernelData d) (d.sigma/2) (half_pos d.hsigma)).comp
    (continuous_const.prodMk ((WithLp.prod_continuous_toLp 2 E E).comp
      ((continuous_fst.comp continuous_snd).prodMk (continuous_active d c none))))

theorem continuous_recombine (d : Data ι m) (c : Children d) :
    Continuous (fun z : Host ι m × (Fin m → E)=>recombine d c z.1 z.2) := by
  unfold recombine
  exact (((((WithLp.prod_continuous_ofLp 2 E E).snd.comp
    ((continuous_phase d c 1).comp continuous_fst)).const_smul (d.sigma/2)).add
    (continuous_finsetSum _ fun i _=>((continuous_apply i).comp continuous_snd).const_smul
      (GaussLegendre.weight m i*c.scale i))).add
    (((continuous_reserve d c).comp continuous_fst).const_smul c.beta)).const_smul d.sigma⁻¹

instance parentKernel_markov (d : Data ι m) (c : Children d) : IsMarkovKernel (parentKernel d c) :=
  Kernel.IsMarkovKernel.map _ (continuous_recombine d c).measurable
instance averagedJoint_probability (d : Data ι m) (c : Children d) : IsProbabilityMeasure (averagedJoint d c) := by
  unfold averagedJoint
  infer_instance

omit [DecidableEq ι] in
theorem split_target (d : Data ι m) (c : Children d) : SplitTarget d c := by
  let μ := MeanBenchmarkCoupling.positionLaw d
  let γ := stdGaussian E
  let ν := Measure.pi (fun _ : Option (Fin m)=>stdGaussian E)
  let f : E × (Option (Fin m) → E) → Option (Option (Fin m)) → E :=
    fun pz i=>i.elim (GaussianAssembly.residual (coefficients d c) pz.1 pz.2)
      (GaussianAssembly.active (coefficients d c) pz.1 pz.2)
  have hf : Measurable f := by
    apply Measurable.of_eval
    intro i
    cases i <;> dsimp [f,GaussianAssembly.residual,GaussianAssembly.active,GaussianAssembly.noiseSum] <;> fun_prop
  have hs : MeasurePreserving f (γ.prod ν) (Measure.pi (fun _ : Option (Option (Fin m))=>stdGaussian E)) :=
    ⟨hf,GaussianAssembly.manuscript_joint_law d.hsigma c.beta_pos c.budget⟩
  have hp := (measurePreserving_prodAssoc μ γ ν).comp
    (((Measure.measurePreserving_swap (μ := γ) (ν := μ)).prod (MeasurePreserving.id ν)).comp
      (measurePreserving_prodAssoc γ μ ν).symm)
  have hall := ((MeasurePreserving.id μ).prod hs).comp hp
  exact hall.map_eq

end AcceleratedLogConcave.Conditional.MeanReferenceLayer

end

noncomputable section
open Set MeasureTheory ProbabilityTheory AcceleratedLogConcave
open scoped ENNReal
set_option autoImplicit false
namespace AcceleratedLogConcave.Conditional.MeanReferenceLayer
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem lintegral_pi_product {n : ℕ} (f : Fin n → E → ℝ≥0∞) (hf : ∀ i,Measurable (f i)) :
    (∫⁻ p,∏ i,f i (p i) ∂Measure.pi (fun _ : Fin n=>stdGaussian E))=
      ∏ i,∫⁻ x,f i x ∂stdGaussian E := by
  have hi := iIndepFun_pi (μ := fun _ : Fin n=>stdGaussian E) (fun i=>(hf i).aemeasurable)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hi
    (fun i=>(hf i).comp (measurable_pi_apply i))]
  apply Finset.prod_congr rfl
  intro i _
  exact (measurePreserving_eval (fun _ : Fin n=>stdGaussian E) i).lintegral_comp (hf i)

theorem finiteProduct_invariant {n : ℕ} (k : Fin n → Kernel E E)
    (hk : ∀ i,IsMarkovKernel (k i)) (hinv : ∀ i,k i ∘ₘ stdGaussian E=stdGaussian E) :
    finiteProduct n (fun i=>(k i).comap (fun p : Fin n → E=>p i) (measurable_pi_apply i)) ∘ₘ
      Measure.pi (fun _ : Fin n=>stdGaussian E)=Measure.pi (fun _ : Fin n=>stdGaussian E) := by
  let : ∀ i,IsMarkovKernel (k i) := hk
  let κ := finiteProduct n (fun i=>(k i).comap (fun p : Fin n → E=>p i) (measurable_pi_apply i))
  let : IsMarkovKernel κ := finiteProduct_markov n _ (fun _=>inferInstance)
  apply (Measure.pi_eq fun s hs=>?_).symm
  rw [Measure.bind_apply (MeasurableSet.univ_pi hs) κ.aemeasurable]
  have he : ∀ p,κ p (Set.univ.pi s)=∏ i,k i (p i) (s i) := by
    intro p
    rw [finiteProduct_apply n _ (fun _=>inferInstance),Measure.pi_pi]
    rfl
  simp_rw [he]
  rw [lintegral_pi_product _ (fun i=>(k i).measurable_coe (hs i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Measure.bind_apply (hs i) (k i).aemeasurable,hinv i]
end AcceleratedLogConcave.Conditional.MeanReferenceLayer
end

noncomputable section
open Set MeasureTheory ProbabilityTheory AcceleratedLogConcave
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AcceleratedLogConcave.Conditional.MeanReferenceLayer
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem option_split {J : Type*} [Fintype J] :
    MeasurePreserving (fun p : Option J → E=>(p none,fun j=>p (some j)))
      (Measure.pi (fun _ : Option J=>stdGaussian E))
      ((stdGaussian E).prod (Measure.pi (fun _ : J=>stdGaussian E))) := by
  let e := MeasurableEquiv.piOptionEquivProd (fun _ : Option J=>E)
  have h : MeasurePreserving e.symm
      ((Measure.pi (fun _ : J=>stdGaussian E)).prod (stdGaussian E))
      (Measure.pi (fun _ : Option J=>stdGaussian E)) :=
    ⟨e.symm.measurable,Measure.pi_map_piOptionEquivProd (fun _=>stdGaussian E)⟩
  exact Measure.measurePreserving_swap.comp h.symm

omit [Fintype ι] in
theorem bind_map_input {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (k : Kernel B C) (f : A → B) (hf : Measurable f) :
    k ∘ₘ μ.map f=(k.comap f hf) ∘ₘ μ := by
  rw [← Measure.deterministic_comp_eq_map hf,Measure.comp_assoc,Kernel.comp_deterministic_eq_comap]

omit [Fintype ι] in
theorem retained_update {B P Q : Type*} [MeasurableSpace B] [MeasurableSpace P]
    [MeasurableSpace Q] (μ : Measure B) (ν : Measure P) (ξ : Measure Q)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ]
    (k : Kernel (B × P) Q) [IsMarkovKernel k]
    (hi : ∀ b,k.comap (fun p=>(b,p)) measurable_prodMk_left ∘ₘ ν=ξ) :
    ((Kernel.deterministic Prod.fst measurable_fst) ×ₖ k) ∘ₘ (μ.prod ν)=μ.prod ξ := by
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.bind_apply (hs.prod ht) (Kernel.aemeasurable _),Measure.prod_prod]
  simp_rw [Kernel.prod_apply_prod,Kernel.deterministic_apply]
  have hD : Measurable (fun b : B=>(Measure.dirac b) s) :=
    (Measure.measurable_coe hs).comp Measure.measurable_dirac
  have hM : Measurable (fun a : B × P=>(Measure.dirac a.1) s*k a t) :=
    (hD.comp measurable_fst).mul (k.measurable_coe ht)
  rw [lintegral_prod _ hM.aemeasurable]
  have he : ∀ b,(∫⁻ p,(Measure.dirac b) s*k (b,p) t ∂ν)=
      (Measure.dirac b) s*ξ t := by
    intro b
    have hM : Measurable (fun p : P=>k (b,p) t) :=
      (k.measurable_coe ht).comp measurable_prodMk_left
    rw [lintegral_const_mul _ hM]
    congr 1
    change (∫⁻ p,(k.comap (fun q=>(b,q)) measurable_prodMk_left) p t ∂ν)=ξ t
    rw [← Measure.bind_apply ht (Kernel.aemeasurable _),hi b]
  simp_rw [he]
  rw [lintegral_mul_const _ hD]
  simp [Measure.dirac_apply' _ hs,lintegral_indicator hs]

omit [Fintype ι] in
theorem compProd_comap_push {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) [IsProbabilityMeasure μ]
    (k : Kernel B C) [IsMarkovKernel k] (f : A → B) (hf : Measurable f) :
    (μ ⊗ₘ k.comap f hf).map (fun z=>(f z.1,z.2))=(μ.map f) ⊗ₘ k := by
  have hF : Measurable (fun z : A × C=>(f z.1,z.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  ext s hs
  rw [Measure.map_apply hF hs,
    Measure.compProd_apply (hs.preimage hF),
    Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  rfl

end AcceleratedLogConcave.Conditional.MeanReferenceLayer
end

noncomputable section
open Set MeasureTheory ProbabilityTheory AcceleratedLogConcave
open Numerics Numerics.MeanFlowLp Conditional
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AcceleratedLogConcave.Conditional.MeanReferenceLayer
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

abbrev BaseState (ι : Type*) := (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) × EuclideanSpace ℝ ι
abbrev SplitState (ι : Type*) (m : ℕ) := BaseState ι × (Fin m → EuclideanSpace ℝ ι)

def splitState (d : Data ι m) (c : Children d) (h : Host ι m) : SplitState ι m :=
  (((h.2.1,active d c h none),reserve d c h),fun i=>active d c h (some i))
def baseLaw (d : Data ι m) : Measure (BaseState ι) :=
  ((MeanBenchmarkCoupling.positionLaw d).prod (stdGaussian E)).prod (stdGaussian E)

omit [DecidableEq ι] in
theorem measurable_splitState (d : Data ι m) (c : Children d) : Measurable (splitState d c) :=
  (((measurable_fst.comp measurable_snd).prodMk (continuous_active d c none).measurable).prodMk
    (continuous_reserve d c).measurable).prodMk
      (Measurable.of_eval fun i=>(continuous_active d c (some i)).measurable)

instance baseLaw_probability (d : Data ι m) : IsProbabilityMeasure (baseLaw d) := by
  unfold baseLaw
  infer_instance

omit [DecidableEq ι] in
theorem splitState_law (d : Data ι m) (c : Children d) :
    ((stdGaussian E).prod (freshLaw d)).map (splitState d c)=
      (baseLaw d).prod (Measure.pi (fun _ : Fin m=>stdGaussian E)) := by
  let μ := MeanBenchmarkCoupling.positionLaw d
  let γ := stdGaussian E
  let π := Measure.pi (fun _ : Fin m=>stdGaussian E)
  have h0 : MeasurePreserving
      (fun h : Host ι m=>(h.2.1,fun i : Option (Option (Fin m))=>i.elim (reserve d c h) (active d c h)))
      (γ.prod (freshLaw d)) (μ.prod (Measure.pi (fun _ : Option (Option (Fin m))=>stdGaussian E))) :=
    ⟨by apply Measurable.prodMk (measurable_fst.comp measurable_snd);apply Measurable.of_eval;intro i;cases i
        exact (continuous_reserve d c).measurable
        exact (continuous_active d c _).measurable,
      split_target d c⟩
  have h1 := ((MeasurePreserving.id μ).prod (option_split (ι:=ι) (J:=Option (Fin m)))).comp h0
  have h2 := ((MeasurePreserving.id μ).prod
    ((MeasurePreserving.id γ).prod (option_split (ι:=ι) (J:=Fin m)))).comp h1
  have p1 := ((MeasurePreserving.id μ).prod (measurePreserving_prodAssoc γ γ π).symm).comp h2
  have p2 := ((MeasurePreserving.id μ).prod
    ((Measure.measurePreserving_swap (μ:=γ) (ν:=γ)).prod (MeasurePreserving.id π))).comp p1
  have p3 := ((MeasurePreserving.id μ).prod (measurePreserving_prodAssoc γ γ π)).comp p2
  have p4 := (measurePreserving_prodAssoc μ γ (γ.prod π)).symm.comp p3
  have p5 := (measurePreserving_prodAssoc (μ.prod γ) γ π).symm.comp p4
  exact p5.map_eq

def stateCenter (d : Data ι m) (i : Fin m) (b : BaseState ι) : E :=
  d.x+(d.r*AffineGraph.backwardEnd d.G.R) •
    (CenteringFlowLp.phase (kernelData d) (d.sigma/2) (half_pos d.hsigma)
      (GaussLegendre.node m i) (WithLp.toLp 2 b.1)).fst

theorem continuous_stateCenter (d : Data ι m) (i : Fin m) : Continuous (stateCenter d i) := by
  unfold stateCenter
  have hc := CenteringFlowLp.continuous_phase (kernelData d) (d.sigma/2) (half_pos d.hsigma)
  fun_prop

def stateChildren (d : Data ι m) (c : Children d) : Kernel (SplitState ι m) (Fin m → E) :=
  finiteProduct m (fun i=>(c.kernel i).comap
    (fun z=>(stateCenter d i z.1,z.2 i))
    (((continuous_stateCenter d i).measurable.comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)))
instance stateChildren_markov (d : Data ι m) (c : Children d) : IsMarkovKernel (stateChildren d c) := by
  let : ∀ i,IsMarkovKernel (c.kernel i) := c.markov
  exact finiteProduct_markov m _ (fun _=>inferInstance)

theorem stateChildren_apply (d : Data ι m) (c : Children d) (z : SplitState ι m) :
    stateChildren d c z=Measure.pi (fun i=>c.kernel i (stateCenter d i z.1,z.2 i)) := by
  let : ∀ i,IsMarkovKernel (c.kernel i) := c.markov
  exact finiteProduct_apply m _ (fun _=>inferInstance) z

theorem stateChildren_invariant (d : Data ι m) (c : Children d) (b : BaseState ι) :
    (stateChildren d c).comap (fun p=>(b,p)) measurable_prodMk_left ∘ₘ
      Measure.pi (fun _ : Fin m=>stdGaussian E)=Measure.pi (fun _ : Fin m=>stdGaussian E) := by
  let k (i : Fin m) : Kernel E E :=
    (c.kernel i).comap (fun p=>(stateCenter d i b,p)) measurable_prodMk_left
  let : ∀ i,IsMarkovKernel (k i) := fun i=>by dsimp [k];let := c.markov i;infer_instance
  have he : (stateChildren d c).comap (fun p=>(b,p)) measurable_prodMk_left=
      finiteProduct m (fun i=>(k i).comap (fun p : Fin m → E=>p i) (measurable_pi_apply i)) := by
    ext p : 1
    rw [Kernel.comap_apply,stateChildren_apply,finiteProduct_apply m _ (fun _=>inferInstance)]
    rfl
  rw [he]
  exact finiteProduct_invariant k (fun _=>inferInstance) (fun i=>c.invariant i _)

theorem children_eq_state_comap (d : Data ι m) (c : Children d) :
    childrenKernel d c=(stateChildren d c).comap (splitState d c) (measurable_splitState d c) := by
  ext h : 1
  rw [(product_target d c).2,Kernel.comap_apply,stateChildren_apply]
  rfl

theorem averagedJoint_eq (d : Data ι m) (c : Children d) :
    averagedJoint d c=((stdGaussian E).prod (freshLaw d)) ⊗ₘ childrenKernel d c := by
  rw [averagedJoint,jointKernel,← Measure.comp_assoc,freshKernel,
    ← Measure.compProd_eq_comp_prod,← Measure.compProd_eq_comp_prod,Measure.compProd_const]

theorem updated_split_law (d : Data ι m) (c : Children d) :
    (averagedJoint d c).map (fun z=>((splitState d c z.1).1,z.2))=
      (baseLaw d).prod (Measure.pi (fun _ : Fin m=>stdGaussian E)) := by
  let μ := (stdGaussian E).prod (freshLaw d)
  let π := Measure.pi (fun _ : Fin m=>stdGaussian E)
  have hp := compProd_comap_push μ (stateChildren d c) (splitState d c) (measurable_splitState d c)
  rw [← children_eq_state_comap,← averagedJoint_eq,splitState_law] at hp
  have hm : Measurable (fun z : SplitState ι m × (Fin m → E)=>(z.1.1,z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have he := congrArg (fun ν=>ν.map (fun z : SplitState ι m × (Fin m → E)=>(z.1.1,z.2))) hp
  have hg : Measurable (fun z : Host ι m × (Fin m → E)=>(splitState d c z.1,z.2)) :=
    ((measurable_splitState d c).comp measurable_fst).prodMk measurable_snd
  rw [Measure.map_map hm hg] at he
  refine he.trans ?_
  have hu := retained_update (baseLaw d) π π (stateChildren d c) (stateChildren_invariant d c)
  rw [Measure.compProd_eq_comp_prod,Measure.map_comp _ _ hm]
  rw [← hu]
  congr 1
  ext z s hs
  rw [Kernel.map_apply' _ hm _ hs,Kernel.id_prod_apply' _ _ (hs.preimage hm),
    Kernel.deterministic_prod_apply' measurable_fst _ _ hs]
  rfl

theorem childJoint_target (d : Data ι m) (c : Children d) : ChildJointTarget d c := by
  let μ := (MeanBenchmarkCoupling.positionLaw d).prod (stdGaussian E)
  let γ := stdGaussian E
  let π := Measure.pi (fun _ : Fin m=>stdGaussian E)
  have h := (measurePreserving_prodAssoc μ γ π)
  have hopt := (option_split (ι:=ι) (J:=Fin m)).map_eq
  let merge : E × (Fin m → E) → Option (Fin m) → E := fun z i=>i.elim z.1 z.2
  have hmerge : MeasurePreserving merge (γ.prod π) (Measure.pi (fun _ : Option (Fin m)=>stdGaussian E)) := by
    have hs := (option_split (ι:=ι) (J:=Fin m))
    have hm : Measurable merge := by
      apply Measurable.of_eval;intro i;cases i <;> dsimp [merge] <;> fun_prop
    refine ⟨hm,?_⟩
    rw [← hs.map_eq,Measure.map_map hm hs.measurable]
    have hid : merge ∘ (fun p : Option (Fin m) → E=>(p none,fun j=>p (some j)))=id := by
      funext p i;cases i <;> rfl
    rw [hid,Measure.map_id]
  have hout := ((MeasurePreserving.id μ).prod hmerge).comp h
  have hm : Measurable (fun z : BaseState ι × (Fin m → E)=>(z.1.1,merge (z.1.2,z.2))) :=
    measurable_fst.fst.prodMk (hmerge.measurable.comp (measurable_fst.snd.prodMk measurable_snd))
  have he := congrArg (fun ν=>ν.map (fun z : BaseState ι × (Fin m → E)=>(z.1.1,merge (z.1.2,z.2)))) (updated_split_law d c)
  have hg : Measurable (fun z : Host ι m × (Fin m → E)=>((splitState d c z.1).1,z.2)) :=
    (((measurable_splitState d c).comp measurable_fst).fst.prodMk measurable_snd)
  rw [Measure.map_map hm hg] at he
  exact he.trans hout.map_eq

end AcceleratedLogConcave.Conditional.MeanReferenceLayer
end

noncomputable section
open Set MeasureTheory ProbabilityTheory AcceleratedLogConcave
open Numerics Numerics.MeanFlowLp Conditional
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AcceleratedLogConcave.Conditional.MeanReferenceLayer
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

omit [DecidableEq ι] in
theorem option_merge {J : Type*} [Fintype J] :
    MeasurePreserving (fun z : E × (J → E)=>fun i : Option J=>i.elim z.1 z.2)
      ((stdGaussian E).prod (Measure.pi (fun _ : J=>stdGaussian E)))
      (Measure.pi (fun _ : Option J=>stdGaussian E)) := by
  have hs := (option_split (ι:=ι) (J:=J))
  have hm : Measurable (fun z : E × (J → E)=>fun i : Option J=>i.elim z.1 z.2) := by
    apply Measurable.of_eval;intro i;cases i <;> dsimp <;> fun_prop
  refine ⟨hm,?_⟩
  rw [← hs.map_eq,Measure.map_map hm hs.measurable]
  have he : (fun z : E × (J → E)=>fun i : Option J=>i.elim z.1 z.2) ∘
      (fun p : Option J → E=>(p none,fun j=>p (some j)))=id := by
    funext p i;cases i <;> rfl
  rw [he,Measure.map_id]

theorem endpoint_preserving (d : Data ι m) (t : ℝ) :
    MeasurePreserving (fun yg : E × E=>MeanBenchmarkCoupling.endpoint d t yg.1 yg.2)
      ((MeanBenchmarkCoupling.positionLaw d).prod (stdGaussian E)) (stdGaussian E) := by
  have h0 : MeasurePreserving (WithLp.toLp 2 : E × E → Centering.Phase E)
      ((MeanBenchmarkCoupling.positionLaw d).prod (stdGaussian E))
      (KernelFlowLp.seedMeasure (kernelData d)) :=
    ⟨(WithLp.prod_continuous_toLp 2 E E).measurable,rfl⟩
  exact (KernelFlowLp.momentum_preserving (kernelData d)).comp
    ((CenteringFlowLp.phase_preserving (kernelData d) (d.sigma/2) (half_pos d.hsigma) t).comp h0)

theorem outputJoint_target (d : Data ι m) (c : Children d) : OutputJointTarget d c := by
  let γ := stdGaussian E
  let π := Measure.pi (fun _ : Fin m=>stdGaussian E)
  let πopt := Measure.pi (fun _ : Option (Fin m)=>stdGaussian E)
  have h1 := (endpoint_preserving d 1).prod (MeasurePreserving.id πopt)
  have h2 := ((MeasurePreserving.id γ).prod (option_split (ι:=ι) (J:=Fin m))).comp h1
  have h3 := (measurePreserving_prodAssoc γ γ π).symm.comp h2
  have h4 := ((Measure.measurePreserving_swap (μ:=γ) (ν:=γ)).prod (MeasurePreserving.id π)).comp h3
  have h5 := (measurePreserving_prodAssoc γ γ π).comp h4
  have h6 := ((MeasurePreserving.id γ).prod (option_merge (ι:=ι) (J:=Fin m))).comp h5
  have h7 := (option_merge (ι:=ι) (J:=Option (Fin m))).comp h6
  let f : (E × E) × (Option (Fin m) → E) → Option (Option (Fin m)) → E :=
    fun z j=>j.elim (z.2 none) (fun i=>i.elim (MeanBenchmarkCoupling.endpoint d 1 z.1.1 z.1.2)
      (fun i=>z.2 (some i)))
  have hf : Measurable f := h7.measurable
  have hg : Measurable (fun z : Host ι m × (Fin m → E)=>((z.1.2.1,active d c z.1 none),
      fun j : Option (Fin m)=>j.elim (reserve d c z.1) z.2)) := by
    apply Measurable.prodMk
    · exact measurable_fst.snd.fst.prodMk ((continuous_active d c none).measurable.comp measurable_fst)
    · apply Measurable.of_eval;intro j;cases j
      · exact (continuous_reserve d c).measurable.comp measurable_fst
      · rename_i i
        change Measurable (fun z : Host ι m × (Fin m → E)=>z.2 i)
        exact (measurable_pi_apply i).comp measurable_snd
  have he := congrArg (fun ν=>ν.map f) (childJoint_target d c)
  rw [Measure.map_map hf hg] at he
  exact he.trans h7.map_eq

def outputMap (d : Data ι m) (c : Children d) (v : Option (Option (Fin m)) → E) : E :=
  d.sigma⁻¹ • ((d.sigma/2) • v (some none)+
    (∑ i,(GaussLegendre.weight m i*c.scale i) • v (some (some i)))+c.beta • v none)

omit [DecidableEq ι] in
theorem continuous_outputMap (d : Data ι m) (c : Children d) : Continuous (outputMap d c) := by
  unfold outputMap
  fun_prop

omit [DecidableEq ι] in
theorem outputMap_invariant (d : Data ι m) (c : Children d) :
    (Measure.pi (fun _ : Option (Option (Fin m))=>stdGaussian E)).map (outputMap d c)=stdGaussian E := by
  let split : E × (Option (Fin m) → E) → Option (Option (Fin m)) → E :=
    fun pz i=>i.elim (GaussianAssembly.residual (coefficients d c) pz.1 pz.2)
      (GaussianAssembly.active (coefficients d c) pz.1 pz.2)
  have hs : Measurable split := by
    apply Measurable.of_eval;intro i;cases i <;>
      dsimp [split,GaussianAssembly.residual,GaussianAssembly.active,GaussianAssembly.noiseSum] <;> fun_prop
  have hl := GaussianAssembly.manuscript_joint_law («E»:=E) d.hsigma c.beta_pos c.budget
  change ((stdGaussian E).prod (Measure.pi (fun _ : Option (Fin m)=>stdGaussian E))).map split=_ at hl
  have he : outputMap d c ∘ split=Prod.fst := by
    funext pz
    have hr := GaussianAssembly.inventory_reconstruction d.hsigma c.beta_pos c.budget pz.1 pz.2
    change d.sigma⁻¹ • _=pz.1
    dsimp only [split,Option.elim_none,Option.elim_some,coefficients]
    change d.sigma • pz.1=(d.sigma/2) • GaussianAssembly.active (coefficients d c) pz.1 pz.2 none+
      (∑ i,(GaussLegendre.weight m i*c.scale i) • GaussianAssembly.active (coefficients d c) pz.1 pz.2 (some i))+
        c.beta • GaussianAssembly.residual (coefficients d c) pz.1 pz.2 at hr
    rw [← hr,smul_smul,inv_mul_cancel₀ d.hsigma.ne',one_smul]
  rw [← hl,Measure.map_map (continuous_outputMap d c).measurable hs,he]
  simp

theorem parentKernel_invariant (d : Data ι m) (c : Children d) :
    parentKernel d c ∘ₘ stdGaussian E=stdGaussian E := by
  have hm : Measurable (fun z : Host ι m × (Fin m → E)=>
      fun j : Option (Option (Fin m))=>j.elim (reserve d c z.1)
        (fun i=>i.elim ((phase d c 1 z.1).snd) z.2)) := by
    apply Measurable.of_eval;intro j;cases j
    · exact (continuous_reserve d c).measurable.comp measurable_fst
    · rename_i i;cases i
      · exact ((WithLp.prod_continuous_ofLp 2 E E).snd.comp
          ((continuous_phase d c 1).comp continuous_fst)).measurable
      · rename_i i
        change Measurable (fun z : Host ι m × (Fin m → E)=>z.2 i)
        exact (measurable_pi_apply i).comp measurable_snd
  have he := congrArg (fun ν=>ν.map (outputMap d c)) (outputJoint_target d c)
  rw [Measure.map_map (continuous_outputMap d c).measurable hm,outputMap_invariant] at he
  rw [parentKernel,← Measure.map_comp _ _ (continuous_recombine d c).measurable]
  exact he

theorem lintegral_jointKernel (d : Data ι m) (c : Children d) (p : E)
    (f : Host ι m × (Fin m → E) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z,f z ∂jointKernel d c p)=
      ∫⁻ a,∫⁻ q,f ((p,a),q) ∂childrenKernel d c (p,a) ∂freshLaw d := by
  rw [jointKernel,Kernel.lintegral_comp _ _ _ hf]
  simp_rw [Kernel.lintegral_id_prod hf]
  rw [freshKernel,Kernel.lintegral_id_prod hf.lintegral_kernel_prod_right']
  rfl

theorem retained_joint (d : Data ι m) (c : Children d) :
    (averagedJoint d c).map (fun z=>(z.1.1,recombine d c z.1 z.2))=
      (stdGaussian E) ⊗ₘ parentKernel d c := by
  have hm : Measurable (fun z : Host ι m × (Fin m → E)=>(z.1.1,recombine d c z.1 z.2)) :=
    measurable_fst.fst.prodMk (continuous_recombine d c).measurable
  apply Measure.ext_of_lintegral
  intro f hf
  have hF : Measurable (fun z : Host ι m × (Fin m → E)=>f (z.1.1,recombine d c z.1 z.2)) := hf.comp hm
  rw [lintegral_map hf hm,averagedJoint,
    Measure.lintegral_bind (Kernel.aemeasurable _) hF.aemeasurable,
    Measure.lintegral_compProd hf]
  apply lintegral_congr
  intro p
  have hfp : Measurable (fun b : E=>f (p,b)) := hf.comp measurable_prodMk_left
  rw [lintegral_jointKernel d c p _ hF,parentKernel,
    Kernel.map_apply _ (continuous_recombine d c).measurable,
    lintegral_map hfp (continuous_recombine d c).measurable]
  have hM : Measurable (fun z : Host ι m × (Fin m → E)=>f (p,recombine d c z.1 z.2)) :=
    hf.comp (measurable_const.prodMk (continuous_recombine d c).measurable)
  rw [lintegral_jointKernel d c p _ hM]

theorem kernel_target (d : Data ι m) (c : Children d) : KernelTarget d c :=
  ⟨inferInstance,parentKernel_invariant d c,retained_joint d c⟩

end AcceleratedLogConcave.Conditional.MeanReferenceLayer
end
