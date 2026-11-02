import AcceleratedLogConcave.Kinetic.GaussianEmbedding
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Gaussian moments for the Hamiltonian transport chaos

Moment identities are derived from the actual Gaussian measure, rather than
postulated as bounds on an abstract transport operator.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace NNReal
namespace AcceleratedLogConcave.Kinetic.ConditionalContraction

private theorem fourth_derivative_gaussian_mgf (v : ℝ) :
    iteratedDeriv 4 (fun t : ℝ => Real.exp (v * t ^ 2 / 2)) 0 = 3 * v ^ 2 := by
  let F (t : ℝ) := Real.exp (v * t ^ 2 / 2)
  have h0 (t : ℝ) : HasDerivAt F (v * t * F t) t := by
    convert ((((hasDerivAt_id t).pow 2).const_mul v).div_const 2).exp using 1 <;>
      first | rfl | (dsimp [F]; ring)
  have h1 (t : ℝ) : HasDerivAt (fun s => v * s * F s) ((v + v ^ 2 * t ^ 2) * F t) t := by
    convert ((hasDerivAt_id t).const_mul v).mul (h0 t) using 1 <;> first | rfl | (dsimp; ring)
  have h2 (t : ℝ) : HasDerivAt (fun s => (v + v ^ 2 * s ^ 2) * F s)
      ((3 * v ^ 2 * t + v ^ 3 * t ^ 3) * F t) t := by
    convert ((hasDerivAt_const t v).add (((hasDerivAt_id t).pow 2).const_mul (v ^ 2))).mul
      (h0 t) using 1 <;> first | rfl | (dsimp; ring)
  have h3 (t : ℝ) : HasDerivAt (fun s => (3 * v ^ 2 * s + v ^ 3 * s ^ 3) * F s)
      ((3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * F t) t := by
    convert (((hasDerivAt_id t).const_mul (3 * v ^ 2)).add
      (((hasDerivAt_id t).pow 3).const_mul (v ^ 3))).mul (h0 t) using 1 <;> first | rfl | (dsimp; ring)
  have d0 : deriv F = fun t => v * t * F t := funext (fun t => (h0 t).deriv)
  have d1 : deriv (fun t => v * t * F t) = fun t => (v + v ^ 2 * t ^ 2) * F t :=
    funext (fun t => (h1 t).deriv)
  have d2 : deriv (fun t => (v + v ^ 2 * t ^ 2) * F t) =
      fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * F t := funext (fun t => (h2 t).deriv)
  have d3 : deriv (fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * F t) =
      fun t => (3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * F t :=
    funext (fun t => (h3 t).deriv)
  change iteratedDeriv 4 F 0 = _
  rw [iteratedDeriv_succ' (n := 3), d0, iteratedDeriv_succ' (n := 2), d1,
    iteratedDeriv_succ' (n := 1), d2, iteratedDeriv_succ' (n := 0), d3, iteratedDeriv_zero]
  simp [F]

/-- Fourth moment of the genuine centered real Gaussian. -/
theorem integral_pow_four_gaussianReal (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  have hm := iteratedDeriv_mgf_zero (X := id) (μ := gaussianReal 0 v) (by simp) 4
  have he : mgf id (gaussianReal 0 v) = fun t => Real.exp ((v : ℝ) * t ^ 2 / 2) := by
    ext t
    simp [mgf_id_gaussianReal]
  rw [he] at hm
  simpa using hm.symm.trans (fourth_derivative_gaussian_mgf (v : ℝ))


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Every linear functional of the actual standard Gaussian has the expected
fourth moment, including zero-dimensional and degenerate directions. -/
theorem integral_inner_pow_four (v : E) :
    (∫ x, (inner ℝ v x) ^ 4 ∂stdGaussian E) = 3 * ‖v‖ ^ 4 := by
  let L : StrongDual ℝ E := innerSL ℝ v
  have he := IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) L
  calc
    _ = ∫ r : ℝ, r ^ 4 ∂(stdGaussian E).map L :=
      (integral_map L.continuous.aemeasurable (by fun_prop)).symm
    _ = 3 * ‖v‖ ^ 4 := by
      rw [he, integral_strongDual_stdGaussian, integral_pow_four_gaussianReal, variance_dual_stdGaussian]
      simp only [Real.coe_toNNReal _ (sq_nonneg ‖L‖)]
      simp only [L, innerSL_apply_norm]
      ring


private theorem integrable_inner_pow_four (v : E) :
    Integrable (fun x => (inner ℝ v x) ^ 4) (stdGaussian E) := by
  have h := (IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ v) 4 (by norm_num)).integrable_norm_pow
    (p := 4) (by norm_num)
  simpa only [innerSL_apply_apply, Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 from rfl,
    pow_mul, sq_abs] using h

/-- Products of linear Gaussian coordinates are actual L2 functions. -/
theorem memLp_inner_mul_inner (u v : E) :
    MemLp (fun x => inner ℝ u x * inner ℝ v x) 2 (stdGaussian E) := by
  let : ENNReal.HolderTriple 4 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
    norm_num [ENNReal.toReal_add]⟩
  exact (IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ u) 4 (by norm_num)).mul
    (IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ v) 4 (by norm_num))

/-- Polarization of the scalar fourth moment gives the paired-square Gaussian
identity without independence or nondegeneracy premises. -/
theorem integral_inner_sq_mul_inner_sq (u v : E) :
    (∫ x, (inner ℝ u x) ^ 2 * (inner ℝ v x) ^ 2 ∂stdGaussian E) =
      ‖u‖ ^ 2 * ‖v‖ ^ 2 + 2 * (inner ℝ u v) ^ 2 := by
  have hp := integrable_inner_pow_four (u + v)
  have hm := integrable_inner_pow_four (u - v)
  have hu := integrable_inner_pow_four u
  have hv := integrable_inner_pow_four v
  have he : (fun x => (inner ℝ (u + v) x) ^ 4 + (inner ℝ (u - v) x) ^ 4 -
      2 * (inner ℝ u x) ^ 4 - 2 * (inner ℝ v x) ^ 4) =
      (fun x => 12 * ((inner ℝ u x) ^ 2 * (inner ℝ v x) ^ 2)) := by
    funext x
    simp only [inner_add_left, inner_sub_left]
    ring
  have hi := congrArg (fun f : E → ℝ => ∫ x, f x ∂stdGaussian E) he
  have hs₁ := integral_sub ((hp.add hm).sub (hu.const_mul 2)) (hv.const_mul 2)
  have hs₂ := integral_sub (hp.add hm) (hu.const_mul 2)
  have ha := integral_add hp hm
  simp only [Pi.add_apply, Pi.sub_apply] at hs₁ hs₂ ha
  rw [hs₁, hs₂, ha,
    integral_const_mul, integral_const_mul, integral_const_mul] at hi
  simp only [integral_inner_pow_four] at hi
  have hnplus : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * inner ℝ u v + ‖v‖ ^ 2 := norm_add_sq_real u v
  have hnminus : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * inner ℝ u v + ‖v‖ ^ 2 := norm_sub_sq_real u v
  have hp4 : ‖u + v‖ ^ 4 = (‖u‖ ^ 2 + 2 * inner ℝ u v + ‖v‖ ^ 2) ^ 2 := by
    rw [← hnplus]; ring
  have hm4 : ‖u - v‖ ^ 4 = (‖u‖ ^ 2 - 2 * inner ℝ u v + ‖v‖ ^ 2) ^ 2 := by
    rw [← hnminus]; ring
  rw [hp4, hm4] at hi
  nlinarith

/-- Integrability of the fourth-order products used in Wick's identity. -/
theorem integrable_inner_four (u v w z : E) :
    Integrable (fun x => (inner ℝ u x * inner ℝ v x) *
      (inner ℝ w x * inner ℝ z x)) (stdGaussian E) :=
  (memLp_inner_mul_inner u v).integrable_mul (memLp_inner_mul_inner w z)

private theorem integrable_inner_sq_mul_inner_sq (u v : E) :
    Integrable (fun x => (inner ℝ u x) ^ 2 * (inner ℝ v x) ^ 2) (stdGaussian E) := by
  simpa only [mul_pow] using (memLp_inner_mul_inner u v).integrable_sq

/-- Wick's fourth-moment identity for the actual standard Gaussian, obtained
by polarization of its one-dimensional fourth moment. -/
theorem integral_inner_four (u v w z : E) :
    (∫ x, (inner ℝ u x * inner ℝ v x) * (inner ℝ w x * inner ℝ z x) ∂stdGaussian E) =
      inner ℝ u v * inner ℝ w z + inner ℝ u w * inner ℝ v z +
        inner ℝ u z * inner ℝ v w := by
  have hpp := integrable_inner_sq_mul_inner_sq (u + v) (w + z)
  have hmp := integrable_inner_sq_mul_inner_sq (u - v) (w + z)
  have hpm := integrable_inner_sq_mul_inner_sq (u + v) (w - z)
  have hmm := integrable_inner_sq_mul_inner_sq (u - v) (w - z)
  have he : (fun x => (inner ℝ (u + v) x)^2 * (inner ℝ (w + z) x)^2 -
      (inner ℝ (u - v) x)^2 * (inner ℝ (w + z) x)^2 -
      (inner ℝ (u + v) x)^2 * (inner ℝ (w - z) x)^2 +
      (inner ℝ (u - v) x)^2 * (inner ℝ (w - z) x)^2) =
      (fun x => 16 * ((inner ℝ u x * inner ℝ v x) *
        (inner ℝ w x * inner ℝ z x))) := by
    funext x
    simp only [inner_add_left, inner_sub_left]
    ring
  have hi := congrArg (fun f : E → ℝ => ∫ x, f x ∂stdGaussian E) he
  have ha := integral_add ((hpp.sub hmp).sub hpm) hmm
  have hs₁ := integral_sub (hpp.sub hmp) hpm
  have hs₂ := integral_sub hpp hmp
  simp only [Pi.sub_apply] at ha hs₁ hs₂
  rw [ha, hs₁, hs₂, integral_const_mul] at hi
  simp only [integral_inner_sq_mul_inner_sq] at hi
  simp only [norm_add_sq_real, norm_sub_sq_real,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right] at hi
  linear_combination -hi / 16

/-- Covariance of arbitrary Gaussian coordinates. -/
theorem integral_inner_mul_inner (u v : E) :
    (∫ x, inner ℝ u x * inner ℝ v x ∂stdGaussian E) = inner ℝ u v := by
  have h := covarianceBilin_apply (IsGaussian.memLp_two_id (μ := stdGaussian E)) u v
  rw [covarianceBilin_stdGaussian] at h
  change inner ℝ u v = _ at h
  simpa only [integral_id_stdGaussian, id_eq, sub_zero] using h.symm

/-- The centered quadratic coordinate, as a genuine Gaussian L2 function. -/
def centeredQuadratic (u v : E) : E → ℝ :=
  fun x => inner ℝ u x * inner ℝ v x - inner ℝ u v

theorem memLp_centeredQuadratic (u v : E) :
    MemLp (centeredQuadratic u v) 2 (stdGaussian E) :=
  (memLp_inner_mul_inner u v).sub (memLp_const _)

theorem integral_centeredQuadratic (u v : E) :
    (∫ x, centeredQuadratic u v x ∂stdGaussian E) = 0 := by
  change (∫ x, inner ℝ u x * inner ℝ v x - inner ℝ u v ∂stdGaussian E) = 0
  rw [integral_sub ((memLp_inner_mul_inner u v).integrable (by norm_num))
    (integrable_const _), integral_inner_mul_inner]
  simp

/-- Covariance of centered quadratic Gaussian chaos. -/
theorem integral_centeredQuadratic_mul (u v w z : E) :
    (∫ x, centeredQuadratic u v x * centeredQuadratic w z x ∂stdGaussian E) =
      inner ℝ u w * inner ℝ v z + inner ℝ u z * inner ℝ v w := by
  have he : (fun x => centeredQuadratic u v x * centeredQuadratic w z x) =
      (fun x => (inner ℝ u x * inner ℝ v x) * (inner ℝ w x * inner ℝ z x) -
        inner ℝ w z * (inner ℝ u x * inner ℝ v x) -
        inner ℝ u v * (inner ℝ w x * inner ℝ z x) + inner ℝ u v * inner ℝ w z) := by
    funext x
    dsimp [centeredQuadratic]
    ring
  rw [he]
  have h₁ := integrable_inner_four u v w z
  have h₂ := ((memLp_inner_mul_inner u v).integrable (by norm_num)).const_mul (inner ℝ w z)
  have h₃ := ((memLp_inner_mul_inner w z).integrable (by norm_num)).const_mul (inner ℝ u v)
  have ha := integral_add ((h₁.sub h₂).sub h₃) (integrable_const (inner ℝ u v * inner ℝ w z))
  have hs₁ := integral_sub (h₁.sub h₂) h₃
  have hs₂ := integral_sub h₁ h₂
  simp only [Pi.sub_apply] at ha hs₁ hs₂
  rw [ha, hs₁, hs₂, integral_const_mul, integral_const_mul,
    integral_inner_four, integral_inner_mul_inner, integral_inner_mul_inner]
  simp
  ring

/-- The centered quadratic coordinate in the actual Gaussian Hilbert space. -/
def centeredQuadraticLp (u v : E) : Lp ℝ 2 (stdGaussian E) :=
  (memLp_centeredQuadratic u v).toLp (centeredQuadratic u v)

theorem centeredQuadraticLp_coe (u v : E) :
    centeredQuadraticLp u v =ᵐ[stdGaussian E] centeredQuadratic u v :=
  (memLp_centeredQuadratic u v).coeFn_toLp

theorem inner_centeredQuadraticLp (u v w z : E) :
    inner ℝ (centeredQuadraticLp u v) (centeredQuadraticLp w z) =
      inner ℝ u w * inner ℝ v z + inner ℝ u z * inner ℝ v w := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, centeredQuadratic u v x * centeredQuadratic w z x ∂stdGaussian E := by
      apply integral_congr_ae
      filter_upwards [centeredQuadraticLp_coe u v, centeredQuadraticLp_coe w z] with x hx hy
      rw [hx, hy, real_inner_comm]
      rfl
    _ = _ := integral_centeredQuadratic_mul u v w z

/-- Finite centered quadratic Gaussian chaos with coefficient matrix B. -/
def quadraticChaos {ι : Type*} [Fintype ι] (b : ι → E) (B : ι → ι → ℝ) :
    Lp ℝ 2 (stdGaussian E) :=
  ∑ i, ∑ j, B i j • centeredQuadraticLp (b i) (b j)

/-- The covariance formula includes nonsymmetric matrices, so the eventual
transport estimate does not require an unproved Hessian symmetry premise. -/
theorem inner_quadraticChaos {ι : Type*} [Fintype ι] (b : ι → E)
    (hb : Orthonormal ℝ b) (B C : ι → ι → ℝ) :
    inner ℝ (quadraticChaos b B) (quadraticChaos b C) =
      ∑ i, ∑ j, B i j * (C i j + C j i) := by
  classical
  simp only [quadraticChaos, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, inner_centeredQuadraticLp, orthonormal_iff_ite.mp hb]
  simp only [mul_add, Finset.sum_add_distrib]
  simp
  rw [Finset.sum_comm (f := fun i j => C i j * B j i)]
  simp only [mul_comm]

/-- Exact centered quadratic energy, before imposing matrix symmetry. -/
theorem quadraticChaos_norm_sq {ι : Type*} [Fintype ι] (b : ι → E)
    (hb : Orthonormal ℝ b) (B : ι → ι → ℝ) :
    ‖quadraticChaos b B‖ ^ 2 = ∑ i, ∑ j, B i j * (B i j + B j i) := by
  rw [← real_inner_self_eq_norm_sq, inner_quadraticChaos b hb]

/-- The quadratic energy is at most twice the squared Hilbert--Schmidt norm,
with no matrix symmetry assumption. -/
theorem quadraticChaos_norm_sq_le {ι : Type*} [Fintype ι] (b : ι → E)
    (hb : Orthonormal ℝ b) (B : ι → ι → ℝ) :
    ‖quadraticChaos b B‖ ^ 2 ≤ 2 * ∑ i, ∑ j, (B i j) ^ 2 := by
  rw [quadraticChaos_norm_sq b hb]
  calc
    _ ≤ ∑ i, ∑ j, ((B i j)^2 + ((B i j)^2 + (B j i)^2) / 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      nlinarith [sq_nonneg (B i j - B j i)]
    _ = _ := by
      simp only [← Finset.sum_div, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => (B j i)^2)]
      ring

/-- Symmetric matrices attain the exact quadratic-chaos energy. -/
theorem quadraticChaos_norm_sq_of_symmetric {ι : Type*} [Fintype ι] (b : ι → E)
    (hb : Orthonormal ℝ b) (B : ι → ι → ℝ) (hB : ∀ i j, B i j = B j i) :
    ‖quadraticChaos b B‖ ^ 2 = 2 * ∑ i, ∑ j, (B i j) ^ 2 := by
  rw [quadraticChaos_norm_sq b hb, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hB i j]
  ring

/-- Product of coordinates from the two independent actual Gaussian blocks. -/
def mixedCoordinate (u v : E) : E × E → ℝ :=
  fun z => inner ℝ u z.1 * inner ℝ v z.2

theorem memLp_mixedCoordinate (u v : E) :
    MemLp (mixedCoordinate u v) 2 ((stdGaussian E).prod (stdGaussian E)) := by
  apply (memLp_two_iff_integrable_sq (by unfold mixedCoordinate; fun_prop)).mpr
  have hu := (IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ u) 2 (by norm_num)).integrable_sq
  have hv := (IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ v) 2 (by norm_num)).integrable_sq
  simpa only [mixedCoordinate, mul_pow, innerSL_apply_apply] using hu.mul_prod hv

def mixedCoordinateLp (u v : E) : Lp ℝ 2 ((stdGaussian E).prod (stdGaussian E)) :=
  (memLp_mixedCoordinate u v).toLp (mixedCoordinate u v)

theorem mixedCoordinateLp_coe (u v : E) :
    mixedCoordinateLp u v =ᵐ[(stdGaussian E).prod (stdGaussian E)] mixedCoordinate u v :=
  (memLp_mixedCoordinate u v).coeFn_toLp

theorem inner_mixedCoordinateLp (u v w z : E) :
    inner ℝ (mixedCoordinateLp u v) (mixedCoordinateLp w z) =
      inner ℝ u w * inner ℝ v z := by
  rw [L2.inner_def]
  calc
    _ = ∫ a, (inner ℝ u a.1 * inner ℝ w a.1) *
        (inner ℝ v a.2 * inner ℝ z a.2) ∂(stdGaussian E).prod (stdGaussian E) := by
      apply integral_congr_ae
      filter_upwards [mixedCoordinateLp_coe u v, mixedCoordinateLp_coe w z] with a ha hb
      rw [ha, hb, real_inner_comm]
      change mixedCoordinate u v a * mixedCoordinate w z a = _
      dsimp [mixedCoordinate]
      ring
    _ = _ := by
      rw [integral_prod_mul (fun x => inner ℝ u x * inner ℝ w x)
        (fun x => inner ℝ v x * inner ℝ z x), integral_inner_mul_inner, integral_inner_mul_inner]

/-- Actual mixed momentum/auxiliary Gaussian chaos. -/
def mixedChaos {ι : Type*} [Fintype ι] (b : ι → E) (B : ι → ι → ℝ) :
    Lp ℝ 2 ((stdGaussian E).prod (stdGaussian E)) :=
  ∑ i, ∑ j, B i j • mixedCoordinateLp (b i) (b j)

theorem inner_mixedChaos {ι : Type*} [Fintype ι] (b : ι → E)
    (hb : Orthonormal ℝ b) (B C : ι → ι → ℝ) :
    inner ℝ (mixedChaos b B) (mixedChaos b C) = ∑ i, ∑ j, B i j * C i j := by
  classical
  simp only [mixedChaos, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, inner_mixedCoordinateLp, orthonormal_iff_ite.mp hb]
  simp [mul_comm]

theorem mixedChaos_norm_sq {ι : Type*} [Fintype ι] (b : ι → E)
    (hb : Orthonormal ℝ b) (B : ι → ι → ℝ) :
    ‖mixedChaos b B‖ ^ 2 = ∑ i, ∑ j, (B i j) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_mixedChaos b hb]
  simp only [pow_two]

/-- Lift the centered quadratic chaos without changing the auxiliary block. -/
def liftedQuadraticChaos {ι : Type*} [Fintype ι] (b : ι → E) (B : ι → ι → ℝ) :
    Lp ℝ 2 ((stdGaussian E).prod (stdGaussian E)) :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst (quadraticChaos b B)

theorem inner_liftedQuadratic_mixedCoordinate (u v w z : E) :
    inner ℝ (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst
      (measurePreserving_fst (ν := stdGaussian E)) (centeredQuadraticLp u v))
      (mixedCoordinateLp w z) = 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ a, (centeredQuadratic u v a.1 * inner ℝ w a.1) * inner ℝ z a.2
        ∂(stdGaussian E).prod (stdGaussian E) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_compMeasurePreserving (centeredQuadraticLp u v)
        (measurePreserving_fst (ν := stdGaussian E)),
        measurePreserving_fst.quasiMeasurePreserving.ae (centeredQuadraticLp_coe u v),
        mixedCoordinateLp_coe w z] with a ha hb hc
      change inner ℝ (Lp.compMeasurePreserving Prod.fst measurePreserving_fst
        (centeredQuadraticLp u v) a) (mixedCoordinateLp w z a) = _
      rw [ha, Function.comp_apply, hb, hc, real_inner_comm]
      change centeredQuadratic u v a.1 * mixedCoordinate w z a = _
      dsimp [mixedCoordinate]
      ring
    _ = 0 := by
      rw [integral_prod_mul (fun x => centeredQuadratic u v x * inner ℝ w x)
        (fun x => inner ℝ z x)]
      have hz := integral_strongDual_stdGaussian (innerSL ℝ z)
      change (∫ x, inner ℝ z x ∂stdGaussian E) = 0 at hz
      rw [hz, mul_zero]

/-- The centered quadratic and mixed chaoses are orthogonal under the actual
product Gaussian law. -/
theorem inner_liftedQuadraticChaos_mixedChaos {ι : Type*} [Fintype ι]
    (b : ι → E) (B C : ι → ι → ℝ) :
    inner ℝ (liftedQuadraticChaos b B) (mixedChaos b C) = 0 := by
  simp only [liftedQuadraticChaos, quadraticChaos, mixedChaos, map_sum, map_smul,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    inner_liftedQuadratic_mixedCoordinate, mul_zero, Finset.sum_const_zero]

/-- The exact two-chaos decomposition of the microscopic Hamiltonian term. -/
def hamiltonianChaos {ι : Type*} [Fintype ι] (b : ι → E) (B : ι → ι → ℝ)
    (s n : ℝ) : Lp ℝ 2 ((stdGaussian E).prod (stdGaussian E)) :=
  -s • liftedQuadraticChaos b B + n • mixedChaos b B

theorem hamiltonianChaos_norm_sq_le {ι : Type*} [Fintype ι] (b : ι → E)
    (hb : Orthonormal ℝ b) (B : ι → ι → ℝ) (s n : ℝ) :
    ‖hamiltonianChaos b B s n‖ ^ 2 ≤ (2 * s ^ 2 + n ^ 2) * ∑ i, ∑ j, (B i j)^2 := by
  have hq := quadraticChaos_norm_sq_le b hb B
  have hm := mixedChaos_norm_sq b hb B
  have hn : ‖liftedQuadraticChaos b B‖ = ‖quadraticChaos b B‖ :=
    (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst).norm_map _
  have ho := inner_liftedQuadraticChaos_mixedChaos b B B
  simp only [hamiltonianChaos, norm_add_sq_real, real_inner_smul_left, real_inner_smul_right,
    ho, mul_zero, add_zero, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, neg_sq, hn, hm]
  nlinarith [mul_le_mul_of_nonneg_left hq (sq_nonneg s)]

end AcceleratedLogConcave.Kinetic.ConditionalContraction
