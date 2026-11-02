/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Multivariate Gaussian Bakry-Emery Instance

Concrete finite-dimensional Gaussian data for the Stage N1 multivariate
Bakry-Emery construction.
-/

import AcceleratedLogConcave.External.MarkovSemigroups.Instances.WorkInProgress.Euclidean
import AcceleratedLogConcave.External.MarkovSemigroups.Instances.WorkInProgress.EuclideanEntropyDecay
import AcceleratedLogConcave.External.MarkovSemigroups.Instances.WorkInProgress.EuclideanStein
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Probability.Distributions.Gaussian.Real

-- Compatibility with the upstream elaborator; this does not change kernel checking.
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Set Real ProbabilityTheory

noncomputable section

attribute [local simp] Function.comp_def Pi.mul_def Pi.add_def Pi.smul_def

/-! ### General lemmas (Mathlib-PR candidates)

Two facts of independent interest, stated at full generality. Both are extracted
from the Gaussian Bakry-Émery instance work but mention only Mathlib notions.
-/

/-- A non-degenerate real Gaussian measure has full topological support: every
nonempty open set has positive measure.

Follows from `volume ≪ gaussianReal` (the Gaussian density is everywhere positive)
together with the open-positivity of Lebesgue measure. Mathlib has no `IsOpenPosMeasure`
instance for `gaussianReal`; this is a clean upstream candidate. -/
theorem gaussianReal_isOpenPosMeasure (μ : ℝ) {v : NNReal} (hv : v ≠ 0) :
    (gaussianReal μ v).IsOpenPosMeasure :=
  (gaussianReal_absolutelyContinuous' μ hv).isOpenPosMeasure

/-- For a full-support measure (`IsOpenPosMeasure`), a continuous function that
satisfies a bound almost everywhere satisfies it everywhere. This is the order
analogue of `MeasureTheory.Measure.eq_of_ae_eq` (which lives in `OpenPos.lean`,
where only the `=` versions are provided). Upstream candidate. -/
theorem Continuous.le_of_ae_le {X : Type*} [TopologicalSpace X]
    {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    {m : MeasurableSpace X} {μ : Measure X} [μ.IsOpenPosMeasure]
    {f g : X → α} (hf : Continuous f) (hg : Continuous g)
    (hae : f ≤ᵐ[μ] g) : ∀ x, f x ≤ g x := by
  intro x
  by_contra hlt
  rw [not_le] at hlt
  have h0 : μ {y | g y < f y} = 0 := by
    have h := ae_iff.mp hae
    simpa only [not_le] using h
  exact (isOpen_lt hg hf).measure_ne_zero μ ⟨x, hlt⟩ h0

namespace GaussianFin

open scoped BigOperators ContDiff

variable {n : ℕ}

/-- The standard Gaussian product measure on `Fin n → ℝ`. -/
def γFin (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => Gaussian1D.γ)

instance instIsProbabilityMeasureγFin (n : ℕ) : IsProbabilityMeasure (γFin n) := by
  unfold γFin
  infer_instance

/-- The 1D standard Gaussian has full support (special case of
`gaussianReal_isOpenPosMeasure`). -/
instance instIsOpenPosMeasureγ : Gaussian1D.γ.IsOpenPosMeasure :=
  gaussianReal_isOpenPosMeasure 0 (by norm_num)

/-- The multivariate standard Gaussian `γFin n` has full support
(product of full-support factors). -/
instance instIsOpenPosMeasureγFin (n : ℕ) : (γFin n).IsOpenPosMeasure := by
  unfold γFin
  infer_instance

/-- For a continuous `f`, an a.e. lower bound `ε ≤ f` w.r.t. the full-support
measure `γFin n` upgrades to a pointwise (everywhere) lower bound. -/
theorem le_of_ae_le_of_continuous {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : Continuous f)
    {ε : ℝ} (hae : ∀ᵐ y ∂γFin n, ε ≤ f y) : ∀ x, ε ≤ f x :=
  Continuous.le_of_ae_le continuous_const hf hae

theorem measurePreserving_piFinSuccAbove_γFin {n : ℕ} (i : Fin (n + 1)) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i)
      (γFin (n + 1)) (Gaussian1D.γ.prod (γFin n)) := by
  simpa [γFin] using
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => Gaussian1D.γ) i)

theorem integral_γFin_succAbove {n : ℕ} (i : Fin (n + 1))
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Integrable f (γFin (n + 1))) :
    ∫ x, f x ∂γFin (n + 1) =
      ∫ s, ∫ y, f (i.insertNth s y) ∂γFin n ∂Gaussian1D.γ := by
  let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have he : MeasurePreserving e (γFin (n + 1)) (Gaussian1D.γ.prod (γFin n)) :=
    measurePreserving_piFinSuccAbove_γFin (n := n) i
  have hcomp : Integrable (f ∘ e.symm) (Gaussian1D.γ.prod (γFin n)) := by
    exact
      (he.symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding e.symm)).2 hf
  calc
    ∫ x, f x ∂γFin (n + 1)
      = ∫ p : ℝ × (Fin n → ℝ), f (e.symm p) ∂(Gaussian1D.γ.prod (γFin n)) := by
          simpa using
            (he.integral_comp' (g := fun p : ℝ × (Fin n → ℝ) => f (e.symm p)))
    _ = ∫ s, ∫ y, f (i.insertNth s y) ∂γFin n ∂Gaussian1D.γ := by
          simpa [e, Fin.insertNthEquiv] using
            (integral_prod (f := fun p : ℝ × (Fin n → ℝ) => f (e.symm p)) hcomp)

/-- The affine Mehler shift on `(Fin n → ℝ)`. -/
def ouShiftFin (t : ℝ) (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => exp (-t) * x i + sqrt (1 - exp (-2 * t)) * y i

theorem ouShiftFin_insertNth {n : ℕ} (i : Fin (n + 1)) (t s u : ℝ)
    (x y : Fin n → ℝ) :
    ouShiftFin t (i.insertNth s x) (i.insertNth u y) =
      i.insertNth (exp (-t) * s + sqrt (1 - exp (-2 * t)) * u) (ouShiftFin t x y) := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp [ouShiftFin]
  · rcases Fin.exists_succAbove_eq hji with ⟨k, rfl⟩
    simp [ouShiftFin]

/-- The multivariate Ornstein-Uhlenbeck semigroup via the Mehler formula. -/
def ouSemigroupFin (t : ℝ) (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => ∫ y, f (ouShiftFin t x y) ∂γFin n

theorem ouSemigroupFin_insertNth_eq {n : ℕ} (t : ℝ) {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf_meas : Measurable f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M)
    (i : Fin (n + 1)) (s : ℝ) (x : Fin n → ℝ) :
    ouSemigroupFin t f (i.insertNth s x) =
      ∫ u, ∫ y, f (i.insertNth (exp (-t) * s + sqrt (1 - exp (-2 * t)) * u) (ouShiftFin t x y))
        ∂γFin n ∂Gaussian1D.γ := by
  let g : (Fin (n + 1) → ℝ) → ℝ := fun z => f (ouShiftFin t (i.insertNth s x) z)
  have hcont_shift : Continuous (fun z : Fin (n + 1) → ℝ => ouShiftFin t (i.insertNth s x) z) := by
    continuity
  have hg_meas : Measurable g := hf_meas.comp hcont_shift.measurable
  have hg_int : Integrable g (γFin (n + 1)) := by
    refine Integrable.mono' (integrable_const M) hg_meas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun z => hM (ouShiftFin t (i.insertNth s x) z))
  unfold ouSemigroupFin
  simpa [g, ouShiftFin_insertNth] using
    (integral_γFin_succAbove (n := n) (i := i) (f := g) hg_int)

def sectionInputFin (t : ℝ) {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ)
    (i : Fin (n + 1)) (x : Fin n → ℝ) : ℝ → ℝ :=
  fun r => ∫ y, f (i.insertNth r (ouShiftFin t x y)) ∂γFin n

theorem ouSemigroupFin_section_eq_ouSemigroup
    {n : ℕ} (t : ℝ) {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf_meas : Measurable f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M)
    (i : Fin (n + 1)) (x : Fin n → ℝ) :
    (fun s => ouSemigroupFin t f (i.insertNth s x)) =
      Gaussian1D.ouSemigroup t (sectionInputFin t f i x) := by
  funext s
  rw [ouSemigroupFin_insertNth_eq (n := n) (t := t) (hf_meas := hf_meas) (hM := hM) i s x]
  simp [Gaussian1D.ouSemigroup, sectionInputFin]

/-- Coordinate partial derivative along the `i`-th standard basis vector. -/
def partialDeriv (i : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- Second coordinate derivative along the `i`-th standard basis vector. -/
def secondPartial (i : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ (partialDeriv i f) x (Pi.single i 1)

private theorem secondPartial_eq (i : Fin n) (f : (Fin n → ℝ) → ℝ) :
    secondPartial i f = partialDeriv i (partialDeriv i f) := rfl

attribute [local simp] secondPartial_eq

/-- The multivariate carré du champ: sum of squared coordinate derivatives. -/
def ouGammaFin (f g : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => ∑ i : Fin n, partialDeriv i f x * partialDeriv i g x

/-- Core test functions for the finite-dimensional Gaussian OU semigroup.

We require:
- `C^∞` regularity;
- a global bound on the function values;
- a uniform global bound on all coordinate first and second partials.

This is the direct finite-dimensional analogue of `Gaussian1D.IsCore`. -/
def IsCoreFin (f : (Fin n → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∃ M : ℝ,
    ∀ x, ‖f x‖ ≤ M ∧
      (∀ i : Fin n, ‖partialDeriv i f x‖ ≤ M) ∧
      ∀ i : Fin n, ‖secondPartial i f x‖ ≤ M

theorem IsCoreFin.contDiff {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    ContDiff ℝ ∞ f := hf.1

theorem IsCoreFin.bound_exists {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M := by
  obtain ⟨_, M, hM⟩ := hf
  exact ⟨M, fun x => (hM x).1⟩

theorem IsCoreFin.continuous {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    Continuous f := hf.contDiff.continuous

theorem IsCoreFin.measurable {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    Measurable f := hf.continuous.measurable

theorem IsCoreFin.stronglyMeasurable {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    StronglyMeasurable f := hf.continuous.stronglyMeasurable

theorem IsCoreFin.partial_contDiff {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (i : Fin n) :
    ContDiff ℝ ∞ (partialDeriv i f) := by
  unfold partialDeriv
  simpa using (hf.contDiff.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem IsCoreFin.partial_differentiable {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (i : Fin n) :
    Differentiable ℝ (partialDeriv i f) :=
  (hf.partial_contDiff i).differentiable (by simp)

theorem IsCoreFin.partial_continuous {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (i : Fin n) :
    Continuous (partialDeriv i f) := (hf.partial_contDiff i).continuous

theorem IsCoreFin.partial_measurable {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (i : Fin n) :
    Measurable (partialDeriv i f) := (hf.partial_continuous i).measurable

theorem IsCoreFin.partial_stronglyMeasurable {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f)
    (i : Fin n) : StronglyMeasurable (partialDeriv i f) :=
  (hf.partial_continuous i).stronglyMeasurable

theorem IsCoreFin.secondPartial_contDiff {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (i : Fin n) :
    ContDiff ℝ ∞ (secondPartial i f) := by
  change ContDiff ℝ ∞ (fun x => (fderiv ℝ (partialDeriv i f) x) (Pi.single i 1))
  exact ((hf.partial_contDiff i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem IsCoreFin.secondPartial_continuous {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f)
    (i : Fin n) : Continuous (secondPartial i f) :=
  (hf.secondPartial_contDiff i).continuous

theorem IsCoreFin.secondPartial_measurable {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f)
    (i : Fin n) : Measurable (secondPartial i f) :=
  (hf.secondPartial_continuous i).measurable

theorem IsCoreFin.secondPartial_stronglyMeasurable {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f)
    (i : Fin n) : StronglyMeasurable (secondPartial i f) :=
  (hf.secondPartial_continuous i).stronglyMeasurable

/-- Restrict a multivariate function to the `i`-th coordinate line through `x`. -/
def coordSection (i : Fin n) (x : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) : ℝ → ℝ :=
  fun s => f (Function.update x i s)

theorem section_contDiff {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (i : Fin n) (x : Fin n → ℝ) :
    ContDiff ℝ ∞ (coordSection i x f) := by
  unfold coordSection
  exact hf.comp (contDiff_update ∞ x i)

theorem section_hasDerivAt {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (i : Fin n) (x : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (coordSection i x f)
      (partialDeriv i f (Function.update x i s)) s := by
  unfold coordSection partialDeriv
  have h_update := hasDerivAt_update x i s
  have h_f : HasFDerivAt f (fderiv ℝ f (Function.update x i s)) (Function.update x i s) :=
    ((hf.differentiable (by simp)).differentiableAt).hasFDerivAt
  simpa [partialDeriv] using h_f.comp_hasDerivAt s h_update

theorem section_deriv {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (i : Fin n) (x : Fin n → ℝ) :
    deriv (coordSection i x f) = fun s => partialDeriv i f (Function.update x i s) := by
  funext s
  exact (section_hasDerivAt hf i x s).deriv

theorem partialDeriv_update_hasDerivAt {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f)
    (i : Fin n) (x : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun t => partialDeriv i f (Function.update x i t))
      (secondPartial i f (Function.update x i s)) s := by
  change HasDerivAt (fun s => partialDeriv i f (Function.update x i s))
    (secondPartial i f (Function.update x i s)) s
  have h_update := hasDerivAt_update x i s
  have h_f : HasFDerivAt (partialDeriv i f)
      (fderiv ℝ (partialDeriv i f) (Function.update x i s))
      (Function.update x i s) :=
    ((hf.partial_differentiable i).differentiableAt).hasFDerivAt
  convert h_f.comp_hasDerivAt s h_update using 1 <;> rfl

theorem section_secondDeriv {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f)
    (i : Fin n) (x : Fin n → ℝ) :
    deriv (deriv (coordSection i x f)) = fun s => secondPartial i f (Function.update x i s) := by
  funext s
  rw [section_deriv hf.contDiff i x]
  exact (partialDeriv_update_hasDerivAt hf i x s).deriv

/-- `C¹`-order companion of `section_contDiff`: the coordinate section of a
`ContDiff ℝ 1` function is again `ContDiff ℝ 1`. Used for telescope iterates
which are only `C¹` (not `C^∞`). -/
theorem section_contDiff_one {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (i : Fin n) (x : Fin n → ℝ) :
    ContDiff ℝ 1 (coordSection i x f) := by
  unfold coordSection
  exact hf.comp (contDiff_update 1 x i)

/-- `C¹`-order companion of `section_hasDerivAt`: the derivative of the
coordinate section is the coordinate partial. Only differentiability of `f`
is needed. -/
theorem section_hasDerivAt_of_differentiable {f : (Fin n → ℝ) → ℝ}
    (hf : Differentiable ℝ f) (i : Fin n) (x : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (coordSection i x f)
      (partialDeriv i f (Function.update x i s)) s := by
  unfold coordSection partialDeriv
  have h_update := hasDerivAt_update x i s
  have h_f : HasFDerivAt f (fderiv ℝ f (Function.update x i s))
      (Function.update x i s) :=
    (hf (Function.update x i s)).hasFDerivAt
  simpa [partialDeriv] using h_f.comp_hasDerivAt s h_update

/-- `C¹`-order companion of `section_deriv`. -/
theorem section_deriv_of_differentiable {f : (Fin n → ℝ) → ℝ}
    (hf : Differentiable ℝ f) (i : Fin n) (x : Fin n → ℝ) :
    deriv (coordSection i x f) =
      fun s => partialDeriv i f (Function.update x i s) := by
  funext s
  exact (section_hasDerivAt_of_differentiable hf i x s).deriv

theorem stein_partialDeriv_ouShiftFin {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : IsCoreFin f) (t : ℝ) (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    ∫ y, y i * partialDeriv i f (ouShiftFin t x y) ∂γFin (n + 1) =
      sqrt (1 - exp (-2 * t)) * ouSemigroupFin t (secondPartial i f) x := by
  have hf_core : IsCoreFin f := hf
  obtain ⟨_, M, hM⟩ := hf
  have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0).1
  let a : ℝ := exp (-t)
  let b : ℝ := sqrt (1 - exp (-2 * t))
  let x' : Fin n → ℝ := i.removeNth x
  let φ : ℝ × (Fin n → ℝ) → (Fin (n + 1) → ℝ) := fun p =>
    Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i
      (a * x i + b * p.1) (ouShiftFin t x' p.2)
  let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  let G : ℝ × (Fin n → ℝ) → ℝ := fun p => secondPartial i f (φ p)
  let H : ℝ × (Fin n → ℝ) → ℝ := fun p => p.1 * partialDeriv i f (φ p)
  have hφ_meas : Measurable φ := by
    refine measurable_pi_iff.2 ?_
    intro j
    by_cases hji : j = i
    · subst hji
      simpa [φ, a, b] using
        ((measurable_const).add ((measurable_const).mul measurable_fst))
    · rcases Fin.exists_succAbove_eq hji with ⟨k, rfl⟩
      simpa [φ, x', a, b, ouShiftFin] using
        ((measurable_const).add ((measurable_const).mul ((measurable_pi_apply k).comp measurable_snd)))
  have hG_int : Integrable G (Gaussian1D.γ.prod (γFin n)) := by
    refine Integrable.mono' (integrable_const M) ?_ ?_
    · exact ((IsCoreFin.secondPartial_measurable hf_core i).comp hφ_meas).aestronglyMeasurable
    · filter_upwards with p
      exact (hM (φ p)).2.2 i
  have hH_int : Integrable H (Gaussian1D.γ.prod (γFin n)) := by
    refine Integrable.mono'
      ((((memLp_id_gaussianReal 1).integrable le_rfl).abs.comp_fst (γFin n)).const_mul M)
      ?_ ?_
    · refine ((measurable_fst.mul ?_).aestronglyMeasurable)
      exact (IsCoreFin.partial_measurable hf_core i).comp hφ_meas
    · filter_upwards with p
      have hp : ‖partialDeriv i f (φ p)‖ ≤ M := (hM (φ p)).2.1 i
      calc
        ‖H p‖
          = |p.1| * ‖partialDeriv i f (φ p)‖ := by simp [H, norm_mul, Real.norm_eq_abs]
        _ ≤ |p.1| * M := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
        _ = M * |p.1| := by ring
  have hsplit :
      ∫ y, y i * partialDeriv i f (ouShiftFin t x y) ∂γFin (n + 1) =
        ∫ p, H p ∂(Gaussian1D.γ.prod (γFin n)) := by
    have he : MeasurePreserving e (γFin (n + 1)) (Gaussian1D.γ.prod (γFin n)) :=
      measurePreserving_piFinSuccAbove_γFin (n := n) i
    have hEq : (fun y : Fin (n + 1) → ℝ => y i * partialDeriv i f (ouShiftFin t x y)) = H ∘ e := by
      funext y
      have hx : i.insertNth (x i) x' = x := by
        simp [x']
      have hy : i.insertNth (y i) (i.removeNth y) = y := by
        simp
      change y i * partialDeriv i f (ouShiftFin t x y) = H (y i, i.removeNth y)
      rw [← hx, ← hy, ouShiftFin_insertNth]
      simp [a, b, H, φ]
    calc
      ∫ y, y i * partialDeriv i f (ouShiftFin t x y) ∂γFin (n + 1)
        = ∫ y, (H ∘ e) y ∂γFin (n + 1) := by rw [hEq]
      _ = ∫ p, H p ∂(Gaussian1D.γ.prod (γFin n)) := he.integral_comp' H
  have hGsplit :
      ∫ p, G p ∂(Gaussian1D.γ.prod (γFin n)) = ouSemigroupFin t (secondPartial i f) x := by
    have he : MeasurePreserving e (γFin (n + 1)) (Gaussian1D.γ.prod (γFin n)) :=
      measurePreserving_piFinSuccAbove_γFin (n := n) i
    have hEq : (fun y : Fin (n + 1) → ℝ => secondPartial i f (ouShiftFin t x y)) = G ∘ e := by
      funext y
      have hx : i.insertNth (x i) x' = x := by
        simp [x']
      have hy : i.insertNth (y i) (i.removeNth y) = y := by
        simp
      change secondPartial i f (ouShiftFin t x y) = G (y i, i.removeNth y)
      rw [← hx, ← hy, ouShiftFin_insertNth]
      simp [a, b, G, φ]
    calc
      ∫ p, G p ∂(Gaussian1D.γ.prod (γFin n))
        = ∫ y, G (e y) ∂γFin (n + 1) := by symm; exact he.integral_comp' G
      _ = ∫ y, (G ∘ e) y ∂γFin (n + 1) := by rfl
      _ = ∫ y, secondPartial i f (ouShiftFin t x y) ∂γFin (n + 1) := by rw [← hEq]
      _ = ouSemigroupFin t (secondPartial i f) x := rfl
  have hb_le_one : |b| ≤ 1 := by
    have hb_nn : 0 ≤ b := by simp [b]
    rw [abs_of_nonneg hb_nn]
    by_cases hrad : 0 ≤ 1 - exp (-2 * t)
    · have hsqrt : sqrt (1 - exp (-2 * t)) ≤ 1 := by
        refine (Real.sqrt_le_iff).2 ?_
        constructor
        · positivity
        · have hexp_nonneg : 0 ≤ exp (-2 * t) := by positivity
          linarith
      simpa [b] using hsqrt
    · have hzero : sqrt (1 - exp (-2 * t)) = 0 :=
        Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hrad)
      simp [b, hzero]
  have hinner :
      ∀ z : Fin n → ℝ,
        ∫ u, H (u, z) ∂Gaussian1D.γ =
          b * ∫ u, secondPartial i f (i.insertNth (a * x i + b * u) (ouShiftFin t x' z))
            ∂Gaussian1D.γ := by
    intro z
    let base : Fin (n + 1) → ℝ := i.insertNth 0 (ouShiftFin t x' z)
    let g : ℝ → ℝ := fun u => coordSection i base (partialDeriv i f) (a * x i + b * u)
    have hg_C1 : ContDiff ℝ 1 g := by
      have hsec : ContDiff ℝ ∞ (coordSection i base (partialDeriv i f)) :=
        section_contDiff (IsCoreFin.partial_contDiff hf_core i) i base
      have h_aff : ContDiff ℝ 1 (fun u : ℝ => a * x i + b * u) := by
        exact contDiff_const.add (contDiff_const.mul contDiff_id)
      simpa [g] using (hsec.of_le (by simp)).comp h_aff
    have hg_bd : ∀ u, |g u| ≤ M := by
      intro u
      simp [g, coordSection]
      rw [← Real.norm_eq_abs]
      exact (hM _).2.1 i
    have hderiv_eq :
        ∀ u, deriv g u = b * secondPartial i f (Function.update base i (a * x i + b * u)) := by
      intro u
      have h_aff : HasDerivAt (fun s : ℝ => a * x i + b * s) b u := by
        simpa [a, b] using ((hasDerivAt_id u).const_mul b).const_add (a * x i)
      have h_part :
          HasDerivAt (coordSection i base (partialDeriv i f))
            (secondPartial i f (Function.update base i (a * x i + b * u))) (a * x i + b * u) :=
        section_hasDerivAt (IsCoreFin.partial_contDiff hf_core i) i base (a * x i + b * u)
      simpa [g, mul_comm] using (h_part.comp u h_aff).deriv
    have hg'_bd : ∀ u, |deriv g u| ≤ M := by
      intro u
      rw [hderiv_eq u, abs_mul]
      have hsec_bd : |secondPartial i f (Function.update base i (a * x i + b * u))| ≤ M := by
        rw [← Real.norm_eq_abs]
        exact (hM _).2.2 i
      calc
        |b| * |secondPartial i f (Function.update base i (a * x i + b * u))|
          ≤ 1 * M := mul_le_mul hb_le_one hsec_bd (abs_nonneg _) (by positivity)
        _ = M := by ring
    have hstein := Gaussian1D.stein_identity_standard hg_C1 hg_bd hg'_bd
    have hφ_update : ∀ u : ℝ,
        φ (u, z) = Function.update base i (a * x i + b * u) := by
      intro u
      ext j
      by_cases hji : j = i
      · subst hji
        simp [φ, base]
      · rcases Fin.exists_succAbove_eq hji with ⟨k, rfl⟩
        simp [φ, base, x', ouShiftFin]
    rw [show (fun u => H (u, z)) = fun u => u * g u from by
      funext u
      simp [H, g, coordSection, hφ_update u]]
    rw [hstein, show deriv g = fun u => b * secondPartial i f (Function.update base i (a * x i + b * u))
      from by funext u; exact hderiv_eq u, integral_const_mul]
    congr 2
    ext u
    rw [← hφ_update u]
  have houter :
      ∫ p, H p ∂(Gaussian1D.γ.prod (γFin n)) =
        b * ∫ p, G p ∂(Gaussian1D.γ.prod (γFin n)) := by
    calc
      ∫ p, H p ∂(Gaussian1D.γ.prod (γFin n))
        = ∫ z, ∫ u, H (u, z) ∂Gaussian1D.γ ∂γFin n := by
            rw [integral_prod_symm H hH_int]
      _
        = ∫ z, b * ∫ u,
            G (u, z) ∂Gaussian1D.γ ∂γFin n := by
                refine integral_congr_ae (Filter.Eventually.of_forall hinner)
      _ = b * ∫ z, ∫ u,
            G (u, z)
              ∂Gaussian1D.γ ∂γFin n := by
                rw [integral_const_mul]
      _ = b * ∫ p, G p ∂(Gaussian1D.γ.prod (γFin n)) := by
            rw [integral_prod_symm G hG_int]
  calc
    ∫ y, y i * partialDeriv i f (ouShiftFin t x y) ∂γFin (n + 1)
      = ∫ p, H p ∂(Gaussian1D.γ.prod (γFin n)) := hsplit
    _ = b * ∫ p, G p ∂(Gaussian1D.γ.prod (γFin n)) := houter
    _ = b * ouSemigroupFin t (secondPartial i f) x := by rw [hGsplit]

theorem sum_smul_single (v : Fin n → ℝ) :
    (∑ i : Fin n, v i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) = v := by
  ext j
  simp [Pi.single_apply]

theorem fderiv_apply_eq_sum_partial {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (x v : Fin n → ℝ) :
    fderiv ℝ f x v = ∑ i : Fin n, v i * partialDeriv i f x := by
  have hdiff : DifferentiableAt ℝ f x := (hf.differentiable (by simp)).differentiableAt
  calc
    fderiv ℝ f x v = (fderiv ℝ f x) (∑ i : Fin n, v i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
      rw [sum_smul_single]
    _ = ∑ i : Fin n, (fderiv ℝ f x) (v i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
      rw [map_sum]
    _ = ∑ i : Fin n, v i * partialDeriv i f x := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [ContinuousLinearMap.map_smul]
      simp [partialDeriv, smul_eq_mul]

theorem IsCoreFin.exists_lipschitzWith {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    ∃ C : NNReal, LipschitzWith C f := by
  obtain ⟨hf_smooth, M, hM⟩ := hf
  have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0).1
  refine ⟨⟨n * M, by positivity⟩, ?_⟩
  refine lipschitzWith_of_nnnorm_fderiv_le (hf_smooth.differentiable (by simp)) ?_
  intro x
  have hbound : ‖fderiv ℝ f x‖ ≤ n * M := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
    intro v
    have hcoord : ∀ i : Fin n, ‖v i‖ ≤ ‖v‖ := by
      intro i
      exact norm_le_pi_norm v i
    have hvsum : ∑ i : Fin n, ‖v i‖ ≤ n * ‖v‖ := by
      calc
        ∑ i : Fin n, ‖v i‖ ≤ ∑ i : Fin n, ‖v‖ := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact hcoord i
        _ = n * ‖v‖ := by simp [nsmul_eq_mul]
    calc
      ‖fderiv ℝ f x v‖ = ‖∑ i : Fin n, v i * partialDeriv i f x‖ := by
        rw [fderiv_apply_eq_sum_partial hf_smooth]
      _ ≤ ∑ i : Fin n, ‖v i * partialDeriv i f x‖ := by
            simpa using (norm_sum_le Finset.univ (fun i : Fin n => v i * partialDeriv i f x))
      _ = ∑ i : Fin n, ‖v i‖ * ‖partialDeriv i f x‖ := by
            congr with i
            rw [norm_mul]
      _ ≤ ∑ i : Fin n, ‖v i‖ * M := by
            refine Finset.sum_le_sum ?_
            intro i hi
            gcongr
            exact (hM x).2.1 i
      _ = (∑ i : Fin n, ‖v i‖) * M := by rw [Finset.sum_mul]
      _ ≤ (n * ‖v‖) * M := by
            exact mul_le_mul_of_nonneg_right hvsum hM_nn
      _ = (n * M) * ‖v‖ := by ring
  exact_mod_cast hbound

theorem hasLineDerivAt_ouSemigroupFin
    (t : ℝ) {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (x v : Fin n → ℝ) :
    HasLineDerivAt ℝ (ouSemigroupFin t f)
      (exp (-t) * ∫ y, ∑ i : Fin n, v i * partialDeriv i f (ouShiftFin t x y) ∂γFin n) x v := by
  set a := exp (-t)
  set b := sqrt (1 - exp (-2 * t))
  set F : ℝ → (Fin n → ℝ) → ℝ := fun s y => f (ouShiftFin t (x + s • v) y)
  set F' : ℝ → (Fin n → ℝ) → ℝ := fun s y =>
    a * ∑ i : Fin n, v i * partialDeriv i f (ouShiftFin t (x + s • v) y)
  have hs : Set.Ioo (-1 : ℝ) 1 ∈ nhds (0 : ℝ) :=
    Ioo_mem_nhds (by linarith) zero_lt_one
  obtain ⟨hf_smooth, M, hM⟩ := hf
  have hf_core : IsCoreFin f := ⟨hf_smooth, M, hM⟩
  have hF_meas : ∀ s, AEStronglyMeasurable (F s) (γFin n) := by
    intro s
    have hcont_shift : Continuous (fun y : Fin n → ℝ => ouShiftFin t (x + s • v) y) := by
      continuity
    exact ((hf_smooth.continuous.comp hcont_shift).measurable.aestronglyMeasurable)
  have hF_int : Integrable (F 0) (γFin n) := by
    refine Integrable.mono' (integrable_const M) (hF_meas 0) ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    simpa [F, a, b] using (hM (ouShiftFin t x y)).1
  have hF'_meas : AEStronglyMeasurable (F' 0) (γFin n) := by
    have hmeas_term : ∀ i : Fin n,
        Measurable (fun y : Fin n → ℝ => v i * partialDeriv i f (ouShiftFin t x y)) := by
      intro i
      have hcont_shift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
        continuity
      exact measurable_const.mul (((hf_core.partial_continuous i).comp hcont_shift).measurable)
    have hmeas_sum : Measurable (fun y : Fin n → ℝ =>
        ∑ i : Fin n, v i * partialDeriv i f (ouShiftFin t x y)) :=
      Finset.measurable_sum Finset.univ (fun i _ => hmeas_term i)
    simpa [F', a] using (measurable_const.mul hmeas_sum).aestronglyMeasurable
  have h_bound_int : Integrable (fun _ : Fin n → ℝ => |a| * (n * M * ‖v‖)) (γFin n) :=
    integrable_const _
  have h_bound :
      ∀ᵐ y ∂γFin n, ∀ s ∈ Set.Ioo (-1 : ℝ) 1,
        ‖F' s y‖ ≤ |a| * (n * M * ‖v‖) := by
    refine Filter.Eventually.of_forall ?_
    intro y s hs_mem
    have hvsum : ∑ i : Fin n, ‖v i‖ ≤ n * ‖v‖ := by
      calc
        ∑ i : Fin n, ‖v i‖ ≤ ∑ i : Fin n, ‖v‖ := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact norm_le_pi_norm v i
        _ = n * ‖v‖ := by simp [nsmul_eq_mul]
    have hsum :
        ‖∑ i : Fin n, v i * partialDeriv i f (ouShiftFin t (x + s • v) y)‖ ≤ n * M * ‖v‖ := by
      calc
        ‖∑ i : Fin n, v i * partialDeriv i f (ouShiftFin t (x + s • v) y)‖
            ≤ ∑ i : Fin n, ‖v i * partialDeriv i f (ouShiftFin t (x + s • v) y)‖ := by
                simpa using
                  (norm_sum_le Finset.univ
                    (fun i : Fin n => v i * partialDeriv i f (ouShiftFin t (x + s • v) y)))
        _ = ∑ i : Fin n, ‖v i‖ * ‖partialDeriv i f (ouShiftFin t (x + s • v) y)‖ := by
              congr with i
              rw [norm_mul]
        _ ≤ ∑ i : Fin n, ‖v i‖ * M := by
              refine Finset.sum_le_sum ?_
              intro i hi
              gcongr
              exact (hM (ouShiftFin t (x + s • v) y)).2.1 i
        _ = (∑ i : Fin n, ‖v i‖) * M := by rw [Finset.sum_mul]
        _ ≤ (n * ‖v‖) * M := by
              exact mul_le_mul_of_nonneg_right hvsum ((norm_nonneg _).trans (hM 0).1)
        _ = n * M * ‖v‖ := by ring
    show ‖a * ∑ i : Fin n, v i * partialDeriv i f (ouShiftFin t (x + s • v) y)‖ ≤
        |a| * (n * M * ‖v‖)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left hsum (abs_nonneg a)
  have h_diff :
      ∀ᵐ y ∂γFin n, ∀ s ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt (F · y) (F' s y) s := by
    refine Filter.Eventually.of_forall ?_
    intro y s hs_mem
    have h_inner :
        HasDerivAt (fun u : ℝ => ouShiftFin t (x + u • v) y) (a • v) s := by
      set z : Fin n → ℝ := ouShiftFin t x y
      have h_eq :
          (fun u : ℝ => ouShiftFin t (x + u • v) y) = fun u => z + u • (a • v) := by
        funext u
        ext j
        simp [ouShiftFin, z, a, smul_eq_mul]
        ring
      have hraw : HasDerivAt (fun u : ℝ => z + u • (a • v)) (a • v) s := by
        simpa using (((hasDerivAt_id s).smul_const (a • v)).const_add z)
      rw [h_eq]
      exact hraw
    have h_f :
        HasFDerivAt f (fderiv ℝ f (ouShiftFin t (x + s • v) y))
          (ouShiftFin t (x + s • v) y) :=
      ((hf_smooth.differentiable (by simp)).differentiableAt).hasFDerivAt
    have h_comp := h_f.comp_hasDerivAt s h_inner
    have htarget :
        (fderiv ℝ f (ouShiftFin t (x + s • v) y)) (a • v) =
          a * ∑ i : Fin n, v i * partialDeriv i f (ouShiftFin t (x + s • v) y) := by
      rw [fderiv_apply_eq_sum_partial hf_smooth (ouShiftFin t (x + s • v) y) (a • v)]
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    have hc := h_comp.congr_deriv htarget
    simpa only [Function.comp_def, F, F'] using hc
  obtain ⟨_, h_deriv⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
      (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas h_bound h_bound_int h_diff
  have h_lhs : (fun s => ∫ y, F s y ∂γFin n) = fun s => ouSemigroupFin t f (x + s • v) := rfl
  have h_rhs :
      ∫ y, F' 0 y ∂γFin n =
        exp (-t) * ∫ y, ∑ i : Fin n, v i * partialDeriv i f (ouShiftFin t x y) ∂γFin n := by
    have hF0 :
        (fun y => F' 0 y) =
          (fun y => a * ∑ i : Fin n, v i * partialDeriv i f (ouShiftFin t x y)) := by
      funext y
      simp [F', a]
    rw [hF0, integral_const_mul]
  simpa [HasLineDerivAt, h_lhs, h_rhs]
    using h_deriv

theorem ouSemigroupFin_exists_lipschitzWith
    (t : ℝ) (ht : 0 ≤ t) {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    ∃ C : NNReal, LipschitzWith C (ouSemigroupFin t f) := by
  obtain ⟨C, hC⟩ := hf.exists_lipschitzWith
  obtain ⟨hf_smooth, M, hM⟩ := hf
  have hf_core : IsCoreFin f := ⟨hf_smooth, M, hM⟩
  have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0).1
  have hf_cont : Continuous f := hf_core.continuous
  refine ⟨C, LipschitzWith.of_dist_le_mul ?_⟩
  intro x x'
  have hsec_int : ∀ x₀ : Fin n → ℝ, Integrable (fun y => f (ouShiftFin t x₀ y)) (γFin n) := by
    intro x₀
    refine Integrable.mono' (integrable_const M) ?_ ?_
    · have hcont_shift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x₀ y) := by
        continuity
      exact ((hf_cont.comp hcont_shift).measurable.aestronglyMeasurable)
    · exact Filter.Eventually.of_forall (fun y => (hM (ouShiftFin t x₀ y)).1)
  have hdiff_int :
      Integrable (fun y => f (ouShiftFin t x y) - f (ouShiftFin t x' y)) (γFin n) := by
    refine Integrable.mono' (integrable_const (2 * M)) ?_ ?_
    · have hcontx : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by continuity
      have hcontx' : Continuous (fun y : Fin n → ℝ => ouShiftFin t x' y) := by continuity
      exact (((hf_cont.comp hcontx).sub (hf_cont.comp hcontx')).measurable.aestronglyMeasurable)
    · refine Filter.Eventually.of_forall ?_
      intro y
      calc
        ‖f (ouShiftFin t x y) - f (ouShiftFin t x' y)‖
            ≤ ‖f (ouShiftFin t x y)‖ + ‖f (ouShiftFin t x' y)‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (hM (ouShiftFin t x y)).1 (hM (ouShiftFin t x' y)).1
        _ = 2 * M := by ring
  have hpoint :
      ∀ y : Fin n → ℝ,
        ‖f (ouShiftFin t x y) - f (ouShiftFin t x' y)‖ ≤ (C : ℝ) * ‖x - x'‖ := by
    intro y
    set a := exp (-t)
    have ha_le_one : |a| ≤ 1 := by
      rw [abs_of_nonneg (exp_pos (-t)).le]
      exact Real.exp_le_one_iff.mpr (by linarith)
    have hshift : ouShiftFin t x y - ouShiftFin t x' y = a • (x - x') := by
      ext i
      simp [ouShiftFin, a, Pi.smul_apply, smul_eq_mul]
      ring
    have hmul : |a| * ‖x - x'‖ ≤ ‖x - x'‖ := by
      have hxnn : 0 ≤ ‖x - x'‖ := norm_nonneg _
      nlinarith
    calc
      ‖f (ouShiftFin t x y) - f (ouShiftFin t x' y)‖
          ≤ (C : ℝ) * ‖ouShiftFin t x y - ouShiftFin t x' y‖ := hC.norm_sub_le _ _
      _ = (C : ℝ) * ‖a • (x - x')‖ := by rw [hshift]
      _ = (C : ℝ) * (|a| * ‖x - x'‖) := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ (C : ℝ) * ‖x - x'‖ := by
            gcongr
  have hsub :
      ouSemigroupFin t f x - ouSemigroupFin t f x' =
        ∫ y, f (ouShiftFin t x y) - f (ouShiftFin t x' y) ∂γFin n := by
    unfold ouSemigroupFin
    rw [integral_sub (hsec_int x) (hsec_int x')]
  calc
    dist (ouSemigroupFin t f x) (ouSemigroupFin t f x')
        = ‖∫ y, f (ouShiftFin t x y) - f (ouShiftFin t x' y) ∂γFin n‖ := by
            rw [dist_eq_norm, hsub]
    _ ≤ ∫ y, ‖f (ouShiftFin t x y) - f (ouShiftFin t x' y)‖ ∂γFin n := norm_integral_le_integral_norm _
    _ ≤ ∫ _y, (C : ℝ) * ‖x - x'‖ ∂γFin n := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
          · exact integrable_const _
          · exact Filter.Eventually.of_forall hpoint
    _ = (C : ℝ) * dist x x' := by
          rw [integral_const, dist_eq_norm]
          simp

theorem hasFDerivAt_ouSemigroupFin
    (t : ℝ) (ht : 0 ≤ t) {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (x : Fin n → ℝ) :
    HasFDerivAt (ouSemigroupFin t f)
      (∑ i : Fin n,
        (exp (-t) * ouSemigroupFin t (partialDeriv i f) x) •
          (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
  obtain ⟨C, hC⟩ := ouSemigroupFin_exists_lipschitzWith (n := n) t ht hf
  have hf_core : IsCoreFin f := hf
  let L : (Fin n → ℝ) →L[ℝ] ℝ :=
    ∑ i : Fin n, (exp (-t) * ouSemigroupFin t (partialDeriv i f) x) •
      (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)
  refine hC.hasFDerivAt_of_hasLineDerivAt_of_closure (s := Set.univ) ?_ ?_
  · simp
  · intro v hv
    have hint_term : ∀ i : Fin n,
        Integrable (fun y : Fin n → ℝ => v i * partialDeriv i f (ouShiftFin t x y)) (γFin n) := by
      intro i
      obtain ⟨_, M, hM⟩ := hf
      have hcont_shift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
        continuity
      refine Integrable.mono' (integrable_const (‖v i‖ * M))
        ((measurable_const.mul ((hf_core.partial_continuous i).comp hcont_shift).measurable).aestronglyMeasurable) ?_
      refine Filter.Eventually.of_forall ?_
      intro y
      rw [norm_mul]
      gcongr
      exact (hM (ouShiftFin t x y)).2.1 i
    have hline := hasLineDerivAt_ouSemigroupFin (n := n) t hf x v
    convert hline using 1
    calc
      L v = ∑ i : Fin n, (exp (-t) * ouSemigroupFin t (partialDeriv i f) x) * v i := by
        simp [L, mul_comm]
      _ = exp (-t) * ∑ i : Fin n, v i * ouSemigroupFin t (partialDeriv i f) x := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
      _ = exp (-t) *
            ∑ i : Fin n, v i * ∫ y, partialDeriv i f (ouShiftFin t x y) ∂γFin n := by
              simp [ouSemigroupFin]
      _ = exp (-t) *
            ∑ i : Fin n, ∫ y, v i * partialDeriv i f (ouShiftFin t x y) ∂γFin n := by
              congr 2 with i
              rw [← integral_const_mul]
      _ = exp (-t) *
            ∫ y, ∑ i : Fin n, v i * partialDeriv i f (ouShiftFin t x y) ∂γFin n := by
              rw [integral_finsetSum Finset.univ (fun i _ => hint_term i)]

theorem fderiv_ouSemigroupFin_eq
    (t : ℝ) (ht : 0 ≤ t) {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    fderiv ℝ (ouSemigroupFin t f) =
      fun x =>
        ∑ i : Fin n,
          (exp (-t) * ouSemigroupFin t (partialDeriv i f) x) •
            (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) := by
  funext x
  exact (hasFDerivAt_ouSemigroupFin (n := n) t ht hf x).fderiv

theorem hasDerivAt_coordSection_ouSemigroupFin_C1
    (t : ℝ) {f : (Fin n → ℝ) → ℝ} (hf_C1 : ContDiff ℝ 1 f)
    (i : Fin n) {M : ℝ} (hM0 : ∀ x, ‖f x‖ ≤ M) (hM1 : ∀ x, ‖partialDeriv i f x‖ ≤ M)
    (x : Fin n → ℝ) (s₀ : ℝ) :
    HasDerivAt (fun s => ouSemigroupFin t f (Function.update x i s))
      (exp (-t) * ouSemigroupFin t (partialDeriv i f) (Function.update x i s₀)) s₀ := by
  set a := exp (-t)
  set b := sqrt (1 - exp (-2 * t))
  set F : ℝ → (Fin n → ℝ) → ℝ := fun s y => f (ouShiftFin t (Function.update x i s) y)
  set F' : ℝ → (Fin n → ℝ) → ℝ := fun s y =>
    a * partialDeriv i f (ouShiftFin t (Function.update x i s) y)
  have hs : Set.Ioo (s₀ - 1) (s₀ + 1) ∈ nhds s₀ :=
    Ioo_mem_nhds (sub_lt_self _ zero_lt_one) (lt_add_of_pos_right _ zero_lt_one)
  have hF_meas : ∀ s, AEStronglyMeasurable (F s) (γFin n) := by
    intro s
    have hcont_shift : Continuous (fun y : Fin n → ℝ => ouShiftFin t (Function.update x i s) y) := by
      continuity
    have hmeas : Measurable (fun y => F s y) := (hf_C1.continuous.comp hcont_shift).measurable
    exact hmeas.aestronglyMeasurable
  have hF_int : Integrable (F s₀) (γFin n) := by
    refine Integrable.mono' (integrable_const M) (hF_meas s₀) ?_
    exact Filter.Eventually.of_forall (fun y => hM0 _)
  have hF'_meas : AEStronglyMeasurable (F' s₀) (γFin n) := by
    have hpartial_cont : Continuous (partialDeriv i f) := by
      unfold partialDeriv
      simpa using (hf_C1.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcont_shift : Continuous (fun y : Fin n → ℝ => ouShiftFin t (Function.update x i s₀) y) := by
      continuity
    have hmeas : Measurable (fun y => F' s₀ y) :=
      (measurable_const.mul (hpartial_cont.comp hcont_shift).measurable)
    exact hmeas.aestronglyMeasurable
  have h_bound : ∀ᵐ y ∂γFin n, ∀ s ∈ Set.Ioo (s₀ - 1) (s₀ + 1), ‖F' s y‖ ≤ |a| * M := by
    refine Filter.Eventually.of_forall ?_
    intro y s hs_mem
    show ‖a * partialDeriv i f (ouShiftFin t (Function.update x i s) y)‖ ≤ |a| * M
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |partialDeriv i f (ouShiftFin t (Function.update x i s) y)| ≤ M := by
      rw [← Real.norm_eq_abs]
      exact hM1 _
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg a)
  have h_bound_int : Integrable (fun _ : Fin n → ℝ => |a| * M) (γFin n) := integrable_const _
  have h_diff :
      ∀ᵐ y ∂γFin n, ∀ s ∈ Set.Ioo (s₀ - 1) (s₀ + 1), HasDerivAt (F · y) (F' s y) s := by
    refine Filter.Eventually.of_forall ?_
    intro y s hs_mem
    show HasDerivAt (fun u => f (ouShiftFin t (Function.update x i u) y))
      (a * partialDeriv i f (ouShiftFin t (Function.update x i s) y)) s
    have h_affine : HasDerivAt (fun u : ℝ => a * u + b * y i) a s := by
      simpa [a, b] using (((hasDerivAt_id s).const_mul a).add_const (b * y i))
    set z : Fin n → ℝ := ouShiftFin t x y
    have h_inner_eq :
        (fun u : ℝ => ouShiftFin t (Function.update x i u) y) =
          fun u => Function.update z i (a * u + b * y i) := by
      funext u
      ext j
      by_cases hji : j = i
      · subst hji
        simp [ouShiftFin, z, a, b]
      · simp [ouShiftFin, z, a, b, hji]
    have h_inner :
        HasDerivAt (fun u : ℝ => ouShiftFin t (Function.update x i u) y)
          (Pi.single i a) s := by
      have htmp : HasDerivAt (fun u : ℝ => Function.update z i (a * u + b * y i))
          (Pi.single i a) s := by
        have hraw :=
          (HasFDerivAt.comp s
            (hasFDerivAt_update z (i := i) (a * s + b * y i))
            h_affine.hasFDerivAt).hasDerivAt
        simp only [Function.comp_def] at hraw
        convert hraw using 1
        ext j
        by_cases hji : j = i
        · subst hji
          simp [ContinuousLinearMap.toSpanSingleton_apply]
        · simp [hji, ContinuousLinearMap.toSpanSingleton_apply]
      rw [h_inner_eq]
      exact htmp
    have h_f :
        HasFDerivAt f (fderiv ℝ f (ouShiftFin t (Function.update x i s) y))
          (ouShiftFin t (Function.update x i s) y) :=
      ((hf_C1.differentiable (by simp)).differentiableAt).hasFDerivAt
    have h_comp := h_f.comp_hasDerivAt s h_inner
    have htarget :
        (fderiv ℝ f (ouShiftFin t (Function.update x i s) y)) (Pi.single i a) =
          a * partialDeriv i f (ouShiftFin t (Function.update x i s) y) := by
      rw [partialDeriv]
      have hsingle : Pi.single i a = a • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
        ext j
        by_cases hji : j = i
        · subst hji
          simp
        · simp [Pi.single_eq_of_ne hji]
      rw [hsingle, ContinuousLinearMap.map_smul]
      simp [smul_eq_mul]
    have hc := h_comp.congr_deriv htarget
    simpa only [Function.comp_def, F, F'] using hc
  obtain ⟨_, h_deriv⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
      (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas h_bound h_bound_int h_diff
  have h_lhs : (fun s => ∫ y, F s y ∂γFin n) =
      fun s => ouSemigroupFin t f (Function.update x i s) := rfl
  have h_rhs :
      ∫ y, F' s₀ y ∂γFin n =
        a * ouSemigroupFin t (partialDeriv i f) (Function.update x i s₀) := by
    rw [show (fun y => F' s₀ y) =
        (fun y => a * partialDeriv i f (ouShiftFin t (Function.update x i s₀) y)) from rfl]
    rw [integral_const_mul]
    rfl
  simpa [h_lhs, h_rhs, a] using h_deriv

theorem partialDeriv_ouSemigroupFin_eq
    (t : ℝ) (ht : 0 ≤ t) {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f)
    (i : Fin n) :
    partialDeriv i (ouSemigroupFin t f) =
      fun x => exp (-t) * ouSemigroupFin t (partialDeriv i f) x := by
  funext x
  rw [partialDeriv, (hasFDerivAt_ouSemigroupFin (n := n) t ht hf x).fderiv]
  have hsum :
      (∑ j : Fin n,
        ((exp (-t) * ouSemigroupFin t (partialDeriv j f) x) •
          (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) (Pi.single i (1 : ℝ))) =
      exp (-t) * ouSemigroupFin t (partialDeriv i f) x := by
    rw [Finset.sum_eq_single i]
    · simp [ContinuousLinearMap.proj_apply]
    · intro j _ hji
      simp [ContinuousLinearMap.proj_apply, hji]
    · simp [ContinuousLinearMap.proj_apply]
  simpa using hsum

theorem section_deriv_ouSemigroupFin_eq {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f)
    (t : ℝ) (i : Fin n) (x : Fin n → ℝ) :
    deriv (fun s => ouSemigroupFin t f (Function.update x i s)) =
      fun s => exp (-t) * ouSemigroupFin t (partialDeriv i f) (Function.update x i s) := by
  have hf_core : IsCoreFin f := hf
  have hf_cont : ContDiff ℝ ∞ f := hf.contDiff
  obtain ⟨_, M, hM⟩ := hf
  funext s
  exact (hasDerivAt_coordSection_ouSemigroupFin_C1 (t := t)
    (hf_C1 := hf_cont.of_le (by simp))
    (i := i)
    (hM0 := fun z => (hM z).1)
    (hM1 := fun z => (hM z).2.1 i)
    (x := x) (s₀ := s)).deriv

theorem section_secondDeriv_ouSemigroupFin_eq {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f)
    (t : ℝ) (i : Fin n) (x : Fin n → ℝ) :
    deriv (deriv (fun s => ouSemigroupFin t f (Function.update x i s))) =
      fun s => exp (-2 * t) * ouSemigroupFin t (secondPartial i f) (Function.update x i s) := by
  have hf_core : IsCoreFin f := hf
  have hf_partial : ContDiff ℝ ∞ (partialDeriv i f) := hf.partial_contDiff i
  obtain ⟨_, M, hM⟩ := hf
  funext s
  have h :=
    hasDerivAt_coordSection_ouSemigroupFin_C1 (t := t)
      (hf_C1 := hf_partial.of_le (by simp))
      (i := i)
      (hM0 := fun z => (hM z).2.1 i)
      (hM1 := fun z => (hM z).2.2 i)
      (x := x) (s₀ := s)
  calc
    deriv (deriv (fun s => ouSemigroupFin t f (Function.update x i s))) s
        = deriv (fun s => exp (-t) * ouSemigroupFin t (partialDeriv i f) (Function.update x i s)) s := by
            rw [section_deriv_ouSemigroupFin_eq hf_core t i x]
    _ = exp (-2 * t) * ouSemigroupFin t (secondPartial i f) (Function.update x i s) := by
          have hscaled : HasDerivAt
              (fun s => exp (-t) * ouSemigroupFin t (partialDeriv i f) (Function.update x i s))
              (exp (-t) * (exp (-t) * ouSemigroupFin t (secondPartial i f) (Function.update x i s))) s := by
            simpa [secondPartial] using h.const_mul (exp (-t))
          have hdscaled := hscaled.deriv
          rw [show exp (-2 * t) = exp (-t) * exp (-t) by
            rw [show (-2 * t : ℝ) = -t + -t by ring, exp_add]]
          simpa [mul_assoc] using hdscaled

theorem IsCoreFin.section_isCore {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f)
    (i : Fin n) (x : Fin n → ℝ) :
    Gaussian1D.IsCore (coordSection i x f) := by
  obtain ⟨hf_smooth, M, hM⟩ := hf
  have hf_core : IsCoreFin f := ⟨hf_smooth, M, hM⟩
  have hsection : ContDiff ℝ ∞ (coordSection i x f) := by
    exact section_contDiff hf_smooth i x
  refine ⟨hsection, ⟨M, fun s => ?_⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [coordSection] using (hM (Function.update x i s)).1
  · rw [section_deriv hf_smooth i x]
    simpa [coordSection] using (hM (Function.update x i s)).2.1 i
  · rw [section_secondDeriv hf_core i x]
    simpa [coordSection] using (hM (Function.update x i s)).2.2 i

theorem IsCoreFin.integrable {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    Integrable f (γFin n) := by
  obtain ⟨M, hM⟩ := hf.bound_exists
  refine Integrable.mono' (integrable_const M) hf.stronglyMeasurable.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall hM

theorem integrable_abs_eval_γFin (i : Fin n) :
    Integrable (fun x : Fin n → ℝ => |x i|) (γFin n) := by
  have heval : MeasurePreserving (Function.eval i) (γFin n) Gaussian1D.γ := by
    simpa [γFin] using
      (MeasureTheory.measurePreserving_eval (μ := fun _ : Fin n => Gaussian1D.γ) i)
  simpa [Function.comp, Function.eval] using
    heval.integrable_comp_of_integrable (((memLp_id_gaussianReal 1).integrable le_rfl).abs)

theorem integrable_sum_abs_γFin :
    Integrable (fun x : Fin n → ℝ => ∑ i : Fin n, |x i|) (γFin n) := by
  simpa using
    (integrable_finsetSum (s := Finset.univ)
      (f := fun i (x : Fin n → ℝ) => |x i|)
      (fun i _ => integrable_abs_eval_γFin (n := n) i))

theorem IsCoreFin.integrable_partial_mul {f g : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (hg : IsCoreFin g) (i : Fin n) :
    Integrable (fun x => partialDeriv i f x * partialDeriv i g x) (γFin n) := by
  obtain ⟨hf_smooth, Mf, hfM⟩ := hf
  obtain ⟨hg_smooth, Mg, hgM⟩ := hg
  have hf_core : IsCoreFin f := ⟨hf_smooth, Mf, hfM⟩
  have hg_core : IsCoreFin g := ⟨hg_smooth, Mg, hgM⟩
  let M := Mf * Mg
  have hmf : Measurable (partialDeriv i f) :=
    (hf_core.partial_continuous i).measurable
  have hmg : Measurable (partialDeriv i g) :=
    (hg_core.partial_continuous i).measurable
  refine Integrable.mono' (integrable_const M)
    (hmf.mul hmg).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  rw [norm_mul]
  have hMf_nn : 0 ≤ Mf := (norm_nonneg _).trans (hfM 0).1
  exact mul_le_mul ((hfM x).2.1 i) ((hgM x).2.1 i) (norm_nonneg _) hMf_nn

theorem IsCoreFin.integrable_sq {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    Integrable (fun x => (f x) ^ 2) (γFin n) := by
  obtain ⟨M, hM⟩ := hf.bound_exists
  refine Integrable.mono' (integrable_const (M ^ 2))
    ((hf.measurable.pow_const 2).aemeasurable.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hx : |f x| ≤ M := by
    rw [← Real.norm_eq_abs]
    exact hM x
  have hx2 : (f x) ^ 2 ≤ M ^ 2 := by
    have : |f x| ^ 2 ≤ M ^ 2 := by nlinarith [abs_nonneg (f x)]
    rwa [sq_abs] at this
  have hnorm : ‖M ^ 2‖ = M ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  linarith

/-- Dirichlet energy for the multivariate Gaussian candidate. -/
def ouEnergyFin (f g : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ x, ouGammaFin f g x ∂γFin n

@[simp] theorem partialDeriv_const (i : Fin n) (c : ℝ) :
    partialDeriv i (fun _ : Fin n → ℝ => c) = 0 := by
  funext x
  simp [partialDeriv]

@[simp] theorem secondPartial_const (i : Fin n) (c : ℝ) :
    secondPartial i (fun _ : Fin n → ℝ => c) = 0 := by
  funext x
  simp [secondPartial]

theorem IsCoreFin_const (c : ℝ) : IsCoreFin (fun _ : Fin n → ℝ => c) := by
  refine ⟨contDiff_const, ⟨‖c‖, fun x => ?_⟩⟩
  refine ⟨le_rfl, ?_, ?_⟩
  · intro i
    simp [partialDeriv_const]
  · intro i
    simp [partialDeriv]

theorem IsCoreFin_add {f g : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (hg : IsCoreFin g) :
    IsCoreFin (f + g) := by
  obtain ⟨hf_smooth, Mf, hfM⟩ := hf
  obtain ⟨hg_smooth, Mg, hgM⟩ := hg
  refine ⟨hf_smooth.add hg_smooth, ⟨Mf + Mg, fun x => ?_⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · calc
      ‖(f + g) x‖ = ‖f x + g x‖ := rfl
      _ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
      _ ≤ Mf + Mg := add_le_add (hfM x).1 (hgM x).1
  · intro i
    have hdf : DifferentiableAt ℝ f x := (hf_smooth.differentiable (by simp)).differentiableAt
    have hdg : DifferentiableAt ℝ g x := (hg_smooth.differentiable (by simp)).differentiableAt
    unfold partialDeriv
    rw [fderiv_add hdf hdg, add_apply]
    calc
      ‖partialDeriv i f x + partialDeriv i g x‖
        ≤ ‖partialDeriv i f x‖ + ‖partialDeriv i g x‖ := norm_add_le _ _
      _ ≤ Mf + Mg := add_le_add ((hfM x).2.1 i) ((hgM x).2.1 i)
  · intro i
    have hf_core : IsCoreFin f := ⟨hf_smooth, Mf, hfM⟩
    have hg_core : IsCoreFin g := ⟨hg_smooth, Mg, hgM⟩
    have hpartialf_smooth : ContDiff ℝ ∞ (partialDeriv i f) := hf_core.partial_contDiff i
    have hpartialg_smooth : ContDiff ℝ ∞ (partialDeriv i g) := hg_core.partial_contDiff i
    have hdf' : DifferentiableAt ℝ (partialDeriv i f) x := (hpartialf_smooth.differentiable (by simp)).differentiableAt
    have hdg' : DifferentiableAt ℝ (partialDeriv i g) x := (hpartialg_smooth.differentiable (by simp)).differentiableAt
    unfold secondPartial
    have hpartial_add : partialDeriv i (f + g) = fun y => partialDeriv i f y + partialDeriv i g y := by
      funext y
      have hdfy : DifferentiableAt ℝ f y := (hf_smooth.differentiable (by simp)).differentiableAt
      have hdgy : DifferentiableAt ℝ g y := (hg_smooth.differentiable (by simp)).differentiableAt
      unfold partialDeriv
      rw [fderiv_add hdfy hdgy, add_apply]
    rw [hpartial_add]
    change ‖(fderiv ℝ ((partialDeriv i f) + (partialDeriv i g)) x) (Pi.single i 1)‖ ≤ Mf + Mg
    rw [fderiv_add hdf' hdg', add_apply]
    calc
      ‖secondPartial i f x + secondPartial i g x‖
        ≤ ‖secondPartial i f x‖ + ‖secondPartial i g x‖ := norm_add_le _ _
      _ ≤ Mf + Mg := add_le_add ((hfM x).2.2 i) ((hgM x).2.2 i)

theorem IsCoreFin_smul (c : ℝ) {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    IsCoreFin (c • f) := by
  obtain ⟨hf_smooth, M, hM⟩ := hf
  refine ⟨hf_smooth.const_smul c, ⟨‖c‖ * M, fun x => ?_⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · calc
      ‖(c • f) x‖ = ‖c * f x‖ := by simp [Pi.smul_apply]
      _ = ‖c‖ * ‖f x‖ := norm_mul _ _
      _ ≤ ‖c‖ * M := mul_le_mul_of_nonneg_left (hM x).1 (norm_nonneg _)
  · intro i
    have hsmul : fderiv ℝ (c • f) x = c • fderiv ℝ f x := by
      exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) (R := ℝ) (f := f) (c := c)) x
    rw [partialDeriv, hsmul]
    simp only [smul_eq_mul, smul_apply]
    calc
      ‖c * partialDeriv i f x‖ = ‖c‖ * ‖partialDeriv i f x‖ := norm_mul _ _
      _ ≤ ‖c‖ * M := mul_le_mul_of_nonneg_left ((hM x).2.1 i) (norm_nonneg _)
  · intro i
    rw [secondPartial]
    have hpartial :
        partialDeriv i (c • f) = fun y => c * partialDeriv i f y := by
      funext y
      have hsmul : fderiv ℝ (c • f) y = c • fderiv ℝ f y := by
        exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) (R := ℝ) (f := f) (c := c)) y
      rw [partialDeriv, hsmul]
      simp [partialDeriv, smul_eq_mul, smul_apply]
    rw [hpartial]
    change ‖(fderiv ℝ (c • partialDeriv i f) x) (Pi.single i 1)‖ ≤ ‖c‖ * M
    have hsmul : fderiv ℝ (c • partialDeriv i f) x =
        c • fderiv ℝ (partialDeriv i f) x := by
      exact congrFun
        (fderiv_const_smul_field (𝕜 := ℝ) (R := ℝ) (f := partialDeriv i f) (c := c)) x
    rw [hsmul]
    simp only [smul_apply, smul_eq_mul]
    calc
      ‖c * secondPartial i f x‖ = ‖c‖ * ‖secondPartial i f x‖ := norm_mul _ _
      _ ≤ ‖c‖ * M := mul_le_mul_of_nonneg_left ((hM x).2.2 i) (norm_nonneg _)

theorem partialDeriv_mul (i : Fin n) {f g : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    partialDeriv i (f * g) = fun x => partialDeriv i f x * g x + f x * partialDeriv i g x := by
  funext x
  have hdf : DifferentiableAt ℝ f x := (hf.differentiable (by simp)).differentiableAt
  have hdg : DifferentiableAt ℝ g x := (hg.differentiable (by simp)).differentiableAt
  unfold partialDeriv
  rw [fderiv_mul hdf hdg, add_apply]
  simp only [smul_apply, smul_eq_mul]
  ring

theorem IsCoreFin_mul {f g : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (hg : IsCoreFin g) :
    IsCoreFin (f * g) := by
  obtain ⟨hf_smooth, Mf, hfM⟩ := hf
  obtain ⟨hg_smooth, Mg, hgM⟩ := hg
  refine ⟨hf_smooth.mul hg_smooth, ⟨Mf * Mg + 2 * (Mf * Mg) + Mf * Mg, fun x => ?_⟩⟩
  have hMf_nn : 0 ≤ Mf := (norm_nonneg _).trans (hfM 0).1
  have hMg_nn : 0 ≤ Mg := (norm_nonneg _).trans (hgM 0).1
  refine ⟨?_, ?_, ?_⟩
  · calc
      ‖(f * g) x‖ = ‖f x * g x‖ := rfl
      _ = ‖f x‖ * ‖g x‖ := norm_mul _ _
      _ ≤ Mf * Mg := mul_le_mul (hfM x).1 (hgM x).1 (norm_nonneg _) hMf_nn
      _ ≤ Mf * Mg + 2 * (Mf * Mg) + Mf * Mg := by nlinarith
  · intro i
    rw [partialDeriv_mul i hf_smooth hg_smooth]
    have h1 : ‖partialDeriv i f x * g x‖ ≤ Mf * Mg := by
      rw [norm_mul]
      exact mul_le_mul ((hfM x).2.1 i) (hgM x).1 (norm_nonneg _) hMf_nn
    have h2 : ‖f x * partialDeriv i g x‖ ≤ Mf * Mg := by
      rw [norm_mul]
      exact mul_le_mul (hfM x).1 ((hgM x).2.1 i) (norm_nonneg _) hMf_nn
    calc
      ‖partialDeriv i f x * g x + f x * partialDeriv i g x‖
        ≤ ‖partialDeriv i f x * g x‖ + ‖f x * partialDeriv i g x‖ := norm_add_le _ _
      _ ≤ Mf * Mg + Mf * Mg := add_le_add h1 h2
      _ ≤ Mf * Mg + 2 * (Mf * Mg) + Mf * Mg := by nlinarith
  · intro i
    have hdf : DifferentiableAt ℝ f x := (hf_smooth.differentiable (by simp)).differentiableAt
    have hdg : DifferentiableAt ℝ g x := (hg_smooth.differentiable (by simp)).differentiableAt
    have hf_core : IsCoreFin f := ⟨hf_smooth, Mf, hfM⟩
    have hg_core : IsCoreFin g := ⟨hg_smooth, Mg, hgM⟩
    have hpartialf_smooth : ContDiff ℝ ∞ (partialDeriv i f) := hf_core.partial_contDiff i
    have hpartialg_smooth : ContDiff ℝ ∞ (partialDeriv i g) := hg_core.partial_contDiff i
    have hdf' : DifferentiableAt ℝ (partialDeriv i f) x :=
      (hpartialf_smooth.differentiable (by simp)).differentiableAt
    have hdg' : DifferentiableAt ℝ (partialDeriv i g) x :=
      (hpartialg_smooth.differentiable (by simp)).differentiableAt
    rw [secondPartial, partialDeriv_mul i hf_smooth hg_smooth]
    set u : (Fin n → ℝ) → ℝ := fun y => partialDeriv i f y * g y
    set v : (Fin n → ℝ) → ℝ := fun y => f y * partialDeriv i g y
    change ‖(fderiv ℝ (u + v) x) (Pi.single i 1)‖ ≤ Mf * Mg + 2 * (Mf * Mg) + Mf * Mg
    have hadd : fderiv ℝ (u + v) x = fderiv ℝ u x + fderiv ℝ v x := by
      simpa [u, v] using fderiv_add (hdf'.mul hdg) (hdf.mul hdg')
    rw [hadd]
    rw [add_apply]
    have hmul1' : fderiv ℝ ((partialDeriv i f) * g) x =
        partialDeriv i f x • fderiv ℝ g x + g x • fderiv ℝ (partialDeriv i f) x := by
      exact fderiv_mul hdf' hdg
    have hmul1 :
        (fderiv ℝ (fun y => partialDeriv i f y * g y) x) (Pi.single i 1) =
          secondPartial i f x * g x + partialDeriv i f x * partialDeriv i g x := by
      rw [show (fun y => partialDeriv i f y * g y) = ((partialDeriv i f) * g) by rfl, hmul1',
        add_apply]
      simp [secondPartial, partialDeriv, smul_eq_mul]
      ring
    have hmul2' : fderiv ℝ (f * partialDeriv i g) x =
        f x • fderiv ℝ (partialDeriv i g) x + partialDeriv i g x • fderiv ℝ f x := by
      exact fderiv_mul hdf hdg'
    have hmul2 :
        (fderiv ℝ (fun y => f y * partialDeriv i g y) x) (Pi.single i 1) =
          partialDeriv i f x * partialDeriv i g x + f x * secondPartial i g x := by
      rw [show (fun y => f y * partialDeriv i g y) = (f * partialDeriv i g) by rfl, hmul2',
        add_apply]
      simp [secondPartial, partialDeriv, smul_eq_mul]
      ring
    rw [hmul1, hmul2]
    have e1 : ‖secondPartial i f x * g x‖ ≤ Mf * Mg := by
      rw [norm_mul]
      exact mul_le_mul ((hfM x).2.2 i) (hgM x).1 (norm_nonneg _) hMf_nn
    have e2 : ‖partialDeriv i f x * partialDeriv i g x‖ ≤ Mf * Mg := by
      rw [norm_mul]
      exact mul_le_mul ((hfM x).2.1 i) ((hgM x).2.1 i) (norm_nonneg _) hMf_nn
    have e3 : ‖f x * secondPartial i g x‖ ≤ Mf * Mg := by
      rw [norm_mul]
      exact mul_le_mul (hfM x).1 ((hgM x).2.2 i) (norm_nonneg _) hMf_nn
    calc
      ‖secondPartial i f x * g x + partialDeriv i f x * partialDeriv i g x +
          (partialDeriv i f x * partialDeriv i g x + f x * secondPartial i g x)‖
        ≤ ‖secondPartial i f x * g x‖ + ‖partialDeriv i f x * partialDeriv i g x‖ +
            (‖partialDeriv i f x * partialDeriv i g x‖ + ‖f x * secondPartial i g x‖) := by
              exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
      _ ≤ Mf * Mg + Mf * Mg + (Mf * Mg + Mf * Mg) := by gcongr
      _ = Mf * Mg + 2 * (Mf * Mg) + Mf * Mg := by ring

@[simp] theorem partialDeriv_smul (i : Fin n) (c : ℝ) {f : (Fin n → ℝ) → ℝ} :
    partialDeriv i (c • f) = fun x => c * partialDeriv i f x := by
  funext x
  have hsmul : fderiv ℝ (c • f) x = c • fderiv ℝ f x := by
    exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) (R := ℝ) (f := f) (c := c)) x
  rw [partialDeriv, hsmul]
  simp [partialDeriv, smul_eq_mul, smul_apply]

theorem partialDeriv_add (i : Fin n) {f g : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    partialDeriv i (f + g) = fun x => partialDeriv i f x + partialDeriv i g x := by
  funext x
  have hdf : DifferentiableAt ℝ f x := (hf.differentiable (by simp)).differentiableAt
  have hdg : DifferentiableAt ℝ g x := (hg.differentiable (by simp)).differentiableAt
  unfold partialDeriv
  rw [fderiv_add hdf hdg, add_apply]

/-- Chain rule for the coordinate partial of a real power: when `f` is `C^∞` and
nowhere zero, `∂ᵢ(fᵣ) = r · f^{r-1} · ∂ᵢf`. -/
theorem partialDeriv_rpow (i : Fin n) {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfne : ∀ x, f x ≠ 0) (r : ℝ) :
    partialDeriv i (fun z => f z ^ r) = fun x => (r * f x ^ (r - 1)) * partialDeriv i f x := by
  funext x
  have hfx : HasFDerivAt f (fderiv ℝ f x) x :=
    (hf.differentiable (by simp)).differentiableAt.hasFDerivAt
  have h := hfx.rpow_const (p := r) (Or.inl (hfne x))
  unfold partialDeriv
  rw [h.fderiv, smul_apply, smul_eq_mul]

/-- **Strictly-positive `rpow` closure for `IsCoreFin`.** If `f` is a Gaussian
core function bounded below by some `ε > 0`, then `x ↦ f x ^ r` is again core, for
any real exponent `r`. On `[ε, M]` the function `t ↦ t^c` and its first two
derivatives are bounded, so all `C^∞_b` data of `f^r` follow from the chain and
product rules. Discharges the `IsCore_rpow_pos_strict` field for the Gaussian
instance. -/
theorem IsCoreFin_rpow_pos {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f)
    {ε : ℝ} (hε : 0 < ε) (hpos : ∀ x, ε ≤ f x) (r : ℝ) :
    IsCoreFin (fun x => f x ^ r) := by
  obtain ⟨hf_smooth, M, hM⟩ := hf
  have hf_core : IsCoreFin f := ⟨hf_smooth, M, hM⟩
  have hfpos : ∀ x, 0 < f x := fun x => lt_of_lt_of_le hε (hpos x)
  have hfne : ∀ x, f x ≠ 0 := fun x => (hfpos x).ne'
  have hfleM : ∀ x, f x ≤ M := fun x =>
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using (hM x).1)
  have hMpos : 0 < M := lt_of_lt_of_le hε ((hpos 0).trans (hfleM 0))
  -- Uniform bound on `f^c` over the orbit, for any exponent `c`.
  have rbd : ∀ (c : ℝ) (x), f x ^ c ≤ ε ^ c + M ^ c := by
    intro c x
    rcases le_total 0 c with hc | hc
    · have h := Real.rpow_le_rpow (hfpos x).le (hfleM x) hc
      have := Real.rpow_nonneg hε.le c
      linarith
    · have h := Real.rpow_le_rpow_of_nonpos hε (hpos x) hc
      have := Real.rpow_nonneg hMpos.le c
      linarith
  have hsmooth : ContDiff ℝ ∞ (fun x => f x ^ r) := hf_smooth.rpow_const_of_ne hfne
  set C1 : ℝ := |r| * (ε ^ (r - 1) + M ^ (r - 1)) * M with hC1
  set C2 : ℝ := |r| * |r - 1| * (ε ^ (r - 1 - 1) + M ^ (r - 1 - 1)) * M ^ 2 with hC2
  set B0 : ℝ := ε ^ r + M ^ r with hB0
  have hC1nn : 0 ≤ C1 := by positivity
  have hC2nn : 0 ≤ C2 := by positivity
  have hB0nn : 0 ≤ B0 := by positivity
  refine ⟨hsmooth, ⟨B0 + C1 + (C1 + C2), fun x => ⟨?_, ?_, ?_⟩⟩⟩
  · -- value bound
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (hfpos x) r)]
    have := rbd r x
    linarith
  · -- first-partial bound
    intro i
    rw [partialDeriv_rpow i hf_smooth hfne r, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos (hfpos x) _)]
    have hb1 : |partialDeriv i f x| ≤ M := by simpa [Real.norm_eq_abs] using (hM x).2.1 i
    have key : |r| * f x ^ (r - 1) * |partialDeriv i f x| ≤ C1 := by
      rw [hC1]
      apply mul_le_mul _ hb1 (abs_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left (rbd (r - 1) x) (abs_nonneg r)
    linarith
  · -- second-partial bound
    intro i
    have hAsmooth : ContDiff ℝ ∞ (fun x => r * f x ^ (r - 1)) :=
      contDiff_const.mul (hf_smooth.rpow_const_of_ne hfne)
    have hBsmooth' : ContDiff ℝ ∞ (partialDeriv i f) := hf_core.partial_contDiff i
    have hform : secondPartial i (fun z => f z ^ r) x
        = r * (r - 1) * f x ^ (r - 1 - 1) * partialDeriv i f x ^ 2
          + r * f x ^ (r - 1) * secondPartial i f x := by
      have hkey : partialDeriv i (fun z => f z ^ r)
          = (fun y => r * f y ^ (r - 1)) * partialDeriv i f := by
        rw [partialDeriv_rpow i hf_smooth hfne r]; rfl
      have hAd : partialDeriv i (fun y => r * f y ^ (r - 1))
          = fun y => r * ((r - 1) * f y ^ (r - 1 - 1) * partialDeriv i f y) := by
        have hrw : (fun y => r * f y ^ (r - 1)) = (r : ℝ) • (fun y => f y ^ (r - 1)) := by
          funext y; simp [Pi.smul_apply, smul_eq_mul]
        rw [hrw, partialDeriv_smul, partialDeriv_rpow i hf_smooth hfne (r - 1)]
      show partialDeriv i (partialDeriv i (fun z => f z ^ r)) x = _
      rw [hkey, partialDeriv_mul i hAsmooth hBsmooth', hAd]
      show r * ((r - 1) * f x ^ (r - 1 - 1) * partialDeriv i f x) * partialDeriv i f x
          + r * f x ^ (r - 1) * secondPartial i f x
          = r * (r - 1) * f x ^ (r - 1 - 1) * partialDeriv i f x ^ 2
            + r * f x ^ (r - 1) * secondPartial i f x
      ring
    rw [hform, Real.norm_eq_abs]
    have hb1 : |partialDeriv i f x| ≤ M := by simpa [Real.norm_eq_abs] using (hM x).2.1 i
    have hb2 : |secondPartial i f x| ≤ M := by simpa [Real.norm_eq_abs] using (hM x).2.2 i
    have hsq : partialDeriv i f x ^ 2 ≤ M ^ 2 :=
      sq_le_sq' (abs_le.mp hb1).1 (abs_le.mp hb1).2
    have hB : |r * f x ^ (r - 1) * secondPartial i f x| ≤ C1 := by
      rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hfpos x) _), hC1]
      apply mul_le_mul _ hb2 (abs_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left (rbd (r - 1) x) (abs_nonneg r)
    have hA : |r * (r - 1) * f x ^ (r - 1 - 1) * partialDeriv i f x ^ 2| ≤ C2 := by
      have hp1 : |f x ^ (r - 1 - 1)| = f x ^ (r - 1 - 1) :=
        abs_of_pos (Real.rpow_pos_of_pos (hfpos x) _)
      have hp2 : |partialDeriv i f x ^ 2| = partialDeriv i f x ^ 2 :=
        abs_of_nonneg (sq_nonneg _)
      rw [abs_mul, abs_mul, abs_mul, hp1, hp2, hC2]
      have h1 : |r| * |r - 1| * f x ^ (r - 1 - 1) ≤ |r| * |r - 1| * (ε ^ (r - 1 - 1) + M ^ (r - 1 - 1)) :=
        mul_le_mul_of_nonneg_left (rbd (r - 1 - 1) x) (by positivity)
      calc |r| * |r - 1| * f x ^ (r - 1 - 1) * partialDeriv i f x ^ 2
          ≤ |r| * |r - 1| * (ε ^ (r - 1 - 1) + M ^ (r - 1 - 1)) * M ^ 2 := by
            apply mul_le_mul h1 hsq (sq_nonneg _) (by positivity)
        _ = C2 := by rw [hC2]
    calc |r * (r - 1) * f x ^ (r - 1 - 1) * partialDeriv i f x ^ 2 + r * f x ^ (r - 1) * secondPartial i f x|
        ≤ |r * (r - 1) * f x ^ (r - 1 - 1) * partialDeriv i f x ^ 2|
            + |r * f x ^ (r - 1) * secondPartial i f x| := abs_add_le _ _
      _ ≤ C2 + C1 := add_le_add hA hB
      _ ≤ B0 + C1 + (C1 + C2) := by linarith

theorem IsCoreFin.integrable_gamma {f g : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (hg : IsCoreFin g) :
    Integrable (ouGammaFin f g) (γFin n) := by
  convert
    (integrable_finsetSum (s := Finset.univ)
      (f := fun i x => partialDeriv i f x * partialDeriv i g x)
      (fun i _ => hf.integrable_partial_mul hg i)) using 1
  rfl

@[reducible]
def dirichletSpaceFin (n : ℕ) : DirichletSpace (Fin n → ℝ) where
  μ := γFin n
  hμ := inferInstance
  energy := ouEnergyFin
  energy_symm := fun f g => by
    simp [ouEnergyFin, ouGammaFin, mul_comm]
  energy_nonneg := fun f => by
    unfold ouEnergyFin ouGammaFin
    refine integral_nonneg ?_
    intro x
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (partialDeriv i f x))
  IsCore := IsCoreFin
  IsCore_const := IsCoreFin_const
  IsCore_add := fun hf hg => IsCoreFin_add hf hg
  IsCore_smul := fun c _ hf => IsCoreFin_smul c hf
  energy_add_left := fun f₁ f₂ g hf₁ hf₂ hg => by
    have hΓ :
        ouGammaFin (f₁ + f₂) g = fun x => ouGammaFin f₁ g x + ouGammaFin f₂ g x := by
      ext x
      unfold ouGammaFin
      have hsum :
          (fun i : Fin n => partialDeriv i (f₁ + f₂) x * partialDeriv i g x) =
            fun i : Fin n =>
              partialDeriv i f₁ x * partialDeriv i g x +
                partialDeriv i f₂ x * partialDeriv i g x := by
        funext i
        rw [partialDeriv_add i hf₁.contDiff hf₂.contDiff]
        ring
      rw [hsum]
      rw [Finset.sum_add_distrib]
    rw [ouEnergyFin, hΓ, integral_add (hf₁.integrable_gamma hg) (hf₂.integrable_gamma hg)]
    rfl
  energy_smul_left := fun c f g hf hg => by
    have hΓ : ouGammaFin (c • f) g = fun x => c * ouGammaFin f g x := by
      ext x
      unfold ouGammaFin
      simp_rw [partialDeriv_smul]
      rw [Finset.mul_sum]
      congr with i
      ring
    rw [ouEnergyFin, hΓ, integral_const_mul]
    rw [ouEnergyFin]
  energy_const := fun c => by
    simp [ouEnergyFin, ouGammaFin, partialDeriv_const]

theorem ouGammaFin_symm {f g : (Fin n → ℝ) → ℝ} :
    ouGammaFin f g = ouGammaFin g f := by
  ext x
  simp [ouGammaFin, mul_comm]

theorem ouGammaFin_nonneg {f : (Fin n → ℝ) → ℝ} (x : Fin n → ℝ) :
    0 ≤ ouGammaFin f f x := by
  unfold ouGammaFin
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (partialDeriv i f x))

theorem ouGammaFin_leibniz {f g h : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (hg : IsCoreFin g) (_hh : IsCoreFin h) (x : Fin n → ℝ) :
    ouGammaFin (f * g) h x = f x * ouGammaFin g h x + g x * ouGammaFin f h x := by
  unfold ouGammaFin
  have hsum :
      (fun i : Fin n => partialDeriv i (f * g) x * partialDeriv i h x) =
        fun i : Fin n =>
          f x * (partialDeriv i g x * partialDeriv i h x) +
            g x * (partialDeriv i f x * partialDeriv i h x) := by
    funext i
    rw [partialDeriv_mul i hf.contDiff hg.contDiff]
    ring
  rw [hsum, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

@[simp] theorem ouGammaFin_const_left (c : ℝ) (f : (Fin n → ℝ) → ℝ) :
    ouGammaFin (fun _ => c) f = 0 := by
  ext x
  simp [ouGammaFin, partialDeriv_const]

@[simp] theorem ouGammaFin_const_right (c : ℝ) (f : (Fin n → ℝ) → ℝ) :
    ouGammaFin f (fun _ => c) = 0 := by
  rw [ouGammaFin_symm, ouGammaFin_const_left]

/-- Linear Gaussian mixing map `(x,y) ↦ a x + b y` on the product space. -/
def mixCLM (a b : ℝ) : ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin n =>
    a • (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)) +
    b • (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ))

@[simp] theorem mixCLM_apply (a b : ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    mixCLM (n := n) a b p = fun i => a * p.1 i + b * p.2 i := by
  ext i
  simp [mixCLM, ContinuousLinearMap.pi_apply]

theorem charFunDual_gamma1D (L : StrongDual ℝ ℝ) :
    charFunDual Gaussian1D.γ L = Complex.exp (-(L 1) ^ 2 / 2) := by
  rw [charFunDual_eq_charFun_map_one, Gaussian1D.γ, gaussianReal_map_continuousLinearMap,
    charFun_gaussianReal]
  congr 1
  simp [sq_nonneg]
  ring

theorem charFunDual_γFin (L : StrongDual ℝ (Fin n → ℝ)) :
    charFunDual (γFin n) L = Complex.exp (-((∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2)) / 2) := by
  rw [show charFunDual (γFin n) L =
      ∏ i : Fin n, charFunDual Gaussian1D.γ (L.comp (.single ℝ (fun _ : Fin n => ℝ) i)) by
    simpa [γFin] using (charFunDual_pi (μ := fun _ : Fin n => Gaussian1D.γ) L)]
  simp_rw [charFunDual_gamma1D]
  simp_rw [ContinuousLinearMap.comp_apply]
  rw [← Complex.exp_sum]
  congr 1
  simp [ContinuousLinearMap.single_apply]
  calc
    ∑ x : Fin n, -↑(L (Pi.single x (1 : ℝ))) ^ 2 / (2 : ℂ)
        = ∑ x : Fin n, (↑(L (Pi.single x (1 : ℝ))) ^ 2 : ℂ) * (-((1 : ℂ) / 2)) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
    _ = (∑ x : Fin n, (↑(L (Pi.single x (1 : ℝ))) ^ 2 : ℂ)) * (-((1 : ℂ) / 2)) := by
          rw [Finset.sum_mul]
    _ = (-∑ x : Fin n, (↑(L (Pi.single x (1 : ℝ))) ^ 2 : ℂ)) / (2 : ℂ) := by
          ring

theorem comp_mixCLM_inl_apply_single (a b : ℝ) (L : StrongDual ℝ (Fin n → ℝ)) (i : Fin n) :
    (((L.comp (mixCLM (n := n) a b)).comp
      (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) =
      a * L (Pi.single i (1 : ℝ)) := by
  have hfun :
      (fun j : Fin n => a * (Pi.single i (1 : ℝ) : Fin n → ℝ) j) =
        a • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
    ext j
    simp [Pi.smul_apply, smul_eq_mul]
  simp [mixCLM, smul_eq_mul]
  rw [hfun, map_smul]
  simp [smul_eq_mul]

theorem comp_mixCLM_inr_apply_single (a b : ℝ) (L : StrongDual ℝ (Fin n → ℝ)) (i : Fin n) :
    (((L.comp (mixCLM (n := n) a b)).comp
      (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) =
      b * L (Pi.single i (1 : ℝ)) := by
  have hfun :
      (fun j : Fin n => b * (Pi.single i (1 : ℝ) : Fin n → ℝ) j) =
        b • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
    ext j
    simp [Pi.smul_apply, smul_eq_mul]
  simp [mixCLM, smul_eq_mul]
  rw [hfun, map_smul]
  simp [smul_eq_mul]

/-- Any orthogonal scalar mix `(x,y) ↦ a x + b y` preserves the standard
Gaussian product law. -/
theorem ou_kernel_map_coeff (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ((γFin n).prod (γFin n)).map (mixCLM (n := n) a b) = γFin n := by
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map, charFunDual_prod, charFunDual_γFin, charFunDual_γFin, charFunDual_γFin]
  have hinl :
      ∑ i : Fin n,
        ((((L.comp (mixCLM (n := n) a b)).comp
          (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) ^ 2) =
        a ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2 := by
    calc
      _ = ∑ i : Fin n, (a * L (Pi.single i (1 : ℝ))) ^ 2 := by
            congr with i
            rw [comp_mixCLM_inl_apply_single]
      _ = _ := by
            rw [Finset.mul_sum]
            congr with i
            ring
  have hinr :
      ∑ i : Fin n,
        ((((L.comp (mixCLM (n := n) a b)).comp
          (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) ^ 2) =
        b ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2 := by
    calc
      _ = ∑ i : Fin n, (b * L (Pi.single i (1 : ℝ))) ^ 2 := by
            congr with i
            rw [comp_mixCLM_inr_apply_single]
      _ = _ := by
            rw [Finset.mul_sum]
            congr with i
            ring
  rw [hinl, hinr]
  rw [← Complex.exp_add]
  congr 1
  let S : ℝ := ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2
  have hs : a ^ 2 * S + b ^ 2 * S = S := by
    calc
      a ^ 2 * S + b ^ 2 * S = (a ^ 2 + b ^ 2) * S := by ring
      _ = S := by rw [hab, one_mul]
  have hgoal :
      -(↑(a ^ 2 * S) : ℂ) / (2 : ℂ) + -(↑(b ^ 2 * S) : ℂ) / (2 : ℂ) =
        -(↑S : ℂ) / (2 : ℂ) := by
    calc
      -(↑(a ^ 2 * S) : ℂ) / (2 : ℂ) + -(↑(b ^ 2 * S) : ℂ) / (2 : ℂ)
          = (↑(a ^ 2 * S) : ℂ) * (-((1 : ℂ) / 2)) +
              (↑(b ^ 2 * S) : ℂ) * (-((1 : ℂ) / 2)) := by ring
      _ = ((↑(a ^ 2 * S) : ℂ) + (↑(b ^ 2 * S) : ℂ)) * (-((1 : ℂ) / 2)) := by ring
      _ = (↑(a ^ 2 * S + b ^ 2 * S) : ℂ) * (-((1 : ℂ) / 2)) := by norm_num
      _ = (↑S : ℂ) * (-((1 : ℂ) / 2)) := by rw [hs]
      _ = -(↑S : ℂ) / (2 : ℂ) := by ring
  simpa [S] using hgoal

theorem ou_kernel_map_fin (t : ℝ) (ht : 0 ≤ t) :
    ((γFin n).prod (γFin n)).map
      (mixCLM (n := n) (exp (-t)) (sqrt (1 - exp (-2 * t)))) = γFin n := by
  apply ou_kernel_map_coeff
  have hnonneg : 0 ≤ 1 - exp (-2 * t) := Gaussian1D.one_sub_exp_nonneg t ht
  rw [sq_sqrt hnonneg, sq, ← exp_add]
  rw [show -t + -t = -2 * t by ring]
  ring

/-- Orthogonal Gaussian rotation on `(Fin n → ℝ) × (Fin n → ℝ)`. -/
def rotCLM (a b : ℝ) :
    ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (mixCLM (n := n) a b).prod (mixCLM (n := n) b (-a))

theorem comp_rotCLM_inl_apply_single (a b : ℝ)
    (L : StrongDual ℝ ((Fin n → ℝ) × (Fin n → ℝ))) (i : Fin n) :
    (((L.comp (rotCLM (n := n) a b)).comp
      (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) =
      a * ((L.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ)))
        (Pi.single i (1 : ℝ))) +
      b * ((L.comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ)))
        (Pi.single i (1 : ℝ))) := by
  have hpair :
      rotCLM (n := n) a b ((Pi.single i (1 : ℝ)), (0 : Fin n → ℝ)) =
        a • ((Pi.single i (1 : ℝ) : Fin n → ℝ), 0) +
          b • (0, (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
    apply Prod.ext
    · ext j
      simp [rotCLM, mixCLM_apply, smul_eq_mul]
    · ext j
      simp [rotCLM, mixCLM_apply, smul_eq_mul]
  simp [ContinuousLinearMap.comp_apply]
  rw [hpair, map_add, map_smul, map_smul]
  simp [smul_eq_mul]

theorem comp_rotCLM_inr_apply_single (a b : ℝ)
    (L : StrongDual ℝ ((Fin n → ℝ) × (Fin n → ℝ))) (i : Fin n) :
    (((L.comp (rotCLM (n := n) a b)).comp
      (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) =
      b * ((L.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ)))
        (Pi.single i (1 : ℝ))) -
      a * ((L.comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ)))
        (Pi.single i (1 : ℝ))) := by
  have hpair :
      rotCLM (n := n) a b ((0 : Fin n → ℝ), Pi.single i (1 : ℝ)) =
        b • ((Pi.single i (1 : ℝ) : Fin n → ℝ), 0) +
          (-a) • (0, (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
    apply Prod.ext
    · ext j
      simp [rotCLM, mixCLM_apply, smul_eq_mul]
    · ext j
      simp [rotCLM, mixCLM_apply, smul_eq_mul]
  simp [ContinuousLinearMap.comp_apply]
  rw [hpair, map_add, map_smul, map_smul]
  simp [smul_eq_mul]
  rw [sub_eq_add_neg]

/-- Orthogonal rotations preserve the Gaussian product law on
`(Fin n → ℝ) × (Fin n → ℝ)`. -/
theorem rotCLM_map_coeff (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ((γFin n).prod (γFin n)).map (rotCLM (n := n) a b) =
      (γFin n).prod (γFin n) := by
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map, charFunDual_prod, charFunDual_γFin, charFunDual_γFin,
    charFunDual_prod, charFunDual_γFin, charFunDual_γFin]
  let A : Fin n → ℝ := fun i =>
    ((L.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ)))
      (Pi.single i (1 : ℝ)))
  let B : Fin n → ℝ := fun i =>
    ((L.comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ)))
      (Pi.single i (1 : ℝ)))
  let S₁ : ℝ := ∑ i : Fin n,
    ((((L.comp (rotCLM (n := n) a b)).comp
      (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ)))
      (Pi.single i (1 : ℝ))) ^ 2)
  let S₂ : ℝ := ∑ i : Fin n,
    ((((L.comp (rotCLM (n := n) a b)).comp
      (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ)))
      (Pi.single i (1 : ℝ))) ^ 2)
  let T₁ : ℝ := ∑ i : Fin n, (A i) ^ 2
  let T₂ : ℝ := ∑ i : Fin n, (B i) ^ 2
  have hsum : S₁ + S₂ = T₁ + T₂ := by
    calc
      S₁ + S₂ = ∑ i : Fin n, ((a * A i + b * B i) ^ 2 + (b * A i - a * B i) ^ 2) := by
        rw [show S₁ = ∑ i : Fin n, (a * A i + b * B i) ^ 2 by
          unfold S₁ A
          congr with i
          rw [comp_rotCLM_inl_apply_single]
            ,
          show S₂ = ∑ i : Fin n, (b * A i - a * B i) ^ 2 by
          unfold S₂ A B
          congr with i
          rw [comp_rotCLM_inr_apply_single]]
        rw [← Finset.sum_add_distrib]
      _ = ∑ i : Fin n, (A i ^ 2 + B i ^ 2) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        calc
          (a * A i + b * B i) ^ 2 + (b * A i - a * B i) ^ 2
            = (a ^ 2 + b ^ 2) * (A i ^ 2 + B i ^ 2) := by ring
          _ = A i ^ 2 + B i ^ 2 := by rw [hab, one_mul]
      _ = T₁ + T₂ := by
        unfold T₁ T₂
        rw [Finset.sum_add_distrib]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  calc
    -(↑S₁ : ℂ) / (2 : ℂ) + -(↑S₂ : ℂ) / (2 : ℂ)
        = (↑(S₁ + S₂) : ℂ) * (-((1 : ℂ) / 2)) := by
            norm_num
            ring
    _ = (↑(T₁ + T₂) : ℂ) * (-((1 : ℂ) / 2)) := by rw [hsum]
    _ = -(↑T₁ : ℂ) / (2 : ℂ) + -(↑T₂ : ℂ) / (2 : ℂ) := by
          norm_num
          ring

theorem mixCLM_rotCLM (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    mixCLM (n := n) a b (rotCLM (n := n) a b p) = p.1 := by
  ext i
  simp [rotCLM, mixCLM_apply]
  calc
    a * (a * p.1 i + b * p.2 i) + b * (b * p.1 i + -(a * p.2 i))
          = (a ^ 2 + b ^ 2) * p.1 i := by ring
    _ = p.1 i := by rw [hab, one_mul]

/-- Scalar multiplication on `Fin n → ℝ` as a continuous linear map. -/
def smulFinCLM (c : ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  c • ContinuousLinearMap.id ℝ (Fin n → ℝ)

theorem comp_smulFinCLM_apply_single (c : ℝ)
    (L : StrongDual ℝ (Fin n → ℝ)) (i : Fin n) :
    ((L.comp (smulFinCLM (n := n) c)) (Pi.single i (1 : ℝ))) =
      c * L (Pi.single i (1 : ℝ)) := by
  simp [smulFinCLM, smul_eq_mul]

/-- Mixed Gaussian coordinates with variance `a² + b² = c²` equal the scalar
pushforward of the standard Gaussian by `c`. -/
theorem ou_kernel_map_coeff_scaled (a b c : ℝ)
    (hvar : a ^ 2 + b ^ 2 = c ^ 2) (_hc : 0 ≤ c) :
    ((γFin n).prod (γFin n)).map (mixCLM (n := n) a b) =
      (γFin n).map (smulFinCLM (n := n) c) := by
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map, charFunDual_prod, charFunDual_γFin, charFunDual_γFin,
    charFunDual_map, charFunDual_γFin]
  have hmix :
      ∑ i : Fin n,
        ((((L.comp (mixCLM (n := n) a b)).comp
          (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) ^ 2) +
      ∑ i : Fin n,
        ((((L.comp (mixCLM (n := n) a b)).comp
          (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) ^ 2) =
      c ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2 := by
    calc
      _ = a ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2 +
            b ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2 := by
              rw [show ∑ i : Fin n,
                    ((((L.comp (mixCLM (n := n) a b)).comp
                      (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ)))
                      (Pi.single i (1 : ℝ))) ^ 2) =
                    a ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2 by
                    calc
                      _ = ∑ i : Fin n, (a * L (Pi.single i (1 : ℝ))) ^ 2 := by
                            congr with i
                            rw [comp_mixCLM_inl_apply_single]
                      _ = _ := by
                            rw [Finset.mul_sum]
                            congr with i
                            ring,
                  show ∑ i : Fin n,
                    ((((L.comp (mixCLM (n := n) a b)).comp
                      (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ)))
                      (Pi.single i (1 : ℝ))) ^ 2) =
                    b ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2 by
                    calc
                      _ = ∑ i : Fin n, (b * L (Pi.single i (1 : ℝ))) ^ 2 := by
                            congr with i
                            rw [comp_mixCLM_inr_apply_single]
                      _ = _ := by
                            rw [Finset.mul_sum]
                            congr with i
                            ring]
      _ = c ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2 := by
            rw [← hvar]
            ring
  have hsmul :
      ∑ i : Fin n, (((L.comp (smulFinCLM (n := n) c)) (Pi.single i (1 : ℝ))) ^ 2) =
        c ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2 := by
    calc
      _ = ∑ i : Fin n, (c * L (Pi.single i (1 : ℝ))) ^ 2 := by
            congr with i
            rw [comp_smulFinCLM_apply_single]
      _ = _ := by
            rw [Finset.mul_sum]
            congr with i
            ring
  let S₁ : ℝ := ∑ i : Fin n,
    ((((L.comp (mixCLM (n := n) a b)).comp
      (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) ^ 2)
  let S₂ : ℝ := ∑ i : Fin n,
    ((((L.comp (mixCLM (n := n) a b)).comp
      (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) ^ 2)
  let T : ℝ := ∑ i : Fin n, (((L.comp (smulFinCLM (n := n) c)) (Pi.single i (1 : ℝ))) ^ 2)
  have hS : S₁ + S₂ = c ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2 := by
    simpa [S₁, S₂] using hmix
  have hT : T = c ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2 := by
    simpa [T] using hsmul
  rw [← Complex.exp_add]
  rw [show ∑ i : Fin n,
      ((((L.comp (mixCLM (n := n) a b)).comp
        (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) ^ 2) = S₁ by
      rfl]
  rw [show ∑ i : Fin n,
      ((((L.comp (mixCLM (n := n) a b)).comp
        (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) ^ 2) = S₂ by
      rfl]
  rw [show ∑ i : Fin n, (((L.comp (smulFinCLM (n := n) c)) (Pi.single i (1 : ℝ))) ^ 2) = T by
      rfl]
  congr 1
  calc
    -(↑S₁ : ℂ) / (2 : ℂ) + -(↑S₂ : ℂ) / (2 : ℂ)
        = -(↑(S₁ + S₂) : ℂ) / (2 : ℂ) := by
            norm_num
            ring
    _ = -(↑(c ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2) : ℂ) / (2 : ℂ) := by
          rw [hS]
    _ = -(↑T : ℂ) / (2 : ℂ) := by rw [hT]

theorem ouSemigroupFin_mean (f : (Fin n → ℝ) → ℝ) (t : ℝ) (ht : 0 ≤ t) (hf : IsCoreFin f) :
    ∫ x, ouSemigroupFin t f x ∂γFin n = ∫ x, f x ∂γFin n := by
  set a := exp (-t)
  set b := sqrt (1 - exp (-2 * t))
  have hmap : ((γFin n).prod (γFin n)).map (mixCLM (n := n) a b) = γFin n := by
    simpa [a, b] using ou_kernel_map_fin (n := n) t ht
  have hf_map_sm : AEStronglyMeasurable f (((γFin n).prod (γFin n)).map (mixCLM (n := n) a b)) := by
    simpa [hmap] using hf.stronglyMeasurable.aestronglyMeasurable
  have hf_map_int : Integrable f (((γFin n).prod (γFin n)).map (mixCLM (n := n) a b)) := by
    simpa [hmap] using hf.integrable
  have hcomp :
      ∫ p, f (mixCLM (n := n) a b p) ∂((γFin n).prod (γFin n)) = ∫ x, f x ∂γFin n := by
    simpa [hmap] using
      (integral_map (f := f) (Measurable.aemeasurable (by fun_prop)) hf_map_sm).symm
  have hmix_int : Integrable (f ∘ mixCLM (n := n) a b) ((γFin n).prod (γFin n)) :=
    (integrable_map_measure hf_map_sm (Measurable.aemeasurable (by fun_prop))).mp
      hf_map_int
  have hprod :
      ∫ x, ∫ y, f (mixCLM (n := n) a b (x, y)) ∂γFin n ∂γFin n =
        ∫ p, f (mixCLM (n := n) a b p) ∂((γFin n).prod (γFin n)) := by
    simpa using (integral_prod (f := f ∘ mixCLM (n := n) a b) hmix_int).symm
  have hiter :
      (∫ x, ouSemigroupFin t f x ∂γFin n) =
        ∫ x, ∫ y, f (mixCLM (n := n) a b (x, y)) ∂γFin n ∂γFin n := by
    unfold ouSemigroupFin
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    congr 1
  rw [hiter, hprod]
  exact hcomp

theorem ouSemigroupFin_contraction (f : (Fin n → ℝ) → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf : IsCoreFin f) :
    ∫ x, (ouSemigroupFin t f x) ^ 2 ∂γFin n ≤ ∫ x, (f x) ^ 2 ∂γFin n := by
  set a := exp (-t)
  set b := sqrt (1 - exp (-2 * t))
  have hmap : ((γFin n).prod (γFin n)).map (mixCLM (n := n) a b) = γFin n := by
    simpa [a, b] using ou_kernel_map_fin (n := n) t ht
  obtain ⟨M, hM⟩ := hf.bound_exists
  have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hf_meas : Measurable f := hf.measurable
  have hf2_int : Integrable (fun x => (f x) ^ 2) (γFin n) := hf.integrable_sq
  have hf2_map_sm : AEStronglyMeasurable (fun x => (f x) ^ 2)
      (((γFin n).prod (γFin n)).map (mixCLM (n := n) a b)) := by
    simpa [hmap] using ((hf.measurable.pow_const 2).aemeasurable.aestronglyMeasurable)
  have hf2_map_int : Integrable (fun x => (f x) ^ 2)
      (((γFin n).prod (γFin n)).map (mixCLM (n := n) a b)) := by
    simpa [hmap] using hf2_int
  have hf2_mix_int : Integrable (fun p => (f (mixCLM (n := n) a b p)) ^ 2)
      ((γFin n).prod (γFin n)) :=
    (integrable_map_measure hf2_map_sm (Measurable.aemeasurable (by fun_prop))).mp hf2_map_int
  have hf_mix_int : ∀ x, Integrable (fun y => f (mixCLM (n := n) a b (x, y))) (γFin n) := by
    intro x
    have hsec_meas : Measurable (fun y : Fin n → ℝ => mixCLM (n := n) a b (x, y)) := by
      fun_prop
    refine Integrable.mono' (integrable_const M)
      ((hf_meas.comp hsec_meas).aemeasurable.aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall (fun y => hM (mixCLM (n := n) a b (x, y)))
  have h_convex : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) :=
    Even.convexOn_pow (Nat.even_iff.mpr rfl)
  have h_cont : ContinuousOn (fun x : ℝ => x ^ 2) Set.univ := (continuous_pow 2).continuousOn
  have h_closed : IsClosed (Set.univ : Set ℝ) := isClosed_univ
  have hJensen :
      ∀ x, (∫ y, f (mixCLM (n := n) a b (x, y)) ∂γFin n) ^ 2 ≤
        ∫ y, (f (mixCLM (n := n) a b (x, y))) ^ 2 ∂γFin n := by
    intro x
    have hmem : ∀ᵐ y ∂γFin n, f (mixCLM (n := n) a b (x, y)) ∈ (Set.univ : Set ℝ) :=
      Filter.Eventually.of_forall (fun y => Set.mem_univ _)
    have hf_mix2_int : Integrable (fun y => (f (mixCLM (n := n) a b (x, y))) ^ 2) (γFin n) := by
      have hsec_meas : Measurable (fun y : Fin n → ℝ => mixCLM (n := n) a b (x, y)) := by
        fun_prop
      refine Integrable.mono' (integrable_const (M ^ 2))
        (((hf_meas.comp hsec_meas).pow_const 2).aemeasurable.aestronglyMeasurable) ?_
      refine Filter.Eventually.of_forall ?_
      intro y
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hy : |f (mixCLM (n := n) a b (x, y))| ≤ M := by
        rw [← Real.norm_eq_abs]
        exact hM (mixCLM (n := n) a b (x, y))
      have hy2 : (f (mixCLM (n := n) a b (x, y))) ^ 2 ≤ M ^ 2 := by
        have : |f (mixCLM (n := n) a b (x, y))| ^ 2 ≤ M ^ 2 := by
          nlinarith [abs_nonneg (f (mixCLM (n := n) a b (x, y)))]
        rwa [sq_abs] at this
      have hnorm : ‖M ^ 2‖ = M ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      linarith
    exact ConvexOn.map_integral_le h_convex h_cont h_closed hmem (hf_mix_int x) hf_mix2_int
  have hiter :
      (∫ x, (ouSemigroupFin t f x) ^ 2 ∂γFin n) =
        ∫ x, (∫ y, f (mixCLM (n := n) a b (x, y)) ∂γFin n) ^ 2 ∂γFin n := by
    unfold ouSemigroupFin
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    congr 1
  calc
    ∫ x, (ouSemigroupFin t f x) ^ 2 ∂γFin n
      = ∫ x, (∫ y, f (mixCLM (n := n) a b (x, y)) ∂γFin n) ^ 2 ∂γFin n := hiter
    _ ≤ ∫ x, ∫ y, (f (mixCLM (n := n) a b (x, y))) ^ 2 ∂γFin n ∂γFin n := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun x => sq_nonneg _)
          · exact hf2_mix_int.integral_prod_left
          · exact Filter.Eventually.of_forall hJensen
    _ = ∫ p, (f (mixCLM (n := n) a b p)) ^ 2 ∂((γFin n).prod (γFin n)) := by
          simpa using (integral_prod (f := fun p => (f (mixCLM (n := n) a b p)) ^ 2) hf2_mix_int).symm
    _ = ∫ x, (f x) ^ 2 ∂γFin n := by
          simpa [hmap] using
            (integral_map (f := fun x => (f x) ^ 2) (Measurable.aemeasurable (by fun_prop))
              hf2_map_sm).symm

theorem ouSemigroupFin_selfAdjoint (f g : (Fin n → ℝ) → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf : IsCoreFin f) (hg : IsCoreFin g) :
    ∫ x, ouSemigroupFin t f x * g x ∂γFin n =
      ∫ x, f x * ouSemigroupFin t g x ∂γFin n := by
  set a := exp (-t)
  set b := sqrt (1 - exp (-2 * t))
  have hab : a ^ 2 + b ^ 2 = 1 := by
    have hnonneg : 0 ≤ 1 - exp (-2 * t) := Gaussian1D.one_sub_exp_nonneg t ht
    rw [show a = exp (-t) by rfl, show b = sqrt (1 - exp (-2 * t)) by rfl]
    rw [sq_sqrt hnonneg, sq, ← exp_add]
    rw [show -t + -t = -2 * t by ring]
    ring
  have hmap : ((γFin n).prod (γFin n)).map (rotCLM (n := n) a b) =
      (γFin n).prod (γFin n) := rotCLM_map_coeff (n := n) a b hab
  obtain ⟨Mf, hMf⟩ := hf.bound_exists
  obtain ⟨Mg, hMg⟩ := hg.bound_exists
  have hMf_nn : 0 ≤ Mf := (norm_nonneg _).trans (hMf 0)
  have hMg_nn : 0 ≤ Mg := (norm_nonneg _).trans (hMg 0)
  have hF_sm : AEStronglyMeasurable
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (mixCLM (n := n) a b p) * g p.1)
      ((γFin n).prod (γFin n)) := by
    exact
      (((hf.measurable.comp (mixCLM (n := n) a b).continuous.measurable)).mul
        (hg.measurable.comp measurable_fst)).aemeasurable.aestronglyMeasurable
  have hG_sm : AEStronglyMeasurable
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f p.1 * g (mixCLM (n := n) a b p))
      ((γFin n).prod (γFin n)) := by
    have h_meas : Measurable
        (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f p.1 * g (mixCLM (n := n) a b p)) :=
      (hf.measurable.comp measurable_fst).mul
        (hg.measurable.comp (mixCLM (n := n) a b).continuous.measurable)
    exact h_meas.aemeasurable.aestronglyMeasurable
  have hF_int : Integrable
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (mixCLM (n := n) a b p) * g p.1)
      ((γFin n).prod (γFin n)) := by
    refine Integrable.mono' (integrable_const (Mf * Mg)) hF_sm ?_
    refine Filter.Eventually.of_forall ?_
    intro p
    rw [norm_mul]
    exact mul_le_mul (hMf _) (hMg _) (norm_nonneg _) hMf_nn
  have hG_int : Integrable
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f p.1 * g (mixCLM (n := n) a b p))
      ((γFin n).prod (γFin n)) := by
    refine Integrable.mono' (integrable_const (Mf * Mg)) hG_sm ?_
    refine Filter.Eventually.of_forall ?_
    intro p
    rw [norm_mul]
    exact mul_le_mul (hMf _) (hMg _) (norm_nonneg _) hMf_nn
  have hlaw :
      HasLaw (rotCLM (n := n) a b) ((γFin n).prod (γFin n)) ((γFin n).prod (γFin n)) :=
    ⟨(Measurable.aemeasurable (by fun_prop)), hmap⟩
  have hswap :
      ∫ p, f (mixCLM (n := n) a b p) * g p.1 ∂((γFin n).prod (γFin n)) =
        ∫ p, f p.1 * g (mixCLM (n := n) a b p) ∂((γFin n).prod (γFin n)) := by
    calc
      ∫ p, f (mixCLM (n := n) a b p) * g p.1 ∂((γFin n).prod (γFin n))
          = ∫ p,
              (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
                f q.1 * g (mixCLM (n := n) a b q)) (rotCLM (n := n) a b p)
              ∂((γFin n).prod (γFin n)) := by
                refine integral_congr_ae ?_
                refine Filter.Eventually.of_forall ?_
                intro p
                change f (mixCLM (n := n) a b p) * g p.1 =
                  f ((rotCLM (n := n) a b p).1) *
                    g (mixCLM (n := n) a b (rotCLM (n := n) a b p))
                rw [mixCLM_rotCLM (n := n) a b hab p]
                simp [rotCLM]
      _ = ∫ p, f p.1 * g (mixCLM (n := n) a b p) ∂((γFin n).prod (γFin n)) := by
            exact hlaw.integral_comp hG_sm
  have hleft_prod :
      ∫ x, ouSemigroupFin t f x * g x ∂γFin n =
        ∫ p, f (mixCLM (n := n) a b p) * g p.1 ∂((γFin n).prod (γFin n)) := by
    have hiter :
        ∫ x, ouSemigroupFin t f x * g x ∂γFin n =
          ∫ x, ∫ y, f (mixCLM (n := n) a b (x, y)) * g x ∂γFin n ∂γFin n := by
      unfold ouSemigroupFin
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      have hxy :
          (fun y : Fin n → ℝ => f (ouShiftFin t x y)) =
            fun y : Fin n → ℝ => f (mixCLM (n := n) a b (x, y)) := by
        funext y
        have harg : ouShiftFin t x y = mixCLM (n := n) a b (x, y) := by
          ext i
          simp [ouShiftFin, mixCLM_apply, a, b]
        exact congrArg f harg
      calc
        (∫ y, f (ouShiftFin t x y) ∂γFin n) * g x
            = (∫ y, f (mixCLM (n := n) a b (x, y)) ∂γFin n) * g x := by
                simp [hxy]
        _ = ∫ y, f (mixCLM (n := n) a b (x, y)) * g x ∂γFin n := by
              symm
              simpa [mul_comm] using
                (integral_const_mul (r := g x)
                  (f := fun y : Fin n → ℝ => f (mixCLM (n := n) a b (x, y))))
    rw [hiter]
    simpa using
      (integral_prod
        (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
          f (mixCLM (n := n) a b p) * g p.1) hF_int).symm
  have hright_prod :
      ∫ x, f x * ouSemigroupFin t g x ∂γFin n =
        ∫ p, f p.1 * g (mixCLM (n := n) a b p) ∂((γFin n).prod (γFin n)) := by
    have hiter :
        ∫ x, f x * ouSemigroupFin t g x ∂γFin n =
          ∫ x, ∫ y, f x * g (mixCLM (n := n) a b (x, y)) ∂γFin n ∂γFin n := by
      unfold ouSemigroupFin
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      have hxy :
          (fun y : Fin n → ℝ => g (ouShiftFin t x y)) =
            fun y : Fin n → ℝ => g (mixCLM (n := n) a b (x, y)) := by
        funext y
        have harg : ouShiftFin t x y = mixCLM (n := n) a b (x, y) := by
          ext i
          simp [ouShiftFin, mixCLM_apply, a, b]
        exact congrArg g harg
      calc
        f x * ∫ y, g (ouShiftFin t x y) ∂γFin n
            = f x * ∫ y, g (mixCLM (n := n) a b (x, y)) ∂γFin n := by
                simp [hxy]
        _ = ∫ y, f x * g (mixCLM (n := n) a b (x, y)) ∂γFin n := by
              symm
              simpa using
                (integral_const_mul (r := f x)
                  (f := fun y : Fin n → ℝ => g (mixCLM (n := n) a b (x, y))))
    rw [hiter]
    simpa using
      (integral_prod
        (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
          f p.1 * g (mixCLM (n := n) a b p)) hG_int).symm
  rw [hleft_prod, hright_prod]
  exact hswap

theorem ouSemigroupFin_compose (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    ouSemigroupFin (s + t) f = ouSemigroupFin s (ouSemigroupFin t f) := by
  ext x
  obtain ⟨M, hM⟩ := hf.bound_exists
  have hf_meas : Measurable f := hf.measurable
  set ast := exp (-(s + t))
  set bst := sqrt (1 - exp (-2 * (s + t)))
  set as := exp (-s)
  set bs := sqrt (1 - exp (-2 * s))
  set at_ := exp (-t)
  set bt := sqrt (1 - exp (-2 * t))
  have hbst_nn : 0 ≤ 1 - exp (-2 * (s + t)) :=
    Gaussian1D.one_sub_exp_nonneg (s + t) (by linarith)
  have hbs_nn : 0 ≤ 1 - exp (-2 * s) := Gaussian1D.one_sub_exp_nonneg s hs
  have hbt_nn : 0 ≤ 1 - exp (-2 * t) := Gaussian1D.one_sub_exp_nonneg t ht
  have h_ast : ast = as * at_ := by
    show exp (-(s + t)) = exp (-s) * exp (-t)
    rw [show -(s + t) = -s + -t by ring, exp_add]
  set Ψ : ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] (Fin n → ℝ) :=
    mixCLM (n := n) (at_ * bs) bt
  have h_var_eq : (at_ * bs) ^ 2 + bt ^ 2 = bst ^ 2 := by
    show (exp (-t) * sqrt (1 - exp (-2 * s))) ^ 2 + sqrt (1 - exp (-2 * t)) ^ 2 =
        sqrt (1 - exp (-2 * (s + t))) ^ 2
    rw [mul_pow, sq_sqrt hbs_nn, sq_sqrt hbt_nn, sq_sqrt hbst_nn]
    rw [show exp (-t) ^ 2 = exp (-2 * t) by
      rw [show (-2 * t : ℝ) = -t + -t by ring, exp_add]
      ring]
    have h2 : exp (-2 * t) * exp (-2 * s) = exp (-2 * (s + t)) := by
      rw [← exp_add]
      congr 1
      ring
    linarith [h2]
  have hΨ_law :
      ((γFin n).prod (γFin n)).map Ψ = (γFin n).map (smulFinCLM (n := n) bst) := by
    simpa [Ψ] using
      (ou_kernel_map_coeff_scaled (n := n) (a := at_ * bs) (b := bt) (c := bst)
        h_var_eq (sqrt_nonneg _))
  have hΨ_int : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (ast • x + Ψ p))
      ((γFin n).prod (γFin n)) := by
    refine Integrable.mono' (integrable_const M) ?_ ?_
    · exact (hf_meas.comp ((measurable_const.add Ψ.continuous.measurable))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun p => hM _)
  have hRHS :
      ouSemigroupFin s (ouSemigroupFin t f) x =
        ∫ p, f (ast • x + Ψ p) ∂((γFin n).prod (γFin n)) := by
    unfold ouSemigroupFin
    have h_eq_pt : ∀ y' y : Fin n → ℝ,
        ouShiftFin t (ouShiftFin s x y') y = ast • x + Ψ (y', y) := by
      intro y' y
      ext i
      rw [h_ast]
      simp [ouShiftFin, Ψ, mixCLM_apply, smul_eq_mul, as, bs, at_, bt]
      ring
    simp_rw [h_eq_pt]
    simpa using
      (integral_prod (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (ast • x + Ψ p)) hΨ_int).symm
  have hcompose :
      ∫ p, f (ast • x + Ψ p) ∂((γFin n).prod (γFin n)) =
        ∫ z, f (ast • x + bst • z) ∂γFin n := by
    have h_lhs_via_law :
        ∫ p, f (ast • x + Ψ p) ∂((γFin n).prod (γFin n)) =
          ∫ w, f (ast • x + w) ∂(((γFin n).prod (γFin n)).map Ψ) := by
      have hsm : AEStronglyMeasurable (fun w : Fin n → ℝ => f (ast • x + w))
          (((γFin n).prod (γFin n)).map Ψ) := by
        exact (hf_meas.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      rw [integral_map Ψ.continuous.measurable.aemeasurable hsm]
    have h_rhs_via_law :
        ∫ z, f (ast • x + bst • z) ∂γFin n =
          ∫ w, f (ast • x + w) ∂((γFin n).map (smulFinCLM (n := n) bst)) := by
      have hsm : AEStronglyMeasurable (fun w : Fin n → ℝ => f (ast • x + w))
          ((γFin n).map (smulFinCLM (n := n) bst)) := by
        exact (hf_meas.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      have htmp :
          ∫ w, f (ast • x + w) ∂((γFin n).map (smulFinCLM (n := n) bst)) =
            ∫ z, f (ast • x + smulFinCLM (n := n) bst z) ∂γFin n := by
        rw [integral_map (smulFinCLM (n := n) bst).continuous.measurable.aemeasurable hsm]
      calc
        ∫ z, f (ast • x + bst • z) ∂γFin n
            = ∫ z, f (ast • x + smulFinCLM (n := n) bst z) ∂γFin n := by
                simp [smulFinCLM]
        _ = ∫ w, f (ast • x + w) ∂((γFin n).map (smulFinCLM (n := n) bst)) := htmp.symm
    rw [h_lhs_via_law, h_rhs_via_law, hΨ_law]
  show ouSemigroupFin (s + t) f x = ouSemigroupFin s (ouSemigroupFin t f) x
  rw [hRHS, hcompose]
  unfold ouSemigroupFin
  refine integral_congr_ae ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  have harg : ouShiftFin (s + t) x y = ast • x + bst • y := by
    ext i
    simp [ouShiftFin, smul_eq_mul, ast, bst]
  exact congrArg f harg

theorem ouSemigroupFin_zero (f : (Fin n → ℝ) → ℝ) :
    ouSemigroupFin 0 f = f := by
  ext x
  have hconst : (fun y : Fin n → ℝ => f (ouShiftFin 0 x y)) = fun _ : Fin n → ℝ => f x := by
    funext y
    congr 1
    ext i
    simp [ouShiftFin]
  rw [ouSemigroupFin, hconst, integral_const]
  simp

theorem stronglyMeasurable_ouSemigroupFin (t : ℝ) {g : (Fin n → ℝ) → ℝ}
    (hg_meas : Measurable g) :
    StronglyMeasurable (ouSemigroupFin t g) := by
  set a := exp (-t)
  set b := sqrt (1 - exp (-2 * t))
  have hmix_sm : StronglyMeasurable
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => g (mixCLM (n := n) a b p)) :=
    (hg_meas.comp (mixCLM (n := n) a b).continuous.measurable).stronglyMeasurable
  have hEq :
      (fun x => ouSemigroupFin t g x) =
        fun x => ∫ y, g (mixCLM (n := n) a b (x, y)) ∂γFin n := by
    funext x
    have hxy :
        (fun y : Fin n → ℝ => g (ouShiftFin t x y)) =
          fun y : Fin n → ℝ => g (mixCLM (n := n) a b (x, y)) := by
      funext y
      have harg : ouShiftFin t x y = mixCLM (n := n) a b (x, y) := by
        ext i
        simp [ouShiftFin, mixCLM_apply, a, b]
      exact congrArg g harg
    simp [ouSemigroupFin, hxy]
  simpa [hEq] using hmix_sm.integral_prod_right' (ν := γFin n)

theorem integrable_of_bound {g : (Fin n → ℝ) → ℝ} {M : ℝ}
    (hg_meas : Measurable g) (hM : ∀ x, ‖g x‖ ≤ M) :
    Integrable g (γFin n) := by
  refine Integrable.mono' (integrable_const M) hg_meas.aemeasurable.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall hM

theorem norm_ouSemigroupFin_le_of_bound (t : ℝ) {g : (Fin n → ℝ) → ℝ}
    (hg_meas : Measurable g) {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (x : Fin n → ℝ) :
    ‖ouSemigroupFin t g x‖ ≤ M := by
  have hsec_int : Integrable (fun y : Fin n → ℝ => g (ouShiftFin t x y)) (γFin n) := by
    have hcont_shift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
      continuity
    refine integrable_of_bound (M := M)
      ((hg_meas.comp hcont_shift.measurable)) ?_
    intro y
    exact hM (ouShiftFin t x y)
  calc
    ‖ouSemigroupFin t g x‖ = ‖∫ y, g (ouShiftFin t x y) ∂γFin n‖ := rfl
    _ ≤ ∫ y, ‖g (ouShiftFin t x y)‖ ∂γFin n := norm_integral_le_integral_norm _
    _ ≤ ∫ _y : Fin n → ℝ, M ∂γFin n := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
          · exact integrable_const M
          · exact Filter.Eventually.of_forall (fun y => hM (ouShiftFin t x y))
    _ = M := by simp

theorem continuous_ouSemigroupFin_of_bound (t : ℝ) {g : (Fin n → ℝ) → ℝ}
    (hg_cont : Continuous g) {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) :
    Continuous (ouSemigroupFin t g) := by
  rw [continuous_iff_continuousAt]
  intro x
  show Tendsto (fun x' => ∫ y, g (ouShiftFin t x' y) ∂γFin n) (nhds x)
    (nhds (∫ y, g (ouShiftFin t x y) ∂γFin n))
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun _ => M) ?_ ?_ (integrable_const M) ?_
  · filter_upwards with x'
    have hshift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x' y) := by
      continuity
    exact (hg_cont.comp hshift).aestronglyMeasurable
  · filter_upwards with x'
    filter_upwards with y
    exact hM (ouShiftFin t x' y)
  · filter_upwards with y
    have h_arg : Tendsto (fun x' : Fin n → ℝ => ouShiftFin t x' y) (nhds x)
        (nhds (ouShiftFin t x y)) := by
      have hcont : Continuous (fun x' : Fin n → ℝ => ouShiftFin t x' y) := by
        continuity
      exact hcont.tendsto x
    exact (hg_cont.tendsto _).comp h_arg

theorem ouSemigroupFin_preserves_bound (t : ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) :
    ∃ M : ℝ, ∀ x, ‖ouSemigroupFin t f x‖ ≤ M := by
  obtain ⟨M, hM⟩ := hf.bound_exists
  exact ⟨M, fun x => norm_ouSemigroupFin_le_of_bound (n := n) t hf.measurable hM x⟩

theorem partialDeriv_ouSemigroupFin_preserves_bound (t : ℝ) (ht : 0 ≤ t)
    {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (i : Fin n) :
    ∃ M : ℝ, ∀ x, ‖partialDeriv i (ouSemigroupFin t f) x‖ ≤ M := by
  have hf_core : IsCoreFin f := hf
  obtain ⟨_, M, hM⟩ := hf
  refine ⟨M, ?_⟩
  intro x
  rw [partialDeriv_ouSemigroupFin_eq (n := n) t ht hf_core i]
  calc
    ‖exp (-t) * ouSemigroupFin t (partialDeriv i f) x‖
      = exp (-t) * ‖ouSemigroupFin t (partialDeriv i f) x‖ := by
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (exp_nonneg _)]
    _ ≤ exp (-t) * M := by
          gcongr
          exact norm_ouSemigroupFin_le_of_bound (n := n) t (hf_core.partial_measurable i)
            (fun y => (hM y).2.1 i) x
    _ ≤ M := by
          have hexp_le : exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
          have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0).1
          nlinarith

theorem continuous_partialDeriv_ouSemigroupFin (t : ℝ) (ht : 0 ≤ t)
    {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (i : Fin n) :
    Continuous (partialDeriv i (ouSemigroupFin t f)) := by
  have hf_core : IsCoreFin f := hf
  obtain ⟨_, M, hM⟩ := hf
  have hEq := partialDeriv_ouSemigroupFin_eq (n := n) t ht hf_core i
  rw [hEq]
  exact continuous_const.mul
    (continuous_ouSemigroupFin_of_bound (n := n) t (hf_core.partial_continuous i)
      (fun x => (hM x).2.1 i))

theorem contDiffOne_ouSemigroupFin
    (t : ℝ) (ht : 0 ≤ t) {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    ContDiff ℝ 1 (ouSemigroupFin t f) := by
  have hf_core : IsCoreFin f := hf
  obtain ⟨_, M, hM⟩ := hf
  rw [contDiff_one_iff_fderiv]
  refine ⟨?_, ?_⟩
  · intro x
    exact (hasFDerivAt_ouSemigroupFin (n := n) t ht hf_core x).differentiableAt
  · rw [show Continuous (fderiv ℝ (ouSemigroupFin t f)) ↔
        ContDiff ℝ 0 (fderiv ℝ (ouSemigroupFin t f)) by
          simp]
    rw [contDiff_clm_apply_iff
      (𝕜 := ℝ) (D := Fin n → ℝ) (E := Fin n → ℝ) (F := ℝ)
      (f := fderiv ℝ (ouSemigroupFin t f))]
    intro y
    refine contDiff_zero.2 ?_
    have hEq :
        (fun x => fderiv ℝ (ouSemigroupFin t f) x y) =
          fun x => ∑ i : Fin n, exp (-t) * ouSemigroupFin t (partialDeriv i f) x * y i := by
      funext x
      rw [fderiv_ouSemigroupFin_eq (n := n) t ht hf_core]
      simp [ContinuousLinearMap.proj_apply]
    rw [hEq]
    refine continuous_finsetSum _ ?_
    intro i hi
    exact ((continuous_const.mul
      (continuous_ouSemigroupFin_of_bound (n := n) t (hf_core.partial_continuous i)
        (fun x => (hM x).2.1 i))).mul continuous_const)

theorem section_secondDeriv_ouSemigroupFin_preserves_bound (t : ℝ) (ht : 0 ≤ t)
    {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (i : Fin n) (x : Fin n → ℝ) :
    ∃ M : ℝ, ∀ s, ‖deriv (deriv (fun r => ouSemigroupFin t f (Function.update x i r))) s‖ ≤ M := by
  have hf_core : IsCoreFin f := hf
  obtain ⟨_, M, hM⟩ := hf
  refine ⟨M, ?_⟩
  intro s
  rw [section_secondDeriv_ouSemigroupFin_eq (n := n) hf_core t i x]
  calc
    ‖exp (-2 * t) * ouSemigroupFin t (secondPartial i f) (Function.update x i s)‖
      = exp (-2 * t) * ‖ouSemigroupFin t (secondPartial i f) (Function.update x i s)‖ := by
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (exp_nonneg _)]
    _ ≤ exp (-2 * t) * M := by
          gcongr
          exact norm_ouSemigroupFin_le_of_bound (n := n) t
            (hf_core.secondPartial_measurable i)
            (fun y => (hM y).2.2 i) (Function.update x i s)
    _ ≤ M := by
          have hexp_le : exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
          have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0).1
          nlinarith

theorem ouSemigroupFin_preserves_core_bounds (t : ℝ) (ht : 0 ≤ t)
    {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    ∃ M : ℝ,
      (∀ x, ‖ouSemigroupFin t f x‖ ≤ M) ∧
      (∀ i x, ‖partialDeriv i (ouSemigroupFin t f) x‖ ≤ M) ∧
      ∀ i x s, ‖deriv (deriv (fun r => ouSemigroupFin t f (Function.update x i r))) s‖ ≤ M := by
  have hf_core : IsCoreFin f := hf
  obtain ⟨_, M, hM⟩ := hf
  refine ⟨M, ?_, ?_, ?_⟩
  · intro x
    exact norm_ouSemigroupFin_le_of_bound (n := n) t hf_core.measurable (fun y => (hM y).1) x
  · intro i x
    rw [partialDeriv_ouSemigroupFin_eq (n := n) t ht hf_core i]
    calc
      ‖exp (-t) * ouSemigroupFin t (partialDeriv i f) x‖
        = exp (-t) * ‖ouSemigroupFin t (partialDeriv i f) x‖ := by
            rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (exp_nonneg _)]
      _ ≤ exp (-t) * M := by
            gcongr
            exact norm_ouSemigroupFin_le_of_bound (n := n) t (hf_core.partial_measurable i)
              (fun y => (hM y).2.1 i) x
      _ ≤ M := by
            have hexp_le : exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
            have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0).1
            nlinarith
  · intro i x s
    rw [section_secondDeriv_ouSemigroupFin_eq (n := n) hf_core t i x]
    calc
      ‖exp (-2 * t) * ouSemigroupFin t (secondPartial i f) (Function.update x i s)‖
        = exp (-2 * t) *
            ‖ouSemigroupFin t (secondPartial i f) (Function.update x i s)‖ := by
              rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (exp_nonneg _)]
      _ ≤ exp (-2 * t) * M := by
            gcongr
            exact norm_ouSemigroupFin_le_of_bound (n := n) t
              (hf_core.secondPartial_measurable i) (fun y => (hM y).2.2 i) (Function.update x i s)
      _ ≤ M := by
            have hexp_le : exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
            have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0).1
            nlinarith

theorem sq_ouSemigroupFin_le_ouSemigroupFin_sq (t : ℝ) {g : (Fin n → ℝ) → ℝ}
    (hg_meas : Measurable g) {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (x : Fin n → ℝ) :
    (ouSemigroupFin t g x) ^ 2 ≤ ouSemigroupFin t (fun y => g y ^ 2) x := by
  have h_shift_meas : Measurable (fun y : Fin n → ℝ => ouShiftFin t x y) := by
    have hcont_shift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
      continuity
    exact hcont_shift.measurable
  have h_inner_int :
      Integrable (fun y : Fin n → ℝ => g (ouShiftFin t x y)) (γFin n) := by
    refine integrable_of_bound (M := M) (hg_meas.comp h_shift_meas) ?_
    intro y
    exact hM (ouShiftFin t x y)
  have h_inner_sq_int :
      Integrable (fun y : Fin n → ℝ => g (ouShiftFin t x y) ^ 2) (γFin n) := by
    refine integrable_of_bound (M := M ^ 2) ((hg_meas.comp h_shift_meas).pow_const 2) ?_
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : |g (ouShiftFin t x y)| ≤ M := by
      rw [← Real.norm_eq_abs]
      exact hM (ouShiftFin t x y)
    have h2 : (g (ouShiftFin t x y)) ^ 2 ≤ M ^ 2 := by
      have : |g (ouShiftFin t x y)| ^ 2 ≤ M ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      rwa [sq_abs] at this
    exact h2
  have h_conv : ConvexOn ℝ Set.univ (fun s : ℝ => s ^ 2) :=
    Even.convexOn_pow (Nat.even_iff.mpr rfl)
  have h_cont : ContinuousOn (fun s : ℝ => s ^ 2) Set.univ := (continuous_pow 2).continuousOn
  have h_closed : IsClosed (Set.univ : Set ℝ) := isClosed_univ
  have h_aem :
      ∀ᵐ y ∂γFin n, g (ouShiftFin t x y) ∈ (Set.univ : Set ℝ) :=
    Filter.Eventually.of_forall (fun _ => Set.mem_univ _)
  simpa [ouSemigroupFin] using
    ConvexOn.map_integral_le h_conv h_cont h_closed h_aem h_inner_int h_inner_sq_int

theorem ouSemigroupFin_integral_eq_of_bound (t : ℝ) (ht : 0 ≤ t)
    {g : (Fin n → ℝ) → ℝ} (hg_meas : Measurable g) {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) :
    ∫ x, ouSemigroupFin t g x ∂γFin n = ∫ x, g x ∂γFin n := by
  set a := exp (-t)
  set b := sqrt (1 - exp (-2 * t))
  have hmap : ((γFin n).prod (γFin n)).map (mixCLM (n := n) a b) = γFin n := by
    simpa [a, b] using ou_kernel_map_fin (n := n) t ht
  have hg_int : Integrable g (γFin n) := integrable_of_bound hg_meas hM
  have hg_map_sm : AEStronglyMeasurable g
      (((γFin n).prod (γFin n)).map (mixCLM (n := n) a b)) := by
    simpa [hmap] using hg_meas.aemeasurable.aestronglyMeasurable
  have hg_map_int : Integrable g (((γFin n).prod (γFin n)).map (mixCLM (n := n) a b)) := by
    simpa [hmap] using hg_int
  have hcomp :
      ∫ p, g (mixCLM (n := n) a b p) ∂((γFin n).prod (γFin n)) = ∫ x, g x ∂γFin n := by
    simpa [hmap] using
      (integral_map (f := g) (Measurable.aemeasurable (by fun_prop)) hg_map_sm).symm
  have hmix_int : Integrable (g ∘ mixCLM (n := n) a b) ((γFin n).prod (γFin n)) :=
    (integrable_map_measure hg_map_sm (Measurable.aemeasurable (by fun_prop))).mp hg_map_int
  have hprod :
      ∫ x, ∫ y, g (mixCLM (n := n) a b (x, y)) ∂γFin n ∂γFin n =
        ∫ p, g (mixCLM (n := n) a b p) ∂((γFin n).prod (γFin n)) := by
    simpa using (integral_prod (f := g ∘ mixCLM (n := n) a b) hmix_int).symm
  have hiter :
      (∫ x, ouSemigroupFin t g x ∂γFin n) =
        ∫ x, ∫ y, g (mixCLM (n := n) a b (x, y)) ∂γFin n ∂γFin n := by
    unfold ouSemigroupFin
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    have hxy :
        (fun y : Fin n → ℝ => g (ouShiftFin t x y)) =
          fun y : Fin n → ℝ => g (mixCLM (n := n) a b (x, y)) := by
      funext y
      have harg : ouShiftFin t x y = mixCLM (n := n) a b (x, y) := by
        ext i
        simp [ouShiftFin, mixCLM_apply, a, b]
      exact congrArg g harg
    simp [hxy]
  rw [hiter, hprod]
  exact hcomp

theorem ouSemigroupFin_gradient_decay (f : (Fin n → ℝ) → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf : IsCoreFin f) :
    ∫ x, ouGammaFin (ouSemigroupFin t f) (ouSemigroupFin t f) x ∂γFin n ≤
      exp (-2 * t) * ∫ x, ouGammaFin f f x ∂γFin n := by
  have hf_core : IsCoreFin f := hf
  obtain ⟨_, M, hM⟩ := hf
  have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0).1
  have hΓ_meas : Measurable (ouGammaFin f f) := by
    unfold ouGammaFin
    refine Finset.measurable_sum _ ?_
    intro i hi
    exact (hf_core.partial_measurable i).mul (hf_core.partial_measurable i)
  have hΓ_bound : ∀ x, ‖ouGammaFin f f x‖ ≤ n * M ^ 2 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (ouGammaFin_nonneg (f := f) x)]
    unfold ouGammaFin
    calc
      ∑ i : Fin n, partialDeriv i f x * partialDeriv i f x
          ≤ ∑ i : Fin n, M ^ 2 := by
              refine Finset.sum_le_sum ?_
              intro i hi
              have h1 : |partialDeriv i f x| ≤ M := by
                rw [← Real.norm_eq_abs]
                exact (hM x).2.1 i
              have h2 : (partialDeriv i f x) ^ 2 ≤ M ^ 2 := by
                have : |partialDeriv i f x| ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
                rwa [sq_abs] at this
              simpa [pow_two] using h2
      _ = n * M ^ 2 := by simp [nsmul_eq_mul]
  have hpt :
      ∀ x, ouGammaFin (ouSemigroupFin t f) (ouSemigroupFin t f) x ≤
        exp (-2 * t) * ouSemigroupFin t (ouGammaFin f f) x := by
    intro x
    have h_terms :
        ∀ i : Fin n,
          partialDeriv i (ouSemigroupFin t f) x * partialDeriv i (ouSemigroupFin t f) x ≤
            exp (-2 * t) *
              ouSemigroupFin t (fun y => partialDeriv i f y * partialDeriv i f y) x := by
      intro i
      have hj :=
        sq_ouSemigroupFin_le_ouSemigroupFin_sq (n := n) t
          (g := partialDeriv i f) (hg_meas := hf_core.partial_measurable i)
          (hM := fun y => (hM y).2.1 i) x
      rw [partialDeriv_ouSemigroupFin_eq (n := n) t ht hf_core i]
      calc
        (exp (-t) * ouSemigroupFin t (partialDeriv i f) x) *
            (exp (-t) * ouSemigroupFin t (partialDeriv i f) x)
          = exp (-2 * t) * (ouSemigroupFin t (partialDeriv i f) x) ^ 2 := by
              rw [show exp (-2 * t) = exp (-t) * exp (-t) by
                rw [show (-2 * t : ℝ) = -t + -t by ring, exp_add]]
              ring
        _ ≤ exp (-2 * t) * ouSemigroupFin t (fun y => partialDeriv i f y ^ 2) x := by
              exact mul_le_mul_of_nonneg_left hj (exp_nonneg _)
        _ = exp (-2 * t) *
              ouSemigroupFin t (fun y => partialDeriv i f y * partialDeriv i f y) x := by
              congr 2
              ext y
              ring
    have h_sum_int :
        ∀ i : Fin n,
          Integrable
            (fun y : Fin n → ℝ =>
              partialDeriv i f (ouShiftFin t x y) * partialDeriv i f (ouShiftFin t x y)) (γFin n) := by
      intro i
      have hcont_shift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
        continuity
      refine integrable_of_bound (M := M ^ 2)
        (((hf_core.partial_measurable i).comp hcont_shift.measurable).mul
          ((hf_core.partial_measurable i).comp hcont_shift.measurable)) ?_
      intro y
      rw [norm_mul]
      have hi : ‖partialDeriv i f (ouShiftFin t x y)‖ ≤ M := (hM (ouShiftFin t x y)).2.1 i
      have hsq : ‖partialDeriv i f (ouShiftFin t x y)‖ * ‖partialDeriv i f (ouShiftFin t x y)‖
          ≤ M * M := mul_le_mul hi hi (norm_nonneg _) hM_nn
      simpa [sq] using hsq
    unfold ouGammaFin
    calc
      ∑ i : Fin n, partialDeriv i (ouSemigroupFin t f) x * partialDeriv i (ouSemigroupFin t f) x
        ≤ ∑ i : Fin n,
            exp (-2 * t) * ouSemigroupFin t (fun y => partialDeriv i f y * partialDeriv i f y) x := by
              exact Finset.sum_le_sum (fun i _ => h_terms i)
      _ = exp (-2 * t) *
            ∑ i : Fin n, ouSemigroupFin t (fun y => partialDeriv i f y * partialDeriv i f y) x := by
              rw [Finset.mul_sum]
      _ = exp (-2 * t) * ouSemigroupFin t (ouGammaFin f f) x := by
            congr 1
            calc
              ∑ i : Fin n, ouSemigroupFin t (fun y => partialDeriv i f y * partialDeriv i f y) x
                  = ∑ i : Fin n,
                      ∫ y, partialDeriv i f (ouShiftFin t x y) * partialDeriv i f (ouShiftFin t x y)
                        ∂γFin n := by
                          simp [ouSemigroupFin]
              _ = ∫ y,
                    ∑ i : Fin n,
                      partialDeriv i f (ouShiftFin t x y) * partialDeriv i f (ouShiftFin t x y)
                    ∂γFin n := by
                        rw [integral_finsetSum Finset.univ (fun i _ => h_sum_int i)]
              _ = ouSemigroupFin t (ouGammaFin f f) x := by
                    simp [ouSemigroupFin, ouGammaFin]
  have hupper_int :
      Integrable (fun x => exp (-2 * t) * ouSemigroupFin t (ouGammaFin f f) x) (γFin n) := by
    refine integrable_of_bound (M := exp (-2 * t) * (n * M ^ 2))
      ((stronglyMeasurable_ouSemigroupFin (n := n) t hΓ_meas).measurable.const_mul _) ?_
    intro x
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (exp_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (norm_ouSemigroupFin_le_of_bound (n := n) t hΓ_meas hΓ_bound x) (exp_nonneg _)
  have h_inv :=
    ouSemigroupFin_integral_eq_of_bound (n := n) t ht hΓ_meas hΓ_bound
  calc
    ∫ x, ouGammaFin (ouSemigroupFin t f) (ouSemigroupFin t f) x ∂γFin n
      ≤ ∫ x, exp (-2 * t) * ouSemigroupFin t (ouGammaFin f f) x ∂γFin n := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun x => ouGammaFin_nonneg (f := ouSemigroupFin t f) x)
          · exact hupper_int
          · exact Filter.Eventually.of_forall hpt
    _ = exp (-2 * t) * ∫ x, ouGammaFin f f x ∂γFin n := by
          rw [integral_const_mul, h_inv]

theorem ouSemigroupFin_ergodic (f : (Fin n → ℝ) → ℝ) (hf : IsCoreFin f) :
    Tendsto
      (fun t => ∫ x, (ouSemigroupFin t f x) ^ 2 ∂γFin n - (∫ x, f x ∂γFin n) ^ 2)
      atTop (nhds 0) := by
  obtain ⟨M, hM⟩ := hf.bound_exists
  have hM_nn : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0)
  have hf_cont : Continuous f := hf.continuous
  have hf_meas : Measurable f := hf.measurable
  set Ef : ℝ := ∫ y, f y ∂γFin n with hEf_def
  have h_exp_neg_atTop : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have h_exp_neg2_atTop : Tendsto (fun t : ℝ => Real.exp (-2 * t)) atTop (nhds 0) := by
    have h_neg2t : Tendsto (fun t : ℝ => -2 * t) atTop atBot := by
      refine Filter.tendsto_atBot.mpr ?_
      intro B
      rw [Filter.eventually_atTop]
      refine ⟨max 1 ((1 - B) / 2), ?_⟩
      intro t ht
      have h1 : (1 - B) / 2 ≤ t := (le_max_right _ _).trans ht
      linarith
    exact Real.tendsto_exp_atBot.comp h_neg2t
  have h_b_atTop : Tendsto (fun t : ℝ => Real.sqrt (1 - Real.exp (-2 * t))) atTop (nhds 1) := by
    have h_inner : Tendsto (fun t : ℝ => 1 - Real.exp (-2 * t)) atTop (nhds 1) := by
      simpa using Filter.Tendsto.const_sub 1 h_exp_neg2_atTop
    simpa using h_inner.sqrt
  have h_ptwise : ∀ x, Tendsto (fun t => ouSemigroupFin t f x) atTop (nhds Ef) := by
    intro x
    show Tendsto
      (fun t => ∫ y, f (ouShiftFin t x y) ∂γFin n)
      atTop (nhds (∫ y, f y ∂γFin n))
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ => M) ?_ ?_ (integrable_const M) ?_
    · filter_upwards with t
      have hshift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
        continuity
      exact (hf_meas.comp hshift.measurable).aestronglyMeasurable
    · filter_upwards with t
      filter_upwards with y
      exact hM _
    · filter_upwards with y
      have h_arg : Tendsto (fun t : ℝ => ouShiftFin t x y) atTop (nhds y) := by
        have h1 : Tendsto (fun t : ℝ => Real.exp (-t) • x) atTop (nhds 0) := by
          simpa [Pi.zero_apply] using h_exp_neg_atTop.smul_const x
        have h2 : Tendsto
            (fun t : ℝ => Real.sqrt (1 - Real.exp (-2 * t)) • y) atTop (nhds y) := by
          simpa using h_b_atTop.smul_const y
        have := h1.add h2
        have h_eq :
            (fun t : ℝ => ouShiftFin t x y) =
              fun t : ℝ => Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-2 * t)) • y := by
          funext t
          ext i
          simp [ouShiftFin, Pi.add_apply]
        simpa [h_eq, one_smul] using this
      exact (hf_cont.tendsto y).comp h_arg
  have h_bound : ∀ x t, |ouSemigroupFin t f x| ≤ M := by
    intro x t
    exact norm_ouSemigroupFin_le_of_bound (n := n) t hf_meas hM x
  have h_outer :
      Tendsto (fun t => ∫ x, (ouSemigroupFin t f x) ^ 2 ∂γFin n) atTop (nhds (Ef ^ 2)) := by
    have h_target : Ef ^ 2 = ∫ _x, Ef ^ 2 ∂γFin n := by simp
    rw [h_target]
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ => M ^ 2) ?_ ?_ (integrable_const _) ?_
    · filter_upwards with t
      exact ((stronglyMeasurable_ouSemigroupFin (n := n) t hf_meas).pow 2).aestronglyMeasurable
    · filter_upwards with t
      filter_upwards with x
      have habs : |ouSemigroupFin t f x| ≤ M := h_bound x t
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have : |ouSemigroupFin t f x| ^ 2 ≤ M ^ 2 := by
        nlinarith [abs_nonneg (ouSemigroupFin t f x)]
      rwa [sq_abs] at this
    · filter_upwards with x
      exact (h_ptwise x).pow 2
  have := h_outer.sub_const (Ef ^ 2)
  simpa [hEf_def] using this

theorem ouSemigroupFin_entropy_sq_ergodic (f : (Fin n → ℝ) → ℝ) (hf : IsCoreFin f) :
    Tendsto
      (fun t => DirichletSpace.entropy (ds := dirichletSpaceFin (n := n))
        (ouSemigroupFin t (fun x => f x * f x))) atTop (nhds 0) := by
  obtain ⟨M, hM⟩ := hf.bound_exists
  have hM_nn : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0)
  have hf_cont : Continuous f := hf.continuous
  have hf_meas : Measurable f := hf.measurable
  set g : (Fin n → ℝ) → ℝ := fun x => f x * f x with hg_def
  have hg_cont : Continuous g := hf_cont.mul hf_cont
  have hg_meas : Measurable g := hg_cont.measurable
  have hg_nn : ∀ x, 0 ≤ g x := fun x => mul_self_nonneg _
  have hg_bdd : ∀ x, g x ≤ M ^ 2 := by
    intro x
    have h1 : |f x| ≤ M := by
      rw [← Real.norm_eq_abs]
      exact hM x
    have h2 : (f x) ^ 2 ≤ M ^ 2 := by
      have : |f x| ^ 2 ≤ M ^ 2 := by
        nlinarith [abs_nonneg (f x)]
      rwa [sq_abs] at this
    show f x * f x ≤ M ^ 2
    have : f x * f x = (f x) ^ 2 := by ring
    linarith
  set Eg : ℝ := ∫ y, g y ∂γFin n with hEg_def
  have h_exp_neg_atTop : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have h_exp_neg2_atTop : Tendsto (fun t : ℝ => Real.exp (-2 * t)) atTop (nhds 0) := by
    have h_neg2t : Tendsto (fun t : ℝ => -2 * t) atTop atBot := by
      refine Filter.tendsto_atBot.mpr ?_
      intro B
      rw [Filter.eventually_atTop]
      refine ⟨max 1 ((1 - B) / 2), ?_⟩
      intro t ht
      have h1 : (1 - B) / 2 ≤ t := (le_max_right _ _).trans ht
      linarith
    exact Real.tendsto_exp_atBot.comp h_neg2t
  have h_b_atTop : Tendsto (fun t : ℝ => Real.sqrt (1 - Real.exp (-2 * t))) atTop (nhds 1) := by
    have h_inner : Tendsto (fun t : ℝ => 1 - Real.exp (-2 * t)) atTop (nhds 1) := by
      simpa using Filter.Tendsto.const_sub 1 h_exp_neg2_atTop
    simpa using h_inner.sqrt
  have h_ptwise : ∀ x, Tendsto (fun t => ouSemigroupFin t g x) atTop (nhds Eg) := by
    intro x
    show Tendsto
      (fun t => ∫ y, g (ouShiftFin t x y) ∂γFin n)
      atTop (nhds (∫ y, g y ∂γFin n))
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ => M ^ 2) ?_ ?_ (integrable_const _) ?_
    · filter_upwards with t
      have hshift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
        continuity
      exact (hg_meas.comp hshift.measurable).aestronglyMeasurable
    · filter_upwards with t
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn _)]
      exact hg_bdd _
    · filter_upwards with y
      have h_arg : Tendsto (fun t : ℝ => ouShiftFin t x y) atTop (nhds y) := by
        have h1 : Tendsto (fun t : ℝ => Real.exp (-t) • x) atTop (nhds 0) := by
          simpa [Pi.zero_apply] using h_exp_neg_atTop.smul_const x
        have h2 : Tendsto
            (fun t : ℝ => Real.sqrt (1 - Real.exp (-2 * t)) • y) atTop (nhds y) := by
          simpa using h_b_atTop.smul_const y
        have := h1.add h2
        have h_eq :
            (fun t : ℝ => ouShiftFin t x y) =
              fun t : ℝ => Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-2 * t)) • y := by
          funext t
          ext i
          simp [ouShiftFin, Pi.add_apply]
        simpa [h_eq, one_smul] using this
      exact (hg_cont.tendsto y).comp h_arg
  have h_Ptg_bdd : ∀ x t, 0 ≤ ouSemigroupFin t g x ∧ ouSemigroupFin t g x ≤ M ^ 2 := by
    intro x t
    have hint : Integrable (fun y => g (ouShiftFin t x y)) (γFin n) := by
      refine Integrable.mono' (integrable_const (M ^ 2)) ?_ ?_
      · have hshift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
          continuity
        exact (hg_meas.comp hshift.measurable).aestronglyMeasurable
      · filter_upwards with y
        rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn _)]
        exact hg_bdd _
    refine ⟨?_, ?_⟩
    · exact integral_nonneg (fun y => hg_nn _)
    · calc
        ∫ y, g (ouShiftFin t x y) ∂γFin n
            ≤ ∫ _y : Fin n → ℝ, M ^ 2 ∂γFin n := by
                exact integral_mono hint (integrable_const _) (fun y => hg_bdd _)
        _ = M ^ 2 := by simp
  have hM2_nn : (0 : ℝ) ≤ M ^ 2 := sq_nonneg M
  obtain ⟨B, hB⟩ : ∃ B, ∀ s ∈ Set.Icc (0 : ℝ) (M ^ 2), |s * Real.log s| ≤ B := by
    have h_compact : IsCompact (Set.Icc (0 : ℝ) (M ^ 2)) := isCompact_Icc
    have h_cont_abs : Continuous (fun s => |s * Real.log s|) :=
      Real.continuous_mul_log.abs
    have h_im_compact : IsCompact ((fun s => |s * Real.log s|) '' Set.Icc 0 (M ^ 2)) :=
      h_compact.image h_cont_abs
    obtain ⟨B, hB⟩ := h_im_compact.bddAbove
    refine ⟨B, fun s hs => ?_⟩
    exact hB ⟨s, hs, rfl⟩
  have h_outer_log :
      Tendsto (fun t => ∫ x, ouSemigroupFin t g x * Real.log (ouSemigroupFin t g x) ∂γFin n)
        atTop (nhds (Eg * Real.log Eg)) := by
    have h_target : Eg * Real.log Eg = ∫ _x, Eg * Real.log Eg ∂γFin n := by simp
    rw [h_target]
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ => B) ?_ ?_ (integrable_const _) ?_
    · filter_upwards with t
      have hPtg_sm : MeasureTheory.StronglyMeasurable (ouSemigroupFin t g) :=
        stronglyMeasurable_ouSemigroupFin (n := n) t hg_meas
      have h_log_meas : Measurable (fun x => Real.log (ouSemigroupFin t g x)) :=
        Real.measurable_log.comp hPtg_sm.measurable
      exact (hPtg_sm.measurable.mul h_log_meas).aestronglyMeasurable
    · filter_upwards with t
      filter_upwards with x
      rw [Real.norm_eq_abs]
      exact hB (ouSemigroupFin t g x) ⟨(h_Ptg_bdd x t).1, (h_Ptg_bdd x t).2⟩
    · filter_upwards with x
      have h_cont_pt : ContinuousAt (fun s => s * Real.log s) Eg :=
        Real.continuous_mul_log.continuousAt
      exact h_cont_pt.tendsto.comp (h_ptwise x)
  have h_mean : ∀ t, 0 ≤ t → ∫ x, ouSemigroupFin t g x ∂γFin n = ∫ x, g x ∂γFin n := by
    intro t ht
    refine ouSemigroupFin_integral_eq_of_bound (n := n) (M := M ^ 2) t ht hg_meas ?_
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn x)]
    exact hg_bdd x
  have h_entropy_eq : ∀ t, 0 ≤ t →
      DirichletSpace.entropy (ds := dirichletSpaceFin (n := n)) (ouSemigroupFin t g) =
        (∫ x, ouSemigroupFin t g x * Real.log (ouSemigroupFin t g x) ∂γFin n) -
          Eg * Real.log Eg := by
    intro t ht
    show
      (∫ x, ouSemigroupFin t g x * Real.log (ouSemigroupFin t g x) ∂γFin n) -
        (∫ x, ouSemigroupFin t g x ∂γFin n) * Real.log (∫ x, ouSemigroupFin t g x ∂γFin n) =
      (∫ x, ouSemigroupFin t g x * Real.log (ouSemigroupFin t g x) ∂γFin n) -
        Eg * Real.log Eg
    rw [h_mean t ht]
  have h_diff : Tendsto
      (fun t =>
        (∫ x, ouSemigroupFin t g x * Real.log (ouSemigroupFin t g x) ∂γFin n) -
          Eg * Real.log Eg) atTop (nhds 0) := by
    simpa using h_outer_log.sub_const (Eg * Real.log Eg)
  have h_eq_eventually :
      (fun t => DirichletSpace.entropy (ds := dirichletSpaceFin (n := n))
        (ouSemigroupFin t (fun x => f x * f x))) =ᶠ[atTop]
      (fun t =>
        (∫ x, ouSemigroupFin t g x * Real.log (ouSemigroupFin t g x) ∂γFin n) -
          Eg * Real.log Eg) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    simpa [g, hg_def] using h_entropy_eq t ht
  exact Tendsto.congr' h_eq_eventually.symm h_diff

/-! `ouSemigroupFin_l2_sq_hasDerivWithinAt` and the derived
`ouSemigroupFin_l2_decay_bound` are proved in the later module
`EuclideanFinBE.lean`, which can import the `L²` generator-limit
infrastructure without creating an import cycle. -/

/-! ### Cameron–Martin kernel infrastructure for OU-semigroup smoothing -/

/-- **1D Cameron–Martin / Girsanov shift for the standard Gaussian.**

For the standard Gaussian `Gaussian1D.γ = gaussianReal 0 1` and any `s : ℝ`,
`∫ ψ(u + s) dγ(u) = ∫ ψ(w) · exp(s·w − s²/2) dγ(w)`.

This is the density of the translated Gaussian relative to the reference
Gaussian; no integrability hypothesis on `ψ` is needed because the identity
is proved through the Lebesgue-translation invariance of the underlying
density representation. -/
theorem cameronMartin1D (s : ℝ) (ψ : ℝ → ℝ) :
    ∫ u, ψ (u + s) ∂Gaussian1D.γ
      = ∫ w, ψ w * Real.exp (s * w - s ^ 2 / 2) ∂Gaussian1D.γ := by
  have hγ : (Gaussian1D.γ : Measure ℝ)
      = (volume : Measure ℝ).withDensity (gaussianPDF 0 1) := by
    show gaussianReal 0 1 = _
    exact gaussianReal_of_var_ne_zero 0 one_ne_zero
  have htop : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), gaussianPDF 0 1 x < (⊤ : ENNReal) :=
    Filter.Eventually.of_forall (fun _ => gaussianPDF_lt_top)
  rw [hγ, integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF 0 1) htop,
    integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF 0 1) htop]
  rw [show (fun u => (gaussianPDF 0 1 u).toReal • ψ (u + s))
        = (fun u => (gaussianPDF 0 1 u).toReal * ψ (u + s)) from rfl]
  rw [show (fun w => (gaussianPDF 0 1 w).toReal • (ψ w * Real.exp (s * w - s ^ 2 / 2)))
        = (fun w => (gaussianPDF 0 1 w).toReal * ψ w
            * Real.exp (s * w - s ^ 2 / 2)) from by
        funext w; rw [smul_eq_mul]; ring]
  rw [← integral_add_right_eq_self
      (fun u => (gaussianPDF 0 1 u).toReal * ψ (u + s)) (-s)]
  simp only [neg_add_cancel_right]
  congr 1
  funext w
  have hkey : (gaussianPDF 0 1 (w - s)).toReal
      = (gaussianPDF 0 1 w).toReal * Real.exp (s * w - s ^ 2 / 2) := by
    simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
    unfold gaussianPDFReal
    have hcombine :
        Real.exp (-(w - 0) ^ 2 / (2 * (1:NNReal)))
            * Real.exp (s * w - s ^ 2 / 2)
          = Real.exp (-(w - s - 0) ^ 2 / (2 * (1:NNReal))) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [← hcombine]; ring
  rw [show w - s = w + -s from by ring] at *
  rw [hkey]; ring

/-- **Multivariate Cameron–Martin shift for the product Gaussian.**

For the standard product Gaussian `γFin n` on `Fin n → ℝ` and any shift
`s : Fin n → ℝ`,
`∫ G(y + s) dγFin(y) = ∫ G(w) · exp(⟨s,w⟩ − ‖s‖²/2) dγFin(w)`,
where `⟨s,w⟩ = ∑ᵢ sᵢ wᵢ` and `‖s‖² = ∑ᵢ sᵢ²`.

Proved by induction on `n`, peeling one coordinate with
`integral_γFin_succAbove` and applying the 1D Cameron–Martin shift
`cameronMartin1D` in that coordinate. -/
theorem gaussianFin_cameronMartin : ∀ (n : ℕ) (s : Fin n → ℝ)
    (G : (Fin n → ℝ) → ℝ) (_ : Continuous G) {MG : ℝ} (_ : ∀ z, ‖G z‖ ≤ MG),
    ∫ y, G (y + s) ∂γFin n
      = ∫ w, G w * Real.exp ((∑ i, s i * w i) - (∑ i, s i ^ 2) / 2) ∂γFin n := by
  intro n
  induction n with
  | zero =>
      intro s G hG MG hMG
      have hsub : ∀ z : Fin 0 → ℝ, G z = G ![] := fun z => by
        congr 1; exact Subsingleton.elim _ _
      simp only [Finset.sum_empty, Finset.univ_eq_empty]
      rw [show (fun y : Fin 0 → ℝ => G (y + s)) = fun _ => G ![] from by
            funext y; rw [hsub]]
      rw [show (fun w : Fin 0 → ℝ => G w * Real.exp (0 - 0 / 2))
            = fun _ => G ![] from by funext w; rw [hsub w]; norm_num]
  | succ m ih =>
      intro s G hG MG hMG
      classical
      set s0 : ℝ := s 0 with hs0
      set s' : Fin m → ℝ := Fin.tail s with hs'
      have hcons_s : s = Fin.cons s0 s' := by
        rw [hs0, hs']; exact (Fin.cons_self_tail s).symm
      have hcons_add : ∀ (a b : ℝ) (p q : Fin m → ℝ),
          (Fin.cons a p : Fin (m+1) → ℝ) + Fin.cons b q = Fin.cons (a + b) (p + q) := by
        intro a b p q
        funext j
        refine Fin.cases ?_ (fun k => ?_) j
        · simp only [Pi.add_apply, Fin.cons_zero]
        · simp only [Pi.add_apply, Fin.cons_succ]
      have hpeel : ∀ (F : (Fin (m+1) → ℝ) → ℝ), Integrable F (γFin (m+1)) →
          ∫ y, F y ∂γFin (m + 1)
            = ∫ u, ∫ y', F (Fin.cons u y') ∂γFin m ∂Gaussian1D.γ := by
        intro F hF
        have h := integral_γFin_succAbove (n := m) (0 : Fin (m+1)) hF
        rw [h]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
        refine integral_congr_ae (Filter.Eventually.of_forall (fun y' => ?_))
        show F (Fin.insertNth 0 u y') = F (Fin.cons u y')
        rw [Fin.insertNth_zero']
      have hsum_split : ∀ (u : ℝ) (w' : Fin m → ℝ),
          (∑ j, s j * (Fin.cons u w' : Fin (m+1) → ℝ) j)
            = s0 * u + ∑ k, s' k * w' k := by
        intro u w'
        rw [Fin.sum_univ_succ]
        have hhead : s 0 * (Fin.cons u w' : Fin (m+1) → ℝ) 0 = s0 * u := by
          simp [hs0]
        have htail : ∀ k : Fin m,
            s k.succ * (Fin.cons u w' : Fin (m+1) → ℝ) k.succ = s' k * w' k := by
          intro k; simp [hs', Fin.tail]
        rw [hhead, Finset.sum_congr rfl (fun k _ => htail k)]
      have hnorm_split : (∑ j, s j ^ 2) = s0 ^ 2 + ∑ k, s' k ^ 2 := by
        rw [Fin.sum_univ_succ]
        have hhead : s 0 ^ 2 = s0 ^ 2 := by simp [hs0]
        have htail : ∀ k : Fin m, s k.succ ^ 2 = s' k ^ 2 := by
          intro k; simp [hs', Fin.tail]
        rw [hhead, Finset.sum_congr rfl (fun k _ => htail k)]
      have hcont_shift : Continuous (fun y : Fin (m+1) → ℝ => G (y + s)) :=
        hG.comp (continuous_id.add continuous_const)
      have hInt_lhs : Integrable (fun y : Fin (m+1) → ℝ => G (y + s)) (γFin (m+1)) :=
        integrable_of_bound hcont_shift.measurable (fun y => hMG (y + s))
      have hGcons_cont : ∀ u : ℝ,
          Continuous (fun w' : Fin m → ℝ => G (Fin.cons u w')) :=
        fun u => hG.comp (Continuous.finCons continuous_const continuous_id)
      have hstepL :
          ∫ y, G (y + s) ∂γFin (m + 1)
            = ∫ u, (∫ w', G (Fin.cons (u + s0) w')
                * Real.exp ((∑ k, s' k * w' k) - (∑ k, s' k ^ 2) / 2) ∂γFin m)
                ∂Gaussian1D.γ := by
        rw [hpeel _ hInt_lhs]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
        simp only []
        have harg : (fun y' : Fin m → ℝ => G (Fin.cons u y' + s))
            = fun y' => G (Fin.cons (u + s0) (y' + s')) := by
          funext y'
          rw [hcons_s, hcons_add u s0 y' s']
        rw [harg]
        exact ih s' (fun w' => G (Fin.cons (u + s0) w')) (hGcons_cont (u + s0))
          (MG := MG) (fun z => hMG _)
      have hstepCM :
          ∫ u, (∫ w', G (Fin.cons (u + s0) w')
                * Real.exp ((∑ k, s' k * w' k) - (∑ k, s' k ^ 2) / 2) ∂γFin m)
                ∂Gaussian1D.γ
            = ∫ v, (∫ w', G (Fin.cons v w')
                * Real.exp ((∑ k, s' k * w' k) - (∑ k, s' k ^ 2) / 2) ∂γFin m)
                * Real.exp (s0 * v - s0 ^ 2 / 2) ∂Gaussian1D.γ := by
        have hcm := cameronMartin1D s0
          (fun v => ∫ w', G (Fin.cons v w')
            * Real.exp ((∑ k, s' k * w' k) - (∑ k, s' k ^ 2) / 2) ∂γFin m)
        simpa using hcm
      have hRHSpeel :
          ∫ w, G w * Real.exp ((∑ j, s j * w j) - (∑ j, s j ^ 2) / 2) ∂γFin (m + 1)
            = ∫ v, (∫ w', G (Fin.cons v w')
                * Real.exp ((∑ k, s' k * w' k) - (∑ k, s' k ^ 2) / 2) ∂γFin m)
                * Real.exp (s0 * v - s0 ^ 2 / 2) ∂Gaussian1D.γ := by
        have hInt_rhs : Integrable
            (fun w : Fin (m+1) → ℝ =>
              G w * Real.exp ((∑ j, s j * w j) - (∑ j, s j ^ 2) / 2)) (γFin (m+1)) := by
          -- exp(⟨s,w⟩) = ∏ⱼ exp(sⱼ wⱼ) is γFin-integrable; G is bounded.
          have hexp_prod : Integrable
              (fun w : Fin (m+1) → ℝ => ∏ j, Real.exp (s j * w j)) (γFin (m+1)) := by
            refine MeasureTheory.Integrable.fintype_prod
              (f := fun j u => Real.exp (s j * u))
              (μ := fun _ => Gaussian1D.γ) (fun j => ?_)
            show Integrable (fun u => Real.exp (s j * u)) Gaussian1D.γ
            simpa [Gaussian1D.γ] using
              (ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (s j))
          have hrewrite : (fun w : Fin (m+1) → ℝ =>
                G w * Real.exp ((∑ j, s j * w j) - (∑ j, s j ^ 2) / 2))
              = fun w => Real.exp (- (∑ j, s j ^ 2) / 2)
                  * (G w * ∏ j, Real.exp (s j * w j)) := by
            funext w
            rw [show (∑ j, s j * w j) - (∑ j, s j ^ 2) / 2
                  = (- (∑ j, s j ^ 2) / 2) + (∑ j, s j * w j) from by ring]
            rw [Real.exp_add, Real.exp_sum]
            ring
          rw [hrewrite]
          refine Integrable.const_mul ?_ _
          exact hexp_prod.bdd_mul (c := MG) hG.aestronglyMeasurable
            (Filter.Eventually.of_forall (fun w => hMG w))
        rw [hpeel _ hInt_rhs]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
        simp only []
        rw [← integral_mul_const]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun w' => ?_))
        show G (Fin.cons u w')
              * Real.exp ((∑ j, s j * (Fin.cons u w' : Fin (m+1) → ℝ) j)
                  - (∑ j, s j ^ 2) / 2)
            = G (Fin.cons u w')
              * Real.exp ((∑ k, s' k * w' k) - (∑ k, s' k ^ 2) / 2)
              * Real.exp (s0 * u - s0 ^ 2 / 2)
        rw [hsum_split u w', hnorm_split]
        rw [show (s0 * u + ∑ k, s' k * w' k) - (s0 ^ 2 + ∑ k, s' k ^ 2) / 2
              = ((∑ k, s' k * w' k) - (∑ k, s' k ^ 2) / 2) + (s0 * u - s0 ^ 2 / 2) from by
              ring]
        rw [Real.exp_add]
        ring
      rw [hstepL, hstepCM, ← hRHSpeel]

/-- **Cameron–Martin / kernel representation of the multivariate OU semigroup.**

For `t > 0` (so `b := √(1−e^{−2t}) > 0`) and any continuous bounded `g`,
`(P_t g)(x) = ∫ w, g(b·w) · exp(⟨s,w⟩ − ‖s‖²/2) dγFin(w)` where
`s = (e^{−t}/b)·x`.

The spatial variable `x` enters only through the smooth Gaussian-type weight,
which is the key to differentiating under the integral without any
smoothness or growth control on `g`. -/
theorem ouSemigroupFin_eq_cmKernel (t : ℝ) (ht : 0 < t)
    {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ z, ‖g z‖ ≤ M)
    (x : Fin n → ℝ) :
    ouSemigroupFin t g x
      = ∫ w, g (fun i => Real.sqrt (1 - Real.exp (-2 * t)) * w i)
          * Real.exp ((∑ i, (Real.exp (-t) / Real.sqrt (1 - Real.exp (-2 * t)) * x i) * w i)
              - (∑ i, (Real.exp (-t) / Real.sqrt (1 - Real.exp (-2 * t)) * x i) ^ 2) / 2)
          ∂γFin n := by
  set a : ℝ := Real.exp (-t) with ha
  set b : ℝ := Real.sqrt (1 - Real.exp (-2 * t)) with hb
  have hb_pos : 0 < b := by
    rw [hb]
    apply Real.sqrt_pos.mpr
    have : Real.exp (-2 * t) < 1 := by
      apply Real.exp_lt_one_iff.mpr; linarith
    linarith
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  set s : Fin n → ℝ := fun i => a / b * x i with hs
  set G : (Fin n → ℝ) → ℝ := fun z => g (fun i => b * z i) with hG
  have hG_cont : Continuous G := by
    refine hg.comp ?_
    exact continuous_pi (fun i => continuous_const.mul (continuous_apply i))
  have hG_bd : ∀ z, ‖G z‖ ≤ M := fun z => hM _
  have hrw : (fun y : Fin n → ℝ => g (ouShiftFin t x y))
      = fun y => G (y + s) := by
    funext y
    show g (ouShiftFin t x y) = g (fun i => b * (y + s) i)
    congr 1
    funext i
    show a * x i + b * y i = b * (y i + a / b * x i)
    field_simp
    ring
  have hcm := gaussianFin_cameronMartin n s G hG_cont (MG := M) hG_bd
  calc
    ouSemigroupFin t g x
        = ∫ y, g (ouShiftFin t x y) ∂γFin n := rfl
    _ = ∫ y, G (y + s) ∂γFin n := by rw [hrw]
    _ = ∫ w, G w * Real.exp ((∑ i, s i * w i) - (∑ i, s i ^ 2) / 2) ∂γFin n := hcm
    _ = _ := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
          simp only [hG, hs]

/-! ### Gaussian integrability helpers for OU-semigroup smoothing -/

-- 1D helper (proved earlier).
theorem exp_abs_gamma_integrable (K : ℝ) :
    Integrable (fun u : ℝ => Real.exp (K * |u|)) Gaussian1D.γ := by
  have h1 : Integrable (fun u : ℝ => Real.exp (K * u)) Gaussian1D.γ := by
    simpa [Gaussian1D.γ] using ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := 1) K
  have h2 : Integrable (fun u : ℝ => Real.exp (-K * u)) Gaussian1D.γ := by
    simpa [Gaussian1D.γ] using ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-K)
  refine (h1.add h2).mono ?_ ?_
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hpos1 : 0 < Real.exp (K*u) := Real.exp_pos _
    have hpos2 : 0 < Real.exp (-K*u) := Real.exp_pos _
    rcases abs_cases u with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
      calc Real.exp (K*u) ≤ Real.exp (K*u) + Real.exp (-K*u) := by linarith
        _ = ‖Real.exp (K*u) + Real.exp (-K*u)‖ := by
            rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
    · rw [h, show K * -u = -K * u from by ring]
      calc Real.exp (-K*u) ≤ Real.exp (K*u) + Real.exp (-K*u) := by linarith
        _ = ‖Real.exp (K*u) + Real.exp (-K*u)‖ := by
            rw [Real.norm_eq_abs, abs_of_pos (by linarith)]

-- multivariate exp(K‖w‖), K≥0
theorem exp_norm_gammaFin_integrable (K : ℝ) (hK : 0 ≤ K) :
    Integrable (fun w : Fin n → ℝ => Real.exp (K * ‖w‖)) (γFin n) := by
  have hprod : Integrable
      (fun w : Fin n → ℝ => ∏ j, Real.exp (K * |w j|)) (γFin n) :=
    MeasureTheory.Integrable.fintype_prod
      (f := fun j u => Real.exp (K * |u|)) (μ := fun _ => Gaussian1D.γ)
      (fun j => exp_abs_gamma_integrable K)
  refine hprod.mono ?_ ?_
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_norm)).aestronglyMeasurable
  · filter_upwards with w
    have hnorm_le : ‖w‖ ≤ ∑ j, |w j| := by
      rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _))]
      intro j
      calc ‖w j‖ = |w j| := Real.norm_eq_abs _
        _ ≤ ∑ k, |w k| := Finset.single_le_sum (f := fun k => |w k|)
            (fun k _ => abs_nonneg _) (Finset.mem_univ j)
    have hle : Real.exp (K * ‖w‖) ≤ ∏ j, Real.exp (K * |w j|) := by
      rw [← Real.exp_sum, show (∑ j, K * |w j|) = K * ∑ j, |w j| from by rw [Finset.mul_sum]]
      exact Real.exp_le_exp.mpr (by nlinarith [hnorm_le])
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (K * ‖w‖) ≤ ∏ j, Real.exp (K * |w j|) := hle
      _ = ‖∏ j, Real.exp (K * |w j|)‖ := by
          rw [Real.norm_eq_abs, abs_of_pos (Finset.prod_pos (fun j _ => Real.exp_pos _))]

-- (1+‖w‖)^d ≤ exp(d ‖w‖)
theorem poly_le_exp (d : ℕ) (w : Fin n → ℝ) :
    (1 + ‖w‖) ^ d ≤ Real.exp (d * ‖w‖) := by
  have h1 : (1 : ℝ) + ‖w‖ ≤ Real.exp ‖w‖ := by
    have := Real.add_one_le_exp ‖w‖; linarith
  calc (1 + ‖w‖) ^ d ≤ (Real.exp ‖w‖) ^ d :=
        pow_le_pow_left₀ (by positivity) h1 d
    _ = Real.exp (d * ‖w‖) := by rw [← Real.exp_nat_mul]

def PolyBdd (F : (Fin n → ℝ) → ℝ) : Prop :=
  Continuous F ∧ ∃ (Cf : ℝ) (d : ℕ), 0 ≤ Cf ∧ ∀ w, |F w| ≤ Cf * (1 + ‖w‖) ^ d

theorem polyBdd_mul_exp_integrable {F : (Fin n → ℝ) → ℝ} (hF : PolyBdd F) (K : ℝ) :
    Integrable (fun w => F w * Real.exp (K * ‖w‖)) (γFin n) := by
  obtain ⟨hF_cont, Cf, d, hCf, hbd⟩ := hF
  set K' : ℝ := |K| + d with hK'
  have hK'_nn : 0 ≤ K' := by positivity
  have hbase := exp_norm_gammaFin_integrable (n := n) K' hK'_nn
  refine (hbase.const_mul Cf).mono ?_ ?_
  · exact (hF_cont.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_norm))).aestronglyMeasurable
  · filter_upwards with w
    have hw_nn : 0 ≤ ‖w‖ := norm_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hpoly : (1 + ‖w‖) ^ d ≤ Real.exp (d * ‖w‖) := poly_le_exp d w
    have hKle : Real.exp (K * ‖w‖) ≤ Real.exp (|K| * ‖w‖) :=
      Real.exp_le_exp.mpr (by nlinarith [le_abs_self K, abs_nonneg K])
    calc |F w| * Real.exp (K * ‖w‖)
        ≤ (Cf * (1 + ‖w‖) ^ d) * Real.exp (|K| * ‖w‖) := by
          apply mul_le_mul (hbd w) hKle (Real.exp_pos _).le
          exact mul_nonneg hCf (by positivity)
      _ ≤ (Cf * Real.exp (d * ‖w‖)) * Real.exp (|K| * ‖w‖) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left hpoly hCf
      _ = Cf * Real.exp (K' * ‖w‖) := by
          rw [hK', mul_assoc, ← Real.exp_add]
          congr 2; ring
      _ = ‖Cf * Real.exp (K' * ‖w‖)‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]


/-- Bound `|⟨x,w⟩| ≤ n · ‖x‖ · ‖w‖` on `Fin n → ℝ` (sup norm). -/
theorem abs_sum_mul_le (x w : Fin n → ℝ) :
    |∑ i, x i * w i| ≤ n * (‖x‖ * ‖w‖) := by
  calc |∑ i, x i * w i| ≤ ∑ i, |x i * w i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ‖x‖ * ‖w‖ := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [abs_mul]
        exact mul_le_mul (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm x i)
          (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm w i) (abs_nonneg _) (norm_nonneg _)
    _ = n * (‖x‖ * ‖w‖) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

/-! ### Laplace-family helpers for OU-semigroup smoothing -/

-- continuity/measurability of (x,w) ↦ exp(α ∑ xᵢwᵢ)
theorem cont_expInner (α : ℝ) :
    Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      Real.exp (α * ∑ i, p.1 i * p.2 i)) := by
  refine Real.continuous_exp.comp (continuous_const.mul ?_)
  exact continuous_finsetSum _ (fun i _ =>
    ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd))

-- The base integrand x ↦ ∫ w, F w * exp(α ∑ xᵢwᵢ) is well-defined: integrability for each x.
theorem laplace_integrable {F : (Fin n → ℝ) → ℝ} (hF : PolyBdd F) (α : ℝ) (x : Fin n → ℝ) :
    Integrable (fun w => F w * Real.exp (α * ∑ i, x i * w i)) (γFin n) := by
  have hbase := polyBdd_mul_exp_integrable (n := n) hF (|α| * n * ‖x‖)
  refine hbase.mono ?_ ?_
  · obtain ⟨hFc, _⟩ := hF
    exact (hFc.mul ((cont_expInner α).comp
      (continuous_const.prodMk continuous_id'))).aestronglyMeasurable
  · filter_upwards with w
    obtain ⟨hFc, Cf, d, hCf, hbd⟩ := hF
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
        Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply Real.exp_le_exp.mpr
    calc α * ∑ i, x i * w i ≤ |α * ∑ i, x i * w i| := le_abs_self _
      _ = |α| * |∑ i, x i * w i| := by rw [abs_mul]
      _ ≤ |α| * (n * (‖x‖ * ‖w‖)) :=
          mul_le_mul_of_nonneg_left (abs_sum_mul_le x w) (abs_nonneg _)
      _ = |α| * n * ‖x‖ * ‖w‖ := by ring

-- weight w ↦ α * w j * F w is poly-bounded when F is.
theorem polyBdd_smul_coord {F : (Fin n → ℝ) → ℝ} (hF : PolyBdd F) (α : ℝ) (j : Fin n) :
    PolyBdd (fun w => α * w j * F w) := by
  obtain ⟨hFc, Cf, d, hCf, hbd⟩ := hF
  refine ⟨(continuous_const.mul (continuous_apply j)).mul hFc,
    |α| * Cf, d + 1, by positivity, fun w => ?_⟩
  have hwj : |w j| ≤ 1 + ‖w‖ := by
    have : |w j| ≤ ‖w‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm w j
    have := norm_nonneg w; linarith
  calc |α * w j * F w| = |α| * |w j| * |F w| := by rw [abs_mul, abs_mul]
    _ ≤ |α| * (1 + ‖w‖) * (Cf * (1 + ‖w‖) ^ d) := by
        have h1 : (0:ℝ) ≤ |α| := abs_nonneg _
        have hpos : (0:ℝ) ≤ 1 + ‖w‖ := by positivity
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hwj h1
        · exact hbd w
        · exact abs_nonneg _
        · positivity
    _ = |α| * Cf * (1 + ‖w‖) ^ (d + 1) := by ring


/-! ### Kernel-smoothing: C^∞ of the OU semigroup on bounded functions -/

-- The linear functional Λ(w) := α • ∑ⱼ wⱼ • projⱼ  (the x-derivative direction of exp).
noncomputable def lapDir (α : ℝ) (w : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  α • ∑ j, w j • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)

theorem hasFDerivAt_expInner (α : ℝ) (w x : Fin n → ℝ) :
    HasFDerivAt (fun x : Fin n → ℝ => Real.exp (α * ∑ i, x i * w i))
      (Real.exp (α * ∑ i, x i * w i) • lapDir α w) x := by
  have hbil : HasFDerivAt (fun x : Fin n → ℝ => ∑ i, x i * w i)
      (∑ j, w j • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
    have hpt : (fun x : Fin n → ℝ => ∑ i, x i * w i)
        = ∑ i : Fin n, (fun x : Fin n → ℝ => x i * w i) := by
      funext x; simp [Finset.sum_apply]
    rw [hpt]
    apply HasFDerivAt.sum
    intro j _
    have hproj : HasFDerivAt (fun x : Fin n → ℝ => x j)
        (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ) x := by
      convert (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt using 1
      rfl
    simpa [mul_comm] using hproj.mul_const (w j)
  have hlin : HasFDerivAt (fun x : Fin n → ℝ => α * ∑ i, x i * w i)
      (α • ∑ j, w j • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
    simpa using hbil.const_mul α
  have hcomp := (Real.hasDerivAt_exp (α * ∑ i, x i * w i)).comp_hasFDerivAt x hlin
  have : HasFDerivAt (fun x : Fin n → ℝ => Real.exp (α * ∑ i, x i * w i))
      (Real.exp (α * ∑ i, x i * w i) • (α • ∑ j, w j •
        (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ))) x := by
    simpa only [Function.comp_def] using hcomp
  simpa [lapDir] using this

-- ‖lapDir α w‖ ≤ |α| * n * ‖w‖
theorem norm_lapDir_le (α : ℝ) (w : Fin n → ℝ) :
    ‖lapDir α w‖ ≤ |α| * (n * ‖w‖) := by
  unfold lapDir
  rw [norm_smul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc ‖∑ j, w j • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)‖
      ≤ ∑ j, ‖w j • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, ‖w‖ := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [norm_smul, Real.norm_eq_abs]
        calc |w j| * ‖(ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)‖
            ≤ ‖w‖ * 1 := by
              apply mul_le_mul
              · rw [← Real.norm_eq_abs]; exact norm_le_pi_norm w j
              · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
                simpa using norm_le_pi_norm v j
              · positivity
              · exact norm_nonneg _
          _ = ‖w‖ := by ring
    _ = n * ‖w‖ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

set_option maxHeartbeats 800000 in
theorem hasFDerivAt_laplaceFamily {F : (Fin n → ℝ) → ℝ} (hF : PolyBdd F) (α : ℝ)
    (x₀ : Fin n → ℝ) :
    HasFDerivAt (fun x : Fin n → ℝ => ∫ w, F w * Real.exp (α * ∑ i, x i * w i) ∂γFin n)
      (∫ w, F w • (Real.exp (α * ∑ i, x₀ i * w i) • lapDir α w) ∂γFin n) x₀ := by
  obtain ⟨hFc, Cf, d, hCf, hbd⟩ := hF
  set R : ℝ := ‖x₀‖ + 1 with hR
  set Fn : (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
    fun x w => F w * Real.exp (α * ∑ i, x i * w i) with hFn
  set Fn' : (Fin n → ℝ) → (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] ℝ) :=
    fun x w => F w • (Real.exp (α * ∑ i, x i * w i) • lapDir α w) with hFn'
  set bnd : (Fin n → ℝ) → ℝ :=
    fun w => Cf * (1 + ‖w‖) ^ d * Real.exp (|α| * n * R * ‖w‖) * (|α| * (n * ‖w‖)) with hbnd
  have hball : Metric.ball x₀ 1 ∈ nhds x₀ := Metric.ball_mem_nhds x₀ one_pos
  have hFn_meas : ∀ x, AEStronglyMeasurable (Fn x) (γFin n) := fun x =>
    (hFc.mul ((cont_expInner α).comp
      (continuous_const.prodMk continuous_id'))).aestronglyMeasurable
  have hFn_int : Integrable (Fn x₀) (γFin n) := laplace_integrable ⟨hFc,Cf,d,hCf,hbd⟩ α x₀
  have hcont_lapDir : Continuous (fun w : Fin n → ℝ => lapDir α w) := by
    unfold lapDir
    exact (continuous_finsetSum _
      (fun j _ => (continuous_apply j).smul
        (continuous_const : Continuous (fun _ : Fin n → ℝ =>
          (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ))))).const_smul α
  have hcont_expInner_x0 : Continuous
      (fun w : Fin n → ℝ => Real.exp (α * ∑ i, x₀ i * w i)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_finsetSum _
      (fun i _ => continuous_const.mul (continuous_apply i))))
  have hFn'_meas : AEStronglyMeasurable (Fn' x₀) (γFin n) := by
    have hc : Continuous (Fn' x₀) := by
      rw [hFn']
      exact hFc.smul (hcont_expInner_x0.smul hcont_lapDir)
    exact hc.aestronglyMeasurable
  -- bound integrable: PolyBdd weight times exp
  have hbnd_int : Integrable bnd (γFin n) := by
    have hpb : PolyBdd (fun w : Fin n → ℝ =>
        Cf * (1 + ‖w‖) ^ d * (|α| * (n * ‖w‖))) := by
      refine ⟨(continuous_const.mul ((continuous_const.add
        continuous_norm).pow d)).mul (continuous_const.mul
          (continuous_const.mul continuous_norm)),
        Cf * (|α| * n), d + 1, by positivity, fun w => ?_⟩
      have hwle : ‖w‖ ≤ 1 + ‖w‖ := by have := norm_nonneg w; linarith
      rw [abs_of_nonneg (by positivity)]
      calc Cf * (1 + ‖w‖) ^ d * (|α| * (n * ‖w‖))
          = (Cf * (|α| * n)) * ((1 + ‖w‖) ^ d * ‖w‖) := by ring
        _ ≤ (Cf * (|α| * n)) * ((1 + ‖w‖) ^ d * (1 + ‖w‖)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_left hwle (by positivity)
        _ = Cf * (|α| * n) * (1 + ‖w‖) ^ (d + 1) := by ring
    have := polyBdd_mul_exp_integrable (n := n) hpb (|α| * n * R)
    refine this.congr ?_
    filter_upwards with w
    rw [hbnd]; ring
  -- HasFDerivAt for the integrand at each x, and the norm bound on the ball
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := bnd)
    (F' := Fn') hball (Filter.Eventually.of_forall hFn_meas) hFn_int hFn'_meas
    ?_ hbnd_int ?_
  · filter_upwards with w
    intro x hx
    have hxR : ‖x‖ ≤ R := by
      rw [hR]
      have hb : ‖x - x₀‖ < 1 := by simpa [dist_eq_norm] using hx
      calc ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := by
            have := norm_add_le (x - x₀) x₀; simpa using this
        _ ≤ 1 + ‖x₀‖ := by linarith
        _ = ‖x₀‖ + 1 := by ring
    rw [hFn', norm_smul, Real.norm_eq_abs, norm_smul, Real.norm_eq_abs]
    have hexp_le : Real.exp (α * ∑ i, x i * w i)
        ≤ Real.exp (|α| * n * R * ‖w‖) := by
      apply Real.exp_le_exp.mpr
      calc α * ∑ i, x i * w i ≤ |α| * |∑ i, x i * w i| := by
            rw [← abs_mul]; exact le_abs_self _
        _ ≤ |α| * (n * (‖x‖ * ‖w‖)) :=
            mul_le_mul_of_nonneg_left (abs_sum_mul_le x w) (abs_nonneg _)
        _ ≤ |α| * (n * (R * ‖w‖)) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right hxR (norm_nonneg _)
        _ = |α| * n * R * ‖w‖ := by ring
    rw [hbnd]
    have h1 : |Real.exp (α * ∑ i, x i * w i)| ≤ Real.exp (|α| * n * R * ‖w‖) := by
      rw [abs_of_pos (Real.exp_pos _)]; exact hexp_le
    have h2 : ‖lapDir α w‖ ≤ |α| * (n * ‖w‖) := norm_lapDir_le α w
    calc |F w| * (|Real.exp (α * ∑ i, x i * w i)| * ‖lapDir α w‖)
        ≤ (Cf * (1 + ‖w‖) ^ d) *
            (Real.exp (|α| * n * R * ‖w‖) * (|α| * (n * ‖w‖))) := by
          apply mul_le_mul (hbd w) _ (by positivity)
            (mul_nonneg hCf (by positivity))
          exact mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le
      _ = Cf * (1 + ‖w‖) ^ d * Real.exp (|α| * n * R * ‖w‖) * (|α| * (n * ‖w‖)) := by ring
  · filter_upwards with w
    intro x _
    show HasFDerivAt (fun x : Fin n → ℝ => F w * Real.exp (α * ∑ i, x i * w i))
      (F w • (Real.exp (α * ∑ i, x i * w i) • lapDir α w)) x
    have hd := (hasFDerivAt_expInner α w x).const_smul (F w)
    simpa [smul_eq_mul] using hd

-- The integral derivative equals ∑ⱼ J_{α wⱼ F}(x₀) • projⱼ.
set_option maxHeartbeats 800000 in
theorem laplace_fderiv_eq_sum {F : (Fin n → ℝ) → ℝ} (hF : PolyBdd F) (α : ℝ)
    (x₀ : Fin n → ℝ) :
    (∫ w, F w • (Real.exp (α * ∑ i, x₀ i * w i) • lapDir α w) ∂γFin n)
      = ∑ j, (∫ w, (fun w => α * w j * F w) w
          * Real.exp (α * ∑ i, x₀ i * w i) ∂γFin n) •
          (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ) := by
  obtain ⟨hFc, Cf, d, hCf, hbd⟩ := hF
  -- pointwise: integrand = ∑ⱼ (α wⱼ F · exp) • projⱼ
  have hpt : ∀ w : Fin n → ℝ,
      F w • (Real.exp (α * ∑ i, x₀ i * w i) • lapDir α w)
        = ∑ j, ((α * w j * F w) * Real.exp (α * ∑ i, x₀ i * w i)) •
            (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ) := by
    intro w
    simp only [lapDir, smul_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    rintro j -
    congr 1
    ring
  rw [show (fun w => F w • (Real.exp (α * ∑ i, x₀ i * w i) • lapDir α w))
        = fun w => ∑ j, ((α * w j * F w) * Real.exp (α * ∑ i, x₀ i * w i)) •
            (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ) from funext hpt]
  -- integrability of each term
  have hterm_int : ∀ j : Fin n, Integrable
      (fun w => ((α * w j * F w) * Real.exp (α * ∑ i, x₀ i * w i))) (γFin n) :=
    fun j => laplace_integrable (polyBdd_smul_coord ⟨hFc,Cf,d,hCf,hbd⟩ α j) α x₀
  rw [integral_finsetSum _ (fun j _ => (hterm_int j).smul_const _)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_smul_const]

set_option maxHeartbeats 1200000 in
theorem contDiff_laplaceFamily (k : ℕ) (F : (Fin n → ℝ) → ℝ) (hF : PolyBdd F) (α : ℝ) :
    ContDiff ℝ (k : WithTop ℕ∞)
      (fun x : Fin n → ℝ => ∫ w, F w * Real.exp (α * ∑ i, x i * w i) ∂γFin n) := by
  induction k generalizing F α with
  | zero =>
      obtain ⟨hFc, Cf, d, hCf, hbd⟩ := hF
      have hcont : Continuous
          (fun x : Fin n → ℝ => ∫ w, F w * Real.exp (α * ∑ i, x i * w i) ∂γFin n) := by
        refine continuous_iff_continuousAt.mpr (fun x₀ => ?_)
        set R : ℝ := ‖x₀‖ + 1 with hR
        set bound : (Fin n → ℝ) → ℝ :=
          fun w => Cf * (1 + ‖w‖) ^ d * Real.exp (|α| * n * R * ‖w‖) with hbound
        have hbound_int : Integrable bound (γFin n) := by
          have hpb : PolyBdd (fun w : Fin n → ℝ => Cf * (1 + ‖w‖) ^ d) :=
            ⟨continuous_const.mul ((continuous_const.add continuous_norm).pow d),
              Cf, d, hCf, fun w => by rw [abs_of_nonneg (by positivity)]⟩
          have := polyBdd_mul_exp_integrable (n := n) hpb (|α| * n * R)
          simpa [hbound, mul_assoc] using this
        refine MeasureTheory.continuousAt_of_dominated ?_ ?_ hbound_int ?_
        · filter_upwards with x
          exact (hFc.mul ((cont_expInner α).comp
            (continuous_const.prodMk continuous_id'))).aestronglyMeasurable
        · filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0:ℝ) < 1)] with x hx
          filter_upwards with w
          have hxR : ‖x‖ ≤ R := by
            rw [hR]
            have hb : ‖x - x₀‖ < 1 := by simpa [dist_eq_norm] using hx
            calc ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := by
                  have := norm_add_le (x - x₀) x₀; simpa using this
              _ ≤ 1 + ‖x₀‖ := by linarith
              _ = ‖x₀‖ + 1 := by ring
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          have hexp_le : Real.exp (α * ∑ i, x i * w i)
              ≤ Real.exp (|α| * n * R * ‖w‖) := by
            apply Real.exp_le_exp.mpr
            calc α * ∑ i, x i * w i ≤ |α| * |∑ i, x i * w i| := by
                  rw [← abs_mul]; exact le_abs_self _
              _ ≤ |α| * (n * (‖x‖ * ‖w‖)) :=
                  mul_le_mul_of_nonneg_left (abs_sum_mul_le x w) (abs_nonneg _)
              _ ≤ |α| * (n * (R * ‖w‖)) := by
                  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                  apply mul_le_mul_of_nonneg_left _ (by positivity)
                  exact mul_le_mul_of_nonneg_right hxR (norm_nonneg _)
              _ = |α| * n * R * ‖w‖ := by ring
          calc |F w| * Real.exp (α * ∑ i, x i * w i)
              ≤ (Cf * (1 + ‖w‖) ^ d) * Real.exp (|α| * n * R * ‖w‖) := by
                refine mul_le_mul (hbd w) hexp_le (Real.exp_pos _).le ?_
                positivity
            _ = bound w := by simp only [hbound, mul_assoc]
        · filter_upwards with w
          have hcx : Continuous (fun x : Fin n → ℝ =>
              F w * Real.exp (α * ∑ i, x i * w i)) :=
            continuous_const.mul (Real.continuous_exp.comp
              (continuous_const.mul (continuous_finsetSum _
                (fun i _ => (continuous_apply i).mul continuous_const))))
          exact hcx.continuousAt
      have hz : ((0:ℕ) : WithTop ℕ∞) = 0 := by norm_cast
      rw [hz]
      exact contDiff_zero.mpr hcont
  | succ k ih =>
      show ContDiff ℝ ((k : WithTop ℕ∞) + 1)
        (fun x : Fin n → ℝ => ∫ w, F w * Real.exp (α * ∑ i, x i * w i) ∂γFin n)
      rw [contDiff_succ_iff_fderiv]
      refine ⟨fun x => (hasFDerivAt_laplaceFamily hF α x).differentiableAt, ?_, ?_⟩
      · intro h; exact absurd h (by exact_mod_cast WithTop.natCast_ne_top k)
      · have hfd : fderiv ℝ
            (fun x : Fin n → ℝ => ∫ w, F w * Real.exp (α * ∑ i, x i * w i) ∂γFin n)
            = fun x => ∑ j, (∫ w, (fun w => α * w j * F w) w
                * Real.exp (α * ∑ i, x i * w i) ∂γFin n) •
                (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ) := by
          funext x
          rw [(hasFDerivAt_laplaceFamily hF α x).fderiv]
          exact laplace_fderiv_eq_sum hF α x
        rw [hfd]
        apply ContDiff.sum
        intro j _
        have hpb : PolyBdd (fun w : Fin n → ℝ => α * w j * F w) :=
          polyBdd_smul_coord hF α j
        have hck := ih (fun w => α * w j * F w) hpb α
        exact hck.smul_const _

-- g(b•·) is PolyBdd when g is continuous bounded.
theorem polyBdd_comp_smul {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ z, ‖g z‖ ≤ M) (b : ℝ) :
    PolyBdd (fun w => g (fun i => b * w i)) := by
  refine ⟨hg.comp (continuous_pi (fun i => continuous_const.mul (continuous_apply i))),
    M, 0, (norm_nonneg _).trans (hM 0), fun w => ?_⟩
  rw [pow_zero, mul_one, ← Real.norm_eq_abs]
  exact hM _

set_option maxHeartbeats 800000 in
theorem contDiff_ouSemigroupFin_of_bounded (t : ℝ) (ht : 0 < t)
    {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ z, ‖g z‖ ≤ M) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (ouSemigroupFin t g) := by
  set a : ℝ := Real.exp (-t) with ha
  set b : ℝ := Real.sqrt (1 - Real.exp (-2 * t)) with hb
  have hb_pos : 0 < b := by
    rw [hb]; apply Real.sqrt_pos.mpr
    have : Real.exp (-2 * t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  -- the kernel form
  have hrep : ouSemigroupFin t g
      = fun x => Real.exp (- (∑ i, (a / b * x i) ^ 2) / 2)
          * ∫ w, (fun w => g (fun i => b * w i)) w
              * Real.exp ((a / b) * ∑ i, x i * w i) ∂γFin n := by
    funext x
    rw [ouSemigroupFin_eq_cmKernel (n := n) t ht hg hM x]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
    simp only [← ha, ← hb]
    have hS : (∑ i, (a / b * x i) * w i) = (a / b) * ∑ i, x i * w i := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [hS, Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
    rw [show (-((∑ i, (a / b * x i) ^ 2) / 2)) = (-∑ i, (a / b * x i) ^ 2) / 2 from by ring]
    set Aexp := Real.exp (a / b * ∑ i, x i * w i)
    set Bexp := Real.exp ((-∑ i, (a / b * x i) ^ 2) / 2)
    ring
  rw [hrep]
  have hJ : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun x : Fin n → ℝ => ∫ w, (fun w => g (fun i => b * w i)) w
          * Real.exp ((a / b) * ∑ i, x i * w i) ∂γFin n) := by
    rw [contDiff_infty]
    intro k
    exact contDiff_laplaceFamily k (fun w => g (fun i => b * w i))
      (polyBdd_comp_smul hg hM b) (a / b)
  have hpref : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun x : Fin n → ℝ => Real.exp (- (∑ i, (a / b * x i) ^ 2) / 2)) := by
    apply Real.contDiff_exp.comp
    apply ContDiff.div_const
    apply ContDiff.neg
    have hpt2 : (fun x : Fin n → ℝ => ∑ i, (a / b * x i) ^ 2)
        = (fun x => ∑ i ∈ (Finset.univ : Finset (Fin n)),
            (fun x : Fin n → ℝ => (a / b * x i) ^ 2) x) := rfl
    rw [hpt2]
    refine ContDiff.sum (fun i _ => ?_)
    exact ((contDiff_const.mul (contDiff_apply ℝ ℝ i))).pow 2
  exact hpref.mul hJ

/-! ### N1.b discharged: `C^∞` core preservation under the multivariate OU semigroup

The former textbook axiom `ouSemigroupFin_preserves_IsCore` is now a theorem,
discharged via the vetted Cameron–Martin kernel route (Workstream N1.b,
2026-05-19). See `contDiff_ouSemigroupFin_of_bounded` and the supporting
Cameron–Martin / Laplace-family infrastructure above. -/
/-- For a `C^∞` function `g`, the pure second coordinate derivative equals the
second derivative of the `i`-th coordinate section, evaluated at `x i`. This is
the smoothness-only analogue of `section_secondDeriv` (which assumes the
project-level `IsCoreFin`); it lets us transfer the section-wise second-derivative
bound from `ouSemigroupFin_preserves_core_bounds` to the `secondPartial` clause
of `IsCoreFin` for `ouSemigroupFin t f`. -/
theorem secondPartial_eq_section_deriv_of_contDiff {n : ℕ} {g : (Fin n → ℝ) → ℝ}
    (hg : ContDiff ℝ ∞ g) (i : Fin n) (x : Fin n → ℝ) :
    secondPartial i g x
      = deriv (deriv (fun s => g (Function.update x i s))) (x i) := by
  have hpartial_C1 : ContDiff ℝ ∞ (partialDeriv i g) := by
    unfold partialDeriv
    simpa using (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hsec : deriv (deriv (fun s => g (Function.update x i s)))
      = fun s => secondPartial i g (Function.update x i s) := by
    funext s
    have hsd : deriv (fun s => g (Function.update x i s))
        = fun s => partialDeriv i g (Function.update x i s) := by
      funext r
      have h_update := hasDerivAt_update x i r
      have h_f : HasFDerivAt g (fderiv ℝ g (Function.update x i r))
          (Function.update x i r) :=
        ((hg.differentiable (by simp)).differentiableAt).hasFDerivAt
      simpa [partialDeriv] using (h_f.comp_hasDerivAt r h_update).deriv
    rw [hsd]
    have h_update := hasDerivAt_update x i s
    have h_f : HasFDerivAt (partialDeriv i g)
        (fderiv ℝ (partialDeriv i g) (Function.update x i s))
        (Function.update x i s) :=
      ((hpartial_C1.differentiable (by simp)).differentiableAt).hasFDerivAt
    simpa [secondPartial] using (h_f.comp_hasDerivAt s h_update).deriv
  rw [hsec]
  simp

/-- **Multivariate OU smoothing preserves the `IsCoreFin` test algebra.**

For `t ≥ 0`, if `f` is `IsCoreFin`, then `ouSemigroupFin t f` is again
`IsCoreFin`. The `C^∞` regularity comes from the Cameron–Martin kernel
representation (`contDiff_ouSemigroupFin_of_bounded` for `t > 0`, and
`ouSemigroupFin_zero` for `t = 0`); the uniform bounds come from
`ouSemigroupFin_preserves_core_bounds`, with the section-wise second
derivative bound transferred to the `secondPartial` clause via
`secondPartial_eq_section_deriv_of_contDiff`.

Discharged 2026-05-19 (Workstream N1.b) via the vetted Cameron–Martin
kernel route. -/
theorem ouSemigroupFin_preserves_IsCore {n : ℕ}
    (t : ℝ) (ht : 0 ≤ t) {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    IsCoreFin (ouSemigroupFin t f) := by
  have hf_cont : Continuous f := hf.continuous
  obtain ⟨Mf, hMf⟩ := hf.bound_exists
  -- C^∞ regularity of `ouSemigroupFin t f`
  have hsmooth : ContDiff ℝ ∞ (ouSemigroupFin t f) := by
    rcases eq_or_lt_of_le ht with ht0 | htpos
    · rw [← ht0, ouSemigroupFin_zero]
      exact hf.contDiff
    · exact contDiff_ouSemigroupFin_of_bounded (n := n) t htpos hf_cont hMf
  -- uniform bounds
  obtain ⟨M, hMbound, hMpartial, hMsec⟩ :=
    ouSemigroupFin_preserves_core_bounds (n := n) t ht hf
  refine ⟨hsmooth, M, fun x => ⟨hMbound x, fun i => hMpartial i x, fun i => ?_⟩⟩
  rw [secondPartial_eq_section_deriv_of_contDiff hsmooth i x]
  exact hMsec i x (x i)

/-! ### N1.c: multivariate entropy decay for `f²` (BGL Thm. 5.5.2)

The 1D entropy-decay theorem is proved in `EuclideanEntropyDecay.lean`,
where the general per-coordinate building block
`Gaussian1D.boltzmannEntropy_ouSemigroup_decay_le` (FTC assembly of the
Fisher-info decay A1 and de Bruijn A2) is also extracted.

The multivariate bound is obtained by the **telescoping route** (vetted
gemini-3.1-pro-preview 2026-05-13, route confirmed by deep-think
2026-05-19): the macroscopic `(∫·)log(∫·)` terms cancel **once** for the
full operator because `ouSemigroupFin` preserves the Gaussian mean
(`ouSemigroupFin_integral_eq_of_bound`), so the centered `entropy`
difference equals the Boltzmann (`∫ h log h`) difference. The Boltzmann
difference telescopes over the per-coordinate factors with no further
macroscopic terms; each per-coordinate step is the integrated 1D bound,
and the per-coordinate Fisher informations stay controlled by
`4 · ouEnergyFin f f` via orthogonal Fisher monotonicity.

The infrastructure below is staged; the full assembly is in progress. -/

/-- The single-coordinate Ornstein–Uhlenbeck operator: the 1D OU
semigroup acting on coordinate `i` only, freezing the other
coordinates. Equals `Gaussian1D.ouSemigroup t (coordSection i x f)`
evaluated at `x i`. -/
def ouCoord (i : Fin n) (t : ℝ) (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => ∫ s, f (Function.update x i
    (Real.exp (-t) * x i + Real.sqrt (1 - Real.exp (-2 * t)) * s)) ∂Gaussian1D.γ

/-- `ouCoord` is the 1D OU semigroup of the coordinate section. -/
theorem ouCoord_eq_ouSemigroup_coordSection (i : Fin n) (t : ℝ)
    (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    ouCoord i t f x = Gaussian1D.ouSemigroup t (coordSection i x f) (x i) := by
  unfold ouCoord Gaussian1D.ouSemigroup coordSection
  rfl

/-- Bridge: updating coordinate `i` of `i.insertNth a y` to `b` gives
`i.insertNth b y`. Connects `ouCoord` (defined via `Function.update`)
to the `insertNth`-based Fubini lemma `integral_γFin_succAbove`. -/
theorem update_insertNth_same {n : ℕ} (i : Fin (n + 1)) (y : Fin n → ℝ)
    (a b : ℝ) :
    Function.update (Fin.insertNth (α := fun _ => ℝ) i a y) i b
      = Fin.insertNth (α := fun _ => ℝ) i b y := by
  funext j
  rcases eq_or_ne j i with h | h
  · subst h; simp
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq h
    rw [Function.update_of_ne (Fin.succAbove_ne i k)]
    simp

/-- `ouCoord` in `insertNth` coordinates: the single-coordinate OU on
coordinate `i`, evaluated at `i.insertNth s y`, is the 1D OU semigroup
applied to the 1D slice `r ↦ g (i.insertNth r y)`, at the point `s`. -/
theorem ouCoord_insertNth_eq {n : ℕ} (i : Fin (n + 1)) (t : ℝ)
    (g : (Fin (n + 1) → ℝ) → ℝ) (s : ℝ) (y : Fin n → ℝ) :
    ouCoord i t g (Fin.insertNth (α := fun _ => ℝ) i s y) =
      Gaussian1D.ouSemigroup t
        (fun r => g (Fin.insertNth (α := fun _ => ℝ) i r y)) s := by
  unfold ouCoord Gaussian1D.ouSemigroup
  have hi : (Fin.insertNth (α := fun _ => ℝ) i s y) i = s := by simp
  rw [hi]
  refine integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro u
  simp only [update_insertNth_same]

/-- The multivariate Boltzmann entropy `∫ h log h dγ_n` (no
`(∫h)log(∫h)` centering — the centered form is `DirichletSpace.entropy`
under `dirichletSpaceFin`). -/
def boltzmannEntropyFin (h : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ x, h x * Real.log (h x) ∂γFin n

/-- Per-coordinate Fisher information `∫ (∂_i h)² / h dγ_n`. -/
def fisherInfoFinCoord (i : Fin n) (h : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ x, (partialDeriv i h x) ^ 2 / h x ∂γFin n

/-- The 1D slice of `g` along coordinate `i` (other coordinates `y`)
equals the coordinate section based at `i.insertNth 0 y`. -/
theorem slice_eq_coordSection {n : ℕ} (i : Fin (n + 1))
    (g : (Fin (n + 1) → ℝ) → ℝ) (y : Fin n → ℝ) :
    (fun r => g (Fin.insertNth (α := fun _ => ℝ) i r y)) =
      coordSection i (Fin.insertNth (α := fun _ => ℝ) i 0 y) g := by
  funext r
  unfold coordSection
  rw [update_insertNth_same i y 0 r]

/-- **Swapped Fubini split for `γFin (n+1)`.** For a bounded measurable
`h`, the integral splits as the outer integral over the `n` remaining
coordinates of the inner 1D integral over coordinate `i`. The dominating
constant makes the product integrand integrable, so the order of
`integral_γFin_succAbove` can be swapped via `integral_integral_swap`. -/
theorem integral_γFin_succAbove_swap {n : ℕ} (i : Fin (n + 1))
    {h : (Fin (n + 1) → ℝ) → ℝ} (hh_meas : Measurable h) {C : ℝ}
    (hh_bd : ∀ z, ‖h z‖ ≤ C) :
    ∫ x, h x ∂γFin (n + 1) =
      ∫ y, ∫ s, h (Fin.insertNth (α := fun _ => ℝ) i s y)
        ∂Gaussian1D.γ ∂γFin n := by
  have hh_int : Integrable h (γFin (n + 1)) := integrable_of_bound hh_meas hh_bd
  rw [integral_γFin_succAbove (n := n) (i := i) hh_int]
  -- Joint integrability of `(s, y) ↦ h (i.insertNth s y)` on `γ × γFin n`.
  set F : ℝ → (Fin n → ℝ) → ℝ :=
    fun s y => h (Fin.insertNth (α := fun _ => ℝ) i s y) with hF
  have hF_meas : Measurable (Function.uncurry F) := by
    have hcont : Continuous (fun p : ℝ × (Fin n → ℝ) =>
        Fin.insertNth (α := fun _ => ℝ) i p.1 p.2) :=
      Continuous.finInsertNth i continuous_fst continuous_snd
    have : Measurable (fun p : ℝ × (Fin n → ℝ) =>
        h (Fin.insertNth (α := fun _ => ℝ) i p.1 p.2)) :=
      hh_meas.comp hcont.measurable
    change Measurable (fun p : ℝ × (Fin n → ℝ) => F p.1 p.2)
    simpa only [hF] using this
  have hF_int : Integrable (Function.uncurry F)
      (Gaussian1D.γ.prod (γFin n)) := by
    refine Integrable.mono' (integrable_const C)
      hF_meas.aestronglyMeasurable ?_
    filter_upwards with p
    simpa [Function.uncurry, hF] using hh_bd _
  exact MeasureTheory.integral_integral_swap hF_int

/-- **Per-coordinate Boltzmann-entropy step bound.**

For a measurable `g` whose coordinate-`i` 1D slices are `C¹` with slice
derivative `D` (a supplied measurable function with `|D| ≤ M`),
`ε ≤ g ≤ M`, and `t ≥ 0`,
`BE(g) - BE(ouCoord i t g) ≤ (1 - e^{-2t})/2 · ∫ D²/g dγ`.

This is the 1D bound `Gaussian1D.boltzmannEntropy_ouSemigroup_decay_le`
applied to each coordinate-`i` slice and integrated over the remaining
coordinates via `integral_γFin_succAbove`. The Fubini integrability of
the dominating slices follows from the uniform bounds.

The hypotheses are stated at the level of 1D slices (not joint `C^∞`):
`ouCoord j` smooths only the integrated coordinate, so telescope
iterates `ouCoordSet S t g` are in general only `C¹` jointly along the
passthrough coordinates. The slice-level `C¹` hypotheses are exactly
what the internal 1-parameter analysis needs (Gemini deep-think +
3.1-pro vetted, 2026-05-19).

**Strategy:** rewrite `BE` via `integral_γFin_succAbove i`; identify the
inner 1D integral as the 1D Boltzmann entropy of the slice `G_y` and
`ouCoord` as `Gaussian1D.ouSemigroup` of `G_y` (`ouCoord_insertNth_eq`);
apply the 1D lemma slicewise and `integral_mono` over `γ_n`; finally
identify `∫ I(G_y) dγ_n` with `∫ D²/g dγ` via the supplied slice
derivative.

The coordinate-`i` slice derivative is supplied abstractly as `D` (with
`h_slice_deriv : deriv (slice y) = D ∘ insertNth i · y`). For the
telescope iterates `g = ouCoordSet S t g_ε`, `D = ouCoordSet S t (∂_k
g_ε)` via the 1-parameter commutation `hasDerivAt_slice_ouCoordSet`,
which never forms the (potentially ill-behaved) joint Fréchet partial of
the iterate. -/
theorem boltzmannEntropyFin_ouCoord_step_le {n : ℕ} (i : Fin (n + 1))
    (g D : (Fin (n + 1) → ℝ) → ℝ) (hg_meas : Measurable g)
    (h_slice_C1 : ∀ y : Fin n → ℝ,
      ContDiff ℝ 1 (fun r => g (Fin.insertNth (α := fun _ => ℝ) i r y)))
    (h_slice_deriv : ∀ y : Fin n → ℝ,
      deriv (fun r => g (Fin.insertNth (α := fun _ => ℝ) i r y)) =
        fun r => D (Fin.insertNth (α := fun _ => ℝ) i r y))
    (hD_meas : Measurable D) {ε M : ℝ}
    (hε : 0 < ε) (hg_lo : ∀ x, ε ≤ g x) (hg_hi : ∀ x, g x ≤ M)
    (hD_bd : ∀ x, |D x| ≤ M) (t : ℝ) (ht : 0 ≤ t) :
    boltzmannEntropyFin g - boltzmannEntropyFin (ouCoord i t g) ≤
      (1 - Real.exp (-2 * t)) / 2 * ∫ x, (D x) ^ 2 / g x ∂γFin (n + 1) := by
  classical
  have hε_nn : (0 : ℝ) ≤ ε := hε.le
  have hεM : ε ≤ M := le_trans (hg_lo (fun _ => 0)) (hg_hi (fun _ => 0))
  have hM_pos : 0 < M := lt_of_lt_of_le hε hεM
  -- The coordinate-`i` slice and its packaged 1D facts.
  set G : (Fin n → ℝ) → ℝ → ℝ :=
    fun y r => g (Fin.insertNth (α := fun _ => ℝ) i r y) with hG
  have hG_C1 : ∀ y, ContDiff ℝ 1 (G y) := h_slice_C1
  have hG_lo : ∀ y r, ε ≤ G y r := fun y r => hg_lo _
  have hG_hi : ∀ y r, G y r ≤ M := fun y r => hg_hi _
  have hG_deriv : ∀ y, deriv (G y) =
      fun r => D (Fin.insertNth (α := fun _ => ℝ) i r y) :=
    h_slice_deriv
  have hG'_bd : ∀ y r, |deriv (G y) r| ≤ M := by
    intro y r
    rw [hG_deriv y]
    exact hD_bd _
  -- 1D entropy-decay bound applied to each slice.
  have h1D : ∀ y, Gaussian1D.boltzmannEntropy (G y) -
      Gaussian1D.boltzmannEntropy (Gaussian1D.ouSemigroup t (G y)) ≤
      (1 - Real.exp (-2 * t)) / 2 * Gaussian1D.fisherInfo (G y) := fun y =>
    Gaussian1D.boltzmannEntropy_ouSemigroup_decay_le (G y) (hG_C1 y) hε
      (hG_lo y) (hG_hi y) (hG'_bd y) t ht
  -- Uniform `|s log s|` bound on `[0, M]` (covers the slice ranges).
  obtain ⟨B, hB_nn, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧
      ∀ s ∈ Set.Icc (0 : ℝ) M, |s * Real.log s| ≤ B := by
    have h_compact : IsCompact (Set.Icc (0 : ℝ) M) := isCompact_Icc
    have h_cont_abs : Continuous (fun s => |s * Real.log s|) :=
      Real.continuous_mul_log.abs
    obtain ⟨B, hB⟩ := (h_compact.image h_cont_abs).bddAbove
    exact ⟨max B 0, le_max_right _ _, fun s hs =>
      (hB ⟨s, hs, rfl⟩).trans (le_max_left _ _)⟩
  -- (1) `boltzmannEntropyFin g = ∫_y boltzmannEntropy (G y) dγ_n`.
  have hBE_g : boltzmannEntropyFin g =
      ∫ y, Gaussian1D.boltzmannEntropy (G y) ∂γFin n := by
    unfold boltzmannEntropyFin Gaussian1D.boltzmannEntropy
    rw [integral_γFin_succAbove_swap (n := n) (i := i)
      (h := fun x => g x * Real.log (g x))
      (hg_meas.mul (Real.measurable_log.comp hg_meas)) (C := B)
      (fun z => by
        rw [Real.norm_eq_abs]
        exact hB _ ⟨le_trans hε_nn (hg_lo z), hg_hi z⟩)]
  -- The 1D slice OU is bounded by `M` (1D OU of a function ≤ M).
  have hPG_bd : ∀ y s, ε ≤ Gaussian1D.ouSemigroup t (G y) s ∧
      Gaussian1D.ouSemigroup t (G y) s ≤ M := by
    intro y s
    have hGy_int : Integrable
        (fun u => G y (Real.exp (-t) * s +
          Real.sqrt (1 - Real.exp (-2 * t)) * u)) Gaussian1D.γ := by
      refine Integrable.mono' (integrable_const M) ?_ ?_
      · exact (((hG_C1 y).continuous).measurable.comp
          (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
      · filter_upwards with u
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨le_trans (by linarith [hε_nn]) (le_of_lt (lt_of_lt_of_le hε (hG_lo y _))),
          (hG_hi y _)⟩
    constructor
    · show ε ≤ ∫ u, G y (Real.exp (-t) * s +
        Real.sqrt (1 - Real.exp (-2 * t)) * u) ∂Gaussian1D.γ
      calc ε = ∫ _u, ε ∂Gaussian1D.γ := by simp
        _ ≤ _ := integral_mono (integrable_const ε) hGy_int (fun u => hG_lo y _)
    · show ∫ u, G y (Real.exp (-t) * s +
        Real.sqrt (1 - Real.exp (-2 * t)) * u) ∂Gaussian1D.γ ≤ M
      calc ∫ u, _ ∂Gaussian1D.γ
          ≤ ∫ _u, M ∂Gaussian1D.γ :=
            integral_mono hGy_int (integrable_const M) (fun u => hG_hi y _)
        _ = M := by simp
  -- (2) `boltzmannEntropyFin (ouCoord i t g) = ∫_y BE(P_t (G y)) dγ_n`.
  have h_ouCoord_meas : Measurable (ouCoord i t g) := by
    have hupd : Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ =>
        Function.update p.1 i (Real.exp (-t) * p.1 i +
          Real.sqrt (1 - Real.exp (-2 * t)) * p.2)) := by
      have hval : Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ =>
          Real.exp (-t) * p.1 i +
            Real.sqrt (1 - Real.exp (-2 * t)) * p.2) :=
        (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).add
          (measurable_const.mul measurable_snd)
      exact measurable_update'.comp (measurable_fst.prodMk hval)
    have hjoint : Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ =>
        g (Function.update p.1 i (Real.exp (-t) * p.1 i +
          Real.sqrt (1 - Real.exp (-2 * t)) * p.2))) := hg_meas.comp hupd
    exact (hjoint.stronglyMeasurable.integral_prod_right').measurable
  have hBE_ouCoord : boltzmannEntropyFin (ouCoord i t g) =
      ∫ y, Gaussian1D.boltzmannEntropy
        (Gaussian1D.ouSemigroup t (G y)) ∂γFin n := by
    unfold boltzmannEntropyFin Gaussian1D.boltzmannEntropy
    rw [integral_γFin_succAbove_swap (n := n) (i := i)
      (h := fun x => ouCoord i t g x * Real.log (ouCoord i t g x))
      (h_ouCoord_meas.mul (Real.measurable_log.comp h_ouCoord_meas)) (C := B)
      (fun z => by
        rw [Real.norm_eq_abs]
        -- `ouCoord` is itself a 1D OU of a slice, so bounded in `[ε, M]`.
        have hval : ouCoord i t g z =
            Gaussian1D.ouSemigroup t
              (fun r => g (Fin.insertNth (α := fun _ => ℝ) i r
                (Fin.removeNth i z))) (z i) := by
          have hz : z = Fin.insertNth (α := fun _ => ℝ) i (z i)
              (Fin.removeNth i z) := (Fin.insertNth_self_removeNth i z).symm
          conv_lhs => rw [hz]
          rw [ouCoord_insertNth_eq i t g (z i) (Fin.removeNth i z)]
        rw [hval]
        have hb := hPG_bd (Fin.removeNth i z) (z i)
        rw [hG] at hb
        exact hB _ ⟨le_trans hε_nn hb.1, hb.2⟩)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
    simp only [hG, ouCoord_insertNth_eq i t g s y]
  -- (3) `∫ D²/g dγ = ∫_y fisherInfo (G y) dγ_n`.
  have hFI_g : (∫ x, (D x) ^ 2 / g x ∂γFin (n + 1)) =
      ∫ y, Gaussian1D.fisherInfo (G y) ∂γFin n := by
    unfold Gaussian1D.fisherInfo
    rw [integral_γFin_succAbove_swap (n := n) (i := i)
      (h := fun x => (D x) ^ 2 / g x)
      ((hD_meas.pow_const 2).div hg_meas) (C := M ^ 2 / ε)
      (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (div_nonneg (sq_nonneg _) (le_trans hε_nn (hg_lo z)))]
        have hnum : (D z) ^ 2 ≤ M ^ 2 := by
          have := hD_bd z
          nlinarith [abs_nonneg (D z), sq_abs (D z)]
        have hden : ε ≤ g z := hg_lo z
        have hgz_pos : 0 < g z := lt_of_lt_of_le hε hden
        have hstep1 : (D z) ^ 2 / g z ≤ M ^ 2 / g z :=
          div_le_div_of_nonneg_right hnum hgz_pos.le
        have hstep2 : M ^ 2 / g z ≤ M ^ 2 / ε :=
          div_le_div_of_nonneg_left (sq_nonneg _) hε hden
        linarith)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
    have hgd : deriv (G y) s =
        D (Fin.insertNth (α := fun _ => ℝ) i s y) := by
      rw [hG_deriv y]
    have hgv : G y s = g (Fin.insertNth (α := fun _ => ℝ) i s y) := by
      simp [hG]
    simp only []
    rw [hgd, hgv]
  -- Joint measurability of the slice `(y, s) ↦ g (i.insertNth s y)`.
  have h_insert_cont : Continuous (fun p : (Fin n → ℝ) × ℝ =>
      Fin.insertNth (α := fun _ => ℝ) i p.2 p.1) :=
    Continuous.finInsertNth i continuous_snd continuous_fst
  -- `y ↦ boltzmannEntropy (G y)` is measurable.
  have hBE_Gy_meas : Measurable
      (fun y => Gaussian1D.boltzmannEntropy (G y)) := by
    have hj : Measurable (fun p : (Fin n → ℝ) × ℝ =>
        G p.1 p.2 * Real.log (G p.1 p.2)) := by
      have hgj : Measurable (fun p : (Fin n → ℝ) × ℝ => G p.1 p.2) := by
        simpa [hG] using hg_meas.comp h_insert_cont.measurable
      exact hgj.mul (Real.measurable_log.comp hgj)
    simpa [Gaussian1D.boltzmannEntropy] using
      hj.stronglyMeasurable.integral_prod_right'.measurable
  -- `y ↦ boltzmannEntropy (P_t (G y))` is measurable.
  have hBE_PGy_meas : Measurable
      (fun y => Gaussian1D.boltzmannEntropy
        (Gaussian1D.ouSemigroup t (G y))) := by
    have hj : Measurable (fun p : (Fin n → ℝ) × ℝ =>
        Gaussian1D.ouSemigroup t (G p.1) p.2 *
          Real.log (Gaussian1D.ouSemigroup t (G p.1) p.2)) := by
      have hgj : Measurable (fun q : ((Fin n → ℝ) × ℝ) × ℝ =>
          G q.1.1 (Real.exp (-t) * q.1.2 +
            Real.sqrt (1 - Real.exp (-2 * t)) * q.2)) := by
        have : Measurable (fun q : ((Fin n → ℝ) × ℝ) × ℝ =>
            Fin.insertNth (α := fun _ => ℝ) i
              (Real.exp (-t) * q.1.2 +
                Real.sqrt (1 - Real.exp (-2 * t)) * q.2) q.1.1) :=
          (Continuous.finInsertNth i
            ((continuous_const.mul (continuous_snd.comp continuous_fst)).add
              (continuous_const.mul continuous_snd))
            (continuous_fst.comp continuous_fst)).measurable
        simpa [hG] using hg_meas.comp this
      have hP : Measurable (fun p : (Fin n → ℝ) × ℝ =>
          Gaussian1D.ouSemigroup t (G p.1) p.2) := by
        simpa [Gaussian1D.ouSemigroup] using
          hgj.stronglyMeasurable.integral_prod_right'.measurable
      exact hP.mul (Real.measurable_log.comp hP)
    simpa [Gaussian1D.boltzmannEntropy] using
      hj.stronglyMeasurable.integral_prod_right'.measurable
  -- `y ↦ fisherInfo (G y)` is measurable.
  have hFI_Gy_meas : Measurable
      (fun y => Gaussian1D.fisherInfo (G y)) := by
    have hj : Measurable (fun p : (Fin n → ℝ) × ℝ =>
        (deriv (G p.1) p.2) ^ 2 / G p.1 p.2) := by
      have hd : Measurable (fun p : (Fin n → ℝ) × ℝ =>
          deriv (G p.1) p.2) := by
        have : (fun p : (Fin n → ℝ) × ℝ => deriv (G p.1) p.2) =
            fun p => D
              (Fin.insertNth (α := fun _ => ℝ) i p.2 p.1) := by
          funext p; rw [hG_deriv p.1]
        rw [this]
        exact hD_meas.comp h_insert_cont.measurable
      have hgj : Measurable (fun p : (Fin n → ℝ) × ℝ => G p.1 p.2) := by
        simpa [hG] using hg_meas.comp h_insert_cont.measurable
      exact (hd.pow_const 2).div hgj
    simpa [Gaussian1D.fisherInfo] using
      hj.stronglyMeasurable.integral_prod_right'.measurable
  -- Uniform bounds for integrability on the probability space `γFin n`.
  have hBE_Gy_bd : ∀ y, |Gaussian1D.boltzmannEntropy (G y)| ≤ B := by
    intro y
    unfold Gaussian1D.boltzmannEntropy
    calc |∫ s, G y s * Real.log (G y s) ∂Gaussian1D.γ|
        ≤ ∫ s, |G y s * Real.log (G y s)| ∂Gaussian1D.γ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _s, B ∂Gaussian1D.γ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun s => abs_nonneg _))
            (integrable_const B) (Filter.Eventually.of_forall (fun s =>
              hB _ ⟨le_trans hε_nn (hG_lo y s), hG_hi y s⟩))
      _ = B := by simp
  have hBE_PGy_bd : ∀ y, |Gaussian1D.boltzmannEntropy
      (Gaussian1D.ouSemigroup t (G y))| ≤ B := by
    intro y
    unfold Gaussian1D.boltzmannEntropy
    calc |∫ s, Gaussian1D.ouSemigroup t (G y) s *
            Real.log (Gaussian1D.ouSemigroup t (G y) s) ∂Gaussian1D.γ|
        ≤ ∫ s, |Gaussian1D.ouSemigroup t (G y) s *
            Real.log (Gaussian1D.ouSemigroup t (G y) s)| ∂Gaussian1D.γ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _s, B ∂Gaussian1D.γ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun s => abs_nonneg _))
            (integrable_const B) (Filter.Eventually.of_forall (fun s =>
              hB _ ⟨le_trans hε_nn (hPG_bd y s).1, (hPG_bd y s).2⟩))
      _ = B := by simp
  have hFI_Gy_nn : ∀ y, 0 ≤ Gaussian1D.fisherInfo (G y) := by
    intro y
    unfold Gaussian1D.fisherInfo
    refine integral_nonneg (fun s => ?_)
    exact div_nonneg (sq_nonneg _) (le_trans hε_nn (hG_lo y s))
  have hFI_Gy_bd : ∀ y, Gaussian1D.fisherInfo (G y) ≤ M ^ 2 / ε := by
    intro y
    unfold Gaussian1D.fisherInfo
    have hint : Integrable (fun s => (deriv (G y) s) ^ 2 / G y s)
        Gaussian1D.γ := by
      refine Integrable.mono' (integrable_const (M ^ 2 / ε)) ?_ ?_
      · exact (((hG_C1 y).continuous_deriv (by norm_num)).measurable.pow_const 2
          |>.div (hG_C1 y).continuous.measurable).aestronglyMeasurable
      · filter_upwards with s
        rw [Real.norm_eq_abs, abs_of_nonneg
          (div_nonneg (sq_nonneg _) (le_trans hε_nn (hG_lo y s)))]
        have hnum : (deriv (G y) s) ^ 2 ≤ M ^ 2 := by
          have := hG'_bd y s
          nlinarith [abs_nonneg (deriv (G y) s), sq_abs (deriv (G y) s)]
        have hden : ε ≤ G y s := hG_lo y s
        have hgz : 0 < G y s := lt_of_lt_of_le hε hden
        have h1 : (deriv (G y) s) ^ 2 / G y s ≤ M ^ 2 / G y s :=
          div_le_div_of_nonneg_right hnum hgz.le
        have h2 : M ^ 2 / G y s ≤ M ^ 2 / ε :=
          div_le_div_of_nonneg_left (sq_nonneg _) hε hden
        linarith
    calc ∫ s, (deriv (G y) s) ^ 2 / G y s ∂Gaussian1D.γ
        ≤ ∫ _s, M ^ 2 / ε ∂Gaussian1D.γ := by
          refine integral_mono hint (integrable_const _) (fun s => ?_)
          have hnum : (deriv (G y) s) ^ 2 ≤ M ^ 2 := by
            have := hG'_bd y s
            nlinarith [abs_nonneg (deriv (G y) s), sq_abs (deriv (G y) s)]
          have hden : ε ≤ G y s := hG_lo y s
          have hgz : 0 < G y s := lt_of_lt_of_le hε hden
          have h1 : (deriv (G y) s) ^ 2 / G y s ≤ M ^ 2 / G y s :=
            div_le_div_of_nonneg_right hnum hgz.le
          have h2 : M ^ 2 / G y s ≤ M ^ 2 / ε :=
            div_le_div_of_nonneg_left (sq_nonneg _) hε hden
          linarith
      _ = M ^ 2 / ε := by simp
  -- Integrability on the probability space `γFin n` from boundedness.
  have hInt_BE_Gy : Integrable (fun y => Gaussian1D.boltzmannEntropy (G y))
      (γFin n) :=
    Integrable.mono' (integrable_const B) hBE_Gy_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs]; exact hBE_Gy_bd y))
  have hInt_BE_PGy : Integrable (fun y => Gaussian1D.boltzmannEntropy
      (Gaussian1D.ouSemigroup t (G y))) (γFin n) :=
    Integrable.mono' (integrable_const B) hBE_PGy_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs]; exact hBE_PGy_bd y))
  have hInt_FI_Gy : Integrable (fun y => Gaussian1D.fisherInfo (G y))
      (γFin n) :=
    Integrable.mono' (integrable_const (M ^ 2 / ε))
      hFI_Gy_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hFI_Gy_nn y)]; exact hFI_Gy_bd y))
  -- Assembly: `integral_mono` of the slicewise 1D bound `h1D`.
  rw [hBE_g, hBE_ouCoord, hFI_g, ← integral_sub hInt_BE_Gy hInt_BE_PGy,
    ← integral_const_mul]
  refine integral_mono (hInt_BE_Gy.sub hInt_BE_PGy)
    (hInt_FI_Gy.const_mul _) (fun y => h1D y)

/-- **Macroscopic-term cancellation.** For an `IsCoreFin` test function
`f`, the centered entropy difference of `g = f²` and `P_t g` equals
their Boltzmann-entropy difference, because the multivariate OU
semigroup preserves the Gaussian mean
(`ouSemigroupFin_integral_eq_of_bound`), so the two `(∫·)log(∫·)`
terms are identical and cancel in the difference.

This is the only place the macroscopic terms enter, and it requires no
derivatives — pure mean preservation plus linearity. -/
theorem entropy_sub_eq_boltzmann_sub {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (t : ℝ) (ht : 0 ≤ t) (hf : IsCoreFin f) :
    DirichletSpace.entropy (ds := dirichletSpaceFin (n := n)) (fun x => f x * f x) -
        DirichletSpace.entropy (ds := dirichletSpaceFin (n := n))
          (ouSemigroupFin t (fun x => f x * f x)) =
      boltzmannEntropyFin (fun x => f x * f x) -
        boltzmannEntropyFin (ouSemigroupFin t (fun x => f x * f x)) := by
  obtain ⟨M, hM⟩ := hf.bound_exists
  have hM_nn : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0)
  set g : (Fin n → ℝ) → ℝ := fun x => f x * f x with hg_def
  have hg_meas : Measurable g := (hf.measurable.mul hf.measurable)
  have hg_bd : ∀ x, ‖g x‖ ≤ M ^ 2 := by
    intro x
    have hfx : |f x| ≤ M := by rw [← Real.norm_eq_abs]; exact hM x
    have hgx : g x = f x * f x := rfl
    have hnn : 0 ≤ g x := by rw [hgx]; exact mul_self_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, hgx]
    nlinarith [abs_nonneg (f x), sq_abs (f x)]
  -- Mean preservation: ∫ P_t g dγ = ∫ g dγ.
  have h_mean : ∫ x, ouSemigroupFin t g x ∂γFin n = ∫ x, g x ∂γFin n :=
    ouSemigroupFin_integral_eq_of_bound (n := n) (M := M ^ 2) t ht hg_meas hg_bd
  -- Unfold the centered entropy and cancel the equal macroscopic terms.
  unfold DirichletSpace.entropy boltzmannEntropyFin
  show
    ((∫ x, g x * Real.log (g x) ∂γFin n) -
        (∫ x, g x ∂γFin n) * Real.log (∫ x, g x ∂γFin n)) -
      ((∫ x, ouSemigroupFin t g x * Real.log (ouSemigroupFin t g x) ∂γFin n) -
        (∫ x, ouSemigroupFin t g x ∂γFin n) *
          Real.log (∫ x, ouSemigroupFin t g x ∂γFin n)) =
    (∫ x, g x * Real.log (g x) ∂γFin n) -
      (∫ x, ouSemigroupFin t g x * Real.log (ouSemigroupFin t g x) ∂γFin n)
  rw [h_mean]
  ring

/-- The coordinate-`i` partial of `f² + ε` is `2 f ∂_i f`. -/
theorem partialDeriv_sq_add_const {n : ℕ} (i : Fin n)
    {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (ε : ℝ) :
    partialDeriv i (fun x => f x * f x + ε) =
      fun x => 2 * f x * partialDeriv i f x := by
  have hmul : partialDeriv i (fun x => f x * f x) =
      fun x => partialDeriv i f x * f x + f x * partialDeriv i f x := by
    have := partialDeriv_mul (n := n) i hf.contDiff hf.contDiff
    simpa [Pi.mul_def] using this
  funext x
  have hadd : partialDeriv i (fun x => f x * f x + ε) x =
      partialDeriv i (fun x => f x * f x) x := by
    unfold partialDeriv
    rw [show (fun x => f x * f x + ε) =
      (fun x => f x * f x) + (fun _ => ε) from rfl]
    have hd1 : DifferentiableAt ℝ (fun x => f x * f x) x :=
      ((hf.contDiff.mul hf.contDiff).differentiable (by simp)).differentiableAt
    rw [fderiv_add hd1 (by simp), add_apply]
    simp
  rw [hadd, hmul]
  ring

/-- **Per-`ε` energy bookkeeping (T3).** For `IsCoreFin f` and `ε > 0`,
`Σ_i I_i(f² + ε) ≤ 4 · ouEnergyFin f f`, because
`(∂_i(f²+ε))² / (f²+ε) = 4 f² (∂_i f)² / (f²+ε) ≤ 4 (∂_i f)²`. -/
theorem sum_fisherInfoFinCoord_sq_add_const_le {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) {ε : ℝ} (hε : 0 < ε) :
    ∑ i : Fin n, fisherInfoFinCoord i (fun x => f x * f x + ε) ≤
      4 * ouEnergyFin f f := by
  obtain ⟨hf_smooth, M, hM⟩ := hf
  have hf : IsCoreFin f := ⟨hf_smooth, M, hM⟩
  have hM_nn : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0).1
  have hden_pos : ∀ x : Fin n → ℝ, 0 < f x * f x + ε := fun x => by
    have : 0 ≤ f x * f x := mul_self_nonneg _
    linarith
  -- Pointwise: `(∂_i(f²+ε))²/(f²+ε) ≤ 4 (∂_i f)²`.
  have h_ptwise : ∀ i (x : Fin n → ℝ),
      (partialDeriv i (fun x => f x * f x + ε) x) ^ 2 /
        (f x * f x + ε) ≤ 4 * (partialDeriv i f x) ^ 2 := by
    intro i x
    rw [partialDeriv_sq_add_const i hf ε]
    have hdp : 0 < f x * f x + ε := hden_pos x
    have hnum : (2 * f x * partialDeriv i f x) ^ 2 =
        4 * (f x * f x) * (partialDeriv i f x) ^ 2 := by ring
    rw [hnum]
    have hfrac : f x * f x / (f x * f x + ε) ≤ 1 := by
      rw [div_le_one hdp]; nlinarith [mul_self_nonneg (f x)]
    have hpd_nn : 0 ≤ (partialDeriv i f x) ^ 2 := sq_nonneg _
    have hrw : 4 * (f x * f x) * (partialDeriv i f x) ^ 2 /
        (f x * f x + ε) =
        (f x * f x / (f x * f x + ε)) * (4 * (partialDeriv i f x) ^ 2) := by
      rw [mul_comm (f x * f x / (f x * f x + ε)) _, ← mul_div_assoc]
      ring_nf
    rw [hrw]
    nlinarith [hfrac, hpd_nn]
  -- Uniform `M`-bounds on `|f|` and `|∂_i f|`.
  have hf_le : ∀ x, |f x| ≤ M := fun x => by
    rw [← Real.norm_eq_abs]; exact (hM x).1
  have hpd_le : ∀ i x, |partialDeriv i f x| ≤ M := fun i x => by
    rw [← Real.norm_eq_abs]; exact (hM x).2.1 i
  -- Measurability.
  have hf_meas : Measurable f := hf.measurable
  have hpd_meas : ∀ i, Measurable (partialDeriv i f) := fun i =>
    hf.partial_measurable i
  -- Integrability of each numerator/denominator quotient: bounded by
  -- `(2 M²)² / ε`.
  have h_int_lhs : ∀ i, Integrable
      (fun x => (partialDeriv i (fun x => f x * f x + ε) x) ^ 2 /
        (f x * f x + ε)) (γFin n) := by
    intro i
    refine Integrable.mono' (integrable_const ((2 * M ^ 2) ^ 2 / ε)) ?_ ?_
    · have hpdc : Measurable
          (partialDeriv i (fun x => f x * f x + ε)) := by
        rw [partialDeriv_sq_add_const i hf ε]
        exact (measurable_const.mul hf_meas).mul (hpd_meas i)
      have hden : Measurable (fun x => f x * f x + ε) :=
        (hf_meas.mul hf_meas).add_const ε
      exact ((hpdc.pow_const 2).div hden).aestronglyMeasurable
    · filter_upwards with x
      have hdp : 0 < f x * f x + ε := hden_pos x
      have hquot_nn : 0 ≤ (partialDeriv i (fun x => f x * f x + ε) x) ^ 2 /
          (f x * f x + ε) := div_nonneg (sq_nonneg _) hdp.le
      rw [Real.norm_eq_abs, abs_of_nonneg hquot_nn]
      rw [partialDeriv_sq_add_const i hf ε]
      have hnum_bd : (2 * f x * partialDeriv i f x) ^ 2 ≤ (2 * M ^ 2) ^ 2 := by
        have h1 : |2 * f x * partialDeriv i f x| ≤ 2 * M ^ 2 := by
          rw [abs_mul, abs_mul]
          have : (2 : ℝ) * |f x| * |partialDeriv i f x| ≤ 2 * M * M := by
            have := hf_le x; have := hpd_le i x
            nlinarith [abs_nonneg (f x), abs_nonneg (partialDeriv i f x)]
          simpa [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] using
            le_trans this (by nlinarith)
        nlinarith [abs_nonneg (2 * f x * partialDeriv i f x),
          sq_abs (2 * f x * partialDeriv i f x)]
      calc (2 * f x * partialDeriv i f x) ^ 2 / (f x * f x + ε)
          ≤ (2 * M ^ 2) ^ 2 / (f x * f x + ε) :=
            div_le_div_of_nonneg_right hnum_bd hdp.le
        _ ≤ (2 * M ^ 2) ^ 2 / ε :=
            div_le_div_of_nonneg_left (sq_nonneg _) hε
              (by nlinarith [mul_self_nonneg (f x)])
  have h_int_rhs : Integrable
      (fun x => ∑ i : Fin n, 4 * (partialDeriv i f x) ^ 2) (γFin n) := by
    refine integrable_finsetSum _ (fun i _ => ?_)
    refine Integrable.mono' (integrable_const (4 * M ^ 2)) ?_ ?_
    · exact (((hpd_meas i).pow_const 2).const_mul 4).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have : (partialDeriv i f x) ^ 2 ≤ M ^ 2 := by
        have := hpd_le i x
        nlinarith [abs_nonneg (partialDeriv i f x), sq_abs (partialDeriv i f x)]
      nlinarith
  -- Combine: sum of integrals, pointwise bound, then `∫ Σ 4 (∂_i f)²`.
  simp only [fisherInfoFinCoord]
  rw [← integral_finsetSum _ (fun i _ => h_int_lhs i)]
  have hsum_le : ∀ x,
      ∑ i : Fin n, (partialDeriv i (fun x => f x * f x + ε) x) ^ 2 /
        (f x * f x + ε) ≤ ∑ i : Fin n, 4 * (partialDeriv i f x) ^ 2 :=
    fun x => Finset.sum_le_sum (fun i _ => h_ptwise i x)
  have hstep : ∫ x, (∑ i : Fin n,
      (partialDeriv i (fun x => f x * f x + ε) x) ^ 2 /
        (f x * f x + ε)) ∂γFin n ≤
      ∫ x, (∑ i : Fin n, 4 * (partialDeriv i f x) ^ 2) ∂γFin n :=
    integral_mono (integrable_finsetSum _ (fun i _ => h_int_lhs i))
      h_int_rhs hsum_le
  refine le_trans hstep ?_
  -- `∫ Σ 4 (∂_i f)² = 4 · ouEnergyFin f f`.
  have henergy : ∫ x, (∑ i : Fin n, 4 * (partialDeriv i f x) ^ 2) ∂γFin n =
      4 * ouEnergyFin f f := by
    unfold ouEnergyFin ouGammaFin
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  exact le_of_eq henergy

/-! ### T1: factorization of `ouSemigroupFin` into single-coordinate OUs

The multivariate OU Mehler kernel factors over coordinates, so the
`n`-dimensional operator equals the composition of the `n`
single-coordinate `ouCoord` operators (in any order). We formalize this
through a coordinate-set–indexed operator `ouCoordSet S` (OU applied on
the coordinates in `S`, freezing the rest), with `ouCoordSet ∅ = id`,
`ouCoordSet univ = ouSemigroupFin`, and the one-coordinate composition
step `ouCoord j (ouCoordSet S) = ouCoordSet (insert j S)` for `j ∉ S`. -/

/-- The OU Mehler shift restricted to a coordinate set `S`: coordinates
in `S` are pushed through the 1D Mehler map `xᵢ ↦ e^{-t}xᵢ + b yᵢ`,
coordinates outside `S` are frozen. -/
def setShift (S : Finset (Fin n)) (t : ℝ) (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if i ∈ S then
      Real.exp (-t) * x i + Real.sqrt (1 - Real.exp (-2 * t)) * y i
    else x i

/-- The OU semigroup applied on the coordinate subset `S` only. -/
def ouCoordSet (S : Finset (Fin n)) (t : ℝ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun x => ∫ y, f (setShift S t x y) ∂γFin n

theorem setShift_empty (t : ℝ) (x y : Fin n → ℝ) :
    setShift (∅ : Finset (Fin n)) t x y = x := by
  funext i; simp [setShift]

theorem setShift_univ (t : ℝ) (x y : Fin n → ℝ) :
    setShift (Finset.univ : Finset (Fin n)) t x y = ouShiftFin t x y := by
  funext i; simp [setShift, ouShiftFin]

theorem ouCoordSet_empty (t : ℝ) {f : (Fin n → ℝ) → ℝ} :
    ouCoordSet (∅ : Finset (Fin n)) t f = f := by
  funext x
  unfold ouCoordSet
  simp only [setShift_empty]
  simp

theorem ouCoordSet_univ (t : ℝ) {f : (Fin n → ℝ) → ℝ} :
    ouCoordSet (Finset.univ : Finset (Fin n)) t f = ouSemigroupFin t f := by
  funext x
  show (∫ y, f (setShift Finset.univ t x y) ∂γFin n) =
    ∫ y, f (ouShiftFin t x y) ∂γFin n
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  exact congrArg f (setShift_univ t x y)

/-- The multivariate OU semigroup commutes with adding a constant on the
square: `P_t (f² + ε) = P_t (f²) + ε`, because `P_t` is an average
against a probability kernel (`γFin n` is a probability measure). -/
theorem ouSemigroupFin_sq_add_const {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (ε : ℝ) (t : ℝ) (_ht : 0 ≤ t) :
    ouSemigroupFin t (fun x => f x * f x + ε) =
      fun x => ouSemigroupFin t (fun x => f x * f x) x + ε := by
  obtain ⟨M, hM⟩ := hf.bound_exists
  have hM_nn : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0)
  have hf_meas : Measurable f := hf.measurable
  funext x
  have hsq_bd : ∀ z : Fin n → ℝ, ‖f z * f z‖ ≤ M ^ 2 := by
    intro z
    have hz : |f z| ≤ M := by rw [← Real.norm_eq_abs]; exact hM z
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_self_nonneg _)]
    nlinarith [abs_nonneg (f z), sq_abs (f z)]
  have h_int_sq : Integrable
      (fun y : Fin n → ℝ => f (ouShiftFin t x y) * f (ouShiftFin t x y)) (γFin n) := by
    have hcont_shift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
      continuity
    refine integrable_of_bound (M := M ^ 2)
      ((hf_meas.comp hcont_shift.measurable).mul
        (hf_meas.comp hcont_shift.measurable)) ?_
    intro y
    exact hsq_bd (ouShiftFin t x y)
  show ∫ y, (f (ouShiftFin t x y) * f (ouShiftFin t x y) + ε) ∂γFin n
      = (∫ y, f (ouShiftFin t x y) * f (ouShiftFin t x y) ∂γFin n) + ε
  rw [integral_add h_int_sq (integrable_const ε)]
  simp

/-- **ε → 0 reduction (n-dim DCT tail).** If for every `ε > 0` the
regularized Boltzmann difference of `g_ε = f² + ε` is bounded by the
target constant, then the un-regularized Boltzmann difference of `f²` is
bounded by the same constant.

The map `s ↦ s log s` is continuous, hence bounded on the compact value
range `[0, M²+1]` (with `M` the `IsCoreFin` bound on `f`), so dominated
convergence over `ε ∈ 𝓝[>] 0` carries the bound to the limit. This is
the exact `n`-dim analogue of the proved 1D ε-tail in
`Gaussian1D.ouSemigroup_entropy_sq_decay_bound_proved`. -/
theorem boltzmannSubFin_le_of_perEps {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (t : ℝ) (_ht : 0 ≤ t)
    {C : ℝ}
    (hEps : ∀ ε : ℝ, 0 < ε →
      boltzmannEntropyFin (fun x => f x * f x + ε) -
        boltzmannEntropyFin
          (fun x => ouSemigroupFin t (fun x => f x * f x) x + ε) ≤ C) :
    boltzmannEntropyFin (fun x => f x * f x) -
      boltzmannEntropyFin (ouSemigroupFin t (fun x => f x * f x)) ≤ C := by
  obtain ⟨M, hM⟩ := hf.bound_exists
  have hM_nn : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0)
  have hf_meas : Measurable f := hf.measurable
  set g : (Fin n → ℝ) → ℝ := fun x => f x * f x with hg_def
  have hg_meas : Measurable g := hf_meas.mul hf_meas
  have hg_nn : ∀ x, 0 ≤ g x := fun x => mul_self_nonneg _
  have hg_bdd : ∀ x, g x ≤ M ^ 2 := by
    intro x
    have hx : |f x| ≤ M := by rw [← Real.norm_eq_abs]; exact hM x
    have : g x = f x * f x := rfl
    nlinarith [abs_nonneg (f x), sq_abs (f x)]
  -- `P_t g` is in `[0, M²]` pointwise.
  have hPg_bdd : ∀ x, 0 ≤ ouSemigroupFin t g x ∧ ouSemigroupFin t g x ≤ M ^ 2 := by
    intro x
    have hint : Integrable (fun y => g (ouShiftFin t x y)) (γFin n) := by
      have hcont_shift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
        continuity
      refine integrable_of_bound (M := M ^ 2)
        (hg_meas.comp hcont_shift.measurable) ?_
      intro y
      rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn _)]; exact hg_bdd _
    refine ⟨?_, ?_⟩
    · show 0 ≤ ∫ y, g (ouShiftFin t x y) ∂γFin n
      exact integral_nonneg (fun y => hg_nn _)
    · show ∫ y, g (ouShiftFin t x y) ∂γFin n ≤ M ^ 2
      calc ∫ y, g (ouShiftFin t x y) ∂γFin n
          ≤ ∫ _y, M ^ 2 ∂γFin n :=
            integral_mono hint (integrable_const _) (fun y => hg_bdd _)
        _ = M ^ 2 := by simp
  have hPg_meas : Measurable (ouSemigroupFin t g) := by
    have hcont : Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        ouShiftFin t p.1 p.2) := by
      unfold ouShiftFin; fun_prop
    exact ((hg_meas.comp hcont.measurable).stronglyMeasurable.integral_prod_right').measurable
  -- Uniform `|s log s|` bound on `[0, M²+1]`.
  obtain ⟨B, hB_nn, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧
      ∀ s ∈ Set.Icc (0 : ℝ) (M ^ 2 + 1), |s * Real.log s| ≤ B := by
    have h_compact : IsCompact (Set.Icc (0 : ℝ) (M ^ 2 + 1)) := isCompact_Icc
    obtain ⟨B, hB⟩ := (h_compact.image Real.continuous_mul_log.abs).bddAbove
    exact ⟨max B 0, le_max_right _ _, fun s hs =>
      (hB ⟨s, hs, rfl⟩).trans (le_max_left _ _)⟩
  -- DCT: regularized Boltzmann entropies converge as `ε → 0⁺`.
  have h_lim_g : Tendsto
      (fun ε : ℝ => boltzmannEntropyFin (fun x => g x + ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (boltzmannEntropyFin g)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ => B) ?_ ?_ (integrable_const _) ?_
    · filter_upwards [self_mem_nhdsWithin] with ε _
      exact ((hg_meas.add_const ε).mul
        (Real.measurable_log.comp (hg_meas.add_const ε))).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with ε hε_range
      filter_upwards with x
      have h_range : g x + ε ∈ Set.Icc (0 : ℝ) (M ^ 2 + 1) :=
        ⟨by linarith [hg_nn x, hε_range.1], by linarith [hg_bdd x, hε_range.2.le]⟩
      rw [Real.norm_eq_abs]; exact hB _ h_range
    · filter_upwards with x
      have h_tendsto : Tendsto (fun ε : ℝ => g x + ε)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (g x)) := by
        have hh : Tendsto (fun ε : ℝ => g x + ε) (nhds 0) (nhds (g x + 0)) :=
          (tendsto_const_nhds (x := g x)).add tendsto_id
        simpa using hh.mono_left nhdsWithin_le_nhds
      exact (Real.continuous_mul_log.tendsto (g x)).comp h_tendsto
  have h_lim_Pg : Tendsto
      (fun ε : ℝ => boltzmannEntropyFin (fun x => ouSemigroupFin t g x + ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (boltzmannEntropyFin (ouSemigroupFin t g))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ => B) ?_ ?_ (integrable_const _) ?_
    · filter_upwards [self_mem_nhdsWithin] with ε _
      have : Measurable (fun x => (ouSemigroupFin t g x + ε) *
          Real.log (ouSemigroupFin t g x + ε)) :=
        (hPg_meas.add_const ε).mul (Real.measurable_log.comp (hPg_meas.add_const ε))
      exact this.aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with ε hε_range
      filter_upwards with x
      have hb := hPg_bdd x
      have h_range : ouSemigroupFin t g x + ε ∈
          Set.Icc (0 : ℝ) (M ^ 2 + 1) :=
        ⟨by linarith [hb.1, hε_range.1],
         by linarith [hb.2, hε_range.2.le]⟩
      rw [Real.norm_eq_abs]; exact hB _ h_range
    · filter_upwards with x
      have h_tendsto : Tendsto (fun ε : ℝ => ouSemigroupFin t g x + ε)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (ouSemigroupFin t g x)) := by
        have hh : Tendsto (fun ε : ℝ => ouSemigroupFin t g x + ε) (nhds 0)
            (nhds (ouSemigroupFin t g x + 0)) :=
          (tendsto_const_nhds (x := ouSemigroupFin t g x)).add tendsto_id
        simpa using hh.mono_left nhdsWithin_le_nhds
      exact (Real.continuous_mul_log.tendsto (ouSemigroupFin t g x)).comp h_tendsto
  have h_lim : Tendsto
      (fun ε : ℝ => boltzmannEntropyFin (fun x => g x + ε) -
        boltzmannEntropyFin (fun x => ouSemigroupFin t g x + ε))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (boltzmannEntropyFin g - boltzmannEntropyFin (ouSemigroupFin t g))) :=
    h_lim_g.sub h_lim_Pg
  have h_ev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      boltzmannEntropyFin (fun x => g x + ε) -
        boltzmannEntropyFin (fun x => ouSemigroupFin t g x + ε) ≤ C := by
    filter_upwards [self_mem_nhdsWithin] with ε hε_pos
    exact hEps ε hε_pos
  exact le_of_tendsto h_lim h_ev

/-! ### N1.c telescoping infrastructure (reusable, axiom-free)

The lemmas below build the per-coordinate telescoping scaffolding for the
multivariate entropy-decay bound: single-coordinate OU mean preservation
(`integral_ouCoord_eq`), the `ouCoordSet` composition step (T1,
`ouCoord_ouCoordSet`), `ouCoordSet` bounds and measure preservation. They
are independent of the still-open regularity question (see the strategy
comment on `ouSemigroupFin_entropy_sq_decay_bound`). -/

end GaussianFin

namespace Gaussian1D

/-- 1D OU mean preservation: `∫ P_t g dγ = ∫ g dγ` for bounded measurable
`g`. The OU kernel `(u, v) ↦ e^{-t} u + √(1-e^{-2t}) v` pushes `γ ⊗ γ`
forward to `γ` (`ou_kernel_map`), so the Gaussian mean is invariant. -/
theorem integral_ouSemigroup_eq (t : ℝ) (ht : 0 ≤ t)
    {g : ℝ → ℝ} (hg_meas : Measurable g) {C : ℝ} (hg_bd : ∀ x, ‖g x‖ ≤ C) :
    ∫ x, ouSemigroup t g x ∂γ = ∫ x, g x ∂γ := by
  set a := Real.exp (-t)
  set b := Real.sqrt (1 - Real.exp (-2 * t))
  set φ : ℝ × ℝ → ℝ := fun p => a * p.1 + b * p.2
  have hφ : Measurable φ := Measurable.add
    (measurable_const.mul measurable_fst) (measurable_const.mul measurable_snd)
  have hmap := ou_kernel_map t ht
  have hg_int : Integrable g γ :=
    Integrable.mono' (integrable_const C) hg_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall hg_bd)
  have hgφ_int : Integrable (g ∘ φ) (γ.prod γ) := by
    have hasm' : AEStronglyMeasurable g ((γ.prod γ).map φ) := by
      rw [hmap]; exact hg_meas.aestronglyMeasurable
    have hint' : Integrable g ((γ.prod γ).map φ) := by rw [hmap]; exact hg_int
    exact (integrable_map_measure hasm' hφ.aemeasurable).mp hint'
  simp only [ouSemigroup]
  rw [show (∫ x, (∫ y, g (a * x + b * y) ∂γ) ∂γ) = ∫ p, g (φ p) ∂(γ.prod γ) from
    (integral_prod (g ∘ φ) hgφ_int).symm]
  have hlaw : HasLaw φ γ (γ.prod γ) := ⟨hφ.aemeasurable, hmap⟩
  exact hlaw.integral_comp hg_meas.aestronglyMeasurable

end Gaussian1D

namespace GaussianFin

variable {n : ℕ}

/-- `ouCoord` measure-preservation: `∫ ouCoord i t h dγ_{n+1} = ∫ h dγ_{n+1}`
for bounded measurable `h`. The single-coordinate OU is the 1D OU on the
`i`-th slice, which preserves the Gaussian mean. -/
theorem integral_ouCoord_eq {n : ℕ} (i : Fin (n + 1)) (t : ℝ) (ht : 0 ≤ t)
    {h : (Fin (n + 1) → ℝ) → ℝ} (hh_meas : Measurable h) {C : ℝ}
    (hh_bd : ∀ z, ‖h z‖ ≤ C) :
    ∫ x, ouCoord i t h x ∂γFin (n + 1) = ∫ x, h x ∂γFin (n + 1) := by
  -- `ouCoord i t h` is bounded by `C` (it is a Gaussian average of `h`).
  have hC_nn : (0 : ℝ) ≤ C := (norm_nonneg _).trans (hh_bd 0)
  have hou_bd : ∀ x, ‖ouCoord i t h x‖ ≤ C := by
    intro x
    have hint : Integrable (fun s => h (Function.update x i
        (Real.exp (-t) * x i + Real.sqrt (1 - Real.exp (-2 * t)) * s)))
        Gaussian1D.γ := by
      have hmeas : Measurable (fun s => h (Function.update x i
          (Real.exp (-t) * x i + Real.sqrt (1 - Real.exp (-2 * t)) * s))) := by
        have hval : Measurable (fun s : ℝ =>
            Real.exp (-t) * x i + Real.sqrt (1 - Real.exp (-2 * t)) * s) :=
          measurable_const.add (measurable_const.mul measurable_id)
        exact hh_meas.comp
          (measurable_update'.comp (measurable_const.prodMk hval))
      exact Integrable.mono' (integrable_const C) hmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun s => hh_bd _))
    show ‖∫ s, h (Function.update x i _) ∂Gaussian1D.γ‖ ≤ C
    calc ‖∫ s, h (Function.update x i (Real.exp (-t) * x i +
            Real.sqrt (1 - Real.exp (-2 * t)) * s)) ∂Gaussian1D.γ‖
        ≤ ∫ s, C ∂Gaussian1D.γ :=
          norm_integral_le_of_norm_le (integrable_const C)
            (Filter.Eventually.of_forall (fun s => hh_bd _))
      _ = C := by simp
  have hou_meas : Measurable (ouCoord i t h) := by
    have hupd : Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ =>
        Function.update p.1 i (Real.exp (-t) * p.1 i +
          Real.sqrt (1 - Real.exp (-2 * t)) * p.2)) := by
      have hval : Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ =>
          Real.exp (-t) * p.1 i + Real.sqrt (1 - Real.exp (-2 * t)) * p.2) :=
        (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).add
          (measurable_const.mul measurable_snd)
      exact measurable_update'.comp (measurable_fst.prodMk hval)
    have hjoint : Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ =>
        h (Function.update p.1 i (Real.exp (-t) * p.1 i +
          Real.sqrt (1 - Real.exp (-2 * t)) * p.2))) := hh_meas.comp hupd
    exact (hjoint.stronglyMeasurable.integral_prod_right').measurable
  -- Split both sides via `integral_γFin_succAbove_swap` on coordinate `i`.
  rw [integral_γFin_succAbove_swap (n := n) (i := i) hou_meas hou_bd,
      integral_γFin_succAbove_swap (n := n) (i := i) hh_meas hh_bd]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  -- Inner: `∫_s ouCoord i t h (insertNth i s y) dγ = ∫_s h (insertNth i s y) dγ`.
  have hslice_meas : Measurable
      (fun r => h (Fin.insertNth (α := fun _ => ℝ) i r y)) := by
    have hcont : Continuous (fun r : ℝ =>
        Fin.insertNth (α := fun _ => ℝ) i r y) :=
      Continuous.finInsertNth i continuous_id continuous_const
    exact hh_meas.comp hcont.measurable
  calc ∫ s, ouCoord i t h (Fin.insertNth (α := fun _ => ℝ) i s y) ∂Gaussian1D.γ
      = ∫ s, Gaussian1D.ouSemigroup t
          (fun r => h (Fin.insertNth (α := fun _ => ℝ) i r y)) s ∂Gaussian1D.γ := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
        exact ouCoord_insertNth_eq i t h s y
    _ = ∫ s, h (Fin.insertNth (α := fun _ => ℝ) i s y) ∂Gaussian1D.γ :=
        Gaussian1D.integral_ouSemigroup_eq t ht hslice_meas (fun r => hh_bd _)

/-- Pointwise `setShift` peel: for `j ∉ S`, shifting on `S` at the
`j`-updated point `update x j (e^{-t} x_j + b s)` with displacement `y`
equals shifting on `insert j S` at `x` with displacement `update y j s`. -/
theorem setShift_insert_update {n : ℕ} (S : Finset (Fin n)) (j : Fin n)
    (hj : j ∉ S) (t : ℝ) (x y : Fin n → ℝ) (s : ℝ) :
    setShift S t (Function.update x j
        (Real.exp (-t) * x j + Real.sqrt (1 - Real.exp (-2 * t)) * s)) y =
      setShift (insert j S) t x (Function.update y j s) := by
  funext i
  by_cases hij : i = j
  · subst hij
    simp [setShift, hj, Finset.mem_insert]
  · have hi_ne : i ≠ j := hij
    by_cases hiS : i ∈ S
    · simp [setShift, hiS, Finset.mem_insert, hi_ne]
    · simp [setShift, hiS, Finset.mem_insert, hi_ne]

/-- Measure-preservation of `(s, y) ↦ update y j s` on `γ × γ_n → γ_n`:
the Gaussian product measure is invariant under reinjecting an
independent Gaussian coordinate. -/
theorem integral_update_swap {m : ℕ} (j : Fin (m + 1))
    {G : (Fin (m + 1) → ℝ) → ℝ} (hG_meas : Measurable G) {C : ℝ}
    (hG_bd : ∀ z, ‖G z‖ ≤ C) :
    ∫ s, ∫ y, G (Function.update y j s) ∂γFin (m + 1) ∂Gaussian1D.γ =
      ∫ y, G y ∂γFin (m + 1) := by
  have hG_int : Integrable G (γFin (m + 1)) := integrable_of_bound hG_meas hG_bd
  -- Split the RHS via `integral_γFin_succAbove j`.
  rw [integral_γFin_succAbove (n := m) (i := j) hG_int]
  -- For each `s`, rewrite the inner `∫_y G (update y j s)`.
  refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
  show ∫ y, G (Function.update y j s) ∂γFin (m + 1)
      = ∫ y, G (Fin.insertNth (α := fun _ => ℝ) j s y) ∂γFin m
  -- `∫_y G (update y j s)` splits via `integral_γFin_succAbove j` too.
  have hGupd_meas : Measurable (fun y => G (Function.update y j s)) :=
    hG_meas.comp (measurable_update_left)
  have hGupd_int : Integrable (fun y => G (Function.update y j s))
      (γFin (m + 1)) :=
    integrable_of_bound hGupd_meas (fun y => hG_bd _)
  rw [integral_γFin_succAbove (n := m) (i := j) hGupd_int]
  -- `update (insertNth j r z) j s = insertNth j s z`.
  have hrw : ∀ r (z : Fin m → ℝ),
      G (Function.update (Fin.insertNth (α := fun _ => ℝ) j r z) j s) =
        G (Fin.insertNth (α := fun _ => ℝ) j s z) := by
    intro r z
    rw [update_insertNth_same j z r s]
  calc ∫ r, ∫ z, G (Function.update
          (Fin.insertNth (α := fun _ => ℝ) j r z) j s) ∂γFin m ∂Gaussian1D.γ
      = ∫ r, ∫ z, G (Fin.insertNth (α := fun _ => ℝ) j s z)
          ∂γFin m ∂Gaussian1D.γ := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun r => ?_))
        refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
        exact hrw r z
    _ = ∫ z, G (Fin.insertNth (α := fun _ => ℝ) j s z) ∂γFin m := by
        simp

/-- **Composition step (T1).** For `j ∉ S` and bounded measurable `g`,
applying `ouCoord j t` after `ouCoordSet S t` equals `ouCoordSet
(insert j S) t`. The peel uses `setShift_insert_update` pointwise and the
measure preservation `integral_update_swap`. -/
theorem ouCoord_ouCoordSet {m : ℕ} (S : Finset (Fin (m + 1)))
    (j : Fin (m + 1)) (hj : j ∉ S) (t : ℝ)
    {g : (Fin (m + 1) → ℝ) → ℝ} (hg_meas : Measurable g) {C : ℝ}
    (hg_bd : ∀ z, ‖g z‖ ≤ C) :
    ouCoord j t (ouCoordSet S t g) = ouCoordSet (insert j S) t g := by
  funext x
  -- LHS: `∫_s (ouCoordSet S t g)(update x j v_s) dγ(s)` where
  -- `v_s = e^{-t} x_j + b s`, then unfold `ouCoordSet`.
  show ∫ s, ouCoordSet S t g (Function.update x j
      (Real.exp (-t) * x j + Real.sqrt (1 - Real.exp (-2 * t)) * s))
      ∂Gaussian1D.γ
    = ∫ y, g (setShift (insert j S) t x y) ∂γFin (m + 1)
  -- Set `G y := g (setShift (insert j S) t x y)`.
  set G : (Fin (m + 1) → ℝ) → ℝ :=
    fun y => g (setShift (insert j S) t x y) with hG_def
  have hsetShift_meas : ∀ (z : Fin (m + 1) → ℝ),
      Measurable (fun y => setShift (insert j S) t z y) := by
    intro z
    refine Measurable.of_eval (fun i => ?_)
    by_cases hi : i ∈ insert j S
    · simp only [setShift, hi, ite_true]
      exact measurable_const.add
        (measurable_const.mul ((measurable_pi_apply i)))
    · simp only [setShift, hi, ite_false]
      exact measurable_const
  have hG_meas : Measurable G :=
    hg_meas.comp (hsetShift_meas x)
  have hG_bd : ∀ z, ‖G z‖ ≤ C := fun z => hg_bd _
  -- Rewrite the LHS inner `ouCoordSet S t g (update x j v_s)`.
  have hLHS_inner : ∀ s,
      ouCoordSet S t g (Function.update x j
          (Real.exp (-t) * x j + Real.sqrt (1 - Real.exp (-2 * t)) * s))
        = ∫ y, G (Function.update y j s) ∂γFin (m + 1) := by
    intro s
    show ∫ y, g (setShift S t (Function.update x j
        (Real.exp (-t) * x j + Real.sqrt (1 - Real.exp (-2 * t)) * s)) y)
        ∂γFin (m + 1)
      = ∫ y, g (setShift (insert j S) t x (Function.update y j s))
        ∂γFin (m + 1)
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    show g (setShift S t (Function.update x j
        (Real.exp (-t) * x j + Real.sqrt (1 - Real.exp (-2 * t)) * s)) y)
      = g (setShift (insert j S) t x (Function.update y j s))
    rw [setShift_insert_update S j hj t x y s]
  calc ∫ s, ouCoordSet S t g (Function.update x j
        (Real.exp (-t) * x j + Real.sqrt (1 - Real.exp (-2 * t)) * s))
        ∂Gaussian1D.γ
      = ∫ s, ∫ y, G (Function.update y j s) ∂γFin (m + 1) ∂Gaussian1D.γ := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
        exact hLHS_inner s
    _ = ∫ y, G y ∂γFin (m + 1) :=
        integral_update_swap j hG_meas hG_bd

/-- `setShift` is measurable in its displacement argument. -/
theorem measurable_setShift {n : ℕ} (S : Finset (Fin n)) (t : ℝ)
    (x : Fin n → ℝ) : Measurable (fun y => setShift S t x y) := by
  refine Measurable.of_eval (fun i => ?_)
  by_cases hi : i ∈ S
  · simp only [setShift, hi, ite_true]
    exact measurable_const.add (measurable_const.mul (measurable_pi_apply i))
  · simp only [setShift, hi, ite_false]
    exact measurable_const

/-- `ouCoordSet` preserves a uniform two-sided bound `ε ≤ g ≤ M`
(it averages `g` against the probability measure `γ_n`). -/
theorem ouCoordSet_bounds {n : ℕ} (S : Finset (Fin n)) (t : ℝ)
    {g : (Fin n → ℝ) → ℝ} (hg_meas : Measurable g) {ε M : ℝ}
    (hg_lo : ∀ x, ε ≤ g x) (hg_hi : ∀ x, g x ≤ M) :
    ∀ x, ε ≤ ouCoordSet S t g x ∧ ouCoordSet S t g x ≤ M := by
  intro x
  have hgshift_meas : Measurable (fun y => g (setShift S t x y)) :=
    hg_meas.comp (measurable_setShift S t x)
  have hint : Integrable (fun y => g (setShift S t x y)) (γFin n) := by
    refine Integrable.mono' (integrable_const (max |ε| |M|))
      hgshift_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => ?_))
    rw [Real.norm_eq_abs, abs_le]
    have h1 := hg_lo (setShift S t x y)
    have h2 := hg_hi (setShift S t x y)
    constructor
    · calc -max |ε| |M| ≤ -|ε| := by
            simp [neg_le_neg_iff]
        _ ≤ ε := neg_abs_le ε
        _ ≤ _ := h1
    · calc g (setShift S t x y) ≤ M := h2
        _ ≤ |M| := le_abs_self M
        _ ≤ _ := le_max_right _ _
  constructor
  · show ε ≤ ∫ y, g (setShift S t x y) ∂γFin n
    calc ε = ∫ _y, ε ∂γFin n := by simp
      _ ≤ _ := integral_mono (integrable_const ε) hint (fun y => hg_lo _)
  · show ∫ y, g (setShift S t x y) ∂γFin n ≤ M
    calc ∫ y, g (setShift S t x y) ∂γFin n
        ≤ ∫ _y, M ∂γFin n :=
          integral_mono hint (integrable_const M) (fun y => hg_hi _)
      _ = M := by simp

/-- `ouCoordSet S t g` is measurable for measurable `g`. -/
theorem measurable_ouCoordSet {n : ℕ} (S : Finset (Fin n)) (t : ℝ)
    {g : (Fin n → ℝ) → ℝ} (hg_meas : Measurable g) :
    Measurable (ouCoordSet S t g) := by
  have hshift_meas : Measurable
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => setShift S t p.1 p.2) := by
    have key : ∀ i : Fin n, Measurable
        (fun p : (Fin n → ℝ) × (Fin n → ℝ) => setShift S t p.1 p.2 i) := by
      intro i
      by_cases hi : i ∈ S
      · simp only [setShift, hi, ite_true]
        exact (measurable_const.mul
            ((measurable_pi_apply (X := fun _ : Fin n => ℝ) i).comp
              measurable_fst)).add
          (measurable_const.mul
            ((measurable_pi_apply (X := fun _ : Fin n => ℝ) i).comp
              measurable_snd))
      · simp only [setShift, hi, ite_false]
        exact (measurable_pi_apply (X := fun _ : Fin n => ℝ) i).comp
          measurable_fst
    exact (@measurable_pi_iff ((Fin n → ℝ) × (Fin n → ℝ)) (Fin n)
      (fun _ => ℝ) _ _ _).mpr key
  have hjoint : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      g (setShift S t p.1 p.2)) := hg_meas.comp hshift_meas
  exact (hjoint.stronglyMeasurable.integral_prod_right').measurable

/-- **`ouCoordSet` measure-preservation.** `∫ ouCoordSet S t g dγ_n =
∫ g dγ_n` for bounded measurable `g` and `t ≥ 0`: every single-coordinate
OU preserves the Gaussian mean, so the composition does too. Proved by
`Finset.induction` peeling one `ouCoord` factor at a time. -/
theorem integral_ouCoordSet_eq {n : ℕ} (S : Finset (Fin n)) (t : ℝ)
    (ht : 0 ≤ t) {g : (Fin n → ℝ) → ℝ} (hg_meas : Measurable g) {C : ℝ}
    (hg_bd : ∀ z, ‖g z‖ ≤ C) :
    ∫ x, ouCoordSet S t g x ∂γFin n = ∫ x, g x ∂γFin n := by
  classical
  cases n with
  | zero =>
      -- `Fin 0 → ℝ` is a subsingleton; the only Finset is `∅`.
      have hS : S = (∅ : Finset (Fin 0)) := Finset.eq_empty_of_isEmpty S
      subst hS
      rw [ouCoordSet_empty]
  | succ m =>
      induction S using Finset.induction with
      | empty => rw [ouCoordSet_empty]
      | insert j S hj ih =>
          have hou_meas : Measurable (ouCoordSet S t g) :=
            measurable_ouCoordSet S t hg_meas
          have hou_bd : ∀ z, ‖ouCoordSet S t g z‖ ≤ C := by
            intro z
            have hb := ouCoordSet_bounds S t hg_meas (ε := -C) (M := C)
              (fun x => by
                have := hg_bd x
                rw [Real.norm_eq_abs, abs_le] at this; exact this.1)
              (fun x => by
                have := hg_bd x
                rw [Real.norm_eq_abs, abs_le] at this; exact this.2) z
            rw [Real.norm_eq_abs, abs_le]; exact ⟨hb.1, hb.2⟩
          rw [← ouCoord_ouCoordSet S j hj t hg_meas hg_bd]
          rw [integral_ouCoord_eq j t ht hou_meas hou_bd]
          exact ih

/-! ### S2/S4: 1-parameter slice analysis of `ouCoordSet` along a frozen coord

For `k ∉ S`, `setShift S t (·) (·)` leaves coordinate `k` of its first
argument untouched, so the only dependence of `g (setShift S t x y)` on
`x k` is through coordinate `k` of `g` itself. This decouples the slice
analysis of `ouCoordSet S t g` along coordinate `k` into a *single
real-parameter* differentiation under the γ-integral — no joint
multivariate `C²`, no mixed partials. (Gemini deep-think + 3.1-pro
vetted, 2026-05-19.) -/

/-- **Frozen-slot identity.** For `k ∉ S`, shifting on `S` of the
`k`-updated point equals updating coordinate `k` of the shifted point. -/
theorem setShift_update_notMem {n : ℕ} (S : Finset (Fin n)) (k : Fin n)
    (hk : k ∉ S) (t : ℝ) (x y : Fin n → ℝ) (r : ℝ) :
    setShift S t (Function.update x k r) y =
      Function.update (setShift S t x y) k r := by
  funext i
  by_cases hik : i = k
  · subst hik
    simp [setShift, hk]
  · have hi_ne : i ≠ k := hik
    by_cases hiS : i ∈ S
    · simp [setShift, hiS, Function.update_of_ne hi_ne]
    · simp [setShift, hiS, Function.update_of_ne hi_ne]

/-- **S2-core: 1-parameter commutation `HasDerivAt`.** For `k ∉ S` and
`g` differentiable with coordinate-`k` partial bounded by `M`, the slice
`r ↦ ouCoordSet S t g (update x k r)` is differentiable at `x k` with
derivative `ouCoordSet S t (∂_k g) x`. The proof differentiates a single
real parameter under the probability-measure γ-integral with the
*constant* dominator `M` (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`). -/
theorem hasDerivAt_slice_ouCoordSet {n : ℕ} (S : Finset (Fin n)) (k : Fin n)
    (hk : k ∉ S) (t : ℝ) {g : (Fin n → ℝ) → ℝ}
    (hg_diff : Differentiable ℝ g) (hg_meas : Measurable g)
    (h_pd_meas : Measurable (partialDeriv k g)) {M : ℝ}
    (hg_bd : ∀ z, ‖g z‖ ≤ M) (h_pd_bd : ∀ z, |partialDeriv k g z| ≤ M)
    (x : Fin n → ℝ) :
    HasDerivAt (fun r => ouCoordSet S t g (Function.update x k r))
      (ouCoordSet S t (partialDeriv k g) x) (x k) := by
  classical
  -- Rewrite the slice through the frozen-slot identity.
  have hslice_eq : (fun r => ouCoordSet S t g (Function.update x k r)) =
      fun r => ∫ y, g (Function.update (setShift S t x y) k r) ∂γFin n := by
    funext r
    show (∫ y, g (setShift S t (Function.update x k r) y) ∂γFin n) =
      ∫ y, g (Function.update (setShift S t x y) k r) ∂γFin n
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    exact congrArg g (setShift_update_notMem S k hk t x y r)
  rw [hslice_eq]
  -- Differentiate under the integral (single real parameter `r`).
  set F : ℝ → (Fin n → ℝ) → ℝ :=
    fun r y => g (Function.update (setShift S t x y) k r) with hF
  set F' : ℝ → (Fin n → ℝ) → ℝ :=
    fun r y => partialDeriv k g (Function.update (setShift S t x y) k r) with hF'
  have hsetShift_meas : Measurable (fun y => setShift S t x y) :=
    measurable_setShift S t x
  -- Pointwise derivative in `r`: the coordinate-`k` section of `g`.
  have h_diff_ptwise : ∀ y : Fin n → ℝ, ∀ r : ℝ,
      HasDerivAt (fun r => F r y) (F' r y) r := by
    intro y r
    have := section_hasDerivAt_of_differentiable hg_diff k (setShift S t x y) r
    convert this using 1; rfl
  have hF_int : Integrable (F (x k)) (γFin n) := by
    have hmeas : Measurable (F (x k)) := by
      have : Measurable (fun y => Function.update (setShift S t x y) k (x k)) :=
        measurable_update'.comp (hsetShift_meas.prodMk measurable_const)
      exact hg_meas.comp this
    exact integrable_of_bound hmeas (fun y => hg_bd _)
  have hF'_meas : AEStronglyMeasurable (F' (x k)) (γFin n) := by
    have : Measurable (fun y => Function.update (setShift S t x y) k (x k)) :=
      measurable_update'.comp (hsetShift_meas.prodMk measurable_const)
    exact (h_pd_meas.comp this).aestronglyMeasurable
  have h_bound : ∀ᵐ y ∂γFin n, ∀ r ∈ Set.univ, ‖F' r y‖ ≤ M :=
    Filter.Eventually.of_forall (fun y r _ => by
      rw [hF', Real.norm_eq_abs]; exact h_pd_bd _)
  have hF_meas_ev : ∀ᶠ r in nhds (x k),
      AEStronglyMeasurable (F r) (γFin n) := by
    filter_upwards with r
    have : Measurable (fun y => Function.update (setShift S t x y) k r) :=
      measurable_update'.comp (hsetShift_meas.prodMk measurable_const)
    exact (hg_meas.comp this).aestronglyMeasurable
  have hkey :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := γFin n) (F := F) (F' := F') (x₀ := x k)
      (bound := fun _ => M) (s := Set.univ)
      Filter.univ_mem hF_meas_ev hF_int hF'_meas h_bound
      (integrable_const M)
      (Filter.Eventually.of_forall (fun y r _ => h_diff_ptwise y r))
  -- The derivative value: `update (setShift ..) k (x k) = setShift ..`
  -- since `k ∉ S` already freezes coordinate `k` to `x k`.
  have hval : (∫ y, F' (x k) y ∂γFin n) = ouCoordSet S t (partialDeriv k g) x := by
    show (∫ y, partialDeriv k g
        (Function.update (setShift S t x y) k (x k)) ∂γFin n) =
      ∫ y, partialDeriv k g (setShift S t x y) ∂γFin n
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    have hupd : Function.update (setShift S t x y) k (x k) = setShift S t x y := by
      funext i
      by_cases hik : i = k
      · subst hik; simp [setShift, hk]
      · simp [Function.update_of_ne hik]
    exact congrArg (partialDeriv k g) hupd
  rw [← hval]
  exact hkey.2

/-- `ouCoordSet S t g` is (jointly) continuous for continuous bounded `g`:
it is a γ-average of `g ∘ (continuous affine shift)`, dominated by the
constant bound. -/
theorem continuous_ouCoordSet {n : ℕ} (S : Finset (Fin n)) (t : ℝ)
    {g : (Fin n → ℝ) → ℝ} (hg_cont : Continuous g) {M : ℝ}
    (hg_bd : ∀ z, ‖g z‖ ≤ M) :
    Continuous (ouCoordSet S t g) := by
  have hshift_cont : Continuous
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => setShift S t p.1 p.2) := by
    refine continuous_pi (fun i => ?_)
    by_cases hi : i ∈ S
    · simp only [setShift, hi, ite_true]
      exact (continuous_const.mul ((continuous_apply i).comp continuous_fst)).add
        (continuous_const.mul ((continuous_apply i).comp continuous_snd))
    · simp only [setShift, hi, ite_false]
      exact (continuous_apply i).comp continuous_fst
  refine continuous_of_dominated (μ := γFin n) (bound := fun _ => M)
    (fun x => ?_) (fun x => ?_) (integrable_const M)
    (Filter.Eventually.of_forall (fun y => ?_))
  · exact (hg_cont.comp (hshift_cont.comp
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun y => hg_bd _)
  · exact hg_cont.comp (hshift_cont.comp (continuous_id.prodMk continuous_const))

/-- **Slice `C¹` + slice derivative for `ouCoordSet`.** For `k ∉ S` and
`g` `C¹` with continuous bounded `∂_k g`, the coordinate-`k` 1D slice of
`ouCoordSet S t g` is `C¹` with derivative the slice of
`ouCoordSet S t (∂_k g)`. This packages the 1-parameter commutation
(`hasDerivAt_slice_ouCoordSet`) with continuity of the derivative
(`continuous_ouCoordSet` of `∂_k g`) — exactly the slice-level inputs of
`boltzmannEntropyFin_ouCoord_step_le`. -/
theorem ouCoordSet_slice_contDiff_one {n : ℕ} (S : Finset (Fin (n + 1)))
    (k : Fin (n + 1)) (hk : k ∉ S) (t : ℝ) {g : (Fin (n + 1) → ℝ) → ℝ}
    (hg_C1 : ContDiff ℝ 1 g) (h_pd_cont : Continuous (partialDeriv k g))
    {M : ℝ} (hg_bd : ∀ z, ‖g z‖ ≤ M) (h_pd_bd : ∀ z, |partialDeriv k g z| ≤ M)
    (y : Fin n → ℝ) :
    ContDiff ℝ 1
      (fun r => ouCoordSet S t g (Fin.insertNth (α := fun _ => ℝ) k r y)) ∧
    deriv (fun r => ouCoordSet S t g (Fin.insertNth (α := fun _ => ℝ) k r y)) =
      fun r => ouCoordSet S t (partialDeriv k g)
        (Fin.insertNth (α := fun _ => ℝ) k r y) := by
  classical
  have hg_diff : Differentiable ℝ g := hg_C1.differentiable (by norm_num)
  have hg_meas : Measurable g := hg_C1.continuous.measurable
  have h_pd_meas : Measurable (partialDeriv k g) := h_pd_cont.measurable
  set base : Fin (n + 1) → ℝ := Fin.insertNth (α := fun _ => ℝ) k 0 y with hbase
  -- The slice rewritten through `update`-based form.
  have hslice_eq : (fun r => ouCoordSet S t g
        (Fin.insertNth (α := fun _ => ℝ) k r y)) =
      fun r => ouCoordSet S t g (Function.update base k r) := by
    funext r
    rw [hbase, update_insertNth_same k y 0 r]
  -- HasDerivAt at every `r`, via `hasDerivAt_slice_ouCoordSet` based at
  -- `update base k r` (so the basepoint's `k`-coordinate is `r`).
  have h_hasDeriv : ∀ r : ℝ,
      HasDerivAt (fun s => ouCoordSet S t g (Function.update base k s))
        (ouCoordSet S t (partialDeriv k g) (Function.update base k r)) r := by
    intro r
    have hx := hasDerivAt_slice_ouCoordSet S k hk t hg_diff hg_meas
      h_pd_meas hg_bd h_pd_bd (Function.update base k r)
    -- `(update base k r) k = r` and `update (update base k r) k = update base k`.
    have hxk : (Function.update base k r) k = r := by simp
    have hupd : (fun s => ouCoordSet S t g
        (Function.update (Function.update base k r) k s)) =
        fun s => ouCoordSet S t g (Function.update base k s) := by
      funext s; rw [Function.update_idem]
    rw [hxk, hupd] at hx
    exact hx
  -- Continuity of the derivative `r ↦ ouCoordSet S t (∂_k g) (update base k r)`.
  have h_pd_ouCoordSet_cont : Continuous (ouCoordSet S t (partialDeriv k g)) :=
    continuous_ouCoordSet S t h_pd_cont
      (fun z => by rw [Real.norm_eq_abs]; exact h_pd_bd z)
  have h_deriv_cont : Continuous
      (fun r => ouCoordSet S t (partialDeriv k g)
        (Function.update base k r)) :=
    h_pd_ouCoordSet_cont.comp (continuous_const.update k continuous_id)
  refine ⟨?_, ?_⟩
  · rw [hslice_eq]
    rw [contDiff_one_iff_deriv]
    refine ⟨fun r => (h_hasDeriv r).differentiableAt, ?_⟩
    have hderiv_eq : deriv (fun s => ouCoordSet S t g
        (Function.update base k s)) =
        fun r => ouCoordSet S t (partialDeriv k g)
          (Function.update base k r) := by
      funext r; exact (h_hasDeriv r).deriv
    rw [hderiv_eq]; exact h_deriv_cont
  · rw [hslice_eq]
    funext r
    rw [(h_hasDeriv r).deriv, hbase, update_insertNth_same k y 0 r]

/-- **Cauchy–Schwarz for an arbitrary measure** (the measure-general
analogue of the 1D `Gaussian1D.cauchy_schwarz_gamma`). For `A, B` with
`A·B`, `A²`, `B²` all `μ`-integrable,
`(∫ A·B dμ)² ≤ (∫ A² dμ)·(∫ B² dμ)`. Proved via the polynomial
discriminant. -/
theorem cauchy_schwarz_measure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A B : α → ℝ)
    (hAB : Integrable (fun y => A y * B y) μ)
    (hA2 : Integrable (fun y => A y ^ 2) μ)
    (hB2 : Integrable (fun y => B y ^ 2) μ) :
    (∫ y, A y * B y ∂μ) ^ 2 ≤ (∫ y, A y ^ 2 ∂μ) * (∫ y, B y ^ 2 ∂μ) := by
  set IA := ∫ y, A y ^ 2 ∂μ with hIA
  set IB := ∫ y, B y ^ 2 ∂μ with hIB
  set IAB := ∫ y, A y * B y ∂μ with hIAB
  have hIA_nn : 0 ≤ IA := integral_nonneg (fun y => sq_nonneg _)
  have hIB_nn : 0 ≤ IB := integral_nonneg (fun y => sq_nonneg _)
  by_cases hIB0 : IB = 0
  · have hB_ae : (fun y => B y ^ 2) =ᵐ[μ] 0 := by
      have h_nn_ae : ∀ᵐ y ∂μ, 0 ≤ B y ^ 2 :=
        Filter.Eventually.of_forall (fun y => sq_nonneg _)
      exact (integral_eq_zero_iff_of_nonneg_ae h_nn_ae hB2).mp hIB0
    have hAB_ae : (fun y => A y * B y) =ᵐ[μ] 0 := by
      filter_upwards [hB_ae] with y hy
      have : B y = 0 := sq_eq_zero_iff.mp hy
      simp [this]
    have hIAB0 : IAB = 0 := by
      rw [hIAB]; exact integral_eq_zero_of_ae hAB_ae
    rw [hIAB0, hIB0]; simp
  · have hIB_pos : 0 < IB := lt_of_le_of_ne hIB_nn (Ne.symm hIB0)
    set lam : ℝ := IAB / IB with h_lam_def
    have h_expand : ∫ y, (A y - lam * B y) ^ 2 ∂μ
        = IA - 2 * lam * IAB + lam ^ 2 * IB := by
      have h_eq : ∀ y, (A y - lam * B y) ^ 2
          = A y ^ 2 - 2 * lam * (A y * B y) + lam ^ 2 * B y ^ 2 := fun y => by ring
      calc ∫ y, (A y - lam * B y) ^ 2 ∂μ
          = ∫ y, A y ^ 2 - 2 * lam * (A y * B y) + lam ^ 2 * B y ^ 2 ∂μ :=
            integral_congr_ae (Filter.Eventually.of_forall h_eq)
        _ = (∫ y, A y ^ 2 - 2 * lam * (A y * B y) ∂μ) + ∫ y, lam ^ 2 * B y ^ 2 ∂μ :=
            integral_add (hA2.sub (hAB.const_mul (2 * lam))) (hB2.const_mul (lam ^ 2))
        _ = ((∫ y, A y ^ 2 ∂μ) - ∫ y, 2 * lam * (A y * B y) ∂μ)
            + ∫ y, lam ^ 2 * B y ^ 2 ∂μ := by
            rw [integral_sub hA2 (hAB.const_mul (2 * lam))]
        _ = IA - 2 * lam * IAB + lam ^ 2 * IB := by
            rw [integral_const_mul, integral_const_mul]
    have h_nn : 0 ≤ ∫ y, (A y - lam * B y) ^ 2 ∂μ :=
      integral_nonneg (fun y => sq_nonneg _)
    rw [h_expand] at h_nn
    have h_nn' : 0 ≤ IA - IAB ^ 2 / IB := by
      have h_alg : IA - 2 * lam * IAB + lam ^ 2 * IB = IA - IAB ^ 2 / IB := by
        rw [h_lam_def]; field_simp; ring
      linarith [h_alg ▸ h_nn]
    have h_step : IAB ^ 2 / IB ≤ IA := by linarith
    have := mul_le_mul_of_nonneg_right h_step hIB_nn
    rwa [div_mul_cancel₀ _ hIB0] at this

/-- **Pointwise kernel Cauchy–Schwarz.** For `k ∉ S`, with `g ≥ ε > 0`
and `∂_k g` bounded, at every `x`:
`(ouCoordSet S t (∂_k g) x)² / (ouCoordSet S t g x) ≤
   ouCoordSet S t ((∂_k g)²/g) x`,
the Cauchy–Schwarz on the probability kernel `y ↦ setShift S t x y`. -/
theorem ouCoordSet_kernel_cauchy_schwarz {n : ℕ} (S : Finset (Fin n))
    (t : ℝ) {g D : (Fin n → ℝ) → ℝ}
    (hg_meas : Measurable g) (hD_meas : Measurable D)
    {ε Mg MD : ℝ} (hε : 0 < ε)
    (hg_lo : ∀ z, ε ≤ g z) (hg_hi : ∀ z, g z ≤ Mg)
    (hD_bd : ∀ z, |D z| ≤ MD) (x : Fin n → ℝ) :
    (ouCoordSet S t D x) ^ 2 / (ouCoordSet S t g x) ≤
      ouCoordSet S t (fun z => (D z) ^ 2 / g z) x := by
  classical
  have hshift_meas : Measurable (fun y => setShift S t x y) :=
    measurable_setShift S t x
  set u : (Fin n → ℝ) → ℝ := fun y => D (setShift S t x y) with hu
  set v : (Fin n → ℝ) → ℝ := fun y => g (setShift S t x y) with hv
  have hu_meas : Measurable u := hD_meas.comp hshift_meas
  have hv_meas : Measurable v := hg_meas.comp hshift_meas
  have hv_pos : ∀ y, 0 < v y := fun y => lt_of_lt_of_le hε (hg_lo _)
  have hv_lo : ∀ y, ε ≤ v y := fun y => hg_lo _
  have hv_hi : ∀ y, v y ≤ Mg := fun y => hg_hi _
  have hu_bd : ∀ y, |u y| ≤ MD := fun y => hD_bd _
  -- `A := u/√v`, `B := √v`.
  set A : (Fin n → ℝ) → ℝ := fun y => u y / Real.sqrt (v y) with hA
  set B : (Fin n → ℝ) → ℝ := fun y => Real.sqrt (v y) with hB
  have hsqrt_v_pos : ∀ y, 0 < Real.sqrt (v y) :=
    fun y => Real.sqrt_pos.mpr (hv_pos y)
  have hAB_eq : ∀ y, A y * B y = u y := by
    intro y
    rw [hA, hB, div_mul_cancel₀ _ (ne_of_gt (hsqrt_v_pos y))]
  have hA2_eq : ∀ y, A y ^ 2 = (u y) ^ 2 / v y := by
    intro y
    rw [hA, div_pow, Real.sq_sqrt (hv_pos y).le]
  have hB2_eq : ∀ y, B y ^ 2 = v y := by
    intro y; rw [hB, Real.sq_sqrt (hv_pos y).le]
  -- Integrability facts (all bounded, `γFin n` is a probability measure).
  have hsqrt_v_meas : Measurable (fun y => Real.sqrt (v y)) := hv_meas.sqrt
  have hA_meas : Measurable A := hu_meas.div hsqrt_v_meas
  have hB_meas : Measurable B := hsqrt_v_meas
  have hMD_nn : 0 ≤ MD := (abs_nonneg _).trans (hD_bd (setShift S t x 0))
  have hMg_nn : 0 ≤ Mg :=
    le_trans hε.le (le_trans (hg_lo (setShift S t x 0)) (hg_hi (setShift S t x 0)))
  have hAB_int : Integrable (fun y => A y * B y) (γFin n) := by
    refine integrable_of_bound (M := MD)
      (hA_meas.mul hB_meas) ?_
    intro y; rw [hAB_eq y, Real.norm_eq_abs]; exact hu_bd y
  have hA2_int : Integrable (fun y => A y ^ 2) (γFin n) := by
    refine integrable_of_bound (M := MD ^ 2 / ε)
      (hA_meas.pow_const 2) ?_
    intro y
    rw [hA2_eq y, Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg (sq_nonneg _) (hv_pos y).le)]
    have hnum : (u y) ^ 2 ≤ MD ^ 2 := by
      have := hu_bd y
      nlinarith [abs_nonneg (u y), sq_abs (u y)]
    have h1 : (u y) ^ 2 / v y ≤ MD ^ 2 / v y :=
      div_le_div_of_nonneg_right hnum (hv_pos y).le
    have h2 : MD ^ 2 / v y ≤ MD ^ 2 / ε :=
      div_le_div_of_nonneg_left (sq_nonneg _) hε (hv_lo y)
    linarith
  have hB2_int : Integrable (fun y => B y ^ 2) (γFin n) := by
    refine integrable_of_bound (M := Mg)
      (hB_meas.pow_const 2) ?_
    intro y; rw [hB2_eq y, Real.norm_eq_abs, abs_of_nonneg (hv_pos y).le]
    exact hv_hi y
  have hCS := cauchy_schwarz_measure (γFin n) A B hAB_int hA2_int hB2_int
  -- Rewrite the three integrals.
  have hIAB : (∫ y, A y * B y ∂γFin n) = ouCoordSet S t D x := by
    show (∫ y, A y * B y ∂γFin n) = ∫ y, D (setShift S t x y) ∂γFin n
    exact integral_congr_ae (Filter.Eventually.of_forall (fun y => hAB_eq y))
  have hIA2 : (∫ y, A y ^ 2 ∂γFin n) =
      ouCoordSet S t (fun z => (D z) ^ 2 / g z) x := by
    show (∫ y, A y ^ 2 ∂γFin n) =
      ∫ y, (D (setShift S t x y)) ^ 2 / g (setShift S t x y) ∂γFin n
    exact integral_congr_ae (Filter.Eventually.of_forall (fun y => hA2_eq y))
  have hIB2 : (∫ y, B y ^ 2 ∂γFin n) = ouCoordSet S t g x := by
    show (∫ y, B y ^ 2 ∂γFin n) = ∫ y, g (setShift S t x y) ∂γFin n
    exact integral_congr_ae (Filter.Eventually.of_forall (fun y => hB2_eq y))
  rw [hIAB, hIA2, hIB2] at hCS
  -- `(P D x)² / (P g x) ≤ P((D²/g)) x` from `hCS` and `P g x ≥ ε > 0`.
  have hPg_pos : 0 < ouCoordSet S t g x := by
    have hb := ouCoordSet_bounds S t hg_meas (ε := ε) (M := Mg) hg_lo hg_hi x
    exact lt_of_lt_of_le hε hb.1
  rw [div_le_iff₀ hPg_pos]
  exact hCS

/-- **S4: orthogonal Fisher monotonicity (integrated).** For bounded
measurable `g ≥ ε > 0` and bounded measurable `D`,
`∫ (ouCoordSet S t D)² / (ouCoordSet S t g) dγ_n ≤ ∫ D²/g dγ_n`.
Pointwise kernel Cauchy–Schwarz (`ouCoordSet_kernel_cauchy_schwarz`)
then `ouCoordSet` mean preservation (`integral_ouCoordSet_eq`). -/
theorem integral_sq_div_ouCoordSet_le {n : ℕ} (S : Finset (Fin n))
    (t : ℝ) (ht : 0 ≤ t) {g D : (Fin n → ℝ) → ℝ}
    (hg_meas : Measurable g) (hD_meas : Measurable D)
    {ε Mg MD : ℝ} (hε : 0 < ε)
    (hg_lo : ∀ z, ε ≤ g z) (hg_hi : ∀ z, g z ≤ Mg)
    (hD_bd : ∀ z, |D z| ≤ MD) :
    (∫ x, (ouCoordSet S t D x) ^ 2 / (ouCoordSet S t g x) ∂γFin n) ≤
      ∫ x, (D x) ^ 2 / g x ∂γFin n := by
  classical
  have hMD_nn : 0 ≤ MD := (abs_nonneg _).trans (hD_bd 0)
  have hMg_nn : 0 ≤ Mg := le_trans hε.le (le_trans (hg_lo 0) (hg_hi 0))
  -- The quotient `(D z)²/g z` is bounded by `MD²/ε`, measurable.
  set Q : (Fin n → ℝ) → ℝ := fun z => (D z) ^ 2 / g z with hQ
  have hQ_meas : Measurable Q := (hD_meas.pow_const 2).div hg_meas
  have hQ_nn : ∀ z, 0 ≤ Q z := fun z =>
    div_nonneg (sq_nonneg _) (le_trans hε.le (hg_lo z))
  have hQ_bd : ∀ z, ‖Q z‖ ≤ MD ^ 2 / ε := by
    intro z
    rw [hQ, Real.norm_eq_abs, abs_of_nonneg (hQ_nn z)]
    have hnum : (D z) ^ 2 ≤ MD ^ 2 := by
      have := hD_bd z
      nlinarith [abs_nonneg (D z), sq_abs (D z)]
    have hgz_pos : 0 < g z := lt_of_lt_of_le hε (hg_lo z)
    have h1 : (D z) ^ 2 / g z ≤ MD ^ 2 / g z :=
      div_le_div_of_nonneg_right hnum hgz_pos.le
    have h2 : MD ^ 2 / g z ≤ MD ^ 2 / ε :=
      div_le_div_of_nonneg_left (sq_nonneg _) hε (hg_lo z)
    linarith
  -- Integrability of the LHS integrand and of `ouCoordSet S t Q`.
  have hPD_meas : Measurable (ouCoordSet S t D) := measurable_ouCoordSet S t hD_meas
  have hPg_meas : Measurable (ouCoordSet S t g) := measurable_ouCoordSet S t hg_meas
  have hPQ_meas : Measurable (ouCoordSet S t Q) := measurable_ouCoordSet S t hQ_meas
  have hPg_lo : ∀ x, ε ≤ ouCoordSet S t g x := fun x =>
    (ouCoordSet_bounds S t hg_meas (ε := ε) (M := Mg) hg_lo hg_hi x).1
  have hPD_bd : ∀ x, |ouCoordSet S t D x| ≤ MD := by
    intro x
    have hb := ouCoordSet_bounds S t hD_meas (ε := -MD) (M := MD)
      (fun z => by have := hD_bd z; rw [abs_le] at this; linarith [this.1])
      (fun z => by have := hD_bd z; rw [abs_le] at this; linarith [this.2]) x
    rw [abs_le]; exact ⟨hb.1, hb.2⟩
  have hlhs_bd : ∀ x, ‖(ouCoordSet S t D x) ^ 2 / (ouCoordSet S t g x)‖ ≤
      MD ^ 2 / ε := by
    intro x
    have hPgx_pos : 0 < ouCoordSet S t g x := lt_of_lt_of_le hε (hPg_lo x)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg (sq_nonneg _) hPgx_pos.le)]
    have hnum : (ouCoordSet S t D x) ^ 2 ≤ MD ^ 2 := by
      have := hPD_bd x
      nlinarith [abs_nonneg (ouCoordSet S t D x), sq_abs (ouCoordSet S t D x)]
    have h1 : (ouCoordSet S t D x) ^ 2 / ouCoordSet S t g x ≤
        MD ^ 2 / ouCoordSet S t g x :=
      div_le_div_of_nonneg_right hnum hPgx_pos.le
    have h2 : MD ^ 2 / ouCoordSet S t g x ≤ MD ^ 2 / ε :=
      div_le_div_of_nonneg_left (sq_nonneg _) hε (hPg_lo x)
    linarith
  have hlhs_int : Integrable
      (fun x => (ouCoordSet S t D x) ^ 2 / (ouCoordSet S t g x)) (γFin n) :=
    integrable_of_bound ((hPD_meas.pow_const 2).div hPg_meas) hlhs_bd
  have hPQ_int : Integrable (ouCoordSet S t Q) (γFin n) :=
    integrable_of_bound hPQ_meas (fun x => by
      have hb := ouCoordSet_bounds S t hQ_meas (ε := 0) (M := MD ^ 2 / ε)
        (fun z => hQ_nn z)
        (fun z => by
          have := hQ_bd z; rw [Real.norm_eq_abs, abs_of_nonneg (hQ_nn z)] at this
          exact this) x
      rw [Real.norm_eq_abs, abs_of_nonneg hb.1]; exact hb.2)
  have hQ_int : Integrable Q (γFin n) :=
    integrable_of_bound hQ_meas hQ_bd
  -- Pointwise CS, then `integral_mono`, then mean preservation.
  calc (∫ x, (ouCoordSet S t D x) ^ 2 / (ouCoordSet S t g x) ∂γFin n)
      ≤ ∫ x, ouCoordSet S t Q x ∂γFin n :=
        integral_mono hlhs_int hPQ_int (fun x =>
          ouCoordSet_kernel_cauchy_schwarz S t hg_meas hD_meas hε
            hg_lo hg_hi hD_bd x)
    _ = ∫ x, Q x ∂γFin n :=
        integral_ouCoordSet_eq S t ht hQ_meas
          (C := MD ^ 2 / ε) hQ_bd

/-- **S5: the coordinate telescope (single step + induction).** For
`IsCoreFin f`, `ε > 0`, `t ≥ 0` and any `Finset S` of coordinates,
`BE(g_ε) − BE(ouCoordSet S t g_ε) ≤ (1−e^{−2t})/2 · Σ_{k∈S} I_k(g_ε)`,
where `g_ε = f²+ε`. Proved by `Finset.induction`: each inserted
coordinate `k ∉ S` contributes one per-coordinate step
(`boltzmannEntropyFin_ouCoord_step_le` with the abstract slice
derivative `D = ouCoordSet S t (∂_k g_ε)` supplied by the 1-parameter
commutation `ouCoordSet_slice_contDiff_one`), and the resulting
`∫ D²/(ouCoordSet S t g_ε)` is bounded by `I_k(g_ε)` via the orthogonal
Fisher monotonicity `integral_sq_div_ouCoordSet_le`. -/
theorem boltzmann_ouCoordSet_telescope_le {m : ℕ}
    {f : (Fin (m + 1) → ℝ) → ℝ} (hf : IsCoreFin f) {ε : ℝ} (hε : 0 < ε)
    (t : ℝ) (ht : 0 ≤ t) (S : Finset (Fin (m + 1))) :
    boltzmannEntropyFin (fun x => f x * f x + ε) -
        boltzmannEntropyFin (ouCoordSet S t (fun x => f x * f x + ε)) ≤
      (1 - Real.exp (-2 * t)) / 2 *
        ∑ k ∈ S, fisherInfoFinCoord k (fun x => f x * f x + ε) := by
  classical
  obtain ⟨hf_smooth, M, hM⟩ := hf
  have hf : IsCoreFin f := ⟨hf_smooth, M, hM⟩
  have hM_nn : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0).1
  set gε : (Fin (m + 1) → ℝ) → ℝ := fun x => f x * f x + ε with hgε
  have hgε_core : IsCoreFin gε :=
    IsCoreFin_add (IsCoreFin_mul hf hf) (IsCoreFin_const ε)
  have hgε_C1 : ContDiff ℝ 1 gε := hgε_core.contDiff.of_le (by norm_num)
  have hgε_meas : Measurable gε := hgε_core.measurable
  have hf_le : ∀ x, |f x| ≤ M := fun x => by
    rw [← Real.norm_eq_abs]; exact (hM x).1
  have hpd_le : ∀ i x, |partialDeriv i f x| ≤ M := fun i x => by
    rw [← Real.norm_eq_abs]; exact (hM x).2.1 i
  -- Two-sided bounds on `gε`.
  have hgε_lo : ∀ z, ε ≤ gε z := fun z => by
    have : 0 ≤ f z * f z := mul_self_nonneg _
    simp only [hgε]; linarith
  have hgε_hi : ∀ z, gε z ≤ M ^ 2 + ε := fun z => by
    have : f z * f z ≤ M ^ 2 := by
      nlinarith [hf_le z, abs_nonneg (f z), sq_abs (f z)]
    simp only [hgε]; linarith
  have hgε_bd : ∀ z, ‖gε z‖ ≤ M ^ 2 + ε := fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (le_trans hε.le (hgε_lo z))]; exact hgε_hi z
  -- The coordinate-`k` partial of `gε` and its `2M²` bound.
  have hpd_gε_eq : ∀ k : Fin (m + 1), partialDeriv k gε =
      fun x => 2 * f x * partialDeriv k f x := fun k =>
    partialDeriv_sq_add_const k hf ε
  have hpd_gε_cont : ∀ k : Fin (m + 1), Continuous (partialDeriv k gε) := by
    intro k
    rw [hpd_gε_eq k]
    exact (continuous_const.mul hf.continuous).mul (hf.partial_continuous k)
  have hpd_gε_meas : ∀ k : Fin (m + 1), Measurable (partialDeriv k gε) :=
    fun k => (hpd_gε_cont k).measurable
  have hpd_gε_bd : ∀ (k : Fin (m + 1)) z, |partialDeriv k gε z| ≤ 2 * M ^ 2 := by
    intro k z
    rw [hpd_gε_eq k]
    have h1 : |(2 : ℝ) * f z * partialDeriv k f z| =
        2 * |f z| * |partialDeriv k f z| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    rw [h1]
    nlinarith [hf_le z, hpd_le k z, abs_nonneg (f z),
      abs_nonneg (partialDeriv k f z)]
  -- Per-step bound: for `k ∉ S`,
  --   `BE(P_S gε) − BE(ouCoord k (P_S gε)) ≤ (1−e^{−2t})/2 · I_k(gε)`.
  have hstep : ∀ (S : Finset (Fin (m + 1))) (k : Fin (m + 1)), k ∉ S →
      boltzmannEntropyFin (ouCoordSet S t gε) -
          boltzmannEntropyFin (ouCoord k t (ouCoordSet S t gε)) ≤
        (1 - Real.exp (-2 * t)) / 2 * fisherInfoFinCoord k gε := by
    intro S k hk
    set hS : (Fin (m + 1) → ℝ) → ℝ := ouCoordSet S t gε with hhS
    set D : (Fin (m + 1) → ℝ) → ℝ := ouCoordSet S t (partialDeriv k gε) with hD
    -- Slice-`C¹` and slice-derivative of `hS` along `k` (`k ∉ S`).
    have hslice := fun y => ouCoordSet_slice_contDiff_one S k hk t hgε_C1
      (hpd_gε_cont k) (M := max (M ^ 2 + ε) (2 * M ^ 2))
      (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hε.le (hgε_lo z))]
        exact le_trans (hgε_hi z) (le_max_left _ _))
      (fun z => le_trans (hpd_gε_bd k z) (le_max_right _ _)) y
    have hslice_C1 : ∀ y : Fin m → ℝ,
        ContDiff ℝ 1 (fun r => hS (Fin.insertNth (α := fun _ => ℝ) k r y)) :=
      fun y => (hslice y).1
    have hslice_deriv : ∀ y : Fin m → ℝ,
        deriv (fun r => hS (Fin.insertNth (α := fun _ => ℝ) k r y)) =
          fun r => D (Fin.insertNth (α := fun _ => ℝ) k r y) :=
      fun y => (hslice y).2
    have hhS_meas : Measurable hS := measurable_ouCoordSet S t hgε_meas
    have hD_meas : Measurable D :=
      measurable_ouCoordSet S t (hpd_gε_meas k)
    have hhS_lo : ∀ z, ε ≤ hS z := fun z =>
      (ouCoordSet_bounds S t hgε_meas (ε := ε) (M := M ^ 2 + ε)
        hgε_lo hgε_hi z).1
    have hhS_hi : ∀ z, hS z ≤ M ^ 2 + ε := fun z =>
      (ouCoordSet_bounds S t hgε_meas (ε := ε) (M := M ^ 2 + ε)
        hgε_lo hgε_hi z).2
    have hD_bd : ∀ z, |D z| ≤ 2 * M ^ 2 := by
      intro z
      have hb := ouCoordSet_bounds S t (hpd_gε_meas k)
        (ε := -(2 * M ^ 2)) (M := 2 * M ^ 2)
        (fun w => by have := hpd_gε_bd k w; rw [abs_le] at this; linarith [this.1])
        (fun w => by have := hpd_gε_bd k w; rw [abs_le] at this; linarith [this.2]) z
      rw [abs_le]; exact ⟨hb.1, hb.2⟩
    -- Apply the per-coordinate step bound (S3) with abstract `D`.
    -- Common bound for both `hS ≤ ·` and `|D| ≤ ·`.
    set Mstep : ℝ := max (M ^ 2 + ε) (2 * M ^ 2) with hMstep
    have hstep0 := boltzmannEntropyFin_ouCoord_step_le k hS D hhS_meas
      hslice_C1 hslice_deriv hD_meas (ε := ε) (M := Mstep) hε
      hhS_lo (fun z => le_trans (hhS_hi z) (le_max_left _ _))
      (fun z => le_trans (hD_bd z) (le_max_right _ _)) t ht
    -- Bound `∫ D²/hS` by `I_k(gε)` via orthogonal Fisher monotonicity (S4).
    have hS4 : (∫ x, (D x) ^ 2 / hS x ∂γFin (m + 1)) ≤
        fisherInfoFinCoord k gε := by
      have := integral_sq_div_ouCoordSet_le S t ht hgε_meas (hpd_gε_meas k)
        (ε := ε) (Mg := M ^ 2 + ε) (MD := 2 * M ^ 2) hε
        hgε_lo hgε_hi (fun z => hpd_gε_bd k z)
      simpa [hD, hhS, fisherInfoFinCoord] using this
    have hcoef_nn : 0 ≤ (1 - Real.exp (-2 * t)) / 2 := by
      have hexp : Real.exp (-2 * t) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith)
      linarith
    calc boltzmannEntropyFin hS - boltzmannEntropyFin (ouCoord k t hS)
        ≤ (1 - Real.exp (-2 * t)) / 2 * ∫ x, (D x) ^ 2 / hS x ∂γFin (m + 1) :=
          hstep0
      _ ≤ (1 - Real.exp (-2 * t)) / 2 * fisherInfoFinCoord k gε := by
          exact mul_le_mul_of_nonneg_left hS4 hcoef_nn
  -- Induction over `S` accumulating the per-coordinate steps.
  induction S using Finset.induction with
  | empty =>
      simp [ouCoordSet_empty]
  | insert k S hk ih =>
      have hcoef_nn : 0 ≤ (1 - Real.exp (-2 * t)) / 2 := by
        have hexp : Real.exp (-2 * t) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by linarith)
        linarith
      -- `ouCoordSet (insert k S) = ouCoord k ∘ ouCoordSet S` (`k ∉ S`).
      have hcomp : ouCoordSet (insert k S) t gε =
          ouCoord k t (ouCoordSet S t gε) :=
        (ouCoord_ouCoordSet S k hk t hgε_meas (C := M ^ 2 + ε) hgε_bd).symm
      have hI_nn : 0 ≤ fisherInfoFinCoord k gε := by
        unfold fisherInfoFinCoord
        exact integral_nonneg (fun x =>
          div_nonneg (sq_nonneg _) (le_trans hε.le (hgε_lo x)))
      calc boltzmannEntropyFin gε -
            boltzmannEntropyFin (ouCoordSet (insert k S) t gε)
          = (boltzmannEntropyFin gε - boltzmannEntropyFin (ouCoordSet S t gε))
            + (boltzmannEntropyFin (ouCoordSet S t gε) -
                boltzmannEntropyFin (ouCoordSet (insert k S) t gε)) := by ring
        _ ≤ ((1 - Real.exp (-2 * t)) / 2 *
              ∑ j ∈ S, fisherInfoFinCoord j gε)
            + (1 - Real.exp (-2 * t)) / 2 * fisherInfoFinCoord k gε := by
              refine add_le_add ih ?_
              rw [hcomp]
              exact hstep S k hk
        _ = (1 - Real.exp (-2 * t)) / 2 *
              ∑ j ∈ insert k S, fisherInfoFinCoord j gε := by
              rw [Finset.sum_insert hk]; ring

/-- **Integrated multivariate entropy decay for `f²` (BGL Thm. 5.5.2,
n-dim Gaussian case).**

For every `IsCoreFin` test function `f` and every `t ≥ 0`,
`Ent(f²) - Ent(P_t(f²)) ≤ (1 - e^{-2t}) * 2 * E_n(f,f)`.

This is the finite-dimensional Gaussian tensor lift of the proved 1D
theorem `Gaussian1D.ouSemigroup_entropy_sq_decay_bound_proved`, obtained
via the telescoping route documented above.

**Reference:** Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov
Diffusion Operators*, Springer 2014, §5.5, Theorem 5.5.2. -/
theorem ouSemigroupFin_entropy_sq_decay_bound {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (t : ℝ) (ht : 0 ≤ t) (hf : IsCoreFin f) :
    DirichletSpace.entropy (ds := dirichletSpaceFin (n := n)) (fun x => f x * f x) -
      DirichletSpace.entropy (ds := dirichletSpaceFin (n := n))
        (ouSemigroupFin t (fun x => f x * f x)) ≤
      (1 - Real.exp (-2 * 1 * t)) * (2 / 1) * ouEnergyFin f f := by
  -- Step 1 (proved): reduce the centered entropy difference to the
  -- Boltzmann difference via macroscopic-term cancellation.
  rw [entropy_sub_eq_boltzmann_sub f t ht hf]
  -- Step 2 (proved): reduce to the per-ε regularized Boltzmann bound
  -- via the n-dim DCT tail `boltzmannSubFin_le_of_perEps`. After this,
  -- it suffices to bound, for every `ε > 0`,
  --   `BE(f²+ε) - BE(P_t(f²) + ε) ≤ 2 (1 - e^{-2t}) · ouEnergyFin f f`.
  refine boltzmannSubFin_le_of_perEps (n := n) hf t ht ?_
  intro ε hε
  -- The per-ε goal. `g_ε := f²+ε` is `IsCoreFin`; the telescope route
  -- (S2–S5) is fully formalized in `boltzmann_ouCoordSet_telescope_le`.
  -- Here: rewrite `P_t(f²)+ε = P_t g_ε = ouCoordSet univ t g_ε`, apply
  -- the telescope at `S = univ`, then bound `Σ_k I_k(g_ε) ≤ 4·E`
  -- (`sum_fisherInfoFinCoord_sq_add_const_le`). The `n = 0` case is
  -- degenerate (`ouSemigroupFin` is the identity, LHS = 0 ≤ RHS).
  --
  -- Corrected architecture (Gemini deep-think + 3.1-pro, 2026-05-19):
  -- the per-coordinate step lemma was weakened to slice-level `C¹`
  -- hypotheses with an *abstract* slice-derivative `D`; the telescope
  -- iterates' slice `C¹` + slice-derivative are supplied by the
  -- single-real-parameter commutation `hasDerivAt_slice_ouCoordSet`
  -- (frozen-slot identity, `k ∉ S`), avoiding any joint multivariate
  -- `C²` or mixed partials. The earlier "`C²` core predicate"
  -- (`IsCore2Fin`) plan was superseded by this lower-risk 1-parameter
  -- route — no new predicate was needed.
  set gε : (Fin n → ℝ) → ℝ := fun x => f x * f x + ε with hgε
  have hf_meas : Measurable f := hf.measurable
  obtain ⟨M, hM⟩ := hf.bound_exists
  have hM_nn : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0)
  -- `P_t(f²) + ε = P_t g_ε`.
  have hPsq : (fun x => ouSemigroupFin t (fun x => f x * f x) x + ε) =
      ouSemigroupFin t gε :=
    (ouSemigroupFin_sq_add_const hf ε t ht).symm
  rw [hPsq]
  -- Coefficient identity: `(1−e^{−2·1·t})·(2/1) = (1−e^{−2t})·2`.
  have hcoef : (1 - Real.exp (-2 * 1 * t)) * (2 / 1) =
      (1 - Real.exp (-2 * t)) / 2 * 4 := by
    rw [show (-2 * 1 * t : ℝ) = -2 * t from by ring]; ring
  rw [hcoef]
  have hE_nn : 0 ≤ ouEnergyFin f f := by
    unfold ouEnergyFin ouGammaFin
    exact integral_nonneg (fun x => Finset.sum_nonneg
      (fun i _ => mul_self_nonneg _))
  have hcoef_nn : 0 ≤ (1 - Real.exp (-2 * t)) / 2 := by
    have hexp : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  cases n with
  | zero =>
      -- Degenerate: on `Fin 0 → ℝ` the OU shift is the identity, so
      -- `ouSemigroupFin t gε = gε` and the entropy difference is `0`.
      have hid : ouSemigroupFin t gε = gε := by
        funext x
        show (∫ _y, gε (ouShiftFin t x _y) ∂γFin 0) = gε x
        have hshift : ∀ y : Fin 0 → ℝ, ouShiftFin t x y = x := by
          intro y; funext i; exact absurd i.2 (by omega)
        simp only [hshift]
        simp
      rw [hid, sub_self]
      positivity
  | succ m =>
      -- `ouSemigroupFin t gε = ouCoordSet univ t gε`.
      have huniv : ouSemigroupFin t gε =
          ouCoordSet (Finset.univ : Finset (Fin (m + 1))) t gε :=
        (ouCoordSet_univ t).symm
      rw [huniv]
      -- Telescope at `S = univ`, then `Σ_k I_k(gε) ≤ 4·E`.
      have htel := boltzmann_ouCoordSet_telescope_le (f := f) hf hε t ht
        (Finset.univ : Finset (Fin (m + 1)))
      have hsum := sum_fisherInfoFinCoord_sq_add_const_le (n := m + 1)
        (f := f) hf (ε := ε) hε
      calc boltzmannEntropyFin gε -
            boltzmannEntropyFin (ouCoordSet Finset.univ t gε)
          ≤ (1 - Real.exp (-2 * t)) / 2 *
              ∑ k : Fin (m + 1), fisherInfoFinCoord k gε := htel
        _ ≤ (1 - Real.exp (-2 * t)) / 2 * (4 * ouEnergyFin f f) := by
              refine mul_le_mul_of_nonneg_left ?_ hcoef_nn
              simpa [hgε] using hsum
        _ = (1 - Real.exp (-2 * t)) / 2 * 4 * ouEnergyFin f f := by ring

end GaussianFin
