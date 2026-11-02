/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ouGeneratorFin` as an `L²(γFin n)` element (G2/G4 base)

Shared prerequisite for the `GeneratorCompat` discharge
(`plans/gross-discharge.md`, G2/G4): the named OU generator
`ouGeneratorFin f = Δf − x·∇f` (from `EuclideanGenerator`) is
square-integrable against the standard multivariate Gaussian for core
`f`, hence defines an element of `Lp ℝ 2 (γFin n)`.

Split out so the strong-`L²` limit (`EuclideanGeneratorLimit`) and the
γ-IBP / assembly (`EuclideanGeneratorCompat`) can be developed in
parallel against a common base.
-/

import AcceleratedLogConcave.External.MarkovSemigroups.Instances.WorkInProgress.EuclideanFinLp
import AcceleratedLogConcave.External.MarkovSemigroups.Instances.WorkInProgress.EuclideanGenerator

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace ContDiff

noncomputable section

attribute [local simp] Pi.sub_def

namespace GaussianFin

variable {n : ℕ}

/-- `ouGeneratorFin f = Δf − x·∇f ∈ L²(γFin n)` for core `f`.

Strategy: `IsCoreFin` gives `f` `ContDiff ℝ ∞` with uniformly bounded
first/second partials, so `∑ᵢ ∂ᵢ²f` is bounded and `∑ᵢ xᵢ ∂ᵢf` has at
most linear growth in `x`; both are square-integrable against the
standard Gaussian `γFin n` (bounded part via `memLp_two_of_bound`;
linear-growth part via Gaussian polynomial moments). -/
theorem memLp_ouGeneratorFin {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    MemLp (ouGeneratorFin f) 2 (γFin n) := by
  obtain ⟨hcd, M, hM⟩ := hf
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) ((hM (fun _ => 0)).1)
  have hcoreF : IsCoreFin f := ⟨hcd, M, hM⟩
  -- Each Gaussian coordinate is in `L²`.
  have hcoord : ∀ i : Fin n, MemLp (fun x : Fin n → ℝ => x i) 2 (γFin n) := by
    intro i
    have heval : MeasurePreserving (Function.eval i) (γFin n) Gaussian1D.γ := by
      simpa [γFin] using
        (MeasureTheory.measurePreserving_eval (μ := fun _ : Fin n => Gaussian1D.γ) i)
    have hid : MemLp (id : ℝ → ℝ) (2 : ℝ≥0∞) Gaussian1D.γ := by
      have h := memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (2 : ℝ≥0)
      have hcoe : ((2 : ℝ≥0) : ℝ≥0∞) = 2 := by norm_num
      simpa [Gaussian1D.γ, hcoe] using h
    have hcomp := hid.comp_measurePreserving heval
    simpa [Function.comp] using hcomp
  -- Diffusion part `∑ᵢ ∂ᵢ²f` (function-valued Finset sum): bounded ⇒ `L²`.
  have hA : MemLp (∑ i : Fin n, secondPartial i f) 2 (γFin n) := by
    have hsm : StronglyMeasurable (∑ i : Fin n, secondPartial i f) :=
      Finset.stronglyMeasurable_sum _ (fun i _ =>
        (hcoreF.secondPartial_continuous i).stronglyMeasurable)
    refine (memLp_const ((n : ℝ) * M)).mono hsm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => ?_))
    have hnM : (0 : ℝ) ≤ (n : ℝ) * M := by positivity
    have hb : |∑ i : Fin n, secondPartial i f x| ≤ (n : ℝ) * M := by
      calc |∑ i : Fin n, secondPartial i f x|
          ≤ ∑ i : Fin n, |secondPartial i f x| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, M := Finset.sum_le_sum
            (fun i _ => by simpa [Real.norm_eq_abs] using (hM x).2.2 i)
        _ = (n : ℝ) * M := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp only [Finset.sum_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg hnM]
    exact hb
  -- Drift part `∑ᵢ xᵢ ∂ᵢf`: each term is (Gaussian coordinate)·(bounded) ∈ `L²`.
  have hB : MemLp
      (∑ i : Fin n, fun x : Fin n → ℝ => x i * partialDeriv i f x) 2 (γFin n) := by
    refine memLp_finsetSum' _ (fun i _ => ?_)
    have hsm : AEStronglyMeasurable
        (fun x : Fin n → ℝ => x i * partialDeriv i f x) (γFin n) :=
      (((measurable_pi_apply i).stronglyMeasurable).mul
        (hcoreF.partial_continuous i).stronglyMeasurable).aestronglyMeasurable
    refine ((hcoord i).const_mul M).mono hsm
      (Filter.Eventually.of_forall (fun x => ?_))
    have hpm : ‖partialDeriv i f x‖ ≤ M := (hM x).2.1 i
    calc ‖x i * partialDeriv i f x‖
        = ‖x i‖ * ‖partialDeriv i f x‖ := by rw [norm_mul]
      _ ≤ ‖x i‖ * M :=
          mul_le_mul_of_nonneg_left hpm (norm_nonneg _)
      _ = ‖M * x i‖ := by
          rw [norm_mul, Real.norm_eq_abs M, abs_of_nonneg hM0, mul_comm]
  have hougen : ouGeneratorFin f =
      (∑ i : Fin n, secondPartial i f)
        - (∑ i : Fin n, fun x : Fin n → ℝ => x i * partialDeriv i f x) := by
    funext x
    simp [ouGeneratorFin_apply, Finset.sum_apply, Pi.sub_apply]
  rw [hougen]
  exact hA.sub hB

/-- The `L²(γFin n)` element represented by `ouGeneratorFin f`
(`= Δf − x·∇f`), for core `f`. -/
def ouGeneratorFinLp {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    Lp ℝ 2 (γFin n) :=
  (memLp_ouGeneratorFin hf).toLp (ouGeneratorFin f)

/-- **nD Gaussian integration by parts (Dirichlet-form identity)** —
the multivariate Gaussian IBP: for `C^∞` `f, g` with bounded value,
first and pure-second coordinate derivatives, integrating `g` against
the OU generator `Lf = Δf − x·∇f` over the standard Gaussian equals
minus the Dirichlet energy `∫ ⟨∇g,∇f⟩`.

**General (no project definitions)** — stated purely in Mathlib terms
(`fderiv`/`Pi.single`/`MeasureTheory.Measure.pi`/
`ProbabilityTheory.gaussianReal`), so it is a reusable,
vetting-amenable textbook statement; the project-specific
`ouGeneratorFin_ibp_integral` is derived from it by unfolding the
(thin) project definitions. Same strategic pattern as
`gaussianOU_heatEquation_within_zero` (the Gross-G2 deep cruxes are
deferred to general vetted axioms; the discharge route is the
coordinatewise Fubini lift of the *proved* 1D
`Gaussian1D.gaussian_dirichlet_form_bilinear`).

Reference: Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov
Diffusion Operators* (2014), §2.7 / §1.6 (the Dirichlet form
`E(g,f)=∫⟨∇g,∇f⟩` is the generator's energy form: `∫ g·Lf = −E(g,f)`
for the OU generator); Gaussian integration by parts (Stein).
**Vetted Standard / Likely correct** (Gemini `gemini-3-pro-preview`,
2026-05-16; recorded in `AXIOM_AUDIT.md`): sign/normalization exact
(`∇φ/φ = −x` for `N(0,I)` yields the `−x·∇f` drift, coefficient 1, no
factor-2/variance rescale); non-vacuous (`f=g=sin x₀`); pure-second-
partial + boundedness hypotheses sufficient (Gaussian moments absorb
the linear-growth `g·(x·∇f)`; IBP is coordinatewise-Fubini, no
mixed/third partials); `g`'s pure-2nd-partial bound is superfluous-
but-harmless (kept for core-class symmetry). Discharge route: the
coordinatewise Fubini lift of the proved 1D
`Gaussian1D.gaussian_dirichlet_form_bilinear`. -/
private theorem gaussianFin_integrationByParts_coord {n : ℕ}
    {f g : (Fin (n + 1) → ℝ) → ℝ}
    (hf : IsCoreFin f) (hg : IsCoreFin g) (i : Fin (n + 1)) :
    ∫ x, g x * (secondPartial i f x - x i * partialDeriv i f x) ∂γFin (n + 1)
      = - ∫ x, partialDeriv i g x * partialDeriv i f x ∂γFin (n + 1) := by
  obtain ⟨hf_smooth, Mf, hf_bd⟩ := hf
  obtain ⟨hg_smooth, Mg, hg_bd⟩ := hg
  have hf_core : IsCoreFin f := ⟨hf_smooth, Mf, hf_bd⟩
  have hg_core : IsCoreFin g := ⟨hg_smooth, Mg, hg_bd⟩
  have hg_meas : Measurable g := IsCoreFin.measurable hg_core
  have hMf0 : (0 : ℝ) ≤ Mf := le_trans (norm_nonneg _) ((hf_bd (fun _ => 0)).1)
  have hMg0 : (0 : ℝ) ≤ Mg := le_trans (norm_nonneg _) ((hg_bd (fun _ => 0)).1)
  let φ : ℝ × (Fin n → ℝ) → (Fin (n + 1) → ℝ) :=
    fun p => Fin.insertNth (α := fun _ => ℝ) i p.1 p.2
  let A : ℝ × (Fin n → ℝ) → ℝ :=
    fun p => g (φ p) * (secondPartial i f (φ p) - p.1 * partialDeriv i f (φ p))
  let B : ℝ × (Fin n → ℝ) → ℝ :=
    fun p => partialDeriv i g (φ p) * partialDeriv i f (φ p)
  have hφ_meas : Measurable φ := by
    have hφ_cont : Continuous φ :=
      Continuous.finInsertNth i continuous_fst continuous_snd
    exact hφ_cont.measurable
  have hA1_int : Integrable (fun p : ℝ × (Fin n → ℝ) => g (φ p) * secondPartial i f (φ p))
      (Gaussian1D.γ.prod (γFin n)) := by
    refine Integrable.mono' (integrable_const (Mg * Mf))
      (((hg_meas.comp hφ_meas).mul
        ((IsCoreFin.secondPartial_measurable hf_core i).comp hφ_meas)).aestronglyMeasurable) ?_
    filter_upwards with p
    calc
      ‖g (φ p) * secondPartial i f (φ p)‖
          = ‖g (φ p)‖ * ‖secondPartial i f (φ p)‖ := by rw [norm_mul]
      _ ≤ Mg * Mf := by
          exact mul_le_mul ((hg_bd (φ p)).1) ((hf_bd (φ p)).2.2 i)
            (norm_nonneg _) hMg0
  have hA2_int : Integrable (fun p : ℝ × (Fin n → ℝ) => g (φ p) * (p.1 * partialDeriv i f (φ p)))
      (Gaussian1D.γ.prod (γFin n)) := by
    refine Integrable.mono'
      ((((memLp_id_gaussianReal 1).integrable le_rfl).abs.comp_fst (γFin n)).const_mul (Mg * Mf))
      (((hg_meas.comp hφ_meas).mul
        (measurable_fst.mul ((IsCoreFin.partial_measurable hf_core i).comp hφ_meas))).aestronglyMeasurable) ?_
    filter_upwards with p
    calc
      ‖g (φ p) * (p.1 * partialDeriv i f (φ p))‖
          = ‖g (φ p)‖ * (‖p.1‖ * ‖partialDeriv i f (φ p)‖) := by
              rw [norm_mul, norm_mul]
      _ = ‖g (φ p)‖ * (|p.1| * ‖partialDeriv i f (φ p)‖) := by
              simp [Real.norm_eq_abs]
      _ ≤ Mg * (|p.1| * Mf) := by
        have hpartial : |p.1| * ‖partialDeriv i f (φ p)‖ ≤ |p.1| * Mf :=
          mul_le_mul_of_nonneg_left ((hf_bd (φ p)).2.1 i) (abs_nonneg _)
        calc
          ‖g (φ p)‖ * (|p.1| * ‖partialDeriv i f (φ p)‖)
              ≤ Mg * (|p.1| * ‖partialDeriv i f (φ p)‖) := by
                  exact mul_le_mul_of_nonneg_right ((hg_bd (φ p)).1)
                    (mul_nonneg (abs_nonneg _) (norm_nonneg _))
          _ ≤ Mg * (|p.1| * Mf) := by
                  exact mul_le_mul_of_nonneg_left hpartial hMg0
      _ = (Mg * Mf) * |p.1| := by ring
  have hA_int : Integrable A (Gaussian1D.γ.prod (γFin n)) := by
    simpa [A, mul_sub] using hA1_int.sub hA2_int
  have hB_int : Integrable B (Gaussian1D.γ.prod (γFin n)) := by
    refine Integrable.mono' (integrable_const (Mg * Mf))
      ((((IsCoreFin.partial_measurable hg_core i).comp hφ_meas).mul
        ((IsCoreFin.partial_measurable hf_core i).comp hφ_meas)).aestronglyMeasurable) ?_
    filter_upwards with p
    calc
      ‖partialDeriv i g (φ p) * partialDeriv i f (φ p)‖
          = ‖partialDeriv i g (φ p)‖ * ‖partialDeriv i f (φ p)‖ := by rw [norm_mul]
      _ ≤ Mg * Mf := by
          exact mul_le_mul ((hg_bd (φ p)).2.1 i) ((hf_bd (φ p)).2.1 i)
            (norm_nonneg _) hMg0
  have hA_split :
      ∫ x, g x * (secondPartial i f x - x i * partialDeriv i f x) ∂γFin (n + 1)
        = ∫ p, A p ∂(Gaussian1D.γ.prod (γFin n)) := by
    let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
    have he : MeasurePreserving e (γFin (n + 1)) (Gaussian1D.γ.prod (γFin n)) :=
      measurePreserving_piFinSuccAbove_γFin (n := n) i
    have hEq :
        (fun x : Fin (n + 1) → ℝ => g x * (secondPartial i f x - x i * partialDeriv i f x))
          = A ∘ e := by
      funext x
      simp [A, φ, e]
    rw [hEq]
    exact he.integral_comp' A
  have hB_split :
      ∫ x, partialDeriv i g x * partialDeriv i f x ∂γFin (n + 1)
        = ∫ p, B p ∂(Gaussian1D.γ.prod (γFin n)) := by
    let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
    have he : MeasurePreserving e (γFin (n + 1)) (Gaussian1D.γ.prod (γFin n)) :=
      measurePreserving_piFinSuccAbove_γFin (n := n) i
    have hEq :
        (fun x : Fin (n + 1) → ℝ => partialDeriv i g x * partialDeriv i f x)
          = B ∘ e := by
      funext x
      simp [B, φ, e]
    rw [hEq]
    exact he.integral_comp' B
  have hinner : ∀ y : Fin n → ℝ,
      ∫ s, A (s, y) ∂Gaussian1D.γ = - ∫ s, B (s, y) ∂Gaussian1D.γ := by
    intro y
    have hg_slice_smooth : ContDiff ℝ ∞ (fun s => g (Fin.insertNth (α := fun _ => ℝ) i s y)) := by
      simpa [slice_eq_coordSection] using
        (section_contDiff hg_smooth i (Fin.insertNth (α := fun _ => ℝ) i 0 y))
    have hf_slice_smooth : ContDiff ℝ ∞ (fun s => f (Fin.insertNth (α := fun _ => ℝ) i s y)) := by
      simpa [slice_eq_coordSection] using
        (section_contDiff hf_smooth i (Fin.insertNth (α := fun _ => ℝ) i 0 y))
    have hg_slice_deriv :
        deriv (fun s => g (Fin.insertNth (α := fun _ => ℝ) i s y)) =
          fun s => partialDeriv i g (Fin.insertNth (α := fun _ => ℝ) i s y) := by
      simpa [slice_eq_coordSection, update_insertNth_same] using
        (section_deriv hg_smooth i (Fin.insertNth (α := fun _ => ℝ) i 0 y))
    have hf_slice_deriv :
        deriv (fun s => f (Fin.insertNth (α := fun _ => ℝ) i s y)) =
          fun s => partialDeriv i f (Fin.insertNth (α := fun _ => ℝ) i s y) := by
      simpa [slice_eq_coordSection, update_insertNth_same] using
        (section_deriv hf_smooth i (Fin.insertNth (α := fun _ => ℝ) i 0 y))
    have hf_slice_second :
        deriv (deriv (fun s => f (Fin.insertNth (α := fun _ => ℝ) i s y))) =
          fun s => secondPartial i f (Fin.insertNth (α := fun _ => ℝ) i s y) := by
      simpa [slice_eq_coordSection, update_insertNth_same] using
        (section_secondDeriv hf_core i (Fin.insertNth (α := fun _ => ℝ) i 0 y))
    have hg_slice_bd : ∀ s, |g (Fin.insertNth (α := fun _ => ℝ) i s y)| ≤ Mg := by
      intro s
      rw [← Real.norm_eq_abs]
      exact (hg_bd _).1
    have hg_slice_deriv_bd :
        ∀ s, |deriv (fun r => g (Fin.insertNth (α := fun _ => ℝ) i r y)) s| ≤ Mg := by
      intro s
      rw [hg_slice_deriv, ← Real.norm_eq_abs]
      exact (hg_bd _).2.1 i
    have hf_slice_bd : ∀ s, |f (Fin.insertNth (α := fun _ => ℝ) i s y)| ≤ Mf := by
      intro s
      rw [← Real.norm_eq_abs]
      exact (hf_bd _).1
    have hf_slice_deriv_bd :
        ∀ s, |deriv (fun r => f (Fin.insertNth (α := fun _ => ℝ) i r y)) s| ≤ Mf := by
      intro s
      rw [hf_slice_deriv, ← Real.norm_eq_abs]
      exact (hf_bd _).2.1 i
    have hf_slice_second_bd :
        ∀ s, |deriv (deriv (fun r => f (Fin.insertNth (α := fun _ => ℝ) i r y))) s| ≤ Mf := by
      intro s
      rw [hf_slice_second, ← Real.norm_eq_abs]
      exact (hf_bd _).2.2 i
    have h1d := Gaussian1D.gaussian_dirichlet_form_bilinear
      (f := fun s => g (Fin.insertNth (α := fun _ => ℝ) i s y))
      (h := fun s => f (Fin.insertNth (α := fun _ => ℝ) i s y))
      (hf := hg_slice_smooth.of_le
        (by
          exact WithTop.coe_le_coe.mpr (show (1 : ℕ∞) ≤ ⊤ by simp)))
      hg_slice_bd hg_slice_deriv_bd
      (hh := hf_slice_smooth.of_le
        (by
          exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ by simp)))
      hf_slice_bd hf_slice_deriv_bd hf_slice_second_bd
    rw [hf_slice_second, hg_slice_deriv, hf_slice_deriv] at h1d
    simpa [A, B, φ] using h1d
  calc
    ∫ x, g x * (secondPartial i f x - x i * partialDeriv i f x) ∂γFin (n + 1)
      = ∫ p, A p ∂(Gaussian1D.γ.prod (γFin n)) := hA_split
    _ = ∫ y, ∫ s, A (s, y) ∂Gaussian1D.γ ∂γFin n := by
          rw [integral_prod_symm A hA_int]
    _ = ∫ y, - ∫ s, B (s, y) ∂Gaussian1D.γ ∂γFin n := by
          refine integral_congr_ae (Filter.Eventually.of_forall hinner)
    _ = - ∫ y, ∫ s, B (s, y) ∂Gaussian1D.γ ∂γFin n := by
          rw [integral_neg]
    _ = - ∫ p, B p ∂(Gaussian1D.γ.prod (γFin n)) := by
          rw [integral_prod_symm B hB_int]
    _ = - ∫ x, partialDeriv i g x * partialDeriv i f x ∂γFin (n + 1) := by
          rw [hB_split]

theorem gaussianFin_integrationByParts {n : ℕ}
    (f g : (Fin n → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ∞ f) (Mf : ℝ)
    (hf_bd : ∀ x : Fin n → ℝ,
      ‖f x‖ ≤ Mf ∧
      (∀ i : Fin n, ‖fderiv ℝ f x (Pi.single i 1)‖ ≤ Mf) ∧
      (∀ i : Fin n,
        ‖fderiv ℝ (fun z => fderiv ℝ f z (Pi.single i 1)) x
            (Pi.single i 1)‖ ≤ Mf))
    (hg_smooth : ContDiff ℝ ∞ g) (Mg : ℝ)
    (hg_bd : ∀ x : Fin n → ℝ,
      ‖g x‖ ≤ Mg ∧
      (∀ i : Fin n, ‖fderiv ℝ g x (Pi.single i 1)‖ ≤ Mg) ∧
      (∀ i : Fin n,
        ‖fderiv ℝ (fun z => fderiv ℝ g z (Pi.single i 1)) x
            (Pi.single i 1)‖ ≤ Mg)) :
    ∫ x, g x *
        ((∑ i : Fin n,
            fderiv ℝ (fun z => fderiv ℝ f z (Pi.single i 1)) x
              (Pi.single i 1))
          - ∑ i : Fin n, x i * fderiv ℝ f x (Pi.single i 1))
      ∂(MeasureTheory.Measure.pi
          (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1))
      = - ∫ x,
          (∑ i : Fin n,
            fderiv ℝ g x (Pi.single i 1) * fderiv ℝ f x (Pi.single i 1))
          ∂(MeasureTheory.Measure.pi
              (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)) := by
  have hf : IsCoreFin f := by
    refine ⟨hf_smooth, Mf, ?_⟩
    convert hf_bd using 1
    rfl
  have hg : IsCoreFin g := by
    refine ⟨hg_smooth, Mg, ?_⟩
    convert hg_bd using 1
    rfl
  have hMf0 : (0 : ℝ) ≤ Mf := le_trans (norm_nonneg _) ((hf_bd (fun _ => 0)).1)
  have hMg0 : (0 : ℝ) ≤ Mg := le_trans (norm_nonneg _) ((hg_bd (fun _ => 0)).1)
  change ∫ x, g x *
      ((∑ i : Fin n, secondPartial i f x) - ∑ i : Fin n, x i * partialDeriv i f x) ∂γFin n
      = - ∫ x, (∑ i : Fin n, partialDeriv i g x * partialDeriv i f x) ∂γFin n
  cases n with
  | zero =>
      simp [γFin]
  | succ m =>
      have hcoord :
          ∀ i : Fin (m + 1),
            ∫ x, g x * (secondPartial i f x - x i * partialDeriv i f x) ∂γFin (m + 1)
              = - ∫ x, partialDeriv i g x * partialDeriv i f x ∂γFin (m + 1) := by
        intro i
        exact gaussianFin_integrationByParts_coord (n := m) hf hg i
      have hterm_int :
          ∀ i : Fin (m + 1),
            Integrable (fun x => g x * (secondPartial i f x - x i * partialDeriv i f x))
              (γFin (m + 1)) := by
        intro i
        have hA : Integrable (fun x : Fin (m + 1) → ℝ => g x * secondPartial i f x) (γFin (m + 1)) := by
          refine integrable_of_bound (M := Mg * Mf)
            ((IsCoreFin.measurable hg).mul (IsCoreFin.secondPartial_measurable hf i)) ?_
          intro x
          calc
            ‖g x * secondPartial i f x‖
                = ‖g x‖ * ‖secondPartial i f x‖ := by rw [norm_mul]
            _ ≤ Mg * Mf := by
                exact mul_le_mul ((hg_bd x).1) ((hf_bd x).2.2 i) (norm_nonneg _) hMg0
        have hB : Integrable (fun x : Fin (m + 1) → ℝ => g x * (x i * partialDeriv i f x))
            (γFin (m + 1)) := by
          refine Integrable.mono'
            ((integrable_abs_eval_γFin (n := m + 1) i).const_mul (Mg * Mf))
            (((IsCoreFin.measurable hg).mul
              ((measurable_pi_apply i).mul (IsCoreFin.partial_measurable hf i))).aestronglyMeasurable) ?_
          filter_upwards with x
          calc
            ‖g x * (x i * partialDeriv i f x)‖
                = ‖g x‖ * (‖x i‖ * ‖partialDeriv i f x‖) := by
                    rw [norm_mul, norm_mul]
            _ = ‖g x‖ * (|x i| * ‖partialDeriv i f x‖) := by
                    simp [Real.norm_eq_abs]
            _ ≤ Mg * (|x i| * Mf) := by
                have hpartial : |x i| * ‖partialDeriv i f x‖ ≤ |x i| * Mf :=
                  mul_le_mul_of_nonneg_left ((hf_bd x).2.1 i) (abs_nonneg _)
                calc
                  ‖g x‖ * (|x i| * ‖partialDeriv i f x‖)
                      ≤ Mg * (|x i| * ‖partialDeriv i f x‖) := by
                          exact mul_le_mul_of_nonneg_right ((hg_bd x).1)
                            (mul_nonneg (abs_nonneg _) (norm_nonneg _))
                  _ ≤ Mg * (|x i| * Mf) := by
                          exact mul_le_mul_of_nonneg_left hpartial hMg0
            _ = (Mg * Mf) * |x i| := by ring
        simpa [mul_sub] using hA.sub hB
      have hsum_int :
          ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))),
            Integrable (fun x => g x * (secondPartial i f x - x i * partialDeriv i f x))
              (γFin (m + 1)) := by
        intro i hi
        exact hterm_int i
      have henergy_int :
          ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))),
            Integrable (fun x => partialDeriv i g x * partialDeriv i f x) (γFin (m + 1)) := by
        intro i hi
        refine integrable_of_bound (M := Mg * Mf)
          ((IsCoreFin.partial_measurable hg i).mul (IsCoreFin.partial_measurable hf i)) ?_
        intro x
        calc
          ‖partialDeriv i g x * partialDeriv i f x‖
              = ‖partialDeriv i g x‖ * ‖partialDeriv i f x‖ := by rw [norm_mul]
          _ ≤ Mg * Mf := by
              exact mul_le_mul ((hg_bd x).2.1 i) ((hf_bd x).2.1 i) (norm_nonneg _) hMg0
      calc
        ∫ x, g x *
            ((∑ i : Fin (m + 1), secondPartial i f x)
              - ∑ i : Fin (m + 1), x i * partialDeriv i f x) ∂γFin (m + 1)
            = ∫ x, ∑ i : Fin (m + 1), g x * (secondPartial i f x - x i * partialDeriv i f x)
                ∂γFin (m + 1) := by
                  refine integral_congr_ae (Filter.Eventually.of_forall ?_)
                  intro x
                  change g x * ((∑ i : Fin (m + 1), secondPartial i f x)
                    - ∑ i : Fin (m + 1), x i * partialDeriv i f x)
                    = ∑ i : Fin (m + 1), g x * (secondPartial i f x - x i * partialDeriv i f x)
                  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  ring
        _ = ∑ i : Fin (m + 1),
              ∫ x, g x * (secondPartial i f x - x i * partialDeriv i f x) ∂γFin (m + 1) := by
                rw [integral_finsetSum (s := Finset.univ) (f := fun i x =>
                  g x * (secondPartial i f x - x i * partialDeriv i f x)) hsum_int]
        _ = ∑ i : Fin (m + 1),
              - ∫ x, partialDeriv i g x * partialDeriv i f x ∂γFin (m + 1) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                exact hcoord i
        _ = - ∑ i : Fin (m + 1),
              ∫ x, partialDeriv i g x * partialDeriv i f x ∂γFin (m + 1) := by
                simp
        _ = - ∫ x, ∑ i : Fin (m + 1), partialDeriv i g x * partialDeriv i f x ∂γFin (m + 1) := by
                rw [integral_finsetSum (s := Finset.univ) (f := fun i x =>
                  partialDeriv i g x * partialDeriv i f x) henergy_int]

/-- **G4 — nD Gaussian integration by parts, integral form**
(`∫ g·(ouGeneratorFin f) dγFin n = -ouEnergyFin g f`). Derived from
the general `gaussianFin_integrationByParts` by unfolding the thin
project definitions. -/
theorem ouGeneratorFin_ibp_integral {f g : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (hg : IsCoreFin g) :
    ∫ x, g x * ouGeneratorFin f x ∂γFin n = - ouEnergyFin g f := by
  obtain ⟨hsf, Mf, hMf⟩ := hf
  obtain ⟨hsg, Mg, hMg⟩ := hg
  convert gaussianFin_integrationByParts (n := n) f g hsf Mf hMf hsg Mg hMg using 1 <;> rfl

/-- **G4 — nD Gaussian integration by parts (inner-product form).**
For core `f, g`: `⟪g, ouGeneratorFin f⟫_{L²(γFin n)} = -ouEnergyFin g f`.
The `L²` inner product unfolds (via `L2.inner_def` + `MemLp.coeFn_toLp`
for `coreToL2 g` and `ouGeneratorFinLp f`) to
`∫ g·(ouGeneratorFin f) dγ`, which is `ouGeneratorFin_ibp_integral`.
Lives here (imports only the building base, no `EuclideanGeneratorLimit`)
so it verifies independently of the parallel limit work. -/
theorem ouGeneratorFin_ibp {f g : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (hg : IsCoreFin g) :
    ⟪(isCoreFin_memLp g hg).toLp g, ouGeneratorFinLp hf⟫_ℝ
      = - ouEnergyFin g f := by
  -- Pure `Lp` wiring (no math): the analytic content is
  -- `ouGeneratorFin_ibp_integral`. Force `coreToL2`/`ouGeneratorFinLp`
  -- to their `.toLp` normal form (`rfl`), then mirror the proven
  -- `EuclideanFinLp` `L².inner_def` incantation via a hand-written
  -- `have` so the `coeFn_toLp` rewrites match syntactically.
  show ⟪(isCoreFin_memLp g hg).toLp g,
        (memLp_ouGeneratorFin hf).toLp (ouGeneratorFin f)⟫_ℝ
      = - ouEnergyFin g f
  rw [MeasureTheory.L2.inner_def]
  have hint :
      ∫ a, ⟪((isCoreFin_memLp g hg).toLp g) a,
          ((memLp_ouGeneratorFin hf).toLp (ouGeneratorFin f)) a⟫_ℝ
        ∂γFin n
        = ∫ x, g x * ouGeneratorFin f x ∂γFin n := by
    refine integral_congr_ae ?_
    filter_upwards [(isCoreFin_memLp g hg).coeFn_toLp,
      (memLp_ouGeneratorFin hf).coeFn_toLp] with x hgx hfx
    simp only [hgx, hfx]
    change RCLike.re (ouGeneratorFin f x * star (g x))
      = g x * ouGeneratorFin f x
    simp [mul_comm]
  rw [hint, ouGeneratorFin_ibp_integral hf hg]

end GaussianFin

end
