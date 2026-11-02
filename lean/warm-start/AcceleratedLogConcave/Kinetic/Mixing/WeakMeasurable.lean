import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Weak measurability in a separable Hilbert space

A map into a separable real inner product space whose inner products with every
vector are measurable is strongly measurable (Pettis, in the Hilbert case). The
proof recovers distances to arbitrary points from a countable dense subset of the
unit sphere, and then writes every open set as a countable union of balls.
This is used to derive the integrability of clock-indexed families of L²
operators from measurability of their matrix coefficients.
-/
noncomputable section
open MeasureTheory Set TopologicalSpace Metric
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [SecondCountableTopology H] {α : Type*} [MeasurableSpace α]

omit [SecondCountableTopology H] in
/-- The norm is a countable supremum of inner products with unit vectors. -/
theorem norm_eq_iSup_inner_sphere (S : Set (sphere (0 : H) 1)) (hS : Dense S)
    (z : H) : ‖z‖ = ⨆ e : S, ⟪((e : sphere (0 : H) 1) : H), z⟫ := by
  have hle : ∀ e : S, ⟪((e : sphere (0 : H) 1) : H), z⟫ ≤ ‖z‖ := fun e => by
    have h1 : ‖((e : sphere (0 : H) 1) : H)‖ = 1 := by simp
    calc ⟪((e : sphere (0 : H) 1) : H), z⟫ ≤ ‖((e : sphere (0 : H) 1) : H)‖ * ‖z‖ :=
          real_inner_le_norm _ _
      _ = ‖z‖ := by rw [h1, one_mul]
  by_cases hz : z = 0
  · subst hz
    simp
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let e0 : sphere (0 : H) 1 := ⟨‖z‖⁻¹ • z, by simp [norm_smul, hzpos.ne']⟩
  have he0 : ⟪((e0 : sphere (0 : H) 1) : H), z⟫ = ‖z‖ := by
    change ⟪‖z‖⁻¹ • z, z⟫ = ‖z‖
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have : Nonempty S := by
    obtain ⟨e, he, -⟩ := hS.exists_mem_open isOpen_univ ⟨e0, trivial⟩
    exact ⟨⟨e, he⟩⟩
  symm
  apply ciSup_eq_of_forall_le_of_forall_lt_exists_gt hle
  intro c hc
  have hopen : IsOpen {e : sphere (0 : H) 1 | c < ⟪(e : H), z⟫} :=
    isOpen_lt continuous_const
      (continuous_subtype_val.inner continuous_const)
  obtain ⟨e, heS, hec⟩ := hS.exists_mem_open hopen ⟨e0, by simpa [he0] using hc⟩
  exact ⟨⟨e, heS⟩, hec⟩

/-- Distances to every point are measurable when all inner products are. -/
theorem measurable_dist_of_weak (u : α → H)
    (hu : ∀ g : H, Measurable (fun a => ⟪g, u a⟫)) (x : H) :
    Measurable (fun a => ‖u a - x‖) := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (sphere (0 : H) 1)
  have : Countable S := hSc.to_subtype
  have : (fun a => ‖u a - x‖) = fun a => ⨆ e : S, (⟪((e : sphere (0 : H) 1) : H), u a⟫ -
      ⟪((e : sphere (0 : H) 1) : H), x⟫) := by
    funext a
    rw [norm_eq_iSup_inner_sphere S hSd (u a - x)]
    simp only [inner_sub_right]
  rw [this]
  exact Measurable.iSup fun e => (hu _).sub_const _

/-- Pettis' theorem for separable real inner product spaces. -/
theorem measurable_of_weak [MeasurableSpace H] [BorelSpace H] (u : α → H)
    (hu : ∀ g : H, Measurable (fun a => ⟪g, u a⟫)) : Measurable u := by
  apply measurable_of_isOpen
  intro U hU
  have hr : ∀ x : U, ∃ r : ℝ, 0 < r ∧ Metric.ball (x : H) r ⊆ U := fun x => by
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp hU x x.2
    exact ⟨r, hr, hb⟩
  choose r hr0 hrU using hr
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : U => Metric.ball (x : H) (r x)) (fun x => Metric.isOpen_ball)
  have hUeq : U = ⋃ x ∈ T, Metric.ball (x : H) (r x) := by
    rw [hT]
    apply Subset.antisymm
    · intro y hy
      exact mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self (hr0 ⟨y, hy⟩)⟩
    · exact iUnion_subset fun x => hrU x
  rw [hUeq, preimage_iUnion₂]
  exact MeasurableSet.biUnion hTc fun x _ => by
    have h := measurableSet_lt (measurable_dist_of_weak u hu (x : H)) (measurable_const (a := r x))
    convert h using 1
    ext a
    simp [Metric.mem_ball, dist_eq_norm]

/-- Strong measurability from measurability of every matrix coefficient. -/
theorem stronglyMeasurable_of_weak (u : α → H)
    (hu : ∀ g : H, Measurable (fun a => ⟪g, u a⟫)) : StronglyMeasurable u := by
  let _ : MeasurableSpace H := borel H
  have _ : BorelSpace H := ⟨rfl⟩
  exact (measurable_of_weak u hu).stronglyMeasurable

omit [SecondCountableTopology H] in
/-- A family of contractions that is strongly measurable on each input is
integrable on each input, over a probability space. -/
theorem integrable_of_stronglyMeasurable_contraction (μ : Measure α) [IsProbabilityMeasure μ]
    (T : α → H →L[ℝ] H) (hT : ∀ r, ‖T r‖ ≤ 1)
    (hm : ∀ f, StronglyMeasurable (fun r => T r f)) (f : H) :
    Integrable (fun r => T r f) μ :=
  Integrable.mono' (integrable_const ‖f‖) (hm f).aestronglyMeasurable
    (Filter.Eventually.of_forall fun r =>
      ((T r).le_opNorm f).trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hT r) (norm_nonneg f)))

/-- Strong measurability passes to the family of Hilbert adjoints. -/
theorem stronglyMeasurable_adjoint [CompleteSpace H] (T : α → H →L[ℝ] H)
    (hm : ∀ f, StronglyMeasurable (fun r => T r f)) (f : H) :
    StronglyMeasurable (fun r => (T r).adjoint f) := by
  apply stronglyMeasurable_of_weak
  intro g
  have h : (fun r => ⟪g, (T r).adjoint f⟫) = fun r => ⟪T r g, f⟫ := by
    funext r
    rw [ContinuousLinearMap.adjoint_inner_right]
  rw [h]
  have hm' : Measurable (fun r => innerSL ℝ f (T r g)) :=
    ((innerSL ℝ f).continuous.comp_stronglyMeasurable (hm g)).measurable
  convert hm' using 2 with r
  simp [real_inner_comm]

section Indicators
open scoped ENNReal Topology
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- Matrix coefficients of a family of bounded operators on `L²(μ)` are measurable
once they are measurable on pairs of indicator functions. -/
theorem measurable_inner_of_indicator (T : α → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (h : ∀ (c d : ℝ) {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B),
      Measurable fun r => ⟪indicatorConstLp 2 hA (measure_ne_top μ A) c,
        T r (indicatorConstLp 2 hB (measure_ne_top μ B) d)⟫)
    (f g : Lp ℝ 2 μ) : Measurable fun r => ⟪f, T r g⟫ := by
  have hfix : ∀ (c : ℝ) {A : Set X} (hA : MeasurableSet A) (g : Lp ℝ 2 μ),
      Measurable fun r => ⟪indicatorConstLp 2 hA (measure_ne_top μ A) c, T r g⟫ := by
    intro c A hA g
    refine Lp.induction (p := 2) (by simp) (fun g => Measurable fun r =>
      ⟪indicatorConstLp 2 hA (measure_ne_top μ A) c, T r g⟫) ?_ ?_ ?_ g
    · intro d B hB hμB
      rw [Lp.simpleFunc.coe_indicatorConst]
      simpa using h c d hA hB
    · intro g1 g2 hg1 hg2 _ m1 m2
      simp only [map_add, inner_add_right]
      exact m1.add m2
    · apply isClosed_of_closure_subset
      intro g hg
      rw [mem_closure_iff_seq_limit] at hg
      obtain ⟨u, hu, hug⟩ := hg
      refine measurable_of_tendsto_metrizable (f := fun k r =>
        ⟪indicatorConstLp 2 hA (measure_ne_top μ A) c, T r (u k)⟫) hu ?_
      rw [tendsto_pi_nhds]
      intro r
      exact (continuous_const.inner ((T r).continuous)).continuousAt.tendsto.comp hug
  revert g
  refine Lp.induction (p := 2) (by simp) (fun f => ∀ g : Lp ℝ 2 μ, Measurable fun r => ⟪f, T r g⟫)
    ?_ ?_ ?_ f
  · intro c A hA hμA g
    rw [Lp.simpleFunc.coe_indicatorConst]
    exact hfix c hA g
  · intro f1 f2 hf1 hf2 _ m1 m2 g
    simp only [inner_add_left]
    exact (m1 g).add (m2 g)
  · apply isClosed_of_closure_subset
    intro f hf
    rw [mem_closure_iff_seq_limit] at hf
    obtain ⟨u, hu, huf⟩ := hf
    intro g
    refine measurable_of_tendsto_metrizable (f := fun k r => ⟪u k, T r g⟫) (fun k => hu k g) ?_
    rw [tendsto_pi_nhds]
    intro r
    exact (continuous_id.inner continuous_const).continuousAt.tendsto.comp huf

end Indicators

end AcceleratedLogConcave.Kinetic
