import AcceleratedLogConcave.Oracle.SamplingExecutableStability

/-!
Source-only proposal, 2026-10-21. Not compiled or accepted for integration.

Center-section regularity for the literal sampling executable on each fixed full
raw tape. The external host momentum is irrelevant to the returned Point, even
without child stability; fresh child momenta still come from the same raw tape.

No topology or measurable-space instance on tapes, no joint tape measurability,
no probability law, and no precision-rank induction are asserted here.
-/
noncomputable section
namespace AcceleratedLogConcave.Oracle
open TapeLowering AffineLowering NoisyLayer RecursiveMeanProgram PrivateSamplingProgram
open SourceExecutableTables RetainedMeanFinalBatch Numerics.AffineGraph
open scoped BigOperators NNReal

namespace FixedTapeStability

/-- The full-tape child invariant gives the usual Lipschitz API for each center
section. Both the entering momentum and every raw tape coordinate stay fixed. -/
theorem childStable_center_lipschitzWith (p : Program c .point) (coeff : Fin c → ℝ)
    (G : Point d → Point d) (K : ℝ≥0) (h : ChildStable p coeff G (K : ℝ))
    (P : Point d) (tape : Tape d p) :
    LipschitzWith K (fun x : Point d =>
      childPoint (run p G ⟨coeff, x, P⟩ Env.empty tape)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm] using childStable_tape p coeff G K h P x y tape

end FixedTapeStability

namespace FixedTapeSampling
open FixedTapeStability

set_option backward.isDefEq.respectTransparency false in
/-- Equal coefficients and center suffice for the sampling Point output.
Unlike the body transport theorem, this compares the actual setup executions.
It intentionally does not claim equality of the full Result or its trace. -/
theorem code_same_center_coefficients
    {c cf : Fin n → ℕ} {p : ∀ i, Program (c i) .point}
    {pf : ∀ i, Program (cf i) .point} (cfg : Config n C c cf p pf)
    (T : ∀ i, Fin (tapeShape (p i)).gaussianBlocks →
      Fin (tapeShape (p i)).gaussianBlocks → ℝ)
    (coeff : ∀ i, Fin (c i) → ℝ)
    (Tf : ∀ i, Fin (tapeShape (pf i)).gaussianBlocks →
      Fin (tapeShape (pf i)).gaussianBlocks → ℝ)
    (coeffF : ∀ i, Fin (cf i) → ℝ) (G : Point d → Point d)
    (input input' : Inputs d C)
    (hcoeff : input'.coefficient = input.coefficient)
    (hcenter : input'.center = input.center)
    (htable : ∀ i, input.coefficient ∘ (cfg.mainSlots ∘ childSlot c p i) =
      matrixTable (T i) (coeff i))
    (htableF : ∀ i, input.coefficient ∘ cfg.finalSlots i = matrixTable (Tf i) (coeffF i))
    (tape : Tape d (code cfg)) :
    childPoint (run (code cfg) G input' Env.empty tape) =
      childPoint (run (code cfg) G input Env.empty tape) := by
  let ρ : Env d (replyCtx n [.point, .scalar, .point, .point]) :=
    setupEnv cfg input tape.2.1
  let ρ' : Env d (replyCtx n [.point, .scalar, .point, .point]) :=
    setupEnv cfg input' tape.2.1
  have hs : @ρ' = @ρ := by
    simp only [ρ, ρ', PrivateSamplingProgram.setupEnv, hcoeff, hcenter]
  have hb := body_same_coefficients cfg batchRef (RefMap.shiftMany n Ref.here)
    T coeff Tf coeffF G input input' (setupEnv cfg input tape.2.1)
    hcoeff htable htableF tape.2.2.2.2.2
  rw [run_code_setup, run_code_setup]
  change childPoint (run _ G input' ρ' _) = childPoint (run _ G input ρ _)
  rw [hs]
  exact hb

set_option backward.isDefEq.respectTransparency false in
/-- The actual executable's external momentum is unused. There is no oracle
regularity, child IH, radius-sign, covariance-law, or dimension restriction. -/
theorem build_momentum_eq (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
    (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
    (G : Point d → Point d) (x P P' : Point d)
    (tape : Tape d (SamplingExecutable.build S e r Ds main final N).program) :
    childPoint (run (SamplingExecutable.build S e r Ds main final N).program G
        ⟨(SamplingExecutable.build S e r Ds main final N).coefficient, x, P'⟩ Env.empty tape) =
      childPoint (run (SamplingExecutable.build S e r Ds main final N).program G
        ⟨(SamplingExecutable.build S e r Ds main final N).coefficient, x, P⟩ Env.empty tape) := by
  let cfg := samplingConfig main final N
  let input : Inputs d (samplingSize main final) :=
    ⟨samplingTable S e r Ds main final, x, P⟩
  let T := fun i => CovarianceSetup.childRoot (samplingNoise S r Ds)
    (S.radius r (e i)) (main i).shiftVector
  let Tf := fun i => CovarianceSetup.childRoot (samplingNoise S r Ds)
    (S.radius r (e i)) (final i).shiftVector
  have ht (i : Fin n) : input.coefficient ∘
      (cfg.mainSlots ∘ childSlot (fun i => (main i).size) (fun i => (main i).program) i) =
      matrixTable (T i) (main i).coefficient := by
    funext j
    simp only [input, cfg, samplingConfig, Function.comp_apply, samplingTable_main,
      samplingMainTable, RecursiveMeanPublicTable.sourceLayerTable, layerTable_child,
      T, samplingNoise]
  have htf (i : Fin n) : input.coefficient ∘ cfg.finalSlots i =
      matrixTable (Tf i) (final i).coefficient := by
    funext j
    simp only [input, cfg, samplingConfig, Function.comp_apply, samplingTable_final, Tf]
  exact code_same_center_coefficients cfg T (fun i => (main i).coefficient)
    Tf (fun i => (final i).coefficient) G input
    ⟨samplingTable S e r Ds main final, x, P'⟩ rfl rfl ht htf tape

section Actual
variable (S : SamplingGeometry m) (e : Fin n ≃ S.Node) (r Ds : ℝ)
    (main final : Fin n → ExecutableData) (N : ℕ)
    (G : Point d → Point d) (κ : ℝ) (hm : 0 < m) (hr : 0 ≤ r) (hκ : 0 ≤ κ)
    (hmain : ∀ i, ChildStable (main i).program (main i).coefficient G κ)
    (hfinal : ∀ i, ChildStable (final i).program (final i).coefficient G κ)
include hm hr hκ hmain hfinal

/-- Finite center Lipschitz constant, including the fresh final child batch at
N = 0. No contraction hypothesis is needed. -/
theorem build_center_lipschitzWith (P : Point d)
    (tape : Tape d (SamplingExecutable.build S e r Ds main final N).program) :
    LipschitzWith
      ⟨κ*r*∑ j ∈ Finset.range (N+1), (κ*r^2)^j, by positivity⟩
      (fun x : Point d =>
        childPoint (run (SamplingExecutable.build S e r Ds main final N).program G
          ⟨(SamplingExecutable.build S e r Ds main final N).coefficient, x, P⟩
          Env.empty tape)) := by
  exact childStable_center_lipschitzWith _ _ _ _
    (build_childStable S e r Ds main final N G κ hm hr hκ hmain hfinal) P tape

/-- The geometric Lipschitz constant requires the same strict contraction
hypothesis as the supplier theorem; it is not an unconditional replacement. -/
theorem build_center_lipschitzWith_geometric (hq : κ*r^2 < 1) (P : Point d)
    (tape : Tape d (SamplingExecutable.build S e r Ds main final N).program) :
    LipschitzWith ⟨κ*r/(1-κ*r^2),
      div_nonneg (mul_nonneg hκ hr) (sub_pos.mpr hq).le⟩
      (fun x : Point d =>
        childPoint (run (SamplingExecutable.build S e r Ds main final N).program G
          ⟨(SamplingExecutable.build S e r Ds main final N).coefficient, x, P⟩
          Env.empty tape)) := by
  exact childStable_center_lipschitzWith _ _ _ _
    (build_childStable_geometric S e r Ds main final N G κ hm hr hκ hmain hfinal hq) P tape

theorem build_center_continuous (P : Point d)
    (tape : Tape d (SamplingExecutable.build S e r Ds main final N).program) :
    Continuous (fun x : Point d =>
      childPoint (run (SamplingExecutable.build S e r Ds main final N).program G
        ⟨(SamplingExecutable.build S e r Ds main final N).coefficient, x, P⟩ Env.empty tape)) :=
  (build_center_lipschitzWith S e r Ds main final N G κ hm hr hκ hmain hfinal P tape).continuous

theorem build_center_measurable (P : Point d)
    (tape : Tape d (SamplingExecutable.build S e r Ds main final N).program) :
    Measurable (fun x : Point d =>
      childPoint (run (SamplingExecutable.build S e r Ds main final N).program G
        ⟨(SamplingExecutable.build S e r Ds main final N).coefficient, x, P⟩ Env.empty tape)) :=
  (build_center_continuous S e r Ds main final N G κ hm hr hκ hmain hfinal P tape).measurable

/-- A concrete consumer: any continuous center parameterization may be used.
No regularity of the ignored external momentum parameterization is required. -/
theorem build_continuous_center_parameter {α : Type*} [TopologicalSpace α]
    (x P : α → Point d) (hx : Continuous x)
    (tape : Tape d (SamplingExecutable.build S e r Ds main final N).program) :
    Continuous (fun a =>
      childPoint (run (SamplingExecutable.build S e r Ds main final N).program G
        ⟨(SamplingExecutable.build S e r Ds main final N).coefficient, x a, P a⟩
        Env.empty tape)) := by
  have heq : (fun a =>
      childPoint (run (SamplingExecutable.build S e r Ds main final N).program G
        ⟨(SamplingExecutable.build S e r Ds main final N).coefficient, x a, P a⟩
        Env.empty tape)) = (fun a =>
      childPoint (run (SamplingExecutable.build S e r Ds main final N).program G
        ⟨(SamplingExecutable.build S e r Ds main final N).coefficient, x a, 0⟩
        Env.empty tape)) := by
    funext a
    exact build_momentum_eq S e r Ds main final N G (x a) 0 (P a) tape
  rw [heq]
  exact (build_center_continuous S e r Ds main final N G κ hm hr hκ hmain hfinal
    (0 : Point d) tape).comp hx

/-- Fixed-tape Borel composition with an arbitrary measurable center map.
There is deliberately no measurability assumption on the unused host momentum. -/
theorem build_measurable_center_parameter {α : Type*} [MeasurableSpace α]
    (x P : α → Point d) (hx : Measurable x)
    (tape : Tape d (SamplingExecutable.build S e r Ds main final N).program) :
    Measurable (fun a =>
      childPoint (run (SamplingExecutable.build S e r Ds main final N).program G
        ⟨(SamplingExecutable.build S e r Ds main final N).coefficient, x a, P a⟩
        Env.empty tape)) := by
  have heq : (fun a =>
      childPoint (run (SamplingExecutable.build S e r Ds main final N).program G
        ⟨(SamplingExecutable.build S e r Ds main final N).coefficient, x a, P a⟩
        Env.empty tape)) = (fun a =>
      childPoint (run (SamplingExecutable.build S e r Ds main final N).program G
        ⟨(SamplingExecutable.build S e r Ds main final N).coefficient, x a, 0⟩
        Env.empty tape)) := by
    funext a
    exact build_momentum_eq S e r Ds main final N G (x a) 0 (P a) tape
  rw [heq]
  exact (build_center_measurable S e r Ds main final N G κ hm hr hκ hmain hfinal
    (0 : Point d) tape).comp hx

end Actual
end FixedTapeSampling
end AcceleratedLogConcave.Oracle
