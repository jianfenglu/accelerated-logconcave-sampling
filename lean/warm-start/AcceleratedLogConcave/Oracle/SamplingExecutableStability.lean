import AcceleratedLogConcave.Oracle.SamplingBlockStability
import AcceleratedLogConcave.Oracle.SamplingExecutable

/-! Actual sampling build stability on every fixed raw tape, under child IHs.
No distribution, covariance validity, oracle Lipschitz assumption, or rank induction. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.FixedTapeSampling
open TapeLowering AffineLowering NoisyLayer RecursiveMeanProgram PrivateSamplingProgram
open SourceExecutableTables FixedTapeStability RetainedMeanFinalBatch Numerics.AffineGraph
open scoped BigOperators

/-- Reindex the existing source row bound onto the actual executable node table. -/
theorem sampling_matrix_mass_le (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
    (r : ℝ) (hm : 0 < m) (hr : 0 ≤ r) (i : Fin n) :
    (∑ j, |samplingMatrix S e r i j|) ≤ r^2 := by
  calc
    _ = ∑ j : S.Node, |(S.graph r (0 : ℝ) 0).matrix (e i) j| := by
      exact e.sum_comp (fun j => |(S.graph r (0 : ℝ) 0).matrix (e i) j|)
    _ ≤ _ := S.sum_abs_matrix_le hm r hr (0 : ℝ) 0 (e i)

/-- The actual final row has absolute coefficient mass r, not one. -/
theorem sampling_final_mass (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
    (r : ℝ) (hm : 0 < m) (hr : 0 ≤ r) :
    (∑ i, |samplingFinalWeight S e r i|) = r := by
  calc
    _ = ∑ j : S.Node, |-(r/samplingEnd S.τ)*S.row (samplingEnd S.τ) j| :=
      e.sum_comp _
    _ = r := S.sum_abs_output_weights hm r hr

section Actual
variable (S : SamplingGeometry m) (e : Fin n ≃ S.Node) (r Ds : ℝ)
    (main final : Fin n → ExecutableData) (N : ℕ)
    (G : Point d → Point d) (κ : ℝ) (hm : 0 < m) (hr : 0 ≤ r) (hκ : 0 ≤ κ)
    (hmain : ∀ i, ChildStable (main i).program (main i).coefficient G κ)
    (hfinal : ∀ i, ChildStable (final i).program (final i).coefficient G κ)
include hm hr hκ hmain hfinal

set_option backward.isDefEq.respectTransparency false in
/-- Fixed P and one raw tape for the literal SamplingExecutable.build. -/
theorem build_sub_le (P x y : Point d)
    (tape : Tape d (SamplingExecutable.build S e r Ds main final N).program) :
    ‖childPoint (run (SamplingExecutable.build S e r Ds main final N).program G
        ⟨(SamplingExecutable.build S e r Ds main final N).coefficient,x,P⟩ Env.empty tape) -
      childPoint (run (SamplingExecutable.build S e r Ds main final N).program G
        ⟨(SamplingExecutable.build S e r Ds main final N).coefficient,y,P⟩ Env.empty tape)‖ ≤
      κ*r*‖x-y‖*∑ j ∈ Finset.range (N+1), (κ*r^2)^j := by
  let cfg := samplingConfig main final N
  let input : Inputs d (samplingSize main final) := ⟨samplingTable S e r Ds main final,x,P⟩
  let T := fun i => CovarianceSetup.childRoot (samplingNoise S r Ds)
    (S.radius r (e i)) (main i).shiftVector
  let Tf := fun i => CovarianceSetup.childRoot (samplingNoise S r Ds)
    (S.radius r (e i)) (final i).shiftVector
  have ht (i : Fin n) : input.coefficient ∘
      (cfg.mainSlots ∘ childSlot (fun i => (main i).size) (fun i => (main i).program) i) =
      matrixTable (T i) (main i).coefficient := by
    funext j
    simp only [input,cfg,samplingConfig,Function.comp_apply,samplingTable_main,
      samplingMainTable,RecursiveMeanPublicTable.sourceLayerTable,layerTable_child,T,samplingNoise]
  have htf (i : Fin n) : input.coefficient ∘ cfg.finalSlots i =
      matrixTable (Tf i) (final i).coefficient := by
    funext j
    simp only [input,cfg,samplingConfig,Function.comp_apply,samplingTable_final,Tf]
  have hrow (i : Fin n) :
      (∑ j, |input.coefficient (cfg.mainSlots
        (aSlot (fun i => (main i).size) (fun i => (main i).program) i j))|) ≤ r^2 := by
    simpa only [input,cfg,samplingConfig,samplingTable_main,samplingMainTable,
      RecursiveMeanPublicTable.sourceLayerTable,layerTable_a] using sampling_matrix_mass_le S e r hm hr i
  have hw : (∑ i, |input.coefficient (cfg.rowWeight i)|) ≤ r := by
    simpa only [input,cfg,samplingConfig,samplingTable_scalar,samplingScalarTable,
      Fin.append_right,Fin.append_left] using (sampling_final_mass S e r hm hr).le
  exact code_sub_le cfg T (fun i => (main i).coefficient) Tf (fun i => (final i).coefficient)
    G input κ (r^2) r hκ (sq_nonneg r) hr ht htf hmain hfinal hrow hw
    ⟨samplingTable S e r Ds main final,y,P⟩ rfl tape

/-- The finite bound yields the geometric constant only under q < 1. -/
theorem build_sub_le_geometric (hq : κ*r^2 < 1) (P x y : Point d)
    (tape : Tape d (SamplingExecutable.build S e r Ds main final N).program) :
    ‖childPoint (run (SamplingExecutable.build S e r Ds main final N).program G
        ⟨(SamplingExecutable.build S e r Ds main final N).coefficient,x,P⟩ Env.empty tape) -
      childPoint (run (SamplingExecutable.build S e r Ds main final N).program G
        ⟨(SamplingExecutable.build S e r Ds main final N).coefficient,y,P⟩ Env.empty tape)‖ ≤
      (κ*r/(1-κ*r^2))*‖x-y‖ := by
  have hb := build_sub_le S e r Ds main final N G κ hm hr hκ hmain hfinal P x y tape
  have hs : ∑ j ∈ Finset.range (N+1), (κ*r^2)^j ≤ (1-κ*r^2)⁻¹ := by
    simpa using (geom_sum_Ico_le_of_lt_one (m := 0) (n := N+1)
      (mul_nonneg hκ (sq_nonneg r)) hq)
  calc
    _ ≤ κ*r*‖x-y‖*∑ j ∈ Finset.range (N+1), (κ*r^2)^j := hb
    _ ≤ κ*r*‖x-y‖*(1-κ*r^2)⁻¹ := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- All entering P and full residual tapes are retained in the finite ChildStable result. -/
theorem build_childStable :
    ChildStable (SamplingExecutable.build S e r Ds main final N).program
      (SamplingExecutable.build S e r Ds main final N).coefficient G
      (κ*r*∑ j ∈ Finset.range (N+1), (κ*r^2)^j) := by
  intro P x y z rest
  have hb := build_sub_le S e r Ds main final N G κ hm hr hκ hmain hfinal
    P x y (joinTape _ z rest)
  convert hb using 1
  ring

theorem build_childStable_geometric (hq : κ*r^2 < 1) :
    ChildStable (SamplingExecutable.build S e r Ds main final N).program
      (SamplingExecutable.build S e r Ds main final N).coefficient G (κ*r/(1-κ*r^2)) := by
  intro P x y z rest
  exact build_sub_le_geometric S e r Ds main final N G κ hm hr hκ hmain hfinal hq
    P x y (joinTape _ z rest)
end Actual

end AcceleratedLogConcave.Oracle.FixedTapeSampling
