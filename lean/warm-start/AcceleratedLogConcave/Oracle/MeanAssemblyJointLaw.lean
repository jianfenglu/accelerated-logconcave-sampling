import AcceleratedLogConcave.Oracle.MeanMainBatchCoupling
import AcceleratedLogConcave.Oracle.PrivateSamplingTapeProjections
import AcceleratedLogConcave.Conditional.TerminalChildrenParentFamily
import AcceleratedLogConcave.Probability.MixedResidualAbsorption

/-! The actual incoming source-mean assembly, averaged over its original
retained input and literal raw Gaussian occurrences. The original input is
retained through its exact reconstruction, never conditioned away. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Oracle.MeanAssemblyJointLaw
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open SourceMeanExecutable CanonicalTapeLaw CanonicalTapeMeasurability
open Conditional.GaussianAssembly
open AcceleratedLogConcave.Probability.MixedResidualAbsorption
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {m n a h d : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData)
    (N : ℕ)
local notation "host" => SourceMeanExecutable.program M nodes anchors seeds main final sampling N
local instance canonicalTapeSpace (d : ℕ) (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalResidualSpace (p : Prog c Γ τ) :
    MeasurableSpace (ResidualTape p) := residualSpace p

/-- These are precisely the setup draws after the private call and scale row. -/
def raw (ω : Tape d host) (i : Fin (m+1)) : Point d := (ω.2.2.2.2.1 i).1

def slot (i : Fin (m+1)) : GaussianSlot host :=
  .inr (.inr (.inr (.inr (.inl ⟨i,.inl PUnit.unit⟩))))

theorem slot_injective : Function.Injective (slot M nodes anchors seeds main final sampling N) := by
  intro i j hij
  exact congrArg Sigma.fst (Sum.inl.inj (Sum.inr.inj (Sum.inr.inj
    (Sum.inr.inj (Sum.inr.inj hij)))))

theorem raw_preserving (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d)) :
    MeasurePreserving (raw M nodes anchors seeds main final sampling N)
      (tapeLaw L host) (Measure.pi fun _ : Fin (m+1) => stdGaussian (Point d)) := by
  let f := fun z : GaussianSlot host → Point d =>
    fun j => z (slot M nodes anchors seeds main final sampling N j)
  have hm : Measurable f := by fun_prop
  have hsplit := CanonicalTapeFactorization.measurePreserving_splitTape L host
  let : IsProbabilityMeasure L.uniformDraw := L.uniform_probability
  let : IsProbabilityMeasure (residualLaw L.uniformDraw host) := residualLaw_probability L.uniformDraw host
  have hfst := measurePreserving_fst.comp hsplit
  have hsel : MeasurePreserving f (Measure.pi fun _ : GaussianSlot host => L.pointDraw)
      (Measure.pi fun _ : Fin (m+1) => stdGaussian (Point d)) := by
    refine ⟨hm, ?_⟩
    rw [hL]
    exact PrivateSamplingTapeProjections.pi_selection _ _
      (slot_injective M nodes anchors seeds main final sampling N)
  exact hsel.comp hfst

/-- The concrete coefficients have strict assembly slack, including m=0. -/
theorem assembly_mass : mass (SourceMeanExecutable.assembly M) < 1 := by
  have hw : ∑ i : Fin m, (Numerics.GaussLegendre.weight m i)^2 ≤ 1 := by
    by_cases hm : 0 < m
    · exact Conditional.TerminalChildrenParentFamily.sum_weight_sq_le_one hm
    · have : m = 0 := by omega
      subst m
      simp
  have hR : M.R^2 ≤ 1/4 := by nlinarith [M.R_pos, M.R_le_half]
  have hs : (Real.sqrt (3 : ℝ))^2 = 3 := Real.sq_sqrt (by norm_num)
  have he : mass (SourceMeanExecutable.assembly M) =
      1/4 + (M.R * Real.sqrt 3 / 4)^2 *
        ∑ i : Fin m, (Numerics.GaussLegendre.weight m i)^2 := by
    unfold mass SourceMeanExecutable.assembly
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ]
    rw [Finset.mul_sum]
    congr 1
    · norm_num
    · apply Finset.sum_congr rfl
      intro i _
      ring
  rw [he]
  have hb := mul_le_mul_of_nonneg_left hw (sq_nonneg (M.R * Real.sqrt 3 / 4))
  nlinarith

/-- Full active inventory plus the deterministic reserve. The first active
coordinate is G0; coordinate i.succ is the actual stored active-final Pi. -/
def assembled (z : Point d × Tape d host) : Option (Fin (m+1)) → Point d :=
  assemble (SourceMeanExecutable.assembly M)
    ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin (m+1)) => Point d)).symm
      (raw M nodes anchors seeds main final sampling N z.2,z.1))

theorem assembled_preserving (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d)) :
    MeasurePreserving (assembled M nodes anchors seeds main final sampling N)
      (L.pointDraw.prod (tapeLaw L host))
      (Measure.pi fun _ : Option (Fin (m+1)) => stdGaussian (Point d)) := by
  let : IsProbabilityMeasure L.pointDraw := L.point_probability
  let : IsProbabilityMeasure (tapeLaw L host) := tapeLaw_probability L host
  have hp := (MeasurePreserving.id L.pointDraw).prod
    (raw_preserving M nodes anchors seeds main final sampling N L hL)
  rw [hL] at hp ⊢
  exact (show MeasurePreserving
      (assemble (SourceMeanExecutable.assembly M) : _ → Option (Fin (m+1)) → Point d)
      (Measure.pi fun _ : Option (Fin (m+1)) => stdGaussian (Point d))
      (Measure.pi fun _ : Option (Fin (m+1)) => stdGaussian (Point d)) from
        ⟨measurable_assemble _, assemble_map_pi (assembly_mass M)⟩).comp
    (comparisonPack_preserving.comp hp)

theorem reconstructed_original (z : Point d × Tape d host) :
    reconstruct (SourceMeanExecutable.assembly M)
      (assembled M nodes anchors seeds main final sampling N z) = z.1 :=
  reconstruct_assemble (assembly_mass M) _

/-- Exact retained joint law. In particular the original P is correlated with
all active coordinates and reserve by reconstruction; it is not an extra
independent factor in the final retained coupling. -/
theorem original_assembled_law (L : PrimitiveLaws d)
    (hL : L.pointDraw = stdGaussian (Point d)) :
    (L.pointDraw.prod (tapeLaw L host)).map
      (fun z => (z.1,assembled M nodes anchors seeds main final sampling N z)) =
    (Measure.pi fun _ : Option (Fin (m+1)) => stdGaussian (Point d)).map
      (fun y => (reconstruct (SourceMeanExecutable.assembly M) y,y)) := by
  have hp := assembled_preserving M nodes anchors seeds main final sampling N L hL
  have hm : Measurable (fun y : Option (Fin (m+1)) → Point d =>
      (reconstruct (SourceMeanExecutable.assembly M) y,y)) := by
    dsimp [reconstruct]
    fun_prop
  rw [← hp.map_eq, Measure.map_map hm hp.measurable]
  congr 1
  funext z
  simp only [Function.comp_apply, reconstructed_original]

/-- Literal stored assembly arithmetic at the actual public table. -/
theorem literal_assembly_values (r σ Ds δ t w : ℝ) (P : Point d)
    (Z : Fin (m+1) → Point d) (i : Fin (m+1)) :
    MeanExecutablePrefix.assemblyValues
      (prefixSlot (a := a) main final sampling ∘ PrefixPublicTable.assemblySlot)
      (⟨SourceMeanExecutable.table M nodes anchors r σ Ds δ t w main final sampling,0,P⟩ : Inputs d _)
      P Z i = active (SourceMeanExecutable.assembly M) P Z i := by
  apply MeanExecutablePrefix.assemblyValues_eq_active
  · exact assembly_mass M
  · funext j
    simp only [Function.comp_apply, table_prefix, PrefixPublicTable.table_assembly]

end AcceleratedLogConcave.Oracle.MeanAssemblyJointLaw
