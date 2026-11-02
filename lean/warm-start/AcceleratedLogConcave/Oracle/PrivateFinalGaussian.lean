import AcceleratedLogConcave.Oracle.ResidualGaussianRecombination
import AcceleratedLogConcave.Oracle.PrivateSamplingNoiseBudget
import AcceleratedLogConcave.Oracle.PrivateFinalCoupling

/-! Exact Gaussian aggregation of returned final references and the actual
fresh residual. This is conditional only on a proved joint product law; the
chronological coupling supplies that law without redrawing any source tape. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix
namespace AcceleratedLogConcave.Oracle.PrivateFinalGaussian
open Numerics.AffineGraph SourceExecutableTables
variable {d : ℕ}

private theorem weighted_preserving {I : Type*} [Fintype I]
    (w : I → ℝ) {s : ℝ} (hs : s ≠ 0) (hw : ∑ i, w i ^ 2 = s^2) :
    MeasurePreserving (fun z : I → Point d => ∑ i, w i • z i)
      (Measure.pi (fun _ : I => stdGaussian (Point d)))
      ((stdGaussian (Point d)).map (fun z => s • z)) := by
  let R : Matrix Unit I ℝ := fun _ i => w i / s
  have hR : R * R.transpose = 1 := by
    ext i j
    cases i; cases j
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,ite_true]
    change (∑ i, (w i/s)*(w i/s)) = 1
    simp_rw [← sq,div_pow]
    rw [← Finset.sum_div,hw,div_self (pow_ne_zero _ hs)]
  have hp := (measurePreserving_eval (fun _ : Unit => stdGaussian (Point d)) ()).comp
    (ResidualGaussianRecombination.matrix_preserving (d := d) R hR)
  have hscale : MeasurePreserving (fun z : Point d => s • z) (stdGaussian (Point d))
      ((stdGaussian (Point d)).map (fun z => s • z)) := ⟨by fun_prop,rfl⟩
  have he : (fun z : I → Point d => ∑ i, w i • z i) =
      (fun z : I → Point d => s • (∑ i, R () i • z i)) := by
    funext z
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul]
    congr 1
    dsimp only [R]
    field_simp
  rw [he]
  exact hscale.comp hp

variable {m n : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node) (r : ℝ)

def preNoise (z : (Fin n → Point d) × Point d) : Point d :=
  (∑ i, samplingFinalWeight S e r i • (samplingFinalWidth S r • z.1 i)) +
    samplingBeta S e r • z.2

/-- The whole returned-reference vector and fresh actual residual aggregate
to variance tau²/2, with no assumptions on individual-coordinate marginals. -/
theorem preNoise_preserving (hm : 0 < m) (hr : 0 < r) :
    MeasurePreserving (preNoise (d := d) S e r)
      ((Measure.pi (fun _ : Fin n => stdGaussian (Point d))).prod (stdGaussian (Point d)))
      ((stdGaussian (Point d)).map (fun z => (S.τ/Real.sqrt 2) • z)) := by
  let w : Fin n ⊕ Unit → ℝ := Sum.elim
    (fun i => samplingFinalWeight S e r i * samplingFinalWidth S r)
    (fun _ => samplingBeta S e r)
  have hs : S.τ/Real.sqrt 2 ≠ 0 := ne_of_gt (div_pos (S.R_pos.trans_le S.R_le_τ) (by positivity))
  have hw : ∑ i, w i ^ 2 = (S.τ/Real.sqrt 2)^2 := by
    simp only [Fintype.sum_sum_type,w,Sum.elim_inl,Sum.elim_inr,Fintype.sum_unique,mul_pow]
    rw [PrivateSamplingNoiseBudget.beta_sq S e r hm hr]
    ring
  have hunit := (measurePreserving_funUnique (stdGaussian (Point d)) Unit).symm
    (MeasurableEquiv.funUnique Unit (Point d))
  have hsplit := (measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin n ⊕ Unit => stdGaussian (Point d))).comp
    ((MeasurePreserving.id (Measure.pi (fun _ : Fin n => stdGaussian (Point d)))).prod hunit)
  have hp := (weighted_preserving w hs hw).comp hsplit
  convert hp using 1
  funext z
  simp only [preNoise,Function.comp_def,Fintype.sum_sum_type,w,smul_smul,
    Sum.elim_inl,Sum.elim_inr,Fintype.sum_unique]
  rfl

/-- Arbitrary coarse history is retained as a joint factor; this does not
assert independence after additionally conditioning on the original parent P. -/
theorem coarse_preNoise_preserving {H : Type*} [MeasurableSpace H]
    (ν : Measure H) [SFinite ν] (hm : 0 < m) (hr : 0 < r) :
    MeasurePreserving (fun z : H × ((Fin n → Point d) × Point d) =>
      (z.1,preNoise S e r z.2))
      (ν.prod ((Measure.pi (fun _ : Fin n => stdGaussian (Point d))).prod (stdGaussian (Point d))))
      (ν.prod ((stdGaussian (Point d)).map (fun z => (S.τ/Real.sqrt 2) • z))) :=
  (MeasurePreserving.id ν).prod (preNoise_preserving S e r hm hr)

section LiteralSuffix
open AffineLowering TapeLowering NoisyLayer SourceMeanLayer
open CanonicalTapeLaw CanonicalTapeMeasurability
variable (main final : Fin n → ExecutableData) (N : ℕ)
  {Γ : Ctx} (direct : Ref Γ .point)
local instance {c : ℕ} {Δ : Ctx} {τ : Ty} (p : Prog c Δ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p

/-- The final residual and reserve are the two literal instructions in the
unread suffix, with their complete joint law; the output-row tape is retained
in the domain of this projection. -/
theorem suffix_residual_reserve (L : PrimitiveLaws d)
    (hL : L.pointDraw = stdGaussian (Point d)) :
    MeasurePreserving (fun ω : Tape d (PrivateFinalCoupling.suffix main final N direct) =>
      ((show Point d from ω.1),(show Point d from ω.2.1)))
      (tapeLaw L (PrivateFinalCoupling.suffix main final N direct))
      ((stdGaussian (Point d)).prod (stdGaussian (Point d))) := by
  let cfg := samplingConfig main final N
  let row := affineRow [] (.there (.there (RefMap.shiftMany n direct)))
    ((List.ofFn fun i => (cfg.rowWeight i,.there (.there (batchRef i)))) ++
      [(cfg.beta,.there .here),(cfg.reserve,.here)])
  let : IsProbabilityMeasure L.pointDraw := L.point_probability
  let : IsProbabilityMeasure (tapeLaw L row) := tapeLaw_probability L row
  have hp := (MeasurePreserving.id L.pointDraw).prod
    (measurePreserving_fst (μ := L.pointDraw) (ν := tapeLaw L row))
  rw [← hL]
  exact hp
end LiteralSuffix

end AcceleratedLogConcave.Oracle.PrivateFinalGaussian
