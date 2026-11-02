import AcceleratedLogConcave.Probability.MixedResidualCompiler
import AcceleratedLogConcave.Conditional.GaussianAssembly

/-! Full mixed Gaussian/residual pushforwards. Gaussian completion acts only on the
Gaussian coordinates. The auxiliary factor may retain arbitrary saved inputs jointly
with all actual uniform/unit residual coordinates. Its independence from the entire
completion vector is explicit in the product input law; no conditional independence
from a retained momentum or a tape-selected clock is asserted. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace AcceleratedLogConcave.Probability.MixedResidualAbsorption
open Conditional.GaussianAssembly Oracle Oracle.TapeLowering MixedResidualTape

variable {ι E R : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace R]

lemma measurable_assemble (a : ι → ℝ) :
    Measurable (assemble a : (Option ι → E) → Option ι → E) := by
  apply Measurable.of_eval
  intro i
  cases i <;> dsimp [assemble, active, Conditional.GaussianAssembly.residual, noiseSum] <;> fun_prop

/-- The full assembly preserves the joint law, tensor the identity on arbitrary residual data. -/
theorem assemble_preserving {a : ι → ℝ} (ha : mass a < 1)
    (ν : Measure R) [SFinite ν] :
    MeasurePreserving (fun xr : (Option ι → E) × R => (assemble a xr.1, xr.2))
      ((Measure.pi (fun _ : Option ι => stdGaussian E)).prod ν)
      ((Measure.pi (fun _ : Option ι => stdGaussian E)).prod ν) :=
  (show MeasurePreserving (assemble a : (Option ι → E) → Option ι → E)
      (Measure.pi (fun _ : Option ι => stdGaussian E))
      (Measure.pi (fun _ : Option ι => stdGaussian E)) from
        ⟨measurable_assemble a, assemble_map_pi ha⟩).prod (MeasurePreserving.id ν)

/-- Original designated momentum as a function of all assembled Gaussian coordinates. -/
def reconstruct (a : ι → ℝ) (y : Option ι → E) : E :=
  (∑ i, a i • y (some i)) + reserve a • y none

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma reconstruct_assemble {a : ι → ℝ} (ha : mass a < 1) (x : Option ι → E) :
    reconstruct a (assemble a x) = x none :=
  (residual_reconstruction ha (x none) (fun i => x (some i))).symm

/-- Original momentum is retained, with its exact correlated joint law. This is deliberately
not a product law conditional on that momentum. The arbitrary factor is kept in full. -/
theorem assemble_retained_original_law {a : ι → ℝ} (ha : mass a < 1)
    (ν : Measure R) [SFinite ν] :
    (((Measure.pi (fun _ : Option ι => stdGaussian E)).prod ν).map
      (fun xr => (xr.1 none, assemble a xr.1, xr.2))) =
    (((Measure.pi (fun _ : Option ι => stdGaussian E)).prod ν).map
      (fun yr => (reconstruct a yr.1, yr.1, yr.2))) := by
  have hm : Measurable (fun yr : (Option ι → E) × R =>
      (reconstruct a yr.1, yr.1, yr.2)) := by
    dsimp [reconstruct]
    fun_prop
  have h := congrArg (fun μ : Measure ((Option ι → E) × R) =>
    μ.map (fun yr => (reconstruct a yr.1, yr.1, yr.2))) (assemble_preserving ha ν).map_eq
  rw [Measure.map_map hm (assemble_preserving ha ν).measurable] at h
  change (((Measure.pi (fun _ : Option ι => stdGaussian E)).prod ν).map
    (fun xr => (reconstruct a (assemble a xr.1), assemble a xr.1, xr.2))) = _ at h
  simpa only [reconstruct_assemble ha] using h

lemma mass_neg (a : ι → ℝ) : mass (-a) = mass a := by simp [mass]

/-- Literal Gaussian completion for the child's negative comparison shift. -/
def absorbed (a : ι → ℝ) (x : Option ι → E) (i : ι) : E :=
  active (-a) (x none) (fun j => x (some j)) i

lemma measurable_absorbed (a : ι → ℝ) :
    Measurable (absorbed a : (Option ι → E) → ι → E) := by
  apply Measurable.of_eval
  intro i
  dsimp [absorbed, active, noiseSum]
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The covariance completion uses the actual positive matrix square root. -/
lemma absorbed_eq_sqrt [DecidableEq ι] {a : ι → ℝ} (ha : mass a < 1)
    (x : Option ι → E) (i : ι) :
    absorbed a x i =
      (∑ j, (CFC.sqrt (1 - Matrix.vecMulVec a a)) i j • x (some j)) - a i • x none := by
  have hn : mass (-a) < 1 := by simpa only [mass_neg] using ha
  rw [absorbed, active_eq_sqrt_sum hn]
  have hv : Matrix.vecMulVec (-a) (-a) = Matrix.vecMulVec a a := by
    ext j k
    simp
  rw [hv]
  simp only [Pi.neg_apply, neg_smul]
  abel

/-- The whole completed Gaussian block is standard jointly. -/
theorem absorbed_preserving {a : ι → ℝ} (ha : mass a < 1) :
    MeasurePreserving (absorbed a : (Option ι → E) → ι → E)
      (Measure.pi (fun _ : Option ι => stdGaussian E))
      (Measure.pi (fun _ : ι => stdGaussian E)) := by
  have hn : mass (-a) < 1 := by simpa only [mass_neg] using ha
  have he : MeasurePreserving
      (MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => E)).symm
      ((Measure.pi (fun _ : ι => stdGaussian E)).prod (stdGaussian E))
      (Measure.pi (fun _ : Option ι => stdGaussian E)) :=
    ⟨(MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => E)).symm.measurable,
      Measure.pi_map_piOptionEquivProd (fun _ : Option ι => stdGaussian E)⟩
  have hp := (measurePreserving_fst (μ := Measure.pi (fun _ : ι => stdGaussian E))
    (ν := stdGaussian E)).comp he.symm
  exact hp.comp ⟨measurable_assemble (-a), assemble_map_pi hn⟩

omit [BorelSpace E] in
/-- Pack a literal independent comparison input and raw Gaussian inventory. -/
theorem comparisonPack_preserving :
    MeasurePreserving
      (fun qz : E × (ι → E) => (MeasurableEquiv.piOptionEquivProd
        (fun _ : Option ι => E)).symm (qz.2,qz.1))
      ((stdGaussian E).prod (Measure.pi (fun _ : ι => stdGaussian E)))
      (Measure.pi (fun _ : Option ι => stdGaussian E)) :=
  (show MeasurePreserving
    (MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => E)).symm
    ((Measure.pi (fun _ : ι => stdGaussian E)).prod (stdGaussian E))
    (Measure.pi (fun _ : Option ι => stdGaussian E)) from
      ⟨(MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => E)).symm.measurable,
        Measure.pi_map_piOptionEquivProd (fun _ : Option ι => stdGaussian E)⟩).comp
    Measure.measurePreserving_swap

/-- Full comparison completion with an arbitrary retained residual/saved factor. -/
theorem comparisonMixed_preserving {a : ι → ℝ} (ha : mass a < 1)
    (ν : Measure R) [SFinite ν] :
    MeasurePreserving (fun qzr : E × ((ι → E) × R) =>
      (absorbed a ((MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => E)).symm
        (qzr.2.1,qzr.1)),qzr.2.2))
      ((stdGaussian E).prod ((Measure.pi (fun _ : ι => stdGaussian E)).prod ν))
      ((Measure.pi (fun _ : ι => stdGaussian E)).prod ν) :=
  ((absorbed_preserving ha).prod (MeasurePreserving.id ν)).comp
    ((comparisonPack_preserving.prod (MeasurePreserving.id ν)).comp
      (measurePreserving_prodAssoc (stdGaussian E)
        (Measure.pi (fun _ : ι => stdGaussian E)) ν).symm)

/-- Joint completion law, retaining every residual and saved coordinate in an arbitrary factor. -/
theorem absorbed_full_law {a : ι → ℝ} (ha : mass a < 1)
    (ν : Measure R) [SFinite ν] :
    (((Measure.pi (fun _ : Option ι => stdGaussian E)).prod ν).map
      (fun xr => (absorbed a xr.1, xr.2))) =
      (Measure.pi (fun _ : ι => stdGaussian E)).prod ν :=
  ((absorbed_preserving ha).prod (MeasurePreserving.id ν)).map_eq

/-- Actual `ResidualTape` specialization. The law retains all uniform and unit leaves. -/
theorem absorbed_actual_residual_law {c : ℕ} {Γ : Ctx} {τ : Ty}
    (p : Prog c Γ τ) {a : GaussianSlot p → ℝ} (ha : mass a < 1) (d : ℕ) :
    (((Measure.pi (fun _ : Option (GaussianSlot p) => stdGaussian (Point d))).prod
      (residualLaw p)).map (fun xr => (absorbed a xr.1, xr.2))) =
      (Measure.pi (fun _ : GaussianSlot p => stdGaussian (Point d))).prod (residualLaw p) :=
  absorbed_full_law ha (residualLaw p)

/-- Literal full absorbed source tape from an actual compiled raw tape. -/
def absorbedCompiledTape {c : ℕ} {τ : Ty} {n d : ℕ}
    (p : Program c τ) (e : GaussianSlot p ≃ Fin n) (seedOrigin : Fin n → Origin)
    (a : Fin n → ℝ) (qw : Point d × Tape d (compileWith p e seedOrigin)) : Tape d p :=
  let data := unpackCompiledTape p e seedOrigin qw.2
  joinTape p (fun s => absorbed a
    ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin n) => Point d)).symm
      (data.1,qw.1)) (e s)) data.2

/-- The completed source tape is literally the actual positive-root auxiliary
transform minus the comparison shift, with the same actual residual coordinates. -/
theorem absorbedCompiledTape_eq_literal {c : ℕ} {τ : Ty} {n d : ℕ}
    (p : Program c τ) (e : GaussianSlot p ≃ Fin n) (seedOrigin : Fin n → Origin)
    {a : Fin n → ℝ} (ha : mass a < 1)
    (qw : Point d × Tape d (compileWith p e seedOrigin)) :
    absorbedCompiledTape p e seedOrigin a qw =
      let data := unpackCompiledTape p e seedOrigin qw.2
      joinTape p (fun s =>
        transformedGaussian (CFC.sqrt (1 - Matrix.vecMulVec a a) : Matrix (Fin n) (Fin n) ℝ) data.1 (e s) -
          a (e s) • qw.1) data.2 := by
  dsimp only [absorbedCompiledTape]
  apply congrArg (fun z => joinTape p z (unpackCompiledTape p e seedOrigin qw.2).2)
  funext s
  simpa only [pack_input_apply, transformedGaussian, Option.elim_some, Option.elim_none] using
    absorbed_eq_sqrt ha
      ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin n) => Point d)).symm
        ((unpackCompiledTape p e seedOrigin qw.2).1,qw.1)) (e s)

/-- The full compiled-tape sampling law becomes the actual full source law after
Gaussian absorption. The actual residual tape is retained unchanged. This uses
independence of the comparison input and all compiled raw coordinates explicitly. -/
theorem absorbedCompiledTape_preserving {c : ℕ} {τ : Ty} {n : ℕ}
    (d : ℕ) (p : Program c τ) (e : GaussianSlot p ≃ Fin n)
    (seedOrigin : Fin n → Origin) {a : Fin n → ℝ} (ha : mass a < 1) :
    MeasurePreserving (absorbedCompiledTape p e seedOrigin a)
      ((stdGaussian (Point d)).prod (tapeLaw d (compileWith p e seedOrigin)))
      (tapeLaw d p) :=
  (enumeratedJoin_preserving d p e).comp
    ((comparisonMixed_preserving ha (residualLaw p)).comp
      ((MeasurePreserving.id (stdGaussian (Point d))).prod
        (unpackCompiledTape_preserving d p e seedOrigin)))

/-- All supplied saved inputs can be retained, jointly with the absorbed source
tape, when the stated full raw input law makes them independent of completion. -/
theorem absorbedCompiledTape_saved_preserving {c : ℕ} {τ : Ty} {n : ℕ}
    (d : ℕ) (p : Program c τ) (e : GaussianSlot p ≃ Fin n)
    (seedOrigin : Fin n → Origin) {a : Fin n → ℝ} (ha : mass a < 1)
    (ν : Measure R) [SFinite ν] :
    MeasurePreserving
      (fun qs : (Point d × Tape d (compileWith p e seedOrigin)) × R =>
        (absorbedCompiledTape p e seedOrigin a qs.1,qs.2))
      (((stdGaussian (Point d)).prod (tapeLaw d (compileWith p e seedOrigin))).prod ν)
      ((tapeLaw d p).prod ν) :=
  (absorbedCompiledTape_preserving d p e seedOrigin ha).prod (MeasurePreserving.id ν)

end AcceleratedLogConcave.Probability.MixedResidualAbsorption
