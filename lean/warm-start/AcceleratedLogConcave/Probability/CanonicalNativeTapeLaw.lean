import AcceleratedLogConcave.Oracle.SamplingCanonicalTapeLaw
import AcceleratedLogConcave.Probability.MixedResidualTape

/-! Agreement of the receiving canonical product semantics with the native
Gaussian/uniform interpreter semantics. No coordinates are removed. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Probability.CanonicalNativeTapeLaw
open Oracle Oracle.TapeLowering CanonicalTapeMeasurability CanonicalTapeLaw

/-- Actual primitive instructions: standard Gaussian points and closed-unit
uniform draws, with their proved probability normalization. -/
def primitiveLaws (d : ℕ) : PrimitiveLaws d where
  pointDraw := stdGaussian (Point d)
  uniformDraw := MixedResidualTape.uniformLaw
  point_probability := inferInstance
  uniform_probability := inferInstance

theorem instrSpace_eq (d : ℕ) (i : Instr c Γ τ) :
    instrSpace d i = MixedResidualTape.instrTapeMeasurableSpace d i := by
  cases i <;> rfl

theorem tapeSpace_eq (d : ℕ) (p : Prog c Γ τ) :
    tapeSpace d p = MixedResidualTape.tapeMeasurableSpace d p := by
  induction p with
  | ret r => rfl
  | step o i next ih =>
    change (instrSpace d i).prod (tapeSpace d next) =
      (MixedResidualTape.instrTapeMeasurableSpace d i).prod
        (MixedResidualTape.tapeMeasurableSpace d next)
    rw [instrSpace_eq, ih]
  | batch o children next ihc ihn =>
    change (@MeasurableSpace.pi _ _ (fun j => tapeSpace d (children j))).prod
      (tapeSpace d next) =
      (@MeasurableSpace.pi _ _ (fun j => MixedResidualTape.tapeMeasurableSpace d (children j))).prod
        (MixedResidualTape.tapeMeasurableSpace d next)
    rw [show (fun j => tapeSpace d (children j)) =
      (fun j => MixedResidualTape.tapeMeasurableSpace d (children j)) from funext ihc, ihn]

theorem instrLaw_heq (d : ℕ) (i : Instr c Γ τ) :
    HEq (CanonicalTapeLaw.instrLaw (primitiveLaws d) i) (MixedResidualTape.instrLaw d i) := by
  cases i <;> rfl

private theorem prod_heq {X Y : Type*} {a a' : MeasurableSpace X} {b b' : MeasurableSpace Y}
    (ha : a = a') (hb : b = b')
    (μ : @Measure X a) (μ' : @Measure X a') (ν : @Measure Y b) (ν' : @Measure Y b')
    (hμ : HEq μ μ') (hν : HEq ν ν') :
    HEq (@Measure.prod X Y a b μ ν) (@Measure.prod X Y a' b' μ' ν') := by
  cases ha
  cases hb
  cases eq_of_heq hμ
  cases eq_of_heq hν
  rfl

private theorem pi_heq {I : Type*} [Fintype I] {X : I → Type*}
    {a a' : ∀ i, MeasurableSpace (X i)} (ha : a = a')
    (μ : ∀ i, @Measure (X i) (a i)) (μ' : ∀ i, @Measure (X i) (a' i))
    (hμ : ∀ i, HEq (μ i) (μ' i)) :
    HEq (@Measure.pi I X _ a μ) (@Measure.pi I X _ a' μ') := by
  cases ha
  have he : μ = μ' := funext (fun i => eq_of_heq (hμ i))
  cases he
  rfl

theorem tapeLaw_heq (d : ℕ) (p : Prog c Γ τ) :
    HEq (CanonicalTapeLaw.tapeLaw (primitiveLaws d) p) (MixedResidualTape.tapeLaw d p) := by
  induction p with
  | ret r => rfl
  | step o i next ih =>
    simp only [CanonicalTapeLaw.tapeLaw, MixedResidualTape.tapeLaw]
    exact prod_heq (instrSpace_eq d i) (tapeSpace_eq d next) _ _ _ _ (instrLaw_heq d i) ih
  | batch o children next ihc ihn =>
    simp only [CanonicalTapeLaw.tapeLaw, MixedResidualTape.tapeLaw]
    apply prod_heq _ (tapeSpace_eq d next) _ _ _ _ _ ihn
    · change @MeasurableSpace.pi _ _ (fun j => tapeSpace d (children j)) =
        @MeasurableSpace.pi _ _ (fun j => MixedResidualTape.tapeMeasurableSpace d (children j))
      rw [show (fun j => tapeSpace d (children j)) =
        (fun j => MixedResidualTape.tapeMeasurableSpace d (children j)) from
        funext (fun j => tapeSpace_eq d (children j))]
    · exact pi_heq (funext (fun j => tapeSpace_eq d (children j))) _ _ ihc

/-- Translate by the identity of the SAME tape carrier, not a resampling map. -/
def nativeLaw (d : ℕ) (p : Prog c Γ τ) : Measure (Tape d p) :=
  @Measure.map (Tape d p) (Tape d p) (tapeSpace d p)
    (MixedResidualTape.tapeMeasurableSpace d p) id (CanonicalTapeLaw.tapeLaw (primitiveLaws d) p)

private theorem map_id_of_heq {X : Type*} {a a' : MeasurableSpace X}
    (ha : a = a') (μ : @Measure X a) (ν : @Measure X a') (hμ : HEq μ ν) :
    @Measure.map X X a a' id μ = ν := by
  cases ha
  rw [eq_of_heq hμ]
  exact Measure.map_id

/-- Exact equality of full independent-instruction laws, Gaussian and uniform
coordinates and every structural unit included. -/
theorem nativeLaw_eq (d : ℕ) (p : Prog c Γ τ) :
    nativeLaw d p = MixedResidualTape.tapeLaw d p :=
  map_id_of_heq (tapeSpace_eq d p) _ _ (tapeLaw_heq d p)

/-- The identity of the existing full tape carries the canonical law to the
native execution law. This allows the causal producer to feed actual execution. -/
theorem identity_preserving (d : ℕ) (p : Prog c Γ τ) :
    @MeasurePreserving (Tape d p) (Tape d p) (tapeSpace d p)
      (MixedResidualTape.tapeMeasurableSpace d p) id
      (CanonicalTapeLaw.tapeLaw (primitiveLaws d) p) (MixedResidualTape.tapeLaw d p) := by
  have hm : @Measurable (Tape d p) (Tape d p) (tapeSpace d p)
      (MixedResidualTape.tapeMeasurableSpace d p) id := by
    rw [tapeSpace_eq]
    exact measurable_id
  exact @MeasurePreserving.mk _ _ (tapeSpace d p)
    (MixedResidualTape.tapeMeasurableSpace d p) id _ _ hm (nativeLaw_eq d p)

/-- The converse identity transports actual execution to the canonical cut
semantics. It changes only the measurable-space presentation. -/
theorem native_identity_preserving (d : ℕ) (p : Prog c Γ τ) :
    @MeasurePreserving (Tape d p) (Tape d p)
      (MixedResidualTape.tapeMeasurableSpace d p) (tapeSpace d p) id
      (MixedResidualTape.tapeLaw d p) (CanonicalTapeLaw.tapeLaw (primitiveLaws d) p) := by
  have hm : @Measurable (Tape d p) (Tape d p)
      (MixedResidualTape.tapeMeasurableSpace d p) (tapeSpace d p) id := by
    rw [tapeSpace_eq]
    exact measurable_id
  exact @MeasurePreserving.mk _ _ (MixedResidualTape.tapeMeasurableSpace d p)
    (tapeSpace d p) id _ _ hm
      (map_id_of_heq (tapeSpace_eq d p).symm _ _ (tapeLaw_heq d p).symm)

private theorem map_eq_of_heq {X Y : Type*} {a a' : MeasurableSpace X}
    [MeasurableSpace Y] (ha : a = a') (μ : @Measure X a) (ν : @Measure X a')
    (hμ : HEq μ ν) (f : X → Y) :
    @Measure.map X Y a _ f μ = @Measure.map X Y a' _ f ν := by
  cases ha
  rw [eq_of_heq hμ]

/-- Any readout has the identical law under the native and canonical
presentations. This is equality of the full measures, not a marginal shortcut. -/
theorem map_native_eq {Y : Type*} [MeasurableSpace Y] (d : ℕ) (p : Prog c Γ τ)
    (f : Tape d p → Y) :
    @Measure.map (Tape d p) Y (MixedResidualTape.tapeMeasurableSpace d p) _ f
      (MixedResidualTape.tapeLaw d p) =
    @Measure.map (Tape d p) Y (tapeSpace d p) _ f
      (CanonicalTapeLaw.tapeLaw (primitiveLaws d) p) :=
  map_eq_of_heq (tapeSpace_eq d p).symm _ _ (tapeLaw_heq d p).symm f

end AcceleratedLogConcave.Probability.CanonicalNativeTapeLaw
