import AcceleratedLogConcave.Oracle.MeanChronologicalLaws
import AcceleratedLogConcave.Oracle.MeanFinalAssemblyReadout

/-! Joint Gaussian comparison laws of the actual finite mean-main coupling.
The static coarse host retains incoming correlations and the original parent.
Only the complete unread tape is a fresh product factor. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Oracle.MeanChronologicalSupport
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RecursiveMeanProgram RecursiveMeanContinuation SourceMeanLayer SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateCausalLayer PrivateCausalAdvance MeanChronologicalCoupling
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable {m n a h d : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData) (N : ℕ)
  (r Ds : ℝ) (hr : 0<r) (hDs : 0<Ds)
  (hmass : ∀ i,CovarianceSetup.shiftSq (main i).shiftVector≤Ds^2)
  {A : Type*} [MeasurableSpace A]
  (L : PrimitiveLaws d) (hL : L.pointDraw=stdGaussian (Point d))
  (x P referencePosition : A → Point d) (hx : Measurable x) (hP : Measurable P)
  (hreference : Measurable referencePosition)
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (σ : ℝ) (hσ : 0<σ) (hsmall : r^2*ell≤1/2) (δ t w : ℝ)
local instance : MeasurableSpace
    (Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N)) := prefixSpace d _


def sourceView (z : History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)) := (z.1.1,z.2)

theorem sourceView_measurable : Measurable (sourceView (d := d) (A := A) M nodes anchors seeds main final sampling N) :=
  measurable_fst.fst.prodMk measurable_snd

def initialView (z : A × Tape d (Host M nodes anchors seeds main final sampling N)) : Coarse (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N) :=
  ((z.1,(split (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N) z.2).1),z.2)

include L in
theorem initialView_measurable : Measurable (initialView (d := d) (A := A) M nodes anchors seeds main final sampling N) :=
  (measurable_fst.prodMk (((measurePreserving_split L (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N)).measurable.comp
    (measurable_snd : Measurable (Prod.snd : A × Tape d (Host M nodes anchors seeds main final sampling N) → _))).fst)).prodMk measurable_snd

theorem step_sourceView (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining) (k : Fin N)
    (J : FreshChildBatchCoupling.Lower L (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) :
    (MeanChronologicalCoupling.step M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w s hs k J).map (sourceView M nodes anchors seeds main final sampling N)=
      Kernel.deterministic (sourceView M nodes anchors seeds main final sampling N) (sourceView_measurable M nodes anchors seeds main final sampling N) := by
  rw [MeanChronologicalCoupling.step,← Kernel.map_comp_right _
    (record_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass L σ δ t w s hs k) (sourceView_measurable M nodes anchors seeds main final sampling N)]
  change (adjoin M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs J).map
    ((sourceView M nodes anchors seeds main final sampling N) ∘ Prod.fst)=_
  rw [Kernel.map_comp_right _ measurable_fst (sourceView_measurable M nodes anchors seeds main final sampling N),
    ← Kernel.fst_eq,adjoin_original,Kernel.id_map]

variable (Jall : ∀ (k : ℕ) (hk : k<N),FreshChildBatchCoupling.Lower L
  (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass (stage M nodes anchors seeds main final sampling N k hk.le).1 (stage_positive M nodes anchors seeds main final sampling N k hk)))

theorem iteration_sourceView (k : ℕ) (hk : k≤N) :
    (iteration M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall k hk).map (sourceView M nodes anchors seeds main final sampling N)=
      Kernel.deterministic (sourceView M nodes anchors seeds main final sampling N) (sourceView_measurable M nodes anchors seeds main final sampling N) := by
  induction k with
  | zero => exact Kernel.id_map (sourceView_measurable M nodes anchors seeds main final sampling N)
  | succ k ih =>
    rw [iteration,Kernel.map_comp,step_sourceView,Kernel.deterministic_comp_eq_map]
    exact ih (by omega)

/-- The static coarse prefix is the one on the same original full tape.
This is proved for the constructed kernel, not inferred from a marginal law. -/
theorem kernel_sourceView : (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall).map (sourceView M nodes anchors seeds main final sampling N)=
    Kernel.deterministic (initialView M nodes anchors seeds main final sampling N) (initialView_measurable M nodes anchors seeds main final sampling N L) := by
  rw [kernel,Kernel.map_comp,iteration_sourceView,Kernel.deterministic_comp_eq_map,
    Kernel.deterministic_map (MeanInitialComparison.prepare_measurable M nodes anchors seeds main final sampling N L) (sourceView_measurable M nodes anchors seeds main final sampling N)]
  congr 1

theorem kernel_readout_ae {E : Type*} [MeasurableSpace E] [MeasurableEq E] (f : Coarse (d := d) M nodes anchors seeds main final sampling N A → E) (hf : Measurable f)
    (g : A × Tape d (Host M nodes anchors seeds main final sampling N) → E) (hg : Measurable g)
    (heq : ∀ z,f (initialView M nodes anchors seeds main final sampling N z).1=g z)
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) :
    ∀ᵐ z ∂kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ∘ₘ ρ,f z.1.1=g (z.1.1.1,z.2) := by
  let valid : Coarse (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N) → Prop :=
    fun y => f y.1=g (y.1.1,y.2)
  have hv : MeasurableSet {y | valid y} :=
    measurableSet_eq_fun (hf.comp measurable_fst) (hg.comp (measurable_fst.fst.prodMk measurable_snd))
  have hmap : (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ∘ₘ ρ).map (sourceView M nodes anchors seeds main final sampling N)=ρ.map (initialView M nodes anchors seeds main final sampling N) := by
    rw [Measure.map_comp _ _ (sourceView_measurable M nodes anchors seeds main final sampling N),kernel_sourceView,Measure.deterministic_comp_eq_map]
  have hi : ∀ᵐ y ∂ρ.map (initialView M nodes anchors seeds main final sampling N),valid y :=
    (ae_map_iff (initialView_measurable M nodes anchors seeds main final sampling N L).aemeasurable hv).2 (ae_of_all ρ heq)
  rw [← hmap] at hi
  exact ae_of_ae_map (sourceView_measurable M nodes anchors seeds main final sampling N).aemeasurable hi

end AcceleratedLogConcave.Oracle.MeanChronologicalSupport
