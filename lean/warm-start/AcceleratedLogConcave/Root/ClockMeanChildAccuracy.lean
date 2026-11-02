import AcceleratedLogConcave.Oracle.PrescribedRetainedFullAccuracy
import AcceleratedLogConcave.Root.CubicOuterMainStability
import AcceleratedLogConcave.Root.ClockMainWorkBounds
import AcceleratedLogConcave.Root.ClockRetainedFinalSplice

/-! Actual fixed-clock mean children inherit retained accuracy from the full
source precision induction. Original-potential curvature, the literal clock
inventory and scheduled physical scales supply all root guards internally. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace AcceleratedLogConcave.Root.ClockMeanChildAccuracy
open Oracle Numerics Numerics.AffineGraph RecursiveSize RecursiveCall
open CubicExecutableWorkShift PrescribedRetainedQuantitativeInduction
open RecursiveRadiusFamily
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := CanonicalTapeMeasurability.tapeSpace d p
variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : MeanSourceScalarAbsorption.threshold P≤P.y)
local notation "privateHy" => MeanSourceScalarAbsorption.private_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
local notation "baseHy" => PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) privateHy
local notation "hR" => PrescribedRetainedCoupling.radiusGuard P hK hc hsmall hC privateHy
local notation "src" => source P hR
local notation "nr" => ClockNoisyLayer.N P
local notation "mainState" => OuterMainStability.mainState P nr
local notation "finalState" => FinalMeanScheduledData.state P

include hC in
/-- The actual clock inventory satisfies the source outer-width payment. -/
theorem inventory :
    (nr:ℝ)≤P.Csch*128*((P.K:ℝ)+4)*(Nat.ceil (Real.exp (P.y/128)):ℝ) := by
  change (ClockCollocation.count P.delta P.K:ℝ)≤_
  rw [ClockMainWorkBounds.inventory_literal P]
  push_cast
  have h0 : 0≤128*((P.K:ℝ)+4)*(Nat.ceil (Real.exp (P.y/128)):ℝ) := by positivity
  nlinarith

include hK hc hsmall hC hy in
/-- Positivity and both main-root scalar caps are paid at the literal count. -/
theorem main_caps (clock : ClockLaw.Clock) (i : ClockNoisyLayer.Index P) :
    0<(mainState i clock).radius ∧ 0<(mainState i clock).width ∧
      P.delta*(mainState i clock).radius^2≤P.delta ∧
      P.delta*((mainState i clock).radius/(mainState i clock).width)≤P.delta := by
  have h := CubicOuterMainStability.initial_main_certificate P hK hc hsmall hC baseHy
    (ClockCollocation.count_pos P.delta_pos P.K) i clock (inventory P hC)
  rcases h with ⟨hr,hσ,hsize⟩
  exact ⟨hr,hσ,by simpa only [SizeBound,Real.rpow_one,one_mul,mul_one] using hsize⟩

include hK hc hsmall hC hy in
/-- The same physical source band also gives the main radius cap one. -/
theorem main_radius_le_one (clock : ClockLaw.Clock) (i : ClockNoisyLayer.Index P) :
    (mainState i clock).radius≤1 := by
  have h := main_caps P hK hc hsmall hC hy clock i
  have hs : (mainState i clock).radius^2≤1 := (mul_le_mul_iff_right₀ P.delta_pos).mp (by simpa only [mul_one,one_mul,mul_comm] using h.2.2.1)
  nlinarith [h.1]

include hK hc hsmall hC hy in
/-- Actual active-final roots have their own final width and the same caps. -/
theorem final_caps (clock : ClockLaw.Clock) (i : ClockNoisyLayer.Index P) :
    0<(finalState i clock).radius ∧ 0<(finalState i clock).width ∧
      P.delta*(finalState i clock).radius^2≤P.delta ∧
      P.delta*((finalState i clock).radius/(finalState i clock).width)≤P.delta := by
  have hpos := FinalMeanScheduledData.root_positive P i clock
  have hs := FinalMeanScheduledData.initial_size P hK hc hsmall hC baseHy i clock
  change SizeBound P.delta P.delta 1 1 _ _ at hs
  exact ⟨hpos.1,hpos.2,by simpa only [SizeBound,Real.rpow_one,one_mul,mul_one] using hs⟩

include hK hc hsmall hC hy in
/-- The actual final radius is at most one, independently of its final width. -/
theorem final_radius_le_one (clock : ClockLaw.Clock) (i : ClockNoisyLayer.Index P) :
    (finalState i clock).radius≤1 := by
  have h := final_caps P hK hc hsmall hC hy clock i
  have hs : (finalState i clock).radius^2≤1 := (mul_le_mul_iff_right₀ P.delta_pos).mp (by simpa only [mul_one,one_mul,mul_comm] using h.2.2.1)
  nlinarith [h.1]

variable {d : ℕ} {V : Point d→ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
local notation "pot" => scaledPotential V (Real.sqrt P.delta)

include hV hlo in
/-- Original convexity supplies the normalized physical-potential lower Hessian. -/
theorem scaled_hessian_nonneg : ∀ z v,0≤fderiv ℝ (fderiv ℝ pot) z v v :=
  physicalPotential_hessian_nonneg hV hlo P.delta_pos.le

include hV hup in
/-- The literal sqrt(delta) adapter gives curvature delta, with no extra analytic input. -/
theorem scaled_hessian_upper : ∀ z v,fderiv ℝ (fderiv ℝ pot) z v v≤P.delta*‖v‖^2 :=
  physicalPotential_hessian_upper hV hup P.delta_pos.le

local notation "Hlo" => scaled_hessian_nonneg P hV hlo
local notation "Hup" => scaled_hessian_upper P hV hup
variable (clock : ClockLaw.Clock) (i : ClockNoisyLayer.Index P)
local notation "rM" => (mainState i clock).radius
local notation "sM" => (mainState i clock).width
local notation "rF" => (finalState i clock).radius
local notation "sF" => (finalState i clock).width
local notation "capM" => main_caps P hK hc hsmall hC hy clock i
local notation "capF" => final_caps P hK hc hsmall hC hy clock i

/-- Exact recursively constructed main law on the full standalone child seed. -/
def mainLaw :=
  reachableLaw P hK hc hsmall hC privateHy P.delta rM sM P.delta_pos.le (capM).1 (capM).2.1 (capM).2.2.1
    (Real.sqrt P.delta) hV Hlo Hup
    (RecursiveCall.Path.refl (C := src) (PrescribedRecursiveStability.root P rM sM))

/-- Exact recursively constructed active-final law on its complete original seed. -/
def finalLaw :=
  reachableLaw P hK hc hsmall hC privateHy P.delta rF sF P.delta_pos.le (capF).1 (capF).2.1 (capF).2.2.1
    (Real.sqrt P.delta) hV Hlo Hup
    (RecursiveCall.Path.refl (C := src) (PrescribedRecursiveStability.root P rF sF))

/-- The main package's radius is the exact outer row's prescribed radius. -/
theorem main_radius : rM=ClockNoisyLayer.radius P clock i := rfl

/-- The main package keeps the literal fresh-child covariance width. -/
theorem main_width : sM=CovarianceSetup.sigma nr (ClockNoisyLayer.rhoC P) (ClockNoisyLayer.a P) :=
  (ClockNoisyLayer.sigma_width P clock i).symm

/-- Main and paid-final source calls use the same literal source-band radius. -/
theorem final_radius : rF=ClockNoisyLayer.radius P clock i := rfl

def mainKernel := (mainLaw P hK hc hsmall hC hy hV hlo hup clock i).joint
def finalKernel := (finalLaw P hK hc hsmall hC hy hV hlo hup clock i).joint

theorem main_markov : IsMarkovKernel (mainKernel P hK hc hsmall hC hy hV hlo hup clock i) :=
  (mainLaw P hK hc hsmall hC hy hV hlo hup clock i).markov

theorem final_markov : IsMarkovKernel (finalKernel P hK hc hsmall hC hy hV hlo hup clock i) :=
  (finalLaw P hK hc hsmall hC hy hV hlo hup clock i).markov

/-- The main kernel retains every coordinate of the literal child seed. -/
theorem main_source : (mainKernel P hK hc hsmall hC hy hV hlo hup clock i).fst=Kernel.const (Point d)
    (FreshChildRetainedCoupling.sourceLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d)
      (ClockNoisyLayer.child P hR hc hsmall clock i).program) :=
  (mainLaw P hK hc hsmall hC hy hV hlo hup clock i).source

/-- The final kernel retains the original designated Gaussian and full tape. -/
theorem final_source : (finalKernel P hK hc hsmall hC hy hV hlo hup clock i).fst=Kernel.const (Point d)
    (FreshChildRetainedCoupling.sourceLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d)
      (ClockRetainedFinalSplice.final P hR hc hsmall clock i).program) :=
  (finalLaw P hK hc hsmall hC hy hV hlo hup clock i).source

/-- Main physical lower-fibre accuracy, including the original designated input. -/
theorem main_fiber : MeanStandaloneLowerErrorBound.Fiber (F := pot) (gradient V)
    (ClockNoisyLayer.child P hR hc hsmall clock i)
    (mainLaw P hK hc hsmall hC hy hV hlo hup clock i).joint rM sM (4*sM*P.delta^(P.K:ℝ)) := by
  exact PrescribedRetainedFullAccuracy.root_fiber P hK hc hsmall hC privateHy P.delta rM sM
    P.delta_pos.le (capM).1 (capM).2.1 (capM).2.2.1 (Real.sqrt P.delta) hV Hlo Hup hy
    (main_radius_le_one P hK hc hsmall hC hy clock i) le_rfl (capM).2.2.2

/-- Paid-final physical lower-fibre accuracy uses its distinct actual width. -/
theorem final_fiber : MeanStandaloneLowerErrorBound.Fiber (F := pot) (gradient V)
    (ClockRetainedFinalSplice.final P hR hc hsmall clock i)
    (finalLaw P hK hc hsmall hC hy hV hlo hup clock i).joint rF sF (4*sF*P.delta^(P.K:ℝ)) := by
  exact PrescribedRetainedFullAccuracy.root_fiber P hK hc hsmall hC privateHy P.delta rF sF
    P.delta_pos.le (capF).1 (capF).2.1 (capF).2.2.1 (Real.sqrt P.delta) hV Hlo Hup hy
    (final_radius_le_one P hK hc hsmall hC hy clock i) le_rfl (capF).2.2.2

end AcceleratedLogConcave.Root.ClockMeanChildAccuracy
