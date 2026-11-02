import AcceleratedLogConcave.Channels.GaussianReverseKL
import AcceleratedLogConcave.Root.ClockFinitePhaseKernel

/-! The actual phase's two independent final Gaussian blocks turn a root
coupling error into KL. The position clock is used only in a common measurable
map, so this estimate includes clock zero and never divides by the clock. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
open MeasureTheory ProbabilityTheory InformationTheory
open scoped NNReal ENNReal
namespace AcceleratedLogConcave.Root.ClockPhaseGaussianKL
open Oracle
variable {d : ℕ}
local notation "E" => Point d
local notation "γ" => stdGaussian E

def shiftedPair (c : ℝ) (w : E) : Measure (E × E) :=
  ((γ).prod γ).map (fun z => (w+z.1,c • w+z.2))

private theorem shiftedPair_eq_prod (c : ℝ) (w : E) :
    shiftedPair c w=((γ).map (fun z => w+z)).prod ((γ).map (fun z => c • w+z)) := by
  unfold shiftedPair
  exact (Measure.map_prod_map γ γ
    (show Measurable (fun z : E => w+z) by fun_prop)
    (show Measurable (fun z : E => c • w+z) by fun_prop)).symm

private theorem shiftedPair_KL (c : ℝ) (u v : E) :
    klDiv (shiftedPair c u) (shiftedPair c v)=ENNReal.ofReal ((1+c^2)*‖u-v‖^2/2) := by
  rw [shiftedPair_eq_prod,shiftedPair_eq_prod,Channels.klDiv_prod_prob,
    Channels.klDiv_shift_stdGaussian,Channels.klDiv_shift_stdGaussian,
    ← smul_sub,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

private theorem shiftedPair_ac (c : ℝ) (u v : E) : shiftedPair c u≪shiftedPair c v := by
  apply (klDiv_ne_top_iff.mp _).1
  rw [shiftedPair_KL]
  exact ENNReal.ofReal_ne_top

theorem refresh_variance_pos {Γ : ℝ} (hΓ : 0<Γ) : 0<1-Real.exp (-2*Γ) := by
  have h := Real.exp_lt_one_iff.mpr (by linarith : -2*Γ<0)
  linarith

private theorem refresh_cost {Γ : ℝ} (hΓ : 0<Γ) (w : E) :
    (1+(Real.exp (-Γ)/Real.sqrt (1-Real.exp (-2*Γ)))^2)*‖w‖^2/2=
      ‖w‖^2/(2*(1-Real.exp (-2*Γ))) := by
  have hv := refresh_variance_pos hΓ
  have hs := Real.sq_sqrt hv.le
  have ht : (Real.exp (-Γ))^2=Real.exp (-2*Γ) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [div_pow,hs,ht]
  have hsum : 1+Real.exp (-2*Γ)/(1-Real.exp (-2*Γ))=1/(1-Real.exp (-2*Γ)) := by
    calc
      _ = (1-Real.exp (-2*Γ))/(1-Real.exp (-2*Γ))+Real.exp (-2*Γ)/(1-Real.exp (-2*Γ)) := by
        rw [div_self (ne_of_gt hv)]
      _ = ((1-Real.exp (-2*Γ))+Real.exp (-2*Γ))/(1-Real.exp (-2*Γ)) := (add_div _ _ _).symm
      _ = _ := by congr 1; ring
  rw [hsum,div_mul_eq_div_div]
  ring

/-- Reverse transport through the actual pair of fresh final Gaussians,
retaining any common input and clock readout r. The whole coupling state is
independent of both fresh Gaussian blocks. -/
theorem refresh_retained {A R : Type*} [MeasurableSpace A] [MeasurableSpace R]
    (μ : Measure A) [IsFiniteMeasure μ] {Γ : ℝ} (hΓ : 0<Γ)
    (u v x : A→E) (hu : Measurable u) (hv : Measurable v) (hx : Measurable x)
    (a : A→ℝ) (ha : Measurable a) (r : A→R) (hr : Measurable r) :
    klDiv ((μ.prod ((γ).prod γ)).map (fun z =>
      (r z.1,(x z.1+a z.1 • (u z.1+z.2.1),
        Real.exp (-Γ) • u z.1+Real.sqrt (1-Real.exp (-2*Γ)) • z.2.2))))
      ((μ.prod ((γ).prod γ)).map (fun z =>
        (r z.1,(x z.1+a z.1 • (v z.1+z.2.1),
          Real.exp (-Γ) • v z.1+Real.sqrt (1-Real.exp (-2*Γ)) • z.2.2))))≤
      ∫⁻ z,ENNReal.ofReal (‖u z-v z‖^2/(2*(1-Real.exp (-2*Γ)))) ∂μ := by
  let c := Real.exp (-Γ)/Real.sqrt (1-Real.exp (-2*Γ))
  let Fu : A × (E × E)→E × E := fun z => (u z.1+z.2.1,c • u z.1+z.2.2)
  let Fv : A × (E × E)→E × E := fun z => (v z.1+z.2.1,c • v z.1+z.2.2)
  have hFu : Measurable Fu := by dsimp [Fu]; fun_prop
  have hFv : Measurable Fv := by dsimp [Fv]; fun_prop
  let κ := Channels.freshKernel ((γ).prod γ) Fu hFu
  let η := Channels.freshKernel ((γ).prod γ) Fv hFv
  have hκ (z : A) : κ z=shiftedPair c (u z) := rfl
  have hη (z : A) : η z=shiftedPair c (v z) := rfl
  let f : A × (E × E)→R × (E × E) := fun z =>
    (r z.1,(x z.1+a z.1 • z.2.1,Real.sqrt (1-Real.exp (-2*Γ)) • z.2.2))
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hb := Channels.klDiv_map_compProd_le_lintegral_of_ac μ κ η
    (fun z => shiftedPair_ac c (u z) (v z)) f hf
  have hcost (z : A) : klDiv (κ z) (η z)=
      ENNReal.ofReal (‖u z-v z‖^2/(2*(1-Real.exp (-2*Γ)))) := by
    rw [hκ,hη,shiftedPair_KL]
    exact congrArg ENNReal.ofReal (refresh_cost hΓ _)
  simp_rw [hcost] at hb
  dsimp only [κ,η] at hb
  rw [Channels.compProd_freshKernel,Channels.compProd_freshKernel,
    Measure.map_map hf (by fun_prop),Measure.map_map hf (by fun_prop)] at hb
  have hs : Real.sqrt (1-Real.exp (-2*Γ))*c=Real.exp (-Γ) := by
    dsimp [c]
    calc
      _ = (Real.sqrt (1-Real.exp (-2*Γ))/Real.sqrt (1-Real.exp (-2*Γ)))*Real.exp (-Γ) := by ring
      _ = _ := by rw [div_self (ne_of_gt (Real.sqrt_pos.mpr (refresh_variance_pos hΓ))),one_mul]
  convert hb using 1
  congr 2 <;> funext z <;>
    simp only [Function.comp_apply,f,Fu,Fv,smul_add,smul_smul,hs]
/-- Literal affine refresh/reheat map of the physical phase. The clock is
multiplied into position, with no restriction that it be nonzero. -/
def phaseOutput (h Γ clock : ℝ) (x w z1 z2 : E) : E × E :=
  (x+(Real.sqrt (2*h^2)*(ClockPublicSetup.s*clock)) • (w+z1),
    Real.exp (-Γ) • w+Real.sqrt (1-Real.exp (-2*Γ)) • z2)

/-- Exact same-tape connection to the actual executable phase. -/
theorem output_eq_phaseOutput (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch)
    (hsmall : P.csch<1/160) (label : ℕ) (Γ : ℝ) (G : E→E)
    (z : (E × E) × ClockFinitePhaseKernel.Draw P hR hc hsmall (d:=d) label) :
    ClockFinitePhaseKernel.output P hR hc hsmall label Γ G z=
      phaseOutput P.delta Γ (ClockUniformDraw.clockOfUniform z.2.1.1.1)
        z.1.1 (ClockPhysicalExecutionKernel.output P hR hc hsmall label G
          (ClockFinitePhaseKernel.normalizedInput P z.1,z.2.1.1)) z.2.1.2 z.2.2 := rfl

/-- The physical source phase's reserve/refresh KL, with its input and clock
retained through any measurable common readout. -/
theorem phase_retained {A R : Type*} [MeasurableSpace A] [MeasurableSpace R]
    (μ : Measure A) [IsFiniteMeasure μ] (h : ℝ) {Γ : ℝ} (hΓ : 0<Γ)
    (u v x : A→E) (hu : Measurable u) (hv : Measurable v) (hx : Measurable x)
    (clock : A→ℝ) (hclock : Measurable clock) (r : A→R) (hr : Measurable r) :
    klDiv ((μ.prod ((γ).prod γ)).map (fun z =>
      (r z.1,phaseOutput h Γ (clock z.1) (x z.1) (u z.1) z.2.1 z.2.2)))
      ((μ.prod ((γ).prod γ)).map (fun z =>
        (r z.1,phaseOutput h Γ (clock z.1) (x z.1) (v z.1) z.2.1 z.2.2)))≤
      ∫⁻ z,ENNReal.ofReal (‖u z-v z‖^2/(2*(1-Real.exp (-2*Γ)))) ∂μ :=
  refresh_retained μ hΓ u v x hu hv hx
    (fun z => Real.sqrt (2*h^2)*(ClockPublicSetup.s*clock z)) (by fun_prop) r hr

/-- A short positive refresh has variance at least its time. -/
theorem refresh_variance_ge {Γ : ℝ} (hΓ : 0≤Γ) (hhalf : Γ≤1/2) :
    Γ≤1-Real.exp (-2*Γ) := by
  have he := Real.add_one_le_exp (2*Γ)
  have hexp : Real.exp (-2*Γ)*Real.exp (2*Γ)=1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (-2*Γ)).le
  rw [hexp] at hm
  by_contra hn
  have hp : 0<Real.exp (-2*Γ)+Γ-1 := by linarith
  have hpos := mul_pos (show 0<1+2*Γ by linarith) hp
  nlinarith

/-- The source short-refresh regime pays the Gaussian comparison by an
inverse refresh time; the random position clock never enters the denominator. -/
theorem refresh_cost_le {Γ : ℝ} (hΓ : 0<Γ) (hhalf : Γ≤1/2) (w : E) :
    ‖w‖^2/(2*(1-Real.exp (-2*Γ)))≤‖w‖^2/(2*Γ) := by
  have hv := refresh_variance_ge hΓ.le hhalf
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity : 0<2*Γ)
    (mul_le_mul_of_nonneg_left hv (by norm_num : (0:ℝ)≤2))

theorem sourceGamma_pos (P : SourceSchedule) {κ : ℝ} (hκ : 1≤κ) :
    0<ClockFinitePhaseKernel.sourceGamma P κ := by
  unfold ClockFinitePhaseKernel.sourceGamma
  positivity [P.delta_pos]

theorem sourceGamma_le_delta (P : SourceSchedule) {κ : ℝ} (hκ : 1≤κ) :
    ClockFinitePhaseKernel.sourceGamma P κ≤P.delta := by
  have hs : 1≤Real.sqrt (κ+2*P.delta^2) := by
    apply (Real.le_sqrt (by norm_num) (by positivity : 0≤κ+2*P.delta^2)).mpr
    nlinarith [sq_nonneg P.delta]
  exact div_le_self P.delta_pos.le hs
end AcceleratedLogConcave.Root.ClockPhaseGaussianKL
