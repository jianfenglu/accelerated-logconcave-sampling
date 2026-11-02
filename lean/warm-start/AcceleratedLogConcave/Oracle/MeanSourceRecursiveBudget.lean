import AcceleratedLogConcave.Oracle.MeanSourceScaleMoments
import AcceleratedLogConcave.Oracle.MeanSourceScalarAbsorption
import AcceleratedLogConcave.Oracle.MeanSourceSharpRms
import AcceleratedLogConcave.Numerics.SmoothInitialUniformBound

/-! Concrete recursive mean payments. The initializer uses the proved
intrinsic displacement of the same source graph. The paid-final moment is
sharpened before its exact R=delta^t width cancellation is used. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Oracle.MeanSourceRecursiveBudget
open Numerics Numerics.MeanFlowLp Numerics.MeanCollocationLp Numerics.AffineGraph
variable {D m : ℕ} (d : MeanFlowLp.Data (Fin D) m)
local notation "B" => Gibbs.primitiveScale d.F d.x

/-- Literal intrinsic row coefficient, paid by the existing five-branch
source displacement proof; no cardinality or output moment is supplied. -/
theorem intrinsic_initializer_le (hr : d.r≤1) (hscale : d.ell*d.r/d.sigma≤1)
    (hpsi : d.G.psi≤1) :
    d.r*‖SmoothInitialDisplacementBound.rowCoefficient d‖≤100*d.r*B := by
  have h := SmoothInitialUniformBound.norm_rowCoefficient_le_sourceSize d hr hscale hpsi
  have hh := mul_le_mul_of_nonneg_left h d.hr.le
  simpa only [SmoothInitialUniformBound.sourceSize,Gibbs.primitiveScale,mul_assoc,mul_left_comm] using hh

/-- The actual small source slope improves the paid-final moment enough
for the final precision shift to fit inside the recursive constant four. -/
theorem final_scale_square_tight_le (hr : d.r≤1) (hslope : d.ell*d.r≤1/8) :
    MeanBenchmarkMoments.finalScaleSquareBudget d≤((3/2:ℝ)*B)^2 := by
  have hp := MeanSourceScaleMoments.position_square_le d hr
  have hp0 : 0≤MeanBenchmarkMoments.positionSquareBudget d := by
    unfold MeanBenchmarkMoments.positionSquareBudget
    positivity
  have ha0 : 0≤d.ell*d.r*backwardEnd d.G.R := mul_nonneg (mul_nonneg d.hell d.hr.le) d.G.backwardEnd_pos.le
  have ha1 : d.ell*d.r*backwardEnd d.G.R≤1/8 := by
    have hb := mul_le_mul_of_nonneg_left d.G.backwardEnd_lt_one.le (by norm_num : (0:ℝ)≤1/8)
    exact (mul_le_mul_of_nonneg_right hslope d.G.backwardEnd_pos.le).trans (by simpa using hb)
  have ha2 := (sq_le_sq₀ ha0 (by norm_num : (0:ℝ)≤1/8)).2 ha1
  have hm := mul_le_mul_of_nonneg_right ha2 hp0
  unfold MeanBenchmarkMoments.finalScaleSquareBudget
  nlinarith [sq_nonneg B]

theorem final_scale_sqrt_tight_le (hr : d.r≤1) (hslope : d.ell*d.r≤1/8) :
    Real.sqrt (MeanBenchmarkMoments.finalScaleSquareBudget d)≤(3/2:ℝ)*B := by
  apply Real.sqrt_le_iff.mpr
  exact ⟨mul_nonneg (by norm_num) (Gibbs.primitiveScale_nonneg _ _),final_scale_square_tight_le d hr hslope⟩

/-- Literal mean main width cancels its own public row envelope, including
all finite child inventory factors. -/
theorem main_width_row_le {n : ℕ} (nodes : Fin n ≃ d.G.MeanNode)
    {rho aRow : ℝ} (hrho : 0≤rho) (ha : 0<aRow) :
    aRow*CovarianceSetup.sigma n rho aRow≤rho/2 := by
  have hn := RecursiveExecutableDomain.mean_inventory_pos d.G nodes
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hs : 1≤Real.sqrt (n:ℝ) := Real.le_sqrt_of_sq_le (by simpa using hnR)
  have hs0 : 0<Real.sqrt (n:ℝ) := by linarith
  have he : aRow*CovarianceSetup.sigma n rho aRow=rho/(2*Real.sqrt (n:ℝ)) := by
    unfold CovarianceSetup.sigma
    field_simp [ha.ne',hs0.ne']
  rw [he]
  exact div_le_div_of_nonneg_left hrho (by norm_num) (by linarith)

/-- The finite executed forcing sum is paid by two copies of a scalar
forcing bound under the actual half-contraction guard. -/
theorem forcing_sum_two (N : ℕ) {χ T : ℝ} (hχ : 0≤χ) (hhalf : χ≤1/2)
    (hT : 0≤T) (η : ℕ → ℝ) (hη : ∀ k,k<N → η k≤T) :
    Collocation.forcingSum χ η N≤2*T := by
  have hs : Collocation.forcingSum χ η N≤Collocation.forcingSum χ (fun _ => T) N := by
    unfold Collocation.forcingSum
    exact Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hη k (Finset.mem_range.mp hk)) (pow_nonneg hχ _)
  rw [Collocation.forcingSum_const] at hs
  have hg : (∑ j ∈ Finset.range N,χ^j)≤1/(1-χ) := by
    simpa using (geom_sum_Ico_le_of_lt_one (m := 0) (n := N) hχ (by linarith : χ<1))
  have hb : 1/(1-χ)≤2 := (div_le_iff₀ (by linarith : 0<1-χ)).2 (by linarith)
  exact hs.trans ((mul_le_mul_of_nonneg_left (hg.trans hb) hT).trans_eq (by ring))

/-- The paid-final source precision shift cancels its literal radius. The
sharper source moment pays at most three original parent-width units. -/
theorem final_payment_le (P : SourceSchedule) {q : ℝ}
    (hR : d.G.R=P.R) (hr : d.r≤1) (hslope : d.ell*d.r≤1/8) :
    4*RecursiveMeanPublicTable.finalWidth d.G.R d.sigma*P.delta^(q-P.t)*
      Real.sqrt (MeanBenchmarkMoments.finalScaleSquareBudget d)≤
        3*d.sigma*P.delta^q*B := by
  have hs := final_scale_sqrt_tight_le d hr hslope
  have hδ := P.delta_pos
  have hp : 0≤4*RecursiveMeanPublicTable.finalWidth d.G.R d.sigma*P.delta^(q-P.t) := by
    unfold RecursiveMeanPublicTable.finalWidth RecursiveMeanPublicTable.finalNoise
    positivity [d.G.R_pos,d.hsigma]
  have h := mul_le_mul_of_nonneg_left hs hp
  have he : 4*RecursiveMeanPublicTable.finalWidth d.G.R d.sigma*P.delta^(q-P.t)*((3/2:ℝ)*B)=
      ((3/2:ℝ)*Real.sqrt 3)*d.sigma*P.delta^q*B := by
    unfold RecursiveMeanPublicTable.finalWidth RecursiveMeanPublicTable.finalNoise
    rw [hR]
    change 4*(P.delta^P.t*(Real.sqrt 3*d.sigma/2)/2)*P.delta^(q-P.t)*((3/2:ℝ)*B)=_
    have hh : P.delta^P.t*P.delta^(q-P.t)=P.delta^q := by rw [←Real.rpow_add hδ]; congr 1; ring
    calc
      _ = ((3/2:ℝ)*Real.sqrt 3)*d.sigma*(P.delta^P.t*P.delta^(q-P.t))*B := by ring
      _ = _ := by rw [hh]
  rw [he] at h
  have hsq : Real.sqrt (3:ℝ)≤2 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (show (3/2:ℝ)*Real.sqrt 3≤3 by linarith) d.hsigma.le)
        (Real.rpow_nonneg hδ.le _)) (Gibbs.primitiveScale_nonneg _ _))

/-- Pure finite-budget arithmetic, retaining all precision powers. Every
input is a scalar source payment, never a parent accuracy assertion. -/
theorem scalar_absorption {δ r σ ell b B₀ E I res quad χ : ℝ} {N K : ℕ} {q : ℝ}
    (hδ : 0<δ) (hδ1 : δ≤1) (hr : 0≤r) (hσ : 0≤σ) (hell : 0≤ell) (hB : 0≤B₀)
    (hb : 0≤b) (hb1 : b≤1) (hq : q≤(K:ℝ))
    (hχ : 0≤χ) (hhalf : χ≤1/2) (htrans : χ^N≤δ^((K:ℝ)+2))
    (hE0 : 0≤E) (hI0 : 0≤I)
    (hE : E≤3*δ^(q-1/4)*B₀) (hI : I≤100*r*B₀)
    (hres : res≤r*B₀*δ^((K:ℝ)+1))
    (hquad : quad≤(ell*r*B₀/2)*δ^((K:ℝ)+1))
    (hsize : ell*r≤σ*δ^((1:ℝ)/4)/4096)
    (η : ℕ → ℝ) (hη : ∀ k,k<N → η k≤128*r*δ^(q-1/4)*B₀) :
    (2*ell)*(χ^N*(r*b*E+I)+Collocation.forcingSum χ (fun k => r*b*E+res+η k) N)+quad≤
      σ*δ^q*B₀ := by
  let p := δ^(q-1/4)
  let p1 := δ^((K:ℝ)+1)
  let p2 := δ^((K:ℝ)+2)
  let target := σ*δ^q*B₀
  have hp : 0≤p := (Real.rpow_pos_of_pos hδ _).le
  have hp1 : 0≤p1 := (Real.rpow_pos_of_pos hδ _).le
  have hp2 : 0≤p2 := (Real.rpow_pos_of_pos hδ _).le
  have hp21 : p2≤1 := Real.rpow_le_one hδ.le hδ1 (by positivity)
  have hbE : r*b*E≤3*r*p*B₀ := by
    have h1 : b*E≤E := by simpa using mul_le_mul_of_nonneg_right hb1 hE0
    have h2 := mul_le_mul_of_nonneg_left (h1.trans hE) hr
    dsimp [p]
    nlinarith
  have hinit0 : 0≤r*b*E+I := add_nonneg (mul_nonneg (mul_nonneg hr hb) hE0) hI0
  have hit := mul_le_mul htrans (add_le_add hbE hI) hinit0 hp2
  have hit' : χ^N*(r*b*E+I)≤3*r*p*B₀+100*r*p2*B₀ := by
    have hsmall := mul_le_mul_of_nonneg_right hp21 (show 0≤3*r*p*B₀ by positivity)
    dsimp only [p2] at *
    nlinarith [hit,hsmall]
  have hforcing := forcing_sum_two N hχ hhalf
    (show 0≤131*r*p*B₀+r*B₀*p1 by positivity)
    (fun k => r*b*E+res+η k) (fun k hk => by have h := hη k hk; dsimp [p,p1] at *; nlinarith)
  have hmain : χ^N*(r*b*E+I)+Collocation.forcingSum χ (fun k => r*b*E+res+η k) N≤
      265*r*p*B₀+100*r*p2*B₀+2*r*p1*B₀ := by nlinarith
  have hpay := mul_le_mul_of_nonneg_left hmain (show (0:ℝ)≤2*ell by positivity)
  have hqp : δ^((1:ℝ)/4)*p=δ^q := by
    dsimp [p]
    rw [←Real.rpow_add hδ]
    congr 1
    ring
  have hq1 : δ^((1:ℝ)/4)*p1≤δ^q := by
    dsimp [p1]
    rw [←Real.rpow_add hδ]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hq2 : δ^((1:ℝ)/4)*p2≤δ^q := by
    dsimp [p2]
    rw [←Real.rpow_add hδ]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have h0 : ell*r*p*B₀≤target/4096 := by
    have h := mul_le_mul_of_nonneg_right hsize (mul_nonneg hp hB)
    dsimp [target]
    rw [show (σ*δ^((1:ℝ)/4)/4096)*(p*B₀)=σ*(δ^((1:ℝ)/4)*p)*B₀/4096 by ring,hqp] at h
    nlinarith
  have h1 : ell*r*p1*B₀≤target/4096 := by
    have h := mul_le_mul_of_nonneg_right hsize (mul_nonneg hp1 hB)
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq1 hσ) hB
    dsimp [target]
    nlinarith
  have h2 : ell*r*p2*B₀≤target/4096 := by
    have h := mul_le_mul_of_nonneg_right hsize (mul_nonneg hp2 hB)
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq2 hσ) hB
    dsimp [target]
    nlinarith
  have ht0 : 0≤target := by dsimp [target]; positivity
  change _≤target
  nlinarith [hpay,h0,h1,h2]

/-- The literal sharp source recurrence with the actual four-family
recursive amplitudes. Every premise below is an ordinary source scalar or
original-data payment; no current-call accuracy is assumed. -/
theorem source_budget_le (P : SourceSchedule) {n : ℕ} (nodes : Fin n ≃ d.G.MeanNode)
    (hm : 0<m) (hr : d.r≤1) (hslope : d.ell*d.r≤1/8)
    (hscale : d.ell*d.r/d.sigma≤1) (hpsi : d.G.psi≤1) (hR : d.G.R=P.R)
    (hδ1 : P.delta≤1) (hDs : 1≤P.Ds) (q : ℝ) (hq : q≤(P.K:ℝ))
    (hrow : ∀ i,∑ j,|d.G.matrix d.r d.sigma (nodes i) (nodes j)|≤
      SourceMeanExecutable.rowBound (m := m) d.r d.sigma P.delta P.t P.w)
    (hhalf : 2*d.ell*SourceMeanExecutable.rowBound (m := m) d.r d.sigma P.delta P.t P.w≤1/2)
    (htrans : (2*d.ell*SourceMeanExecutable.rowBound (m := m) d.r d.sigma P.delta P.t P.w)^P.NP≤P.delta^((P.K:ℝ)+2))
    (hsize : d.ell*d.r≤d.sigma*P.delta^((1:ℝ)/4)/4096)
    (Eprivate : ℝ) (hE0 : 0≤Eprivate) (hE : Eprivate≤3*P.delta^(q-1/4)*B)
    (hres : MeanOriginalBounds.residualBudget d P.h0≤d.r*B*P.delta^((P.K:ℝ)+1))
    (hquad : MeanOriginalBounds.quadratureBudget d≤(d.ell*d.r*B/2)*P.delta^((P.K:ℝ)+1)) :
    let κ := PrivateSourceScalarAbsorption.twiceNonneg d.ell d.hell
    let aRow := SourceMeanExecutable.rowBound (m := m) d.r d.sigma P.delta P.t P.w
    let sigmaM := CovarianceSetup.sigma n (RecursiveMeanPublicTable.centerNoise d.r d.G.R P.Ds) aRow
    let ε := fun (_ : ℕ) (_ : Fin n) => 256*sigmaM*P.delta^(q-1/4)*B
    (∑ i : Fin m,|GaussLegendre.weight m i|)*((κ:ℝ)*MeanSourceSharpRms.sourceMainBudget d nodes P.h0 P.NP κ aRow Eprivate ε)+
      (∑ i : Fin m,|GaussLegendre.weight m i| * (4*RecursiveMeanPublicTable.finalWidth d.G.R d.sigma*P.delta^(q-P.t)*
        Real.sqrt (MeanBenchmarkMoments.finalScaleSquareBudget d)))+
      MeanOriginalBounds.quadratureBudget d≤4*d.sigma*P.delta^q*B := by
  dsimp only
  let aRow := SourceMeanExecutable.rowBound (m := m) d.r d.sigma P.delta P.t P.w
  let rho := RecursiveMeanPublicTable.centerNoise d.r d.G.R P.Ds
  let sigmaM := CovarianceSetup.sigma n rho aRow
  let ε := fun (_ : ℕ) (_ : Fin n) => 256*sigmaM*P.delta^(q-1/4)*B
  let η := fun k => SharedLayerRms.childRowBudget
    (fun i j => d.G.matrix d.r d.sigma (nodes i) (nodes j)) (SourceMeanExecutionRms.finiteBudget P.NP ε) k
  have ha : 0<aRow := by
    have hpow := Real.rpow_nonneg P.delta_pos.le (-4*P.t-P.w)
    have hfirst := mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num : (0:ℝ)≤256) (pow_nonneg (Nat.cast_nonneg m : (0:ℝ)≤m) 5))
      (div_nonneg d.hr.le d.hsigma.le)) hpow
    change 0<256*(m:ℝ)^5*(d.r/d.sigma)*P.delta^(-4*P.t-P.w)+4*d.r^2
    nlinarith [sq_pos_of_pos d.hr]
  have hrho := RecursiveExecutableDomain.center_noise_pos d.G d.r P.Ds d.hr P.Ds_pos
  have hσM : 0≤sigmaM := (CovarianceSetup.sigma_pos (RecursiveExecutableDomain.mean_inventory_pos d.G nodes) hrho ha).le
  have hrhoB : rho≤d.r := by
    have hs5 : 1≤Real.sqrt (5:ℝ) := Real.le_sqrt_of_sq_le (by norm_num)
    have hden : 2≤2*Real.sqrt 5*P.Ds := by nlinarith [mul_le_mul hs5 hDs (by norm_num : (0:ℝ)≤1) (Real.sqrt_nonneg (5:ℝ))]
    calc
      rho ≤ d.r*d.G.R/2 := div_le_div_of_nonneg_left (mul_nonneg d.hr.le d.G.R_pos.le) (by norm_num) hden
      _ ≤ d.r := by nlinarith [d.hr.le,mul_le_mul_of_nonneg_left d.G.R_le_half d.hr.le]
  have hwidth := main_width_row_le d nodes hrho.le ha
  change aRow*sigmaM≤rho/2 at hwidth
  have hη (k : ℕ) : η k≤128*d.r*P.delta^(q-1/4)*B := by
    have h0 (i : Fin n) : 0≤SourceMeanExecutionRms.finiteBudget P.NP ε k i := by
      unfold SourceMeanExecutionRms.finiteBudget ε
      split_ifs <;> positivity [Gibbs.primitiveScale_nonneg d.F d.x,P.delta_pos]
    have hB (i : Fin n) : SourceMeanExecutionRms.finiteBudget P.NP ε k i≤256*sigmaM*P.delta^(q-1/4)*B := by
      unfold SourceMeanExecutionRms.finiteBudget ε
      split_ifs <;> first | exact le_rfl | positivity [Gibbs.primitiveScale_nonneg d.F d.x,P.delta_pos]
    have hh := PrivateSourceScalarAbsorption.child_row_budget_le
      (fun i j => d.G.matrix d.r d.sigma (nodes i) (nodes j))
      (SourceMeanExecutionRms.finiteBudget P.NP ε) aRow (256*sigmaM*P.delta^(q-1/4)*B)
      ha.le (by positivity [Gibbs.primitiveScale_nonneg d.F d.x,P.delta_pos]) hrow k h0 hB
    have hw := mul_le_mul_of_nonneg_right hwidth
      (show 0≤256*P.delta^(q-1/4)*B by positivity [Gibbs.primitiveScale_nonneg d.F d.x,P.delta_pos])
    have hρ := mul_le_mul_of_nonneg_right hrhoB
      (show 0≤128*P.delta^(q-1/4)*B by positivity [Gibbs.primitiveScale_nonneg d.F d.x,P.delta_pos])
    change η k≤aRow*(256*sigmaM*P.delta^(q-1/4)*B) at hh
    nlinarith [hh,hw,hρ]
  have hI := intrinsic_initializer_le d hr hscale hpsi
  have hmain := scalar_absorption P.delta_pos hδ1 d.hr.le d.hsigma.le d.hell
    (Gibbs.primitiveScale_nonneg _ _) d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one.le hq
    (show 0≤2*d.ell*aRow by positivity [d.hell]) hhalf htrans hE0 (MeanSharpOriginalBounds.initializerBudget_nonneg d)
    hE hI hres hquad hsize η (fun k _ => hη k)
  have hfinal := final_payment_le d P hR hr hslope (q := q)
  have hw : (∑ i : Fin m,|GaussLegendre.weight m i|)=1 := by
    simp_rw [abs_of_pos (GaussLegendre.weight_pos m _)]
    exact GaussLegendre.sum_weight m hm
  rw [hw,one_mul,←Finset.sum_mul,hw,one_mul]
  change (2*d.ell)*MeanSourceSharpRms.sourceMainBudget d nodes P.h0 P.NP
    (PrivateSourceScalarAbsorption.twiceNonneg d.ell d.hell) aRow Eprivate ε+_+_≤_
  change (2*d.ell)*((2*d.ell*aRow)^P.NP*(d.r*backwardEnd d.G.R*Eprivate+MeanSharpOriginalBounds.initializerBudget d)+
    Collocation.forcingSum (2*d.ell*aRow) (fun k => d.r*backwardEnd d.G.R*Eprivate+
      MeanOriginalBounds.residualBudget d P.h0+η k) P.NP)+_+_≤_
  linarith

end AcceleratedLogConcave.Oracle.MeanSourceRecursiveBudget
