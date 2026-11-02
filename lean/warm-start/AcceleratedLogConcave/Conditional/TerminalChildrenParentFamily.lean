import AcceleratedLogConcave.Conditional.MeanReferenceLayer
import AcceleratedLogConcave.Conditional.SourcePositionFamily
import AcceleratedLogConcave.Conditional.SourceParameterDomain
import AcceleratedLogConcave.Oracle.Precision
import AcceleratedLogConcave.Oracle.TerminalMean

/-!
# Actual parent assembly with terminal identity children

The terminal references return the same designated inputs. Their increments
vanish; the source centering increment is retained in full. This module's
fixed-data identities do not themselves assert varying-parameter regularity.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff ENNReal
namespace AcceleratedLogConcave.Conditional.TerminalChildrenParentFamily
open Numerics Numerics.MeanFlowLp Numerics.AffineGraph MeanReferenceLayer
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

/-- The actual active-final width, `R n / 2` with `n = sqrt(3) sigma / 2`. -/
def childScale (d : Data ι m) : ℝ := d.G.R * Real.sqrt 3 * d.sigma / 4

/-- Normalized source coefficients depend only on the fixed final inventory. -/
def normalizedCoefficients (G : MeanGeometry m) : Option (Fin m) → ℝ
  | none => 1 / 2
  | some i => GaussLegendre.weight m i * (G.R * Real.sqrt 3 / 4)

omit [DecidableEq ι] in
theorem childScale_pos (d : Data ι m) : 0 < childScale d := by
  unfold childScale
  exact div_pos (mul_pos (mul_pos d.G.R_pos (Real.sqrt_pos.mpr (by norm_num))) d.hsigma)
    (by norm_num)

theorem sum_weight_sq_le_one (hm : 0 < m) :
    ∑ i : Fin m, (GaussLegendre.weight m i) ^ 2 ≤ 1 := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (fun i _ ↦ (GaussLegendre.weight_pos m i).le)
  simpa [GaussLegendre.sum_weight m hm] using h

omit [DecidableEq ι] in
theorem source_budget_remainder_pos (d : Data ι m) (hm : 0 < m) :
    0 < d.sigma ^ 2 - (d.sigma / 2) ^ 2 -
      ∑ i : Fin m, (GaussLegendre.weight m i * childScale d) ^ 2 := by
  have hw := sum_weight_sq_le_one hm
  have hR : d.G.R ^ 2 ≤ 1 / 4 := by nlinarith [d.G.R_pos, d.G.R_le_half]
  have hs : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have heq : (∑ i : Fin m, (GaussLegendre.weight m i * childScale d) ^ 2) =
      (childScale d) ^ 2 * ∑ i : Fin m, (GaussLegendre.weight m i) ^ 2 := by
    simp_rw [mul_pow]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hb := mul_le_mul_of_nonneg_left hw (sq_nonneg (childScale d))
  rw [← heq, mul_one] at hb
  have hcs : (childScale d) ^ 2 ≤ 3 * d.sigma ^ 2 / 64 := by
    unfold childScale
    have hR' := mul_le_mul_of_nonneg_right hR (sq_nonneg d.sigma)
    nlinarith
  nlinarith [sq_pos_of_pos d.hsigma]

/-- The actual positive reserve from the unused variance budget. -/
def beta (d : Data ι m) : ℝ := Real.sqrt
  (d.sigma ^ 2 - (d.sigma / 2) ^ 2 -
    ∑ i : Fin m, (GaussLegendre.weight m i * childScale d) ^ 2)

omit [DecidableEq ι] in
theorem beta_pos (d : Data ι m) (hm : 0 < m) : 0 < beta d :=
  Real.sqrt_pos.mpr (source_budget_remainder_pos d hm)

omit [DecidableEq ι] in
theorem source_budget (d : Data ι m) (hm : 0 < m) :
    (d.sigma / 2) ^ 2 +
      (∑ i : Fin m, (GaussLegendre.weight m i * childScale d) ^ 2) +
      beta d ^ 2 = d.sigma ^ 2 := by
  rw [beta, Real.sq_sqrt (source_budget_remainder_pos d hm).le]
  ring

/-- The literal terminal child reference keeps its designated momentum. -/
def terminalKernel : Kernel (E × E) E := Kernel.deterministic Prod.snd measurable_snd

instance terminalKernel_markov : IsMarkovKernel (terminalKernel (ι := ι)) := by
  unfold terminalKernel
  infer_instance

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem terminalKernel_apply (y p : E) :
    terminalKernel (y,p) = Measure.dirac p := rfl

/-- Source widths and budget, with actual identity references at every final slot. -/
def terminalChildren (d : Data ι m) (hm : 0 < m) : Children d where
  scale _ := childScale d
  scale_pos _ := childScale_pos d
  beta := beta d
  beta_pos := beta_pos d hm
  budget := source_budget d hm
  kernel _ := terminalKernel
  markov _ := inferInstance
  invariant _ y := by
    have heq : (terminalKernel (ι := ι)).comap (fun p ↦ (y,p)) measurable_prodMk_left =
        Kernel.id := by
      ext p : 1
      rfl
    rw [heq]
    exact Measure.id_comp

omit [DecidableEq ι] in
/-- Dividing the source physical coefficients by sigma removes every varying
center, radius and width parameter from the Gaussian assembly coefficients. -/
theorem coefficients_eq_normalized (d : Data ι m) (hm : 0 < m) :
    coefficients d (terminalChildren d hm) = normalizedCoefficients d.G := by
  funext i
  cases i with
  | none =>
    change (d.sigma / 2) / d.sigma = 1 / 2
    field_simp [d.hsigma.ne']
  | some i =>
    change (GaussLegendre.weight m i * childScale d) / d.sigma =
      GaussLegendre.weight m i * (d.G.R * Real.sqrt 3 / 4)
    unfold childScale
    field_simp [d.hsigma.ne']

/-- Terminal child increments cancel. The full source centering increment
survives, with the original retained parent input unchanged. -/
theorem recombine_terminalChildren (d : Data ι m) (hm : 0 < m) (h : Host ι m) :
    recombine d (terminalChildren d hm) h
      (fun i ↦ active d (terminalChildren d hm) h (some i)) =
      h.1 + (1 / 2 : ℝ) •
        ((phase d (terminalChildren d hm) 1 h).snd -
          active d (terminalChildren d hm) h none) := by
  have heq := displacement_target d (terminalChildren d hm) h
    (fun i ↦ active d (terminalChildren d hm) h (some i))
  simp only [sub_self, smul_zero, Finset.sum_const_zero, add_zero] at heq
  apply (smul_right_injective E d.hsigma.ne')
  dsimp only
  rw [smul_add, smul_smul]
  have hc : d.sigma * (1 / 2 : ℝ) = d.sigma / 2 := by ring
  rw [hc]
  rw [smul_sub] at heq
  exact sub_eq_iff_eq_add.mp heq |>.trans (add_comm _ _)

omit [Fintype ι] [DecidableEq ι] in
/-- A literal finite product of deterministic references is a single Dirac law. -/
theorem finiteProduct_dirac {A : Type*} [MeasurableSpace A] (n : ℕ)
    (k : Fin n → Kernel A E) (hk : ∀ i, IsMarkovKernel (k i))
    (x : A) (g : Fin n → E) (hkg : ∀ i, k i x = Measure.dirac (g i)) :
    finiteProduct n k x = Measure.dirac g := by
  induction n with
  | zero =>
    rw [finiteProduct, Kernel.deterministic_apply]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    let := hk 0
    let := finiteProduct_markov n (fun i ↦ k i.succ) (fun i ↦ hk i.succ)
    rw [finiteProduct, Kernel.map_apply _ (measurable_cons n), Kernel.prod_apply,
      hkg 0, ih (fun i ↦ k i.succ) (fun i ↦ hk i.succ)
        (fun i ↦ g i.succ) (fun i ↦ hkg i.succ), Measure.dirac_prod_dirac,
      Measure.map_dirac' (measurable_cons n)]
    congr 1
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i

/-- Every final reference returns the original designated child input, so its
actual independent product is exactly their joint Dirac law. -/
theorem childrenKernel_terminalChildren (d : Data ι m) (hm : 0 < m) (h : Host ι m) :
    childrenKernel d (terminalChildren d hm) h =
      Measure.dirac (fun i ↦ active d (terminalChildren d hm) h (some i)) := by
  exact finiteProduct_dirac m _ (fun _ ↦ inferInstance) h _ (fun _ ↦ rfl)

/-- The retained readout keeps the original parent input and its actual
source centering displacement. -/
def readout (d : Data ι m) (hm : 0 < m) (h : Host ι m) : E :=
  h.1 + (1 / 2 : ℝ) • ((phase d (terminalChildren d hm) 1 h).snd -
    active d (terminalChildren d hm) h none)

theorem continuous_readout (d : Data ι m) (hm : 0 < m) : Continuous (readout d hm) := by
  have hp : Continuous (fun h : Host ι m ↦
      (phase d (terminalChildren d hm) 1 h).snd) :=
    (WithLp.prod_continuous_ofLp 2 E E).snd.comp (continuous_phase d (terminalChildren d hm) 1)
  unfold readout
  exact continuous_fst.add ((hp.sub (continuous_active d (terminalChildren d hm) none)).const_smul
    (1 / 2 : ℝ))


/-- Fresh position and independent Gaussian array, with the original input retained. -/
def retainedKernel (d : Data ι m) (hm : 0 < m) : Kernel E E :=
  (freshKernel d).map (readout d hm)

instance retainedKernel_markov (d : Data ι m) (hm : 0 < m) :
    IsMarkovKernel (retainedKernel d hm) :=
  Kernel.IsMarkovKernel.map _ (continuous_readout d hm).measurable

/-- Equality of complete fixed-input kernels with the actual source parent,
not merely equality after averaging the retained input. -/
theorem parentKernel_eq_retainedKernel (d : Data ι m) (hm : 0 < m) :
    parentKernel d (terminalChildren d hm) = retainedKernel d hm := by
  let g : Host ι m → Host ι m × (Fin m → E) :=
    fun h ↦ (h, fun i ↦ active d (terminalChildren d hm) h (some i))
  have hg : Measurable g := by
    apply measurable_id.prodMk
    apply Measurable.of_eval
    intro i
    exact (continuous_active d (terminalChildren d hm) (some i)).measurable
  have hdet : ((Kernel.id : Kernel (Host ι m) (Host ι m)) ×ₖ
      childrenKernel d (terminalChildren d hm)) = Kernel.deterministic g hg := by
    ext h : 1
    rw [Kernel.prod_apply, Kernel.id_apply, childrenKernel_terminalChildren,
      Measure.dirac_prod_dirac]
    rfl
  unfold parentKernel jointKernel retainedKernel
  rw [hdet, Kernel.map_comp, Kernel.deterministic_map hg
    (continuous_recombine d (terminalChildren d hm)).measurable,
    Kernel.deterministic_comp_eq_map]
  congr 1
  funext h
  exact recombine_terminalChildren d hm h

/-- Gaussian stationarity follows from the proved actual-parent theorem. -/
theorem retainedKernel_invariant (d : Data ι m) (hm : 0 < m) :
    retainedKernel d hm ∘ₘ stdGaussian E = stdGaussian E := by
  rw [← parentKernel_eq_retainedKernel]
  exact parentKernel_invariant d (terminalChildren d hm)

section VaryingParameters
variable {F : EuclideanSpace ℝ ι → ℝ} {ell : ℝ} (hF : ContDiff ℝ 2 F) (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
  (G : MeanGeometry m)

/-- Actual source data at each center, radius and positive parent width. -/
def data (theta : SourceParameters E ell) : Data ι m where
  F := F
  hF := hF
  ell := ell
  hell := hell
  hlo := hlo
  hup := hup
  x := theta.center
  r := theta.radius
  hr := theta.radius_pos
  hsmall := theta.small
  G := G
  sigma := theta.width
  hsigma := theta.width_pos

/-- The exact retained readout on parameter, original input, independent
position and literal Gaussian auxiliary array. -/
def sourceReadout (theta : SourceParameters E ell) (p : E) (fresh : Fresh ι m) : E :=
  let g0 := GaussianAssembly.active (normalizedCoefficients G) p fresh.2 none
  p + (1 / 2 : ℝ) •
    ((Centering.sourceCenteringFlow hF hell hlo hup theta.center theta.radius_pos
      G.backwardEnd_pos.le G.backwardEnd_lt_one theta.small (half_pos theta.width_pos)
      (WithLp.toLp 2 (fresh.1,g0)) 1).snd - g0)

/-- Fixed-data assembly uses exactly the literal physical source readout. -/
theorem readout_data_eq_sourceReadout (hm : 0 < m) (theta : SourceParameters E ell)
    (p : E) (fresh : Fresh ι m) :
    readout (data hF hell hlo hup G theta) hm (p,fresh) =
      sourceReadout hF hell hlo hup G theta p fresh := by
  unfold readout MeanReferenceLayer.phase active
  rw [coefficients_eq_normalized]
  rfl

omit [DecidableEq ι] in
/-- The source position law equals the already constructed exact varying family. -/
theorem positionLaw_data_eq (theta : SourceParameters E ell) :
    MeanBenchmarkCoupling.positionLaw (data hF hell hlo hup G theta) =
      interpolationLaw F theta.center theta.radius (backwardEnd G.R) := rfl

end VaryingParameters

/-- With a nonempty actual final inventory, the first nonterminal band is exact. -/
theorem all_final_terminal_iff (hm : 0 < m) (q t : ℝ) :
    ((1 / 2 : ℝ) < q ∧ ∀ _ : Fin m, Oracle.Precision.terminal (q - t)) ↔
      (1 / 2 : ℝ) < q ∧ q ≤ 1 / 2 + t := by
  have i : Fin m := ⟨0, hm⟩
  simp only [Oracle.Precision.terminal]
  constructor
  · rintro ⟨hq, hchildren⟩
    exact ⟨hq, by have := hchildren i; linarith⟩
  · rintro ⟨hq, hband⟩
    exact ⟨hq, fun _ ↦ by linarith⟩

/-- These are exactly the active-final edges of the source precision interface;
this does not select a complete compiler recursion tree. -/
theorem source_final_edge (q t : ℝ) (hq : (1 / 2 : ℝ) < q) (_i : Fin m) :
    Oracle.Precision.CallEdge t .activeFinal (.mean (q - t)) (.mean q) :=
  Oracle.Precision.CallEdge.activeFinal hq

/-- In the executable terminal source, the retained reference is precisely
our identity child kernel at every center, input, and auxiliary value. -/
theorem terminalKernel_eq_sourceRetained {d : ℕ} (origin : Oracle.Origin)
    (grad : Oracle.Point d → Oracle.Point d) (a r sigma : ℝ)
    (y p z : Oracle.Point d) :
    terminalKernel (y,p) =
      Measure.dirac (Oracle.terminalMeanRetained origin grad a r sigma y p z).2 := rfl

/-- The separate main/private precision decrement has its own terminal check. -/
theorem quarter_child_terminal_iff (q : ℝ) :
    Oracle.Precision.terminal (q - 1 / 4) ↔ q ≤ 3 / 4 := by
  unfold Oracle.Precision.terminal
  constructor <;> intro h <;> linarith

end AcceleratedLogConcave.Conditional.TerminalChildrenParentFamily
