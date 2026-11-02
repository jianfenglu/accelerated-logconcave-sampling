import AcceleratedLogConcave.Root.ClockCollocation
import AcceleratedLogConcave.Numerics.AffineQuadrature
import AcceleratedLogConcave.Root.OuterRootOriginalQuadrature

/-! Physical mesh identities for the prescribed outer clock schedule. Scaling
keeps every source label, and clipped cell integrals telescope before norms. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Root.ClockQuadratureRows
open Numerics Numerics.AffineGraph Numerics.GaussLegendre
open ClockCollocation

def scaleMesh {b : ℝ} (M : IntervalMesh 0 b) (ρ : ℝ) (hρ : 0 < ρ) :
    IntervalMesh 0 (ρ*b) where
  cellsPred := M.cellsPred
  point k := ρ*M.point k
  strictMono := fun _ _ hab => mul_lt_mul_of_pos_left (M.strictMono hab) hρ
  first := by rw [M.first, mul_zero]
  last := by rw [M.last]

variable {b : ℝ} (M : IntervalMesh 0 b) (ρ : ℝ) (hρ : 0 < ρ)

@[simp] theorem scale_left (c : M.Cell) :
    (scaleMesh M ρ hρ).left c = ρ*M.left c := rfl

@[simp] theorem scale_right (c : M.Cell) :
    (scaleMesh M ρ hρ).right c = ρ*M.right c := rfl

@[simp] theorem scale_length (c : M.Cell) :
    (scaleMesh M ρ hρ).length c = ρ*M.length c := by
  simp only [IntervalMesh.length, scale_right, scale_left, mul_sub]

theorem scale_clipped (t : ℝ) (c : M.Cell) :
    (scaleMesh M ρ hρ).clipped (ρ*t) c = ρ*M.clipped t c := by
  simp only [IntervalMesh.clipped, scale_left, scale_right,
    mul_max_of_nonneg, mul_min_of_nonneg, hρ.le]

theorem scale_normalizedCoordinate (t : ℝ) (c : M.Cell) :
    (scaleMesh M ρ hρ).normalizedCoordinate (ρ*t) c = M.normalizedCoordinate t c := by
  simp only [IntervalMesh.normalizedCoordinate, scale_clipped, scale_left, scale_length]
  rw [← mul_sub, mul_div_mul_left _ _ (ne_of_gt hρ)]

theorem scale_location (m : ℕ) (z : M.Source m) :
    (scaleMesh M ρ hρ).location m z = ρ*M.location m z := by
  simp only [IntervalMesh.location, cellNode, scale_left, scale_length]
  ring

theorem scale_row (m : ℕ) (u v : ℝ) (z : M.Source m) :
    (scaleMesh M ρ hρ).row m (ρ*u) (ρ*v) z = ρ*M.row m u v z := by
  rw [(scaleMesh M ρ hρ).row_eq_partialRow, M.row_eq_partialRow,
    scale_normalizedCoordinate, scale_normalizedCoordinate, scale_left, scale_length,
    partialRow_scale _ _ _ _ _ (mul_ne_zero (ne_of_gt hρ) (ne_of_gt (M.length_pos z.1))),
    partialRow_scale _ _ _ _ _ (ne_of_gt (M.length_pos z.1))]
  simp only [one_mul]
  ring

/-- The physical partition has exactly the prescribed cell count. -/
def clockMesh (J : ℕ) (hJ : 0 < J) (clock : ClockLaw.Clock)
    (hc : 0 < (clock:ℝ)) : IntervalMesh 0 (clock:ℝ) where
  cellsPred := (unitMesh J hJ).cellsPred
  point k := (clock:ℝ)*(unitMesh J hJ).point k
  strictMono := (scaleMesh (unitMesh J hJ) clock hc).strictMono
  first := (scaleMesh (unitMesh J hJ) clock hc).first
  last := by rw [(unitMesh J hJ).last, mul_one]

theorem clockMesh_location (J m : ℕ) (hJ : 0 < J) (clock : ClockLaw.Clock)
    (hc : 0 < (clock:ℝ)) (j : Fin (J*m)) :
    (clockMesh J hJ clock hc).location m (enumeration J m hJ j) =
      ClockSchedule.nodeValue J m clock j := by
  change (scaleMesh (unitMesh J hJ) clock hc).location m _ = _
  rw [scale_location, location_enumeration]
  rfl

theorem clockMesh_row (h : ℝ) (hh : 0 < h) (K : ℕ) (clock : ClockLaw.Clock)
    (hc : 0 < (clock:ℝ)) (a : ℝ) (j : MainIndex h K) :
    (clockMesh (ClockSchedule.sourceCells h) (ClockSchedule.sourceCells_pos hh)
      clock hc).row (ClockSchedule.sourceOrder K) 0 ((clock:ℝ)*a)
        (enumeration _ _ (ClockSchedule.sourceCells_pos hh) j) = W h hh K clock a j := by
  change (scaleMesh (unitMesh _ _) clock hc).row _ 0 _ _ = _
  simpa only [mul_zero, W] using scale_row (unitMesh _ _) clock hc
    (ClockSchedule.sourceOrder K) 0 a (enumeration _ _ (ClockSchedule.sourceCells_pos hh) j)

theorem clockMesh_length (J : ℕ) (hJ : 0 < J) (clock : ClockLaw.Clock)
    (hc : 0 < (clock:ℝ)) (c : (clockMesh J hJ clock hc).Cell) :
    (clockMesh J hJ clock hc).length c = (clock:ℝ)/J := by
  change (scaleMesh (unitMesh J hJ) clock hc).length c = _
  rw [scale_length, unitMesh_length]
  ring

section Defect
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Per-cell estimates for the actual physical partition telescope into the
literal fixed-label partial row. No extra factor is paid for earlier cells. -/
theorem prescribedRow_defect_of_cells
    (h : ℝ) (hh : 0 < h) (K : ℕ) (clock : ClockLaw.Clock) (hc : 0 < (clock:ℝ))
    (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) (f : ℝ → E)
    (hf : ContinuousOn f (Icc (0:ℝ) clock))
    (B : (clockMesh _ (ClockSchedule.sourceCells_pos hh) clock hc).Cell → ℝ)
    (hcell : ∀ c,
      let M := clockMesh _ (ClockSchedule.sourceCells_pos hh) clock hc
      ‖(∫ t in M.left c..M.clipped ((clock:ℝ)*a) c, f t) -
        ∑ j : Fin (ClockSchedule.sourceOrder K), M.row (ClockSchedule.sourceOrder K)
          0 ((clock:ℝ)*a) (c,j) • f (M.location (ClockSchedule.sourceOrder K) (c,j))‖ ≤ B c) :
    ‖(∫ t in 0..((clock:ℝ)*a), f t) -
      ∑ j : MainIndex h K, W h hh K clock a j • f (u h K clock j)‖ ≤ ∑ c, B c := by
  let M := clockMesh _ (ClockSchedule.sourceCells_pos hh) clock hc
  have ht : (clock:ℝ)*a ∈ Icc (0:ℝ) clock :=
    ⟨mul_nonneg hc.le ha.1, by simpa using mul_le_mul_of_nonneg_left ha.2 hc.le⟩
  have hsum : (∑ j : MainIndex h K, W h hh K clock a j • f (u h K clock j)) =
      ∑ z : M.Source (ClockSchedule.sourceOrder K),
        M.row (ClockSchedule.sourceOrder K) 0 ((clock:ℝ)*a) z •
          f (M.location (ClockSchedule.sourceOrder K) z) := by
    calc
      _ = ∑ j : MainIndex h K,
          M.row (ClockSchedule.sourceOrder K) 0 ((clock:ℝ)*a)
            (enumeration _ _ (ClockSchedule.sourceCells_pos hh) j) •
          f (M.location (ClockSchedule.sourceOrder K)
            (enumeration _ _ (ClockSchedule.sourceCells_pos hh) j)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [clockMesh_row, clockMesh_location]
        rfl
      _ = _ := (enumeration _ (ClockSchedule.sourceOrder K)
        (ClockSchedule.sourceCells_pos hh)).sum_comp
          (fun z => M.row (ClockSchedule.sourceOrder K) 0 ((clock:ℝ)*a) z •
            f (M.location (ClockSchedule.sourceOrder K) z))
  rw [hsum, Fintype.sum_prod_type,
    ← Numerics.AffineResidual.sum_integral_clipped_left M f hf _ ht,
    ← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => hcell c)

end Defect

section Original
open OuterRootFlowIdentification OuterRootStrongJetLp Analysis.PositiveVarianceSlab
variable {ι : Type*} [Fintype ι]
variable {V : EuclideanSpace ℝ ι → ℝ} (hV : ContDiff ℝ 2 V)
  {m h : ℝ} (hm : 0 < m) (hh : 0 < h)
  (hlo : ∀ z v, m * ‖v‖^2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖^2)

/-- The actual prescribed partial row on the common original-data seed. All
cell errors use the original Gaussian-start jet; only their scalar budgets add. -/
theorem source_prescribedRow (hsmall : h ≤ 1/2) (K : ℕ) (clock : ClockLaw.Clock)
    (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) :
    let F := family hV hm hh hlo hup
    let d := OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup
    let n := ClockSchedule.sourceOrder K - 1
    ‖(∫ t in 0..((clock:ℝ)*a), jetLp F d (Real.sqrt h)⁻¹ 1 t) -
      ∑ j : MainIndex h K, W h hh K clock a j •
        jetLp F d (Real.sqrt h)⁻¹ 1 (u h K clock j)‖ ≤
      (ClockSchedule.sourceCells h : ℝ) *
        (2*((clock:ℝ)/(ClockSchedule.sourceCells h:ℝ))^(n+2)*
          ((2*h^2)*Numerics.ConditionalSmoothing.materialOrderFactor
            (Fintype.card ι) n / (3/4)^(n+1))/((n+1).factorial:ℝ)) := by
  dsimp only
  let F := family hV hm hh hlo hup
  let d := OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup
  let f := jetLp F d (Real.sqrt h)⁻¹ 1
  generalize hn0 : ClockSchedule.sourceOrder K - 1 = n
  have hn : ClockSchedule.sourceOrder K = n+1 := by
    have hp := ClockSchedule.sourceOrder_pos K
    omega
  by_cases hc : 0 < (clock:ℝ)
  · let M := clockMesh _ (ClockSchedule.sourceCells_pos hh) clock hc
    let B := 2*((clock:ℝ)/(ClockSchedule.sourceCells h:ℝ))^(n+2)*
      ((2*h^2)*Numerics.ConditionalSmoothing.materialOrderFactor (Fintype.card ι) n /
        (3/4)^(n+1))/((n+1).factorial:ℝ)
    have hf : ContinuousOn f (Icc (0:ℝ) clock) := by
      apply (jetLp_contDiffOn F d (Real.sqrt h)⁻¹ 1 0).continuousOn.mono
      intro t ht
      apply source_subset d.hb d.hb1
      exact ⟨ht.1, ht.2.trans clock.2.2⟩
    have hcell (c : M.Cell) :
        ‖(∫ t in M.left c..M.clipped ((clock:ℝ)*a) c, f t) -
          ∑ j : Fin (ClockSchedule.sourceOrder K), M.row (ClockSchedule.sourceOrder K)
            0 ((clock:ℝ)*a) (c,j) • f (M.location (ClockSchedule.sourceOrder K) (c,j))‖ ≤ B := by
      have hsub : Icc (M.left c) (M.left c+M.length c) ⊆ Icc (0:ℝ) (1/2) := by
        intro t ht
        refine ⟨(M.lo_le_left c).trans ht.1, ?_⟩
        have hr : M.left c + M.length c = M.right c := by
          simp only [IntervalMesh.length]; ring
        exact ((ht.2.trans (le_of_eq hr)).trans (M.right_le_hi c)).trans clock.2.2
      have H := OuterRootOriginalQuadrature.source_gauss_cell hV hm hh hlo hup hsmall n
        (M.left c) (M.length c) (M.normalizedCoordinate 0 c)
        (M.normalizedCoordinate ((clock:ℝ)*a) c) (M.length_pos c)
        (M.normalizedCoordinate_mem 0 c) (M.normalizedCoordinate_mem _ c) hsub
      have hz : M.clipped 0 c = M.left c := by
        simp only [IntervalMesh.clipped, max_eq_left_iff]
        exact (min_le_left _ _).trans (M.lo_le_left c)
      rw [hn]
      simp only [IntervalMesh.row_eq_partialRow, IntervalMesh.location]
      have hlen : M.length c = (clock:ℝ)/(ClockSchedule.sourceCells h:ℝ) :=
        clockMesh_length _ _ clock hc c
      simp only [M.left_add_length_mul_normalizedCoordinate, hz] at H
      simpa only [hlen, F, d, f, B] using H
    have H := prescribedRow_defect_of_cells h hh K clock hc a ha f hf (fun _ => B) hcell
    have hcard : Fintype.card
        (clockMesh _ (ClockSchedule.sourceCells_pos hh) clock hc).Cell = ClockSchedule.sourceCells h := by
      simp only [IntervalMesh.Cell, Fintype.card_fin]
      exact unitMesh_cells _ (ClockSchedule.sourceCells_pos hh)
    simpa only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, f, B, F, d] using H
  · have hz : (clock:ℝ) = 0 := le_antisymm (le_of_not_gt hc) clock.2.1
    simp [W, hz]

/-- At the endpoint the same estimate uses exactly ClockSchedule.weight. -/
theorem source_finalRow (hsmall : h ≤ 1/2) (K : ℕ) (clock : ClockLaw.Clock) :
    let F := family hV hm hh hlo hup
    let d := OuterRootOriginalData.data hV hh (lower_nonneg hm hlo) hup
    let n := ClockSchedule.sourceOrder K - 1
    ‖(∫ t in 0..(clock:ℝ), jetLp F d (Real.sqrt h)⁻¹ 1 t) -
      ∑ j : MainIndex h K, ClockSchedule.weight (ClockSchedule.sourceCells h)
        (ClockSchedule.sourceOrder K) clock j •
        jetLp F d (Real.sqrt h)⁻¹ 1 (u h K clock j)‖ ≤
      (ClockSchedule.sourceCells h : ℝ) *
        (2*((clock:ℝ)/(ClockSchedule.sourceCells h:ℝ))^(n+2)*
          ((2*h^2)*Numerics.ConditionalSmoothing.materialOrderFactor
            (Fintype.card ι) n / (3/4)^(n+1))/((n+1).factorial:ℝ)) := by
  simpa only [mul_one, W_final] using
    source_prescribedRow hV hm hh hlo hup hsmall K clock 1 ⟨by norm_num, le_rfl⟩

end Original

end AcceleratedLogConcave.Root.ClockQuadratureRows
