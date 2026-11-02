import AcceleratedLogConcave.Conditional.Transport.CompactIntegral

/-!

-/
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff
namespace AcceleratedLogConcave.Conditional.Transport

universe u

/-- Joint smoothness of the literal spatial jet of a smooth time-space map.
The time coordinate is a parameter, not one of the differentiated slots. -/
theorem contDiff_spatialJet (n : ℕ) :
    ∀ {H G : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
      [NormedAddCommGroup G] [NormedSpace ℝ G]
      {F : ℝ × H → G}, ContDiff ℝ ∞ F →
      ContDiff ℝ ∞ (fun p : ℝ × H =>
        iteratedFDeriv ℝ n (fun y => F (p.1,y)) p.2) := by
  induction n with
  | zero =>
    intro H G _ _ _ _ F hF
    exact (continuousMultilinearCurryFin0 ℝ H G).symm.contDiff.comp hF
  | succ n ih =>
    intro H G _ _ _ _ F hF
    let D := spatialPartialDerivative F
    have hD : ContDiff ℝ ∞ D := contDiff_spatialPartialDerivative hF
    have he (t : ℝ) : fderiv ℝ (fun y => F (t,y)) = fun y => D (t,y) :=
      funext (fun y => (hasFDerivAt_spatialPartialDerivative hF t y).fderiv)
    have hj := (continuousMultilinearCurryRightEquiv' ℝ n H G).symm.contDiff.comp (ih hD)
    convert hj using 1
    funext p
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, he p.1]
    rfl

/-- Every iterated spatial Frechet derivative commutes with the compact-time
Bochner integral. The proof applies first-order compact domination to the
jointly smooth n-th jet; it does not postulate a domination supplier. -/
theorem iteratedFDeriv_intervalIntegral_of_contDiff (n : ℕ) :
    ∀ {H G : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
      [FiniteDimensional ℝ H] [NormedAddCommGroup G] [NormedSpace ℝ G]
      [CompleteSpace G] {F : ℝ × H → G} (_hF : ContDiff ℝ ∞ F)
      {a b : ℝ} (_hab : a ≤ b) (x : H),
      iteratedFDeriv ℝ n (fun y => ∫ t in a..b, F (t,y)) x =
        ∫ t in a..b, iteratedFDeriv ℝ n (fun y => F (t,y)) x := by
  induction n with
  | zero =>
    intro H G _ _ _ _ _ _ F hF a b hab x
    exact ((continuousMultilinearCurryFin0 ℝ H G).symm.toLinearIsometry.intervalIntegral_comp_comm (fun t => F (t,x))).symm
  | succ n ih =>
    intro H G _ _ _ _ _ _ F hF a b hab x
    let J : ℝ × H → H [×n]→L[ℝ] G :=
      fun p => iteratedFDeriv ℝ n (fun y => F (p.1,y)) p.2
    have hJ : ContDiff ℝ ∞ J := contDiff_spatialJet n hF
    have he : iteratedFDeriv ℝ n (fun y => ∫ t in a..b, F (t,y)) =
        fun y => ∫ t in a..b, J (t,y) :=
      funext (fun y => ih hF hab y)
    have hslice (t : ℝ) : spatialPartialDerivative J (t,x) =
        fderiv ℝ (iteratedFDeriv ℝ n (fun y => F (t,y))) x :=
      (hasFDerivAt_spatialPartialDerivative hJ t x).fderiv.symm
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    rw [he, (hasFDerivAt_intervalIntegral_of_contDiff hJ hab x).fderiv]
    simp_rw [hslice]
    exact (LinearIsometry.intervalIntegral_comp_comm (𝕜 := ℝ)
      (E := H →L[ℝ] H [×n]→L[ℝ] G) (F := H [×(n+1)]→L[ℝ] G)
      (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n+1) => H) G).symm.toLinearIsometry _).symm

end AcceleratedLogConcave.Conditional.Transport
