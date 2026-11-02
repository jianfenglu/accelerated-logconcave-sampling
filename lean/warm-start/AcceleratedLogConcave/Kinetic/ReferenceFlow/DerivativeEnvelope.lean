import AcceleratedLogConcave.Kinetic.ReferenceFlow.CoreDerivative

/-! A uniform L2 envelope on pointwise derivatives yields the actual strong
L2 derivative, by the mean value theorem and dominated convergence. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace AcceleratedLogConcave.Kinetic

theorem hasDerivAt_L2_of_derivative_envelope {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : ℝ → Lp ℝ 2 μ) (G : Lp ℝ 2 μ)
    (f g : ℝ → X → ℝ) {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hf : ∀ s, F s =ᵐ[μ] f s) (hg : G =ᵐ[μ] g t)
    (hd : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun u => f u x) (g s x) s)
    (B : X → ℝ) (hB : Integrable (fun x => B x ^ 2) μ)
    (hbnd : ∀ s ∈ Ioo a b, ∀ x, ‖g s x‖ ≤ B x) : HasDerivAt F G t := by
  apply hasDerivAt_L2_core_of_envelope μ F G f (g t) t hf hg (hd t ht)
    (fun x => 2 * B x)
  · convert hB.const_mul 4 using 1
    funext x
    ring
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ht)] with s hs hst
    apply Eventually.of_forall
    intro x
    have hdiff := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu => (hd u hu x).hasDerivWithinAt) (fun u hu => hbnd u hu x)
      (convex_Ioo a b) ht hst
    have hne : s-t ≠ 0 := sub_ne_zero.mpr hs
    have hq : ‖slope (fun u => f u x) t s‖ ≤ B x := by
      rw [slope_def_module, norm_smul, norm_inv]
      calc
        _ ≤ ‖s-t‖⁻¹ * (B x * ‖s-t‖) :=
          mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr (norm_nonneg _))
        _ = B x := by field_simp
    exact (norm_sub_le _ _).trans (by linarith [hbnd t ht x])

end AcceleratedLogConcave.Kinetic
