import AcceleratedLogConcave.Tensor.OriginalDataLegacyBudgets
import AcceleratedLogConcave.Tensor.ActualKernelFiniteAssembly

/-! A thin join of the proved original-data P/Q suppliers and the independently
validated conditional kernel assembly. No analytic premise is added here. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Tensor.OriginalDataKernel

/-- The original kernel budget is now a closed theorem from original data only. -/
theorem original_data_actualKernelBudgetStatement :
    QuantitativeKernel.ActualKernelBudgetStatement :=
  QuantitativeKernel.KernelFiniteAssembly.actual_kernel_budget_of_actual_flow_inverse
    LegacyOriginalDataBudgets.original_data_actualFlowBudgetStatement
    LegacyOriginalDataBudgets.original_data_actualInverseBudgetStatement

end AcceleratedLogConcave.Tensor.OriginalDataKernel
