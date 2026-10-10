import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4Differences
import Mathlib.Data.List.Perm.Basic

/-! The concrete right fold may visit spectral roots in reverse order.
Adjacent difference passes commute on every finite answer list. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ChainCompilerRecoveryOrder
namespace D
export GlobalCloseCompletionComplementQ4Differences (pass processList factor)
end D
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : Type} [Field K]
theorem pass_comm (x y : K) (values : List K) :
    D.pass x (D.pass y values)=D.pass y (D.pass x values) := by
  induction values with
  | nil=>rfl
  | cons a rest ih=>
    cases rest with
    | nil=>rfl
    | cons b rest=>
      cases rest with
      | nil=>rfl
      | cons c rest=>
        change ((c-y*b)-x*(b-y*a))::D.pass x (D.pass y (b::c::rest))=
          ((c-x*b)-y*(b-x*a))::D.pass y (D.pass x (b::c::rest))
        rw [ih]
        congr 1
        ring

theorem reverse (roots values : List K) : D.processList roots.reverse values=D.processList roots values := by
  letI : RightCommutative (fun values : List K=>fun node : K=>D.pass node values):=
    ⟨fun values x y=>pass_comm y x values⟩
  exact (List.reverse_perm roots).foldl_eq values

theorem factor_reverse (roots : List K) (target : K) : D.factor roots.reverse target=D.factor roots target := by
  simp [D.factor]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ChainCompilerRecoveryOrder
end
