import Holant.Support

/-! The literal support-in-one-weight-class predicate, independent of its
odd and charge-two hardness sources. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureChargeTwoFamily
open Holant
def UniformFour {K : Type*} [Zero K] {n : ℕ} (f : Signature K n) : Prop :=
  ∀x y,f x≠0 → f y≠0 → weight x%4=weight y%4

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureChargeTwoFamily
