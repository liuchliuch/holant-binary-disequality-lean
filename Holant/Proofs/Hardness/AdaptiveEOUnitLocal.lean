import Holant.Proofs.Hardness.PartialEOUnitLocal

/-! Public adaptive-unit API for the proved same-original-q local construction.
The local proof is shared with PartialEOUnitLocal; no second copy is maintained.
Exactly c,w,z,y are required. b and d remain unrestricted. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.AdaptiveEOUnitLocal
open Holant
export PartialEOUnitLocal
  (EOSupport cube cube_literal weights cube_value weights_nonzero swap01 binary0 binary1
   binary0_value binary1_value unitNetwork unit scale unit_value scale_nonzero scales_exact)
abbrev NonzeroMiddle {K : Type*} [Field K] (q : Signature K 4) := PartialEOUnitLocal.RequiredEntries q
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.AdaptiveEOUnitLocal
